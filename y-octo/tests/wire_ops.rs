use std::{
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};

use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha20Rng;
use serde_json::{Value as Json, json};
use y_octo::{
    Any, CrdtWriter, Doc, DocOptions, JwstCodecError, OrderRange, RawEncoder, ReadDoc, ReadError, StateVector, Update,
    Value, diff_update_v1, encode_state_vector_from_update_v1, merge_updates_v1, validate_update_v1,
};

fn doc(client: u64, gc: bool) -> Doc {
    DocOptions::from_identity(client, "wire-ops".into()).auto_gc(gc).build()
}

// --- 1A.1: DeleteSet unification & ReadDoc Skip deletion completeness ---

#[test]
fn delete_set_matches_between_gc_snapshot_and_raw_merge() {
    let a = doc(1, true);
    let mut text = a.get_or_create_text("t").unwrap();
    text.insert(0, "abcdef").unwrap();
    let u1 = a.encode_update_v1().unwrap();
    let sv1 = a.get_state_vector();
    text.remove(1, 2).unwrap();
    let u2 = a.encode_state_as_update_v1(&sv1).unwrap();
    let sv2 = a.get_state_vector();
    text.remove(2, 2).unwrap();
    let u3 = a.encode_state_as_update_v1(&sv2).unwrap();

    // Receiver 1: applies GC snapshot directly
    let gc_snapshot = a.encode_update_v1().unwrap();
    let mut from_snapshot = doc(2, true);
    from_snapshot.apply_update_from_binary_v1(&gc_snapshot).unwrap();

    // Receiver 2: applies raw-merged incremental updates
    let merged = merge_updates_v1([u1, u2, u3]).unwrap().encode_v1().unwrap();
    let mut from_merge = doc(3, true);
    from_merge.apply_update_from_binary_v1(&merged).unwrap();

    assert_eq!(from_snapshot.get_delete_sets(), a.get_delete_sets());
    assert_eq!(from_merge.get_delete_sets(), a.get_delete_sets());
    assert_eq!(from_snapshot.get_delete_sets(), from_merge.get_delete_sets());
    assert_eq!(from_snapshot.get_delete_sets()[&1], OrderRange::from(vec![1..3, 4..6]));
}

#[test]
fn auto_gc_false_then_explicit_doc_gc_collects_deleted_content() {
    let d = doc(10, false);
    let mut text = d.get_or_create_text("t").unwrap();
    let payload = "secret-deleted-payload-1234567890";
    text.insert(0, payload).unwrap();
    text.remove(0, payload.len() as u64).unwrap();
    text.insert(0, "keep").unwrap();

    // Before explicit GC, auto_gc(false) keeps the deleted string bytes in the
    // wire update.
    let before_gc = d.encode_update_v1().unwrap();
    assert!(
        before_gc.windows(payload.len()).any(|w| w == payload.as_bytes()),
        "deleted payload should remain uncollected before Doc::gc()"
    );

    // Explicit Doc::gc() must still collect historical deleted items even
    // though `collector.deleted` was drained on commit.
    d.gc().unwrap();
    let after_gc = d.encode_update_v1().unwrap();
    assert!(
        !after_gc.windows(payload.len()).any(|w| w == payload.as_bytes()),
        "deleted payload should be collected after Doc::gc()"
    );
    assert!(after_gc.len() < before_gc.len());

    let mut reopened = doc(11, false);
    reopened.apply_update_from_binary_v1(&after_gc).unwrap();
    assert_eq!(reopened.get_or_create_text("t").unwrap().to_string(), "keep");
    assert_eq!(reopened.get_delete_sets(), d.get_delete_sets());
}

#[test]
fn read_doc_rejects_delete_set_on_skip_but_accepts_gc() {
    // 1 client (id=1, clock=0), 1 struct: Skip(3), DeleteSet: client 1 range
    // 1..2
    let mut skip_enc = RawEncoder::default();
    skip_enc.write_var_u64(1).unwrap(); // 1 client
    skip_enc.write_var_u64(1).unwrap(); // 1 struct
    skip_enc.write_var_u64(1).unwrap(); // client 1
    skip_enc.write_var_u64(0).unwrap(); // clock 0
    skip_enc.write_info(10).unwrap(); // Skip
    skip_enc.write_var_u64(3).unwrap(); // len 3
    skip_enc.write_var_u64(1).unwrap(); // 1 delete client
    skip_enc.write_var_u64(1).unwrap(); // client 1
    skip_enc.write_var_u64(1).unwrap(); // 1 range
    skip_enc.write_var_u64(1).unwrap(); // start 1
    skip_enc.write_var_u64(1).unwrap(); // len 1
    let skip_update = skip_enc.into_inner();

    assert!(matches!(
        ReadDoc::from_full_update_v1(skip_update.as_slice()),
        Err(ReadError::IncompleteSnapshot("delete-set targets missing skip range"))
    ));

    // Same update but with GC(3) instead of Skip(3): idempotent delete must
    // succeed.
    let mut gc_enc = RawEncoder::default();
    gc_enc.write_var_u64(1).unwrap();
    gc_enc.write_var_u64(1).unwrap();
    gc_enc.write_var_u64(1).unwrap();
    gc_enc.write_var_u64(0).unwrap();
    gc_enc.write_info(0).unwrap(); // GC
    gc_enc.write_var_u64(3).unwrap(); // len 3
    gc_enc.write_var_u64(1).unwrap();
    gc_enc.write_var_u64(1).unwrap();
    gc_enc.write_var_u64(1).unwrap();
    gc_enc.write_var_u64(1).unwrap();
    gc_enc.write_var_u64(1).unwrap();
    let gc_update = gc_enc.into_inner();

    assert!(ReadDoc::from_full_update_v1(gc_update.as_slice()).is_ok());
}

// --- 1A.2: Stateless V1 wire operators ---

#[test]
fn validate_and_sv_and_diff_error_cases() {
    // [0, 0] is valid empty update; &[] is invalid
    assert!(validate_update_v1(&[0, 0]).is_ok());
    assert!(validate_update_v1(&[]).is_err());
    assert_eq!(
        validate_update_v1(&[0, 0, 0]),
        Err(JwstCodecError::UpdateNotFullyConsumed(1))
    );

    // State vector: &[0] is valid empty SV; &[] is invalid; trailing byte is
    // rejected
    assert_eq!(diff_update_v1(&[0, 0], &[0]).unwrap(), vec![0, 0]);
    assert!(diff_update_v1(&[0, 0], &[]).is_err());
    assert_eq!(
        diff_update_v1(&[0, 0], &[0, 0]),
        Err(JwstCodecError::UpdateNotFullyConsumed(1))
    );

    // Corrupt delete-set tail is rejected by encode_state_vector_from_update_v1
    let d = doc(1, true);
    d.get_or_create_text("t").unwrap().insert(0, "hi").unwrap();
    let mut valid = d.encode_update_v1().unwrap();
    assert_eq!(
        encode_state_vector_from_update_v1(&valid).unwrap(),
        d.get_state_vector().encode_v1().unwrap()
    );
    valid.push(0xFF);
    assert_eq!(
        encode_state_vector_from_update_v1(&valid),
        Err(JwstCodecError::UpdateNotFullyConsumed(1))
    );
    assert_eq!(
        diff_update_v1(&valid, &[0]),
        Err(JwstCodecError::UpdateNotFullyConsumed(1))
    );
}

/// Builds a single-client update containing one root item with no origin,
/// `parent_sub = Some("k")`, and `ContentAny([1, 2])` (len 2, info = `0x28`).
fn build_parent_sub_any_len2_update() -> Vec<u8> {
    let mut enc = RawEncoder::default();
    enc.write_var_u64(1).unwrap(); // 1 client
    enc.write_var_u64(1).unwrap(); // 1 struct
    enc.write_var_u64(1).unwrap(); // client 1
    enc.write_var_u64(0).unwrap(); // clock 0
    enc.write_info(0x28).unwrap(); // BIT6 (0x20) | ContentAny (8)
    enc.write_var_u64(1).unwrap(); // root parent
    enc.write_var_string("m").unwrap();
    enc.write_var_string("k").unwrap(); // parent_sub
    enc.write_var_u64(2).unwrap(); // 2 Any values
    enc.write_u8(125).unwrap(); // Integer
    enc.write_var_i32(1).unwrap();
    enc.write_u8(125).unwrap(); // Integer
    enc.write_var_i32(2).unwrap();
    enc.write_var_u64(0).unwrap(); // empty delete set
    enc.into_inner()
}

#[test]
fn diff_update_v1_bit6_two_stage_golden() {
    let update = build_parent_sub_any_len2_update();
    assert!(validate_update_v1(&update).is_ok());

    let sv_at_1 = StateVector::from([(1, 1)]).encode_v1().unwrap();
    let stage1 = diff_update_v1(&update, &sv_at_1).unwrap();
    // Header: [1 client, 1 struct, client=1, clock=1], then info byte = 0xA8
    assert_eq!(stage1[0..5], [1, 1, 1, 1, 0xA8]);
    // Followed by origin_left=(1, 0), ContentAny(len=1, Integer(2)), empty
    // DS(0)
    assert_eq!(stage1, vec![1, 1, 1, 1, 0xA8, 1, 0, 1, 125, 2, 0]);

    // Stage 2: diffing stage1 against empty SV [0] (offset=0, unsplit) must
    // clear BIT6 because input already had origin_left so no parent_sub was
    // decoded.
    let stage2 = diff_update_v1(&stage1, &[0]).unwrap();
    assert_eq!(stage2, vec![1, 1, 1, 1, 0x88, 1, 0, 1, 125, 2, 0]);
}

#[test]
fn diff_update_v1_utf16_surrogate_split_a_emoji_b() {
    let d = doc(7, true);
    d.get_or_create_text("t").unwrap().insert(0, "A😀B").unwrap();
    let update = d.encode_update_v1().unwrap();

    for (offset, expected_tail) in [(1u64, "😀B"), (2u64, "\u{FFFD}B"), (3u64, "B")] {
        let sv = StateVector::from([(7, offset)]).encode_v1().unwrap();
        let diff = diff_update_v1(&update, &sv).unwrap();
        assert!(validate_update_v1(&diff).is_ok());
        // Check decoded tail string
        let decoded = Update::decode_v1(&diff).unwrap();
        let encoded_again = decoded.encode_v1().unwrap();
        assert_eq!(diff, encoded_again);

        // Apply to a doc holding the first `offset` clocks for
        // non-split-surrogate offsets
        if offset != 2 {
            let mut target = doc(8, true);
            let prefix_doc = doc(7, true);
            prefix_doc
                .get_or_create_text("t")
                .unwrap()
                .insert(0, if offset == 1 { "A" } else { "A😀" })
                .unwrap();
            target
                .apply_update_from_binary_v1(prefix_doc.encode_update_v1().unwrap())
                .unwrap();
            target.apply_update_from_binary_v1(&diff).unwrap();
            assert_eq!(target.get_or_create_text("t").unwrap().to_string(), "A😀B");
        }
        assert!(
            diff.windows(expected_tail.len()).any(|w| w == expected_tail.as_bytes()),
            "offset {offset} diff should contain {expected_tail:?}"
        );
    }
}

#[test]
fn encode_state_vector_client_zero_skip_conservative() {
    // Client 0 (first client in stream) starts with Skip(2), then Item(2, 3).
    // Conservative rule: client 0 must be omitted (not emitted with clock 2 or
    // 5).
    let mut enc = RawEncoder::default();
    enc.write_var_u64(1).unwrap(); // 1 client
    enc.write_var_u64(2).unwrap(); // 2 structs
    enc.write_var_u64(0).unwrap(); // client 0
    enc.write_var_u64(0).unwrap(); // clock 0
    enc.write_info(10).unwrap(); // Skip
    enc.write_var_u64(2).unwrap(); // len 2
    enc.write_info(4).unwrap(); // String
    enc.write_var_u64(1).unwrap();
    enc.write_var_string("t").unwrap();
    enc.write_var_string("abc").unwrap();
    enc.write_var_u64(0).unwrap(); // empty DS
    let u = enc.into_inner();

    assert_eq!(encode_state_vector_from_update_v1(&u).unwrap(), vec![0]);

    // Client with Item(0, 3), Skip(3, 2), Item(5, 4) -> SV stops at 3.
    let mut enc2 = RawEncoder::default();
    enc2.write_var_u64(1).unwrap();
    enc2.write_var_u64(3).unwrap();
    enc2.write_var_u64(5).unwrap(); // client 5
    enc2.write_var_u64(0).unwrap(); // clock 0
    enc2.write_info(4).unwrap();
    enc2.write_var_u64(1).unwrap();
    enc2.write_var_string("t").unwrap();
    enc2.write_var_string("abc").unwrap();
    enc2.write_info(10).unwrap(); // Skip(2)
    enc2.write_var_u64(2).unwrap();
    enc2.write_info(4).unwrap();
    enc2.write_var_u64(1).unwrap();
    enc2.write_var_string("t").unwrap();
    enc2.write_var_string("defg").unwrap();
    enc2.write_var_u64(0).unwrap();
    let u2 = enc2.into_inner();

    assert_eq!(
        encode_state_vector_from_update_v1(&u2).unwrap(),
        StateVector::from([(5, 3)]).encode_v1().unwrap()
    );

    // diff_update_v1 against sv={5: 0} preserves internal Skip(2)
    let diff0 = diff_update_v1(&u2, &[0]).unwrap();
    assert_eq!(diff0, u2);
    // diff_update_v1 against sv={5: 4} drops leading Skip and starts at clock 5
    let diff4 = diff_update_v1(&u2, &StateVector::from([(5, 4)]).encode_v1().unwrap()).unwrap();
    assert_eq!(diff4[0..4], [1, 1, 5, 5]);
}

#[test]
fn diff_update_v1_splits_gc_deleted_json_any_and_preserves_ds() {
    // Build update with GC(4), ContentDeleted(4), ContentJson(["1","2","3"])
    let mut enc = RawEncoder::default();
    enc.write_var_u64(1).unwrap(); // 1 client
    enc.write_var_u64(3).unwrap(); // 3 structs
    enc.write_var_u64(9).unwrap(); // client 9
    enc.write_var_u64(0).unwrap(); // clock 0
    // struct 0: GC(4) -> clocks 0..4
    enc.write_info(0).unwrap();
    enc.write_var_u64(4).unwrap();
    // struct 1: ContentDeleted(4) -> clocks 4..8
    enc.write_info(1).unwrap();
    enc.write_var_u64(1).unwrap();
    enc.write_var_string("r").unwrap();
    enc.write_var_u64(4).unwrap();
    // struct 2: ContentJson(["\"a\"", "undefined", "\"c\""]) -> clocks 8..11
    enc.write_info(2).unwrap();
    enc.write_var_u64(1).unwrap();
    enc.write_var_string("r").unwrap();
    enc.write_var_u64(3).unwrap();
    enc.write_var_string("\"a\"").unwrap();
    enc.write_var_string("undefined").unwrap();
    enc.write_var_string("\"c\"").unwrap();
    // DeleteSet: client 9 range 0..8
    enc.write_var_u64(1).unwrap();
    enc.write_var_u64(9).unwrap();
    enc.write_var_u64(1).unwrap();
    enc.write_var_u64(0).unwrap();
    enc.write_var_u64(8).unwrap();
    let update = enc.into_inner();

    // Split inside GC at clock 2
    let d_gc = diff_update_v1(&update, &StateVector::from([(9, 2)]).encode_v1().unwrap()).unwrap();
    assert!(validate_update_v1(&d_gc).is_ok());
    assert_eq!(d_gc[0..6], [1, 3, 9, 2, 0, 2]); // client 9 @ 2, GC(2)

    // Split inside ContentDeleted at clock 6
    let d_del = diff_update_v1(&update, &StateVector::from([(9, 6)]).encode_v1().unwrap()).unwrap();
    assert!(validate_update_v1(&d_del).is_ok());
    // client 9 @ 6, 2 structs, info = 0x81 (HAS_LEFT | Deleted), left=(9,5),
    // len=2
    assert_eq!(d_del[0..8], [1, 2, 9, 6, 0x81, 9, 5, 2]);

    // Split inside ContentJson at clock 9 (keeps ["undefined", "\"c\""])
    let d_json = diff_update_v1(&update, &StateVector::from([(9, 9)]).encode_v1().unwrap()).unwrap();
    assert!(validate_update_v1(&d_json).is_ok());
    assert_eq!(d_json[0..8], [1, 1, 9, 9, 0x82, 9, 8, 2]);

    // Diff at full SV 11: 0 structs, DeleteSet preserved
    let d_full = diff_update_v1(&update, &StateVector::from([(9, 11)]).encode_v1().unwrap()).unwrap();
    assert_eq!(d_full, vec![0, 1, 9, 1, 0, 8]);
}

#[test]
fn clock_overflow_before_sink_returns_err_without_panic() {
    // Case 1: single GC at clock = u64::MAX, len = 1
    let mut single_enc = RawEncoder::default();
    single_enc.write_var_u64(1).unwrap(); // 1 client
    single_enc.write_var_u64(1).unwrap(); // 1 struct
    single_enc.write_var_u64(7).unwrap(); // client 7
    single_enc.write_var_u64(u64::MAX).unwrap(); // start clock = u64::MAX
    single_enc.write_info(0).unwrap(); // GC
    single_enc.write_var_u64(1).unwrap(); // len = 1
    single_enc.write_var_u64(0).unwrap(); // empty DS
    let single_gc = single_enc.into_inner();

    assert!(matches!(
        diff_update_v1(&single_gc, &[0]),
        Err(JwstCodecError::StructClockInvalid {
            expect: u64::MAX,
            actually: u64::MAX
        })
    ));

    // Case 2: single client from clock = 0 with two consecutive GCs: len =
    // u64::MAX then len = 1
    let mut double_enc = RawEncoder::default();
    double_enc.write_var_u64(1).unwrap(); // 1 client
    double_enc.write_var_u64(2).unwrap(); // 2 structs
    double_enc.write_var_u64(7).unwrap(); // client 7
    double_enc.write_var_u64(0).unwrap(); // start clock = 0
    double_enc.write_info(0).unwrap(); // GC 1
    double_enc.write_var_u64(u64::MAX).unwrap(); // len = u64::MAX -> next clock = u64::MAX
    double_enc.write_info(0).unwrap(); // GC 2
    double_enc.write_var_u64(1).unwrap(); // len = 1 -> overflow
    double_enc.write_var_u64(0).unwrap(); // empty DS
    let double_gc = double_enc.into_inner();

    let expected = JwstCodecError::StructClockInvalid {
        expect: u64::MAX,
        actually: u64::MAX,
    };
    assert_eq!(validate_update_v1(&double_gc).unwrap_err(), expected);
    assert_eq!(encode_state_vector_from_update_v1(&double_gc).unwrap_err(), expected);
    assert_eq!(diff_update_v1(&double_gc, &[0]).unwrap_err(), expected);
}

#[test]
fn embed_and_format_json_validator_matches_update_decode() {
    let deep_arrays = format!("{}0{}", "[".repeat(140), "]".repeat(140));
    let bad_jsons = ["1e400", deep_arrays.as_str()];

    for bad_json in bad_jsons {
        // Content::Embed (tag 5)
        let mut embed_enc = RawEncoder::default();
        embed_enc.write_var_u64(1).unwrap();
        embed_enc.write_var_u64(1).unwrap();
        embed_enc.write_var_u64(1).unwrap();
        embed_enc.write_var_u64(0).unwrap();
        embed_enc.write_info(5).unwrap();
        embed_enc.write_var_u64(1).unwrap();
        embed_enc.write_var_string("t").unwrap();
        embed_enc.write_var_string(bad_json).unwrap();
        embed_enc.write_var_u64(0).unwrap();
        let embed_update = embed_enc.into_inner();

        assert_eq!(
            Update::decode_v1(&embed_update).unwrap_err(),
            JwstCodecError::DamagedDocumentJson
        );
        assert_eq!(
            validate_update_v1(&embed_update),
            Err(JwstCodecError::DamagedDocumentJson)
        );
        assert_eq!(
            encode_state_vector_from_update_v1(&embed_update),
            Err(JwstCodecError::DamagedDocumentJson)
        );
        assert_eq!(
            diff_update_v1(&embed_update, &[0]),
            Err(JwstCodecError::DamagedDocumentJson)
        );

        // Content::Format (tag 6)
        let mut fmt_enc = RawEncoder::default();
        fmt_enc.write_var_u64(1).unwrap();
        fmt_enc.write_var_u64(1).unwrap();
        fmt_enc.write_var_u64(1).unwrap();
        fmt_enc.write_var_u64(0).unwrap();
        fmt_enc.write_info(6).unwrap();
        fmt_enc.write_var_u64(1).unwrap();
        fmt_enc.write_var_string("t").unwrap();
        fmt_enc.write_var_string("bold").unwrap();
        fmt_enc.write_var_string(bad_json).unwrap();
        fmt_enc.write_var_u64(0).unwrap();
        let fmt_update = fmt_enc.into_inner();

        assert_eq!(
            Update::decode_v1(&fmt_update).unwrap_err(),
            JwstCodecError::DamagedDocumentJson
        );
        assert_eq!(
            validate_update_v1(&fmt_update),
            Err(JwstCodecError::DamagedDocumentJson)
        );
        assert_eq!(
            encode_state_vector_from_update_v1(&fmt_update),
            Err(JwstCodecError::DamagedDocumentJson)
        );
        assert_eq!(
            diff_update_v1(&fmt_update, &[0]),
            Err(JwstCodecError::DamagedDocumentJson)
        );
    }
}

#[test]
fn property_wire_ops_invariants() {
    let mut rng = ChaCha20Rng::seed_from_u64(0x5EED_1A20);

    // 1 & 2: diff(u, sv_of(u)) has only DS; applying diff(u, sv) to doc@sv ==
    // applying u
    for seed in 0..24u64 {
        let mut r = ChaCha20Rng::seed_from_u64(seed + 100);
        let a = doc(1, seed % 2 == 0);
        let b = doc(2, seed % 2 == 1);
        let mut ta = a.get_or_create_text("t").unwrap();
        let mut tb = b.get_or_create_text("t").unwrap();
        let mut ma = a.get_or_create_map("m").unwrap();
        let mut aa = a.get_or_create_array("a").unwrap();

        for step in 0..12 {
            match r.random_range(0..5) {
                0 => {
                    let pos = r.random_range(0..=ta.len());
                    ta.insert(pos, if step % 3 == 0 { "😀x" } else { "abc" }).unwrap();
                }
                1 if !ta.is_empty() => {
                    let pos = r.random_range(0..ta.len());
                    let len = r.random_range(1..=(ta.len() - pos).min(2));
                    ta.remove(pos, len).unwrap();
                }
                2 => {
                    let pos = r.random_range(0..=tb.len());
                    tb.insert(pos, "pq").unwrap();
                }
                3 => {
                    ma.insert(format!("k{}", step % 3), Value::Any(Any::Integer(step)))
                        .unwrap();
                }
                _ => {
                    let pos = r.random_range(0..=aa.len());
                    aa.insert(pos, Value::Any(Any::Integer(step))).unwrap();
                }
            }
        }

        let snap_a = a.encode_update_v1().unwrap();
        let sv_a = encode_state_vector_from_update_v1(&snap_a).unwrap();
        assert_eq!(sv_a, a.get_state_vector().encode_v1().unwrap());

        let mut combined = a.clone();
        combined
            .apply_update_from_binary_v1(b.encode_update_v1().unwrap())
            .unwrap();
        let full = combined.encode_update_v1().unwrap();
        assert!(validate_update_v1(&full).is_ok());

        // Property: diff(u, sv_of(u)) leaves only DS (0 struct clients)
        let full_sv = encode_state_vector_from_update_v1(&full).unwrap();
        let remainder = diff_update_v1(&full, &full_sv).unwrap();
        assert_eq!(remainder[0], 0, "diff(u, sv_of(u)) must have 0 struct clients");
        let parsed_rem = Update::decode_v1(&remainder).unwrap();
        assert!(parsed_rem.is_content_empty());
        assert_eq!(
            remainder,
            combined
                .encode_state_as_update_v1(&combined.get_state_vector())
                .unwrap()
        );

        // Property: doc@sv_a + diff(full, sv_a) == doc@sv_a + full
        let delta = diff_update_v1(&full, &sv_a).unwrap();
        let mut via_diff = doc(99, true);
        via_diff.apply_update_from_binary_v1(&snap_a).unwrap();
        via_diff.apply_update_from_binary_v1(&delta).unwrap();

        let mut via_full = doc(99, true);
        via_full.apply_update_from_binary_v1(&snap_a).unwrap();
        via_full.apply_update_from_binary_v1(&full).unwrap();

        assert_eq!(
            via_diff.get_or_create_text("t").unwrap().to_string(),
            via_full.get_or_create_text("t").unwrap().to_string()
        );
        assert_eq!(via_diff.get_state_vector(), via_full.get_state_vector());
        assert_eq!(via_diff.get_delete_sets(), via_full.get_delete_sets());
        assert!(via_diff.store_compare(&via_full));
    }

    // 3: validate_update_v1(u).is_ok() == Update::decode_v1(u).is_ok()
    let sample = {
        let d = doc(1, true);
        d.get_or_create_text("t").unwrap().insert(0, "hello😀").unwrap();
        d.get_or_create_map("m").unwrap().insert("k".into(), 42).unwrap();
        d.encode_update_v1().unwrap()
    };
    // All truncated prefixes
    for len in 0..=sample.len() {
        let slice = &sample[..len];
        assert_eq!(
            validate_update_v1(slice).is_ok(),
            Update::decode_v1(slice).is_ok(),
            "prefix len {len}"
        );
    }
    // Single-byte mutations & random byte buffers
    for _ in 0..200 {
        let mut mutated = sample.clone();
        let idx = rng.random_range(0..mutated.len());
        mutated[idx] = rng.random();
        assert_eq!(
            validate_update_v1(&mutated).is_ok(),
            Update::decode_v1(&mutated).is_ok(),
            "mutated at {idx}"
        );

        let rand_len = rng.random_range(0..32);
        let buf: Vec<u8> = (0..rand_len).map(|_| rng.random()).collect();
        assert_eq!(
            validate_update_v1(&buf).is_ok(),
            Update::decode_v1(&buf).is_ok(),
            "random buf {buf:?}"
        );
    }
}

// --- Node Yjs 13.6.21 & 13.6.33 bidirectional byte-for-byte differential ---

struct WireOracle {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
}

impl WireOracle {
    fn new(version: &str) -> Self {
        let mut child = Command::new("node")
            .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/oracle/wire-ops.mjs"))
            .arg(version)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("spawn node wire-ops.mjs");
        Self {
            input: child.stdin.take().unwrap(),
            output: BufReader::new(child.stdout.take().unwrap()),
            child,
        }
    }

    fn request(&mut self, req: Json) -> Json {
        writeln!(self.input, "{req}").unwrap();
        self.input.flush().unwrap();
        let mut line = String::new();
        self.output.read_line(&mut line).unwrap();
        assert!(!line.is_empty(), "wire-ops oracle exited unexpectedly");
        serde_json::from_str(&line).unwrap()
    }

    fn sv(&mut self, update: &[u8]) -> Vec<u8> {
        let resp = self.request(json!({ "op": "sv", "update": update }));
        resp["bytes"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_u64().unwrap() as u8)
            .collect()
    }

    fn diff(&mut self, update: &[u8], sv: &[u8]) -> Vec<u8> {
        let resp = self.request(json!({ "op": "diff", "update": update, "sv": sv }));
        resp["bytes"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_u64().unwrap() as u8)
            .collect()
    }
}

impl Drop for WireOracle {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[test]
#[ignore = "requires node and y-octo/tests/oracle dependencies"]
fn online_wire_ops_yjs_differential() {
    for version in ["13.6.21", "13.6.33"] {
        let mut oracle = WireOracle::new(version);

        // 1. Yjs-generated cases -> Rust must match Yjs byte-for-byte on sv &
        //    diff
        let built = oracle.request(json!({ "op": "build_cases" }));
        for case in built["cases"].as_array().unwrap() {
            let name = case["name"].as_str().unwrap();
            let update: Vec<u8> = case["update"]
                .as_array()
                .unwrap()
                .iter()
                .map(|v| v.as_u64().unwrap() as u8)
                .collect();
            assert!(validate_update_v1(&update).is_ok(), "{version}/{name} validate");
            assert_eq!(
                encode_state_vector_from_update_v1(&update).unwrap(),
                oracle.sv(&update),
                "{version}/{name} sv mismatch"
            );
            for (i, sv_val) in case["svs"].as_array().unwrap().iter().enumerate() {
                let sv: Vec<u8> = sv_val
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|v| v.as_u64().unwrap() as u8)
                    .collect();
                assert_eq!(
                    diff_update_v1(&update, &sv).unwrap(),
                    oracle.diff(&update, &sv),
                    "{version}/{name} diff[{i}] mismatch"
                );
            }
        }

        // 2. Two-stage BIT6 golden (0xA8 -> 0x88) byte-for-byte vs Yjs
        let bit6_update = build_parent_sub_any_len2_update();
        let sv_1 = StateVector::from([(1, 1)]).encode_v1().unwrap();
        let rust_s1 = diff_update_v1(&bit6_update, &sv_1).unwrap();
        let yjs_s1 = oracle.diff(&bit6_update, &sv_1);
        assert_eq!(rust_s1, yjs_s1, "{version} BIT6 stage 1 (0xA8)");
        assert_eq!(rust_s1[4], 0xA8);

        let rust_s2 = diff_update_v1(&rust_s1, &[0]).unwrap();
        let yjs_s2 = oracle.diff(&yjs_s1, &[0]);
        assert_eq!(rust_s2, yjs_s2, "{version} BIT6 stage 2 (0x88)");
        assert_eq!(rust_s2[4], 0x88);

        // 3. Rust-generated updates (including GC snapshot, ContentDeleted,
        //    ContentJson, A😀B)
        let rust_doc = doc(77, true);
        let mut t = rust_doc.get_or_create_text("t").unwrap();
        t.insert(0, "A😀Bhello").unwrap();
        let sv_mid = rust_doc.get_state_vector().encode_v1().unwrap();
        t.remove(1, 2).unwrap();
        t.insert(2, "ZZ").unwrap();
        let rust_snap = rust_doc.encode_update_v1().unwrap();
        assert_eq!(
            encode_state_vector_from_update_v1(&rust_snap).unwrap(),
            oracle.sv(&rust_snap),
            "{version} rust_snap sv"
        );
        for sv in [vec![0], sv_mid, StateVector::from([(77, 2)]).encode_v1().unwrap()] {
            assert_eq!(
                diff_update_v1(&rust_snap, &sv).unwrap(),
                oracle.diff(&rust_snap, &sv),
                "{version} rust_snap diff sv={sv:?}"
            );
        }

        // 3b. Rust-generated 3-client mixed update (client 100 fully covered,
        // client 200 partially covered mid-struct, client 300 omitted).
        let doc_a = doc(100, true);
        doc_a.get_or_create_text("t").unwrap().insert(0, "alpha").unwrap();
        doc_a.get_or_create_map("m").unwrap().insert("a".into(), 1).unwrap();

        let mut doc_b = doc(200, true);
        doc_b
            .apply_update_from_binary_v1(doc_a.encode_update_v1().unwrap())
            .unwrap();
        doc_b.get_or_create_text("t").unwrap().insert(5, "beta-mid").unwrap();
        doc_b.get_or_create_text("t").unwrap().remove(1, 2).unwrap();

        let mut doc_c = doc(300, true);
        doc_c
            .apply_update_from_binary_v1(doc_b.encode_update_v1().unwrap())
            .unwrap();
        doc_c.get_or_create_text("t").unwrap().insert(0, "gamma").unwrap();
        doc_c.get_or_create_map("m").unwrap().insert("c".into(), "end").unwrap();

        let three_client_update = doc_c.encode_update_v1().unwrap();
        assert_eq!(
            encode_state_vector_from_update_v1(&three_client_update).unwrap(),
            oracle.sv(&three_client_update),
            "{version} rust 3-client sv"
        );
        let sv_partial = StateVector::from([(100, 6), (200, 4)]).encode_v1().unwrap();
        for sv in [vec![0], sv_partial, doc_c.get_state_vector().encode_v1().unwrap()] {
            assert_eq!(
                diff_update_v1(&three_client_update, &sv).unwrap(),
                oracle.diff(&three_client_update, &sv),
                "{version} rust 3-client diff sv={sv:?}"
            );
        }

        // 4. Known conservative difference regression: client 0 starting with
        //    Skip(2)
        // Rust omits client 0 from SV; Yjs's loop has a known quirk on client
        // 0.
        let mut enc = RawEncoder::default();
        enc.write_var_u64(1).unwrap();
        enc.write_var_u64(2).unwrap();
        enc.write_var_u64(0).unwrap();
        enc.write_var_u64(0).unwrap();
        enc.write_info(10).unwrap();
        enc.write_var_u64(2).unwrap();
        enc.write_info(4).unwrap();
        enc.write_var_u64(1).unwrap();
        enc.write_var_string("t").unwrap();
        enc.write_var_string("ab").unwrap();
        enc.write_var_u64(0).unwrap();
        let client0_skip = enc.into_inner();
        assert_eq!(
            encode_state_vector_from_update_v1(&client0_skip).unwrap(),
            vec![0],
            "{version} client-0 Skip(2) must conservatively omit client 0"
        );
        // Verify diff_update_v1 on client-0 Skip(2) still matches Yjs
        assert_eq!(
            diff_update_v1(&client0_skip, &[0]).unwrap(),
            oracle.diff(&client0_skip, &[0]),
            "{version} client-0 Skip(2) diff"
        );
    }
}
