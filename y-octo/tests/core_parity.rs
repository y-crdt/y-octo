use std::sync::{Arc, Mutex};

use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha20Rng;
use y_octo::{
    Any, DeleteSet, Doc, DocOptions, Id, Map, OrderRange, StateVector, Subscription, Text, TextInsert, Update, Value,
    read_var_i32, read_var_u64, validate_update_v1, write_var_i32, write_var_u64,
};
use y_octo_core::{
    CodecError,
    client_blocks::{BlockKindCore, BlockRefCore, ClientBlocksCore, StoreError},
    clock_search::find_clock_segment,
    decoder_v1::{
        DecodeLimitsCore, ItemMetaCore, Span, V1Sink, WireId, decode_state_vector_v1, decode_update_v1,
        decode_update_v1_frame,
    },
    delete_set::DeleteSetCore,
    doc_kernel::decide_integrate_link,
    id_order::{IdOrderCore, RECENT, Recent},
    id_set::IdSetCore,
    item_space::{CHUNK_SIZE, ItemSpaceCore, MAX_SLOTS},
    order_range::{ClockRange, OrderRange as CoreOrderRange},
    pending::{
        LocalStep, StructStep, check_local_readiness, classify_ready_step, classify_struct_step, dep_missing,
        find_missing_dependency, find_missing_dependency_states, split_delete_range,
    },
    state_vector::StateVectorCore,
    utf16::{is_valid_utf8, utf16_len, utf16_split_byte_offset},
    varint::{
        decode_var_i32, decode_var_i32_with_sign, decode_var_u64, encode_var_i32, encode_var_i32_buf, encode_var_u64,
        encode_var_u64_buf,
    },
    yata_store::{IdCore, YataStoreCore},
};

fn push_var_u64(out: &mut Vec<u8>, v: u64) {
    let (buf, len) = encode_var_u64_buf(v);
    out.extend_from_slice(&buf[..len]);
}

fn push_var_str(out: &mut Vec<u8>, s: &str) {
    push_var_u64(out, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

fn push_nested_any_array(out: &mut Vec<u8>, depth: usize) {
    for _ in 0..depth {
        out.push(127u8 - 10u8); // Any::Array wire tag
        push_var_u64(out, 1);
    }
    out.push(127u8 - 1u8); // Any::Null leaf
}

#[test]
fn parity_varint_bytes_and_errors() {
    // Independent hardcoded wire vectors (lib0 / Yjs specification).
    let u64_vectors: &[(u64, &[u8])] = &[
        (0, &[0x00]),
        (1, &[0x01]),
        (127, &[0x7f]),
        (128, &[0x80, 0x01]),
        (16383, &[0xff, 0x7f]),
        (16384, &[0x80, 0x80, 0x01]),
        (u32::MAX as u64, &[0xff, 0xff, 0xff, 0xff, 0x0f]),
        ((1u64 << 53) - 1, &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x0f]),
        (u64::MAX / 2, &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),
        (u64::MAX, &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01]),
    ];
    for &(v, expected) in u64_vectors {
        let (stack_buf, len) = encode_var_u64_buf(v);
        assert_eq!(&stack_buf[..len], expected, "stack encode_var_u64_buf({v})");
        assert_eq!(encode_var_u64(v), expected);

        let mut buf = Vec::new();
        write_var_u64(&mut buf, v).unwrap();
        assert_eq!(buf, expected);

        let mut with_tail = expected.to_vec();
        with_tail.extend_from_slice(&[0xaa, 0xbb]);
        let (tail, dec) = read_var_u64(&with_tail).unwrap();
        assert_eq!(dec, v);
        assert_eq!(tail, &[0xaa, 0xbb]);
        assert_eq!(decode_var_u64(&with_tail), Ok((v, expected.len())));
    }

    let i32_vectors: &[(i32, &[u8])] = &[
        (0, &[0x00]),
        (1, &[0x01]),
        (-1, &[0x41]),
        (63, &[0x3f]),
        (-63, &[0x7f]),
        (64, &[0x80, 0x01]),
        (-64, &[0xc0, 0x01]),
        (16384, &[0x80, 0x80, 0x02]),
        (-16384, &[0xc0, 0x80, 0x02]),
        (i32::MAX, &[0xbf, 0xff, 0xff, 0xff, 0x0f]),
        (i32::MIN, &[0xc0, 0x80, 0x80, 0x80, 0x10]),
    ];
    for &(v, expected) in i32_vectors {
        let (stack_buf, len) = encode_var_i32_buf(v);
        assert_eq!(&stack_buf[..len], expected, "stack encode_var_i32_buf({v})");
        assert_eq!(encode_var_i32(v), expected);

        let mut buf = Vec::new();
        write_var_i32(&mut buf, v).unwrap();
        assert_eq!(buf, expected);

        let mut with_tail = expected.to_vec();
        with_tail.extend_from_slice(&[0x55, 0x66]);
        let (tail, dec) = read_var_i32(&with_tail).unwrap();
        assert_eq!(dec, v);
        assert_eq!(tail, &[0x55, 0x66]);
        assert_eq!(decode_var_i32(&with_tail), Ok((v, expected.len())));
    }

    // lib0 `-0` (0x40) decodes to 0 with negative sign flag preserved in core.
    assert_eq!(decode_var_i32_with_sign(&[0x40, 0xee]), Ok(((0, true), 1)));
    assert_eq!(read_var_i32(&[0x40, 0xee]), Ok((&[0xee][..], 0)));

    // Exact nom::Err variants & Needed values + Core Error parity.
    assert_eq!(decode_var_u64(&[]), Err(CodecError::UnexpectedEof));
    assert_eq!(read_var_u64(&[]), Err(nom::Err::Incomplete(nom::Needed::new(1))));
    assert_eq!(decode_var_u64(&[0x80, 0x80]), Err(CodecError::UnexpectedEof));
    assert_eq!(
        read_var_u64(&[0x80, 0x80]),
        Err(nom::Err::Incomplete(nom::Needed::new(3)))
    );

    let overflow_u64 = [129u8, 128, 128, 128, 128, 128, 128, 128, 128, 2];
    assert_eq!(decode_var_u64(&overflow_u64), Err(CodecError::VarintOverflow));
    assert_eq!(
        read_var_u64(&overflow_u64),
        Err(nom::Err::Failure(nom::error::Error::new(
            &overflow_u64[..],
            nom::error::ErrorKind::TooLarge,
        )))
    );

    assert_eq!(decode_var_i32(&[]), Err(CodecError::UnexpectedEof));
    assert_eq!(read_var_i32(&[]), Err(nom::Err::Incomplete(nom::Needed::new(1))));
    assert_eq!(decode_var_i32(&[0x80]), Err(CodecError::UnexpectedEof));
    assert_eq!(read_var_i32(&[0x80]), Err(nom::Err::Incomplete(nom::Needed::new(2))));

    let overflow_i32 = [128u8, 128, 128, 128, 16];
    assert_eq!(decode_var_i32(&overflow_i32), Err(CodecError::VarintOverflow));
    assert_eq!(
        read_var_i32(&overflow_i32),
        Err(nom::Err::Failure(nom::error::Error::new(
            &overflow_i32[..],
            nom::error::ErrorKind::TooLarge,
        )))
    );
}

#[test]
fn parity_order_range_and_delete_set() {
    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };

    let mut octo = OrderRange::default();
    let mut core = CoreOrderRange::new();
    let rounds = if cfg!(miri) { 16 } else { 80 };
    for _ in 0..rounds {
        let start = next() % 200;
        let len = next() % 15;
        let end = start + len;
        octo.push(start..end);
        core.insert(start, end);
        for c in 0..220 {
            assert_eq!(core.contains(c), octo.contains(c), "clock {c}");
        }
    }

    let mut ds_octo = DeleteSet::default();
    let mut ds_core = DeleteSetCore::new();
    for (client, s, l) in [(1, 0, 10), (1, 20, 5), (1, 10, 10), (2, 5, 7), (3, 0, 0)] {
        ds_octo.add(client, s, l);
        ds_core.insert(client, s, s + l);
    }
    let mut ds_octo2 = DeleteSet::default();
    let mut ds_core2 = DeleteSetCore::new();
    for (client, s, l) in [(1, 25, 5), (4, 1, 3)] {
        ds_octo2.add(client, s, l);
        ds_core2.insert(client, s, s + l);
    }
    ds_octo.merge(&ds_octo2);
    ds_core.merge(&ds_core2);
    for client in 0..=4 {
        for c in 0..35 {
            let expected = ds_octo.get(&client).is_some_and(|r| r.contains(c));
            assert_eq!(ds_core.contains(client, c), expected);
        }
    }
}

#[test]
fn parity_state_vector_and_v1_codec() {
    let mut sv = StateVector::default();
    let mut core = StateVectorCore::new();
    for (c, k) in [(7, 4), (1, 2), (7, 9), (3, 0), (1, 1)] {
        sv.set_max(c, k);
        core.set_max(c, k);
    }
    for c in 0..10 {
        assert_eq!(core.get(c), sv.get(&c));
        for k in 0..12 {
            assert_eq!(core.contains(c, k), sv.contains(&Id::new(c, k)));
        }
    }

    let encoded = sv.encode_v1().unwrap();
    let Ok(decoded_core) = decode_state_vector_v1(&encoded) else {
        panic!("decode_state_vector_v1 failed");
    };
    for c in 0..10 {
        assert_eq!(decoded_core.get(c), sv.get(&c));
    }

    // Duplicate client entries in V1 SV use last-write-wins (overwrite).
    let dup_sv_bytes = [2u8, 7, 9, 7, 3];
    let prod_dup = StateVector::decode_v1(dup_sv_bytes).unwrap();
    let core_dup = decode_state_vector_v1(&dup_sv_bytes).unwrap_or_else(|e| panic!("dup decode failed: {e:?}"));
    assert_eq!(prod_dup.get(&7), 3);
    assert_eq!(core_dup.get(7), prod_dup.get(&7));

    let mut sv2 = StateVector::default();
    let mut core2 = StateVectorCore::new();
    for (c, k) in [(1, 1), (7, 15), (9, 3)] {
        sv2.set_max(c, k);
        core2.set_max(c, k);
    }
    sv.merge_with(&sv2);
    core.merge_with(&core2);
    for c in 0..12 {
        assert_eq!(core.get(c), sv.get(&c));
    }
}

#[test]
fn parity_utf16_and_clock_search() {
    let s = "a😀中文🎉b";
    assert!(is_valid_utf8(s.as_bytes()));
    assert_eq!(utf16_len(s.as_bytes()), s.encode_utf16().count());

    let b = utf16_split_byte_offset(s.as_bytes(), 2);
    assert!(b.split_surrogate);
    assert_eq!(b.start, 1);
    assert_eq!(b.end, 5);

    let b2 = utf16_split_byte_offset(s.as_bytes(), 3);
    assert!(!b2.split_surrogate);
    assert_eq!(b2.start, 5);

    // every boundary of every text, against a walk over the chars of `std`:
    // runs of one-byte chars (the branch of their own in the core), chars of
    // two, three and four bytes, and the mixes of them
    let ascii = "The quick brown fox jumps over the lazy dog. ".repeat(if cfg!(miri) { 1 } else { 40 });
    let mixed = "héllo 世界 😀 naïve café — ".repeat(if cfg!(miri) { 1 } else { 30 });
    for text in [
        "",
        "a",
        "é",
        "世",
        "😀",
        "a😀",
        "😀a",
        "😀😀",
        ascii.as_str(),
        mixed.as_str(),
    ] {
        let units = text.encode_utf16().count() as u64;
        assert_eq!(utf16_len(text.as_bytes()) as u64, units);
        assert_eq!(
            utf16_len(text.as_bytes()),
            text.chars().map(|c| c.len_utf16()).sum::<usize>()
        );
        let mut clock = 0u64;
        for (byte, ch) in text.char_indices() {
            for unit in 0..ch.len_utf16() as u64 {
                let at = utf16_split_byte_offset(text.as_bytes(), clock + unit);
                assert_eq!(
                    (at.start, at.end, at.split_surrogate),
                    (byte, byte + ch.len_utf8(), unit == 1),
                    "{text:?} at {}",
                    clock + unit
                );
            }
            clock += ch.len_utf16() as u64;
        }
        assert_eq!(clock, units);
        for target in [units, units + 1, u64::MAX] {
            let at = utf16_split_byte_offset(text.as_bytes(), target);
            assert_eq!((at.start, at.end, at.split_surrogate), (text.len(), text.len(), false));
        }
    }

    let segs = [(0u64, 5u64), (5, 3), (12, 4)];
    for c in 0..20 {
        let expected = segs.iter().position(|&(s, l)| s <= c && c < s + l);
        assert_eq!(find_clock_segment(&segs, c), expected);
    }
}

#[test]
fn parity_decoder_v1_with_real_doc_updates() {
    let doc1 = Doc::with_client(1);
    {
        let mut text = doc1.get_or_create_text("t").unwrap();
        text.insert(0, "hello 😀 world").unwrap();
        text.remove(6, 2).unwrap();
    }
    let update_bytes = doc1.encode_state_as_update_v1(&StateVector::default()).unwrap();
    assert!(validate_update_v1(&update_bytes).is_ok());
    let summary = decode_update_v1_frame(&update_bytes, &DecodeLimitsCore::default_update())
        .expect("decode_update_v1_frame failed");
    assert_eq!(summary.clients, 1);
    assert!(summary.structs >= 1);
    assert_eq!(summary.delete_clients, 1);
    assert!(summary.delete_ranges >= 1);
    assert!(Update::decode_v1(&update_bytes).is_ok());

    // Truncated / malformed inputs never panic and are rejected by both.
    for len in 0..update_bytes.len() {
        let prefix = &update_bytes[..len];
        assert!(validate_update_v1(prefix).is_err());
        assert!(decode_update_v1_frame(prefix, &DecodeLimitsCore::default_update()).is_err());
    }
}

#[test]
fn parity_decoder_v1_any_depth_and_content_tags_and_embed_format_boundary() {
    // Helper: wrap a single item/struct payload under client=1, clock=0, root
    // parent="r"
    let wrap_single_struct = |info_and_payload: &[u8]| -> Vec<u8> {
        let mut out = vec![1u8, 1, 1, 0]; // 1 client, 1 struct, client=1, clock=0
        out.extend_from_slice(info_and_payload);
        out.push(0); // 0 delete clients
        out
    };

    // 1. max_any_depth = 128 alignment: 65 & 128 accepted by both, 129 rejected
    //    by both.
    for (depth, should_accept) in [(65usize, true), (128usize, true), (129usize, false)] {
        let mut payload = Vec::new();
        payload.push(8u8); // Content::Any, explicit parent
        payload.push(1u8); // parent kind = String
        push_var_str(&mut payload, "r");
        push_var_u64(&mut payload, 1); // 1 Any value
        push_nested_any_array(&mut payload, depth);
        let frame = wrap_single_struct(&payload);

        let prod_res = Update::decode_v1(&frame);
        let core_res = decode_update_v1_frame(&frame, &DecodeLimitsCore::default_update());
        assert_eq!(
            prod_res.is_ok(),
            should_accept,
            "prod depth={depth} unexpected: {prod_res:?}"
        );
        assert_eq!(
            core_res.is_ok(),
            should_accept,
            "core depth={depth} unexpected: {core_res:?}"
        );
    }

    // 2. All V1 content tags: 0 (GC), 1 (Deleted), 2 (Json), 3 (Binary), 4
    //    (String), 5 (Embed), 6 (Format), 7 (Type), 8 (Any), 9 (Doc), 10
    //    (Skip).
    let mut item = Vec::new();
    let append_hdr = |buf: &mut Vec<u8>, tag: u8| {
        buf.push(tag);
        if tag != 0 && tag != 10 {
            buf.push(1u8);
            push_var_str(buf, "r");
        }
    };

    let tag_cases: Vec<(u8, Vec<u8>)> = vec![
        (0, vec![3]), // GC(3)
        (1, vec![2]), // Deleted(2)
        (2, {
            let mut v = Vec::new();
            push_var_u64(&mut v, 1);
            push_var_str(&mut v, "a");
            v
        }), // Json(["a"])
        (3, {
            let mut v = Vec::new();
            push_var_u64(&mut v, 2);
            v.extend_from_slice(&[0xde, 0xad]);
            v
        }), // Binary([0xde, 0xad])
        (4, {
            let mut v = Vec::new();
            push_var_str(&mut v, "hi");
            v
        }), // String("hi")
        (5, {
            let mut v = Vec::new();
            push_var_str(&mut v, &serde_json::to_string(&Any::True).unwrap());
            v
        }), // Embed(true)
        (6, {
            let mut v = Vec::new();
            push_var_str(&mut v, "bold");
            push_var_str(&mut v, &serde_json::to_string(&Any::Integer(1)).unwrap());
            v
        }), // Format("bold", 1)
        (7, vec![0]), // Type(Array)
        (8, vec![1, 127 - 7]), // Any([true])
        (9, {
            let mut v = Vec::new();
            push_var_str(&mut v, "subdoc");
            v.push(127 - 9); // Object
            push_var_u64(&mut v, 0);
            v
        }), // Doc("subdoc", {})
        (10, vec![4]), // Skip(4)
    ];

    for (tag, body) in &tag_cases {
        item.clear();
        append_hdr(&mut item, *tag);
        item.extend_from_slice(body);
        let frame = wrap_single_struct(&item);
        assert!(
            decode_update_v1_frame(&frame, &DecodeLimitsCore::default_update()).is_ok(),
            "core rejected valid tag {tag}"
        );
        assert!(
            validate_update_v1(&frame).is_ok(),
            "validate_update_v1 rejected valid tag {tag}"
        );
        assert!(
            Update::decode_v1(&frame).is_ok(),
            "Update::decode_v1 rejected valid tag {tag}"
        );
    }

    // 3. Explicit M1 scope boundary: Embed (tag 5) and Format (tag 6) with
    //    valid
    // UTF-8 that is invalid JSON MUST be accepted by M1 decoder_v1 (UTF-8
    // layer only) and rejected by production Update::decode_v1 (JSON parser).
    let mut bad_embed_item = Vec::new();
    append_hdr(&mut bad_embed_item, 5);
    push_var_str(&mut bad_embed_item, "{not valid json");
    let bad_embed_frame = wrap_single_struct(&bad_embed_item);
    assert!(decode_update_v1_frame(&bad_embed_frame, &DecodeLimitsCore::default_update()).is_ok());
    assert!(Update::decode_v1(&bad_embed_frame).is_err());

    let mut bad_format_item = Vec::new();
    append_hdr(&mut bad_format_item, 6);
    push_var_str(&mut bad_format_item, "bold");
    push_var_str(&mut bad_format_item, "{not valid json");
    let mut bad_format_frame = wrap_single_struct(&bad_format_item);
    assert!(decode_update_v1_frame(&bad_format_frame, &DecodeLimitsCore::default_update()).is_ok());
    assert!(Update::decode_v1(&bad_format_frame).is_err());
    bad_format_frame.clear();
}

#[test]
fn parity_decoder_v1_generic_v1sink_spans_and_events() {
    struct RecordingSink<'a> {
        input: &'a [u8],
        seen: std::collections::HashSet<u64>,
        clients: Vec<(u64, usize)>,
        items: usize,
        gcs: usize,
        skips: usize,
        deletes: Vec<(u64, u64, u64)>,
        any_spans: Vec<Span>,
    }

    impl<'a> RecordingSink<'a> {
        fn assert_span(&self, span: Span) {
            assert!(span.start <= span.end && span.end <= self.input.len());
        }
        fn assert_str_span(&self, span: Span) {
            self.assert_span(span);
            assert!(std::str::from_utf8(&self.input[span.start..span.end]).is_ok());
        }
    }

    impl V1Sink for RecordingSink<'_> {
        fn core_validates_utf8(&self) -> bool {
            true
        }
        fn validate_utf8_early(&mut self, _slot: u8, _span: Span) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_decode_error(&mut self, _err: CodecError, _a: usize, _b: u64) {}
        fn record_client(&mut self, client: u64) -> Result<bool, CodecError> {
            Ok(self.seen.insert(client))
        }
        fn begin_client(&mut self, client: u64, count: usize) -> Result<(), CodecError> {
            self.clients.push((client, count));
            Ok(())
        }
        fn on_gc(&mut self, _id: WireId, len: u64) -> Result<(), CodecError> {
            assert!(len > 0);
            self.gcs += 1;
            Ok(())
        }
        fn on_skip(&mut self, _id: WireId, len: u64) -> Result<(), CodecError> {
            assert!(len > 0);
            self.skips += 1;
            Ok(())
        }
        fn on_item(&mut self, _id: WireId, len: u64, meta: ItemMetaCore) -> Result<(), CodecError> {
            assert!(len > 0);
            self.assert_span(meta.raw_range);
            if let Some(sub) = meta.parent_sub {
                self.assert_str_span(sub);
            }
            self.items += 1;
            Ok(())
        }
        fn on_deleted(&mut self, _len: u64) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_json_start(&mut self, _count: usize) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_json_value(&mut self, value: Span) -> Result<(), CodecError> {
            self.assert_str_span(value);
            Ok(())
        }
        fn on_json_finish(&mut self) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_binary(&mut self, value: Span) -> Result<(), CodecError> {
            self.assert_span(value);
            Ok(())
        }
        fn on_string(&mut self, value: Span) -> Result<(), CodecError> {
            self.assert_str_span(value);
            Ok(())
        }
        fn on_embed(&mut self, value: Span) -> Result<(), CodecError> {
            self.assert_str_span(value);
            Ok(())
        }
        fn on_format(&mut self, key: Span, value: Span) -> Result<(), CodecError> {
            self.assert_str_span(key);
            self.assert_str_span(value);
            Ok(())
        }
        fn on_type(&mut self, _kind: u64, tag: Option<Span>) -> Result<(), CodecError> {
            if let Some(t) = tag {
                self.assert_str_span(t);
            }
            Ok(())
        }
        fn on_any_content_start(&mut self, _count: usize) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_content_value(&mut self) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_content_finish(&mut self) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_doc(&mut self, guid: Span) -> Result<(), CodecError> {
            self.assert_str_span(guid);
            Ok(())
        }
        fn on_any_start(&mut self) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_undefined(&mut self) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_null(&mut self) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_i32(&mut self, _value: i32) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_f32_bits(&mut self, _bits: u32) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_f64_bits(&mut self, _bits: u64) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_i64_bits(&mut self, _bits: u64) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_bool(&mut self, _value: bool) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_str(&mut self, value: Span) -> Result<(), CodecError> {
            self.assert_str_span(value);
            Ok(())
        }
        fn on_any_bytes(&mut self, value: Span) -> Result<(), CodecError> {
            self.assert_span(value);
            Ok(())
        }
        fn on_any_begin_object(&mut self, _count: usize) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_object_key(&mut self, key: Span) -> Result<(), CodecError> {
            self.assert_str_span(key);
            Ok(())
        }
        fn on_any_begin_array(&mut self, _count: usize) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_end_container(&mut self) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_any_finish(&mut self, range: Span) -> Result<(), CodecError> {
            self.assert_span(range);
            self.any_spans.push(range);
            Ok(())
        }
        fn begin_delete_client(&mut self, _client: u64, _count: usize) -> Result<(), CodecError> {
            Ok(())
        }
        fn on_delete_range(&mut self, client: u64, start: u64, end: u64) -> Result<(), CodecError> {
            assert!(start < end);
            self.deletes.push((client, start, end));
            Ok(())
        }
    }

    for fixture in [
        include_bytes!("../src/fixtures/basic.bin").as_slice(),
        include_bytes!("../src/fixtures/with-subdoc.bin").as_slice(),
    ] {
        let mut sink = RecordingSink {
            input: fixture,
            seen: std::collections::HashSet::new(),
            clients: Vec::new(),
            items: 0,
            gcs: 0,
            skips: 0,
            deletes: Vec::new(),
            any_spans: Vec::new(),
        };
        decode_update_v1(fixture, &mut sink, &DecodeLimitsCore::default_update()).unwrap();
        let summary = decode_update_v1_frame(fixture, &DecodeLimitsCore::default_update()).unwrap();
        assert_eq!(sink.clients.len(), summary.clients);
        assert_eq!(sink.items + sink.gcs + sink.skips, summary.structs);
    }
}

// --- `client_blocks` and `yata_store` against `Doc` ---
//
// Replicas edit one root text and exchange updates in any order, twice, and
// as state diffs. Every update a `Doc` applies is decoded from its bytes and
// replayed on a `YataStoreCore`; the harness below only holds structs back
// until the store has what they depend on, which is what the pending queue of
// `Doc` does. Both must then agree on the visible clocks in document order,
// the state vector, the delete set, where every struct starts, and, after
// both collected and merged, on every struct and its origins.

const SEQUENCE_ROOT: &str = "t";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SeqStruct {
    id: IdCore,
    len: u64,
    /// `ContentDeleted` on the wire
    collected: bool,
    left: Option<IdCore>,
    right: Option<IdCore>,
}

struct SeqReader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl SeqReader<'_> {
    fn byte(&mut self) -> u8 {
        let byte = self.bytes[self.pos];
        self.pos += 1;
        byte
    }

    fn var(&mut self) -> u64 {
        let (value, used) = decode_var_u64(&self.bytes[self.pos..]).unwrap();
        self.pos += used;
        value
    }

    fn id(&mut self) -> IdCore {
        IdCore {
            client: self.var(),
            clock: self.var(),
        }
    }

    fn string(&mut self) -> &str {
        let len = self.var() as usize;
        let value = std::str::from_utf8(&self.bytes[self.pos..self.pos + len]).unwrap();
        self.pos += len;
        value
    }
}

/// The items and the delete set of an update V1 of a document that only
/// holds the text `SEQUENCE_ROOT`. A `Skip` is a gap, not a struct.
fn read_sequence_update(bytes: &[u8]) -> (Vec<SeqStruct>, Vec<(u64, u64, u64)>) {
    let mut reader = SeqReader { bytes, pos: 0 };
    let mut structs = Vec::new();
    for _ in 0..reader.var() {
        let count = reader.var();
        let client = reader.var();
        let mut clock = reader.var();
        for _ in 0..count {
            let info = reader.byte();
            if info == 10 {
                clock += reader.var();
                continue;
            }
            assert_ne!(info & 0x1f, 0, "a root text holds no GC struct");
            let left = (info & 0x80 != 0).then(|| reader.id());
            let right = (info & 0x40 != 0).then(|| reader.id());
            if left.is_none() && right.is_none() {
                assert_eq!(reader.var(), 1, "the parent is the root type");
                assert_eq!(reader.string(), SEQUENCE_ROOT);
            }
            let (len, collected) = match info & 0x1f {
                1 => (reader.var(), true),
                4 => (reader.string().encode_utf16().count() as u64, false),
                other => panic!("content {other} is not text"),
            };
            structs.push(SeqStruct {
                id: IdCore { client, clock },
                len,
                collected,
                left,
                right,
            });
            clock += len;
        }
    }
    let mut deleted = Vec::new();
    for _ in 0..reader.var() {
        let client = reader.var();
        for _ in 0..reader.var() {
            let clock = reader.var();
            deleted.push((client, clock, reader.var()));
        }
    }
    assert_eq!(reader.pos, bytes.len(), "update not fully decoded");
    (structs, deleted)
}

/// Adjacent ranges of one client are one range.
fn merge_ranges(mut ranges: Vec<(u64, u64, u64)>) -> Vec<(u64, u64, u64)> {
    ranges.sort_unstable();
    let mut merged: Vec<(u64, u64, u64)> = Vec::new();
    for range in ranges {
        match merged.last_mut() {
            Some(last) if last.0 == range.0 && last.1 + last.2 == range.1 => last.2 += range.2,
            _ => merged.push(range),
        }
    }
    merged
}

struct SeqReplica {
    doc: Doc,
    text: Text,
    outbox: Arc<Mutex<Vec<Vec<u8>>>>,
    _subscription: Subscription,
    core: YataStoreCore,
    /// structs whose dependencies the core does not hold yet
    waiting: Vec<SeqStruct>,
    /// every deleted range received so far
    deleted: Vec<(u64, u64, u64)>,
}

impl SeqReplica {
    fn new(client: u64, gc: bool) -> Self {
        let doc = DocOptions::from_identity(client, "core-parity".into())
            .auto_gc(gc)
            .build();
        let text = doc.get_or_create_text(SEQUENCE_ROOT).unwrap();
        let outbox = Arc::new(Mutex::new(Vec::new()));
        let sink = outbox.clone();
        let subscription = doc.subscribe(move |event| {
            if event.local {
                sink.lock().unwrap().push(event.update.clone());
            }
        });
        Self {
            doc,
            text,
            outbox,
            _subscription: subscription,
            // every other replica keys the hash of its conflict scans: the
            // key changes where a scan looks an id up, never what it answers
            core: if client.is_multiple_of(2) {
                YataStoreCore::new()
            } else {
                YataStoreCore::with_key(client.wrapping_mul(0x9E37_79B9_7F4A_7C15), !client)
            },
            waiting: Vec::new(),
            deleted: Vec::new(),
        }
    }

    fn sent(&self) -> usize {
        self.outbox.lock().unwrap().len()
    }

    fn update(&self, index: usize) -> Vec<u8> {
        self.outbox.lock().unwrap()[index].clone()
    }

    fn known(&self, origin: Option<IdCore>) -> bool {
        origin.is_none_or(|origin| self.core.node_id(origin).is_some())
    }

    /// Replays an update on the core: every struct whose clocks continue the
    /// ones of its client and whose origins are integrated, then every
    /// deletion of clocks the core holds.
    fn replay(&mut self, bytes: &[u8]) {
        let (structs, deleted) = read_sequence_update(bytes);
        self.waiting.extend(structs);
        self.deleted.extend(deleted);
        loop {
            let mut progressed = false;
            for s in std::mem::take(&mut self.waiting) {
                let state = self.core.get_state(s.id.client);
                if s.id.clock + s.len <= state {
                    // a duplicate
                    continue;
                }
                if s.id.clock > state || !self.known(s.left) || !self.known(s.right) {
                    self.waiting.push(s);
                    continue;
                }
                // the core holds a prefix: the rest follows its last clock
                let offset = state - s.id.clock;
                let id = IdCore {
                    client: s.id.client,
                    clock: state,
                };
                let left = if offset > 0 {
                    Some(IdCore {
                        client: s.id.client,
                        clock: state - 1,
                    })
                } else {
                    s.left
                };
                self.core.integrate(id, s.len - offset, left, s.right).unwrap();
                if s.collected {
                    self.core.delete_range(id.client, id.clock, s.id.clock + s.len).unwrap();
                }
                progressed = true;
            }
            if !progressed {
                break;
            }
        }
        for &(client, clock, len) in &self.deleted {
            self.core.delete_range(client, clock, clock + len).unwrap();
        }
    }

    /// A local edit: the core replays the update of its commit.
    fn local(&mut self, edit: impl FnOnce(&mut Text)) {
        let before = self.sent();
        edit(&mut self.text);
        for index in before..self.sent() {
            let bytes = self.update(index);
            self.replay(&bytes);
        }
        self.compare();
    }

    fn apply(&mut self, bytes: &[u8]) {
        self.apply_only(bytes);
        self.compare();
    }

    /// `apply` without the comparison, for runs that compare now and then.
    fn apply_only(&mut self, bytes: &[u8]) {
        self.doc.apply_update_from_binary_v1(bytes).unwrap();
        self.replay(bytes);
    }

    /// The deleted ranges of the timelines of the core.
    fn core_deleted(&self) -> Vec<(u64, u64, u64)> {
        let mut ranges = Vec::new();
        for entry in self.core.clients() {
            for pos in 0..entry.blocks.len() {
                let block = entry.blocks.get(pos).unwrap();
                if block.kind.deleted() {
                    let (start, end) = entry.blocks.range(pos).unwrap();
                    ranges.push((entry.client, start, end - start));
                }
            }
        }
        merge_ranges(ranges)
    }

    /// The invariants the Lean proofs keep, on the running store.
    fn check_core(&self) {
        let mut linked = 0usize;
        let mut cursor = self.core.start();
        let mut prev = None;
        while let Some(idx) = cursor {
            let item = self.core.items()[idx as usize];
            assert_eq!(item.left, prev);
            linked += 1;
            prev = cursor;
            cursor = item.right;
        }
        let mut blocks = 0usize;
        for pair in self.core.clients().windows(2) {
            assert!(pair[0].client < pair[1].client, "timelines by increasing client");
        }
        for entry in self.core.clients() {
            for pos in 0..entry.blocks.len() {
                let block = entry.blocks.get(pos).unwrap();
                let (start, end) = entry.blocks.range(pos).unwrap();
                assert!(start < end);
                let item = self.core.items()[block.kind.item().unwrap() as usize];
                assert_eq!(
                    item.id,
                    IdCore {
                        client: entry.client,
                        clock: start
                    }
                );
                assert_eq!(item.len, end - start);
                assert_eq!(item.deleted, block.kind.deleted());
                assert!(!item.gc || item.deleted);
                blocks += 1;
            }
        }
        assert_eq!(linked, blocks, "the sequence holds every block and nothing else");
    }

    fn compare(&self) {
        self.check_core();
        if self.doc.has_pending_updates() {
            return;
        }
        assert!(self.waiting.is_empty(), "the core waits where the document does not");

        let mut doc_ids = Vec::new();
        for run in self.text.identity_runs().unwrap() {
            let TextInsert::Text(text) = run.insert else {
                panic!("the text only holds strings");
            };
            for offset in 0..text.encode_utf16().count() as u64 {
                doc_ids.push((run.id.client, run.id.clock + offset));
            }
        }
        let mut core_ids = Vec::new();
        for (id, len) in self.core.visible_ids() {
            for offset in 0..len {
                core_ids.push((id.client, id.clock + offset));
            }
        }
        assert_eq!(core_ids, doc_ids, "visible clocks in document order");

        let state = self.doc.get_state_vector();
        let mut clients = 0;
        for (client, clock) in state.iter() {
            assert_eq!(self.core.get_state(*client), *clock, "state of client {client}");
            clients += usize::from(*clock > 0);
        }
        assert_eq!(self.core.clients().len(), clients);

        let mut doc_deleted = Vec::new();
        for (client, ranges) in self.doc.get_delete_sets().iter() {
            for range in ranges {
                doc_deleted.push((*client, range.start, range.end - range.start));
            }
        }
        assert_eq!(self.core_deleted(), merge_ranges(doc_deleted), "delete set");

        // `origin_owner`: every clock belongs to the struct the document
        // encodes it in, or to a part of it
        let (structs, _) = read_sequence_update(&self.doc.encode_update_v1().unwrap());
        for s in &structs {
            for clock in [s.id.clock, s.id.clock + s.len / 2, s.id.clock + s.len - 1] {
                let owner = self
                    .core
                    .node_id(IdCore {
                        client: s.id.client,
                        clock,
                    })
                    .unwrap();
                assert_eq!(owner.client, s.id.client);
                assert!(s.id.clock <= owner.clock && owner.clock <= clock);
            }
            assert_eq!(
                self.core.node_id(IdCore {
                    client: s.id.client,
                    clock: s.id.clock
                }),
                Some(s.id)
            );
        }
    }

    /// `Doc::gc` on both sides: deleted items drop their content and
    /// everything that can merge is merged; then the structs are the same.
    fn collect_and_compare(&mut self) {
        self.doc.gc().unwrap();
        self.core.gc();
        loop {
            let mut merged = false;
            for ci in 0..self.core.clients().len() {
                let mut pos = 0;
                while pos < self.core.clients()[ci].blocks.len() {
                    let id = IdCore {
                        client: self.core.clients()[ci].client,
                        clock: self.core.clients()[ci].blocks.get(pos).unwrap().clock,
                    };
                    if self.core.merge_adjacent(id).unwrap() {
                        merged = true;
                    } else {
                        pos += 1;
                    }
                }
            }
            if !merged {
                break;
            }
        }
        self.compare();
        if self.doc.has_pending_updates() {
            // the encoded state also carries the structs that wait
            return;
        }

        let (mut expected, _) = read_sequence_update(&self.doc.encode_update_v1().unwrap());
        expected.sort_unstable_by_key(|s| (s.id.client, s.id.clock));
        let mut actual = Vec::new();
        for entry in self.core.clients() {
            for pos in 0..entry.blocks.len() {
                let block = entry.blocks.get(pos).unwrap();
                let item = self.core.items()[block.kind.item().unwrap() as usize];
                actual.push(SeqStruct {
                    id: item.id,
                    len: item.len,
                    collected: item.gc,
                    left: item.origin_left,
                    right: item.origin_right,
                });
            }
        }
        actual.sort_unstable_by_key(|s| (s.id.client, s.id.clock));
        assert_eq!(actual, expected, "structs after gc");
    }
}

struct SeqScenario {
    replicas: Vec<SeqReplica>,
    /// `delivered[to][from]`: which updates of `from` reached `to`
    delivered: Vec<Vec<Vec<bool>>>,
}

impl SeqScenario {
    fn new(replicas: &[(u64, bool)]) -> Self {
        let count = replicas.len();
        Self {
            replicas: replicas
                .iter()
                .map(|&(client, gc)| SeqReplica::new(client, gc))
                .collect(),
            delivered: vec![vec![Vec::new(); count]; count],
        }
    }

    fn insert(&mut self, replica: usize, index: u64, text: &str) {
        self.replicas[replica].local(|t| t.insert(index, text).unwrap());
    }

    fn remove(&mut self, replica: usize, index: u64, len: u64) {
        self.replicas[replica].local(|t| t.remove(index, len).unwrap());
    }

    fn deliver(&mut self, from: usize, to: usize, index: usize) {
        let bytes = self.replicas[from].update(index);
        let delivered = &mut self.delivered[to][from];
        if delivered.len() <= index {
            delivered.resize(index + 1, false);
        }
        delivered[index] = true;
        self.replicas[to].apply(&bytes);
    }

    /// Sends `to` what its state vector lacks of the state of `from`.
    fn sync(&mut self, from: usize, to: usize) {
        let state = self.replicas[to].doc.get_state_vector();
        let bytes = self.replicas[from].doc.encode_state_as_update_v1(&state).unwrap();
        self.replicas[to].apply(&bytes);
    }

    fn undelivered(&self, from: usize, to: usize) -> Vec<usize> {
        let delivered = &self.delivered[to][from];
        (0..self.replicas[from].sent())
            .filter(|&index| !delivered.get(index).copied().unwrap_or(false))
            .collect()
    }

    /// Delivers what is still on its way, then every replica collects: all
    /// of them hold the same structs.
    fn settle(&mut self) {
        let count = self.replicas.len();
        for to in 0..count {
            for from in 0..count {
                if from != to {
                    for index in self.undelivered(from, to) {
                        self.deliver(from, to, index);
                    }
                }
            }
        }
        for to in 0..count {
            for from in 0..count {
                if from != to {
                    self.sync(from, to);
                }
            }
        }
        for replica in &mut self.replicas {
            assert!(!replica.doc.has_pending_updates());
            replica.collect_and_compare();
        }
        let text = self.replicas[0].text.to_string();
        let ids = self.replicas[0].core.visible_ids();
        for replica in &self.replicas {
            assert_eq!(replica.text.to_string(), text);
            assert_eq!(replica.core.visible_ids(), ids);
        }
    }
}

#[test]
fn parity_yata_store_conflict_scan_branches() {
    // every replica inserts at the same places before it hears of the others
    let orders: &[[usize; 3]] = if cfg!(miri) {
        &[[0, 1, 2], [2, 1, 0]]
    } else {
        &[[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
    };
    for &order in orders {
        let mut s = SeqScenario::new(&[(5, false), (2, false), (9, false)]);
        s.insert(0, 0, "ab");
        s.deliver(0, 1, 0);
        s.deliver(0, 2, 0);
        // same left origin, different clients; then one inside the other
        s.insert(0, 1, "x");
        s.insert(1, 1, "yy");
        s.insert(2, 1, "z");
        s.insert(2, 2, "w");
        s.insert(1, 2, "v");
        // at the start and at the end of the sequence
        s.insert(0, 0, "s");
        s.insert(1, 0, "t");
        s.insert(2, 4, "e");
        for to in 0..3 {
            for from in order {
                if from != to {
                    for index in s.undelivered(from, to) {
                        s.deliver(from, to, index);
                    }
                }
            }
        }
        s.settle();
    }
}

#[test]
fn parity_yata_store_split_merge_delete_and_gc() {
    let mut s = SeqScenario::new(&[(1, false), (2, true)]);
    s.insert(0, 0, "abcdefgh");
    s.deliver(0, 1, 0);
    // deletions inside one struct, across structs and of deleted clocks
    s.remove(0, 2, 3);
    s.remove(1, 1, 5);
    s.insert(1, 1, "XY");
    s.deliver(1, 0, 0);
    s.deliver(1, 0, 1);
    s.deliver(0, 1, 1);
    s.remove(0, 0, 2);
    s.deliver(0, 1, 2);
    // a split the document never made merges back
    let core = &mut s.replicas[0].core;
    let before = core.visible_ids();
    let blocks: usize = core.clients().iter().map(|entry| entry.blocks.len()).sum();
    let last = core.clients()[0].blocks.end_clock() - 1;
    core.split(IdCore { client: 1, clock: last }).unwrap();
    let after: usize = core.clients().iter().map(|entry| entry.blocks.len()).sum();
    assert!(after == blocks || after == blocks + 1);
    assert_eq!(
        core.visible_ids().iter().map(|(_, len)| len).sum::<u64>(),
        before.iter().map(|(_, len)| len).sum::<u64>()
    );
    s.replicas[0].compare();
    s.settle();
}

/// The clocks `visible_ids` stands for, one by one.
fn visible_clocks(core: &YataStoreCore) -> Vec<(u64, u64)> {
    let mut clocks = Vec::new();
    for (id, len) in core.visible_ids() {
        for offset in 0..len {
            clocks.push((id.client, id.clock + offset));
        }
    }
    clocks
}

fn timeline_blocks(core: &YataStoreCore) -> usize {
    core.clients().iter().map(|entry| entry.blocks.len()).sum()
}

#[test]
fn parity_yata_store_merge_adjacent_answers() {
    let at = |client: u64, clock: u64| IdCore { client, clock };
    let mut s = SeqScenario::new(&[(1, false), (2, false)]);
    // three structs of one client, each typed right after the one before
    s.insert(0, 0, "a");
    s.insert(0, 1, "b");
    s.insert(0, 2, "c");
    for index in 0..3 {
        s.deliver(0, 1, index);
    }
    let clocks = visible_clocks(&s.replicas[0].core);
    assert_eq!(timeline_blocks(&s.replicas[0].core), 3);
    {
        let core = &mut s.replicas[0].core;
        // a struct the store does not hold; the last struct of a timeline
        assert_eq!(core.merge_adjacent(at(9, 0)), Err(StoreError::MissingStruct));
        assert_eq!(core.merge_adjacent(at(1, 3)), Err(StoreError::MissingStruct));
        assert_eq!(core.merge_adjacent(at(1, 2)), Ok(false));
        // any clock of a struct names it: "a" and "b", then "ab" and "c"
        assert_eq!(core.merge_adjacent(at(1, 0)), Ok(true));
        assert_eq!(timeline_blocks(core), 2);
        assert_eq!(core.merge_adjacent(at(1, 1)), Ok(true));
        assert_eq!(timeline_blocks(core), 1);
        assert_eq!(core.merge_adjacent(at(1, 0)), Ok(false));
        assert_eq!(core.visible_ids(), vec![(at(1, 0), 3)]);
    }
    assert_eq!(visible_clocks(&s.replicas[0].core), clocks);
    s.replicas[0].compare();

    // another client types inside the struct: its halves are no neighbours of
    // the sequence any more
    s.insert(1, 1, "X");
    s.deliver(1, 0, 0);
    assert_eq!(timeline_blocks(&s.replicas[0].core), 3);
    assert_eq!(s.replicas[0].core.merge_adjacent(at(1, 0)), Ok(false));
    // a deleted struct and a live one do not merge, two deleted ones do
    s.remove(0, 2, 1);
    assert_eq!(s.replicas[0].core.merge_adjacent(at(1, 1)), Ok(false));
    s.remove(0, 2, 1);
    let clocks = visible_clocks(&s.replicas[0].core);
    let blocks = timeline_blocks(&s.replicas[0].core);
    assert_eq!(s.replicas[0].core.merge_adjacent(at(1, 1)), Ok(true));
    assert_eq!(timeline_blocks(&s.replicas[0].core), blocks - 1);
    assert_eq!(visible_clocks(&s.replicas[0].core), clocks);
    s.replicas[0].compare();
    // one that dropped its content and one that did not do not merge
    s.insert(0, 2, "de");
    s.remove(0, 2, 1);
    s.replicas[0].core.gc();
    s.remove(0, 2, 1);
    let deleted = s.replicas[0].core.clients()[0].blocks.len() - 2;
    let first = s.replicas[0].core.clients()[0].blocks.get(deleted).unwrap().clock;
    assert_eq!(s.replicas[0].core.merge_adjacent(at(1, first)), Ok(false));
    s.replicas[0].core.gc();
    assert_eq!(s.replicas[0].core.merge_adjacent(at(1, first)), Ok(true));
    s.replicas[0].compare();
    for index in s.undelivered(0, 1) {
        s.deliver(0, 1, index);
    }
    s.settle();
}

#[test]
fn parity_yata_store_many_concurrent_writers() {
    // under Miri a few writers: the same branches, hundreds of times slower
    let writers: u64 = if cfg!(miri) { 12 } else { 2_000 };
    // 1 writes "ab"; every writer inserts between the two before it hears of
    // most of the others
    let mut base = SeqReplica::new(1, false);
    base.local(|t| t.insert(0, "ab").unwrap());
    let seed = base.update(0);

    // the writers with an even number saw "ab" only: the same two origins.
    // The ones with an odd number saw what the odd ones before them wrote
    // there, and write left of it: the same left origin, another right
    // origin. Every fifth writer goes on typing after its own first clock.
    // The clients are not in the order of the writers.
    let mut updates: Vec<Vec<u8>> = Vec::new();
    let mut chain = seed.clone();
    for writer in 0..writers {
        let mut doc = DocOptions::from_identity(100 + (writer * 7) % writers, "core-parity".into())
            .auto_gc(false)
            .build();
        let mut text = doc.get_or_create_text(SEQUENCE_ROOT).unwrap();
        doc.apply_update_from_binary_v1(if writer % 2 == 1 { &chain } else { &seed })
            .unwrap();
        assert!(!doc.has_pending_updates());
        let before = doc.get_state_vector();
        text.insert(1, "x").unwrap();
        if writer % 5 == 0 {
            text.insert(2, "yz").unwrap();
        }
        if writer % 2 == 1 {
            chain = doc.encode_update_v1().unwrap();
        }
        updates.push(doc.encode_state_as_update_v1(&before).unwrap());
    }

    // two replicas receive everything, in two orders: as written, and from
    // the last writer back (every odd writer then waits for the one before)
    let mut forward = SeqReplica::new(2, false);
    let mut backward = SeqReplica::new(3, false);
    forward.apply(&seed);
    backward.apply(&seed);
    let every = if cfg!(miri) { 4 } else { 250 };
    for (count, update) in updates.iter().enumerate() {
        forward.apply_only(update);
        if count % every == 0 {
            forward.compare();
        }
    }
    for (count, update) in updates.iter().rev().enumerate() {
        backward.apply_only(update);
        if count % every == 0 {
            backward.compare();
        }
    }
    forward.compare();
    backward.compare();
    assert!(!forward.doc.has_pending_updates() && !backward.doc.has_pending_updates());
    assert_eq!(forward.core.clients().len() as u64, writers + 1);
    assert_eq!(visible_clocks(&forward.core), visible_clocks(&backward.core));
    assert_eq!(forward.text.to_string(), backward.text.to_string());
    assert_eq!(forward.text.len(), 2 + writers + 2 * writers.div_ceil(5));
    forward.collect_and_compare();
    backward.collect_and_compare();
    assert_eq!(forward.core.visible_ids(), backward.core.visible_ids());
}

#[test]
fn parity_yata_store_random_updates_in_any_order() {
    const ALPHABET: [&str; 10] = ["a", "b", "c", "d", "x", "y", "é", "ß", "中", "文"];
    // under Miri a few short runs: the same branches, hundreds of times slower
    let (seeds, steps) = if cfg!(miri) { (2u64, 16) } else { (32, 160) };
    for seed in 0..seeds {
        let replicas: &[(u64, bool)] = if seed % 2 == 0 {
            &[(1, false), (2, false)]
        } else {
            &[(40, true), (7, false), (23, true), (11, false)]
        };
        let count = replicas.len();
        let mut rng = ChaCha20Rng::seed_from_u64(0xC02E_0000 + seed);
        let mut s = SeqScenario::new(replicas);
        for _ in 0..steps {
            let replica = rng.random_range(0..count);
            let len = s.replicas[replica].text.len();
            match rng.random_range(0..100) {
                0..40 => {
                    let index = rng.random_range(0..=len);
                    let text = (0..rng.random_range(1..=4))
                        .map(|_| ALPHABET[rng.random_range(0..ALPHABET.len())])
                        .collect::<String>();
                    s.insert(replica, index, &text);
                }
                40..55 if len > 0 => {
                    let index = rng.random_range(0..len);
                    let span = rng.random_range(1..=(len - index).min(3));
                    s.remove(replica, index, span);
                }
                55..85 => {
                    let from = (replica + rng.random_range(1..count)) % count;
                    let waiting = s.undelivered(from, replica);
                    let sent = s.replicas[from].sent();
                    if !waiting.is_empty() {
                        // mostly in order, sometimes any later update first
                        let pick = if rng.random_range(0..3) == 0 {
                            rng.random_range(0..waiting.len())
                        } else {
                            0
                        };
                        s.deliver(from, replica, waiting[pick]);
                    } else if sent > 0 {
                        // a duplicate
                        s.deliver(from, replica, rng.random_range(0..sent));
                    }
                }
                85..95 => {
                    let from = (replica + rng.random_range(1..count)) % count;
                    s.sync(from, replica);
                }
                95..100 => s.replicas[replica].collect_and_compare(),
                _ => {}
            }
        }
        s.settle();
    }
}

#[test]
fn parity_client_blocks_timeline_of_a_document() {
    // the timeline of one client, rebuilt from the structs a document encodes
    let doc = Doc::with_client(3);
    let mut text = doc.get_or_create_text(SEQUENCE_ROOT).unwrap();
    text.insert(0, "hello world").unwrap();
    text.remove(2, 3).unwrap();
    text.insert(4, "!!").unwrap();
    text.remove(0, 1).unwrap();
    let (mut structs, deleted) = read_sequence_update(&doc.encode_update_v1().unwrap());
    structs.sort_unstable_by_key(|s| s.id.clock);
    let is_deleted = |clock: u64| deleted.iter().any(|d| d.1 <= clock && clock < d.1 + d.2);

    let mut timeline = ClientBlocksCore::new();
    for (slot, s) in structs.iter().enumerate() {
        let kind = if is_deleted(s.id.clock) {
            BlockKindCore::DeletedItem(slot as u32)
        } else {
            BlockKindCore::Item(slot as u32)
        };
        let block = BlockRefCore {
            clock: s.id.clock,
            kind,
        };
        assert_eq!(timeline.append(block, 0), Err(StoreError::ZeroLength));
        timeline.append(block, s.len).unwrap();
    }
    assert_eq!(timeline.end_clock(), doc.get_state_vector().get(&3));
    for (slot, s) in structs.iter().enumerate() {
        assert_eq!(timeline.range(slot), Some((s.id.clock, s.id.clock + s.len)));
        for clock in s.id.clock..s.id.clock + s.len {
            assert_eq!(timeline.find(clock), Some(slot));
            let deleted = doc.get_delete_sets().iter().any(|(_, ranges)| ranges.contains(clock));
            assert_eq!(deleted, timeline.get(slot).unwrap().kind.deleted());
        }
    }
    assert_eq!(timeline.find(timeline.end_clock()), None);
}

/// The item arena `y-octo` had before it ran on `ItemSpaceCore`: the same
/// chunks, free list and quarantine, written with the `Vec` methods the core
/// does without (`pop`, `append`, `truncate`, `shrink_to_fit`).
#[derive(Default)]
struct LegacyItemSpace {
    first: Vec<Option<u64>>,
    rest: Vec<Vec<Option<u64>>>,
    slots: usize,
    free: Vec<u32>,
    quarantine: Vec<u32>,
}

impl LegacyItemSpace {
    fn slot_mut(&mut self, slot: u32) -> Option<&mut Option<u64>> {
        let (chunk, offset) = (slot as usize / CHUNK_SIZE, slot as usize % CHUNK_SIZE);
        if chunk == 0 {
            self.first.get_mut(offset)
        } else {
            self.rest.get_mut(chunk - 1)?.get_mut(offset)
        }
    }

    fn check_capacity(&self, additional: usize, limit: usize) -> bool {
        self.slots
            .checked_sub(self.free.len())
            .and_then(|occupied| occupied.checked_add(additional))
            .is_some_and(|n| n <= limit)
    }

    fn alloc(&mut self, item: u64, limit: usize) -> Result<u32, u64> {
        if !self.check_capacity(1, limit) {
            return Err(item);
        }
        if let Some(slot) = self.free.pop() {
            *self.slot_mut(slot).expect("allocated slot") = Some(item);
            return Ok(slot);
        }
        let slot = self.slots;
        let (chunk, offset) = (slot / CHUNK_SIZE, slot % CHUNK_SIZE);
        if chunk > 0 && offset == 0 {
            self.rest.push(Vec::new());
        }
        if chunk == 0 {
            self.first.push(Some(item));
        } else {
            self.rest[chunk - 1].push(Some(item));
        }
        self.slots += 1;
        Ok(slot as u32)
    }

    fn get(&mut self, slot: u32) -> Option<u64> {
        self.slot_mut(slot).and_then(|cell| *cell)
    }

    fn retire(&mut self, slot: u32) -> Option<u64> {
        let item = self.slot_mut(slot).and_then(Option::take)?;
        self.quarantine.push(slot);
        Some(item)
    }

    fn finish(&mut self) -> Option<Vec<u32>> {
        self.free.append(&mut self.quarantine);
        let compact = self.slots >= 256 && self.free.len() as u64 * 5 > self.slots as u64 * 2;
        if !compact && self.free.len() != self.slots {
            return None;
        }
        if self.free.is_empty() {
            return None;
        }
        let mut remap = vec![0u32; self.slots];
        let mut live = 0u32;
        for (slot, entry) in remap.iter_mut().enumerate() {
            let source = self.slot_mut(slot as u32).expect("allocated slot");
            if source.is_none() {
                continue;
            }
            if slot as u32 != live {
                let item = source.take();
                *self.slot_mut(live).expect("allocated slot") = item;
            }
            live += 1;
            *entry = live;
        }
        if let Some(last) = (live as usize).checked_sub(1) {
            let (chunk, offset) = (last / CHUNK_SIZE, last % CHUNK_SIZE);
            self.rest.truncate(chunk);
            let tail = if chunk == 0 {
                &mut self.first
            } else {
                &mut self.rest[chunk - 1]
            };
            tail.truncate(offset + 1);
            tail.shrink_to_fit();
        } else {
            self.first = Vec::new();
            self.rest.clear();
        }
        self.rest.shrink_to_fit();
        self.free = Vec::new();
        self.quarantine = Vec::new();
        self.slots = live as usize;
        Some(remap)
    }
}

#[test]
fn parity_item_space_with_the_arena_it_replaces() {
    let (seeds, rounds) = if cfg!(miri) { (1u64, 1_500) } else { (6, 40_000) };
    for seed in 0..seeds {
        let mut rng = ChaCha20Rng::seed_from_u64(0x17E3_0000 + seed);
        let mut core = ItemSpaceCore::<u64>::new();
        let mut legacy = LegacyItemSpace::default();
        // a low limit on some runs, so that the arena fills up
        let limit = if seed % 2 == 0 { MAX_SLOTS } else { 2 * CHUNK_SIZE + 300 };
        for round in 0..rounds {
            // growth, then mass retirement: both answers of `finish` happen
            let shrinking = (round / 3_000) % 2 == 1;
            match rng.random_range(0..if shrinking { 16 } else { 10 }) {
                0..5 => {
                    let item: u64 = rng.random();
                    assert_eq!(core.alloc(item, limit), legacy.alloc(item, limit));
                }
                5..7 | 10..16 => {
                    let slot = rng.random_range(0..legacy.slots as u32 + 3);
                    assert_eq!(core.retire(slot), legacy.retire(slot));
                }
                7 => {
                    let before = core.chunk_count();
                    let moved = core.finish();
                    assert_eq!(moved, legacy.finish());
                    if moved.is_some() {
                        assert!(core.chunk_count() <= before);
                        assert_eq!(
                            core.allocated_capacity(),
                            core.slots(),
                            "no slot is kept for an item that is gone"
                        );
                        assert_eq!((core.free_slots(), core.quarantined()), (0, 0));
                    }
                }
                8 => {
                    let a = rng.random_range(0..legacy.slots as u32 + 2);
                    let b = rng.random_range(0..legacy.slots as u32 + 2);
                    let expected = (a != b).then(|| legacy.get(a).zip(legacy.get(b))).flatten();
                    assert_eq!(core.get_two_mut(a, b).map(|(x, y)| (*x, *y)), expected);
                    if let Some((x, y)) = core.get_two_mut(a, b) {
                        // written through the two borrows, in the order asked
                        *x ^= 1;
                        *y ^= 2;
                        *legacy.slot_mut(a).unwrap().as_mut().unwrap() ^= 1;
                        *legacy.slot_mut(b).unwrap().as_mut().unwrap() ^= 2;
                    }
                }
                _ => {
                    let slot = rng.random_range(0..legacy.slots as u32 + 2);
                    let item: u64 = rng.random();
                    if let Some(held) = core.get_mut(slot) {
                        *held = item;
                        *legacy.slot_mut(slot).unwrap() = Some(item);
                    }
                    assert_eq!(core.get(slot).copied(), legacy.get(slot));
                }
            }
            assert_eq!(core.slots(), legacy.slots);
            assert_eq!(core.free_slots(), legacy.free.len());
            assert_eq!(core.quarantined(), legacy.quarantine.len());
            assert_eq!(core.chunk_count(), 1 + legacy.rest.len());
            for additional in [0, 1, 2, limit, usize::MAX] {
                assert_eq!(
                    core.check_capacity(additional, limit),
                    legacy.check_capacity(additional, limit)
                );
            }
            if round % 251 == 0 {
                for slot in 0..legacy.slots as u32 + 1 {
                    assert_eq!(core.get(slot).copied(), legacy.get(slot));
                }
            }
        }
        for slot in 0..legacy.slots as u32 + 1 {
            assert_eq!(core.get(slot).copied(), legacy.get(slot));
        }
    }
}

#[test]
fn parity_item_space_of_a_document_that_collects_most_of_its_items() {
    // the arena behind a document: a subtree is collected, the arena moves the
    // items that are left, and the document reads, encodes and syncs as a
    // replica that never held the subtree's items in its arena
    let count = if cfg!(miri) { 96 } else { 6_000 };
    let doc = Doc::with_client(7);
    let mut text = doc.get_or_create_text(SEQUENCE_ROOT).unwrap();
    for i in 0..count {
        // one item each: the cursor moves back and forth
        text.insert(if i % 2 == 0 { 0 } else { text.len() }, "ab").unwrap();
    }
    let kept = text.to_string();
    let mut doomed = doc.get_or_create_text("doomed").unwrap();
    for i in 0..4 * count {
        doomed.insert(if i % 2 == 0 { 0 } else { doomed.len() }, "x").unwrap();
    }
    doomed.remove(0, doomed.len()).unwrap();
    doc.gc().unwrap();
    assert_eq!(text.to_string(), kept);
    // the items still answer after the move, and new ones go in
    text.insert(1, "!").unwrap();
    text.remove(0, 1).unwrap();
    let mut peer = Doc::with_client(8);
    peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
        .unwrap();
    let peer_text = peer.get_or_create_text(SEQUENCE_ROOT).unwrap();
    assert_eq!(peer_text.to_string(), text.to_string());
    assert_eq!(peer.get_state_vector(), doc.get_state_vector());
    assert_eq!(peer.get_delete_sets(), doc.get_delete_sets());
}

#[test]
fn parity_id_set_keyed_and_cleared_with_a_hash_set() {
    use std::collections::HashSet;
    let (seeds, rounds) = if cfg!(miri) { (2u64, 400) } else { (24, 6_000) };
    for seed in 0..seeds {
        let mut rng = ChaCha20Rng::seed_from_u64(0x1D5E_0000 + seed);
        let mut set = match seed % 3 {
            0 => IdSetCore::new(),
            1 => IdSetCore::with_key(0, 0),
            _ => IdSetCore::with_key(rng.random(), rng.random()),
        };
        let mut reference: HashSet<(u64, u64)> = HashSet::new();
        // ids a peer would choose to collide in a table that is not keyed:
        // few clients, clocks that differ in high bits only
        let id_of = |rng: &mut ChaCha20Rng| -> (u64, u64) {
            match rng.random_range(0..4) {
                0 => (rng.random_range(0..4), rng.random_range(0..64)),
                1 => (rng.random_range(0..4), rng.random_range(0..64u64) << 40),
                2 => (rng.random_range(0..64u64) << 44, 5),
                _ => (rng.random(), rng.random()),
            }
        };
        for _ in 0..rounds {
            let (client, clock) = id_of(&mut rng);
            let id = IdCore { client, clock };
            match rng.random_range(0..100) {
                0..60 => {
                    assert!(set.insert(id));
                    reference.insert((client, clock));
                }
                60..97 => assert_eq!(set.contains(id), reference.contains(&(client, clock))),
                97..99 => {
                    set.clear();
                    reference.clear();
                    assert!(!set.contains(id));
                }
                // a set that is emptied again and again, as the scan does
                // after every candidate it takes
                _ => {
                    for clock in 0..rng.random_range(1..40u64) {
                        set.clear();
                        reference.clear();
                        assert!(set.is_empty());
                        assert!(set.insert(IdCore { client, clock }));
                        reference.insert((client, clock));
                    }
                }
            }
            assert_eq!(set.len(), reference.len());
            assert_eq!(set.is_empty(), reference.is_empty());
        }
        for &(client, clock) in &reference {
            assert!(set.contains(IdCore { client, clock }));
        }
    }
}

#[test]
fn parity_id_order_with_a_list_searched_by_hand() {
    // the candidates of a conflict scan are distinct ids: the place the
    // list answers is then the only one, and the two sets the scan had
    // before are read off it
    use std::collections::HashSet;
    let (seeds, rounds) = if cfg!(miri) { (2u64, 300) } else { (24, 5_000) };
    for seed in 0..seeds {
        let mut rng = ChaCha20Rng::seed_from_u64(0x1D0D_0000 + seed);
        let mut order = IdOrderCore::new();
        if seed % 3 != 0 {
            order.key(rng.random(), rng.random());
        }
        let mut list: Vec<(u64, u64)> = Vec::new();
        let mut before_origin: HashSet<(u64, u64)> = HashSet::new();
        let mut conflicting: HashSet<(u64, u64)> = HashSet::new();
        let mut conflict_from = 0usize;
        let mut last = 0usize;
        // ids a peer would choose to collide in a table that is not keyed
        let id_of = |rng: &mut ChaCha20Rng| -> (u64, u64) {
            match rng.random_range(0..4) {
                0 => (rng.random_range(0..4), rng.random_range(0..512)),
                1 => (rng.random_range(0..4), rng.random_range(0..512u64) << 40),
                2 => (rng.random_range(0..512u64) << 44, 5),
                _ => (rng.random(), rng.random()),
            }
        };
        for _ in 0..rounds {
            let (client, clock) = id_of(&mut rng);
            let id = IdCore { client, clock };
            match rng.random_range(0..100) {
                0..55 => {
                    if before_origin.insert((client, clock)) {
                        assert!(order.push(id));
                        list.push((client, clock));
                        conflicting.insert((client, clock));
                    }
                }
                // the scan takes a candidate: nothing conflicts after it
                55..60 => {
                    conflict_from = order.len();
                    conflicting.clear();
                }
                60..80 => {
                    // the place answered last, then the last `RECENT` ones
                    let from = list.len().saturating_sub(RECENT);
                    let expected = if list.get(last) == Some(&(client, clock)) {
                        Recent::At(last)
                    } else {
                        match list[from..].iter().position(|held| *held == (client, clock)) {
                            Some(at) => Recent::At(from + at),
                            None if from == 0 => Recent::Absent,
                            None => Recent::Far,
                        }
                    };
                    assert_eq!(order.recent(id), expected);
                    if let Recent::At(at) = expected {
                        last = at;
                    }
                }
                _ => {
                    let at = order.position(id);
                    if let Some(at) = at {
                        last = at;
                    }
                    assert_eq!(at, list.iter().position(|held| *held == (client, clock)));
                    assert_eq!(at.is_some(), before_origin.contains(&(client, clock)));
                    assert_eq!(
                        at.is_some_and(|at| at >= conflict_from),
                        conflicting.contains(&(client, clock))
                    );
                }
            }
            assert_eq!(order.len(), list.len());
            assert_eq!(order.is_empty(), list.is_empty());
        }
        for (at, &(client, clock)) in list.iter().enumerate() {
            assert_eq!(order.position(IdCore { client, clock }), Some(at));
        }
    }
}

/// The scan for a missing dependency `y-octo` ran before it called the core.
fn legacy_find_missing_dependency(
    id: Id,
    origin_left: Option<Id>,
    origin_right: Option<Id>,
    parent: Option<Id>,
    state: &StateVector,
) -> Option<u64> {
    for dependency in [origin_left, origin_right, parent].into_iter().flatten() {
        if dependency.client != id.client && dependency.clock >= state.get(&dependency.client) {
            return Some(dependency.client);
        }
    }
    None
}

/// What `UpdateIterator::next` of `y-octo` did with one struct before it
/// called the core, as the answer the core gives: the branches of its `if`
/// chain, in their order.
fn legacy_struct_step(id: Id, len: u64, is_skip: bool, state: &StateVector, missing_dep: Option<u64>) -> StructStep {
    if is_skip {
        StructStep::Skip
    } else if !state.contains(&id) {
        StructStep::MissingLocal {
            client: id.client,
            missing_clock: id.clock - 1,
        }
    } else if let Some(client) = missing_dep {
        StructStep::MissingDep { client }
    } else {
        let local_state = state.get(&id.client);
        let offset = local_state - id.clock;
        if offset == 0 || offset < len {
            StructStep::Apply {
                offset,
                next_state: id.clock + len,
            }
        } else {
            StructStep::AlreadyApplied
        }
    }
}

#[test]
fn parity_pending_struct_decisions_with_the_iterator_they_replace() {
    let core = |id: Id| IdCore {
        client: id.client,
        clock: id.clock,
    };
    let clocks: &[u64] = if cfg!(miri) {
        &[0, 4, 9]
    } else {
        &[0, 1, 2, 3, 4, 5, 6, 9]
    };
    let lens: &[u64] = if cfg!(miri) { &[0, 1, 5] } else { &[0, 1, 2, 3, 5] };
    let deps: &[Option<Id>] = if cfg!(miri) {
        &[
            None,
            Some(Id::new(1, 0)),
            Some(Id::new(2, 3)),
            Some(Id::new(2, 4)),
            Some(Id::new(3, 0)),
        ]
    } else {
        &[
            None,
            Some(Id::new(1, 0)),
            Some(Id::new(1, 7)),
            Some(Id::new(2, 0)),
            Some(Id::new(2, 3)),
            Some(Id::new(2, 4)),
            Some(Id::new(3, 0)),
            Some(Id::new(3, 1)),
        ]
    };
    let helds: &[u64] = if cfg!(miri) { &[0, 4] } else { &[0, 1, 4, 5, 6, 12] };
    for &held in helds {
        let mut state = StateVector::default();
        let mut core_state = StateVectorCore::new();
        // client 3 is unknown to the document
        for (client, clock) in [(1, held), (2, 4)] {
            if clock > 0 {
                state.set_max(client, clock);
                core_state.set_max(client, clock);
            }
        }
        for &clock in clocks {
            let id = Id::new(1, clock);
            for &left in deps {
                for &right in deps {
                    for &parent in deps {
                        let expected = legacy_find_missing_dependency(id, left, right, parent, &state);
                        let (l, r, p) = (left.map(core), right.map(core), parent.map(core));
                        assert_eq!(find_missing_dependency(core(id), l, r, p, &core_state), expected);
                        let of = |dep: Option<Id>| dep.map_or(0, |dep| state.get(&dep.client));
                        assert_eq!(
                            find_missing_dependency_states(1, l, of(left), r, of(right), p, of(parent)),
                            expected
                        );
                        // one dependency at a time, as `y-octo` asks
                        let one_by_one = [left, right, parent]
                            .into_iter()
                            .find_map(|dep| dep_missing(1, dep.map(core), of(dep)));
                        assert_eq!(one_by_one, expected);
                    }
                }
            }
            for &len in lens {
                for is_skip in [false, true] {
                    for missing in [None, Some(2), Some(3)] {
                        let expected = legacy_struct_step(id, len, is_skip, &state, missing);
                        let local_state = state.get(&1);
                        assert_eq!(
                            classify_struct_step(core(id), len, is_skip, local_state, missing),
                            expected
                        );
                        // the two steps `y-octo` takes
                        let two_steps = match check_local_readiness(core(id), is_skip, local_state) {
                            LocalStep::Skip => StructStep::Skip,
                            LocalStep::MissingLocal { client, missing_clock } => {
                                StructStep::MissingLocal { client, missing_clock }
                            }
                            LocalStep::Ready => classify_ready_step(core(id), len, local_state, missing),
                        };
                        assert_eq!(two_steps, expected);
                        // a skip is decided without the state
                        if is_skip {
                            assert_eq!(check_local_readiness(core(id), true, 0), LocalStep::Skip);
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn parity_pending_delete_ranges_with_the_delete_set_iterator() {
    let (seeds, clients) = if cfg!(miri) { (6u64, 3u64) } else { (200, 6) };
    for seed in 0..seeds {
        let mut rng = ChaCha20Rng::seed_from_u64(0xDE1E_0000 + seed);
        // an update without structs, with a delete set of ranges that
        // neither touch nor overlap
        let mut bytes = Vec::new();
        push_var_u64(&mut bytes, 0);
        push_var_u64(&mut bytes, clients);
        let mut ranges: Vec<(u64, ClockRange)> = Vec::new();
        for client in 1..=clients {
            push_var_u64(&mut bytes, client);
            let count = rng.random_range(1..5u64);
            push_var_u64(&mut bytes, count);
            let mut clock = 0u64;
            for _ in 0..count {
                clock += rng.random_range(1..6u64);
                let len = rng.random_range(1..6u64);
                push_var_u64(&mut bytes, clock);
                push_var_u64(&mut bytes, len);
                ranges.push((
                    client,
                    ClockRange {
                        start: clock,
                        end: clock + len,
                    },
                ));
                clock += len;
            }
        }
        let mut state = StateVector::default();
        for client in 1..=clients {
            // some clients are unknown to the document
            if rng.random_range(0..4) > 0 {
                state.set_max(client, rng.random_range(1..30));
            }
        }

        let mut update = Update::decode_v1(&bytes).unwrap();
        let mut applied: Vec<(u64, u64, u64)> = update
            .delete_set_iter(state.clone())
            .map(|(client, range)| (client, range.start, range.end))
            .collect();
        applied.sort_unstable();

        let mut expected = Vec::new();
        for (client, range) in &ranges {
            let local_state = state.get(client);
            let split = split_delete_range(range.start, range.end, local_state);
            if let Some(part) = split.applicable {
                assert!(part.start == range.start && part.end == range.end.min(local_state));
                expected.push((*client, part.start, part.end));
            }
            if let Some(part) = split.pending {
                assert!(part.start == range.start.max(local_state) && part.end == range.end);
            }
            // every clock is in one part, on its side of the state
            for clock in range.start..range.end {
                let within = |part: Option<ClockRange>| part.is_some_and(|p| p.start <= clock && clock < p.end);
                assert_eq!(within(split.applicable), clock < local_state);
                assert_eq!(within(split.pending), clock >= local_state);
            }
        }
        expected.sort_unstable();
        assert_eq!(applied, expected);
        // nothing is handed out twice: the iterator is done
        assert_eq!(update.delete_set_iter(state).count(), 0);
    }
}

#[test]
fn parity_pending_deletes_wait_for_the_structs_they_delete() {
    // the document side of the cut: a delete that arrives before the text it
    // deletes waits, in part or as a whole, and is applied when the text is
    // there
    let author = Doc::with_client(1);
    let mut text = author.get_or_create_text(SEQUENCE_ROOT).unwrap();
    let updates = Arc::new(Mutex::new(Vec::<Vec<u8>>::new()));
    let sink = updates.clone();
    let _subscription: Subscription = author.subscribe(move |event| {
        if event.local {
            sink.lock().unwrap().push(event.update.clone());
        }
    });
    text.insert(0, "hello").unwrap();
    text.insert(5, " world").unwrap();
    text.remove(3, 5).unwrap();
    text.insert(3, "p!").unwrap();
    let updates = updates.lock().unwrap().clone();
    assert_eq!(updates.len(), 4);
    let expected = text.to_string();

    // every order of the four updates
    let mut orders = vec![vec![]];
    for _ in 0..updates.len() {
        orders = orders
            .into_iter()
            .flat_map(|order: Vec<usize>| {
                (0..updates.len())
                    .filter(|i| !order.contains(i))
                    .map(|i| [order.clone(), vec![i]].concat())
                    .collect::<Vec<_>>()
            })
            .collect();
    }
    assert_eq!(orders.len(), 24);
    let orders = if cfg!(miri) { &orders[..6] } else { &orders[..] };
    for order in orders {
        let mut replica = Doc::with_client(2);
        for &i in order {
            replica.apply_update_from_binary_v1(updates[i].clone()).unwrap();
        }
        let replica_text = replica.get_or_create_text(SEQUENCE_ROOT).unwrap();
        assert_eq!(replica_text.to_string(), expected, "order {order:?}");
        assert_eq!(replica.get_state_vector(), author.get_state_vector());
        assert_eq!(replica.get_delete_sets(), author.get_delete_sets());
    }
}

// --- `doc_kernel` and `yata_store` against `Doc`: a map key ---
//
// Replicas set and remove one key of a root map and exchange what they hold
// in any order. The list of the key is replayed on a `YataStoreCore` made
// with a key of its own, and a value is linked there as
// `decide_integrate_link` says: at the end of the list it takes the key and
// the value before it is deleted, anywhere else it is deleted itself. Both
// must agree on the value of the key and on every deleted clock.

struct KeyReplica {
    doc: Doc,
    map: Map,
    core: YataStoreCore,
    /// the structs the replica holds, in the order it took them
    known: Vec<(IdCore, Option<IdCore>)>,
}

impl KeyReplica {
    fn new(client: u64, gc: bool, key: (u64, u64)) -> Self {
        let doc = DocOptions::from_identity(client, "core-parity-key".into())
            .auto_gc(gc)
            .build();
        let map = doc.get_or_create_map("m").unwrap();
        Self {
            doc,
            map,
            core: YataStoreCore::with_key(key.0, key.1),
            known: Vec::new(),
        }
    }

    /// The clocks of the list of the core, with whether each is deleted.
    fn clocks(&self) -> Vec<(u64, u64, bool)> {
        let mut clocks = Vec::new();
        let mut cursor = self.core.start();
        while let Some(idx) = cursor {
            let item = self.core.items()[idx as usize];
            clocks.extend((item.id.clock..item.id.clock + item.len).map(|clock| (item.id.client, clock, item.deleted)));
            cursor = item.right;
        }
        clocks
    }

    fn integrate(&mut self, id: IdCore, origin_left: Option<IdCore>) {
        let idx = self.core.integrate(id, 1, origin_left, None).unwrap();
        let item = self.core.items()[idx as usize];
        let plan = decide_integrate_link(item.left.is_some(), item.right.is_some(), true, false, true);
        if plan.delete_prev_map_winner {
            let left = self.core.items()[item.left.unwrap() as usize];
            self.core
                .delete_range(left.id.client, left.id.clock, left.id.clock + left.len)
                .unwrap();
        }
        if plan.delete_self {
            self.core.delete_range(id.client, id.clock, id.clock + 1).unwrap();
        }
        self.known.push((id, origin_left));
    }

    fn set(&mut self, value: &str) {
        let client = self.doc.client();
        let id = IdCore {
            client,
            clock: self.core.get_state(client),
        };
        // a new value is typed after the last clock of the key
        let origin_left = self.clocks().last().map(|&(client, clock, _)| IdCore { client, clock });
        self.map.insert("k".into(), value).unwrap();
        self.integrate(id, origin_left);
    }

    fn remove(&mut self) {
        self.map.remove("k");
        if let Some(&(client, clock, false)) = self.clocks().last() {
            self.core.delete_range(client, clock, clock + 1).unwrap();
        }
    }

    fn receive(&mut self, from: &KeyReplica) {
        self.doc
            .apply_update_from_binary_v1(from.doc.encode_update_v1().unwrap())
            .unwrap();
        for (id, origin_left) in from.known.clone() {
            if self.core.node_id(id).is_none() {
                self.integrate(id, origin_left);
            }
        }
        for (client, clock, deleted) in from.clocks() {
            if deleted {
                self.core.delete_range(client, clock, clock + 1).unwrap();
            }
        }
    }

    fn check(&self, values: &std::collections::HashMap<(u64, u64), String>) {
        let clocks = self.clocks();
        // at most the last clock of the key is not deleted, and it is the value
        let expected = match clocks.split_last() {
            Some((last, before)) => {
                assert!(before.iter().all(|(_, _, deleted)| *deleted), "{clocks:?}");
                (!last.2).then(|| values[&(last.0, last.1)].clone())
            }
            None => None,
        };
        let value = match self.map.get("k") {
            Some(Value::Any(Any::String(value))) => Some(value),
            None => None,
            other => panic!("the value of the key is {other:?}"),
        };
        assert_eq!(value, expected, "{clocks:?}");
        let mut deleted = DeleteSet::default();
        for (client, clock, _) in clocks.iter().filter(|(_, _, deleted)| *deleted) {
            deleted.add_range(*client, *clock..*clock + 1);
        }
        assert_eq!(self.doc.get_delete_sets(), deleted);
        for (client, clock, _) in &clocks {
            assert!(self.doc.get_state_vector().get(client) > *clock);
        }
    }
}

fn exchange(replicas: &mut [KeyReplica], to: usize, from: usize) {
    if from != to {
        let (low, high) = replicas.split_at_mut(from.max(to));
        if from < to {
            high[0].receive(&low[from]);
        } else {
            low[to].receive(&high[0]);
        }
    }
}

#[test]
fn parity_map_key_with_the_list_the_kernel_links() {
    let mut rng = ChaCha20Rng::seed_from_u64(0x6b65_795f_6c77_7721);
    let rounds = if cfg!(miri) { 2 } else { 40 };
    let steps = if cfg!(miri) { 30 } else { 150 };
    for round in 0..rounds {
        let count = rng.random_range(2..5usize);
        let mut replicas: Vec<KeyReplica> = (0..count)
            .map(|at| KeyReplica::new(at as u64 + 1, (at + round) % 2 == 0, (rng.random(), rng.random())))
            .collect();
        let mut values = std::collections::HashMap::new();
        for step in 0..steps {
            let at = rng.random_range(0..count);
            match rng.random_range(0..10u32) {
                0..=3 => {
                    let client = at as u64 + 1;
                    let value = format!("{round}/{step}");
                    values.insert((client, replicas[at].core.get_state(client)), value.clone());
                    replicas[at].set(&value);
                }
                4 => replicas[at].remove(),
                _ => {
                    let from = rng.random_range(0..count);
                    exchange(&mut replicas, at, from);
                }
            }
            replicas[at].check(&values);
        }
        // everybody takes what everybody holds: one list, one value
        for _ in 0..2 {
            for to in 0..count {
                for from in 0..count {
                    exchange(&mut replicas, to, from);
                }
            }
        }
        let first = replicas[0].clocks();
        for replica in &replicas {
            replica.check(&values);
            assert_eq!(replica.clocks(), first, "round {round}");
            assert_eq!(replica.map.get("k"), replicas[0].map.get("k"));
        }
    }
}
