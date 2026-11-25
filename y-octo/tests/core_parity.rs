use std::sync::{Arc, Mutex};

use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha20Rng;
use y_octo::{
    Any, DeleteSet, Doc, DocOptions, Id, OrderRange, StateVector, Subscription, Text, TextInsert, Update, read_var_i32,
    read_var_u64, validate_update_v1, write_var_i32, write_var_u64,
};
use y_octo_core::{
    CodecError,
    client_blocks::{BlockKindCore, BlockRefCore, ClientBlocksCore, StoreError},
    clock_search::find_clock_segment,
    decoder_v1::{DecodeLimitsCore, decode_state_vector_v1, decode_update_v1_frame},
    delete_set::DeleteSetCore,
    order_range::OrderRange as CoreOrderRange,
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
    for _ in 0..80 {
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
    let bad_format_frame = wrap_single_struct(&bad_format_item);
    assert!(decode_update_v1_frame(&bad_format_frame, &DecodeLimitsCore::default_update()).is_ok());
    assert!(Update::decode_v1(&bad_format_frame).is_err());
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
            core: YataStoreCore::new(),
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
        self.doc.apply_update_from_binary_v1(bytes).unwrap();
        self.replay(bytes);
        self.compare();
    }

    /// The deleted ranges of the timelines of the core.
    fn core_deleted(&self) -> Vec<(u64, u64, u64)> {
        let mut ranges = Vec::new();
        for entry in &self.core.clients {
            for (pos, block) in entry.blocks.blocks.iter().enumerate() {
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
        let mut cursor = self.core.start;
        let mut prev = None;
        while let Some(idx) = cursor {
            let item = self.core.items[idx as usize];
            assert_eq!(item.left, prev);
            linked += 1;
            prev = cursor;
            cursor = item.right;
        }
        let mut blocks = 0usize;
        for entry in &self.core.clients {
            for (pos, block) in entry.blocks.blocks.iter().enumerate() {
                let (start, end) = entry.blocks.range(pos).unwrap();
                assert!(start < end);
                let item = self.core.items[block.kind.item().unwrap() as usize];
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
        assert_eq!(self.core.clients.len(), clients);

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
            for ci in 0..self.core.clients.len() {
                let mut pos = 0;
                while pos < self.core.clients[ci].blocks.len() {
                    let id = IdCore {
                        client: self.core.clients[ci].client,
                        clock: self.core.clients[ci].blocks.blocks[pos].clock,
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
        for entry in &self.core.clients {
            for block in &entry.blocks.blocks {
                let item = self.core.items[block.kind.item().unwrap() as usize];
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
    for order in [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
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
    let blocks: usize = core.clients.iter().map(|entry| entry.blocks.len()).sum();
    let last = core.clients[0].blocks.end_clock - 1;
    core.split(IdCore { client: 1, clock: last }).unwrap();
    let after: usize = core.clients.iter().map(|entry| entry.blocks.len()).sum();
    assert!(after == blocks || after == blocks + 1);
    assert_eq!(
        core.visible_ids().iter().map(|(_, len)| len).sum::<u64>(),
        before.iter().map(|(_, len)| len).sum::<u64>()
    );
    s.replicas[0].compare();
    s.settle();
}

#[test]
fn parity_yata_store_random_updates_in_any_order() {
    const ALPHABET: [&str; 10] = ["a", "b", "c", "d", "x", "y", "é", "ß", "中", "文"];
    // under Miri a few short runs: the same branches, hundreds of times slower
    let (seeds, steps) = if cfg!(miri) { (2u64, 40) } else { (32, 160) };
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
    assert_eq!(timeline.end_clock, doc.get_state_vector().get(&3));
    for (slot, s) in structs.iter().enumerate() {
        assert_eq!(timeline.range(slot), Some((s.id.clock, s.id.clock + s.len)));
        for clock in s.id.clock..s.id.clock + s.len {
            assert_eq!(timeline.find(clock), Some(slot));
            let deleted = doc.get_delete_sets().iter().any(|(_, ranges)| ranges.contains(clock));
            assert_eq!(deleted, timeline.blocks[slot].kind.deleted());
        }
    }
    assert_eq!(timeline.find(timeline.end_clock), None);
}
