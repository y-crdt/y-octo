//! A V1 delete set may list its ranges in any order and repeat a client block.
//! Every decoder must read that to the same canonical set, without the
//! quadratic cost of inserting each range into the middle of a sorted list.
#![allow(clippy::single_range_in_vec_init)]

use std::{
    ops::Range,
    time::{Duration, Instant},
};

use y_octo::{CrdtWriter, Doc, DocOptions, OrderRange, RawEncoder, ReadDoc, StateVector, Update, diff_update_v1};

/// Far above every low clock of the sparse batches.
const HIGH: u64 = 1 << 40;

/// Delete-set blocks in wire order: a client and its ranges.
type Blocks = Vec<(u64, Vec<Range<u64>>)>;

/// Debug builds take a second or two here; the margin is for sanitizer jobs
/// and loaded runners. The quadratic path takes longer even in release.
const BUDGET: Duration = Duration::from_secs(10);
/// A linear merge sorts nothing, so it gets a tighter limit.
const MERGE_BUDGET: Duration = Duration::from_secs(2);
/// Sparse batches stay at logarithmic cost per range.
const SPARSE_BUDGET: Duration = Duration::from_secs(5);
const REMOVE_BUDGET: Duration = Duration::from_secs(12);

fn scale() -> u64 {
    if cfg!(miri) { 64 } else { 400_000 }
}

/// Disjoint, non-adjacent ranges ordered so each lands in the middle of those
/// before it: lowest, highest, second lowest, second highest, ...
fn inward_ranges(count: u64) -> Vec<Range<u64>> {
    let (mut low, mut high) = (0, count);
    let mut ranges = Vec::with_capacity(count as usize);
    while low < high {
        ranges.push(low * 2..low * 2 + 1);
        low += 1;
        if low < high {
            high -= 1;
            ranges.push(high * 2..high * 2 + 1);
        }
    }
    ranges
}

fn write_delete_set(out: &mut RawEncoder, blocks: &[(u64, Vec<Range<u64>>)]) {
    out.write_var_u64(blocks.len() as u64).unwrap();
    for (client, ranges) in blocks {
        out.write_var_u64(*client).unwrap();
        out.write_var_u64(ranges.len() as u64).unwrap();
        for range in ranges {
            out.write_var_u64(range.start).unwrap();
            out.write_var_u64(range.end - range.start).unwrap();
        }
    }
}

/// An update with no structs and exactly these delete-set blocks.
fn deletes_only(blocks: &[(u64, Vec<Range<u64>>)]) -> Vec<u8> {
    let mut out = RawEncoder::default();
    out.write_var_u64(0).unwrap();
    write_delete_set(&mut out, blocks);
    out.into_inner()
}

/// `base`, a full update with an empty delete set, with these blocks instead.
fn with_deletes(base: &[u8], blocks: &[(u64, Vec<Range<u64>>)]) -> Vec<u8> {
    let (&0, structs) = base.split_last().expect("update") else {
        panic!("base update has deletions");
    };
    let mut out = RawEncoder::default();
    write_delete_set(&mut out, blocks);
    [structs, &out.into_inner()].concat()
}

fn empty_state_vector() -> Vec<u8> {
    StateVector::default().encode_v1().unwrap()
}

/// The same set of clocks, spelled four ways on the wire, and its canonical
/// spelling (clients descending, as the encoder writes them).
fn spellings() -> (Vec<Blocks>, Blocks) {
    let canonical = vec![(9, vec![1..2, 30..32]), (2, vec![0..6, 8..10, 12..13])];
    let spellings = vec![
        canonical.clone(),
        // out of order
        vec![(2, vec![12..13, 0..6, 8..10]), (9, vec![30..32, 1..2])],
        // overlapping, touching, repeated and empty
        vec![
            (2, vec![3..6, 0..4, 9..10, 8..9, 12..13, 12..13, 11..11]),
            (9, vec![31..32, 30..31, 1..2]),
        ],
        // one client split over repeated blocks, with an all-empty client
        vec![
            (2, vec![8..10]),
            (9, vec![30..32]),
            (7, vec![5..5]),
            (2, vec![12..13, 2..6]),
            (9, vec![1..2]),
            (2, vec![0..3]),
        ],
    ];
    (spellings, canonical)
}

#[test]
fn update_decode_canonicalizes_any_spelling() {
    let (spellings, canonical) = spellings();
    let expected = deletes_only(&canonical);
    for blocks in spellings {
        let update = Update::decode_v1(deletes_only(&blocks)).unwrap();
        assert_eq!(update.encode_v1().unwrap(), expected, "{blocks:?}");
    }
}

#[test]
fn diff_update_canonicalizes_any_spelling() {
    let (spellings, canonical) = spellings();
    let expected = deletes_only(&canonical);
    let sv = empty_state_vector();
    for blocks in spellings {
        assert_eq!(
            diff_update_v1(&deletes_only(&blocks), &sv).unwrap(),
            expected,
            "{blocks:?}"
        );
    }
}

fn text_doc(client: u64, len: usize) -> (Doc, Vec<u8>) {
    let doc = DocOptions::from_identity(client, "scale".into()).build();
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "x".repeat(len)).unwrap();
    let update = doc.encode_update_v1().unwrap();
    (doc, update)
}

#[test]
fn read_doc_canonicalizes_any_spelling() {
    let doc = DocOptions::from_identity(5, "scale".into()).build();
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "abcdefghijklmnop").unwrap();
    let base = doc.encode_update_v1().unwrap();

    let spellings: [Blocks; 4] = [
        vec![(5, vec![1..3, 5..6, 8..12])],
        vec![(5, vec![8..12, 1..3, 5..6])],
        vec![(5, vec![9..12, 2..3, 8..10, 5..6, 5..5, 1..2])],
        vec![(5, vec![8..10]), (5, vec![5..6, 10..12]), (5, vec![1..3])],
    ];
    for blocks in spellings {
        let read = ReadDoc::from_full_update_v1(with_deletes(&base, &blocks)).unwrap();
        assert_eq!(read.text("t").unwrap().to_string(), "adeghmnop", "{blocks:?}");
    }
}

#[test]
fn order_range_extend_is_not_quadratic() {
    let count = scale();
    let ranges = inward_ranges(count);
    let started = Instant::now();
    let mut range = OrderRange::new();
    range.extend(ranges);
    let elapsed = started.elapsed();
    eprintln!("OrderRange::extend {count} ranges: {elapsed:?}");
    assert_eq!(range.ranges_len() as u64, count);
    assert!(cfg!(miri) || elapsed < BUDGET, "took {elapsed:?}");
}

#[test]
fn order_range_merge_is_not_quadratic() {
    let count = scale();
    let (evens, odds): (Vec<_>, Vec<_>) = (0..count).map(|i| i * 4..i * 4 + 1).partition(|r| r.start % 8 == 0);
    let (mut range, other) = (OrderRange::from(evens), OrderRange::from(odds));
    let started = Instant::now();
    range.merge(other);
    let elapsed = started.elapsed();
    eprintln!("OrderRange::merge {count} ranges: {elapsed:?}");
    assert_eq!(range.ranges_len() as u64, count);
    assert!(cfg!(miri) || elapsed < MERGE_BUDGET, "took {elapsed:?}");
}

#[test]
fn update_decode_is_not_quadratic() {
    let count = scale();
    let wire = deletes_only(&[(1, inward_ranges(count))]);
    let started = Instant::now();
    let update = Update::decode_v1(&wire).unwrap();
    let elapsed = started.elapsed();
    eprintln!("Update::decode_v1 {count} ranges: {elapsed:?}");
    let sorted: Vec<_> = (0..count).map(|i| i * 2..i * 2 + 1).collect();
    assert_eq!(update.encode_v1().unwrap(), deletes_only(&[(1, sorted)]));
    assert!(cfg!(miri) || elapsed < BUDGET, "took {elapsed:?}");
}

#[test]
fn diff_update_is_not_quadratic() {
    let count = scale();
    let wire = deletes_only(&[(1, inward_ranges(count))]);
    let sv = empty_state_vector();
    let started = Instant::now();
    let diff = diff_update_v1(&wire, &sv).unwrap();
    let elapsed = started.elapsed();
    eprintln!("diff_update_v1 {count} ranges: {elapsed:?}");
    let sorted: Vec<_> = (0..count).map(|i| i * 2..i * 2 + 1).collect();
    assert_eq!(diff, deletes_only(&[(1, sorted)]));
    assert!(cfg!(miri) || elapsed < BUDGET, "took {elapsed:?}");
}

#[test]
fn read_doc_delete_set_is_not_quadratic() {
    // each range splits the text, so this also pays for the splits
    let count = if cfg!(miri) { 16 } else { 100_000 };
    let (_doc, base) = text_doc(1, count as usize * 2);
    let wire = with_deletes(&base, &[(1, inward_ranges(count))]);
    let started = Instant::now();
    let read = ReadDoc::from_full_update_v1(wire).unwrap();
    let elapsed = started.elapsed();
    eprintln!("ReadDoc::from_full_update_v1 {count} ranges: {elapsed:?}");
    assert_eq!(read.text("t").unwrap().len(), count);
    assert!(cfg!(miri) || elapsed < BUDGET, "took {elapsed:?}");
}

/// One range joining the low run and one new range past the high end: the
/// envelope of the batch spans everything added so far.
fn sparse_batch(i: u64) -> [Range<u64>; 2] {
    [i..i + 1, HIGH + 4 * i..HIGH + 4 * i + 1]
}

fn sparse_expected(count: u64) -> OrderRange {
    (0..count).flat_map(sparse_batch).collect()
}

fn sparse_count() -> u64 {
    if cfg!(miri) { 32 } else { 100_000 }
}

#[test]
fn sparse_extend_batches_are_not_quadratic() {
    let count = sparse_count();
    let mut range = OrderRange::new();
    let started = Instant::now();
    for i in 0..count {
        range.extend(sparse_batch(i));
    }
    let elapsed = started.elapsed();
    eprintln!("sparse OrderRange::extend {count} batches: {elapsed:?}");
    assert_eq!(range, sparse_expected(count));
    assert!(cfg!(miri) || elapsed < SPARSE_BUDGET, "took {elapsed:?}");
}

#[test]
fn sparse_merge_batches_are_not_quadratic() {
    let count = sparse_count();
    let mut range = OrderRange::new();
    let started = Instant::now();
    for i in 0..count {
        range.merge(OrderRange::from(sparse_batch(i).to_vec()));
    }
    let elapsed = started.elapsed();
    eprintln!("sparse OrderRange::merge {count} batches: {elapsed:?}");
    assert_eq!(range, sparse_expected(count));
    assert!(cfg!(miri) || elapsed < SPARSE_BUDGET, "took {elapsed:?}");
}

/// Removes `count` nested maps, each holding `keys` values, in one
/// transaction in the order `order` gives, checks the result and returns how
/// long the removal took.
fn remove_nested_maps(count: usize, keys: usize, order: impl Iterator<Item = usize>) -> Duration {
    let doc = DocOptions::from_identity(1, "scale".into()).build();
    let mut root = doc.get_or_create_map("root").unwrap();
    let mut filler = doc.get_or_create_array("filler").unwrap();
    let mut children = Vec::with_capacity(count);
    for i in 0..count {
        let child = doc.create_map().unwrap();
        root.insert(format!("k{i}"), child.clone()).unwrap();
        children.push(child);
    }
    // the children's values get clocks apart from each other
    for child in &mut children {
        for key in 0..keys {
            child.insert(format!("v{key}"), 1).unwrap();
            filler.push(0).unwrap();
        }
    }

    let started = Instant::now();
    doc.transact_mut(None, |tx| {
        let mut map = tx.map(&root)?;
        for i in order {
            map.remove(&format!("k{i}"));
        }
        Ok(())
    })
    .unwrap();
    let elapsed = started.elapsed();

    assert_eq!(root.len(), 0);
    let update = doc.encode_update_v1().unwrap();
    let replica = Doc::try_from_binary_v1(&update).unwrap();
    assert_eq!(replica.get_or_create_map("root").unwrap().len(), 0);
    assert_eq!(replica.encode_update_v1().unwrap(), update);
    elapsed
}

#[test]
fn removing_nested_maps_in_one_transaction_is_not_quadratic() {
    let count = if cfg!(miri) { 12 } else { 120_000 };
    let elapsed = remove_nested_maps(count, 1, 0..count);
    eprintln!("Map::remove {count} nested maps in one transaction: {elapsed:?}");
    assert!(cfg!(miri) || elapsed < REMOVE_BUDGET, "took {elapsed:?}");
}

/// Each removal deletes the map, which joins the maps removed before, and its
/// values, past every value removed before: a batch of `1 + keys` ranges at
/// both ends of the set.
#[test]
fn removing_nested_maps_with_many_values_is_not_quadratic() {
    let count = if cfg!(miri) { 6 } else { 20_000 };
    for keys in [8, 12] {
        let elapsed = remove_nested_maps(count, keys, 0..count);
        eprintln!("Map::remove {count} nested maps with {keys} values in one transaction: {elapsed:?}");
        assert!(cfg!(miri) || elapsed < REMOVE_BUDGET, "{keys} values took {elapsed:?}");
    }
}

/// The same removals last to first, so each batch lands below the ranges
/// removed before.
#[test]
fn removing_nested_maps_backwards_is_not_quadratic() {
    let count = if cfg!(miri) { 6 } else { 20_000 };
    let elapsed = remove_nested_maps(count, 8, (0..count).rev());
    eprintln!("Map::remove {count} nested maps with 8 values backwards: {elapsed:?}");
    assert!(cfg!(miri) || elapsed < REMOVE_BUDGET, "took {elapsed:?}");
}

/// One merge of `k` new ranges that all land in the gap after the first of
/// `2k + 1` old ranges, each next to the one before it.
#[test]
fn merge_into_one_inner_gap_is_not_quadratic() {
    let k = if cfg!(miri) { 64 } else { 200_000 };
    let mut old = vec![0..1];
    old.extend((0..2 * k).map(|i| HIGH + 4 * i..HIGH + 4 * i + 1));
    let new: Vec<_> = (0..k).map(|i| 10 + 4 * i..10 + 4 * i + 1).collect();
    let expected: OrderRange = old.iter().chain(&new).cloned().collect();
    let mut range = OrderRange::from(old);
    let incoming = OrderRange::from(new);
    let started = Instant::now();
    range.merge(incoming);
    let elapsed = started.elapsed();
    eprintln!("OrderRange::merge {k} ranges into one inner gap: {elapsed:?}");
    assert_eq!(range, expected);
    assert!(cfg!(miri) || elapsed < MERGE_BUDGET, "took {elapsed:?}");
}

/// One range joining the low run and `high` new ranges past the high end, one
/// batch more than a few ranges.
fn end_heavy_batch(i: u64, high: u64) -> Vec<Range<u64>> {
    let mut batch = vec![i..i + 1];
    batch.extend((0..high).map(|j| HIGH + 4 * (i * high + j)..HIGH + 4 * (i * high + j) + 1));
    batch
}

#[test]
fn end_heavy_extend_batches_are_not_quadratic() {
    let count = if cfg!(miri) { 16 } else { 40_000 };
    for high in [8, 16] {
        let mut range = OrderRange::new();
        let started = Instant::now();
        for i in 0..count {
            range.extend(end_heavy_batch(i, high));
        }
        let elapsed = started.elapsed();
        eprintln!("1 + {high} OrderRange::extend {count} batches: {elapsed:?}");
        let expected: OrderRange = (0..count).flat_map(|i| end_heavy_batch(i, high)).collect();
        assert_eq!(range, expected);
        assert!(cfg!(miri) || elapsed < SPARSE_BUDGET, "1 + {high} took {elapsed:?}");
    }
}

/// One client with `count` separate two-character text structs, each deleted
/// at its second character so every struct is cut.
fn separate_structs_each_cut(count: u64) -> Vec<u8> {
    let mut out = RawEncoder::default();
    out.write_var_u64(1).unwrap(); // clients
    out.write_var_u64(count).unwrap(); // structs
    out.write_var_u64(1).unwrap(); // client
    out.write_var_u64(0).unwrap(); // first clock
    for i in 0..count {
        if i == 0 {
            out.write_info(4).unwrap(); // string, no origins
            out.write_var_u64(1).unwrap(); // parent is a root
            out.write_var_string("t").unwrap();
        } else {
            out.write_info(0x80 | 4).unwrap(); // string after its left origin
            out.write_var_u64(1).unwrap();
            out.write_var_u64(i * 2 - 1).unwrap();
        }
        out.write_var_string("ab").unwrap();
    }
    let ranges: Vec<_> = (0..count).map(|i| i * 2..i * 2 + 1).collect();
    write_delete_set(&mut out, &[(1, ranges)]);
    out.into_inner()
}

#[test]
fn read_doc_cutting_many_structs_is_not_quadratic() {
    let count = if cfg!(miri) { 16 } else { 200_000 };
    let wire = separate_structs_each_cut(count);
    let started = Instant::now();
    let read = ReadDoc::from_full_update_v1(wire).unwrap();
    let elapsed = started.elapsed();
    eprintln!("ReadDoc::from_full_update_v1 {count} separate structs cut: {elapsed:?}");
    assert_eq!(read.text("t").unwrap().to_string(), "b".repeat(count as usize));
    assert!(cfg!(miri) || elapsed < BUDGET, "took {elapsed:?}");
}
