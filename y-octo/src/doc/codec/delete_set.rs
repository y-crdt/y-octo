use std::{
    collections::{VecDeque, hash_map::Entry},
    mem,
    ops::{Deref, Range},
};

use super::*;
use crate::doc::OrderRange;

impl<W: CrdtWriter> CrdtWrite<W> for Range<u64> {
    fn write(&self, encoder: &mut W) -> JwstCodecResult {
        encoder.write_var_u64(self.start)?;
        encoder.write_var_u64(self.end - self.start)?;
        Ok(())
    }
}

impl<W: CrdtWriter> CrdtWrite<W> for OrderRange {
    fn write(&self, encoder: &mut W) -> JwstCodecResult {
        // canonicalize like yjs' sortAndMergeDeleteSet so the wire format is
        // stable no matter how the ranges were inserted or decoded
        write_ranges(self, encoder)
    }
}

fn write_ranges<W: CrdtWriter>(ranges: &OrderRange, encoder: &mut W) -> JwstCodecResult {
    encoder.write_var_u64(ranges.ranges_len() as u64)?;
    for range in ranges {
        range.write(encoder)?;
    }
    Ok(())
}

/// Deleted clock ranges per client. Read it through `Deref`; change it with
/// the methods below, which keep every client's ranges canonical and drop
/// clients with nothing deleted.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct DeleteSet {
    // a named field: a tuple struct's `pub(crate)` constructor would make the
    // glob re-exports of `DeleteSet` ambiguous in visibility
    pub(crate) clients: ClientMap<OrderRange>,
}

impl Deref for DeleteSet {
    type Target = ClientMap<OrderRange>;

    fn deref(&self) -> &Self::Target {
        &self.clients
    }
}

impl<const N: usize> From<[(Client, Vec<Range<u64>>); N]> for DeleteSet {
    fn from(value: [(Client, Vec<Range<u64>>); N]) -> Self {
        let mut map = ClientMap::with_capacity(N);
        // a later entry for the same client replaces the earlier one, an
        // empty one removes it
        for (client, ranges) in value {
            let ranges = OrderRange::from(ranges);
            if ranges.is_empty() {
                map.remove(&client);
            } else {
                map.insert(client, ranges);
            }
        }
        Self { clients: map }
    }
}

impl DeleteSet {
    /// Builds a set from `(client, range)` pairs in any order, in
    /// `O(k log k)`. Decoders collect into this rather than adding ranges one
    /// at a time, which is quadratic for out-of-order wire input.
    pub(crate) fn from_flat_ranges(mut ranges: Vec<(Client, Range<u64>)>) -> Self {
        ranges.sort_unstable_by_key(|(client, range)| (*client, range.start, range.end));

        let mut clients = ClientMap::default();
        let mut ranges = ranges.into_iter().filter(|(_, range)| !range.is_empty()).peekable();
        while let Some((client, mut last)) = ranges.next() {
            // stays unallocated for a client with a single merged range
            let mut earlier = VecDeque::new();
            while let Some((_, range)) = ranges.next_if(|(next, _)| *next == client) {
                if last.end >= range.start {
                    last.end = last.end.max(range.end);
                } else {
                    earlier.push_back(mem::replace(&mut last, range));
                }
            }
            let merged = if earlier.is_empty() {
                OrderRange::from(last)
            } else {
                earlier.push_back(last);
                OrderRange::from_sorted_disjoint(earlier)
            };
            clients.insert(client, merged);
        }
        Self { clients }
    }

    /// Adds the half-open range `from..from.saturating_add(len)`: a range
    /// reaching past `u64::MAX` is cut there. Nothing is added when the
    /// range is empty (`len == 0` or `from == u64::MAX`).
    pub fn add(&mut self, client: Client, from: Clock, len: Clock) {
        self.add_range(client, from..from.saturating_add(len));
    }

    pub fn add_range(&mut self, client: Client, range: Range<u64>) {
        if range.is_empty() {
            return;
        }
        match self.clients.entry(client) {
            Entry::Occupied(e) => {
                e.into_mut().push(range);
            }
            Entry::Vacant(e) => {
                e.insert(range.into());
            }
        }
    }

    pub fn batch_add_ranges(&mut self, client: Client, ranges: Vec<Range<u64>>) {
        match self.clients.entry(client) {
            Entry::Occupied(e) => {
                e.into_mut().extend_vec(ranges);
            }
            Entry::Vacant(e) => {
                // `ranges` may come in any order (e.g. the clocks of a map's
                // children); `From` sorts and merges them so later pushes see
                // a canonical list
                let ranges = OrderRange::from(ranges);
                if !ranges.is_empty() {
                    e.insert(ranges);
                }
            }
        }
    }

    pub fn merge(&mut self, other: &Self) {
        for (client, range) in &other.clients {
            match self.clients.entry(*client) {
                Entry::Occupied(e) => {
                    e.into_mut().merge_from(range);
                }
                Entry::Vacant(e) => {
                    if !range.is_empty() {
                        e.insert(range.clone());
                    }
                }
            }
        }
    }

    /// Removes the ranges of `client`, returning them.
    pub fn remove(&mut self, client: &Client) -> Option<OrderRange> {
        self.clients.remove(client)
    }

    /// Removes every client.
    pub fn clear(&mut self) {
        self.clients.clear();
    }

    /// Clears entries in place when the backing map capacity is within
    /// `max_cap`, or resets to an empty map to avoid retaining oversized
    /// buffers from occasional large transactions.
    pub(crate) fn clear_or_reset(&mut self, max_cap: usize) {
        if self.clients.capacity() <= max_cap {
            self.clients.clear();
        } else {
            *self = Self::default();
        }
    }
}

impl<W: CrdtWriter> CrdtWrite<W> for DeleteSet {
    fn write(&self, encoder: &mut W) -> JwstCodecResult {
        // skip clients whose ranges canonicalize to nothing (e.g. only
        // zero-length ranges), keeping the wire format minimal and stable
        let mut clients = self
            .iter()
            .filter_map(|(&client, ranges)| (!ranges.is_empty()).then_some((client, ranges)))
            .collect::<Vec<_>>();
        clients.sort_unstable_by_key(|entry| std::cmp::Reverse(entry.0));

        encoder.write_var_u64(clients.len() as u64)?;

        for (client, ranges) in clients {
            encoder.write_var_u64(client)?;
            write_ranges(ranges, encoder)?;
        }

        Ok(())
    }
}

#[cfg(test)]
#[allow(clippy::single_range_in_vec_init)]
mod tests {
    use super::*;

    #[test]
    fn test_delete_set_add() {
        let delete_set = DeleteSet::from([
            (1, vec![0..10, 20..30]),
            (2, vec![0..5, 10..20]),
            (3, vec![15..20, 30..35]),
            (4, vec![0..10]),
        ]);

        {
            let mut delete_set = delete_set.clone();
            delete_set.add(1, 5, 25);
            assert_eq!(delete_set.get(&1), Some(&OrderRange::from(0..30)));
        }

        {
            let mut delete_set = delete_set;
            delete_set.add(1, 5, 10);
            assert_eq!(delete_set.get(&1), Some(&OrderRange::from(vec![0..15, 20..30])));
        }
    }

    #[test]
    fn test_delete_set_batch_push() {
        let delete_set = DeleteSet::from([
            (1, vec![0..10, 20..30]),
            (2, vec![0..5, 10..20]),
            (3, vec![15..20, 30..35]),
            (4, vec![0..10]),
        ]);

        {
            let mut delete_set = delete_set.clone();
            delete_set.batch_add_ranges(1, vec![0..5, 10..20]);
            assert_eq!(delete_set.get(&1), Some(&OrderRange::from(0..30)));
        }

        {
            let mut delete_set = delete_set;
            delete_set.batch_add_ranges(1, vec![40..50, 10..20]);
            assert_eq!(delete_set.get(&1), Some(&OrderRange::from(vec![0..30, 40..50])));
        }
    }

    fn assert_canonical(range: &OrderRange) {
        let ranges = range.into_iter().collect::<Vec<_>>();
        assert!(ranges.iter().all(|r| !r.is_empty()), "empty range in {range:?}");
        for pair in ranges.windows(2) {
            assert!(pair[0].end < pair[1].start, "unsorted or touching ranges in {range:?}");
        }
        assert_eq!(range.ranges_len(), ranges.len(), "{range:?}");
    }

    #[test]
    fn test_delete_set_batch_add_unsorted_vacant() {
        let sorted = || {
            let mut set = DeleteSet::default();
            set.batch_add_ranges(1, vec![2..4, 6..8, 10..12]);
            set
        };
        let mut unsorted = DeleteSet::default();
        unsorted.batch_add_ranges(1, vec![10..12, 2..4, 6..8]);
        assert_eq!(unsorted, sorted());
        assert_canonical(&unsorted[&1]);

        // later additions in the same transaction keep every range
        let follow_up = |set: &mut DeleteSet| {
            set.add_range(1, 4..5);
            set.batch_add_ranges(1, vec![13..14, 8..9]);
            set.add_range(1, 0..1);
            set.add(1, 20, 2);
        };
        let mut expected = sorted();
        follow_up(&mut expected);
        follow_up(&mut unsorted);
        assert_eq!(unsorted, expected);
        assert_eq!(
            unsorted[&1],
            OrderRange::from(vec![0..1, 2..5, 6..9, 10..12, 13..14, 20..22])
        );
        assert_canonical(&unsorted[&1]);
    }

    #[test]
    fn test_delete_set_skips_empty() {
        let mut set = DeleteSet::default();
        set.add_range(1, 5..5);
        set.add(2, 3, 0);
        set.batch_add_ranges(3, vec![]);
        set.batch_add_ranges(4, vec![7..7, 9..9]);
        set.merge(&DeleteSet::from([(5, vec![6..6])]));
        assert!(set.is_empty(), "{set:?}");

        let set = DeleteSet::from([(1, vec![]), (2, vec![4..4]), (3, vec![5..6, 0..1])]);
        assert_eq!(set.len(), 1);
        assert_eq!(set[&3], OrderRange::from(vec![0..1, 5..6]));
        assert_canonical(&set[&3]);
    }

    #[test]
    fn test_delete_set_merge() {
        let other = DeleteSet::from([(1, vec![10..12, 2..4, 3..6, 8..8]), (2, vec![1..2])]);

        let mut set = DeleteSet::from([(2, vec![2..3])]);
        set.merge(&other);
        assert_eq!(set.len(), 2, "{set:?}");
        assert_eq!(set[&1], OrderRange::from(vec![2..6, 10..12]));
        assert_eq!(set[&2], OrderRange::from(1..3));
        assert_canonical(&set[&1]);

        set.add_range(1, 6..10);
        assert_eq!(set[&1], OrderRange::from(2..12));
    }

    #[test]
    fn test_from_flat_ranges() {
        let set = DeleteSet::from_flat_ranges(vec![
            (2, 8..9),
            (1, 5..6),
            (2, 0..3),
            (3, 4..4),
            (2, 2..5),
            (1, 6..7),
            (2, 9..10),
            (4, 0..u64::MAX),
            (4, 7..8),
        ]);
        assert_eq!(
            set,
            DeleteSet::from([(1, vec![5..7]), (2, vec![0..5, 8..10]), (4, vec![0..u64::MAX])])
        );
        assert_canonical(&set[&2]);
        assert!(DeleteSet::from_flat_ranges(Vec::new()).is_empty());
    }

    #[test]
    fn test_delete_set_remove_and_clear() {
        let mut set = DeleteSet::from([(1, vec![0..1]), (2, vec![3..5])]);
        assert_eq!(set.remove(&1), Some(OrderRange::from(0..1)));
        assert_eq!(set.remove(&1), None);
        assert_eq!(set.len(), 1);
        set.clear();
        assert!(set.is_empty());
    }

    fn encode(delete_set: DeleteSet) -> Vec<u8> {
        Update {
            delete_set,
            ..Update::default()
        }
        .encode_v1()
        .unwrap()
    }

    #[test]
    fn test_delete_set_from_later_entry_replaces_earlier() {
        let set = DeleteSet::from([(1, vec![0..2]), (2, vec![7..8]), (1, vec![5..6])]);
        assert_eq!(set.len(), 2);
        assert_eq!(set[&1], OrderRange::from(5..6));
        assert_eq!(encode(set), encode(DeleteSet::from([(2, vec![7..8]), (1, vec![5..6])])));

        for empty in [vec![], vec![5..5]] {
            let set = DeleteSet::from([(1, vec![0..2]), (2, vec![7..8]), (1, empty.clone())]);
            assert_eq!(set.len(), 1, "{empty:?}");
            assert!(set.get(&1).is_none(), "{empty:?}");
            assert_eq!(encode(set), encode(DeleteSet::from([(2, vec![7..8])])), "{empty:?}");

            let set = DeleteSet::from([(1, vec![0..2]), (1, empty.clone())]);
            assert!(set.is_empty(), "{empty:?}");
            assert_eq!(encode(set), encode(DeleteSet::default()), "{empty:?}");
        }
    }

    #[test]
    fn test_delete_set_add_saturates() {
        let mut set = DeleteSet::default();
        // up to u64::MAX exactly
        set.add(1, u64::MAX - 2, 2);
        assert_eq!(set[&1], OrderRange::from(u64::MAX - 2..u64::MAX));
        // one past it is cut at u64::MAX
        set.add(2, u64::MAX - 2, 3);
        assert_eq!(set[&2], OrderRange::from(u64::MAX - 2..u64::MAX));
        set.add(2, 0, u64::MAX);
        assert_eq!(set[&2], OrderRange::from(vec![0..u64::MAX]));
        // empty ranges add nothing
        set.add(3, u64::MAX, 1);
        set.add(4, u64::MAX, u64::MAX);
        set.add(5, 5, 0);
        assert_eq!(set.len(), 2, "{set:?}");
    }

    #[test]
    fn test_encode_decode() {
        let delete_set = DeleteSet::from([(1, vec![0..10, 20..30]), (2, vec![0..5, 10..20])]);
        let update = Update {
            delete_set: delete_set.clone(),
            ..Update::default()
        };
        let decoded = Update::decode_v1(update.encode_v1().unwrap()).unwrap();
        assert_eq!(delete_set, decoded.delete_set);
    }
}
