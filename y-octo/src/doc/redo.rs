//! Local redo mapping: which ids a redo recreated an old id range under.
//!
//! Yjs keeps this as `Item.redone` and has to carry it through every item split
//! (`splitItem` offsets the right half) and refuse merges of redone items. Here
//! the mapping is keyed by id ranges in a table owned by the store, so
//! splitting or merging items never touches it. It is local memory state: it is
//! not encoded into updates and other peers never see it.

use std::collections::BTreeMap;

use super::*;

/// `old id range -> new start`, ranges of equal length.
#[derive(Debug, Default)]
pub(crate) struct RedoMap {
    /// Per client, disjoint ranges keyed by their first old clock.
    clients: ClientMap<BTreeMap<Clock, RedoRange>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RedoRange {
    len: u64,
    target: Id,
}

impl RedoMap {
    /// Records that `old..old+len` was recreated as `new..new+len`.
    ///
    /// A range is registered once: like Yjs `redoItem`, a redo of content that
    /// already has a target reuses it. Adjacent ranges whose targets are
    /// contiguous are coalesced, so registering a range piece by piece (an item
    /// split by a remote peer and recreated segment by segment) ends up as one
    /// entry.
    pub fn insert(&mut self, old: Id, len: u64, new: Id) {
        debug_assert!(len > 0, "empty redo range");
        debug_assert!(
            old.client != new.client || old.clock + len <= new.clock || new.clock + len <= old.clock,
            "redo range maps onto itself"
        );

        let ranges = self.clients.entry(old.client).or_default();
        let start = old.clock;
        let end = start + len;

        debug_assert!(
            ranges.range(..end).next_back().is_none_or(|(s, r)| s + r.len <= start),
            "redo range registered twice; a redone item reuses its target"
        );

        let mut start = start;
        let mut range = RedoRange { len, target: new };

        if let Some((&s, &r)) = ranges.range(..start).next_back()
            && s + r.len == start
            && r.target.client == new.client
            && r.target.clock + r.len == new.clock
        {
            ranges.remove(&s);
            start = s;
            range = RedoRange {
                len: r.len + range.len,
                target: r.target,
            };
        }

        if let Some(r) = ranges.get(&end).copied()
            && r.target.client == range.target.client
            && range.target.clock + range.len == r.target.clock
        {
            ranges.remove(&end);
            range.len += r.len;
        }

        ranges.insert(start, range);
    }

    pub(super) fn is_empty(&self) -> bool {
        self.clients.is_empty()
    }

    /// Upper bound on distinct cuts made by cleaning old redo targets.
    pub(super) fn target_split_bound(&self, store: &DocStore) -> usize {
        let mut total = 0usize;
        for mapping in self.clients.values().flat_map(|ranges| ranges.values()) {
            let start = mapping.target;
            let end = start.clock + mapping.len;
            let Some(blocks) = store.items.get(&start.client) else {
                continue;
            };
            let Some(first) = blocks.find(start.clock) else {
                continue;
            };
            for i in first..blocks.len() {
                let node = blocks.node(start.client, i).expect("block index");
                if node.clock() >= end {
                    break;
                }
                if node.is_item() {
                    let lo = (node.clock() + 1).max(start.clock);
                    let hi = (node.clock() + node.len() - 1).min(end);
                    if lo <= hi {
                        total = total.saturating_add(usize::try_from(hi - lo + 1).unwrap_or(usize::MAX));
                    }
                }
            }
        }
        total
    }

    /// The id `id` was recreated as by one redo, if any.
    pub fn get(&self, id: Id) -> Option<Id> {
        let (start, range) = self.clients.get(&id.client)?.range(..=id.clock).next_back()?;
        (id.clock < start + range.len).then(|| range.target + (id.clock - start))
    }

    /// `Ok(n)`: `id` and the `n - 1` ids after it were recreated by one
    /// redo, contiguously. `Err(n)`: they were not, nor any of the next
    /// `n - 1` ids (`u64::MAX` when nothing after `id` was).
    pub fn range_at(&self, id: Id) -> Result<u64, u64> {
        let Some(ranges) = self.clients.get(&id.client) else {
            return Err(u64::MAX);
        };
        if let Some((start, range)) = ranges.range(..=id.clock).next_back()
            && id.clock < start + range.len
        {
            return Ok(start + range.len - id.clock);
        }
        Err(ranges
            .range(id.clock..)
            .next()
            .map_or(u64::MAX, |(start, _)| start - id.clock))
    }

    /// [RedoMap::follow] for the ids `id..id+len`: the ranges at the ends of
    /// their redo chains, which split where parts were recreated by
    /// different redos.
    pub fn follow_range(&self, id: Id, len: u64) -> Vec<(Id, u64)> {
        let mut ends = Vec::new();
        let mut pending = vec![(id, len)];
        while let Some((id, len)) = pending.pop() {
            match self.range_at(id) {
                Ok(n) => {
                    let n = n.min(len);
                    if n < len {
                        pending.push((id + n, len - n));
                    }
                    pending.push((self.get(id).expect("recreated"), n));
                }
                Err(gap) if gap < len => {
                    pending.push((id + gap, len - gap));
                    ends.push((id, gap));
                }
                Err(_) => ends.push((id, len)),
            }
        }
        ends
    }

    /// Follows the redo chain of `id` (old -> new -> newer ...) to the id that
    /// has not been recreated, keeping the offset inside every range. Returns
    /// `id` itself when it was never recreated.
    pub fn follow(&self, mut id: Id) -> Id {
        // Every target is a fresh id created by a redo after its source, so a
        // chain cannot cycle.
        while let Some(next) = self.get(id) {
            id = next;
        }
        id
    }

    #[cfg(test)]
    fn ranges(&self, client: Client) -> Vec<(Clock, u64, Id)> {
        self.clients
            .get(&client)
            .map(|ranges| ranges.iter().map(|(s, r)| (*s, r.len, r.target)).collect())
            .unwrap_or_default()
    }
}

impl DocStore {
    /// Yjs `followRedone`: the struct holding the end of `id`'s redo chain and
    /// the offset of the followed id inside it. `None` when that id is not in
    /// the store or has been garbage collected.
    pub(crate) fn follow_redone(&self, id: Id) -> Option<(ItemRef, u64)> {
        self.item_with_offset(self.redone.follow(id))
    }

    /// The item holding `id` and the offset of `id` inside it. `None` when
    /// `id` is not in the store or has been garbage collected.
    pub(crate) fn item_with_offset(&self, id: Id) -> Option<(ItemRef, u64)> {
        let node = self.get_node(id)?;
        Some((Some(node.as_item()?), id.clock - node.clock()))
    }

    /// Registers that a redo recreated `old..old+len` as `new..new+len`.
    pub(crate) fn register_redone(&mut self, old: Id, len: u64, new: Id) {
        self.redone.insert(old, len, new);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(client: Client, clock: Clock) -> Id {
        Id::new(client, clock)
    }

    #[test]
    fn single_range_with_offset() {
        let mut map = RedoMap::default();
        map.insert(id(1, 10), 5, id(1, 100));

        assert_eq!(map.get(id(1, 9)), None);
        assert_eq!(map.get(id(1, 10)), Some(id(1, 100)));
        assert_eq!(map.get(id(1, 12)), Some(id(1, 102)));
        assert_eq!(map.get(id(1, 14)), Some(id(1, 104)));
        assert_eq!(map.get(id(1, 15)), None);
        assert_eq!(map.follow(id(1, 13)), id(1, 103));
    }

    #[test]
    fn ranges_at_an_id() {
        let mut map = RedoMap::default();
        assert_eq!(map.range_at(id(1, 0)), Err(u64::MAX));
        map.insert(id(1, 10), 5, id(2, 0));
        map.insert(id(1, 20), 5, id(3, 0));
        assert_eq!(map.range_at(id(1, 12)), Ok(3));
        assert_eq!(map.range_at(id(1, 10)), Ok(5));
        assert_eq!(map.range_at(id(1, 5)), Err(5));
        assert_eq!(map.range_at(id(1, 15)), Err(5));
        assert_eq!(map.range_at(id(1, 25)), Err(u64::MAX));
        assert_eq!(map.range_at(id(2, 0)), Err(u64::MAX));
    }

    #[test]
    fn following_ranges_splits_where_redos_differ() {
        let mut map = RedoMap::default();
        assert_eq!(map.follow_range(id(1, 0), 3), [(id(1, 0), 3)]);
        // (1, 0..6) -> (2, 0..6); (2, 2..4) -> (3, 0..2)
        map.insert(id(1, 0), 6, id(2, 0));
        map.insert(id(2, 2), 2, id(3, 0));
        let mut ends = map.follow_range(id(1, 1), 6);
        ends.sort_by_key(|(id, _)| (id.client, id.clock));
        assert_eq!(ends, [(id(1, 6), 1), (id(2, 1), 1), (id(2, 4), 2), (id(3, 0), 2)]);
    }

    #[test]
    fn lookup_misses() {
        let mut map = RedoMap::default();
        assert_eq!(map.get(id(1, 0)), None);
        assert_eq!(map.follow(id(1, 0)), id(1, 0));

        map.insert(id(1, 10), 5, id(2, 0));
        // other client, before, after, and in a gap
        assert_eq!(map.get(id(2, 12)), None);
        assert_eq!(map.get(id(1, 0)), None);
        assert_eq!(map.get(id(1, 15)), None);
        map.insert(id(1, 20), 5, id(2, 10));
        assert_eq!(map.get(id(1, 17)), None);
        assert_eq!(map.follow(id(1, 17)), id(1, 17));
    }

    #[test]
    fn segmented_registration_coalesces() {
        // An item split by a remote peer into three parts, recreated part by
        // part, in any order.
        let mut map = RedoMap::default();
        map.insert(id(1, 3), 2, id(1, 23));
        map.insert(id(1, 0), 3, id(1, 20));
        map.insert(id(1, 5), 4, id(1, 25));

        assert_eq!(map.ranges(1), vec![(0, 9, id(1, 20))]);
        for clock in 0..9 {
            assert_eq!(map.get(id(1, clock)), Some(id(1, 20 + clock)));
        }
    }

    #[test]
    fn segments_with_discontiguous_targets_stay_apart() {
        let mut map = RedoMap::default();
        map.insert(id(1, 0), 3, id(1, 20));
        map.insert(id(1, 3), 3, id(1, 40));
        map.insert(id(1, 6), 3, id(2, 26));

        assert_eq!(
            map.ranges(1),
            vec![(0, 3, id(1, 20)), (3, 3, id(1, 40)), (6, 3, id(2, 26))]
        );
        assert_eq!(map.get(id(1, 2)), Some(id(1, 22)));
        assert_eq!(map.get(id(1, 4)), Some(id(1, 41)));
        assert_eq!(map.get(id(1, 8)), Some(id(2, 28)));
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "redo range registered twice")]
    fn registering_a_range_twice_is_a_bug() {
        let mut map = RedoMap::default();
        map.insert(id(1, 0), 10, id(1, 100));
        map.insert(id(1, 2), 3, id(1, 102));
    }

    #[test]
    fn redo_chain_keeps_offsets() {
        // old -> new -> newer, where the second redo recreated the new range in
        // two parts
        let mut map = RedoMap::default();
        map.insert(id(1, 0), 6, id(1, 6));
        map.insert(id(1, 6), 2, id(1, 12));
        map.insert(id(1, 8), 4, id(1, 20));

        assert_eq!(map.follow(id(1, 0)), id(1, 12));
        assert_eq!(map.follow(id(1, 1)), id(1, 13));
        assert_eq!(map.follow(id(1, 2)), id(1, 20));
        assert_eq!(map.follow(id(1, 5)), id(1, 23));
        // following from the middle of the chain
        assert_eq!(map.follow(id(1, 9)), id(1, 21));
        // the end of the chain maps to itself
        assert_eq!(map.follow(id(1, 21)), id(1, 21));
    }
}
