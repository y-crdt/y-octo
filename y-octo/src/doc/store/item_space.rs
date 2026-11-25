use std::num::NonZeroU32;

use y_octo_core::item_space::ItemSpaceCore;

use super::*;

/// A slot in one document. Only store-owned structures keep these across a
/// commit, so they can all be updated when the arena moves its live items.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ItemIdx(NonZeroU32);

const _: () = assert!(size_of::<Option<ItemIdx>>() == 4);

impl ItemIdx {
    /// The item of a slot the arena handed out: below `u32::MAX`
    /// (`ItemSpaceCore::alloc`), so one more is a `NonZeroU32`.
    #[inline]
    fn new(slot: u32) -> Option<Self> {
        NonZeroU32::new(slot.checked_add(1)?).map(Self)
    }

    #[cfg(test)]
    #[inline]
    pub(in crate::doc) fn slot(self) -> usize {
        (self.0.get() - 1) as usize
    }

    /// The slot as `y_octo_core` names it: in the arena (`ItemSpaceCore`)
    /// and in a block of a `ClientBlocksCore`.
    #[inline]
    pub(super) fn core_slot(self) -> u32 {
        self.0.get() - 1
    }

    /// The item of a slot read back from a `ClientBlocksCore`: one that
    /// [ItemIdx::core_slot] put there, so it is below `u32::MAX` and the sum
    /// is exact. No branch and no panic: this is on the path of every node
    /// read.
    #[inline]
    pub(super) fn of_core_slot(slot: u32) -> Self {
        debug_assert!(slot < u32::MAX, "slot of an item");
        Self(NonZeroU32::MIN.saturating_add(slot))
    }
}

/// Where [ItemSpace::finish] moved the items: for every old slot, one more
/// than the new slot of its item, and `0` for a slot that held none. This is
/// the table `ItemSpaceCore::finish` of `y-octo-core` answers and
/// `ClientBlocksCore::remap_slots` reads, and the bits of an
/// `Option<ItemIdx>`: four bytes per old slot.
#[derive(Debug)]
pub(crate) struct Moved(Vec<u32>);

impl Moved {
    /// Where the item at `old` is now; `None` if `old` held no item.
    #[inline]
    pub(in crate::doc) fn get(&self, old: ItemIdx) -> Option<ItemIdx> {
        NonZeroU32::new(self.0[old.core_slot() as usize]).map(ItemIdx)
    }

    #[inline]
    pub(super) fn table(&self) -> &[u32] {
        &self.0
    }
}

/// The items of one document: the arena `ItemSpaceCore` of `y-octo-core`,
/// whose functions `proofs/` proves (`ItemSpace.lean`). Nothing here reads or
/// writes a slot by itself: an [ItemIdx] is a slot of the core plus one, and
/// every method is the call of the core it is named after.
#[derive(Debug, Default)]
pub(crate) struct ItemSpace {
    core: ItemSpaceCore<Item>,
    #[cfg(test)]
    limit: Option<usize>,
}

fn too_many_items() -> JwstCodecError {
    JwstCodecError::IncompleteDocument(TOO_MANY_ITEMS.into())
}

impl ItemSpace {
    /// How many items the arena may hold: every slot plus one fits
    /// [ItemIdx].
    #[inline]
    fn limit(&self) -> usize {
        #[cfg(test)]
        if let Some(limit) = self.limit {
            return limit;
        }
        u32::MAX as usize
    }

    pub fn check_capacity(&self, additional: usize) -> JwstCodecResult {
        if self.core.check_capacity(additional, self.limit()) {
            Ok(())
        } else {
            Err(too_many_items())
        }
    }

    /// Whether `additional` more items fit an arena that holds no more than
    /// `limit` of them, when that is fewer than it takes.
    #[inline]
    pub(crate) fn fits_within(&self, additional: usize, limit: usize) -> bool {
        self.core.check_capacity(additional, limit.min(self.limit()))
    }

    #[cfg(test)]
    pub(crate) fn set_limit(&mut self, limit: usize) {
        self.limit = Some(limit.min(u32::MAX as usize));
    }

    /// How many items the arena holds, the ones retired in this transaction
    /// included.
    #[cfg(test)]
    pub(crate) fn occupied(&self) -> usize {
        self.core.slots() - self.core.free_slots()
    }

    /// How many slots the chunks have allocated.
    #[cfg(test)]
    pub(crate) fn allocated(&self) -> usize {
        self.core.allocated_capacity()
    }

    pub fn alloc(&mut self, item: Item) -> JwstCodecResult<ItemIdx> {
        let limit = self.limit();
        match self.core.alloc(item, limit) {
            Ok(slot) => ItemIdx::new(slot).ok_or_else(too_many_items),
            Err(_) => Err(too_many_items()),
        }
    }

    #[inline]
    pub fn get(&self, id: ItemIdx) -> Option<&Item> {
        self.core.get(id.core_slot())
    }

    #[inline]
    pub fn get_mut(&mut self, id: ItemIdx) -> Option<&mut Item> {
        self.core.get_mut(id.core_slot())
    }

    #[inline]
    pub fn get_two_mut(&mut self, a: ItemIdx, b: ItemIdx) -> Option<(&mut Item, &mut Item)> {
        self.core.get_two_mut(a.core_slot(), b.core_slot())
    }

    pub fn retire(&mut self, id: ItemIdx) {
        self.core.retire(id.core_slot()).expect("retiring a live item");
    }

    #[cfg(test)]
    pub(super) fn live(&self) -> impl Iterator<Item = (ItemIdx, &Item)> {
        (0..self.core.slots() as u32).filter_map(|slot| Some((ItemIdx::new(slot)?, self.core.get(slot)?)))
    }

    /// Calls `relink` on every item, in the order of the slots.
    pub fn for_each_mut(&mut self, mut relink: impl FnMut(&mut Item)) {
        for slot in 0..self.core.slots() as u32 {
            if let Some(item) = self.core.get_mut(slot) {
                relink(item);
            }
        }
    }

    /// Called after the transaction has finished using temporary cursors.
    /// Live items move in place toward the front; the only full-size scratch
    /// allocation holds four bytes per old slot.
    pub fn finish(&mut self) -> Option<Moved> {
        self.core.finish().map(Moved)
    }
}

#[cfg(test)]
mod tests {
    use y_octo_core::item_space::CHUNK_SIZE;

    use super::*;

    #[test]
    fn quarantine_and_compaction_preserve_live_values_and_release_chunks() {
        let mut arena = ItemSpace::default();
        let count = if cfg!(miri) { 8 * CHUNK_SIZE } else { 100_000 };
        let ids: Vec<_> = (0..count)
            .map(|clock| {
                arena
                    .alloc(Item {
                        id: Id::new(7, clock as u64),
                        ..Item::default()
                    })
                    .unwrap()
            })
            .collect();
        for (i, &id) in ids.iter().enumerate() {
            if i % 10 != 0 {
                arena.retire(id);
                assert!(arena.get(id).is_none());
            }
        }
        let fresh = arena.alloc(Item::default()).unwrap();
        assert_eq!(fresh.slot(), count);
        let before = arena.core.chunk_count();
        let allocated = arena.allocated();
        let remap = arena.finish().unwrap();
        assert!(arena.core.chunk_count() * 5 < before);
        assert_eq!(arena.core.slots(), count.div_ceil(10) + 1);
        // no slot is kept for an item that is gone
        assert_eq!(arena.allocated(), arena.core.slots());
        assert!(arena.allocated() * 5 < allocated);
        for (i, id) in ids.iter().enumerate() {
            match remap.get(*id) {
                Some(new) => {
                    assert_eq!(i % 10, 0);
                    assert_eq!(arena.get(new).unwrap().id.clock, i as u64);
                    // the table as `ClientBlocksCore::remap_slots` reads it
                    assert_eq!(remap.table()[id.core_slot() as usize], new.core_slot() + 1);
                    assert_eq!(ItemIdx::of_core_slot(new.core_slot()), new);
                }
                None => {
                    assert_ne!(i % 10, 0);
                    assert_eq!(remap.table()[id.core_slot() as usize], 0);
                }
            }
        }
    }

    /// An arena of `first` items keeps its first `kept` ones, is filled up
    /// to `second` items and keeps its first `kept_again` ones. Answers how
    /// many slots it has memory for after each of the two compactions.
    fn compacted_twice(first: usize, kept: usize, second: usize, kept_again: usize) -> (usize, usize) {
        let mut arena = ItemSpace::default();
        let ids: Vec<_> = (0..first).map(|_| arena.alloc(Item::default()).unwrap()).collect();
        for &id in &ids[kept..] {
            arena.retire(id);
        }
        arena.finish().expect("the first compaction");
        assert_eq!(arena.live().count(), kept);
        let once = arena.allocated();
        let ids: Vec<_> = (kept..second).map(|_| arena.alloc(Item::default()).unwrap()).collect();
        assert_eq!(ids[0].slot(), kept);
        for &id in &ids[kept_again - kept..] {
            arena.retire(id);
        }
        arena.finish().expect("the second compaction");
        assert_eq!(arena.live().count(), kept_again);
        assert_eq!(arena.core.slots(), kept_again);
        (once, arena.allocated())
    }

    #[test]
    fn a_chunk_that_grew_again_gives_its_memory_back_at_the_next_compaction() {
        // the case of the review of PR #61: the chunk the first compaction
        // ended in (1023 slots) grows past a chunk's size when it is filled
        // again, and the second compaction keeps exactly that chunk, full.
        // It must not keep the memory the chunk grew to.
        assert_eq!(
            compacted_twice(2 * CHUNK_SIZE, CHUNK_SIZE - 1, 2 * CHUNK_SIZE, CHUNK_SIZE),
            (CHUNK_SIZE - 1, CHUNK_SIZE)
        );
        // the chunk that grew is one of the full ones before the last
        assert_eq!(
            compacted_twice(2 * CHUNK_SIZE, CHUNK_SIZE - 1, 4 * CHUNK_SIZE, 2 * CHUNK_SIZE),
            (CHUNK_SIZE - 1, 2 * CHUNK_SIZE)
        );
        if cfg!(miri) {
            return;
        }
        // the same at the end of a later chunk, and in the middle of one
        assert_eq!(
            compacted_twice(4 * CHUNK_SIZE, 2 * CHUNK_SIZE - 1, 4 * CHUNK_SIZE, 2 * CHUNK_SIZE),
            (2 * CHUNK_SIZE - 1, 2 * CHUNK_SIZE)
        );
        assert_eq!(compacted_twice(2 * CHUNK_SIZE, 600, 2 * CHUNK_SIZE, 1000), (600, 1000));
        assert_eq!(
            compacted_twice(4 * CHUNK_SIZE, CHUNK_SIZE + 300, 4 * CHUNK_SIZE, CHUNK_SIZE + 900),
            (CHUNK_SIZE + 300, CHUNK_SIZE + 900)
        );
        // nothing new is kept: the chunk is as full as it was
        assert_eq!(
            compacted_twice(2 * CHUNK_SIZE, CHUNK_SIZE, 2 * CHUNK_SIZE, CHUNK_SIZE),
            (CHUNK_SIZE, CHUNK_SIZE)
        );
        // the second compaction ends after a chunk that grew in the middle
        assert_eq!(
            compacted_twice(4 * CHUNK_SIZE, CHUNK_SIZE + 300, 6 * CHUNK_SIZE, 3 * CHUNK_SIZE + 17),
            (CHUNK_SIZE + 300, 3 * CHUNK_SIZE + 17)
        );
    }

    #[test]
    #[cfg(not(loom))]
    fn collected_subtree_compacts_around_staging_and_preserves_wire_and_undo() {
        let doc = Doc::with_client(7);
        let mut root = doc.get_or_create_map("root").unwrap();
        let doomed = doc.create_map().unwrap();
        root.insert("doomed".into(), doomed.clone()).unwrap();
        let keep = doc.get_or_create_map("keep").unwrap();
        let count = if cfg!(miri) { 300 } else { 100_000 };
        doc.transact_mut(None, |tx| {
            let mut entries = tx.map(&doomed)?;
            for i in 0..count * 9 / 10 {
                entries.insert(i.to_string(), i as i64)?;
            }
            let mut entries = tx.map(&keep)?;
            for i in count * 9 / 10..count {
                entries.insert(i.to_string(), i as i64)?;
            }
            Ok(())
        })
        .unwrap();
        let mut draft = doc.create_map().unwrap();
        let mut list = doc.create_array().unwrap();
        list.push(3).unwrap();
        draft.insert("list".into(), list.clone()).unwrap();
        let mut other_draft = doc.create_text().unwrap();
        other_draft.insert(0, "abc").unwrap();
        let mut body = doc.get_or_create_text("body").unwrap();
        let undo = UndoManager::<()>::new(&doc, [(&body).into()], UndoOptions::default()).unwrap();
        body.insert(0, "abc").unwrap();
        undo.stop_capturing().unwrap();
        body.remove(1, 1).unwrap();
        undo.undo().unwrap();
        let allocated = || doc.store.read().unwrap().type_arena.items.allocated();
        let before = allocated();
        root.remove("doomed");
        doc.gc().unwrap();
        assert!(allocated() * 3 < before);
        assert_eq!(keep.len(), (count / 10) as u64);
        assert_eq!(
            keep.get(&(count - 1).to_string()),
            Some(Value::from((count - 1) as i64))
        );
        assert_eq!(body.to_string(), "abc");
        undo.redo().unwrap();
        assert_eq!(body.to_string(), "ac");
        assert_eq!(list.get(0), Some(Value::from(3)));
        list.push(4).unwrap();
        other_draft.insert(1, "!").unwrap();
        root.insert("draft".into(), draft.clone()).unwrap();
        root.insert("other".into(), other_draft.clone()).unwrap();
        assert_eq!(other_draft.to_string(), "a!bc");
        assert_eq!(list.get(1), Some(Value::from(4)));
        // After both mounts all private timelines have gone. Every occupied
        // arena slot corresponds to precisely one published block.
        {
            let store = doc.store.read().unwrap();
            let owners: HashSet<_> = store
                .items
                .iter()
                .flat_map(|(&c, b)| b.nodes(c))
                .filter_map(|n| n.as_item())
                .collect();
            let space = &store.type_arena.items;
            let actual: HashSet<_> = space.live().map(|(idx, _)| idx).collect();
            assert_eq!(owners, actual);
            for &idx in &owners {
                let item = space.get(idx).unwrap();
                if let Some(next) = item.right {
                    assert_eq!(space.get(next).unwrap().left, Some(idx));
                }
                if let Some(prev) = item.left {
                    assert_eq!(space.get(prev).unwrap().right, Some(idx));
                }
            }
            store.self_check().unwrap();
        }
        let bytes = doc.encode_update_v1().unwrap();
        let mut peer = Doc::with_client(8);
        peer.apply_update_from_binary_v1(bytes.clone()).unwrap();
        let peer_root = peer.get_or_create_map("root").unwrap();
        let peer_keep = peer.get_or_create_map("keep").unwrap();
        assert_eq!(
            serde_json::to_value(&root).unwrap(),
            serde_json::to_value(&peer_root).unwrap()
        );
        assert_eq!(
            serde_json::to_value(&keep).unwrap(),
            serde_json::to_value(&peer_keep).unwrap()
        );
        assert_eq!(peer.get_state_vector(), doc.get_state_vector());
        assert_eq!(peer.get_delete_sets(), doc.get_delete_sets());
        for (source, target) in [(&doc, &peer), (&peer, &doc)] {
            let delta = source.encode_state_as_update(&target.get_state_vector()).unwrap();
            // V1 repeats its delete set even when the receiver knows all
            // clocks.
            assert!(delta.structs.is_empty());
            assert_eq!(delta.delete_set, target.get_delete_sets());
        }
        undo.clear(true, true).unwrap();
        drop(undo);
        doc.gc().unwrap();
        peer.gc().unwrap();
        assert!(
            doc.encode_update_v1().unwrap() == peer.encode_update_v1().unwrap(),
            "replicas with equal retention policies must encode identically"
        );
        assert_eq!(peer.get_or_create_text("body").unwrap().to_string(), "ac");
    }

    #[test]
    fn distinct_slots_are_borrowed_in_argument_order() {
        let mut arena = ItemSpace::default();
        let ids: Vec<_> = (0..=2 * CHUNK_SIZE)
            .map(|_| arena.alloc(Item::default()).unwrap())
            .collect();
        for (a, b) in [
            (0, 3),
            (3, 0),
            (0, CHUNK_SIZE),
            (CHUNK_SIZE, 0),
            (CHUNK_SIZE, CHUNK_SIZE + 1),
            (2 * CHUNK_SIZE, CHUNK_SIZE),
        ] {
            let (x, y) = arena.get_two_mut(ids[a], ids[b]).unwrap();
            x.id.clock = 11;
            y.id.clock = 22;
            assert_eq!(arena.get(ids[a]).unwrap().id.clock, 11);
            assert_eq!(arena.get(ids[b]).unwrap().id.clock, 22);
        }
        assert!(arena.get_two_mut(ids[0], ids[0]).is_none());
        arena.retire(ids[4]);
        assert!(arena.get_two_mut(ids[0], ids[4]).is_none());
        assert!(arena.finish().is_none());
        assert_eq!(arena.alloc(Item::default()).unwrap(), ids[4]);
    }
}

#[cfg(all(test, not(loom)))]
mod regressions;
