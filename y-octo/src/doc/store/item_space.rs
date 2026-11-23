use std::num::NonZeroU32;

use super::*;

/// A slot in one document. Only store-owned structures keep these across a
/// commit, so they can all be updated when the arena moves its live items.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ItemIdx(NonZeroU32);

const _: () = assert!(size_of::<Option<ItemIdx>>() == 4);

const CHUNK_SIZE: usize = 1024;

impl ItemIdx {
    fn new(slot: usize) -> Option<Self> {
        NonZeroU32::new(u32::try_from(slot).ok()?.checked_add(1)?).map(Self)
    }

    #[inline]
    pub(in crate::doc) fn slot(self) -> usize {
        (self.0.get() - 1) as usize
    }

    #[inline]
    fn location(self) -> (usize, usize) {
        let slot = self.slot();
        (slot / CHUNK_SIZE, slot % CHUNK_SIZE)
    }
}

/// Each chunk grows on demand up to CHUNK_SIZE entries.
#[derive(Debug, Default)]
pub(crate) struct ItemSpace {
    first: Vec<Option<Item>>,
    rest: Vec<Vec<Option<Item>>>,
    slots: usize,
    free: Vec<ItemIdx>,
    quarantine: Vec<ItemIdx>,
    #[cfg(test)]
    limit: Option<usize>,
}

impl ItemSpace {
    pub fn check_capacity(&self, additional: usize) -> JwstCodecResult {
        #[cfg(test)]
        let limit = self.limit.unwrap_or(u32::MAX as usize);
        #[cfg(not(test))]
        let limit = u32::MAX as usize;
        if self
            .slots
            .checked_sub(self.free.len())
            .and_then(|occupied| occupied.checked_add(additional))
            .is_none_or(|n| n > limit)
        {
            return Err(JwstCodecError::IncompleteDocument(
                "the document holds too many items".into(),
            ));
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn set_limit(&mut self, limit: usize) {
        self.limit = Some(limit.min(u32::MAX as usize));
    }

    #[inline]
    fn chunk_mut(&mut self, index: usize) -> Option<&mut Vec<Option<Item>>> {
        if index == 0 {
            Some(&mut self.first)
        } else {
            self.rest.get_mut(index - 1)
        }
    }

    #[inline]
    fn slot_mut(&mut self, id: ItemIdx) -> Option<&mut Option<Item>> {
        let (chunk, offset) = id.location();
        self.chunk_mut(chunk)?.get_mut(offset)
    }

    pub fn alloc(&mut self, item: Item) -> JwstCodecResult<ItemIdx> {
        #[cfg(test)]
        self.check_capacity(1)?;
        if let Some(id) = self.free.pop() {
            *self.slot_mut(id).expect("allocated slot") = Some(item);
            return Ok(id);
        }
        let id = ItemIdx::new(self.slots)
            .ok_or_else(|| JwstCodecError::IncompleteDocument("the document holds too many items".into()))?;
        let (chunk, offset) = id.location();
        if chunk > 0 && offset == 0 {
            self.rest.push(Vec::new());
        }
        self.chunk_mut(chunk).expect("allocated chunk").push(Some(item));
        self.slots += 1;
        Ok(id)
    }

    #[inline]
    pub fn get(&self, id: ItemIdx) -> Option<&Item> {
        let (chunk, offset) = id.location();
        if chunk == 0 {
            self.first.get(offset)?.as_ref()
        } else {
            self.rest.get(chunk - 1)?.get(offset)?.as_ref()
        }
    }

    #[inline]
    pub fn get_mut(&mut self, id: ItemIdx) -> Option<&mut Item> {
        self.slot_mut(id)?.as_mut()
    }

    pub fn get_two_mut(&mut self, a: ItemIdx, b: ItemIdx) -> Option<(&mut Item, &mut Item)> {
        if a == b {
            return None;
        }
        let reversed = a.slot() > b.slot();
        let (left, right) = if reversed { (b, a) } else { (a, b) };
        let (lc, li) = left.location();
        let (rc, ri) = right.location();
        let (left, right) = if lc == rc {
            let (before, after) = self.chunk_mut(lc)?.split_at_mut_checked(ri)?;
            (before.get_mut(li)?, after.first_mut()?)
        } else if lc == 0 {
            (self.first.get_mut(li)?, self.rest.get_mut(rc - 1)?.get_mut(ri)?)
        } else {
            let (before, after) = self.rest.split_at_mut_checked(rc - 1)?;
            (before.get_mut(lc - 1)?.get_mut(li)?, after.first_mut()?.get_mut(ri)?)
        };
        let (left, right) = (left.as_mut()?, right.as_mut()?);
        Some(if reversed { (right, left) } else { (left, right) })
    }

    pub fn retire(&mut self, id: ItemIdx) {
        self.slot_mut(id).and_then(Option::take).expect("retiring a live item");
        self.quarantine.push(id);
    }

    #[cfg(test)]
    pub(super) fn live(&self) -> impl Iterator<Item = (ItemIdx, &Item)> {
        self.first
            .iter()
            .chain(self.rest.iter().flatten())
            .enumerate()
            .filter_map(|(i, slot)| Some((ItemIdx::new(i)?, slot.as_ref()?)))
    }

    pub fn live_mut(&mut self) -> impl Iterator<Item = &mut Item> {
        self.first
            .iter_mut()
            .chain(self.rest.iter_mut().flatten())
            .filter_map(Option::as_mut)
    }

    /// Called after the transaction has finished using temporary cursors.
    /// Live items move in place toward the front; the only full-size scratch
    /// allocation holds four bytes per old slot.
    pub fn finish(&mut self) -> Option<Vec<Option<ItemIdx>>> {
        self.free.append(&mut self.quarantine);
        let compact = self.slots >= 256 && self.free.len() as u64 * 5 > self.slots as u64 * 2;
        if !compact && self.free.len() != self.slots {
            return None;
        }
        if self.free.is_empty() {
            return None;
        }
        let mut remap = vec![None; self.slots];
        let mut live = 0;
        for (slot, entry) in remap.iter_mut().enumerate() {
            let old = ItemIdx::new(slot).expect("allocated slot");
            let source = self.slot_mut(old).expect("allocated slot");
            if source.is_none() {
                continue;
            }
            let new = ItemIdx::new(live).expect("allocated slot");
            if old != new {
                let item = source.take();
                *self.slot_mut(new).expect("allocated slot") = item;
            }
            *entry = Some(new);
            live += 1;
        }
        if let Some(last) = live.checked_sub(1).and_then(ItemIdx::new) {
            let (chunk, offset) = last.location();
            self.rest.truncate(chunk);
            let tail = self.chunk_mut(chunk).expect("last live chunk");
            tail.truncate(offset + 1);
            tail.shrink_to_fit();
        } else {
            self.first = Vec::new();
            self.rest.clear();
        }
        self.rest.shrink_to_fit();
        self.free = Vec::new();
        self.quarantine = Vec::new();
        self.slots = live;
        Some(remap)
    }
}

#[cfg(test)]
mod tests {
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
        let before = 1 + arena.rest.len();
        let remap = arena.finish().unwrap();
        assert!((1 + arena.rest.len()) * 5 < before);
        assert_eq!(arena.slots, count.div_ceil(10) + 1);
        for (i, id) in ids.iter().enumerate() {
            match remap[id.slot()] {
                Some(new) => {
                    assert_eq!(i % 10, 0);
                    assert_eq!(arena.get(new).unwrap().id.clock, i as u64);
                }
                None => assert_ne!(i % 10, 0),
            }
        }
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
        let allocated = || {
            let store = doc.store.read().unwrap();
            let space = &store.type_arena.items;
            space.first.capacity() + space.rest.iter().map(Vec::capacity).sum::<usize>()
        };
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
            let actual: HashSet<_> = (0..space.slots)
                .map(|i| ItemIdx::new(i).unwrap())
                .filter(|i| space.get(*i).is_some())
                .collect();
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
