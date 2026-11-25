//! The sequence half of `DocStore` (`y-octo/src/doc/store.rs`) as an index
//! core: one YATA sequence whose items live in an arena and name their
//! neighbours by slot, next to the block timeline of every client.
//!
//! It has what a root sequence needs and nothing else: `integrate` (the
//! `repair` splits, the conflict scan of `find_conflict_left`, the links),
//! `split`, `merge_adjacent`, `delete_range`, `gc` (deleted items drop their
//! content) and `visible_ids`. Content, parents, map keys, nested types and
//! the pending queue stay in `y-octo`. A slot is never reused: a merged item
//! leaves its slot behind, where `ItemSpace` of `y-octo` would recycle it.

use alloc::vec::Vec;

use crate::client_blocks::{BlockKindCore, BlockRefCore, ClientBlocksCore, MAX_BLOCKS, StoreError};

/// The arena never holds more items than a `u32` slot can name.
pub const MAX_ITEMS: usize = 4_294_967_295;

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct IdCore {
    pub client: u64,
    pub clock: u64,
}

/// An item of the sequence: the clocks `id.clock .. id.clock + len` of
/// `id.client`. `origin_left` and `origin_right` are the origins of its first
/// clock; `left` and `right` are the slots of its neighbours. `gc` says that
/// the content of a deleted item is gone (`Content::Deleted`).
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct ItemCore {
    pub id: IdCore,
    pub len: u64,
    pub origin_left: Option<IdCore>,
    pub origin_right: Option<IdCore>,
    pub left: Option<u32>,
    pub right: Option<u32>,
    pub deleted: bool,
    pub gc: bool,
}

#[cfg_attr(not(aeneas_extract), derive(Clone, Debug, PartialEq, Eq))]
pub struct ClientEntryCore {
    pub client: u64,
    pub blocks: ClientBlocksCore,
}

#[cfg_attr(not(aeneas_extract), derive(Clone, Debug, PartialEq, Eq))]
pub struct YataStoreCore {
    pub items: Vec<ItemCore>,
    /// the first item of the sequence
    pub start: Option<u32>,
    pub clients: Vec<ClientEntryCore>,
}

fn id_eq(a: IdCore, b: IdCore) -> bool {
    a.client == b.client && a.clock == b.clock
}

fn opt_id_eq(a: Option<IdCore>, b: Option<IdCore>) -> bool {
    match a {
        Some(x) => match b {
            Some(y) => id_eq(x, y),
            None => false,
        },
        None => match b {
            Some(_) => false,
            None => true,
        },
    }
}

fn opt_slot_eq(a: Option<u32>, b: Option<u32>) -> bool {
    match a {
        Some(x) => match b {
            Some(y) => x == y,
            None => false,
        },
        None => match b {
            Some(_) => false,
            None => true,
        },
    }
}

fn slot_is(a: Option<u32>, b: u32) -> bool {
    match a {
        Some(x) => x == b,
        None => false,
    }
}

/// What the conflict scan does with a candidate: it ends, it goes on, or it
/// goes on with the candidate as the new left neighbour.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
enum ScanStep {
    Stop,
    Skip,
    Take,
}

/// An item cannot anchor to a struct of its client created at or after
/// itself.
fn check_origin(id: IdCore, origin: Option<IdCore>) -> Result<(), StoreError> {
    match origin {
        Some(origin) => {
            if origin.client == id.client && origin.clock >= id.clock {
                Err(StoreError::InvalidOrigin)
            } else {
                Ok(())
            }
        }
        None => Ok(()),
    }
}

/// The conditions of `DocStore::merge_items`: `right` (slot `r`) follows
/// `left` (slot `l`) in the sequence and continues it: its first clock is
/// the next one, typed right after the last clock of `left`, with the same
/// right origin, and both hold the same kind of content.
fn continues(left: ItemCore, l: u32, right: ItemCore, r: u32) -> bool {
    if !slot_is(left.right, r) || !slot_is(right.left, l) {
        return false;
    }
    let after_last = match right.origin_left {
        Some(origin) => origin.client == left.id.client && origin.clock == left.id.clock + (left.len - 1),
        None => false,
    };
    after_last && opt_id_eq(left.origin_right, right.origin_right) && left.gc == right.gc
}

fn ids_contain(ids: &[IdCore], id: IdCore) -> bool {
    let mut i = 0usize;
    while i < ids.len() {
        if id_eq(ids[i], id) {
            return true;
        }
        i += 1;
    }
    false
}

impl Default for YataStoreCore {
    fn default() -> Self {
        Self::new()
    }
}

impl YataStoreCore {
    pub fn new() -> Self {
        Self {
            items: Vec::new(),
            start: None,
            clients: Vec::new(),
        }
    }

    fn client_index(&self, client: u64) -> Option<usize> {
        let mut i = 0usize;
        while i < self.clients.len() {
            if self.clients[i].client == client {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    /// `DocStore::get_state`: the next clock expected from `client`.
    pub fn get_state(&self, client: u64) -> u64 {
        match self.client_index(client) {
            Some(ci) => self.clients[ci].blocks.end_clock,
            None => 0,
        }
    }

    /// The timeline and the block in it that hold `id`.
    fn locate(&self, id: IdCore) -> Option<(usize, usize)> {
        match self.client_index(id.client) {
            Some(ci) => match self.clients[ci].blocks.find(id.clock) {
                Some(pos) => Some((ci, pos)),
                None => None,
            },
            None => None,
        }
    }

    /// `DocStore::get_node_id`: the first id of the struct that holds `id`.
    pub fn node_id(&self, id: IdCore) -> Option<IdCore> {
        match self.locate(id) {
            Some((ci, pos)) => Some(IdCore {
                client: id.client,
                clock: self.clients[ci].blocks.blocks[pos].clock,
            }),
            None => None,
        }
    }

    /// Makes `value` the left neighbour of the item at `slot`, if there is
    /// one.
    fn set_left(&mut self, slot: Option<u32>, value: u32) {
        match slot {
            Some(idx) => self.items[idx as usize].left = Some(value),
            None => {}
        }
    }

    /// Makes `value` the right neighbour of the item at `slot`; without a
    /// slot, the first item of the sequence.
    fn set_next(&mut self, slot: Option<u32>, value: u32) {
        match slot {
            Some(idx) => self.items[idx as usize].right = Some(value),
            None => self.start = Some(value),
        }
    }

    /// `DocStore::split_node`: the item of the block `pos` of the timeline
    /// `ci` keeps its first `diff` clocks (`0 < diff < len`); the rest is a
    /// new item right after it. Returns the slots of the two halves.
    fn split_node(&mut self, ci: usize, pos: usize, diff: u64) -> Result<(u32, u32), StoreError> {
        let block = self.clients[ci].blocks.blocks[pos];
        let left_idx = match block.kind.item() {
            Some(idx) => idx,
            None => return Err(StoreError::NotAnItem),
        };
        if self.items.len() >= MAX_ITEMS {
            return Err(StoreError::Capacity);
        }
        let item = self.items[left_idx as usize];
        let right_idx = self.items.len() as u32;
        let clock = item.id.clock + diff;
        let right = ItemCore {
            id: IdCore {
                client: item.id.client,
                clock,
            },
            len: item.len - diff,
            origin_left: Some(IdCore {
                client: item.id.client,
                clock: clock - 1,
            }),
            origin_right: item.origin_right,
            left: Some(left_idx),
            right: item.right,
            deleted: item.deleted,
            gc: item.gc,
        };
        let kind = if block.kind.deleted() {
            BlockKindCore::DeletedItem(right_idx)
        } else {
            BlockKindCore::Item(right_idx)
        };
        // the timeline first: it refuses a split that is not inside the block
        match self.clients[ci].blocks.split_boundary(pos, clock, kind) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        self.items[left_idx as usize].len = diff;
        self.items.push(right);
        self.set_next(Some(left_idx), right_idx);
        self.set_left(item.right, right_idx);
        Ok((left_idx, right_idx))
    }

    /// `DocStore::split_at_and_get_right`: afterwards a struct starts at
    /// `id`. Returns its slot when it is an item.
    pub fn split(&mut self, id: IdCore) -> Result<Option<u32>, StoreError> {
        let (ci, pos) = match self.locate(id) {
            Some(found) => found,
            None => return Err(StoreError::MissingStruct),
        };
        let block = self.clients[ci].blocks.blocks[pos];
        let idx = match block.kind.item() {
            Some(idx) => idx,
            None => return Ok(None),
        };
        if id.clock == block.clock {
            return Ok(Some(idx));
        }
        match self.split_node(ci, pos, id.clock - block.clock) {
            Ok((_, right)) => Ok(Some(right)),
            Err(error) => Err(error),
        }
    }

    /// `DocStore::split_at_and_get_left`: afterwards a struct ends at `id`.
    /// Returns its slot when it is an item.
    pub fn split_after(&mut self, id: IdCore) -> Result<Option<u32>, StoreError> {
        let (ci, pos) = match self.locate(id) {
            Some(found) => found,
            None => return Err(StoreError::MissingStruct),
        };
        let block = self.clients[ci].blocks.blocks[pos];
        let idx = match block.kind.item() {
            Some(idx) => idx,
            None => return Ok(None),
        };
        let cut = id.clock - block.clock + 1;
        if cut >= self.items[idx as usize].len {
            return Ok(Some(idx));
        }
        match self.split_node(ci, pos, cut) {
            Ok((left, _)) => Ok(Some(left)),
            Err(error) => Err(error),
        }
    }

    /// The item right after `left` in the sequence; the first item of the
    /// sequence without a left neighbour.
    fn next_of(&self, left: Option<u32>) -> Option<u32> {
        match left {
            Some(idx) => self.items[idx as usize].right,
            None => self.start,
        }
    }

    /// One candidate of `find_conflict_left`, branch for branch. The two sets
    /// hold struct starts and already include the candidate.
    fn scan_step(
        &self,
        id: IdCore,
        origin_left: Option<IdCore>,
        origin_right: Option<IdCore>,
        candidate: ItemCore,
        before_origin: &[IdCore],
        conflicting: &[IdCore],
    ) -> ScanStep {
        if opt_id_eq(origin_left, candidate.origin_left) {
            if candidate.id.client < id.client {
                ScanStep::Take
            } else if opt_id_eq(origin_right, candidate.origin_right) {
                ScanStep::Stop
            } else {
                ScanStep::Skip
            }
        } else {
            let candidate_left = match candidate.origin_left {
                Some(origin) => origin,
                None => return ScanStep::Stop,
            };
            // origins can point inside a struct; the sets hold struct
            // starts
            let owner = match self.node_id(candidate_left) {
                Some(owner) => owner,
                None => return ScanStep::Stop,
            };
            if !ids_contain(before_origin, owner) {
                ScanStep::Stop
            } else if !ids_contain(conflicting, owner) {
                ScanStep::Take
            } else {
                ScanStep::Skip
            }
        }
    }

    /// `find_conflict_left` of `y-octo/src/doc/common/algorithm.rs`:
    /// `conflict` is the first candidate, `left` the neighbour found so far.
    fn find_conflict_left(
        &self,
        id: IdCore,
        origin_left: Option<IdCore>,
        origin_right: Option<IdCore>,
        left: Option<u32>,
        conflict: Option<u32>,
        right: Option<u32>,
    ) -> Option<u32> {
        let mut left = left;
        let mut conflict = conflict;
        let mut conflicting: Vec<IdCore> = Vec::new();
        let mut before_origin: Vec<IdCore> = Vec::new();
        while let Some(current) = conflict {
            if slot_is(right, current) {
                break;
            }
            let candidate = self.items[current as usize];
            before_origin.push(candidate.id);
            conflicting.push(candidate.id);
            match self.scan_step(id, origin_left, origin_right, candidate, &before_origin, &conflicting) {
                ScanStep::Stop => break,
                ScanStep::Take => {
                    left = Some(current);
                    conflicting = Vec::new();
                }
                ScanStep::Skip => {}
            }
            conflict = candidate.right;
        }
        left
    }

    /// `DocStore::check_append`: the struct continues the timeline of its
    /// client and its clocks do not overflow.
    fn check_append(&self, id: IdCore, len: u64) -> Result<(), StoreError> {
        let continues = match self.client_index(id.client) {
            Some(ci) => self.clients[ci].blocks.continues(id.clock),
            None => true,
        };
        if !continues {
            return Err(StoreError::ClockMismatch);
        }
        if len > u64::MAX - id.clock {
            return Err(StoreError::ClockOverflow);
        }
        Ok(())
    }

    /// The timeline of `client`, created empty when it has none yet.
    fn ensure_client(&mut self, client: u64) -> Result<usize, StoreError> {
        match self.client_index(client) {
            Some(ci) => Ok(ci),
            None => {
                if self.clients.len() >= MAX_ITEMS {
                    return Err(StoreError::Capacity);
                }
                let ci = self.clients.len();
                self.clients.push(ClientEntryCore {
                    client,
                    blocks: ClientBlocksCore::new(),
                });
                Ok(ci)
            }
        }
    }

    /// `DocStore::repair`, left origin: a struct ends at the origin. Returns
    /// the slot of that struct and its last id; nothing when it is no item.
    fn repair_left(&mut self, origin: Option<IdCore>) -> Result<(Option<u32>, Option<IdCore>), StoreError> {
        let origin = match origin {
            Some(origin) => origin,
            None => return Ok((None, None)),
        };
        let slot = match self.split_after(origin) {
            Ok(slot) => slot,
            Err(error) => return Err(error),
        };
        match slot {
            Some(idx) => {
                let item = self.items[idx as usize];
                let last = IdCore {
                    client: item.id.client,
                    clock: item.id.clock + (item.len - 1),
                };
                Ok((Some(idx), Some(last)))
            }
            None => Ok((None, None)),
        }
    }

    /// `DocStore::repair`, right origin: a struct starts at the origin.
    /// Returns the slot of that struct and its id; nothing when it is no
    /// item.
    fn repair_right(&mut self, origin: Option<IdCore>) -> Result<(Option<u32>, Option<IdCore>), StoreError> {
        let origin = match origin {
            Some(origin) => origin,
            None => return Ok((None, None)),
        };
        let slot = match self.split(origin) {
            Ok(slot) => slot,
            Err(error) => return Err(error),
        };
        match slot {
            Some(idx) => Ok((Some(idx), Some(self.items[idx as usize].id))),
            None => Ok((None, None)),
        }
    }

    /// Whether other items may sit between `left` and `right`: unless
    /// `right` follows `left` directly, or is the first item when there is
    /// no `left`.
    fn needs_scan(&self, left: Option<u32>, right: Option<u32>) -> bool {
        match left {
            Some(idx) => !opt_slot_eq(self.items[idx as usize].right, right),
            None => match right {
                Some(idx) => match self.items[idx as usize].left {
                    Some(_) => true,
                    None => false,
                },
                None => true,
            },
        }
    }

    /// The left neighbour of a new item between `left` and `right`:
    /// `find_conflict_left` when other items may sit between the two.
    fn conflict_left(
        &self,
        id: IdCore,
        origin_left: Option<IdCore>,
        origin_right: Option<IdCore>,
        left: Option<u32>,
        right: Option<u32>,
    ) -> Option<u32> {
        if self.needs_scan(left, right) {
            self.find_conflict_left(id, origin_left, origin_right, left, self.next_of(left), right)
        } else {
            left
        }
    }

    /// The linking half of `DocStore::integrate_item`: the item becomes the
    /// right neighbour of `left` (the first item without one) and the last
    /// block of the timeline of its client.
    fn link(
        &mut self,
        id: IdCore,
        len: u64,
        origin_left: Option<IdCore>,
        origin_right: Option<IdCore>,
        left: Option<u32>,
    ) -> Result<u32, StoreError> {
        if self.items.len() >= MAX_ITEMS {
            return Err(StoreError::Capacity);
        }
        let next = self.next_of(left);
        let ci = match self.ensure_client(id.client) {
            Ok(ci) => ci,
            Err(error) => return Err(error),
        };
        let idx = self.items.len() as u32;
        let block = BlockRefCore {
            clock: id.clock,
            kind: BlockKindCore::Item(idx),
        };
        match self.clients[ci].blocks.append(block, len) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        self.items.push(ItemCore {
            id,
            len,
            origin_left,
            origin_right,
            left,
            right: next,
            deleted: false,
            gc: false,
        });
        self.set_next(left, idx);
        self.set_left(next, idx);
        Ok(idx)
    }

    /// `DocStore::repair` and `DocStore::integrate_item` for a live item of
    /// the sequence: splits at the two origins, runs the conflict scan and
    /// links the item where it stops. Returns the slot of the item.
    pub fn integrate(
        &mut self,
        id: IdCore,
        len: u64,
        origin_left: Option<IdCore>,
        origin_right: Option<IdCore>,
    ) -> Result<u32, StoreError> {
        if len == 0 {
            return Err(StoreError::ZeroLength);
        }
        match check_origin(id, origin_left) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        match check_origin(id, origin_right) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        match self.check_append(id, len) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        // two splits and the item itself
        if self.items.len() > MAX_ITEMS - 3 {
            return Err(StoreError::Capacity);
        }
        let (left, this_left) = match self.repair_left(origin_left) {
            Ok(found) => found,
            Err(error) => return Err(error),
        };
        let (right, this_right) = match self.repair_right(origin_right) {
            Ok(found) => found,
            Err(error) => return Err(error),
        };
        let left = self.conflict_left(id, this_left, this_right, left, right);
        self.link(id, len, this_left, this_right, left)
    }

    /// `DocStore::merge_items` and the timeline half of `merge_with_lefts`
    /// for the struct that holds `id` and its successor on the timeline:
    /// when they are neighbours of the sequence too and the second continues
    /// the first, they become one item. Returns whether they did.
    pub fn merge_adjacent(&mut self, id: IdCore) -> Result<bool, StoreError> {
        let (ci, pos) = match self.locate(id) {
            Some(found) => found,
            None => return Err(StoreError::MissingStruct),
        };
        let next_pos = pos + 1;
        if next_pos >= self.clients[ci].blocks.len() {
            return Ok(false);
        }
        let left_kind = self.clients[ci].blocks.blocks[pos].kind;
        let right_kind = self.clients[ci].blocks.blocks[next_pos].kind;
        if !left_kind.same_kind(right_kind) {
            return Ok(false);
        }
        let l = match left_kind.item() {
            Some(idx) => idx,
            None => return Ok(false),
        };
        let r = match right_kind.item() {
            Some(idx) => idx,
            None => return Ok(false),
        };
        let left = self.items[l as usize];
        let right = self.items[r as usize];
        if !continues(left, l, right, r) {
            return Ok(false);
        }
        match self.clients[ci].blocks.merge_adjacent(pos) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        self.items[l as usize].len = left.len + right.len;
        self.items[l as usize].right = right.right;
        self.set_left(right.right, l);
        Ok(true)
    }

    /// Makes `clock` the first clock of a block of the timeline `ci` when a
    /// live item holds it after its first clock.
    fn split_inside(&mut self, ci: usize, clock: u64) -> Result<(), StoreError> {
        let pos = match self.clients[ci].blocks.find(clock) {
            Some(pos) => pos,
            None => return Ok(()),
        };
        let start = self.clients[ci].blocks.blocks[pos].clock;
        let live = match self.clients[ci].blocks.blocks[pos].kind {
            BlockKindCore::Item(_) => true,
            BlockKindCore::DeletedItem(_) => false,
            BlockKindCore::Gc => false,
            BlockKindCore::Skip => false,
        };
        if live && start < clock {
            match self.split_node(ci, pos, clock - start) {
                Ok(_) => Ok(()),
                Err(error) => Err(error),
            }
        } else {
            Ok(())
        }
    }

    /// Deletes the block `pos` of the timeline `ci` when it is a live item.
    fn delete_block(&mut self, ci: usize, pos: usize) -> Result<(), StoreError> {
        let slot = match self.clients[ci].blocks.blocks[pos].kind {
            BlockKindCore::Item(idx) => Some(idx),
            BlockKindCore::DeletedItem(_) => None,
            BlockKindCore::Gc => None,
            BlockKindCore::Skip => None,
        };
        let idx = match slot {
            Some(idx) => idx,
            None => return Ok(()),
        };
        match self.clients[ci].blocks.mark_deleted(pos) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        self.items[idx as usize].deleted = true;
        Ok(())
    }

    /// `DocStore::delete_range`: deletes the clocks `start..end` of `client`
    /// the store holds, from the struct that holds `start` on; nothing when
    /// it does not hold `start` or the range is empty. Structs are split at
    /// the two ends of the range unless they are deleted already.
    ///
    /// Everything that can fail (the room for the two splits, the splits
    /// themselves) comes before the first struct is deleted: an error leaves
    /// the deletions of the store as they were.
    pub fn delete_range(&mut self, client: u64, start: u64, end: u64) -> Result<(), StoreError> {
        let ci = match self.client_index(client) {
            Some(ci) => ci,
            None => return Ok(()),
        };
        match self.clients[ci].blocks.find(start) {
            Some(_) => {}
            None => return Ok(()),
        }
        if start >= end {
            return Ok(());
        }
        // one split at each end of the range: an item and a block each
        if self.items.len() > MAX_ITEMS - 2 {
            return Err(StoreError::Capacity);
        }
        if self.clients[ci].blocks.len() > MAX_BLOCKS - 2 {
            return Err(StoreError::Capacity);
        }
        match self.split_inside(ci, start) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        match self.split_inside(ci, end) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        // no live struct reaches over `start` or `end` any more: delete the
        // live ones from the struct that holds `start` to `end`
        let mut pos = match self.clients[ci].blocks.find(start) {
            Some(pos) => pos,
            None => return Ok(()),
        };
        loop {
            let block_start = match self.clients[ci].blocks.range(pos) {
                Some((block_start, _)) => block_start,
                None => return Ok(()),
            };
            if block_start >= end {
                return Ok(());
            }
            match self.delete_block(ci, pos) {
                Ok(()) => {}
                Err(error) => return Err(error),
            }
            pos += 1;
        }
    }

    /// `gc_item_content(_, parent_gced = false)` for every deleted item: it
    /// keeps its place in the sequence and drops its content.
    pub fn gc(&mut self) {
        let mut i = 0usize;
        while i < self.items.len() {
            if self.items[i].deleted {
                self.items[i].gc = true;
            }
            i += 1;
        }
    }

    /// First id and length of every item that is not deleted, in the order
    /// of the sequence.
    pub fn visible_ids(&self) -> Vec<(IdCore, u64)> {
        let mut out: Vec<(IdCore, u64)> = Vec::new();
        let mut cursor = self.start;
        while let Some(idx) = cursor {
            let item = self.items[idx as usize];
            if !item.deleted {
                out.push((item.id, item.len));
            }
            cursor = item.right;
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(client: u64, clock: u64) -> IdCore {
        IdCore { client, clock }
    }

    /// Every item of the sequence, in order: id, length, deleted.
    fn sequence(store: &YataStoreCore) -> Vec<(IdCore, u64, bool)> {
        let mut out = Vec::new();
        let mut cursor = store.start;
        let mut prev = None;
        while let Some(idx) = cursor {
            let item = store.items[idx as usize];
            assert_eq!(item.left, prev, "left link of slot {idx}");
            out.push((item.id, item.len, item.deleted));
            prev = cursor;
            cursor = item.right;
        }
        out
    }

    /// The timelines agree with the items they name.
    fn check(store: &YataStoreCore) {
        let mut linked = sequence(store).len();
        for entry in &store.clients {
            for (pos, block) in entry.blocks.blocks.iter().enumerate() {
                let (start, end) = entry.blocks.range(pos).unwrap();
                assert!(start < end);
                let idx = block.kind.item().expect("the sequence holds items only");
                let item = store.items[idx as usize];
                assert_eq!(item.id, id(entry.client, start));
                assert_eq!(item.len, end - start);
                assert_eq!(item.deleted, block.kind.deleted());
                assert!(!item.gc || item.deleted);
                linked -= 1;
            }
        }
        assert_eq!(linked, 0, "every linked item is on a timeline");
    }

    #[test]
    fn concurrent_inserts_at_the_same_place_order_by_client() {
        // three replicas insert at the start of the empty sequence
        let orders: [[u64; 3]; 6] = [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]];
        for order in orders {
            let mut store = YataStoreCore::new();
            for client in order {
                store.integrate(id(client, 0), 2, None, None).unwrap();
                check(&store);
            }
            assert_eq!(
                sequence(&store),
                [(id(1, 0), 2, false), (id(2, 0), 2, false), (id(3, 0), 2, false)]
            );
        }
    }

    #[test]
    fn integrate_splits_at_the_origins() {
        let mut store = YataStoreCore::new();
        store.integrate(id(1, 0), 6, None, None).unwrap();
        // between clocks 2 and 3 of the first item
        store.integrate(id(2, 0), 1, Some(id(1, 2)), Some(id(1, 3))).unwrap();
        check(&store);
        assert_eq!(
            sequence(&store),
            [(id(1, 0), 3, false), (id(2, 0), 1, false), (id(1, 3), 3, false)]
        );
        // the right half names the last clock of the left half
        let right = store.items[1];
        assert_eq!(right.origin_left, Some(id(1, 2)));
        assert_eq!(store.node_id(id(1, 5)), Some(id(1, 3)));
        assert_eq!(store.node_id(id(1, 6)), None);
        assert_eq!(store.get_state(1), 6);
        assert_eq!(store.get_state(2), 1);
        assert_eq!(store.get_state(9), 0);
    }

    #[test]
    fn a_later_origin_inside_the_scanned_prefix_does_not_move_the_item() {
        // 1 writes "ab"; 2 inserts after "a"; 3 inserts after "a" too, with
        // the item of 2 as right origin. Whatever the order, 2 < 3 by client.
        let mut store = YataStoreCore::new();
        store.integrate(id(1, 0), 2, None, None).unwrap();
        store.integrate(id(3, 0), 1, Some(id(1, 0)), Some(id(1, 1))).unwrap();
        store.integrate(id(2, 0), 1, Some(id(1, 0)), Some(id(1, 1))).unwrap();
        check(&store);
        assert_eq!(
            sequence(&store),
            [
                (id(1, 0), 1, false),
                (id(2, 0), 1, false),
                (id(3, 0), 1, false),
                (id(1, 1), 1, false)
            ]
        );
        // an item that names 3 as its left origin stays right of it
        store.integrate(id(4, 0), 1, Some(id(3, 0)), Some(id(1, 1))).unwrap();
        check(&store);
        assert_eq!(sequence(&store)[3], (id(4, 0), 1, false));
    }

    #[test]
    fn integrate_refuses_bad_structs_without_linking_them() {
        let mut store = YataStoreCore::new();
        assert_eq!(store.integrate(id(1, 0), 0, None, None), Err(StoreError::ZeroLength));
        store.integrate(id(1, 0), 2, None, None).unwrap();
        assert_eq!(store.integrate(id(1, 3), 1, None, None), Err(StoreError::ClockMismatch));
        assert_eq!(
            store.integrate(id(1, 2), u64::MAX, None, None),
            Err(StoreError::ClockOverflow)
        );
        assert_eq!(
            store.integrate(id(1, 2), 1, Some(id(1, 2)), None),
            Err(StoreError::InvalidOrigin)
        );
        assert_eq!(
            store.integrate(id(2, 0), 1, Some(id(7, 0)), None),
            Err(StoreError::MissingStruct)
        );
        assert_eq!(
            store.integrate(id(2, 0), 1, None, Some(id(1, 2))),
            Err(StoreError::MissingStruct)
        );
        check(&store);
        assert_eq!(sequence(&store), [(id(1, 0), 2, false)]);
        assert_eq!(store.clients.len(), 1);
    }

    #[test]
    fn delete_range_splits_live_items_only() {
        let mut store = YataStoreCore::new();
        store.integrate(id(1, 0), 10, None, None).unwrap();
        store.delete_range(1, 3, 6).unwrap();
        check(&store);
        assert_eq!(
            sequence(&store),
            [(id(1, 0), 3, false), (id(1, 3), 3, true), (id(1, 6), 4, false)]
        );
        // inside the deleted item: nothing to do, and no split
        store.delete_range(1, 4, 5).unwrap();
        assert_eq!(store.items.len(), 3);
        // across deleted and live items, and beyond the state of the client
        store.delete_range(1, 4, 99).unwrap();
        check(&store);
        assert_eq!(
            sequence(&store),
            [(id(1, 0), 3, false), (id(1, 3), 3, true), (id(1, 6), 4, true)]
        );
        // unknown clocks and clients are ignored
        store.delete_range(1, 10, 12).unwrap();
        store.delete_range(5, 0, 1).unwrap();
        store.delete_range(1, 2, 2).unwrap();
        check(&store);
        assert_eq!(store.visible_ids(), vec![(id(1, 0), 3)]);
    }

    #[test]
    fn merge_needs_a_continuation_in_the_sequence_and_on_the_timeline() {
        let mut store = YataStoreCore::new();
        store.integrate(id(1, 0), 4, None, None).unwrap();
        store.split(id(1, 2)).unwrap();
        check(&store);
        assert_eq!(sequence(&store), [(id(1, 0), 2, false), (id(1, 2), 2, false)]);
        assert_eq!(store.merge_adjacent(id(1, 1)), Ok(true));
        check(&store);
        assert_eq!(sequence(&store), [(id(1, 0), 4, false)]);
        // the last struct of a timeline has no successor
        assert_eq!(store.merge_adjacent(id(1, 0)), Ok(false));
        assert_eq!(store.merge_adjacent(id(1, 4)), Err(StoreError::MissingStruct));

        // an item in between, a different deleted state, a successor that sits
        // elsewhere in the sequence
        store.integrate(id(2, 0), 1, Some(id(1, 1)), Some(id(1, 2))).unwrap();
        assert_eq!(store.merge_adjacent(id(1, 0)), Ok(false));
        store.integrate(id(1, 4), 1, Some(id(1, 3)), None).unwrap();
        store.delete_range(1, 4, 5).unwrap();
        assert_eq!(store.merge_adjacent(id(1, 2)), Ok(false));
        store.integrate(id(1, 5), 1, Some(id(1, 3)), None).unwrap();
        store.delete_range(1, 5, 6).unwrap();
        assert_eq!(store.merge_adjacent(id(1, 4)), Ok(false));
        check(&store);
        assert_eq!(sequence(&store).len(), 5);
    }

    #[test]
    fn gc_drops_the_content_of_deleted_items_and_keeps_them_apart_from_live_ones() {
        let mut store = YataStoreCore::new();
        store.integrate(id(1, 0), 6, None, None).unwrap();
        store.delete_range(1, 2, 4).unwrap();
        store.gc();
        check(&store);
        let flags: Vec<_> = store.items.iter().map(|item| (item.deleted, item.gc)).collect();
        assert_eq!(flags, [(false, false), (true, true), (false, false)]);
        // a deleted half that was collected does not merge with one that was
        // not
        store.delete_range(1, 4, 5).unwrap();
        assert_eq!(store.merge_adjacent(id(1, 2)), Ok(false));
        store.gc();
        assert_eq!(store.merge_adjacent(id(1, 2)), Ok(true));
        check(&store);
        assert_eq!(
            sequence(&store),
            [(id(1, 0), 2, false), (id(1, 2), 3, true), (id(1, 5), 1, false)]
        );
        assert_eq!(store.visible_ids(), vec![(id(1, 0), 2), (id(1, 5), 1)]);
    }
}
