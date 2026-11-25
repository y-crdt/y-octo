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
//!
//! The conflict scan keeps the candidates it has walked in one list, as the
//! scan of `y-octo` does (`IdOrderCore`, under the key the store was made
//! with), and the decisions a root sequence shares with `DocStore` are the
//! functions of `doc_kernel` both run.

use alloc::vec::Vec;

use crate::{
    client_blocks::{BlockKindCore, BlockRefCore, ClientBlocksCore, MAX_BLOCKS, StoreError},
    doc_kernel::{MergeSide, can_merge_items, check_origin, needs_conflict_scan},
    id_order::{IdOrderCore, Recent},
};

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

#[cfg_attr(not(aeneas_extract), derive(Clone, Debug))]
pub struct ClientEntryCore {
    pub client: u64,
    pub blocks: ClientBlocksCore,
}

#[cfg_attr(not(aeneas_extract), derive(Clone, Debug))]
pub struct YataStoreCore {
    // The fields are private: a store is only ever what `new` and the
    // functions below make of it, so the order of `clients` cannot be
    // broken from outside. `items`, `start` and `clients` read them.
    items: Vec<ItemCore>,
    /// the first item of the sequence
    start: Option<u32>,
    /// the timelines, by strictly increasing client
    clients: Vec<ClientEntryCore>,
    /// the key of the hash of a conflict scan (`IdOrderCore::with_key`)
    k0: u64,
    k1: u64,
}

#[inline]
pub(crate) fn id_eq(a: IdCore, b: IdCore) -> bool {
    a.client == b.client && a.clock == b.clock
}

#[inline]
pub(crate) fn opt_id_eq(a: Option<IdCore>, b: Option<IdCore>) -> bool {
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

#[inline]
pub(crate) fn opt_slot_eq(a: Option<u32>, b: Option<u32>) -> bool {
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

#[inline]
pub(crate) fn slot_is(a: Option<u32>, b: u32) -> bool {
    match a {
        Some(x) => x == b,
        None => false,
    }
}

/// What the conflict scan does with a candidate: it ends, it goes on, or it
/// goes on with the candidate as the new left neighbour.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum ScanStep {
    Stop,
    Skip,
    Take,
}

/// What the origins and the clients of an item and of a candidate of its
/// conflict scan decide: the step, or that the struct that holds the left
/// origin of the candidate has to be looked up first.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum ConflictDecision {
    Step(ScanStep),
    Owner(IdCore),
}

/// The first half of a step of `find_conflict_left` (the YATA rule), for an
/// item of `this_client` with the two origins `origin_left`/`origin_right`
/// and a candidate between them:
///
/// - the same left origin: the item goes right of a candidate of a smaller
///   client (`Take`), stops before one with the same right origin (`Stop`) and
///   goes on over any other (`Skip`);
/// - another left origin: the scan ends at a candidate without one (`Stop`);
///   with one, `decide_owner_step` decides once the caller knows where the
///   struct that holds it is (`Owner`).
///
/// `y-octo` runs this function in `find_conflict_left`, and so does
/// `YataStoreCore`, whose scan is proved to be the one of the model.
#[inline]
pub fn decide_conflict_step(
    this_client: u64,
    origin_left: Option<IdCore>,
    origin_right: Option<IdCore>,
    candidate_client: u64,
    candidate_left: Option<IdCore>,
    candidate_right: Option<IdCore>,
) -> ConflictDecision {
    if opt_id_eq(origin_left, candidate_left) {
        if candidate_client < this_client {
            ConflictDecision::Step(ScanStep::Take)
        } else if opt_id_eq(origin_right, candidate_right) {
            ConflictDecision::Step(ScanStep::Stop)
        } else {
            ConflictDecision::Step(ScanStep::Skip)
        }
    } else {
        match candidate_left {
            Some(origin) => ConflictDecision::Owner(origin),
            None => ConflictDecision::Step(ScanStep::Stop),
        }
    }
}

/// The second half, for a candidate with another left origin: `in_before`
/// says that the struct that holds this origin is one of the candidates the
/// scan has seen, `in_conflicting` that it is one seen since the left
/// neighbour last changed. The scan ends at an origin it has not seen
/// (`Stop`), takes a candidate whose origin is left of the left neighbour
/// (`Take`) and goes on over one whose origin is right of it (`Skip`).
#[inline]
pub fn decide_owner_step(in_before: bool, in_conflicting: bool) -> ScanStep {
    if !in_before {
        ScanStep::Stop
    } else if !in_conflicting {
        ScanStep::Take
    } else {
        ScanStep::Skip
    }
}

/// What `can_merge_items` reads of an item.
fn merge_side(item: ItemCore) -> MergeSide {
    MergeSide {
        id: item.id,
        len: item.len,
        origin_left: item.origin_left,
        origin_right: item.origin_right,
        left: item.left,
        right: item.right,
    }
}

/// The conditions of `DocStore::merge_items`: `right` (slot `r`) follows
/// `left` (slot `l`) in the sequence and continues it (`can_merge_items`:
/// its first clock is the next one, typed right after the last clock of
/// `left`, with the same right origin; the sequence is one list), and both
/// hold the same kind of content.
fn continues(left: ItemCore, l: u32, right: ItemCore, r: u32) -> bool {
    can_merge_items(merge_side(left), l, merge_side(right), r, true) && left.gc == right.gc
}

impl Default for YataStoreCore {
    fn default() -> Self {
        Self::new()
    }
}

impl YataStoreCore {
    /// The empty store. Its conflict scans hash under the key `(0, 0)`.
    pub fn new() -> Self {
        Self::with_key(0, 0)
    }

    /// The empty store whose conflict scans hash under the key `(k0, k1)`:
    /// two words the peers that choose the ids cannot know, so that the ids
    /// they send cannot be chosen to share their probes. The key changes
    /// where a scan looks an id up, never what it answers.
    pub fn with_key(k0: u64, k1: u64) -> Self {
        Self {
            items: Vec::new(),
            start: None,
            clients: Vec::new(),
            k0,
            k1,
        }
    }

    /// The arena of the items; the links between them are indices into it.
    pub fn items(&self) -> &[ItemCore] {
        &self.items
    }

    /// The first item of the sequence.
    pub fn start(&self) -> Option<u32> {
        self.start
    }

    /// The timelines, by strictly increasing client.
    pub fn clients(&self) -> &[ClientEntryCore] {
        &self.clients
    }

    /// Binary search of the timelines: whether `client` has one, and where
    /// it is, or where it goes.
    fn find_client(&self, client: u64) -> (bool, usize) {
        let mut low = 0usize;
        let mut high = self.clients.len();
        while low < high {
            let mid = low + (high - low) / 2;
            let at = self.clients[mid].client;
            if at == client {
                return (true, mid);
            } else if at < client {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        (false, low)
    }

    fn client_index(&self, client: u64) -> Option<usize> {
        let (found, index) = self.find_client(client);
        if found { Some(index) } else { None }
    }

    /// `DocStore::get_state`: the next clock expected from `client`.
    pub fn get_state(&self, client: u64) -> u64 {
        match self.client_index(client) {
            Some(ci) => self.clients[ci].blocks.end_clock(),
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
                clock: self.clients[ci].blocks.block_at(pos).clock,
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
        let block = self.clients[ci].blocks.block_at(pos);
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
        let block = self.clients[ci].blocks.block_at(pos);
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
        let block = self.clients[ci].blocks.block_at(pos);
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

    /// One candidate of `find_conflict_left`, branch for branch
    /// (`decide_conflict_step`, `decide_owner_step`). `order` holds the
    /// first ids of the candidates walked so far, the candidate among them
    /// (what Yjs keeps as the set `itemsBeforeOrigin`); the ones from the
    /// place `conflict_from` on came since the last candidate that was
    /// taken (`conflictingItems`). As in `y-octo`, the struct an origin
    /// points into is looked for among the last candidates first
    /// (`IdOrderCore::recent`) and through the table of the list only when
    /// it is not there (`IdOrderCore::position`).
    fn scan_step(
        &self,
        id: IdCore,
        origin_left: Option<IdCore>,
        origin_right: Option<IdCore>,
        candidate: ItemCore,
        order: &mut IdOrderCore,
        conflict_from: usize,
    ) -> ScanStep {
        let candidate_left = match decide_conflict_step(
            id.client,
            origin_left,
            origin_right,
            candidate.id.client,
            candidate.origin_left,
            candidate.origin_right,
        ) {
            ConflictDecision::Step(step) => return step,
            ConflictDecision::Owner(origin) => origin,
        };
        // origins can point inside a struct; the list holds struct starts
        let owner = match self.node_id(candidate_left) {
            Some(owner) => owner,
            None => return ScanStep::Stop,
        };
        let found = match order.recent(owner) {
            Recent::At(at) => Some(at),
            Recent::Absent => None,
            Recent::Far => order.position(owner),
        };
        match found {
            Some(at) => decide_owner_step(true, at >= conflict_from),
            None => decide_owner_step(false, false),
        }
    }

    /// `find_conflict_left` of `y-octo/src/doc/common/algorithm.rs`:
    /// `conflict` is the first candidate, `left` the neighbour found so far.
    /// It fails only when the list of the candidates cannot grow
    /// (`IdOrderCore::push`, past `2 ^ 30` of them).
    fn find_conflict_left(
        &self,
        id: IdCore,
        origin_left: Option<IdCore>,
        origin_right: Option<IdCore>,
        left: Option<u32>,
        conflict: Option<u32>,
        right: Option<u32>,
    ) -> Result<Option<u32>, StoreError> {
        let mut left = left;
        let mut conflict = conflict;
        let mut order = IdOrderCore::with_key(self.k0, self.k1);
        let mut conflict_from = 0usize;
        while let Some(current) = conflict {
            if slot_is(right, current) {
                break;
            }
            let candidate = self.items[current as usize];
            if !order.push(candidate.id) {
                return Err(StoreError::Capacity);
            }
            match self.scan_step(id, origin_left, origin_right, candidate, &mut order, conflict_from) {
                ScanStep::Stop => break,
                ScanStep::Take => {
                    left = Some(current);
                    // nothing conflicts with what comes after it yet
                    conflict_from = order.len();
                }
                ScanStep::Skip => {}
            }
            conflict = candidate.right;
        }
        Ok(left)
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

    /// The timeline of `client`, created empty at its place among the
    /// others when it has none yet.
    fn ensure_client(&mut self, client: u64) -> Result<usize, StoreError> {
        let (found, index) = self.find_client(client);
        if found {
            return Ok(index);
        }
        if self.clients.len() >= MAX_ITEMS {
            return Err(StoreError::Capacity);
        }
        let entry = ClientEntryCore {
            client,
            blocks: ClientBlocksCore::new(),
        };
        // `Vec::insert` at the end is `push` (Aeneas models `insert` below
        // the length only)
        if index == self.clients.len() {
            self.clients.push(entry);
        } else {
            self.clients.insert(index, entry);
        }
        Ok(index)
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

    /// Whether other items may sit between `left` and `right`
    /// (`needs_conflict_scan`): unless `right` follows `left` directly, or
    /// is the first item when there is no `left`.
    fn needs_scan(&self, left: Option<u32>, right: Option<u32>) -> bool {
        match left {
            Some(idx) => needs_conflict_scan(true, self.items[idx as usize].right, right, None),
            None => {
                let right_left = match right {
                    Some(idx) => self.items[idx as usize].left,
                    None => None,
                };
                needs_conflict_scan(false, None, right, right_left)
            }
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
    ) -> Result<Option<u32>, StoreError> {
        if self.needs_scan(left, right) {
            self.find_conflict_left(id, origin_left, origin_right, left, self.next_of(left), right)
        } else {
            Ok(left)
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
        let left = match self.conflict_left(id, this_left, this_right, left, right) {
            Ok(left) => left,
            Err(error) => return Err(error),
        };
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
        let left_kind = self.clients[ci].blocks.block_at(pos).kind;
        let right_kind = self.clients[ci].blocks.block_at(next_pos).kind;
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
        let start = self.clients[ci].blocks.block_at(pos).clock;
        let kind = self.clients[ci].blocks.block_at(pos).kind;
        let live = match kind {
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
        let block = self.clients[ci].blocks.block_at(pos);
        let slot = match block.kind {
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

    /// The timelines agree with the items they name, and are sorted by
    /// client.
    fn check(store: &YataStoreCore) {
        let mut linked = sequence(store).len();
        for pair in store.clients.windows(2) {
            assert!(pair[0].client < pair[1].client, "timelines by increasing client");
        }
        for entry in &store.clients {
            for pos in 0..entry.blocks.len() {
                let block = entry.blocks.get(pos).unwrap();
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
    fn timelines_are_found_by_binary_search_whatever_the_order_of_arrival() {
        // clients arrive in an order that inserts at the start, in the middle
        // and at the end of the sorted timelines
        let arrivals: [u64; 9] = [50, 10, 90, 30, 70, 20, 80, 0, u64::MAX];
        let mut store = YataStoreCore::new();
        assert_eq!(store.find_client(7), (false, 0));
        for (seen, client) in arrivals.into_iter().enumerate() {
            assert_eq!(store.client_index(client), None);
            assert_eq!(store.get_state(client), 0);
            store.integrate(id(client, 0), 3, None, None).unwrap();
            check(&store);
            assert_eq!(store.clients.len(), seen + 1);
            assert_eq!(store.get_state(client), 3);
        }
        let sorted: Vec<u64> = store.clients.iter().map(|entry| entry.client).collect();
        assert_eq!(sorted, [0, 10, 20, 30, 50, 70, 80, 90, u64::MAX]);
        for (index, client) in sorted.iter().enumerate() {
            assert_eq!(store.find_client(*client), (true, index));
            assert_eq!(store.client_index(*client), Some(index));
        }
        // a client the store does not know: where its timeline would go
        assert_eq!(store.find_client(5), (false, 1));
        assert_eq!(store.find_client(60), (false, 5));
        assert_eq!(store.find_client(u64::MAX - 1), (false, 8));
        assert_eq!(store.client_index(60), None);
        // a second struct of a known client does not add a timeline
        store.integrate(id(30, 3), 1, Some(id(30, 2)), None).unwrap();
        check(&store);
        assert_eq!(store.clients.len(), 9);
        assert_eq!(store.get_state(30), 4);
    }

    #[test]
    fn a_smaller_client_that_arrives_later_goes_before_and_no_timeline_is_added_twice() {
        let clients =
            |store: &YataStoreCore| -> Vec<u64> { store.clients().iter().map(|entry| entry.client).collect() };
        let mut store = YataStoreCore::new();
        store.integrate(id(2, 0), 1, None, None).unwrap();
        store.integrate(id(1, 0), 1, None, None).unwrap();
        check(&store);
        assert_eq!(store.get_state(2), 1);
        assert_eq!(store.get_state(1), 1);
        assert_eq!(clients(&store), [1, 2]);
        // client 2 goes on: its timeline is found, not added again
        store.integrate(id(2, 1), 1, Some(id(2, 0)), None).unwrap();
        check(&store);
        assert_eq!(store.get_state(2), 2);
        assert_eq!(store.get_state(1), 1);
        assert_eq!(clients(&store), [1, 2]);
        assert_eq!(store.items().len(), 3);
        assert!(store.start().is_some());
    }

    #[test]
    fn the_steps_of_the_conflict_scan() {
        let step = ConflictDecision::Step;
        let (a, b, c) = (Some(id(1, 0)), Some(id(1, 5)), Some(id(2, 7)));
        // the same left origin: by client, then by right origin
        assert_eq!(decide_conflict_step(5, a, b, 4, a, c), step(ScanStep::Take));
        assert_eq!(decide_conflict_step(5, None, b, 4, None, b), step(ScanStep::Take));
        assert_eq!(decide_conflict_step(5, a, b, 6, a, b), step(ScanStep::Stop));
        assert_eq!(decide_conflict_step(5, a, None, 5, a, None), step(ScanStep::Stop));
        assert_eq!(decide_conflict_step(5, a, b, 6, a, c), step(ScanStep::Skip));
        assert_eq!(decide_conflict_step(5, a, b, 6, a, None), step(ScanStep::Skip));
        // another left origin: the owner of the one of the candidate decides
        assert_eq!(decide_conflict_step(5, a, b, 4, None, b), step(ScanStep::Stop));
        assert_eq!(
            decide_conflict_step(5, None, b, 4, c, b),
            ConflictDecision::Owner(id(2, 7))
        );
        assert_eq!(
            decide_conflict_step(5, a, b, 9, c, b),
            ConflictDecision::Owner(id(2, 7))
        );
        assert_eq!(decide_owner_step(false, false), ScanStep::Stop);
        assert_eq!(decide_owner_step(false, true), ScanStep::Stop);
        assert_eq!(decide_owner_step(true, false), ScanStep::Take);
        assert_eq!(decide_owner_step(true, true), ScanStep::Skip);
    }

    /// A struct of a replica, as the others receive it.
    #[derive(Clone, Copy, Debug)]
    struct Struct {
        id: IdCore,
        len: u64,
        origin_left: Option<IdCore>,
        origin_right: Option<IdCore>,
    }

    fn xorshift(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }

    /// Integrates the structs a store can take (the next clock of their
    /// client, both origins held), walking `pending` again and again in the
    /// direction given, until none is left.
    fn deliver(store: &mut YataStoreCore, mut pending: Vec<Struct>, backwards: bool) {
        while !pending.is_empty() {
            if backwards {
                pending.reverse();
            }
            let mut later = Vec::new();
            let before = pending.len();
            for item in pending {
                let held = |origin: Option<IdCore>| origin.is_none_or(|origin| store.node_id(origin).is_some());
                if store.get_state(item.id.client) == item.id.clock && held(item.origin_left) && held(item.origin_right)
                {
                    store
                        .integrate(item.id, item.len, item.origin_left, item.origin_right)
                        .unwrap();
                } else {
                    later.push(item);
                }
            }
            assert!(later.len() < before, "a struct that can never be integrated");
            if backwards {
                later.reverse();
            }
            pending = later;
        }
    }

    #[test]
    fn two_thousand_concurrent_inserts_at_one_place_order_by_client() {
        // every client inserts at the start of the empty sequence without
        // seeing the others: each scan walks every item of a smaller client
        // (under Miri a few clients: the same branches, hundreds of times
        // slower)
        let clients: u64 = if cfg!(miri) { 40 } else { 2_000 };
        let ascending: Vec<u64> = (1..=clients).collect();
        let descending: Vec<u64> = ascending.iter().rev().copied().collect();
        // an order that is neither: a walk with a step coprime to the count
        let scattered: Vec<u64> = (0..clients).map(|i| (i * 787) % clients + 1).collect();
        for order in [&ascending, &descending, &scattered] {
            let mut store = YataStoreCore::new();
            for client in order {
                store.integrate(id(*client, 0), 1, None, None).unwrap();
            }
            check(&store);
            assert_eq!(store.clients.len(), clients as usize);
            let ids: Vec<IdCore> = store.visible_ids().into_iter().map(|(id, _)| id).collect();
            let expected: Vec<IdCore> = ascending.iter().map(|client| id(*client, 0)).collect();
            assert_eq!(ids, expected);
        }
    }

    #[test]
    fn a_scan_over_two_thousand_candidates_it_skips_and_takes() {
        // 1 writes "ab". The clients 2, 4, …, 2k insert between the two, each
        // having seen what the ones before it wrote there, at the very left:
        // the right origin of `c` is the item of `c - 2` (the one of "b" for
        // the first). The sequence is a, 2k, …, 4, 2, b. (`k` is a multiple
        // of four; a small one under Miri.)
        let k: u64 = if cfg!(miri) { 40 } else { 2_000 };
        let mut base = YataStoreCore::new();
        base.integrate(id(1, 0), 2, None, None).unwrap();
        for client in (2..=2 * k).step_by(2) {
            let origin_right = if client == 2 { id(1, 1) } else { id(client - 2, 0) };
            base.integrate(id(client, 0), 1, Some(id(1, 0)), Some(origin_right))
                .unwrap();
        }
        check(&base);
        let ids: Vec<IdCore> = base.visible_ids().into_iter().map(|(id, _)| id).collect();
        assert_eq!(ids.len() as u64, k + 2);
        assert_eq!(ids[1], id(2 * k, 0));
        assert_eq!(ids[k as usize], id(2, 0));
        let between = |client: u64, clock: u64| Struct {
            id: id(client, clock),
            len: 1,
            origin_left: Some(id(1, 0)),
            origin_right: Some(id(1, 1)),
        };

        // a client that saw only "ab" and is smaller than all of them: the
        // scan skips every candidate (the same left origin, another right
        // origin, a larger client) and the item stays left of them
        let mut low = base.clone();
        deliver(&mut low, vec![between(0, 0)], false);
        check(&low);
        assert_eq!(low.visible_ids()[1], (id(0, 0), 1));

        // one that is larger than all of them: the scan takes every
        // candidate and the item ends right before "b"
        let mut high = base.clone();
        deliver(&mut high, vec![between(2 * k + 1, 0)], false);
        check(&high);
        assert_eq!(high.visible_ids()[k as usize + 1], (id(2 * k + 1, 0), 1));

        // one in the middle, with two items the scan meets on its way whose
        // left origin is a candidate: one it has seen since the left
        // neighbour last changed (skipped), one it took right before (taken)
        let after = |client: u64| Struct {
            id: id(client, 1),
            len: 1,
            origin_left: Some(id(client, 0)),
            origin_right: Some(id(client - 2, 0)),
        };
        let structs = vec![between(k + 1, 0), after(k + k / 2), after(k / 2)];
        let mut one = base.clone();
        deliver(&mut one, structs.clone(), false);
        let mut other = base.clone();
        deliver(&mut other, structs, true);
        check(&one);
        check(&other);
        assert_eq!(one.visible_ids(), other.visible_ids());
        // it took every candidate of a smaller client: right before "b"
        assert_eq!(one.visible_ids()[k as usize + 3], (id(k + 1, 0), 1));
    }

    #[test]
    fn the_key_of_a_store_changes_no_answer_of_its_scans() {
        // the scans of
        // `a_scan_over_two_thousand_candidates_it_skips_and_takes`, which look
        // origins up among the last candidates and, further back, through the
        // table of the list: under the key of `new`, under `(0, 0)` given by
        // hand and under other keys
        let k: u64 = if cfg!(miri) { 40 } else { 400 };
        let run = |mut store: YataStoreCore| -> YataStoreCore {
            store.integrate(id(1, 0), 2, None, None).unwrap();
            for client in (2..=2 * k).step_by(2) {
                let origin_right = if client == 2 { id(1, 1) } else { id(client - 2, 0) };
                store
                    .integrate(id(client, 0), 1, Some(id(1, 0)), Some(origin_right))
                    .unwrap();
            }
            let between = |client: u64| Struct {
                id: id(client, 0),
                len: 1,
                origin_left: Some(id(1, 0)),
                origin_right: Some(id(1, 1)),
            };
            let after = |client: u64| Struct {
                id: id(client, 1),
                len: 1,
                origin_left: Some(id(client, 0)),
                origin_right: Some(id(client - 2, 0)),
            };
            // origins far back in the walk and right behind it
            let structs = vec![
                between(k + 1),
                after(k + k / 2),
                after(k / 2),
                after(4),
                after(2 * k),
                between(2 * k + 1),
                between(0),
            ];
            deliver(&mut store, structs, false);
            check(&store);
            store
        };
        let plain = run(YataStoreCore::new());
        assert_eq!((plain.k0, plain.k1), (0, 0));
        assert_eq!(plain.visible_ids().len() as u64, k + 2 + 7);
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut keys = vec![(0, 0), (u64::MAX, u64::MAX), (1, 0), (0, 1)];
        for _ in 0..4 {
            keys.push((xorshift(&mut state), xorshift(&mut state)));
        }
        for (k0, k1) in keys {
            let keyed = run(YataStoreCore::with_key(k0, k1));
            assert_eq!((keyed.k0, keyed.k1), (k0, k1));
            assert_eq!(keyed.items, plain.items, "key ({k0}, {k1})");
            assert_eq!(keyed.start, plain.start);
            assert_eq!(keyed.visible_ids(), plain.visible_ids());
            // the key stays with a copy of the store
            let copy = keyed.clone();
            assert_eq!((copy.k0, copy.k1), (k0, k1));
        }
        // a store made with a key is the empty store
        let empty = YataStoreCore::with_key(7, 9);
        assert!(empty.items().is_empty() && empty.start().is_none() && empty.clients().is_empty());
        assert_eq!(YataStoreCore::default().get_state(1), 0);
    }

    #[test]
    fn replicas_that_type_concurrently_converge_whatever_the_order_of_delivery() {
        // `replicas` stores; in every round each writes a few structs at
        // random places of what it holds, then all receive what the others
        // wrote, each in an order of its own
        let replicas = 8usize;
        let rounds = 12;
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut stores: Vec<YataStoreCore> = (0..replicas).map(|_| YataStoreCore::new()).collect();
        for round in 0..rounds {
            let mut written: Vec<Vec<Struct>> = Vec::new();
            for (replica, store) in stores.iter_mut().enumerate() {
                let mut mine = Vec::new();
                for _ in 0..(1 + xorshift(&mut state) % 4) {
                    // between two clocks of the sequence, or at one of its ends
                    let clocks: Vec<IdCore> = sequence(store)
                        .into_iter()
                        .flat_map(|(first, len, _)| (0..len).map(move |offset| id(first.client, first.clock + offset)))
                        .collect();
                    let gap = (xorshift(&mut state) % (clocks.len() as u64 + 1)) as usize;
                    let item = Struct {
                        id: id(replica as u64 + 1, store.get_state(replica as u64 + 1)),
                        len: 1 + xorshift(&mut state) % 3,
                        origin_left: if gap == 0 { None } else { Some(clocks[gap - 1]) },
                        origin_right: clocks.get(gap).copied(),
                    };
                    store
                        .integrate(item.id, item.len, item.origin_left, item.origin_right)
                        .unwrap();
                    mine.push(item);
                }
                written.push(mine);
            }
            for (replica, store) in stores.iter_mut().enumerate() {
                let others: Vec<Struct> = written
                    .iter()
                    .enumerate()
                    .filter(|(from, _)| *from != replica)
                    .flat_map(|(_, structs)| structs.iter().copied())
                    .collect();
                deliver(store, others, (replica + round) % 2 == 1);
                check(store);
            }
            // the same clocks in the same order, whatever the blocks are
            let clocks = |store: &YataStoreCore| -> Vec<IdCore> {
                sequence(store)
                    .into_iter()
                    .flat_map(|(first, len, _)| (0..len).map(move |offset| id(first.client, first.clock + offset)))
                    .collect()
            };
            let first = clocks(&stores[0]);
            for store in &stores[1..] {
                assert_eq!(clocks(store), first, "round {round}");
            }
        }
        assert_eq!(stores[0].clients.len(), replicas);
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
