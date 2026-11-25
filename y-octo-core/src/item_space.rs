//! The item arena of a document: slots that hold an item or nothing, in
//! chunks of `CHUNK_SIZE` that grow on demand.
//!
//! A slot is named by its number. The first chunk is a field of its own, so
//! a small document allocates one vector; the slot `n` sits in the chunk
//! `n / CHUNK_SIZE` at `n % CHUNK_SIZE`. A slot that lost its item
//! (`retire`) is not handed out again before `finish`: what a transaction
//! still points at stays where it is. `finish` lets go of these slots and,
//! when enough of the arena is empty, moves the items to the front, in their
//! order, and answers where each one went.

use alloc::{vec, vec::Vec};

/// The slots of a chunk.
pub const CHUNK_SIZE: usize = 1024;

/// The slots an arena holds at most: a slot, and one more than a slot, fit
/// a `u32`.
pub const MAX_SLOTS: usize = 4_294_967_295;

/// The slots an arena has before `finish` thinks of moving its items.
const COMPACT_SLOTS: usize = 256;

#[cfg_attr(not(aeneas_extract), derive(Debug))]
pub struct ItemSpaceCore<T> {
    /// the chunk of the slots below `CHUNK_SIZE`
    first: Vec<Option<T>>,
    /// the chunks after it: all full but the last one, none empty
    rest: Vec<Vec<Option<T>>>,
    /// how many slots there are
    slots: usize,
    /// the empty slots `alloc` may fill, the next one last
    free: Vec<u32>,
    /// the slots emptied since the last `finish`
    quarantine: Vec<u32>,
}

impl<T> Default for ItemSpaceCore<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// The first `keep` slots of a chunk, in a vector that holds no more.
fn head_of<T>(chunk: &mut [Option<T>], keep: usize) -> Vec<Option<T>> {
    let mut head: Vec<Option<T>> = Vec::with_capacity(keep);
    let mut i = 0usize;
    while i < keep {
        head.push(core::mem::replace(&mut chunk[i], None));
        i += 1;
    }
    head
}

/// The first `keep` slots of a chunk, all of them when it has fewer, in a
/// vector of its own that holds no more: a chunk that grew past what it
/// holds does not keep that memory.
fn cut<T>(chunk: &mut [Option<T>], keep: usize) -> Vec<Option<T>> {
    if keep < chunk.len() {
        head_of(chunk, keep)
    } else {
        head_of(chunk, chunk.len())
    }
}

/// Empties the chunks from the chunk `from` on: their memory goes back at
/// once. The chunks before it are not touched.
fn let_go<T>(chunks: &mut [Vec<Option<T>>], from: usize) {
    let mut i = from;
    while i < chunks.len() {
        let _ = core::mem::replace(&mut chunks[i], Vec::new());
        i += 1;
    }
}

/// The items of two slots, the second one first when `reversed`. `None`
/// when one of them holds no item.
#[inline]
fn pair<'a, T>(x: &'a mut Option<T>, y: &'a mut Option<T>, reversed: bool) -> Option<(&'a mut T, &'a mut T)> {
    match x {
        Some(x) => match y {
            Some(y) => {
                if reversed {
                    Some((y, x))
                } else {
                    Some((x, y))
                }
            }
            None => None,
        },
        None => None,
    }
}

/// The items of the slots `low < high` of one chunk (`pair`).
#[inline]
fn pair_of<T>(cells: &mut [Option<T>], low: usize, high: usize, reversed: bool) -> Option<(&mut T, &mut T)> {
    if low < high && high < cells.len() {
        let (before, after) = cells.split_at_mut(high);
        pair(&mut before[low], &mut after[0], reversed)
    } else {
        None
    }
}

impl<T> ItemSpaceCore<T> {
    /// The arena without a slot. It allocates nothing.
    pub fn new() -> Self {
        Self {
            first: Vec::new(),
            rest: Vec::new(),
            slots: 0,
            free: Vec::new(),
            quarantine: Vec::new(),
        }
    }

    /// How many slots there are, empty ones included.
    #[inline]
    pub fn slots(&self) -> usize {
        self.slots
    }

    /// How many empty slots `alloc` may fill.
    #[inline]
    pub fn free_slots(&self) -> usize {
        self.free.len()
    }

    /// How many slots were emptied since the last `finish`.
    #[inline]
    pub fn quarantined(&self) -> usize {
        self.quarantine.len()
    }

    /// How many chunks there are, the first one included.
    #[inline]
    pub fn chunk_count(&self) -> usize {
        1 + self.rest.len()
    }

    /// How many slots the chunks have memory for: what `finish` gives back
    /// is seen here. A diagnostic for tests (the feature `diagnostics`),
    /// which reads `Vec::capacity`; it is not part of the extracted code.
    #[cfg(feature = "diagnostics")]
    pub fn allocated_capacity(&self) -> usize {
        let mut slots = self.first.capacity();
        for chunk in &self.rest {
            slots += chunk.capacity();
        }
        slots
    }

    /// Whether `additional` more items fit an arena of `limit` items, and
    /// of no more than `MAX_SLOTS`: what `alloc` goes up to. The slots
    /// emptied since the last `finish` count as taken.
    #[inline]
    pub fn check_capacity(&self, additional: usize, limit: usize) -> bool {
        let free = self.free.len();
        if free > self.slots {
            return false;
        }
        let limit = if limit < MAX_SLOTS { limit } else { MAX_SLOTS };
        additional <= limit && self.slots - free <= limit - additional
    }

    /// The slot `slot`, if there is one.
    #[inline]
    fn cell(&self, slot: usize) -> Option<&Option<T>> {
        let chunk = slot / CHUNK_SIZE;
        let offset = slot % CHUNK_SIZE;
        if chunk == 0 {
            if offset < self.first.len() {
                Some(&self.first[offset])
            } else {
                None
            }
        } else if chunk - 1 < self.rest.len() {
            let cells = &self.rest[chunk - 1];
            if offset < cells.len() {
                Some(&cells[offset])
            } else {
                None
            }
        } else {
            None
        }
    }

    /// The slot `slot`, if there is one.
    #[inline]
    fn cell_mut(&mut self, slot: usize) -> Option<&mut Option<T>> {
        let chunk = slot / CHUNK_SIZE;
        let offset = slot % CHUNK_SIZE;
        if chunk == 0 {
            if offset < self.first.len() {
                Some(&mut self.first[offset])
            } else {
                None
            }
        } else if chunk - 1 < self.rest.len() {
            let cells = &mut self.rest[chunk - 1];
            if offset < cells.len() {
                Some(&mut cells[offset])
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Whether `slot` holds an item.
    #[inline]
    fn holds(&self, slot: usize) -> bool {
        match self.cell(slot) {
            Some(cell) => match cell {
                Some(_) => true,
                None => false,
            },
            None => false,
        }
    }

    /// Takes the item out of `slot`, if it holds one.
    #[inline]
    fn take(&mut self, slot: usize) -> Option<T> {
        match self.cell_mut(slot) {
            Some(cell) => match cell {
                Some(_) => core::mem::replace(cell, None),
                None => None,
            },
            None => None,
        }
    }

    /// Puts `item` into `slot`. Hands it back when there is no such slot.
    #[inline]
    fn put(&mut self, slot: usize, item: T) -> Option<T> {
        match self.cell_mut(slot) {
            Some(cell) => {
                *cell = Some(item);
                None
            }
            None => Some(item),
        }
    }

    /// The item of `slot`, if it holds one.
    #[inline]
    pub fn get(&self, slot: u32) -> Option<&T> {
        match self.cell(slot as usize) {
            Some(cell) => match cell {
                Some(item) => Some(item),
                None => None,
            },
            None => None,
        }
    }

    /// The item of `slot`, if it holds one.
    #[inline]
    pub fn get_mut(&mut self, slot: u32) -> Option<&mut T> {
        match self.cell_mut(slot as usize) {
            Some(cell) => match cell {
                Some(item) => Some(item),
                None => None,
            },
            None => None,
        }
    }

    /// The items of two slots, in the order of the arguments. `None` when
    /// the slots are one, or when one of them holds no item.
    pub fn get_two_mut(&mut self, a: u32, b: u32) -> Option<(&mut T, &mut T)> {
        let reversed = a > b;
        let (low, high) = if reversed {
            (b as usize, a as usize)
        } else {
            (a as usize, b as usize)
        };
        let low_chunk = low / CHUNK_SIZE;
        let low_at = low % CHUNK_SIZE;
        let high_chunk = high / CHUNK_SIZE;
        let high_at = high % CHUNK_SIZE;
        if low_chunk == high_chunk {
            // one chunk; `pair_of` refuses the two slots that are one
            if low_chunk == 0 {
                pair_of(&mut self.first, low_at, high_at, reversed)
            } else if low_chunk - 1 < self.rest.len() {
                pair_of(&mut self.rest[low_chunk - 1], low_at, high_at, reversed)
            } else {
                None
            }
        } else if low_chunk == 0 {
            if low_at < self.first.len() && high_chunk - 1 < self.rest.len() {
                let cells = &mut self.rest[high_chunk - 1];
                if high_at < cells.len() {
                    pair(&mut self.first[low_at], &mut cells[high_at], reversed)
                } else {
                    None
                }
            } else {
                None
            }
        } else if low_chunk < high_chunk && high_chunk - 1 < self.rest.len() {
            let (before, after) = self.rest.split_at_mut(high_chunk - 1);
            let low_cells = &mut before[low_chunk - 1];
            let high_cells = &mut after[0];
            if low_at < low_cells.len() && high_at < high_cells.len() {
                pair(&mut low_cells[low_at], &mut high_cells[high_at], reversed)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Puts `item` into an empty slot, or into a new one, and answers the
    /// slot: below `MAX_SLOTS`. An arena that holds `limit` items, the slots
    /// emptied since the last `finish` counted, or one that would need a
    /// slot past `MAX_SLOTS`, hands the item back and is left as it was.
    pub fn alloc(&mut self, item: T, limit: usize) -> Result<u32, T> {
        let free = self.free.len();
        if free > self.slots || self.slots - free >= limit {
            return Err(item);
        }
        if free > 0 {
            let slot = self.free[free - 1];
            match self.put(slot as usize, item) {
                None => {
                    self.free.resize(free - 1, 0);
                    Ok(slot)
                }
                Some(item) => Err(item),
            }
        } else if self.slots >= MAX_SLOTS {
            Err(item)
        } else {
            let slot = self.slots;
            let chunk = slot / CHUNK_SIZE;
            if chunk == 0 {
                self.first.push(Some(item));
            } else if slot % CHUNK_SIZE == 0 {
                let mut cells = Vec::new();
                cells.push(Some(item));
                self.rest.push(cells);
            } else if chunk - 1 < self.rest.len() {
                self.rest[chunk - 1].push(Some(item));
            } else {
                return Err(item);
            }
            self.slots = slot + 1;
            Ok(slot as u32)
        }
    }

    /// Takes the item out of `slot`. The slot stays empty until `finish`.
    /// `None`, and nothing changes, when the slot holds no item.
    pub fn retire(&mut self, slot: u32) -> Option<T> {
        match self.take(slot as usize) {
            Some(item) => {
                self.quarantine.push(slot);
                Some(item)
            }
            None => None,
        }
    }

    /// One step of `compact`: the item of the slot `old`, if there is one,
    /// goes to the slot `live`, the first empty one (the slots between the
    /// two are empty), and the table gets its entry. Answers how many items
    /// are in place after it.
    #[inline]
    fn compact_step(&mut self, moved: &mut [u32], live: usize, old: usize) -> usize {
        if old == live {
            // no slot before this one is empty: its item stays
            if self.holds(old) {
                let next = live + 1;
                moved[old] = next as u32;
                next
            } else {
                live
            }
        } else {
            match self.take(old) {
                Some(item) => {
                    let _ = self.put(live, item);
                    let next = live + 1;
                    moved[old] = next as u32;
                    next
                }
                None => live,
            }
        }
    }

    /// Moves every item to the first empty slot before it, in the order of
    /// the slots. Answers the table of the moves (for every slot one more
    /// than the slot its item went to, and `0` for an empty one) and how
    /// many items there are.
    fn compact(&mut self) -> (Vec<u32>, usize) {
        let slots = self.slots;
        let mut moved = vec![0u32; slots];
        let mut live = 0usize;
        let mut old = 0usize;
        while old < slots {
            live = self.compact_step(&mut moved, live, old);
            old += 1;
        }
        (moved, live)
    }

    /// Lets go of the chunks after the slot `live - 1`, and of the slots
    /// after it in its chunk: the arena keeps `live` slots, and every chunk
    /// it keeps gets a vector that holds no more than the chunk. (A chunk a
    /// compaction ended in grows past its size when it is filled again:
    /// that memory goes back here.) What goes is let go first, then the last
    /// chunk is cut, then the ones before it are copied one at a time: the
    /// arena never holds more than one chunk twice.
    fn shrink(&mut self, live: usize) {
        if live == 0 {
            self.first = Vec::new();
            self.rest = Vec::new();
            return;
        }
        let last = live - 1;
        let chunk = last / CHUNK_SIZE;
        let keep = last % CHUNK_SIZE + 1;
        if chunk == 0 {
            self.rest = Vec::new();
            self.first = cut(&mut self.first, keep);
        } else if chunk - 1 < self.rest.len() {
            let_go(&mut self.rest, chunk);
            let tail = {
                let mut old = core::mem::replace(&mut self.rest[chunk - 1], Vec::new());
                cut(&mut old, keep)
            };
            self.first = cut(&mut self.first, CHUNK_SIZE);
            let mut rest: Vec<Vec<Option<T>>> = Vec::with_capacity(chunk);
            let mut i = 0usize;
            while i < chunk - 1 {
                let mut old = core::mem::replace(&mut self.rest[i], Vec::new());
                rest.push(cut(&mut old, CHUNK_SIZE));
                i += 1;
            }
            rest.push(tail);
            self.rest = rest;
        }
    }

    /// The slots emptied since the last `finish` may be filled again: the
    /// one emptied last first.
    fn release(&mut self) {
        if !self.quarantine.is_empty() {
            self.free.extend_from_slice(&self.quarantine);
            self.quarantine.resize(0, 0);
        }
    }

    /// Whether `finish` moves the items: all slots are empty, or more than
    /// two fifths of at least `COMPACT_SLOTS` slots. Not when no slot is.
    fn sparse(&self) -> bool {
        let free = self.free.len();
        if free == 0 {
            false
        } else if free == self.slots {
            true
        } else if self.slots >= COMPACT_SLOTS {
            (free as u64) * 5 > (self.slots as u64) * 2
        } else {
            false
        }
    }

    /// Ends a transaction: the slots emptied since the last `finish` may be
    /// filled again. When more than two fifths of at least `COMPACT_SLOTS`
    /// slots are empty, or all of them, the items move to the front in their
    /// order and the arena keeps no empty slot; the answer is then the table
    /// of the moves: for every old slot one more than the new slot of its
    /// item, and `0` for a slot that held none (what
    /// `ClientBlocksCore::remap_slots` reads).
    pub fn finish(&mut self) -> Option<Vec<u32>> {
        self.release();
        if !self.sparse() {
            return None;
        }
        let (moved, live) = self.compact();
        self.shrink(live);
        self.free = Vec::new();
        self.quarantine = Vec::new();
        self.slots = live;
        Some(moved)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The slots of the arena, in their order.
    fn cells<T: Clone>(space: &ItemSpaceCore<T>) -> Vec<Option<T>> {
        let mut all = space.first.clone();
        for chunk in &space.rest {
            all.extend(chunk.iter().cloned());
        }
        all
    }

    /// The chunks hold `slots` slots, all full but the last one; the empty
    /// slots are the ones of `free` and `quarantine`, each named once.
    fn check<T: Clone>(space: &ItemSpaceCore<T>) {
        let slots = space.slots;
        assert!(slots <= MAX_SLOTS);
        assert_eq!(space.first.len(), slots.min(CHUNK_SIZE));
        assert_eq!(space.rest.len(), slots.saturating_sub(1) / CHUNK_SIZE);
        for (at, chunk) in space.rest.iter().enumerate() {
            assert_eq!(chunk.len(), (slots - CHUNK_SIZE * (at + 1)).min(CHUNK_SIZE));
        }
        let all = cells(space);
        assert_eq!(all.len(), slots);
        let mut empty: Vec<u32> = space.free.iter().chain(&space.quarantine).copied().collect();
        empty.sort_unstable();
        let expected: Vec<u32> = (0..slots as u32).filter(|&slot| all[slot as usize].is_none()).collect();
        assert_eq!(empty, expected);
        assert_eq!(space.free_slots(), space.free.len());
        assert_eq!(space.quarantined(), space.quarantine.len());
        assert_eq!(space.chunk_count(), 1 + space.rest.len());
        for slot in 0..slots as u32 {
            assert_eq!(space.get(slot).is_some(), all[slot as usize].is_some());
            assert_eq!(space.holds(slot as usize), all[slot as usize].is_some());
        }
        assert!(space.get(slots as u32).is_none());
        assert!(!space.holds(slots));
    }

    fn allocated<T>(space: &ItemSpaceCore<T>) -> usize {
        space.first.capacity() + space.rest.iter().map(Vec::capacity).sum::<usize>()
    }

    #[test]
    fn the_empty_arena_holds_nothing_and_allocates_nothing() {
        let mut space = ItemSpaceCore::<u64>::new();
        check(&space);
        assert_eq!(space.slots(), 0);
        assert_eq!(space.chunk_count(), 1);
        assert_eq!(allocated(&space), 0);
        assert!(space.get(0).is_none());
        assert!(space.get(u32::MAX).is_none());
        assert!(space.get_mut(0).is_none());
        assert!(space.get_two_mut(0, 1).is_none());
        assert_eq!(space.retire(0), None);
        assert_eq!(space.finish(), None);
        check(&space);
        assert!(ItemSpaceCore::<u64>::default().check_capacity(0, 0));
    }

    #[test]
    fn slots_are_handed_out_in_order_and_chunks_grow_on_demand() {
        let mut space = ItemSpaceCore::new();
        for value in 0..(3 * CHUNK_SIZE as u64 + 5) {
            assert_eq!(space.alloc(value, MAX_SLOTS), Ok(value as u32));
            if value % 257 == 0 || value % (CHUNK_SIZE as u64) < 2 {
                check(&space);
            }
        }
        check(&space);
        assert_eq!(space.slots(), 3 * CHUNK_SIZE + 5);
        assert_eq!(space.chunk_count(), 4);
        for value in 0..(3 * CHUNK_SIZE as u32 + 5) {
            assert_eq!(space.get(value), Some(&(value as u64)));
        }
        *space.get_mut(CHUNK_SIZE as u32).unwrap() = 7;
        assert_eq!(space.get(CHUNK_SIZE as u32), Some(&7));
        assert!(space.get_mut(3 * CHUNK_SIZE as u32 + 5).is_none());
        assert!(space.get_mut(u32::MAX).is_none());
    }

    #[test]
    fn check_capacity_counts_the_taken_and_the_quarantined_slots() {
        let mut space = ItemSpaceCore::new();
        for value in 0..10u64 {
            space.alloc(value, MAX_SLOTS).unwrap();
        }
        assert!(space.check_capacity(0, 10));
        assert!(!space.check_capacity(1, 10));
        assert!(space.check_capacity(1, 11));
        assert!(!space.check_capacity(0, 9));
        assert!(!space.check_capacity(usize::MAX, usize::MAX));
        assert!(space.check_capacity(MAX_SLOTS - 10, usize::MAX));
        assert!(!space.check_capacity(MAX_SLOTS - 9, usize::MAX));
        // a retired slot stays taken until `finish`
        assert_eq!(space.retire(3), Some(3));
        assert!(!space.check_capacity(1, 10));
        assert_eq!(space.alloc(99, 10), Err(99));
        check(&space);
        assert_eq!(space.finish(), None);
        assert!(space.check_capacity(1, 10));
        assert!(!space.check_capacity(2, 10));
        assert_eq!(space.alloc(99, 10), Ok(3));
        assert_eq!(space.alloc(100, 10), Err(100));
        check(&space);
        // an arena that holds more than the limit refuses, even with a free
        // slot
        assert_eq!(space.retire(4), Some(4));
        assert_eq!(space.finish(), None);
        assert_eq!(space.alloc(5, 8), Err(5));
        assert_eq!(space.alloc(5, 9), Err(5));
        assert_eq!(space.alloc(5, 10), Ok(4));
        check(&space);
    }

    #[test]
    fn check_capacity_stops_at_the_slots_alloc_goes_up_to() {
        // no arena holds more than `MAX_SLOTS` items, whatever the limit
        // says: `alloc` refuses a slot past them
        let mut space = ItemSpaceCore::new();
        for limit in [MAX_SLOTS, MAX_SLOTS.saturating_add(1), usize::MAX] {
            assert!(space.check_capacity(0, limit));
            assert!(space.check_capacity(MAX_SLOTS, limit));
            assert!(space.check_capacity(MAX_SLOTS - 1, limit));
            // on a target where a `usize` counts no further than the slots
            // there is no such batch
            if let Some(over) = MAX_SLOTS.checked_add(1) {
                assert!(!space.check_capacity(over, limit));
                assert!(!space.check_capacity(over + 1, limit));
            }
            if usize::MAX > MAX_SLOTS {
                assert!(!space.check_capacity(usize::MAX, limit));
                assert!(!space.check_capacity(usize::MAX - 1, limit));
            }
        }
        // a limit below the slots is the one that counts
        assert!(space.check_capacity(MAX_SLOTS - 1, MAX_SLOTS - 1));
        assert!(!space.check_capacity(MAX_SLOTS, MAX_SLOTS - 1));

        // the items the arena holds, and the slots in quarantine, are part of
        // the count
        for value in 0..10u64 {
            space.alloc(value, MAX_SLOTS).unwrap();
        }
        assert_eq!(space.retire(3), Some(3));
        assert_eq!(space.retire(7), Some(7));
        assert_eq!((space.slots(), space.quarantined(), space.free_slots()), (10, 2, 0));
        for limit in [MAX_SLOTS, MAX_SLOTS.saturating_add(1), usize::MAX] {
            assert!(space.check_capacity(MAX_SLOTS - 10, limit));
            assert!(!space.check_capacity(MAX_SLOTS - 9, limit));
            assert!(!space.check_capacity(MAX_SLOTS - 8, limit));
            assert!(!space.check_capacity(MAX_SLOTS, limit));
            assert!(!space.check_capacity(usize::MAX, limit));
        }
        // after `finish` the two slots may be filled again
        assert_eq!(space.finish(), None);
        assert_eq!((space.slots(), space.quarantined(), space.free_slots()), (10, 0, 2));
        for limit in [MAX_SLOTS, MAX_SLOTS.saturating_add(1), usize::MAX] {
            assert!(space.check_capacity(MAX_SLOTS - 8, limit));
            assert!(!space.check_capacity(MAX_SLOTS - 7, limit));
            assert!(!space.check_capacity(usize::MAX, limit));
        }
        check(&space);
    }

    #[test]
    fn retire_empties_a_slot_once_and_finish_frees_it() {
        let mut space = ItemSpaceCore::new();
        for value in 0..5u64 {
            space.alloc(value, MAX_SLOTS).unwrap();
        }
        assert_eq!(space.retire(1), Some(1));
        assert_eq!(space.retire(1), None);
        assert_eq!(space.retire(5), None);
        assert_eq!(space.retire(u32::MAX), None);
        assert!(space.get(1).is_none());
        assert!(space.get_mut(1).is_none());
        check(&space);
        // not reused before `finish`
        assert_eq!(space.alloc(10, MAX_SLOTS), Ok(5));
        assert_eq!(space.retire(4), Some(4));
        assert_eq!(space.quarantined(), 2);
        assert_eq!(space.finish(), None);
        assert_eq!((space.free_slots(), space.quarantined()), (2, 0));
        check(&space);
        // the slot emptied last is filled first
        assert_eq!(space.alloc(11, MAX_SLOTS), Ok(4));
        assert_eq!(space.alloc(12, MAX_SLOTS), Ok(1));
        assert_eq!(space.alloc(13, MAX_SLOTS), Ok(6));
        check(&space);
        assert_eq!(cells(&space), [0, 12, 2, 3, 11, 10, 13].map(Some));
    }

    #[test]
    fn distinct_slots_are_borrowed_in_argument_order() {
        let mut space = ItemSpaceCore::new();
        for value in 0..=(2 * CHUNK_SIZE as u64) {
            space.alloc(value, MAX_SLOTS).unwrap();
        }
        let chunk = CHUNK_SIZE as u32;
        for (a, b) in [
            (0, 3),
            (3, 0),
            (0, chunk - 1),
            (0, chunk),
            (chunk, 0),
            (chunk, chunk + 1),
            (chunk + 1, chunk),
            (2 * chunk - 1, chunk),
            (2 * chunk, chunk),
            (chunk, 2 * chunk),
            (2 * chunk, 0),
        ] {
            let (x, y) = space.get_two_mut(a, b).unwrap();
            assert_eq!((*x, *y), (a as u64, b as u64));
            *x = 11;
            *y = 22;
            assert_eq!(space.get(a), Some(&11));
            assert_eq!(space.get(b), Some(&22));
            *space.get_mut(a).unwrap() = a as u64;
            *space.get_mut(b).unwrap() = b as u64;
            check(&space);
        }
        assert!(space.get_two_mut(0, 0).is_none());
        assert!(space.get_two_mut(chunk, chunk).is_none());
        for (a, b) in [
            (0, 2 * chunk + 1),
            (2 * chunk + 1, 0),
            (chunk, 2 * chunk + 1),
            (2 * chunk, 2 * chunk + 1),
            (2 * chunk, 3 * chunk),
            (5 * chunk, 3 * chunk),
            (0, u32::MAX),
            (u32::MAX, u32::MAX - 1),
        ] {
            assert!(space.get_two_mut(a, b).is_none(), "{a} and {b}");
        }
        assert_eq!(space.retire(4), Some(4));
        assert_eq!(space.retire(chunk + 4), Some(chunk as u64 + 4));
        for (a, b) in [
            (0, 4),
            (4, 0),
            (4, chunk + 4),
            (chunk + 4, chunk + 5),
            (2 * chunk, chunk + 4),
        ] {
            assert!(space.get_two_mut(a, b).is_none(), "{a} and {b}");
        }
        check(&space);
    }

    #[test]
    fn finish_compacts_a_sparse_arena_and_answers_the_moves() {
        for (count, keep_every) in [
            (300usize, 2usize),
            (256, 2),
            (CHUNK_SIZE, 3),
            (CHUNK_SIZE + 1, 3),
            (3 * CHUNK_SIZE, 2),
            (3 * CHUNK_SIZE + 7, 5),
            (10 * CHUNK_SIZE + 1, 10),
            (4 * CHUNK_SIZE, 4 * CHUNK_SIZE),
        ] {
            let mut space = ItemSpaceCore::new();
            for value in 0..count as u64 {
                space.alloc(value, MAX_SLOTS).unwrap();
            }
            for slot in 0..count {
                if slot % keep_every != 0 {
                    assert_eq!(space.retire(slot as u32), Some(slot as u64));
                }
            }
            check(&space);
            let before = allocated(&space);
            let moved = space.finish().expect("more than two fifths are empty");
            check(&space);
            let live = count.div_ceil(keep_every);
            assert_eq!(space.slots(), live);
            assert_eq!((space.free_slots(), space.quarantined()), (0, 0));
            assert_eq!(moved.len(), count);
            for (slot, &to) in moved.iter().enumerate() {
                if slot % keep_every == 0 {
                    let new = (slot / keep_every) as u32;
                    assert_eq!(to, new + 1);
                    assert_eq!(space.get(new), Some(&(slot as u64)));
                } else {
                    assert_eq!(to, 0);
                }
            }
            // no slot is kept for an item that is gone
            assert_eq!(allocated(&space), live, "{count} items, one of {keep_every} kept");
            assert!(allocated(&space) < before);
            assert_eq!(space.rest.capacity(), space.rest.len());
            // the next items go after the kept ones
            assert_eq!(space.alloc(u64::MAX, MAX_SLOTS), Ok(live as u32));
            check(&space);
        }
    }

    /// An arena of `first` slots keeps its first `kept` items, is filled up
    /// to `second` slots and keeps its first `kept_again` items. Answers
    /// how many slots it has memory for after each of the two compactions.
    fn compacted_twice(first: usize, kept: usize, second: usize, kept_again: usize) -> (usize, usize) {
        let mut space = ItemSpaceCore::new();
        for value in 0..first as u64 {
            space.alloc(value, MAX_SLOTS).unwrap();
        }
        for slot in kept..first {
            assert_eq!(space.retire(slot as u32), Some(slot as u64));
        }
        let moved = space.finish().expect("the first compaction");
        assert_eq!(moved.len(), first);
        check(&space);
        let once = allocated(&space);
        for value in kept..second {
            assert_eq!(space.alloc(value as u64, MAX_SLOTS), Ok(value as u32));
        }
        check(&space);
        for slot in kept_again..second {
            assert_eq!(space.retire(slot as u32), Some(slot as u64));
        }
        let moved = space.finish().expect("the second compaction");
        assert_eq!(moved.len(), second);
        check(&space);
        assert_eq!(space.slots(), kept_again);
        for (slot, &to) in moved.iter().enumerate().take(kept_again) {
            assert_eq!(to, slot as u32 + 1);
            assert_eq!(space.get(slot as u32), Some(&(slot as u64)));
        }
        (once, allocated(&space))
    }

    #[test]
    fn the_chunks_a_compaction_keeps_hold_no_more_than_their_items() {
        let chunk = CHUNK_SIZE;
        // the chunk the first compaction ended in is filled again, which
        // makes it grow past what it holds, and the second compaction ends
        // in it: full to its last slot, further in, or where it was
        for (first, kept, second, kept_again) in [
            // the case of the review: 1023 slots kept, then all 1024
            (2 * chunk, chunk - 1, 2 * chunk, chunk),
            (2 * chunk, 600, 2 * chunk, 1000),
            (2 * chunk, 600, 2 * chunk, 600),
            (2 * chunk, chunk, 2 * chunk, chunk),
            (2 * chunk, 1, 2 * chunk, chunk),
            // the same in a chunk after the first one
            (4 * chunk, 2 * chunk - 1, 4 * chunk, 2 * chunk),
            (4 * chunk, chunk + 300, 4 * chunk, chunk + 900),
            (4 * chunk, chunk + 1, 4 * chunk, 2 * chunk),
            (5 * chunk, 3 * chunk - 1, 6 * chunk, 3 * chunk),
            // and when the second compaction ends before that chunk
            (4 * chunk, 2 * chunk + 5, 5 * chunk, chunk),
            (4 * chunk, 2 * chunk + 5, 5 * chunk, chunk + 7),
            // or after it: the chunk that grew is then one of the full
            // chunks before the last one, which give their memory back too
            (2 * chunk, chunk - 1, 4 * chunk, 2 * chunk),
            (2 * chunk, 600, 4 * chunk, 2 * chunk + 1),
            (4 * chunk, chunk + 300, 6 * chunk, 3 * chunk + 17),
            (4 * chunk, 2 * chunk - 1, 6 * chunk, 3 * chunk),
            (3 * chunk, 1, 5 * chunk, 3 * chunk - 1),
        ] {
            // (Miri takes the cases of up to four chunks)
            if cfg!(miri) && second > 4 * chunk {
                continue;
            }
            assert_eq!(
                compacted_twice(first, kept, second, kept_again),
                (kept, kept_again),
                "{first} slots, {kept} kept, {second} slots, {kept_again} kept"
            );
        }
    }

    #[test]
    fn finish_keeps_a_dense_or_small_arena_in_place() {
        // fewer than `COMPACT_SLOTS` slots: no move, however empty
        let mut space = ItemSpaceCore::new();
        for value in 0..255u64 {
            space.alloc(value, MAX_SLOTS).unwrap();
        }
        for slot in 1..255u32 {
            space.retire(slot);
        }
        assert_eq!(space.finish(), None);
        assert_eq!(space.slots(), 255);
        assert_eq!(space.free_slots(), 254);
        check(&space);
        // all of them empty: the arena starts over
        space.retire(0);
        let moved = space.finish().expect("an empty arena is let go");
        assert_eq!(moved, [0u32; 255]);
        assert_eq!(space.slots(), 0);
        assert_eq!(allocated(&space), 0);
        check(&space);

        // exactly two fifths empty: not enough
        let mut space = ItemSpaceCore::new();
        for value in 0..1000u64 {
            space.alloc(value, MAX_SLOTS).unwrap();
        }
        for slot in 0..400u32 {
            space.retire(slot);
        }
        assert_eq!(space.finish(), None);
        check(&space);
        // one more is
        space.retire(400);
        let moved = space.finish().unwrap();
        assert_eq!(space.slots(), 599);
        assert_eq!(moved[400], 0);
        assert_eq!(moved[401], 1);
        assert_eq!(moved[999], 599);
        check(&space);
        assert_eq!(space.get(0), Some(&401));
        assert_eq!(space.get(598), Some(&999));

        // the items of a prefix that is in place keep their slots
        let mut space = ItemSpaceCore::new();
        for value in 0..(2 * CHUNK_SIZE as u64) {
            space.alloc(value, MAX_SLOTS).unwrap();
        }
        for slot in CHUNK_SIZE as u32..2 * CHUNK_SIZE as u32 - 1 {
            space.retire(slot);
        }
        let moved = space.finish().unwrap();
        for (slot, &to) in moved.iter().enumerate().take(CHUNK_SIZE) {
            assert_eq!(to, slot as u32 + 1);
        }
        assert_eq!(space.slots(), CHUNK_SIZE + 1);
        assert_eq!(moved[2 * CHUNK_SIZE - 1], CHUNK_SIZE as u32 + 1);
        assert_eq!(space.get(CHUNK_SIZE as u32), Some(&(2 * CHUNK_SIZE as u64 - 1)));
        assert_eq!(allocated(&space), CHUNK_SIZE + 1);
        check(&space);
    }

    #[test]
    fn the_table_of_finish_is_the_one_remap_slots_reads() {
        use crate::client_blocks::{BlockKindCore, BlockRefCore, ClientBlocksCore};
        let mut space = ItemSpaceCore::new();
        let mut timeline = ClientBlocksCore::new();
        for clock in 0..600u64 {
            let slot = space.alloc(clock, MAX_SLOTS).unwrap();
            timeline
                .append(
                    BlockRefCore {
                        clock,
                        kind: BlockKindCore::Item(slot),
                    },
                    1,
                )
                .unwrap();
        }
        // the blocks of the retired items are collected: no block names an
        // empty slot
        for index in 0..600usize {
            if index % 3 != 0 {
                timeline.mark_deleted(index).unwrap();
                let slot = timeline.mark_gc(index).unwrap();
                assert_eq!(space.retire(slot), Some(index as u64));
            }
        }
        let moved = space.finish().unwrap();
        assert_eq!(timeline.remap_slots(&moved), Ok(()));
        for index in 0..600usize {
            match timeline.get(index).unwrap().kind {
                BlockKindCore::Item(slot) => {
                    assert_eq!(index % 3, 0);
                    assert_eq!(space.get(slot), Some(&(index as u64)));
                }
                kind => {
                    assert_ne!(index % 3, 0);
                    assert!(matches!(kind, BlockKindCore::Gc));
                }
            }
        }
    }

    #[test]
    fn a_random_walk_agrees_with_a_plain_list_of_slots() {
        // the arena next to the list of its slots, with the limit and the
        // quarantine done the plain way
        let mut space = ItemSpaceCore::new();
        let mut model: Vec<Option<u64>> = Vec::new();
        let mut free: Vec<u32> = Vec::new();
        let mut quarantine: Vec<u32> = Vec::new();
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let rounds = if cfg!(miri) { 2_000 } else { 60_000 };
        let limit = 3 * CHUNK_SIZE + 100;
        for round in 0..rounds {
            let draw = next();
            // phases of growth and of mass retirement, so both kinds of
            // `finish` happen
            let shrinking = (round / 4_000) % 2 == 1;
            match draw % if shrinking { 7 } else { 4 } {
                0 | 1 => {
                    let value = next();
                    let occupied = model.len() - free.len();
                    let answer = space.alloc(value, limit);
                    if occupied >= limit {
                        assert_eq!(answer, Err(value));
                    } else if let Some(slot) = free.pop() {
                        model[slot as usize] = Some(value);
                        assert_eq!(answer, Ok(slot));
                    } else {
                        model.push(Some(value));
                        assert_eq!(answer, Ok(model.len() as u32 - 1));
                    }
                }
                2 | 4 | 5 | 6 => {
                    if !model.is_empty() {
                        let slot = (next() % (model.len() as u64 + 2)) as u32;
                        let held = model.get_mut(slot as usize).and_then(Option::take);
                        if held.is_some() {
                            quarantine.push(slot);
                        }
                        assert_eq!(space.retire(slot), held);
                    }
                }
                _ => {
                    if draw % 16 < 3 {
                        free.append(&mut quarantine);
                        let compact = model.len() >= 256 && free.len() * 5 > model.len() * 2;
                        let answer = space.finish();
                        if !free.is_empty() && (compact || free.len() == model.len()) {
                            let moved = answer.expect("a sparse arena is compacted");
                            let mut live = 0u32;
                            let table: Vec<u32> = model
                                .iter()
                                .map(|cell| {
                                    cell.map_or(0, |_| {
                                        live += 1;
                                        live
                                    })
                                })
                                .collect();
                            assert_eq!(moved, table);
                            model.retain(Option::is_some);
                            free.clear();
                            assert_eq!(allocated(&space), model.len());
                        } else {
                            assert_eq!(answer, None);
                        }
                    } else if model.len() >= 2 {
                        let a = (next() % model.len() as u64) as u32;
                        let b = (next() % model.len() as u64) as u32;
                        let expected = (a != b).then(|| model[a as usize].zip(model[b as usize])).flatten();
                        let answer = space.get_two_mut(a, b).map(|(x, y)| (*x, *y));
                        assert_eq!(answer, expected);
                        if let Some((x, y)) = space.get_two_mut(a, b) {
                            core::mem::swap(x, y);
                            model.swap(a as usize, b as usize);
                        }
                    }
                }
            }
            assert_eq!(space.slots(), model.len());
            assert_eq!(space.free, free);
            assert_eq!(space.quarantine, quarantine);
            assert_eq!(space.check_capacity(1, limit), model.len() - free.len() < limit);
            if round % 97 == 0 {
                assert_eq!(cells(&space), model);
                check(&space);
            }
        }
        assert_eq!(cells(&space), model);
        check(&space);
    }
}
