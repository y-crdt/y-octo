//! The ids one conflict scan has walked, in the order it met them, and
//! where an id is in that order.
//!
//! The scan asks two things about the struct an origin points into: whether
//! it walked that struct, and whether it did so after the last candidate it
//! took. Both are read off the place of the struct in the walk, so one list
//! answers them and nothing is ever taken out of it.
//!
//! Most answers are near the end of the list (an item mostly follows the one
//! it was typed after), or are the answer before (the items that follow one
//! item name it one after the other): `recent` looks at the place it
//! answered last, then through the last `RECENT` ids, and says whether there
//! are more. Only `position` needs to find an id among all of them. It keeps a
//! table for that, open addressing with linear probing over a power of two of
//! slots, at most half of them taken; a slot holds one more than a place in the
//! list, four bytes, and the ids stay in the list. The table is made when
//! `position` is first asked, and caught up with the list whenever it is asked
//! again: a scan that never asks pays for the list only.
//!
//! The hash is the keyed one of `id_set` (`key`): a peer that does not know
//! the key cannot choose ids that all probe the same slots.

use alloc::{vec, vec::Vec};

use crate::{
    id_set::home,
    yata_store::{IdCore, id_eq},
};

/// How many ids `recent` looks through: the last ones.
pub const RECENT: usize = 16;

/// The ids a list holds at most, `2 ^ 30`: one more than a place fits a
/// `u32`, and twice as many slots are counted by a `usize`.
pub const MAX_IDS: usize = 1_073_741_824;

/// The slots of the smallest table.
const FIRST_SLOTS: usize = 64;

#[cfg_attr(not(aeneas_extract), derive(Clone, Debug))]
pub struct IdOrderCore {
    /// the ids, in the order they came
    ids: Vec<IdCore>,
    /// no slots, or a power of two of them: `0` for a free slot, else one
    /// more than the place of an id in `ids`
    table: Vec<u32>,
    /// how many ids are in the table: the first ones
    indexed: usize,
    /// the place answered last, if any place was: it is looked at first
    last: usize,
    /// the key of the hash
    k0: u64,
    k1: u64,
}

/// What looking through the last ids of a list ends with: the place of the
/// id, a list that does not hold it, or one that has more ids than were
/// looked through.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum Recent {
    At(usize),
    Absent,
    Far,
}

/// How many slots a table has for `count` ids: the smallest power of two,
/// from `FIRST_SLOTS` on, that they fill no more than half of.
fn slots_for(count: usize) -> usize {
    let mut slots = FIRST_SLOTS;
    while slots / 2 < count && slots / 2 < MAX_IDS {
        slots *= 2;
    }
    slots
}

/// Puts the place `at` of `id` into the first free slot from the home slot
/// of the id on. Answers whether there was one.
fn put(table: &mut [u32], k0: u64, k1: u64, id: IdCore, at: usize) -> bool {
    let slots = table.len();
    // a table without slots is not walked at all
    let mut idx = if slots == 0 { 0 } else { home(k0, k1, id, slots) };
    let mut step = 0usize;
    while step < slots {
        if table[idx] == 0 {
            table[idx] = (at + 1) as u32;
            return true;
        }
        idx += 1;
        if idx == slots {
            idx = 0;
        }
        step += 1;
    }
    false
}

/// Walks the table from the home slot of `id`, at most once around, to the
/// place of the id in `ids`: `None` at a free slot.
fn seek(table: &[u32], ids: &[IdCore], k0: u64, k1: u64, id: IdCore) -> Option<usize> {
    let slots = table.len();
    let mut idx = if slots == 0 { 0 } else { home(k0, k1, id, slots) };
    let mut step = 0usize;
    while step < slots {
        let entry = table[idx];
        if entry == 0 {
            return None;
        }
        let at = (entry - 1) as usize;
        if at < ids.len() && id_eq(ids[at], id) {
            return Some(at);
        }
        idx += 1;
        if idx == slots {
            idx = 0;
        }
        step += 1;
    }
    None
}

impl Default for IdOrderCore {
    fn default() -> Self {
        Self::new()
    }
}

impl IdOrderCore {
    /// The empty list. It allocates nothing, and its hash has the key
    /// `(0, 0)` until `key` gives it another one.
    pub fn new() -> Self {
        Self::with_key(0, 0)
    }

    /// The empty list whose hash has the key `(k0, k1)`: what `new` and
    /// then `key` make. It allocates nothing.
    pub fn with_key(k0: u64, k1: u64) -> Self {
        Self {
            ids: Vec::new(),
            table: Vec::new(),
            indexed: 0,
            last: 0,
            k0,
            k1,
        }
    }

    /// How many ids the list holds.
    #[inline]
    pub fn len(&self) -> usize {
        self.ids.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.ids.len() == 0
    }

    /// Puts `id` at the end of the list. Answers `false`, and leaves the
    /// list as it was, only when it holds `MAX_IDS` ids.
    #[inline]
    pub fn push(&mut self, id: IdCore) -> bool {
        if self.ids.len() >= MAX_IDS {
            return false;
        }
        self.ids.push(id);
        true
    }

    /// Looks for `id` at the place answered last, then among the last
    /// `RECENT` ids, the last one first.
    #[inline]
    pub fn recent(&mut self, id: IdCore) -> Recent {
        let found = self.look(id);
        match found {
            Recent::At(at) => {
                self.last = at;
            }
            Recent::Absent => {}
            Recent::Far => {}
        }
        found
    }

    /// What `recent` answers.
    #[inline]
    fn look(&self, id: IdCore) -> Recent {
        let last = self.last;
        if last < self.ids.len() && id_eq(self.ids[last], id) {
            return Recent::At(last);
        }
        self.window(id)
    }

    /// Looks for `id` among the last `RECENT` ids, the last one first.
    #[inline]
    fn window(&self, id: IdCore) -> Recent {
        let mut at = self.ids.len();
        let mut looked = 0usize;
        while at > 0 && looked < RECENT {
            at -= 1;
            if id_eq(self.ids[at], id) {
                return Recent::At(at);
            }
            looked += 1;
        }
        if at == 0 { Recent::Absent } else { Recent::Far }
    }

    /// Whether the table holds an id: `key` no longer changes the key then.
    #[inline]
    pub fn is_indexed(&self) -> bool {
        self.indexed > 0
    }

    /// Gives the hash the key `(k0, k1)`: two words the peers that choose
    /// the ids cannot know. Nothing happens once the table holds an id.
    pub fn key(&mut self, k0: u64, k1: u64) {
        if self.indexed == 0 {
            self.k0 = k0;
            self.k1 = k1;
        }
    }

    /// Lets go of a table the ids of the list would fill more than half of,
    /// for a free one of their size.
    fn fit(&mut self) {
        let count = self.ids.len();
        if self.table.len() / 2 < count {
            self.table = vec![0u32; slots_for(count)];
            self.indexed = 0;
        }
    }

    /// Makes the table hold every id of the list: all of them in a table
    /// of their size when this one would be more than half full, else the
    /// ids that came since the last time.
    fn index(&mut self) {
        self.fit();
        let count = self.ids.len();
        let mut at = self.indexed;
        while at < count {
            let _ = put(&mut self.table, self.k0, self.k1, self.ids[at], at);
            at += 1;
        }
        self.indexed = count;
    }

    /// A place of `id` in the list, `None` when the list does not hold it.
    pub fn position(&mut self, id: IdCore) -> Option<usize> {
        self.index();
        let found = seek(&self.table, &self.ids, self.k0, self.k1, id);
        match found {
            Some(at) => {
                self.last = at;
            }
            None => {}
        }
        found
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(client: u64, clock: u64) -> IdCore {
        IdCore { client, clock }
    }

    /// The table names the first `indexed` places once each, every one of
    /// them reached from the home slot of its id without crossing a free
    /// slot, and is at most half full.
    fn check(order: &IdOrderCore) {
        let slots = order.table.len();
        assert!(order.indexed <= order.ids.len());
        assert!(order.ids.len() <= MAX_IDS);
        assert!(slots == 0 || slots.is_power_of_two());
        assert!(order.indexed * 2 <= slots);
        let mut places: Vec<usize> = order
            .table
            .iter()
            .filter(|&&entry| entry != 0)
            .map(|&entry| entry as usize - 1)
            .collect();
        places.sort_unstable();
        assert_eq!(places, (0..order.indexed).collect::<Vec<_>>());
        for (slot, &entry) in order.table.iter().enumerate() {
            if entry != 0 {
                let held = order.ids[entry as usize - 1];
                let mut idx = home(order.k0, order.k1, held, slots);
                while idx != slot {
                    assert_ne!(order.table[idx], 0, "a free slot before {held:?}");
                    idx = (idx + 1) % slots;
                }
            }
        }
    }

    #[test]
    fn the_empty_list_holds_nothing_and_allocates_nothing() {
        let mut order = IdOrderCore::default();
        assert!(order.is_empty());
        assert_eq!(order.len(), 0);
        assert_eq!(order.recent(id(0, 0)), Recent::Absent);
        assert_eq!(order.position(id(0, 0)), None);
        assert_eq!(order.last, 0);
        assert!(!order.is_indexed());
        assert_eq!(order.ids.capacity(), 0);
        assert_eq!(order.table.capacity(), 0);
        check(&order);
    }

    #[test]
    fn recent_looks_through_the_last_ids_only() {
        let mut order = IdOrderCore::new();
        for clock in 0..RECENT as u64 {
            assert!(order.push(id(1, clock)));
            // a list of no more than `RECENT` ids is looked through whole
            for known in 0..=clock {
                assert_eq!(order.recent(id(1, known)), Recent::At(known as usize));
            }
            assert_eq!(order.recent(id(2, clock)), Recent::Absent);
            assert_eq!(order.recent(id(1, clock + 1)), Recent::Absent);
        }
        assert!(order.push(id(1, RECENT as u64)));
        assert_eq!(order.len(), RECENT + 1);
        // the place answered last is `RECENT - 1`
        assert_eq!(order.last, RECENT - 1);
        assert_eq!(order.recent(id(1, 0)), Recent::Far);
        assert_eq!(order.recent(id(9, 9)), Recent::Far);
        assert_eq!(order.recent(id(1, 1)), Recent::At(1));
        assert_eq!(order.recent(id(1, RECENT as u64)), Recent::At(RECENT));
        // nothing of this made a table
        assert!(!order.is_indexed());
        assert_eq!(order.table.capacity(), 0);
        // an id that is there twice: the later place is the recent one, the
        // first one is its position
        assert!(order.push(id(1, 3)));
        assert_eq!(order.recent(id(1, 3)), Recent::At(RECENT + 1));
        assert_eq!(order.position(id(1, 3)), Some(3));
        check(&order);
    }

    #[test]
    fn the_place_answered_last_is_looked_at_first() {
        // the ids that follow one id name it one after the other: once it
        // is found, by hand or through the table, it is found again at once,
        // however far back it is
        let mut order = IdOrderCore::new();
        for clock in 0..200u64 {
            assert!(order.push(id(1, clock)));
        }
        assert_eq!(order.last, 0);
        // the place `0` is looked at before any place was answered: it
        // holds the id or it does not
        assert_eq!(order.recent(id(1, 0)), Recent::At(0));
        assert_eq!(order.recent(id(1, 5)), Recent::Far);
        assert_eq!(order.last, 0);
        assert_eq!(order.position(id(1, 5)), Some(5));
        assert_eq!(order.last, 5);
        let slots = order.table.len();
        for clock in 200..400u64 {
            assert!(order.push(id(1, clock)));
            assert_eq!(order.recent(id(1, 5)), Recent::At(5));
        }
        // the table was not asked, and not brought up to the list
        assert_eq!((order.indexed, order.table.len()), (200, slots));
        // another id takes the place
        assert_eq!(order.recent(id(1, 399)), Recent::At(399));
        assert_eq!(order.last, 399);
        assert_eq!(order.recent(id(1, 5)), Recent::Far);
        assert_eq!(order.recent(id(7, 7)), Recent::Far);
        assert_eq!(order.position(id(7, 7)), None);
        assert_eq!(order.last, 399);
        check(&order);
        // a place past the end of a list is not looked at
        let mut empty = IdOrderCore::new();
        assert_eq!(empty.recent(id(0, 0)), Recent::Absent);
    }

    #[test]
    fn position_finds_every_id_and_the_table_follows_the_list() {
        let mut order = IdOrderCore::new();
        order.key(0x243F_6A88_85A3_08D3, 0x1319_8A2E_0370_7344);
        let mut slots = Vec::new();
        let count: u64 = if cfg!(miri) { 150 } else { 3_000 };
        for clock in 0..count {
            assert!(order.push(id(clock % 7, clock)));
            // asked now and then: the table catches up with what came since
            if clock % 5 == 0 || clock < 40 {
                assert_eq!(order.position(id(clock % 7, clock)), Some(clock as usize));
                assert_eq!(order.position(id(clock % 7 + 7, clock)), None);
                assert_eq!(order.indexed, clock as usize + 1);
                // (the whole table is looked through: not every time under
                // Miri)
                if !cfg!(miri) || clock % 25 == 0 {
                    check(&order);
                }
                slots.push((clock as usize + 1, order.table.len()));
            }
        }
        for clock in 0..count {
            assert_eq!(order.position(id(clock % 7, clock)), Some(clock as usize));
        }
        assert_eq!(order.position(id(0, count)), None);
        check(&order);
        // the smallest power of two the ids fill no more than half of
        for (count, slots) in slots {
            assert_eq!(slots, (2 * count).next_power_of_two().max(FIRST_SLOTS), "{count} ids");
        }
        assert_eq!(order.table.len(), if cfg!(miri) { 512 } else { 8192 });
    }

    #[test]
    fn the_first_table_is_made_for_all_the_ids_at_once() {
        let mut order = IdOrderCore::new();
        for clock in 0..1_000u64 {
            assert!(order.push(id(4, clock)));
        }
        assert_eq!(order.table.capacity(), 0);
        assert_eq!(order.position(id(4, 0)), Some(0));
        assert_eq!(order.table.len(), 2048);
        check(&order);
        // up to half of it: no other table
        let pointer = order.table.as_ptr();
        for clock in 1_000..1_024u64 {
            assert!(order.push(id(4, clock)));
        }
        assert_eq!(order.position(id(4, 1_023)), Some(1_023));
        assert_eq!(order.table.as_ptr(), pointer);
        assert!(order.push(id(4, 1_024)));
        assert_eq!(order.position(id(4, 1_024)), Some(1_024));
        assert_eq!(order.table.len(), 4096);
        check(&order);
    }

    #[test]
    fn the_key_is_taken_until_the_table_holds_an_id() {
        let mut order = IdOrderCore::new();
        assert_eq!((order.k0, order.k1), (0, 0));
        order.key(1, 2);
        assert_eq!((order.k0, order.k1), (1, 2));
        // an empty list makes no table: the key may still change
        assert_eq!(order.position(id(1, 1)), None);
        assert!(!order.is_indexed());
        order.key(3, 4);
        assert_eq!((order.k0, order.k1), (3, 4));
        assert!(order.push(id(1, 1)));
        order.key(5, 6);
        assert_eq!((order.k0, order.k1), (5, 6));
        assert_eq!(order.position(id(1, 1)), Some(0));
        assert!(order.is_indexed());
        order.key(7, 8);
        assert_eq!((order.k0, order.k1), (5, 6));
        for clock in 2..200u64 {
            assert!(order.push(id(1, clock)));
        }
        assert_eq!(order.position(id(1, 199)), Some(198));
        order.key(9, 9);
        assert_eq!((order.k0, order.k1), (5, 6));
        check(&order);
    }

    #[test]
    fn a_list_made_with_a_key_is_the_one_that_was_given_it() {
        let made = IdOrderCore::with_key(3, 4);
        assert_eq!((made.k0, made.k1), (3, 4));
        assert!(made.is_empty() && !made.is_indexed());
        assert_eq!(made.ids.capacity(), 0);
        assert_eq!(made.table.capacity(), 0);
        let plain = IdOrderCore::new();
        assert_eq!((plain.k0, plain.k1), (0, 0));
        // the same places and the same table as a list that was given the
        // key afterwards
        let mut made = IdOrderCore::with_key(0x243F_6A88_85A3_08D3, 0x1319_8A2E_0370_7344);
        let mut given = IdOrderCore::new();
        given.key(0x243F_6A88_85A3_08D3, 0x1319_8A2E_0370_7344);
        for clock in 0..300u64 {
            assert!(made.push(id(clock % 5, clock)));
            assert!(given.push(id(clock % 5, clock)));
        }
        for clock in (0..300u64).rev() {
            assert_eq!(made.position(id(clock % 5, clock)), Some(clock as usize));
            assert_eq!(given.position(id(clock % 5, clock)), Some(clock as usize));
        }
        assert_eq!(made.table, given.table);
        check(&made);
    }

    #[test]
    fn a_random_list_agrees_with_a_search_by_hand() {
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let rounds = if cfg!(miri) { 4 } else { 60 };
        for round in 0..rounds {
            let mut order = IdOrderCore::new();
            order.key(next(), next());
            let mut list: Vec<IdCore> = Vec::new();
            // the place answered last
            let mut last = 0usize;
            let steps = if cfg!(miri) { 300 } else { 4_000 };
            for _ in 0..steps {
                let draw = next();
                // a small id space: some ids come twice
                let held = id(draw % 5, (draw >> 8) % (40 + 60 * round));
                match draw >> 60 {
                    0..=9 => {
                        assert!(order.push(held));
                        list.push(held);
                    }
                    10..=12 => {
                        let from = list.len().saturating_sub(RECENT);
                        let expected = if list.get(last) == Some(&held) {
                            Recent::At(last)
                        } else {
                            match list[from..].iter().rposition(|other| *other == held) {
                                Some(at) => Recent::At(from + at),
                                None if from == 0 => Recent::Absent,
                                None => Recent::Far,
                            }
                        };
                        assert_eq!(order.recent(held), expected);
                        if let Recent::At(at) = expected {
                            last = at;
                        }
                    }
                    _ => {
                        let expected = list.iter().position(|other| *other == held);
                        assert_eq!(order.position(held), expected);
                        assert_eq!(order.indexed, list.len());
                        if let Some(at) = expected {
                            last = at;
                        }
                    }
                }
                assert_eq!(order.len(), list.len());
                assert_eq!(order.last, last);
            }
            assert_eq!(order.ids, list);
            check(&order);
        }
    }
}
