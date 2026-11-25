//! A set of ids for the conflict scan of `yata_store`: open addressing with
//! linear probing over a table whose size is a power of two.
//!
//! An id sits at the first free slot from its home slot on (`home`, the hash
//! of the id masked to the table), so a lookup walks from the home slot until
//! it meets the id or a free slot. A single id is never removed: `clear`
//! empties the set. The table is at most half full; it doubles before an
//! insertion that would fill it further.
//!
//! The hash is keyed (`with_key`) by two words, one mixed with the client
//! and one with the clock before the two halves meet (`hash_id`). Which ids
//! share a home slot then depends on both words: a peer that knows neither,
//! or only one of them, has no cheap way to choose ids that all probe the
//! same slots. A peer that knows both can: the set made by `new` has the key
//! `(0, 0)`, which everybody knows, and is for ids no peer chooses. That the
//! hash spreads ids, for any key, is measured (the tests below and
//! `core_parity`), not proved.
//!
//! `insert` accepts while the set holds fewer than `2 ^ 30` ids
//! (`IdSet.insert_spec`): a bound that is enough for the proofs, not one a
//! scan is expected to come near. `y-octo` does not use this set: its scan
//! keeps its candidates in an `id_order::IdOrderCore`, which shares the hash.

use alloc::vec::Vec;

use crate::yata_store::{IdCore, id_eq};

/// The slots of the first table of a set.
pub const FIRST_SLOTS: usize = 16;

#[cfg_attr(not(aeneas_extract), derive(Clone, Debug))]
pub struct IdSetCore {
    /// no slots, or a power of two of them
    buckets: Vec<Option<IdCore>>,
    /// how many slots hold an id
    len: usize,
    /// the key of the hash
    k0: u64,
    k1: u64,
}

/// What probing a table for an id ends with: the id, the free slot it would
/// go to, or a table without the id and without a free slot.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
enum Probe {
    Found,
    Free(usize),
    Full,
}

/// The multipliers of the hash: three odd words (the first three secrets of
/// wyhash).
const CLIENT_MULTIPLE: u64 = 0xa076_1d64_78bd_642f;
const CLOCK_MULTIPLE: u64 = 0xe703_7ed1_a0b4_28db;
const LAST_MULTIPLE: u64 = 0x8ebc_6af0_9c88_c6e3;

/// The two halves of the product of two words, one over the other.
#[inline]
fn fold(a: u64, b: u64) -> u64 {
    let product = (a as u128).wrapping_mul(b as u128);
    (product as u64) ^ ((product >> 64) as u64)
}

/// Mixes the two halves of an id and the key into one word: the client
/// under `k0` and the clock under `k1`, each through a folded product of its
/// own, and the two together through a third one. Neither half of the key
/// is put in after the other half of the id is known to the hash: whoever
/// knows one word of the key still cannot tell which ids agree in the low
/// bits of the answer. The two first products do not wait for each other.
#[inline]
pub(crate) fn hash_id(k0: u64, k1: u64, id: IdCore) -> u64 {
    let client = fold(id.client ^ k0, CLIENT_MULTIPLE);
    let clock = fold(id.clock ^ k1, CLOCK_MULTIPLE);
    fold(client ^ clock, LAST_MULTIPLE)
}

/// The slot the probing of `id` starts at in a table of `slots` slots
/// (`slots > 0`; a power of two for the mask to spread the ids).
#[inline]
pub(crate) fn home(k0: u64, k1: u64, id: IdCore, slots: usize) -> usize {
    (hash_id(k0, k1, id) as usize) & (slots - 1)
}

/// A table of `slots` free slots.
fn free_table(slots: usize) -> Vec<Option<IdCore>> {
    // one allocation: the table does not grow while it is filled
    let mut table: Vec<Option<IdCore>> = Vec::with_capacity(slots);
    let mut i = 0usize;
    while i < slots {
        table.push(None);
        i += 1;
    }
    table
}

/// A free slot.
#[inline]
fn free_slot() -> Option<IdCore> {
    None
}

/// Frees every slot of a table.
fn free_all(table: &mut [Option<IdCore>]) {
    let mut i = 0usize;
    while i < table.len() {
        table[i] = free_slot();
        i += 1;
    }
}

/// Walks the table from the home slot of `id`, at most once around.
fn probe(table: &[Option<IdCore>], k0: u64, k1: u64, id: IdCore) -> Probe {
    let slots = table.len();
    // a table without slots is not walked at all
    let mut idx = if slots == 0 { 0 } else { home(k0, k1, id, slots) };
    let mut step = 0usize;
    while step < slots {
        let slot = table[idx];
        match slot {
            Some(found) => {
                if id_eq(found, id) {
                    return Probe::Found;
                }
            }
            None => return Probe::Free(idx),
        }
        idx += 1;
        if idx == slots {
            idx = 0;
        }
        step += 1;
    }
    Probe::Full
}

/// Puts `id` into a table with a free slot. Returns whether it was not
/// there yet.
fn put(table: &mut [Option<IdCore>], k0: u64, k1: u64, id: IdCore) -> bool {
    match probe(table, k0, k1, id) {
        Probe::Free(idx) => {
            table[idx] = Some(id);
            true
        }
        Probe::Found => false,
        Probe::Full => false,
    }
}

/// The ids of `old` in a table of `slots` slots, and how many they are.
fn rehash(old: &[Option<IdCore>], k0: u64, k1: u64, slots: usize) -> (Vec<Option<IdCore>>, usize) {
    let mut table = free_table(slots);
    let mut count = 0usize;
    let mut i = 0usize;
    while i < old.len() {
        let slot = old[i];
        match slot {
            Some(id) => {
                if put(&mut table, k0, k1, id) {
                    count += 1;
                }
            }
            None => {}
        }
        i += 1;
    }
    (table, count)
}

impl Default for IdSetCore {
    fn default() -> Self {
        Self::new()
    }
}

impl IdSetCore {
    /// The empty set whose hash has the key `(0, 0)`: the same table for the
    /// same ids in every run. It holds no table until the first insertion.
    pub fn new() -> Self {
        Self::with_key(0, 0)
    }

    /// The empty set whose hash has the key `(k0, k1)`. For ids a peer
    /// chooses, the key is two words the peer cannot know.
    pub fn with_key(k0: u64, k1: u64) -> Self {
        Self {
            buckets: Vec::new(),
            len: 0,
            k0,
            k1,
        }
    }

    /// Empties the set. A table of `FIRST_SLOTS` slots, or one that is at
    /// least an eighth full, is emptied in place: nothing is allocated and
    /// the table keeps its memory. A larger table that holds fewer ids is
    /// let go for a table of `FIRST_SLOTS` slots, so emptying a set costs
    /// no more than a constant per id it holds, however large its table
    /// grew before. An empty set is left as it is.
    pub fn clear(&mut self) {
        if self.len == 0 {
            return;
        }
        let slots = self.buckets.len();
        if slots <= FIRST_SLOTS {
            free_all(&mut self.buckets);
        } else if slots / 8 <= self.len {
            free_all(&mut self.buckets);
        } else {
            self.buckets = free_table(FIRST_SLOTS);
        }
        self.len = 0;
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn contains(&self, id: IdCore) -> bool {
        match probe(&self.buckets, self.k0, self.k1, id) {
            Probe::Found => true,
            Probe::Free(_) => false,
            Probe::Full => false,
        }
    }

    /// Makes room for one more id: the first table, or a table twice the
    /// size when this one is half full. Returns `false`, and leaves the set
    /// as it was, only when the table would have to grow beyond what a
    /// `usize` counts.
    fn reserve(&mut self) -> bool {
        let slots = self.buckets.len();
        if slots == 0 {
            self.buckets = free_table(FIRST_SLOTS);
            true
        } else if self.len < slots / 2 {
            true
        } else if slots > usize::MAX / 2 {
            false
        } else {
            let (table, count) = rehash(&self.buckets, self.k0, self.k1, slots * 2);
            self.buckets = table;
            self.len = count;
            true
        }
    }

    /// Adds `id` to the set. Returns `false`, and leaves the set as it was,
    /// only when there is no room for it (`reserve`).
    pub fn insert(&mut self, id: IdCore) -> bool {
        if !self.reserve() {
            return false;
        }
        if put(&mut self.buckets, self.k0, self.k1, id) {
            self.len += 1;
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(client: u64, clock: u64) -> IdCore {
        IdCore { client, clock }
    }

    /// Every id of the table is found from its home slot without crossing a
    /// free slot, the table is a power of two and at most half full.
    fn check(set: &IdSetCore) {
        let slots = set.buckets.len();
        assert!(slots == 0 || slots.is_power_of_two());
        assert!(set.len * 2 <= slots);
        assert_eq!(set.buckets.iter().filter(|slot| slot.is_some()).count(), set.len);
        for (at, slot) in set.buckets.iter().enumerate() {
            if let Some(held) = slot {
                let mut idx = home(set.k0, set.k1, *held, slots);
                while idx != at {
                    assert!(set.buckets[idx].is_some(), "a free slot before {held:?}");
                    assert_ne!(set.buckets[idx], Some(*held), "{held:?} twice");
                    idx = (idx + 1) % slots;
                }
            }
        }
    }

    #[test]
    fn the_empty_set_holds_nothing_and_no_table() {
        let set = IdSetCore::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
        assert!(set.buckets.is_empty());
        assert!(!set.contains(id(0, 0)));
        assert!(!set.contains(id(u64::MAX, u64::MAX)));
        check(&set);
    }

    #[test]
    fn insert_is_idempotent_and_contains_answers_for_what_was_inserted() {
        let mut set = IdSetCore::new();
        assert!(set.insert(id(1, 0)));
        assert!(set.insert(id(1, 0)));
        assert!(set.insert(id(1, 1)));
        assert!(set.insert(id(2, 0)));
        assert_eq!(set.len(), 3);
        assert!(!set.is_empty());
        assert!(set.contains(id(1, 0)));
        assert!(set.contains(id(1, 1)));
        assert!(set.contains(id(2, 0)));
        assert!(!set.contains(id(2, 1)));
        assert!(!set.contains(id(0, 1)));
        assert_eq!(set.buckets.len(), FIRST_SLOTS);
        check(&set);
    }

    #[test]
    fn the_table_doubles_before_it_is_more_than_half_full() {
        let mut set = IdSetCore::new();
        let mut slots = Vec::new();
        for clock in 0..100u64 {
            assert!(set.insert(id(7, clock)));
            check(&set);
            slots.push(set.buckets.len());
        }
        assert_eq!(set.len(), 100);
        // 8 ids fit the first table, 16 the second, …
        assert_eq!(slots[7], 16);
        assert_eq!(slots[8], 32);
        assert_eq!(slots[16], 64);
        assert_eq!(slots[99], 256);
        for clock in 0..100u64 {
            assert!(set.contains(id(7, clock)));
        }
        assert!(!set.contains(id(7, 100)));
        assert!(!set.contains(id(8, 0)));
    }

    #[test]
    fn ids_that_share_a_home_slot_are_all_found() {
        // more ids than the first table has slots: some of them collide
        let mut set = IdSetCore::new();
        let mut homes = [0usize; FIRST_SLOTS];
        for client in 0..8u64 {
            homes[home(0, 0, id(client, 3), FIRST_SLOTS)] += 1;
            assert!(set.insert(id(client, 3)));
        }
        check(&set);
        // a table that is full but for one slot: every probe wraps around
        let mut table = free_table(4);
        assert!(put(&mut table, 0, 0, id(1, 0)));
        assert!(put(&mut table, 0, 0, id(2, 0)));
        assert!(put(&mut table, 0, 0, id(3, 0)));
        assert!(!put(&mut table, 0, 0, id(2, 0)));
        assert_eq!(table.iter().filter(|slot| slot.is_some()).count(), 3);
        assert_eq!(probe(&table, 0, 0, id(3, 0)), Probe::Found);
        assert!(matches!(probe(&table, 0, 0, id(4, 0)), Probe::Free(_)));
        assert!(put(&mut table, 0, 0, id(4, 0)));
        // no free slot is left: an id that is not there ends the walk
        assert_eq!(probe(&table, 0, 0, id(5, 0)), Probe::Full);
        assert!(!put(&mut table, 0, 0, id(5, 0)));
        assert_eq!(probe(&table, 0, 0, id(1, 0)), Probe::Found);
        assert_eq!(probe(&[], 0, 0, id(1, 0)), Probe::Full);
    }

    #[test]
    fn a_large_set_agrees_with_a_reference_set() {
        let mut set = IdSetCore::new();
        let mut reference = std::collections::BTreeSet::new();
        // a fixed pseudo-random walk over a small id space, with repeats
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let rounds = if cfg!(miri) { 300 } else { 20_000 };
        for _ in 0..rounds {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let (client, clock) = (state % 97, (state >> 20) % 211);
            assert_eq!(set.contains(id(client, clock)), reference.contains(&(client, clock)));
            assert!(set.insert(id(client, clock)));
            reference.insert((client, clock));
            assert_eq!(set.len(), reference.len());
        }
        check(&set);
        for client in 0..97u64 {
            for clock in 0..211u64 {
                assert_eq!(set.contains(id(client, clock)), reference.contains(&(client, clock)));
            }
        }
    }

    #[test]
    fn a_keyed_set_holds_what_was_inserted_under_every_key() {
        let keys = [
            (0, 0),
            (1, 0),
            (0, 1),
            (u64::MAX, u64::MAX),
            (0x243F_6A88_85A3_08D3, 0x1319_8A2E_0370_7344),
        ];
        for (k0, k1) in keys {
            let mut set = IdSetCore::with_key(k0, k1);
            assert!(set.is_empty());
            assert!(!set.contains(id(1, 1)));
            for clock in 0..300u64 {
                assert!(set.insert(id(clock % 7, clock)));
                check(&set);
            }
            assert_eq!(set.len(), 300);
            for clock in 0..300u64 {
                assert!(set.contains(id(clock % 7, clock)));
                assert!(!set.contains(id(clock % 7 + 7, clock)));
            }
        }
        // `new` is the set of the key `(0, 0)`
        let (mut plain, mut keyed) = (IdSetCore::new(), IdSetCore::with_key(0, 0));
        for clock in 0..40u64 {
            plain.insert(id(3, clock));
            keyed.insert(id(3, clock));
        }
        assert_eq!(plain.buckets, keyed.buckets);
    }

    #[test]
    fn the_key_decides_the_home_slots() {
        // ids that share a home slot under one key are spread by another one
        let slots = 1usize << 12;
        let mut ids = Vec::new();
        let mut clock = 0u64;
        while ids.len() < 64 {
            if home(11, 13, id(5, clock), slots) == 0 {
                ids.push(id(5, clock));
            }
            clock += 1;
        }
        let mut homes = std::collections::BTreeSet::new();
        for held in &ids {
            homes.insert(home(12, 13, *held, slots));
        }
        assert!(homes.len() > 48, "{} home slots for 64 ids", homes.len());
        let mut homes = std::collections::BTreeSet::new();
        for held in &ids {
            homes.insert(home(11, 14, *held, slots));
        }
        assert!(homes.len() > 48, "{} home slots for 64 ids", homes.len());
        // ids that differ in high bits only, or in both halves alike, are
        // spread under the key `(0, 0)` as well
        let mut homes = std::collections::BTreeSet::new();
        for step in 1..=64u64 {
            homes.insert(home(0, 0, id(5, step << 40), slots));
            homes.insert(home(0, 0, id(step << 40, 5), slots));
            homes.insert(home(0, 0, id(5, (step << 43) | (step << 11)), slots));
        }
        assert!(homes.len() > 150, "{} home slots for 192 ids", homes.len());
    }

    /// How many home slots the ids have in a table of `slots` slots.
    fn home_slots(k0: u64, k1: u64, ids: &[IdCore], slots: usize) -> usize {
        let mut homes = std::collections::BTreeSet::new();
        for held in ids {
            homes.insert(home(k0, k1, *held, slots));
        }
        homes.len()
    }

    #[test]
    fn structured_ids_are_spread_like_random_ones_under_every_key() {
        // the families of ids a peer can send without knowing anything: one
        // client, many clients, halves that agree, halves that differ in
        // high bits only, and halves made of each other with the constants
        // of the hash
        let n: u64 = if cfg!(miri) { 256 } else { 8192 };
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let random: Vec<IdCore> = (0..n).map(|_| id(next(), next())).collect();
        let families: Vec<(&str, Vec<IdCore>)> = vec![
            ("one client, clocks 0..n", (0..n).map(|i| id(7, i)).collect()),
            ("clients 0..n, clock 0", (0..n).map(|i| id(i, 0)).collect()),
            ("clients 0..n, clock = client", (0..n).map(|i| id(i, i)).collect()),
            ("one client, clocks i << 32", (0..n).map(|i| id(7, i << 32)).collect()),
            ("clients i << 32, clock 0", (0..n).map(|i| id(i << 32, 0)).collect()),
            ("one client, clocks i << 48", (0..n).map(|i| id(7, i << 48)).collect()),
            ("clients i << 48, clock 5", (0..n).map(|i| id(i << 48, 5)).collect()),
            (
                "clients and clocks down from u64::MAX",
                (0..n).map(|i| id(u64::MAX - i, u64::MAX - i)).collect(),
            ),
            (
                "clients i * 2^16 + 1, clocks i * 2^20",
                (0..n).map(|i| id((i << 16) + 1, i << 20)).collect(),
            ),
            (
                "clients of 32 clocks each",
                (0..n).map(|i| id(i / 32, i % 32)).collect(),
            ),
            (
                "clock = client * CLIENT_MULTIPLE",
                (0..n).map(|i| id(i, i.wrapping_mul(CLIENT_MULTIPLE))).collect(),
            ),
            (
                "clock = fold(client, CLIENT_MULTIPLE)",
                (0..n).map(|i| id(i, fold(i, CLIENT_MULTIPLE))).collect(),
            ),
            (
                "client = fold(clock, CLOCK_MULTIPLE)",
                (0..n).map(|i| id(fold(i, CLOCK_MULTIPLE), i)).collect(),
            ),
        ];
        let keys = [
            (0u64, 0u64),
            (u64::MAX, u64::MAX),
            (next(), next()),
            (next(), next()),
            (1, 0),
            (0, 1),
        ];
        // a table half full, as the sets and the lists keep theirs
        let slots = 2 * n as usize;
        for (k0, k1) in keys {
            let of_random = home_slots(k0, k1, &random, slots);
            for (name, ids) in &families {
                let got = home_slots(k0, k1, ids, slots);
                assert!(
                    got * 10 >= of_random * 9,
                    "{name} under ({k0:#x}, {k1:#x}): {got} home slots, random ids have {of_random}"
                );
            }
        }
    }

    #[test]
    fn half_a_key_does_not_tell_which_ids_share_a_home_slot() {
        // a peer that knows one word of the key and guesses the other one
        // chooses ids that all have one home slot under its guess: under the
        // key they are spread like any ids. (With the hash this one replaced,
        // a peer that knew `k0` chose the clock that cancels the client, and
        // `k1` did nothing.)
        let (count, slots): (usize, usize) = if cfg!(miri) { (24, 256) } else { (256, 2048) };
        // ids that many, drawn at random, have about this many home slots
        let expected = slots as f64 * (1.0 - (-(count as f64) / slots as f64).exp());
        let enough = (expected * 0.9) as usize;
        let keys = [
            (0x243F_6A88_85A3_08D3u64, 0x1319_8A2E_0370_7344u64),
            (0xA409_3822_299F_31D0, 0x082E_FA98_EC4E_6C89),
            (3, 0xFFFF_FFFF_0000_0000),
        ];
        for (k0, k1) in keys {
            for guess in [0u64, u64::MAX, 0x4528_21E6_38D0_1377] {
                // the word the peer knows, and the one it guesses
                for (known0, known1) in [(k0, guess), (guess, k1)] {
                    assert!((known0, known1) != (k0, k1));
                    // one client, clocks chosen
                    let mut ids = Vec::new();
                    let mut clock = 0u64;
                    while ids.len() < count {
                        if home(known0, known1, id(9, clock), slots) == 0 {
                            ids.push(id(9, clock));
                        }
                        clock += 1;
                    }
                    assert_eq!(home_slots(known0, known1, &ids, slots), 1);
                    let got = home_slots(k0, k1, &ids, slots);
                    assert!(got >= enough, "chosen clocks: {got} home slots, {expected:.0} expected");
                    // one clock, clients chosen
                    let mut ids = Vec::new();
                    let mut client = 0u64;
                    while ids.len() < count {
                        if home(known0, known1, id(client, 9), slots) == 0 {
                            ids.push(id(client, 9));
                        }
                        client += 1;
                    }
                    let got = home_slots(k0, k1, &ids, slots);
                    assert!(
                        got >= enough,
                        "chosen clients: {got} home slots, {expected:.0} expected"
                    );
                }
            }
            // the clock that cancels the client, for the half of the key
            // the peer knows: each product is keyed before the halves meet
            let n = count as u64;
            let cancel0: Vec<IdCore> = (0..n).map(|i| id(i, fold(i ^ k0, CLIENT_MULTIPLE))).collect();
            let cancel1: Vec<IdCore> = (0..n).map(|i| id(fold(i ^ k1, CLOCK_MULTIPLE), i)).collect();
            for ids in [&cancel0, &cancel1] {
                let got = home_slots(k0, k1, ids, slots);
                assert!(got >= enough, "{got} home slots, {expected:.0} expected");
            }
        }
    }

    #[test]
    fn clear_empties_the_set_and_keeps_the_memory_of_the_table() {
        let mut set = IdSetCore::with_key(3, 4);
        // an empty set is left alone: no table appears
        set.clear();
        assert!(set.buckets.is_empty());
        assert_eq!(set.buckets.capacity(), 0);

        for clock in 0..5u64 {
            assert!(set.insert(id(1, clock)));
        }
        let pointer = set.buckets.as_ptr();
        set.clear();
        check(&set);
        assert!(set.is_empty());
        assert_eq!(set.buckets.len(), FIRST_SLOTS);
        assert_eq!(set.buckets.as_ptr(), pointer);
        for clock in 0..5u64 {
            assert!(!set.contains(id(1, clock)));
        }
        // a second `clear` of the emptied set writes nothing
        set.clear();
        assert_eq!(set.buckets.as_ptr(), pointer);

        // a grown table that is an eighth full or more: emptied in place
        for clock in 0..1000u64 {
            assert!(set.insert(id(2, clock)));
        }
        let (pointer, slots) = (set.buckets.as_ptr(), set.buckets.len());
        assert_eq!(slots, 2048);
        set.clear();
        check(&set);
        assert!(set.is_empty());
        assert_eq!(set.buckets.len(), slots);
        assert_eq!(set.buckets.as_ptr(), pointer);
        for clock in 0..1000u64 {
            assert!(!set.contains(id(2, clock)));
        }
        for clock in 0..256u64 {
            assert!(set.insert(id(9, clock)));
        }
        assert_eq!(set.buckets.as_ptr(), pointer);
        set.clear();
        assert_eq!(set.buckets.as_ptr(), pointer);
        assert_eq!(set.buckets.len(), slots);

        // fewer ids than an eighth of the table: the first table again
        for clock in 0..255u64 {
            assert!(set.insert(id(9, clock)));
        }
        set.clear();
        check(&set);
        assert!(set.is_empty());
        assert_eq!(set.buckets.len(), FIRST_SLOTS);
        // which is then emptied in place, however few ids it holds
        assert!(set.insert(id(9, 0)));
        let pointer = set.buckets.as_ptr();
        set.clear();
        assert_eq!(set.buckets.as_ptr(), pointer);
        assert_eq!(set.buckets.len(), FIRST_SLOTS);

        // and the set is used again, with its key
        for clock in 0..1000u64 {
            assert!(set.insert(id(9, clock)));
        }
        check(&set);
        assert_eq!(set.len(), 1000);
        assert_eq!((set.k0, set.k1), (3, 4));
        assert!(set.contains(id(9, 999)));
        assert!(!set.contains(id(2, 999)));
    }
}
