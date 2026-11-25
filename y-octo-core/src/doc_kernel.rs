//! The decisions `DocStore` (`y-octo/src/doc/store.rs`) takes about the
//! structure of a document, apart from the conflict scan (`yata_store`):
//! whether a struct may name another one as its origin or its parent,
//! whether two items are in the same list, whether a type would hold itself,
//! whether a new item has to be scanned for, how it is linked into a list or
//! under a map key, whether two items are one, and where a struct is cut.
//!
//! Every function is pure and total: it is told what the store read off its
//! items and answers what to do. `y-octo` runs them where it took these
//! decisions by hand, and `YataStoreCore` runs the ones a root sequence has.

use crate::{
    client_blocks::StoreError,
    yata_store::{IdCore, opt_id_eq, opt_slot_eq, slot_is},
};

/// Whether the struct `parent_id` may have been there when `item_id` was
/// made: unless it is a struct of the same client created at or after it.
/// (A struct of another client is not known to be late: the update iterator
/// waits for it.)
#[inline]
pub fn parent_precedes_item(item_id: IdCore, parent_id: IdCore) -> bool {
    !(parent_id.client == item_id.client && parent_id.clock >= item_id.clock)
}

/// An item cannot anchor to a struct of its client created at or after
/// itself.
#[inline]
pub fn check_origin(id: IdCore, origin: Option<IdCore>) -> Result<(), StoreError> {
    match origin {
        Some(origin) => {
            if parent_precedes_item(id, origin) {
                Ok(())
            } else {
                Err(StoreError::InvalidOrigin)
            }
        }
        None => Ok(()),
    }
}

/// Whether an item of the parent `other_parent` is in the list of an item
/// of the parent `this_parent`: the same parent type and, as `same_sub`
/// says, the same map key. An item whose parent was not resolved
/// (`this_parent` is `None`) is collected instead of linked: it matches
/// anything.
#[inline]
pub fn same_container(other_parent: Option<u32>, this_parent: Option<u32>, same_sub: bool) -> bool {
    match this_parent {
        Some(this) => match other_parent {
            Some(other) => other == this && same_sub,
            None => false,
        },
        None => true,
    }
}

/// Whether a type put into `parent` is that type itself.
#[inline]
pub fn check_direct_cycle(inner: u32, parent: u32) -> bool {
    inner == parent
}

/// What one step up the type tree says about a type `inner` that is being
/// put under an ancestor of `current`.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum ParentWalkStep {
    /// `current` is `inner`: the type would hold itself
    Cycle,
    /// the walk has taken all the steps it was given
    Exhausted,
    /// go on from the parent of `current`, with this many steps left
    Continue(usize),
}

/// One step of the walk from a type up through its ancestors, looking for
/// `inner`. The walk is given as many steps as the document has types
/// (`remaining` at its first step): an ancestor it has not met by then is
/// not there, since a walk that long goes round a loop of types that does
/// not hold `inner` (`DocKernel.walk_iff_reach` in `proofs/`). No set of the
/// types it met is kept.
#[inline]
pub fn parent_walk_step(inner: u32, current: u32, remaining: usize) -> ParentWalkStep {
    if current == inner {
        ParentWalkStep::Cycle
    } else if remaining == 0 {
        ParentWalkStep::Exhausted
    } else {
        ParentWalkStep::Continue(remaining - 1)
    }
}

/// Whether other items may sit between the two neighbours the origins of a
/// new item name: unless the right one follows the left one directly
/// (`left_right` is the right neighbour of the left one), or is the first
/// item when there is no left one (`right_left` is its left neighbour).
#[inline]
pub fn needs_conflict_scan(
    has_left: bool,
    left_right: Option<u32>,
    right: Option<u32>,
    right_left: Option<u32>,
) -> bool {
    if has_left {
        !opt_slot_eq(left_right, right)
    } else {
        match right {
            Some(_) => match right_left {
                Some(_) => true,
                None => false,
            },
            None => true,
        }
    }
}

/// What linking a new item does besides making it the neighbour of its
/// neighbours.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct IntegrateLinkPlan {
    /// the item is the first one of its list
    pub set_list_start: bool,
    /// the item is the last one under its map key: the value of the key
    pub set_map_winner: bool,
    /// the item it follows was the value of the key until now: delete it
    pub delete_prev_map_winner: bool,
    /// the item is deleted as it is linked: its parent is deleted, or
    /// another item under its map key comes after it
    pub delete_self: bool,
    /// the item counts toward the length of its list
    pub add_list_len: bool,
}

/// The linking half of `DocStore::integrate_item` for an item with or
/// without neighbours (`has_left`, `has_right`), under a map key or in a
/// list (`is_map_entry`), in a parent that is deleted or not.
///
/// Under a map key the last item is the value (last writer wins): an item
/// linked at the end takes the key and the item before it is deleted, an
/// item linked before another one is deleted itself. `DocKernel.lww_integrate`
/// in `proofs/` shows that this leaves every item of a key deleted but the
/// last one.
#[inline]
pub fn decide_integrate_link(
    has_left: bool,
    has_right: bool,
    is_map_entry: bool,
    parent_deleted: bool,
    countable: bool,
) -> IntegrateLinkPlan {
    // every answer is spelled out branch by branch: a negation as the value
    // of a branch is extracted as a proposition, not as a `bool`
    let set_list_start = if has_left {
        false
    } else if is_map_entry {
        false
    } else {
        true
    };
    let set_map_winner = if is_map_entry {
        if has_right { false } else { true }
    } else {
        false
    };
    let delete_prev_map_winner = if set_map_winner { has_left } else { false };
    let delete_self = if parent_deleted {
        true
    } else if is_map_entry {
        has_right
    } else {
        false
    };
    let add_list_len = if delete_self {
        false
    } else if is_map_entry {
        false
    } else {
        countable
    };
    IntegrateLinkPlan {
        set_list_start,
        set_map_winner,
        delete_prev_map_winner,
        delete_self,
        add_list_len,
    }
}

/// What `can_merge_items` reads of an item: its clocks, its origins and its
/// neighbours.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct MergeSide {
    pub id: IdCore,
    pub len: u64,
    pub origin_left: Option<IdCore>,
    pub origin_right: Option<IdCore>,
    pub left: Option<u32>,
    pub right: Option<u32>,
}

/// Whether the item at the slot `r` follows the item at the slot `l` in
/// their list: each names the other as its neighbour (`left_right` is the
/// right neighbour of the one at `l`, `right_left` the left neighbour of the
/// one at `r`). The first thing `can_merge_items` asks, and the cheapest:
/// `DocStore::merge_items` asks it before it reads anything else of the two.
#[inline]
pub fn follows_in_list(left_right: Option<u32>, l: u32, right_left: Option<u32>, r: u32) -> bool {
    slot_is(left_right, r) && slot_is(right_left, l)
}

/// The conditions of `DocStore::merge_items` on the structure of two items:
/// `right` (slot `r`) follows `left` (slot `l`) in the list and continues
/// it. Its first clock is the next one of the same client, it was typed
/// right after the last clock of `left` with the same right origin, and
/// both are in the same list (`same_container`). A `left` without clocks,
/// or whose clocks do not fit a `u64`, continues nothing.
///
/// Whether the contents of the two can be one is left to the caller.
#[inline]
pub fn can_merge_items(left: MergeSide, l: u32, right: MergeSide, r: u32, same_container: bool) -> bool {
    if !follows_in_list(left.right, l, right.left, r) {
        return false;
    }
    if left.id.client != right.id.client {
        return false;
    }
    if left.len == 0 || left.id.clock > u64::MAX - left.len {
        return false;
    }
    if left.id.clock + left.len != right.id.clock {
        return false;
    }
    let after_last = match right.origin_left {
        Some(origin) => origin.client == left.id.client && origin.clock == left.id.clock + (left.len - 1),
        None => false,
    };
    after_last && opt_id_eq(left.origin_right, right.origin_right) && same_container
}

/// The structs `DocStore::delete_range` cuts before it deletes.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct DeleteSplitPlan {
    /// the struct that holds the first clock of the range is cut there
    pub split_start: bool,
    /// the struct that holds the clock after the range is cut there
    pub split_end: bool,
    /// how many items and blocks the two cuts add
    pub needed_splits: usize,
}

/// Whether deleting from or up to the clock `at` cuts the struct that holds
/// it: a live item (`live_item`) that holds `at` after its first clock
/// (`first_clock`). A struct that is deleted already, or is no item, is not
/// cut, and neither is one that starts at `at`.
#[inline]
pub fn cuts_live_item(live_item: bool, first_clock: u64, at: u64) -> bool {
    live_item && at > first_clock
}

/// The cuts `DocStore::delete_range` makes before it deletes the clocks
/// `start..end` of a client, from what `cuts_live_item` says of the struct
/// that holds `start` (`split_start`) and of the one that holds `end`
/// (`split_end`: `false` when the store does not hold `end`): the two, and
/// how many items and blocks they add.
#[inline]
pub fn plan_delete_range_splits(split_start: bool, split_end: bool) -> DeleteSplitPlan {
    let needed_splits = if split_start {
        if split_end { 2 } else { 1 }
    } else if split_end {
        1
    } else {
        0
    };
    DeleteSplitPlan {
        split_start,
        split_end,
        needed_splits,
    }
}

/// The right half of an item that is cut in two.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct SplitPlan {
    /// its first id: the clock `diff` of the item
    pub right_id: IdCore,
    /// its clocks: the ones the left half does not keep
    pub right_len: u64,
    /// its left origin: the last clock of the left half
    pub right_origin_left: IdCore,
    /// it is the last item under a map key: the key goes to it
    pub update_map_winner: bool,
}

/// `DocStore::split_node`: the item `item_id` of `item_len` clocks keeps its
/// first `diff` clocks and the rest becomes a new item right after it.
/// `None` unless `0 < diff < item_len` and `clock + diff`, the clock of the
/// cut, fits a `u64`: nothing is asked of the clocks after it. The right
/// half takes the map key of an item that was the last (no `has_right`).
#[inline]
pub fn plan_split_node(
    item_id: IdCore,
    item_len: u64,
    diff: u64,
    has_right: bool,
    has_parent: bool,
    has_parent_sub: bool,
) -> Option<SplitPlan> {
    if diff == 0 || diff >= item_len {
        return None;
    }
    if item_id.clock > u64::MAX - diff {
        return None;
    }
    let clock = item_id.clock + diff;
    Some(SplitPlan {
        right_id: IdCore {
            client: item_id.client,
            clock,
        },
        right_len: item_len - diff,
        right_origin_left: IdCore {
            client: item_id.client,
            clock: clock - 1,
        },
        update_map_winner: !has_right && has_parent && has_parent_sub,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(client: u64, clock: u64) -> IdCore {
        IdCore { client, clock }
    }

    #[test]
    fn a_struct_of_the_same_client_at_or_after_an_item_does_not_precede_it() {
        assert!(parent_precedes_item(id(1, 5), id(1, 4)));
        assert!(!parent_precedes_item(id(1, 5), id(1, 5)));
        assert!(!parent_precedes_item(id(1, 5), id(1, u64::MAX)));
        // another client is never late
        assert!(parent_precedes_item(id(1, 5), id(2, 5)));
        assert!(parent_precedes_item(id(1, 0), id(2, u64::MAX)));
        assert!(parent_precedes_item(id(u64::MAX, 0), id(0, 0)));

        assert_eq!(check_origin(id(1, 5), None), Ok(()));
        assert_eq!(check_origin(id(1, 5), Some(id(1, 4))), Ok(()));
        assert_eq!(check_origin(id(1, 5), Some(id(2, 9))), Ok(()));
        assert_eq!(check_origin(id(1, 5), Some(id(1, 5))), Err(StoreError::InvalidOrigin));
        assert_eq!(check_origin(id(1, 5), Some(id(1, 6))), Err(StoreError::InvalidOrigin));
        assert_eq!(check_origin(id(1, 0), Some(id(1, 0))), Err(StoreError::InvalidOrigin));
    }

    #[test]
    fn items_are_in_one_list_by_parent_and_key() {
        // every case of the match `DocStore::same_container` was
        let by_hand = |other: Option<u32>, this: Option<u32>, same_sub: bool| match (other, this) {
            (Some(a), Some(b)) => a == b && same_sub,
            (_, Some(_)) => false,
            _ => true,
        };
        for other in [None, Some(1), Some(2)] {
            for this in [None, Some(1), Some(2)] {
                for same_sub in [false, true] {
                    assert_eq!(
                        same_container(other, this, same_sub),
                        by_hand(other, this, same_sub),
                        "{other:?} {this:?} {same_sub}"
                    );
                }
            }
        }
        assert!(same_container(Some(7), Some(7), true));
        assert!(!same_container(Some(7), Some(7), false));
        assert!(!same_container(Some(7), Some(8), true));
        assert!(!same_container(None, Some(7), true));
        assert!(same_container(Some(7), None, false));
        assert!(same_container(None, None, false));
    }

    /// The walk `DocStore::integrate_item` does with the step: from the
    /// parent of `ty` up, with as many steps as there are types.
    fn bounded_walk(parents: &[Option<u32>], inner: u32, ty: u32) -> bool {
        let parent_of = |at: u32| parents.get(at as usize).copied().flatten();
        let mut remaining = parents.len();
        let mut ancestor = parent_of(ty);
        while let Some(current) = ancestor {
            match parent_walk_step(inner, current, remaining) {
                ParentWalkStep::Cycle => return true,
                ParentWalkStep::Exhausted => break,
                ParentWalkStep::Continue(rest) => remaining = rest,
            }
            ancestor = parent_of(current);
        }
        false
    }

    /// The walk it did before: every type it met is kept in a set.
    fn visited_walk(parents: &[Option<u32>], inner: u32, ty: u32) -> bool {
        let parent_of = |at: u32| parents.get(at as usize).copied().flatten();
        let mut visited: Vec<u32> = Vec::new();
        let mut ancestor = parent_of(ty);
        while let Some(current) = ancestor {
            if visited.contains(&current) {
                break;
            }
            visited.push(current);
            if current == inner {
                return true;
            }
            ancestor = parent_of(current);
        }
        false
    }

    #[test]
    fn the_steps_of_the_walk_up_the_type_tree() {
        assert!(check_direct_cycle(3, 3));
        assert!(!check_direct_cycle(3, 4));
        assert_eq!(parent_walk_step(3, 3, 9), ParentWalkStep::Cycle);
        // the type is looked at before the steps are counted
        assert_eq!(parent_walk_step(3, 3, 0), ParentWalkStep::Cycle);
        assert_eq!(parent_walk_step(3, 4, 0), ParentWalkStep::Exhausted);
        assert_eq!(parent_walk_step(3, 4, 1), ParentWalkStep::Continue(0));
        assert_eq!(
            parent_walk_step(3, 4, usize::MAX),
            ParentWalkStep::Continue(usize::MAX - 1)
        );
    }

    #[test]
    fn the_bounded_walk_finds_an_ancestor_however_deep() {
        // a chain: every type is under the one before it
        let depth: u32 = if cfg!(miri) { 200 } else { 2_000 };
        let parents: Vec<Option<u32>> = (0..depth).map(|at| at.checked_sub(1)).collect();
        for inner in [0, 1, depth / 2, depth - 2] {
            assert!(bounded_walk(&parents, inner, depth - 1), "ancestor {inner}");
            assert!(visited_walk(&parents, inner, depth - 1));
        }
        // the walk starts at the parent: a type is no ancestor of itself
        assert!(!bounded_walk(&parents, depth - 1, depth - 1));
        // nor is a type below
        assert!(!bounded_walk(&parents, depth - 1, depth / 2));
        assert!(!bounded_walk(&parents, 0, 0));
        // a type the document does not hold has no parent
        assert!(!bounded_walk(&parents, 0, depth + 5));
        assert!(!bounded_walk(&[], 0, 0));
    }

    #[test]
    fn the_bounded_walk_ends_on_loops_that_are_there_already() {
        // 0 holds itself
        let own = [Some(0u32), Some(0), None];
        assert!(bounded_walk(&own, 0, 0));
        assert!(bounded_walk(&own, 0, 1));
        assert!(!bounded_walk(&own, 1, 0));
        assert!(!bounded_walk(&own, 2, 1));
        // 4 → 3 → 2 → 1 → 3: a loop of three types below a tail of one
        let looped = [None, Some(3u32), Some(1), Some(2), Some(3)];
        for inner in [1, 2, 3] {
            assert!(bounded_walk(&looped, inner, 4), "in the loop: {inner}");
        }
        // a type outside the loop is not found, and the walk ends
        assert!(!bounded_walk(&looped, 0, 4));
        assert!(!bounded_walk(&looped, 4, 4));
        assert!(!bounded_walk(&looped, 4, 2));
        // a parent that is no type of the document ends the walk
        let stale = [Some(9u32), Some(0)];
        assert!(bounded_walk(&stale, 9, 1));
        assert!(bounded_walk(&stale, 0, 1));
        assert!(!bounded_walk(&stale, 1, 1));
    }

    #[test]
    fn the_bounded_walk_agrees_with_the_walk_that_keeps_a_set() {
        // every graph of parent links over up to five types (a parent may
        // also be no type of the document), every pair of types (three
        // types under Miri: the same branches, hundreds of times slower)
        let most = if cfg!(miri) { 3 } else { 5 };
        for types in 0..=most {
            let choices = types + 2;
            let mut graph = vec![0u32; types as usize];
            loop {
                let parents: Vec<Option<u32>> = graph
                    .iter()
                    .map(|&choice| if choice == 0 { None } else { Some(choice - 1) })
                    .collect();
                for inner in 0..=types {
                    for ty in 0..=types {
                        assert_eq!(
                            bounded_walk(&parents, inner, ty),
                            visited_walk(&parents, inner, ty),
                            "{parents:?} inner {inner} under {ty}"
                        );
                    }
                }
                // the next graph
                let mut at = 0;
                while at < graph.len() {
                    graph[at] += 1;
                    if graph[at] < choices {
                        break;
                    }
                    graph[at] = 0;
                    at += 1;
                }
                if at == graph.len() {
                    break;
                }
            }
        }
        // random graphs of a few hundred types
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut below = move |n: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % n
        };
        let rounds = if cfg!(miri) { 4 } else { 400 };
        for _ in 0..rounds {
            let types = 1 + below(if cfg!(miri) { 40 } else { 300 });
            let parents: Vec<Option<u32>> = (0..types)
                .map(|_| match below(10) {
                    0 => None,
                    _ => Some(below(types) as u32),
                })
                .collect();
            for _ in 0..40 {
                let (inner, ty) = (below(types) as u32, below(types) as u32);
                assert_eq!(
                    bounded_walk(&parents, inner, ty),
                    visited_walk(&parents, inner, ty),
                    "{parents:?} inner {inner} under {ty}"
                );
            }
        }
    }

    #[test]
    fn an_item_is_scanned_for_unless_its_neighbours_touch() {
        // what `DocStore::integrate_item` computed by hand
        let by_hand = |has_left: bool, left_right: Option<u32>, right: Option<u32>, right_left: Option<u32>| {
            let right_is_null_or_has_left = match right {
                None => true,
                Some(_) => right_left.is_some(),
            };
            let left_has_other_right_than_self = has_left && left_right != right;
            !has_left && right_is_null_or_has_left || left_has_other_right_than_self
        };
        let slots = [None, Some(0u32), Some(1), Some(u32::MAX)];
        for has_left in [false, true] {
            for left_right in slots {
                for right in slots {
                    for right_left in slots {
                        assert_eq!(
                            needs_conflict_scan(has_left, left_right, right, right_left),
                            by_hand(has_left, left_right, right, right_left),
                            "{has_left} {left_right:?} {right:?} {right_left:?}"
                        );
                    }
                }
            }
        }
        // an empty list, and an item at its end
        assert!(needs_conflict_scan(false, None, None, None));
        assert!(!needs_conflict_scan(true, None, None, None));
        // right before the first item, and between two that touch
        assert!(!needs_conflict_scan(false, None, Some(4), None));
        assert!(!needs_conflict_scan(true, Some(4), Some(4), Some(3)));
        // something in between
        assert!(needs_conflict_scan(false, None, Some(4), Some(2)));
        assert!(needs_conflict_scan(true, Some(5), Some(4), Some(5)));
        assert!(needs_conflict_scan(true, Some(5), None, None));
    }

    #[test]
    fn the_link_plan_is_what_integrate_item_did_by_hand() {
        for bits in 0..32u32 {
            let [has_left, has_right, is_map_entry, parent_deleted, countable] =
                [0, 1, 2, 3, 4].map(|bit| bits & (1 << bit) != 0);
            let plan = decide_integrate_link(has_left, has_right, is_map_entry, parent_deleted, countable);
            // `if let Some(left) … else if key.is_none() { start = idx }`
            assert_eq!(plan.set_list_start, !has_left && !is_map_entry);
            // `if let Some(right) … else if let Some(key) { map_set;
            // delete(left) }`
            assert_eq!(plan.set_map_winner, !has_right && is_map_entry);
            assert_eq!(plan.delete_prev_map_winner, !has_right && is_map_entry && has_left);
            // `if parent_deleted || key.is_some() && right.is_some() { delete
            // }`
            let delete_self = parent_deleted || is_map_entry && has_right;
            assert_eq!(plan.delete_self, delete_self);
            // `else if key.is_none() && countable { len += … }`
            assert_eq!(plan.add_list_len, !delete_self && !is_map_entry && countable);
            // an item that takes a key is not deleted for coming before another
            if plan.set_map_winner {
                assert_eq!(plan.delete_self, parent_deleted);
            }
            // nothing of a map key happens to an item of a list
            if !is_map_entry {
                assert!(!plan.set_map_winner && !plan.delete_prev_map_winner);
                assert_eq!(plan.delete_self, parent_deleted);
            }
        }
    }

    /// The values under one map key, in the order of their list, with
    /// whether each is deleted: what `decide_integrate_link` makes of a new
    /// value at the place `at`.
    fn integrate_under_key(chain: &mut Vec<(u32, bool)>, at: usize, value: u32) {
        let plan = decide_integrate_link(at > 0, at < chain.len(), true, false, true);
        assert!(!plan.set_list_start && !plan.add_list_len);
        if plan.delete_prev_map_winner {
            chain[at - 1].1 = true;
        }
        assert_eq!(plan.set_map_winner, at == chain.len());
        chain.insert(at, (value, plan.delete_self));
    }

    #[test]
    fn the_last_value_under_a_key_wins_whatever_the_order_of_arrival() {
        // values arrive at every place of the list they can: at most the
        // last one is not deleted, and the places alone say which
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut below = move |n: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % n
        };
        for _ in 0..(if cfg!(miri) { 10 } else { 200 }) {
            let mut chain: Vec<(u32, bool)> = Vec::new();
            for value in 0..(1 + below(12)) as u32 {
                let at = below(chain.len() as u64 + 1) as usize;
                integrate_under_key(&mut chain, at, value);
                let (last, before) = chain.split_last().unwrap();
                assert!(before.iter().all(|(_, deleted)| *deleted), "{chain:?}");
                assert!(!last.1, "{chain:?}");
            }
        }
        // two replicas get the same three values in the two orders that end
        // in the same list
        let mut one = Vec::new();
        integrate_under_key(&mut one, 0, 10);
        integrate_under_key(&mut one, 1, 20);
        integrate_under_key(&mut one, 1, 15);
        let mut other = Vec::new();
        integrate_under_key(&mut other, 0, 15);
        integrate_under_key(&mut other, 0, 10);
        integrate_under_key(&mut other, 2, 20);
        assert_eq!(one, [(10, true), (15, true), (20, false)]);
        assert_eq!(one, other);
    }

    fn side(
        id: IdCore,
        len: u64,
        origin_left: Option<IdCore>,
        origin_right: Option<IdCore>,
        left: Option<u32>,
        right: Option<u32>,
    ) -> MergeSide {
        MergeSide {
            id,
            len,
            origin_left,
            origin_right,
            left,
            right,
        }
    }

    #[test]
    fn an_item_follows_another_when_each_names_the_other() {
        assert!(follows_in_list(Some(8), 7, Some(7), 8));
        assert!(!follows_in_list(Some(9), 7, Some(7), 8));
        assert!(!follows_in_list(Some(8), 7, Some(6), 8));
        assert!(!follows_in_list(None, 7, Some(7), 8));
        assert!(!follows_in_list(Some(8), 7, None, 8));
        assert!(!follows_in_list(None, 7, None, 8));
        assert!(follows_in_list(Some(0), u32::MAX, Some(u32::MAX), 0));
        // it is what `can_merge_items` asks first
        let left = side(id(1, 10), 3, None, None, None, Some(8));
        let right = side(id(1, 13), 2, Some(id(1, 12)), None, Some(7), None);
        assert!(can_merge_items(left, 7, right, 8, true));
        for (l, r) in [(6, 8), (7, 9), (8, 7)] {
            assert!(!follows_in_list(left.right, l, right.left, r));
            assert!(!can_merge_items(left, l, right, r, true));
        }
    }

    #[test]
    fn two_items_are_one_when_the_second_continues_the_first() {
        let left = side(id(1, 10), 3, None, Some(id(2, 0)), None, Some(8));
        let right = side(id(1, 13), 2, Some(id(1, 12)), Some(id(2, 0)), Some(7), Some(9));
        assert!(can_merge_items(left, 7, right, 8, true));
        // another list
        assert!(!can_merge_items(left, 7, right, 8, false));
        // not neighbours, either way
        assert!(!can_merge_items(left, 7, right, 9, true));
        assert!(!can_merge_items(left, 6, right, 8, true));
        assert!(!can_merge_items(MergeSide { right: None, ..left }, 7, right, 8, true));
        assert!(!can_merge_items(left, 7, MergeSide { left: None, ..right }, 8, true));
        // another client, a gap, an overlap
        assert!(!can_merge_items(left, 7, MergeSide { id: id(2, 13), ..right }, 8, true));
        assert!(!can_merge_items(left, 7, MergeSide { id: id(1, 14), ..right }, 8, true));
        assert!(!can_merge_items(left, 7, MergeSide { id: id(1, 12), ..right }, 8, true));
        // typed elsewhere: no left origin, another clock, another client
        for origin_left in [None, Some(id(1, 11)), Some(id(1, 13)), Some(id(3, 12))] {
            assert!(!can_merge_items(left, 7, MergeSide { origin_left, ..right }, 8, true));
        }
        // another right origin
        for origin_right in [None, Some(id(2, 1)), Some(id(3, 0))] {
            assert!(!can_merge_items(left, 7, MergeSide { origin_right, ..right }, 8, true));
        }
        let no_right_origin = MergeSide {
            origin_right: None,
            ..left
        };
        assert!(!can_merge_items(no_right_origin, 7, right, 8, true));
        assert!(can_merge_items(
            no_right_origin,
            7,
            MergeSide {
                origin_right: None,
                ..right
            },
            8,
            true
        ));
    }

    #[test]
    fn an_item_without_clocks_or_past_the_last_clock_continues_nothing() {
        let right = side(id(1, 10), 1, Some(id(1, 9)), None, Some(0), None);
        // no clocks: `left.len - 1` is not computed
        let empty = side(id(1, 10), 0, None, None, None, Some(1));
        assert!(!can_merge_items(empty, 0, right, 1, true));
        // clocks that do not fit: `left.id.clock + left.len` is not computed
        let last = side(id(1, u64::MAX), 1, None, None, None, Some(1));
        assert!(!can_merge_items(
            last,
            0,
            MergeSide {
                id: id(1, 0),
                origin_left: Some(id(1, u64::MAX)),
                ..right
            },
            1,
            true
        ));
        let long = side(id(1, 5), u64::MAX, None, None, None, Some(1));
        assert!(!can_merge_items(
            long,
            0,
            MergeSide {
                id: id(1, 4),
                origin_left: Some(id(1, 3)),
                ..right
            },
            1,
            true
        ));
        // the last clocks that do fit
        let fits = side(id(1, u64::MAX - 3), 2, None, None, None, Some(1));
        assert!(can_merge_items(
            fits,
            0,
            MergeSide {
                id: id(1, u64::MAX - 1),
                origin_left: Some(id(1, u64::MAX - 2)),
                ..right
            },
            1,
            true
        ));
    }

    #[test]
    fn a_range_is_cut_out_of_live_items_only() {
        // what `DocStore::delete_range` computed by hand
        for live_item in [false, true] {
            for (at, first_clock) in [(5u64, 5u64), (5, 3), (0, 0), (9, 6), (u64::MAX, 0), (3, 7)] {
                assert_eq!(
                    cuts_live_item(live_item, first_clock, at),
                    live_item && at > first_clock,
                    "{live_item} {first_clock} {at}"
                );
            }
        }
        assert!(cuts_live_item(true, 3, 4));
        assert!(!cuts_live_item(true, 3, 3));
        assert!(!cuts_live_item(false, 3, 4));
        for split_start in [false, true] {
            for split_end in [false, true] {
                assert_eq!(
                    plan_delete_range_splits(split_start, split_end),
                    DeleteSplitPlan {
                        split_start,
                        split_end,
                        needed_splits: usize::from(split_start) + usize::from(split_end)
                    }
                );
            }
        }
    }

    #[test]
    fn an_item_is_cut_inside_its_clocks_only() {
        assert_eq!(plan_split_node(id(1, 10), 5, 0, false, true, true), None);
        assert_eq!(plan_split_node(id(1, 10), 5, 5, false, true, true), None);
        assert_eq!(plan_split_node(id(1, 10), 5, 6, false, true, true), None);
        assert_eq!(plan_split_node(id(1, 10), 0, 0, false, true, true), None);
        assert_eq!(plan_split_node(id(1, 10), 1, 1, false, true, true), None);
        assert_eq!(
            plan_split_node(id(1, 10), 5, 2, false, true, true),
            Some(SplitPlan {
                right_id: id(1, 12),
                right_len: 3,
                right_origin_left: id(1, 11),
                update_map_winner: true
            })
        );
        // the key goes to the right half of its last item only
        for (has_right, has_parent, has_parent_sub) in [
            (true, true, true),
            (false, false, true),
            (false, true, false),
            (true, false, false),
        ] {
            let plan = plan_split_node(id(1, 10), 5, 4, has_right, has_parent, has_parent_sub).unwrap();
            assert!(!plan.update_map_winner);
            assert_eq!(
                (plan.right_id, plan.right_len, plan.right_origin_left),
                (id(1, 14), 1, id(1, 13))
            );
        }
        // clocks that do not fit a `u64` are not computed
        assert_eq!(plan_split_node(id(1, u64::MAX), 5, 1, true, true, true), None);
        assert_eq!(plan_split_node(id(1, u64::MAX - 1), 5, 2, true, true, true), None);
        assert_eq!(
            plan_split_node(id(1, u64::MAX - 2), 3, 2, true, true, true),
            Some(SplitPlan {
                right_id: id(1, u64::MAX),
                right_len: 1,
                right_origin_left: id(1, u64::MAX - 1),
                update_map_winner: false
            })
        );
    }
}
