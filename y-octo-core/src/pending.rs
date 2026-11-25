//! What an update can apply now and what has to wait: the decisions of the
//! struct and delete set iterators of an update.
//!
//! A struct is applied when the document holds every clock of its client
//! before it and every struct it depends on (its origins and its parent);
//! a deleted range is applied up to the clocks the document holds. The
//! functions here are pure: they are told the clocks the document holds and
//! answer what to do.

use crate::{order_range::ClockRange, state_vector::StateVectorCore, yata_store::IdCore};

/// The client of the dependency `dep` when a struct of `id_client` has to
/// wait for it: the document holds the clocks of that client below
/// `dep_state`. A dependency on the same client never blocks: the structs
/// of one client are consumed in the order of their clocks.
#[inline]
pub fn dep_missing(id_client: u64, dep: Option<IdCore>, dep_state: u64) -> Option<u64> {
    match dep {
        Some(dep) => {
            if dep.client != id_client && dep.clock >= dep_state {
                Some(dep.client)
            } else {
                None
            }
        }
        None => None,
    }
}

/// The client of the first dependency (left origin, right origin, then
/// parent) a struct of `id_client` has to wait for. Each dependency comes
/// with the clocks the document holds of its client.
#[inline]
pub fn find_missing_dependency_states(
    id_client: u64,
    origin_left: Option<IdCore>,
    left_state: u64,
    origin_right: Option<IdCore>,
    right_state: u64,
    parent: Option<IdCore>,
    parent_state: u64,
) -> Option<u64> {
    match dep_missing(id_client, origin_left, left_state) {
        Some(client) => Some(client),
        None => match dep_missing(id_client, origin_right, right_state) {
            Some(client) => Some(client),
            None => dep_missing(id_client, parent, parent_state),
        },
    }
}

/// The clocks `state` holds of the client of `dep`, where `dep_missing`
/// reads them: for a dependency on another client.
fn dep_state(id_client: u64, dep: Option<IdCore>, state: &StateVectorCore) -> u64 {
    match dep {
        Some(dep) => {
            if dep.client != id_client {
                state.get(dep.client)
            } else {
                0
            }
        }
        None => 0,
    }
}

/// The client of the dependency `dep` when a struct of `id_client` has to
/// wait for it under `state`.
fn dep_blocks(id_client: u64, dep: Option<IdCore>, state: &StateVectorCore) -> Option<u64> {
    dep_missing(id_client, dep, dep_state(id_client, dep, state))
}

/// The client of the first dependency (left origin, right origin, then
/// parent) of the struct `id` that `state` does not cover.
pub fn find_missing_dependency(
    id: IdCore,
    origin_left: Option<IdCore>,
    origin_right: Option<IdCore>,
    parent: Option<IdCore>,
    state: &StateVectorCore,
) -> Option<u64> {
    match dep_blocks(id.client, origin_left, state) {
        Some(client) => Some(client),
        None => match dep_blocks(id.client, origin_right, state) {
            Some(client) => Some(client),
            None => dep_blocks(id.client, parent, state),
        },
    }
}

/// What the clocks of its own client say about a struct, before its
/// dependencies are looked at.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum LocalStep {
    /// a skip: nothing to apply
    Skip,
    /// the document does not hold the clocks of `client` up to the struct:
    /// `missing_clock`, the one before it, is the last one it lacks
    MissingLocal { client: u64, missing_clock: u64 },
    /// the clocks before the struct are there: its dependencies decide
    Ready,
}

/// What to do with a struct of an update.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum StructStep {
    /// a skip: nothing to apply
    Skip,
    /// the document does not hold the clocks of `client` up to the struct
    MissingLocal { client: u64, missing_clock: u64 },
    /// a struct of `client` this one depends on is not there
    MissingDep { client: u64 },
    /// apply the struct from its clock `offset` on; the document then holds
    /// the clocks of its client below `next_state`
    Apply { offset: u64, next_state: u64 },
    /// the document holds every clock of the struct
    AlreadyApplied,
}

/// The first decision on the struct `id`: `local_state` is the clocks the
/// document holds of `id.client`.
#[inline]
pub fn check_local_readiness(id: IdCore, is_skip: bool, local_state: u64) -> LocalStep {
    if is_skip {
        LocalStep::Skip
    } else if id.clock > local_state {
        LocalStep::MissingLocal {
            client: id.client,
            missing_clock: id.clock - 1,
        }
    } else {
        LocalStep::Ready
    }
}

/// Whether a struct of `len` clocks is applied from its clock `offset` on:
/// from its first clock, or from one of its clocks.
#[inline]
fn applies_from(offset: u64, len: u64) -> bool {
    if offset == 0 { true } else { offset < len }
}

/// The decision on a struct that is `LocalStep::Ready`: `len` clocks from
/// `id` on, of which the document holds those below `local_state`
/// (`id.clock <= local_state`); `missing_dep` is the client of a dependency
/// that is not there.
#[inline]
pub fn classify_ready_step(id: IdCore, len: u64, local_state: u64, missing_dep: Option<u64>) -> StructStep {
    match missing_dep {
        Some(client) => StructStep::MissingDep { client },
        None => {
            // not below zero for a struct that is ready
            let offset = if local_state > id.clock {
                local_state - id.clock
            } else {
                0
            };
            if applies_from(offset, len) {
                // the end of the struct, or the last clock there is
                let next_state = if len > u64::MAX - id.clock {
                    u64::MAX
                } else {
                    id.clock + len
                };
                StructStep::Apply { offset, next_state }
            } else {
                StructStep::AlreadyApplied
            }
        }
    }
}

/// What to do with the struct `id` of `len` clocks: `check_local_readiness`,
/// then `classify_ready_step` for a struct that is ready.
#[inline]
pub fn classify_struct_step(
    id: IdCore,
    len: u64,
    is_skip: bool,
    local_state: u64,
    missing_dep: Option<u64>,
) -> StructStep {
    match check_local_readiness(id, is_skip, local_state) {
        LocalStep::Skip => StructStep::Skip,
        LocalStep::MissingLocal { client, missing_clock } => StructStep::MissingLocal { client, missing_clock },
        LocalStep::Ready => classify_ready_step(id, len, local_state, missing_dep),
    }
}

/// The two parts of a deleted range of clocks: the one the document can
/// apply, and the one that waits for clocks it does not hold. `None` for a
/// part without a clock.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct DeleteSplit {
    pub applicable: Option<ClockRange>,
    pub pending: Option<ClockRange>,
}

/// Cuts the clocks `start .. end` at `local_state`, the clocks the document
/// holds of their client: the ones below it can be applied, the others
/// wait. The first question is the one a range the document holds all the
/// clocks of answers: the usual one.
#[inline]
pub fn split_delete_range(start: u64, end: u64, local_state: u64) -> DeleteSplit {
    if local_state >= end {
        if start < end {
            DeleteSplit {
                applicable: Some(ClockRange { start, end }),
                pending: None,
            }
        } else {
            // no clock
            DeleteSplit {
                applicable: None,
                pending: None,
            }
        }
    } else if local_state <= start {
        if start < end {
            DeleteSplit {
                applicable: None,
                pending: Some(ClockRange { start, end }),
            }
        } else {
            // no clock
            DeleteSplit {
                applicable: None,
                pending: None,
            }
        }
    } else {
        // start < local_state < end
        DeleteSplit {
            applicable: Some(ClockRange {
                start,
                end: local_state,
            }),
            pending: Some(ClockRange {
                start: local_state,
                end,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(client: u64, clock: u64) -> IdCore {
        IdCore { client, clock }
    }

    #[test]
    fn a_dependency_blocks_when_its_clock_is_not_held_by_another_client() {
        assert_eq!(dep_missing(1, None, 0), None);
        // the same client never blocks
        assert_eq!(dep_missing(1, Some(id(1, 100)), 0), None);
        assert_eq!(dep_missing(1, Some(id(2, 5)), 5), Some(2));
        assert_eq!(dep_missing(1, Some(id(2, 5)), 0), Some(2));
        assert_eq!(dep_missing(1, Some(id(2, 5)), 6), None);
        assert_eq!(dep_missing(1, Some(id(2, u64::MAX)), u64::MAX), Some(2));
        assert_eq!(dep_missing(1, Some(id(2, 0)), 0), Some(2));
    }

    #[test]
    fn the_first_missing_dependency_is_left_then_right_then_parent() {
        let left = Some(id(2, 5));
        let right = Some(id(3, 5));
        let parent = Some(id(4, 5));
        let missing = |l, r, p| find_missing_dependency_states(1, left, l, right, r, parent, p);
        assert_eq!(missing(0, 0, 0), Some(2));
        assert_eq!(missing(6, 0, 0), Some(3));
        assert_eq!(missing(6, 6, 0), Some(4));
        assert_eq!(missing(6, 6, 6), None);
        assert_eq!(missing(0, 6, 6), Some(2));
        assert_eq!(find_missing_dependency_states(1, None, 0, None, 0, None, 0), None);
        assert_eq!(find_missing_dependency_states(1, None, 0, None, 0, parent, 5), Some(4));

        let mut state = StateVectorCore::new();
        let find = |state: &StateVectorCore| find_missing_dependency(id(1, 9), left, right, parent, state);
        assert_eq!(find(&state), Some(2));
        state.set_max(2, 6);
        assert_eq!(find(&state), Some(3));
        state.set_max(3, 6);
        assert_eq!(find(&state), Some(4));
        state.set_max(4, 5);
        assert_eq!(find(&state), Some(4));
        state.set_max(4, 6);
        assert_eq!(find(&state), None);
        // dependencies on the client of the struct are not looked up
        let own = Some(id(1, 1000));
        assert_eq!(
            find_missing_dependency(id(1, 9), own, own, own, &StateVectorCore::new()),
            None
        );
    }

    #[test]
    fn find_missing_dependency_is_the_scan_of_y_octo() {
        // the loop `y-octo` ran before it called the core
        fn reference(id: IdCore, deps: [Option<IdCore>; 3], state: &StateVectorCore) -> Option<u64> {
            deps.into_iter()
                .flatten()
                .find(|dep| dep.client != id.client && dep.clock >= state.get(dep.client))
                .map(|dep| dep.client)
        }
        let mut state = StateVectorCore::new();
        state.set_max(1, 3);
        state.set_max(2, 2);
        let choices = [
            None,
            Some(id(1, 2)),
            Some(id(1, 3)),
            Some(id(2, 1)),
            Some(id(2, 2)),
            Some(id(3, 0)),
        ];
        for client in 1..=3u64 {
            for left in choices {
                for right in choices {
                    for parent in choices {
                        let this = id(client, 7);
                        let expected = reference(this, [left, right, parent], &state);
                        assert_eq!(find_missing_dependency(this, left, right, parent, &state), expected);
                        let held = |dep: Option<IdCore>| dep.map_or(0, |dep| state.get(dep.client));
                        assert_eq!(
                            find_missing_dependency_states(
                                client,
                                left,
                                held(left),
                                right,
                                held(right),
                                parent,
                                held(parent)
                            ),
                            expected
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn a_struct_is_classified_by_its_clocks_then_by_its_dependencies() {
        use StructStep::*;
        let at = id(7, 10);
        // a skip is a skip whatever else holds
        assert_eq!(classify_struct_step(at, 5, true, 0, Some(3)), Skip);
        assert_eq!(check_local_readiness(at, true, 0), LocalStep::Skip);
        // clocks before the struct are missing: the last of them is named
        assert_eq!(
            classify_struct_step(at, 5, false, 9, Some(3)),
            MissingLocal {
                client: 7,
                missing_clock: 9
            }
        );
        assert_eq!(
            check_local_readiness(at, false, 0),
            LocalStep::MissingLocal {
                client: 7,
                missing_clock: 9
            }
        );
        assert_eq!(check_local_readiness(at, false, 10), LocalStep::Ready);
        assert_eq!(check_local_readiness(at, false, u64::MAX), LocalStep::Ready);
        // a missing dependency comes before the offset
        assert_eq!(
            classify_struct_step(at, 5, false, 10, Some(3)),
            MissingDep { client: 3 }
        );
        assert_eq!(
            classify_struct_step(at, 5, false, 99, Some(3)),
            MissingDep { client: 3 }
        );
        // applied from the first clock the document lacks
        assert_eq!(
            classify_struct_step(at, 5, false, 10, None),
            Apply {
                offset: 0,
                next_state: 15
            }
        );
        assert_eq!(
            classify_struct_step(at, 5, false, 14, None),
            Apply {
                offset: 4,
                next_state: 15
            }
        );
        assert_eq!(classify_struct_step(at, 5, false, 15, None), AlreadyApplied);
        assert_eq!(classify_struct_step(at, 5, false, u64::MAX, None), AlreadyApplied);
        // a struct without a clock at the state is applied, as `y-octo` did
        assert_eq!(
            classify_struct_step(at, 0, false, 10, None),
            Apply {
                offset: 0,
                next_state: 10
            }
        );
        assert_eq!(classify_struct_step(at, 0, false, 11, None), AlreadyApplied);
        // the end of the clocks
        assert_eq!(
            classify_struct_step(id(7, u64::MAX - 1), 5, false, u64::MAX - 1, None),
            Apply {
                offset: 0,
                next_state: u64::MAX
            }
        );
        assert_eq!(
            classify_struct_step(id(7, 0), u64::MAX, false, 0, None),
            Apply {
                offset: 0,
                next_state: u64::MAX
            }
        );
        // the second step alone never goes below zero
        assert_eq!(
            classify_ready_step(at, 5, 3, None),
            Apply {
                offset: 0,
                next_state: 15
            }
        );
    }

    #[test]
    fn a_deleted_range_is_cut_at_the_clocks_the_document_holds() {
        let range = |start, end| Some(ClockRange { start, end });
        let split = |start, end, state| {
            let cut = split_delete_range(start, end, state);
            (cut.applicable, cut.pending)
        };
        assert_eq!(split(5, 10, 0), (None, range(5, 10)));
        assert_eq!(split(5, 10, 5), (None, range(5, 10)));
        assert_eq!(split(5, 10, 6), (range(5, 6), range(6, 10)));
        assert_eq!(split(5, 10, 9), (range(5, 9), range(9, 10)));
        assert_eq!(split(5, 10, 10), (range(5, 10), None));
        assert_eq!(split(5, 10, u64::MAX), (range(5, 10), None));
        assert_eq!(split(0, u64::MAX, u64::MAX), (range(0, u64::MAX), None));
        assert_eq!(split(0, u64::MAX, 0), (None, range(0, u64::MAX)));
        // a range without a clock has no part
        assert_eq!(split(5, 5, 0), (None, None));
        assert_eq!(split(5, 5, 9), (None, None));
        assert_eq!(split(9, 5, 7), (None, None));
        assert_eq!(split(9, 5, 0), (None, None));
        assert_eq!(split(9, 5, u64::MAX), (None, None));

        // every clock of the range is in one part, on its side of the state
        for start in 0..8u64 {
            for end in 0..8u64 {
                for state in 0..9u64 {
                    let (applicable, pending) = split(start, end, state);
                    for clock in 0..9u64 {
                        let inside = |part: Option<ClockRange>| part.is_some_and(|r| r.start <= clock && clock < r.end);
                        assert_eq!(inside(applicable), start <= clock && clock < end && clock < state);
                        assert_eq!(inside(pending), start <= clock && clock < end && clock >= state);
                    }
                    for part in [applicable, pending].into_iter().flatten() {
                        assert!(part.start < part.end);
                    }
                }
            }
        }
    }
}
