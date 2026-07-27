use super::{HashSet, Id, StateVector};

pub(crate) fn find_clock_segment(
    count: usize,
    clock: u64,
    mut segment_at: impl FnMut(usize) -> Option<(u64, u64)>,
) -> Option<usize> {
    let mut left = 0usize;
    let mut right = count;

    while left < right {
        let middle = left + (right - left) / 2;
        let (start, len) = segment_at(middle)?;
        let end = start.saturating_add(len);
        if clock < start {
            right = middle;
        } else if clock >= end {
            left = middle + 1;
        } else {
            return Some(middle);
        }
    }

    None
}

/// consider `offset` as a utf-16 encoded string offset
pub(crate) fn utf16_offset_to_utf8(value: &str, offset: u64) -> usize {
    if offset == 0 {
        return 0;
    }
    let mut utf16 = 0u64;
    let mut utf8 = 0usize;
    for character in value.chars() {
        utf16 += character.len_utf16() as u64;
        utf8 += character.len_utf8();
        if utf16 >= offset {
            break;
        }
    }
    utf8
}

pub(crate) fn find_conflict_left<T: Clone + Eq>(
    this: ConflictItem,
    mut left: Option<T>,
    mut conflict: Option<T>,
    right: Option<T>,
    mut item: impl FnMut(&T) -> Option<ConflictItem>,
    mut next: impl FnMut(&T) -> Option<T>,
) -> Option<T> {
    let mut conflicting = HashSet::default();
    let mut before_origin = HashSet::default();

    while let Some(current) = conflict {
        if right.as_ref() == Some(&current) {
            break;
        }
        let Some(candidate) = item(&current) else {
            break;
        };
        before_origin.insert(candidate.id);
        conflicting.insert(candidate.id);

        if this.origin_left == candidate.origin_left {
            if candidate.id.client < this.id.client {
                left = Some(current.clone());
                conflicting.clear();
            } else if this.origin_right == candidate.origin_right {
                break;
            }
        } else if let Some(candidate_left) = candidate.origin_left {
            if before_origin.contains(&candidate_left) && !conflicting.contains(&candidate_left) {
                left = Some(current.clone());
                conflicting.clear();
            }
        } else {
            break;
        }

        conflict = next(&current);
    }

    left
}

/// Returns the client of the first dependency (origin left, origin right,
/// then parent) not yet covered by `state`, mirroring yjs' integration order
/// decision. Dependencies on the same client never block: structs of one
/// client are always consumed in clock order.
pub(crate) fn find_missing_dependency(
    id: Id,
    origin_left: Option<Id>,
    origin_right: Option<Id>,
    parent: Option<Id>,
    state: &StateVector,
) -> Option<u64> {
    for dependency in [origin_left, origin_right, parent].into_iter().flatten() {
        if dependency.client != id.client && dependency.clock >= state.get(&dependency.client) {
            return Some(dependency.client);
        }
    }
    None
}

#[derive(Clone, Copy)]
pub(crate) struct ConflictItem {
    pub id: Id,
    pub origin_left: Option<Id>,
    pub origin_right: Option<Id>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn segments(segments: &[(u64, u64)]) -> impl FnMut(usize) -> Option<(u64, u64)> + '_ {
        |index| segments.get(index).copied()
    }

    #[test]
    #[allow(clippy::type_complexity)]
    fn clock_segment_lookup() {
        let cases: &[(&[(u64, u64)], u64, Option<usize>)] = &[
            (&[], 0, None),
            (&[(0, 10)], 0, Some(0)),
            (&[(0, 10)], 9, Some(0)),
            (&[(0, 10)], 10, None),
            (&[(0, 10), (10, 5), (20, 10)], 19, None),
            (&[(0, 10), (10, 5), (20, 10)], 20, Some(2)),
            (&[(0, 10), (10, 5), (20, 10)], 29, Some(2)),
            (&[(0, 10), (10, 5), (20, 10)], 30, None),
            (&[(5, 5), (20, 10)], 4, None),
            (&[(5, 5), (20, 10)], 7, Some(0)),
        ];
        for (segments_input, clock, expected) in cases {
            assert_eq!(
                find_clock_segment(segments_input.len(), *clock, segments(segments_input)),
                *expected,
                "segments {segments_input:?} clock {clock}"
            );
        }
    }

    #[test]
    fn utf16_offsets() {
        let cases: &[(&str, u64, usize)] = &[
            ("", 0, 0),
            ("abc", 0, 0),
            ("abc", 1, 1),
            ("abc", 3, 3),
            ("a😀b", 1, 1),
            // offset inside the surrogate pair rounds up to the char boundary
            ("a😀b", 2, 5),
            ("a😀b", 3, 5),
            ("a😀b", 4, 6),
            ("中文", 1, 3),
            ("中文", 2, 6),
        ];
        for (value, offset, expected) in cases {
            assert_eq!(
                utf16_offset_to_utf8(value, *offset),
                *expected,
                "{value:?} offset {offset}"
            );
        }
    }

    #[test]
    #[allow(clippy::type_complexity)]
    fn missing_dependency_order() {
        let state = StateVector::from([(1, 10), (2, 5)]);
        let id = Id::new(1, 10);
        let cases: &[(Option<Id>, Option<Id>, Option<Id>, Option<u64>)] = &[
            (None, None, None, None),
            // satisfied dependencies never block
            (Some(Id::new(1, 9)), Some(Id::new(2, 4)), Some(Id::new(2, 0)), None),
            // same-client dependencies never block even beyond state
            (Some(Id::new(1, 100)), None, None, None),
            // first unsatisfied dependency wins: left, then right, then parent
            (Some(Id::new(2, 5)), Some(Id::new(3, 0)), Some(Id::new(4, 0)), Some(2)),
            (None, Some(Id::new(3, 0)), Some(Id::new(4, 0)), Some(3)),
            (None, None, Some(Id::new(4, 0)), Some(4)),
        ];
        for (left, right, parent, expected) in cases {
            assert_eq!(
                find_missing_dependency(id, *left, *right, *parent, &state),
                *expected,
                "left {left:?} right {right:?} parent {parent:?}"
            );
        }
    }

    #[derive(Clone, PartialEq, Eq, Debug)]
    struct ConflictNode {
        id: Id,
        origin_left: Option<Id>,
        origin_right: Option<Id>,
        right: Option<usize>,
    }

    fn conflict_left(
        this: ConflictItem,
        left: Option<usize>,
        conflict: Option<usize>,
        right: Option<usize>,
        nodes: &[ConflictNode],
    ) -> Option<usize> {
        find_conflict_left(
            this,
            left,
            conflict,
            right,
            |&index| {
                nodes.get(index).map(|node| ConflictItem {
                    id: node.id,
                    origin_left: node.origin_left,
                    origin_right: node.origin_right,
                })
            },
            |&index| nodes.get(index).and_then(|node| node.right),
        )
    }

    fn item(client: u64, clock: u64, origin_left: Option<Id>, origin_right: Option<Id>) -> ConflictItem {
        ConflictItem {
            id: Id::new(client, clock),
            origin_left,
            origin_right,
        }
    }

    #[test]
    fn conflict_left_decisions() {
        // concurrent inserts at the same position: lower client id goes left
        let concurrent = |this_client: u64, other_client: u64| {
            let nodes = [ConflictNode {
                id: Id::new(other_client, 0),
                origin_left: None,
                origin_right: None,
                right: None,
            }];
            conflict_left(item(this_client, 0, None, None), None, Some(0), None, &nodes)
        };
        assert_eq!(concurrent(2, 1), Some(0), "higher client id inserts after");
        assert_eq!(concurrent(1, 2), None, "lower client id inserts before");

        // same origin left but higher client id and matching origin right:
        // insert before the candidate
        let nodes = [ConflictNode {
            id: Id::new(2, 0),
            origin_left: Some(Id::new(1, 0)),
            origin_right: Some(Id::new(1, 5)),
            right: None,
        }];
        assert_eq!(
            conflict_left(
                item(1, 6, Some(Id::new(1, 0)), Some(Id::new(1, 5))),
                None,
                Some(0),
                None,
                &nodes
            ),
            None
        );

        // a candidate whose origin left was walked past before the last
        // conflicting clear becomes the new left
        let nodes = [
            ConflictNode {
                id: Id::new(1, 0),
                origin_left: Some(Id::new(8, 0)),
                origin_right: None,
                right: Some(1),
            },
            ConflictNode {
                id: Id::new(2, 0),
                origin_left: Some(Id::new(8, 0)),
                origin_right: None,
                right: Some(2),
            },
            ConflictNode {
                id: Id::new(3, 0),
                origin_left: Some(Id::new(1, 0)),
                origin_right: None,
                right: None,
            },
        ];
        assert_eq!(
            conflict_left(item(9, 0, Some(Id::new(8, 0)), None), None, Some(0), None, &nodes),
            Some(2)
        );

        // a conflict chain that reaches the right neighbor keeps the current left
        let nodes = [ConflictNode {
            id: Id::new(2, 0),
            origin_left: Some(Id::new(1, 0)),
            origin_right: None,
            right: Some(1),
        }];
        assert_eq!(
            conflict_left(item(3, 0, Some(Id::new(9, 0)), None), None, Some(0), Some(1), &nodes),
            None
        );
    }
}
