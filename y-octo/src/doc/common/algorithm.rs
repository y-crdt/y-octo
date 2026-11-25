use std::borrow::Cow;

use y_octo_core::{
    id_order::{IdOrderCore, Recent},
    pending::dep_missing,
    utf16::utf16_split_byte_offset,
    yata_store::{ConflictDecision, IdCore, ScanStep, decide_conflict_step, decide_owner_step},
};

use super::{Id, StateVector, TOO_MANY_CANDIDATES};
use crate::{JwstCodecError, JwstCodecResult};

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

/// Slice by Yjs clocks (UTF-16 code units), not UTF-8 bytes or Unicode scalars.
/// Like Yjs ContentString.splice, replace each retained half of a split
/// surrogate pair with U+FFFD rather than rounding the boundary and changing
/// its clock length.
///
/// The two boundaries are found by
/// `y_octo_core::utf16::utf16_split_byte_offset` (proved in `proofs/`): the
/// first from the start of `value`, the second from the first one on, so
/// `value` is walked once.
pub(crate) fn utf16_slice(value: &str, offset: u64, len: u64) -> Cow<'_, str> {
    if len == 0 {
        return Cow::Borrowed(&value[..0]);
    }
    let bytes = value.as_bytes();
    let start = utf16_split_byte_offset(bytes, offset);
    // the clock of the char at `start.start`: `offset`, or the half before it
    let start_clock = if start.split_surrogate { offset - 1 } else { offset };
    let end = utf16_split_byte_offset(&bytes[start.start..], offset.saturating_add(len) - start_clock);
    let selected = &value[if start.split_surrogate { start.end } else { start.start }..start.start + end.start];
    if start.split_surrogate || end.split_surrogate {
        Cow::Owned(format!(
            "{}{selected}{}",
            if start.split_surrogate { "\u{FFFD}" } else { "" },
            if end.split_surrogate { "\u{FFFD}" } else { "" },
        ))
    } else {
        Cow::Borrowed(selected)
    }
}

/// Split `value` in place at UTF-16 code-unit `offset`, returning the right
/// half. Matches [`utf16_slice`] on surrogate-pair boundaries by replacing each
/// retained half with `U+FFFD`.
pub(crate) fn utf16_split_in_place(value: &mut String, offset: u64) -> String {
    let at = utf16_split_byte_offset(value.as_bytes(), offset);
    let right = if at.split_surrogate {
        let tail = &value[at.end..];
        let mut right = String::with_capacity('\u{FFFD}'.len_utf8() + tail.len());
        right.push('\u{FFFD}');
        right.push_str(tail);
        value.truncate(at.start);
        value.push('\u{FFFD}');
        right
    } else {
        value.split_off(at.start)
    };
    value.shrink_to_fit();
    right
}

pub(crate) struct Utf16Slices<'a> {
    value: &'a str,
    chars: std::iter::Peekable<std::str::CharIndices<'a>>,
    clock: u64,
}

impl<'a> Utf16Slices<'a> {
    pub(crate) fn new(value: &'a str) -> Self {
        Self {
            value,
            chars: value.char_indices().peekable(),
            clock: 0,
        }
    }

    fn boundary(&mut self, target: u64) -> (usize, usize, bool) {
        while let Some(&(byte, ch)) = self.chars.peek() {
            let next = self.clock + ch.len_utf16() as u64;
            if target < next {
                return (byte, byte + ch.len_utf8(), target > self.clock);
            }
            self.clock = next;
            self.chars.next();
        }
        (self.value.len(), self.value.len(), false)
    }

    // Callers supplying multiple slices must advance in UTF-16 clock order.
    pub(crate) fn slice(&mut self, offset: u64, len: u64) -> Cow<'a, str> {
        if len == 0 {
            return Cow::Borrowed(&self.value[..0]);
        }
        let (start, after_start, start_surrogate) = self.boundary(offset);
        let (end, _, end_surrogate) = self.boundary(offset.saturating_add(len));
        let selected = &self.value[if start_surrogate { after_start } else { start }..end];
        if start_surrogate || end_surrogate {
            Cow::Owned(format!(
                "{}{selected}{}",
                if start_surrogate { "\u{FFFD}" } else { "" },
                if end_surrogate { "\u{FFFD}" } else { "" },
            ))
        } else {
            Cow::Borrowed(selected)
        }
    }
}

#[inline]
pub(crate) fn core_id(id: Id) -> IdCore {
    IdCore {
        client: id.client,
        clock: id.clock,
    }
}

/// The key of the table of one conflict scan: two words a peer cannot know,
/// so the ids it sends cannot be chosen to share their probes
/// (`IdOrderCore::key`). One `RandomState` gives both. Without the feature
/// `random` (`ahash` 0.8.12 with `compile-time-rng`) the seeds `ahash`
/// hashes under are the ones it was built with, the same in every run of
/// one build. The words are still not one key for the process: every
/// `RandomState::new()` mixes in a counter that `ahash` steps by an address
/// of its own, so no two scans share a key. They are no better hidden than
/// the build, the number of `RandomState`s made before the scan and that
/// address (`proofs/TRUSTED.md`, §4).
#[cfg(not(loom))]
fn scan_key() -> (u64, u64) {
    let state = ahash::RandomState::new();
    (state.hash_one(0u64), state.hash_one(1u64))
}

/// Loom needs every execution of a model to take the same steps.
#[cfg(loom)]
fn scan_key() -> (u64, u64) {
    (0, 0)
}

/// The candidates one conflict scan has walked, in their order: what Yjs
/// keeps as the sets `itemsBeforeOrigin` (all of them) and
/// `conflictingItems` (the ones since the last candidate that was taken).
///
/// Both sets are read off one list, `IdOrderCore` of `y-octo-core`
/// (`IdOrder.recent_spec`, `position_spec` in `proofs/`): a struct is in the
/// first set when the list holds it, and in the second one when its place is
/// not before the last taken candidate. Taking a candidate moves a mark and
/// empties nothing. The struct an origin points into is mostly the one the
/// scan asked for before, or among the last candidates, and is found there
/// by hand; a scan that has to look further back gives the list a key no
/// peer knows and asks its table.
/// How many candidates a scan takes before it refuses the next one: as many
/// as its list holds, or, in tests, a smaller number that reaches the
/// refusal. Outside tests it is nothing: a scan makes its list where it
/// walks, as before.
#[derive(Clone, Copy, Default)]
pub(crate) struct ScanLimit {
    #[cfg(test)]
    pub(crate) candidates: Option<usize>,
}

#[derive(Default)]
struct Scanned {
    order: IdOrderCore,
    /// the place the candidates since the last taken one begin at
    conflict_from: usize,
    /// A smaller number of candidates than the list takes, to reach the
    /// refusal in tests.
    #[cfg(test)]
    limit: Option<usize>,
}

impl Scanned {
    /// The empty list of a scan that takes the candidates `limit` allows.
    #[inline]
    fn limited(limit: ScanLimit) -> Self {
        #[cfg(test)]
        {
            Self {
                limit: limit.candidates,
                ..Self::default()
            }
        }
        #[cfg(not(test))]
        {
            let ScanLimit {} = limit;
            Self::default()
        }
    }

    /// The scan is at the candidate `id`. Answers `false` when the list
    /// does not take it: it holds `2 ^ 30` candidates (`IdOrder.push_spec`).
    /// Candidates are distinct items of one list, 128 bytes each next to a
    /// block of 16 bytes on a timeline and their 16 bytes here: a document
    /// that gets there holds some 170 GB of them. The scan then ends with
    /// an error, as it would for a struct the document has no room for.
    #[inline]
    fn push(&mut self, id: IdCore) -> bool {
        #[cfg(test)]
        if self.limit.is_some_and(|limit| self.order.len() >= limit) {
            return false;
        }
        self.order.push(id)
    }

    /// The candidate the scan is at becomes the left neighbour: nothing
    /// conflicts with what comes after it yet.
    #[inline]
    fn take(&mut self) {
        self.conflict_from = self.order.len();
    }

    /// Whether the struct `owner` is among the candidates walked so far, and
    /// whether it is among the ones since the last taken candidate.
    /// Candidates are structs of the document: none is there twice.
    #[inline]
    fn find(&mut self, owner: IdCore) -> (bool, bool) {
        let at = match self.order.recent(owner) {
            Recent::At(at) => Some(at),
            Recent::Absent => None,
            Recent::Far => self.find_far(owner),
        };
        match at {
            Some(at) => (true, at >= self.conflict_from),
            None => (false, false),
        }
    }

    /// The place of a struct that is not among the last candidates.
    #[cold]
    #[inline(never)]
    fn find_far(&mut self, owner: IdCore) -> Option<usize> {
        if !self.order.is_indexed() {
            let (k0, k1) = scan_key();
            self.order.key(k0, k1);
        }
        self.order.position(owner)
    }
}

/// The YATA conflict scan. What it does with a candidate is decided by
/// `decide_conflict_step` and `decide_owner_step` of `y-octo-core`: the code
/// the scan of `YataStoreCore` runs, which `proofs/` shows to be the scan of
/// the model (`YataStore.scan_step_spec`). The walk, the candidates it has
/// passed ([Scanned]) and the lookup of the struct that holds an origin stay
/// here.
///
/// It fails only when the list of its candidates is full (`Scanned::push`),
/// before anything is linked.
#[inline]
pub(crate) fn find_conflict_left<T: Clone + Eq>(
    this: ConflictItem,
    left: Option<T>,
    conflict: Option<T>,
    right: Option<T>,
    item: impl FnMut(&T) -> Option<ConflictItem>,
    next: impl FnMut(&T) -> Option<T>,
    origin_owner: impl FnMut(Id) -> Option<Id>,
) -> JwstCodecResult<Option<T>> {
    scan_conflict_left(
        ScanLimit::default(),
        this,
        left,
        conflict,
        right,
        item,
        next,
        origin_owner,
    )
}

/// [find_conflict_left] with the number of candidates its list takes.
#[allow(clippy::too_many_arguments)]
pub(crate) fn scan_conflict_left<T: Clone + Eq>(
    limit: ScanLimit,
    this: ConflictItem,
    mut left: Option<T>,
    mut conflict: Option<T>,
    right: Option<T>,
    mut item: impl FnMut(&T) -> Option<ConflictItem>,
    mut next: impl FnMut(&T) -> Option<T>,
    mut origin_owner: impl FnMut(Id) -> Option<Id>,
) -> JwstCodecResult<Option<T>> {
    let mut scanned = Scanned::limited(limit);
    let origin_left = this.origin_left.map(core_id);
    let origin_right = this.origin_right.map(core_id);

    while let Some(current) = conflict {
        if right.as_ref() == Some(&current) {
            break;
        }
        let Some(candidate) = item(&current) else {
            break;
        };
        if !scanned.push(core_id(candidate.id)) {
            return Err(JwstCodecError::IncompleteDocument(TOO_MANY_CANDIDATES.into()));
        }

        // the candidate becomes the left neighbour (`Take`), the scan goes on
        // over it (`Skip`) or ends (`Stop`)
        let take = match decide_conflict_step(
            this.id.client,
            origin_left,
            origin_right,
            candidate.id.client,
            candidate.origin_left.map(core_id),
            candidate.origin_right.map(core_id),
        ) {
            ConflictDecision::Step(ScanStep::Stop) => break,
            ConflictDecision::Step(ScanStep::Take) => true,
            ConflictDecision::Step(ScanStep::Skip) => false,
            ConflictDecision::Owner(candidate_left) => {
                // Origins can point inside compacted structs; the candidates
                // are struct starts.
                let Some(owner) = origin_owner(Id::new(candidate_left.client, candidate_left.clock)) else {
                    break;
                };
                // Yjs stops at an origin outside the scanned prefix; continuing
                // could choose a later conflict and delete the actual map
                // winner.
                let (in_before, in_conflicting) = scanned.find(core_id(owner));
                match decide_owner_step(in_before, in_conflicting) {
                    ScanStep::Stop => break,
                    ScanStep::Take => true,
                    ScanStep::Skip => false,
                }
            }
        };
        if take {
            left = Some(current.clone());
            scanned.take();
        }

        conflict = next(&current);
    }

    Ok(left)
}

/// Returns the client of the first dependency (origin left, origin right,
/// then parent) not yet covered by `state`, mirroring yjs' integration order
/// decision. Dependencies on the same client never block: structs of one
/// client are always consumed in clock order.
///
/// Whether a dependency blocks is `dep_missing` of `y-octo-core`
/// (`Pending.dep_missing_spec`); `state` is only asked for a dependency on
/// another client, and not past the first one that blocks.
pub(crate) fn find_missing_dependency(
    id: Id,
    origin_left: Option<Id>,
    origin_right: Option<Id>,
    parent: Option<Id>,
    state: &StateVector,
) -> Option<u64> {
    for dependency in [origin_left, origin_right, parent] {
        let held = match dependency {
            Some(dependency) if dependency.client != id.client => state.get(&dependency.client),
            _ => 0,
        };
        if let Some(client) = dep_missing(id.client, dependency.map(core_id), held) {
            return Some(client);
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
        for (value, offset, len, expected) in [
            ("", 0, 1, ""),
            ("abc", 0, 3, "abc"),
            ("abc", 1, 1, "b"),
            ("abc", 3, 1, ""),
            ("a😀b", 0, 2, "a\u{FFFD}"),
            ("a😀b", 1, 1, "\u{FFFD}"),
            ("a😀b", 2, 1, "\u{FFFD}"),
            ("a😀b", 2, 2, "\u{FFFD}b"),
            ("a😀b", 2, 0, ""),
            ("a😀b", 1, 2, "😀"),
            ("a😀b", 3, u64::MAX, "b"),
            ("中文", 1, 1, "文"),
        ] {
            assert_eq!(
                utf16_slice(value, offset, len),
                expected,
                "{value:?} offset={offset} len={len}"
            );
        }
        assert!(matches!(utf16_slice("a😀b", 1, 2), Cow::Borrowed("😀")));
        let mut slices = Utf16Slices::new("中😀文🎉尾");
        for (offset, len, expected) in [(0, 2, "中\u{FFFD}"), (2, 3, "\u{FFFD}文\u{FFFD}"), (5, 2, "\u{FFFD}尾")] {
            assert_eq!(slices.slice(offset, len), expected);
        }
        for (value, offset, expected_left, expected_right) in [
            ("abc", 0, "", "abc"),
            ("abc", 1, "a", "bc"),
            ("abc", 3, "abc", ""),
            ("a😀b", 1, "a", "😀b"),
            ("a😀b", 2, "a\u{FFFD}", "\u{FFFD}b"),
            ("a😀b", 3, "a😀", "b"),
            ("中文", 1, "中", "文"),
        ] {
            let mut left = value.to_string();
            let right = utf16_split_in_place(&mut left, offset);
            assert_eq!((left.as_str(), right.as_str()), (expected_left, expected_right));
        }

        // Splitting a large string at a small offset shrinks the left buffer to
        // avoid O(K * N) memory amplification (both normal and surrogate-pair
        // branches).
        let mut big_ascii = "a".repeat(1 << 20);
        let orig_cap = big_ascii.capacity();
        let right = utf16_split_in_place(&mut big_ascii, 1);
        assert_eq!(big_ascii, "a");
        assert_eq!(right.len(), (1 << 20) - 1);
        assert!(big_ascii.capacity() < orig_cap / 2);

        let mut big_surrogate = format!("a😀{}", "b".repeat(1 << 20));
        let orig_surrogate_cap = big_surrogate.capacity();
        let right = utf16_split_in_place(&mut big_surrogate, 2);
        assert_eq!(big_surrogate, "a\u{FFFD}");
        assert!(right.starts_with("\u{FFFD}b"));
        assert!(big_surrogate.capacity() < orig_surrogate_cap / 2);
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
        len: u64,
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
            |id| {
                nodes
                    .iter()
                    .find(|node| {
                        node.id.client == id.client && node.id.clock <= id.clock && id.clock < node.id.clock + node.len
                    })
                    .map(|node| node.id)
            },
        )
        .unwrap()
    }

    fn item(client: u64, clock: u64, origin_left: Option<Id>, origin_right: Option<Id>) -> ConflictItem {
        ConflictItem {
            id: Id::new(client, clock),
            origin_left,
            origin_right,
        }
    }

    /// The scan as it was before its candidates went into [Scanned]: two
    /// hash sets, filled before the decision and emptied when a candidate is
    /// taken.
    fn legacy_conflict_left(
        this: ConflictItem,
        mut left: Option<usize>,
        mut conflict: Option<usize>,
        right: Option<usize>,
        nodes: &[ConflictNode],
    ) -> Option<usize> {
        use std::collections::HashSet;
        let owner_of = |id: Id| {
            nodes
                .iter()
                .find(|node| {
                    node.id.client == id.client && node.id.clock <= id.clock && id.clock < node.id.clock + node.len
                })
                .map(|node| node.id)
        };
        let mut conflicting = HashSet::new();
        let mut before_origin = HashSet::new();
        while let Some(current) = conflict {
            if right == Some(current) {
                break;
            }
            let Some(candidate) = nodes.get(current) else {
                break;
            };
            before_origin.insert(candidate.id);
            conflicting.insert(candidate.id);
            let take = match decide_conflict_step(
                this.id.client,
                this.origin_left.map(core_id),
                this.origin_right.map(core_id),
                candidate.id.client,
                candidate.origin_left.map(core_id),
                candidate.origin_right.map(core_id),
            ) {
                ConflictDecision::Step(ScanStep::Stop) => break,
                ConflictDecision::Step(ScanStep::Take) => true,
                ConflictDecision::Step(ScanStep::Skip) => false,
                ConflictDecision::Owner(candidate_left) => {
                    let Some(owner) = owner_of(Id::new(candidate_left.client, candidate_left.clock)) else {
                        break;
                    };
                    let in_before = before_origin.contains(&owner);
                    match decide_owner_step(in_before, in_before && conflicting.contains(&owner)) {
                        ScanStep::Stop => break,
                        ScanStep::Take => true,
                        ScanStep::Skip => false,
                    }
                }
            };
            if take {
                left = Some(current);
                conflicting.clear();
            }
            conflict = candidate.right;
        }
        left
    }

    #[test]
    fn conflict_scan_agrees_with_the_scan_on_hash_sets() {
        // chains of candidates with origins all over the place: before the
        // chain, inside it (also inside a struct, and on the candidate
        // itself), after it, and nowhere. An origin among the last
        // candidates is found by hand, one further back through the table
        // of the list.
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut below = move |n: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % n
        };
        let rounds = if cfg!(miri) { 60 } else { 6_000 };
        let mut asked_the_table = 0;
        for round in 0..rounds {
            let len = match round % 4 {
                0 => 1 + below(6),
                1 => 10 + below(12),
                2 => 17 + below(40),
                _ => 1 + below(120),
            } as usize;
            let clients = 1 + below(5);
            let mut clocks = [0u64; 8];
            let mut nodes: Vec<ConflictNode> = Vec::with_capacity(len);
            for index in 0..len {
                let client = 1 + below(clients);
                let node_len = 1 + below(3);
                let clock = clocks[client as usize];
                clocks[client as usize] += node_len;
                let origin = |below: &mut dyn FnMut(u64) -> u64, nodes: &[ConflictNode]| match below(10) {
                    0 => None,
                    // the struct before the chain
                    1 | 2 => Some(Id::new(9, 0)),
                    // a struct that is nowhere
                    3 => Some(Id::new(8, 77)),
                    // itself or a later clock of its client
                    4 => Some(Id::new(client, clock + below(4))),
                    // a clock of an earlier candidate, maybe inside it
                    _ if !nodes.is_empty() => {
                        let other = &nodes[below(nodes.len() as u64) as usize];
                        Some(Id::new(other.id.client, other.id.clock + below(other.len)))
                    }
                    _ => Some(Id::new(9, 0)),
                };
                let origin_left = origin(&mut below, &nodes);
                let origin_right = origin(&mut below, &nodes);
                nodes.push(ConflictNode {
                    id: Id::new(client, clock),
                    len: node_len,
                    origin_left,
                    origin_right,
                    right: (index + 1 < len).then_some(index + 1),
                });
            }
            for this_client in [0, 2, 3, 7] {
                for origin_left in [None, Some(Id::new(9, 0)), Some(nodes[0].id)] {
                    for origin_right in [None, Some(Id::new(9, 0)), Some(nodes[len / 2].id)] {
                        let right = match below(4) {
                            0 => Some(below(len as u64) as usize),
                            _ => None,
                        };
                        let this = item(this_client, 1_000, origin_left, origin_right);
                        let expected = legacy_conflict_left(this, None, Some(0), right, &nodes);
                        assert_eq!(
                            conflict_left(this, None, Some(0), right, &nodes),
                            expected,
                            "round {round}, client {this_client}, origins {origin_left:?} {origin_right:?}, right \
                             {right:?}, nodes {nodes:?}"
                        );
                    }
                }
            }
            // how often a scan has to look further back than by hand
            let mut scanned = Scanned::default();
            for node in &nodes {
                assert!(scanned.push(core_id(node.id)));
            }
            // (the first candidate is where a list that answered nothing
            // yet looks first)
            assert_eq!(scanned.find(core_id(nodes[0].id)), (true, true));
            assert!(!scanned.order.is_indexed());
            assert_eq!(scanned.find(core_id(nodes[1.min(len - 1)].id)), (true, true));
            asked_the_table += usize::from(scanned.order.is_indexed());
        }
        assert!(asked_the_table * 4 > rounds, "long chains are part of the test");
    }

    #[test]
    fn scanned_candidates_answer_alike_by_hand_and_through_the_table() {
        use y_octo_core::id_order::RECENT;
        let id = |clock: u64| IdCore {
            client: clock % 3,
            clock,
        };
        for count in [0usize, 1, 5, RECENT, RECENT + 1, 100] {
            for take_at in [None, Some(0), Some(count / 2), Some(count.saturating_sub(1))] {
                let mut scanned = Scanned::default();
                let mut conflicting_from = 0;
                for at in 0..count {
                    assert!(scanned.push(id(at as u64)));
                    if take_at == Some(at) {
                        scanned.take();
                        conflicting_from = at + 1;
                    }
                }
                // the first question for a candidate far back makes the table
                for round in 0..2 {
                    for at in 0..count + 3 {
                        let expected = (at < count, at < count && at >= conflicting_from);
                        assert_eq!(
                            scanned.find(id(at as u64)),
                            expected,
                            "{count} candidates, round {round}"
                        );
                    }
                    // one more candidate in the second round
                    assert_eq!(scanned.order.is_indexed(), count + round as usize > RECENT);
                    // and the scan goes on
                    assert!(scanned.push(id(1_000 + round)));
                    assert_eq!(scanned.find(id(1_000 + round)), (true, true));
                    scanned.take();
                    assert_eq!(scanned.find(id(1_000 + round)), (true, false));
                    conflicting_from = usize::MAX;
                }
            }
        }
    }

    #[test]
    fn a_scan_whose_list_is_full_ends_with_an_error() {
        // five concurrent inserts at one place by smaller clients: a scan
        // for a sixth walks all of them
        let nodes: Vec<ConflictNode> = (0..5)
            .map(|at| ConflictNode {
                id: Id::new(at as u64 + 1, 0),
                len: 1,
                origin_left: None,
                origin_right: None,
                right: (at + 1 < 5).then_some(at + 1),
            })
            .collect();
        let scan = |limit: Option<usize>, right: Option<usize>| {
            scan_conflict_left(
                ScanLimit { candidates: limit },
                item(9, 0, None, None),
                None,
                Some(0),
                right,
                |&index| {
                    nodes.get(index).map(|node| ConflictItem {
                        id: node.id,
                        origin_left: node.origin_left,
                        origin_right: node.origin_right,
                    })
                },
                |&index| nodes.get(index).and_then(|node| node.right),
                |_| None,
            )
        };
        assert_eq!(scan(None, None), Ok(Some(4)));
        // a list that takes every candidate the scan meets changes nothing
        assert_eq!(scan(Some(5), None), Ok(Some(4)));
        assert_eq!(scan(Some(3), Some(3)), Ok(Some(2)));
        // one candidate short: an error, not a neighbour found so far
        for limit in 0..5 {
            assert_eq!(
                scan(Some(limit), None),
                Err(JwstCodecError::IncompleteDocument(
                    "the conflict scan holds too many candidates".into()
                )),
                "a list of {limit} candidates"
            );
        }
        // the list is not asked past the right neighbour
        assert_eq!(scan(Some(0), Some(0)), Ok(None));
    }

    #[test]
    fn conflict_left_decisions() {
        // concurrent inserts at the same position: lower client id goes left
        let concurrent = |this_client: u64, other_client: u64| {
            let nodes = [ConflictNode {
                id: Id::new(other_client, 0),
                len: 1,
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
            len: 1,
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
                len: 2,
                origin_left: Some(Id::new(8, 0)),
                origin_right: None,
                right: Some(1),
            },
            ConflictNode {
                id: Id::new(2, 0),
                len: 1,
                origin_left: Some(Id::new(8, 0)),
                origin_right: None,
                right: Some(2),
            },
            ConflictNode {
                id: Id::new(3, 0),
                len: 1,
                origin_left: Some(Id::new(1, 1)),
                origin_right: None,
                right: Some(3),
            },
            ConflictNode {
                id: Id::new(4, 0),
                len: 1,
                origin_left: None,
                origin_right: None,
                right: Some(4),
            },
            ConflictNode {
                id: Id::new(5, 0),
                len: 1,
                origin_left: Some(Id::new(8, 0)),
                origin_right: None,
                right: None,
            },
        ];
        assert_eq!(
            conflict_left(item(9, 0, Some(Id::new(8, 0)), None), None, Some(0), None, &nodes),
            Some(2)
        );

        // a conflict chain that reaches the right neighbor keeps the current
        // left
        let nodes = [ConflictNode {
            id: Id::new(2, 0),
            len: 1,
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
