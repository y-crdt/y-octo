use std::{collections::VecDeque, mem, ops::Range};

/// A set of `u64` clocks kept as ranges: sorted by start, disjoint,
/// non-adjacent and non-empty. The representation is private so every value
/// keeps that form, whatever order the ranges were added in; equal sets are
/// equal values.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OrderRange(OrderRangeInner);

/// Invariant: `Range` is non-empty or exactly `0..0` (the empty set);
/// `Fragment` holds at least two non-empty ranges with
/// `dq[i].end < dq[i + 1].start`.
#[derive(Debug, PartialEq, Eq, Clone)]
enum OrderRangeInner {
    Range(Range<u64>),
    Fragment(VecDeque<Range<u64>>),
}

impl Default for OrderRange {
    fn default() -> Self {
        Self(OrderRangeInner::Range(0..0))
    }
}

impl From<Range<u64>> for OrderRange {
    fn from(range: Range<u64>) -> Self {
        if range.is_empty() {
            Self::default()
        } else {
            Self(OrderRangeInner::Range(range))
        }
    }
}

/// The ranges may come in any order, overlap, touch or be empty.
impl From<Vec<Range<u64>>> for OrderRange {
    fn from(value: Vec<Range<u64>>) -> Self {
        Self::from_vec(canonical_vec(value))
    }
}

/// The ranges may come in any order, overlap, touch or be empty.
impl From<VecDeque<Range<u64>>> for OrderRange {
    fn from(value: VecDeque<Range<u64>>) -> Self {
        Self::from_vec(canonical_vec(value))
    }
}

/// The ranges may come in any order, overlap, touch or be empty.
impl FromIterator<Range<u64>> for OrderRange {
    fn from_iter<T: IntoIterator<Item = Range<u64>>>(iter: T) -> Self {
        Self::from_vec(canonical_vec(iter))
    }
}

/// Sorts `ranges` by `(start, end)`, drops empty ones and merges every
/// overlapping or touching pair, mirroring yjs' `sortAndMergeDeleteSet`.
fn canonical_vec(ranges: impl IntoIterator<Item = Range<u64>>) -> Vec<Range<u64>> {
    let mut ranges: Vec<Range<u64>> = ranges.into_iter().filter(|r| !r.is_empty()).collect();
    ranges.sort_unstable_by(|a, b| a.start.cmp(&b.start).then(a.end.cmp(&b.end)));

    let mut merged: Vec<Range<u64>> = Vec::with_capacity(ranges.len());
    for range in ranges {
        match merged.last_mut() {
            // ranges are sorted by start, so continuity only depends on the
            // end
            Some(last) if last.end >= range.start => {
                last.end = last.end.max(range.end);
            }
            _ => merged.push(range),
        }
    }
    merged
}

/// Whether `ranges` are non-empty, sorted, disjoint and non-adjacent.
fn is_canonical<'a>(ranges: impl IntoIterator<Item = &'a Range<u64>>) -> bool {
    let mut last_end = None;
    for range in ranges {
        if range.is_empty() || last_end.is_some_and(|end| end >= range.start) {
            return false;
        }
        last_end = Some(range.end);
    }
    true
}

#[inline]
fn is_continuous_range(lhs: &Range<u64>, rhs: &Range<u64>) -> bool {
    lhs.end >= rhs.start && lhs.start <= rhs.end
}

impl OrderRange {
    /// The empty set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Wraps ranges that are already canonical: sorted by start, disjoint,
    /// non-adjacent and non-empty. Skips the sort of the `From` impls.
    pub(crate) fn from_sorted_disjoint(ranges: VecDeque<Range<u64>>) -> Self {
        debug_assert!(
            is_canonical(&ranges),
            "ranges not sorted, disjoint and non-empty: {ranges:?}"
        );
        Self::from_canonical(ranges)
    }

    fn from_vec(ranges: Vec<Range<u64>>) -> Self {
        Self::from_canonical(ranges.into())
    }

    fn from_canonical(mut ranges: VecDeque<Range<u64>>) -> Self {
        match ranges.len() {
            0 => Self::default(),
            1 => Self(OrderRangeInner::Range(ranges.pop_front().expect("one range"))),
            _ => Self(OrderRangeInner::Fragment(ranges)),
        }
    }

    /// Number of disjoint ranges, 0 for the empty set.
    pub fn ranges_len(&self) -> usize {
        match &self.0 {
            OrderRangeInner::Range(range) => usize::from(!range.is_empty()),
            OrderRangeInner::Fragment(ranges) => ranges.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        match &self.0 {
            OrderRangeInner::Range(range) => range.is_empty(),
            // at least two non-empty ranges
            OrderRangeInner::Fragment(_) => false,
        }
    }

    pub fn contains(&self, clock: u64) -> bool {
        match &self.0 {
            OrderRangeInner::Range(range) => range.contains(&clock),
            OrderRangeInner::Fragment(ranges) => {
                // first range that ends after `clock`
                let idx = ranges.partition_point(|r| r.end <= clock);
                ranges.get(idx).is_some_and(|r| r.start <= clock)
            }
        }
    }

    fn check_range_covered(old_vec: &[Range<u64>], new_vec: &[Range<u64>]) -> bool {
        let mut old_iter = old_vec.iter();
        let mut next_old = old_iter.next();
        let mut new_iter = new_vec.iter().peekable();
        let mut next_new = new_iter.next();
        'new_loop: while let Some(new_range) = next_new {
            while let Some(old_range) = next_old {
                if old_range.start < new_range.start || old_range.end > new_range.end {
                    if new_iter.peek().is_some() {
                        next_new = new_iter.next();
                        continue 'new_loop;
                    } else {
                        return false;
                    }
                }
                next_old = old_iter.next();
                if let Some(next_old) = &next_old
                    && next_old.start > new_range.end
                {
                    continue;
                }
            }
            next_new = new_iter.next();
        }
        true
    }

    /// diff_range returns the difference between the old range and the new
    /// range. current range must be covered by the new range
    pub fn diff_range(&self, new_range: &OrderRange) -> Vec<Range<u64>> {
        let old_vec = self.canonical_ranges();
        let new_vec = new_range.canonical_ranges();

        if !Self::check_range_covered(&old_vec, &new_vec) {
            return Vec::new();
        }

        let mut diffs = Vec::new();
        let mut old_idx = 0;

        for new_range in &new_vec {
            let mut overlap_ranges = Vec::new();
            while old_idx < old_vec.len() && old_vec[old_idx].start <= new_range.end {
                overlap_ranges.push(old_vec[old_idx].clone());
                old_idx += 1;
            }

            if overlap_ranges.is_empty() {
                diffs.push(new_range.clone());
            } else {
                let mut last_end = overlap_ranges[0].start;
                if last_end > new_range.start {
                    diffs.push(new_range.start..last_end);
                }

                for overlap in &overlap_ranges {
                    if overlap.start > last_end {
                        diffs.push(last_end..overlap.start);
                    }
                    last_end = overlap.end;
                }

                if new_range.end > last_end {
                    diffs.push(last_end..new_range.end);
                }
            }
        }

        diffs
    }

    /// Push new range to current one.
    /// Range will be merged if overlap exists or turned into fragment if it's
    /// not continuous.
    pub fn push(&mut self, range: Range<u64>) {
        // an empty range covers nothing
        if range.is_empty() {
            return;
        }
        match &mut self.0 {
            OrderRangeInner::Range(r) => {
                if r.is_empty() {
                    *r = range;
                } else if is_continuous_range(r, &range) {
                    r.end = r.end.max(range.end);
                    r.start = r.start.min(range.start);
                } else {
                    let r = r.clone();
                    self.0 = OrderRangeInner::Fragment(if r.start < range.start {
                        VecDeque::from([r, range])
                    } else {
                        VecDeque::from([range, r])
                    });
                }
            }
            OrderRangeInner::Fragment(ranges) => {
                Self::push_inner(ranges, range);
                self.make_single();
            }
        }
    }

    /// Removes and returns the first range.
    pub fn pop(&mut self) -> Option<Range<u64>> {
        match &mut self.0 {
            OrderRangeInner::Range(range) => (!range.is_empty()).then(|| mem::replace(range, 0..0)),
            OrderRangeInner::Fragment(list) => {
                let first = list.pop_front();
                self.make_single();
                first
            }
        }
    }

    pub fn merge(&mut self, other: Self) {
        self.extend(&other);
    }

    /// Folds a `Fragment` left with fewer than two ranges back into a `Range`.
    fn make_single(&mut self) {
        if let OrderRangeInner::Fragment(ranges) = &mut self.0
            && ranges.len() < 2
        {
            self.0 = OrderRangeInner::Range(ranges.pop_front().unwrap_or(0..0));
        }
    }

    /// The ranges in order. Kept for the encoder (yjs' `sortAndMergeDeleteSet`
    /// form), which the representation already is.
    pub(crate) fn canonical_ranges(&self) -> Vec<Range<u64>> {
        let ranges: Vec<Range<u64>> = self.into_iter().collect();
        debug_assert!(is_canonical(&ranges), "OrderRange not canonical: {self:?}");
        ranges
    }

    /// Inserts `range` into a sorted list of disjoint, non-adjacent ranges and
    /// merges every range it overlaps or touches, keeping the list sorted,
    /// disjoint and non-adjacent.
    fn push_inner(list: &mut VecDeque<Range<u64>>, range: Range<u64>) {
        if range.is_empty() {
            return;
        }
        // first range that ends at or after the new start
        let first = list.partition_point(|r| r.end < range.start);
        // first range that starts after the new end
        let last = list.partition_point(|r| r.start <= range.end);

        if first == last {
            list.insert(first, range);
        } else {
            let merged = range.start.min(list[first].start)..range.end.max(list[last - 1].end);
            list[first] = merged;
            list.drain(first + 1..last);
        }
    }
}

impl<'a> IntoIterator for &'a OrderRange {
    type Item = Range<u64>;
    type IntoIter = OrderRangeIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        OrderRangeIter { range: self, idx: 0 }
    }
}

impl Extend<Range<u64>> for OrderRange {
    fn extend<T: IntoIterator<Item = Range<u64>>>(&mut self, other: T) {
        // one push at a time: `self` stays canonical and keeps its ranges
        // even if `other` panics halfway
        for range in other {
            self.push(range);
        }
    }
}

/// Iterates over the ranges in order; the empty set yields nothing.
pub struct OrderRangeIter<'a> {
    range: &'a OrderRange,
    idx: usize,
}

impl Iterator for OrderRangeIter<'_> {
    type Item = Range<u64>;

    fn next(&mut self) -> Option<Self::Item> {
        let range = match &self.range.0 {
            OrderRangeInner::Range(range) => (self.idx == 0 && !range.is_empty()).then(|| range.clone()),
            OrderRangeInner::Fragment(ranges) => ranges.get(self.idx).cloned(),
        };
        self.idx += usize::from(range.is_some());
        range
    }
}

#[cfg(test)]
#[allow(clippy::single_range_in_vec_init)]
mod tests {
    use std::collections::VecDeque;

    use super::{OrderRange, OrderRangeInner};

    fn assert_canonical(range: &OrderRange) {
        match &range.0 {
            OrderRangeInner::Range(r) => assert!(!r.is_empty() || *r == (0..0), "{range:?}"),
            OrderRangeInner::Fragment(ranges) => {
                assert!(ranges.len() >= 2, "short fragment {range:?}");
                assert!(super::is_canonical(ranges), "{range:?}");
            }
        }
    }

    #[test]
    fn test_range_push() {
        let mut range: OrderRange = (0..10).into();

        range.push(5..15);
        assert_eq!(range, OrderRange::from(0..15));

        // turn to fragment
        range.push(20..30);
        assert_eq!(range, OrderRange::from(vec![(0..15), (20..30)]));

        // auto merge
        range.push(15..16);
        assert_eq!(range, OrderRange::from(vec![(0..16), (20..30)]));

        // squash
        range.push(16..20);
        assert_eq!(range, OrderRange::from(0..30));
        assert_canonical(&range);

        let mut range = OrderRange::new();
        range.push(3..4);
        assert_eq!(range, OrderRange::from(3..4));
        range.push(0..1);
        assert_eq!(range, OrderRange::from(vec![0..1, 3..4]));
        assert_canonical(&range);
    }

    #[test]
    fn test_range_pop() {
        let mut range: OrderRange = vec![(0..10), (20..30)].into();
        assert_eq!(range.pop(), Some(0..10));
        // folds back to a single range
        assert_eq!(range.0, OrderRangeInner::Range(20..30));
        assert_eq!(range.pop(), Some(20..30));
        assert!(range.is_empty());
        assert_eq!(range, OrderRange::new());

        let mut range: OrderRange = vec![(0..10), (20..30), (40..50)].into();
        assert_eq!(range.pop(), Some(0..10));
        assert_eq!(range, OrderRange::from(vec![(20..30), (40..50)]));
        assert_canonical(&range);

        let mut range: OrderRange = (0..10).into();
        assert_eq!(range.pop(), Some(0..10));
        assert!(range.is_empty());
        assert_eq!(range.pop(), None);
        assert_eq!(OrderRange::new().pop(), None);
    }

    #[test]
    fn test_range_from_any_order_is_canonical() {
        let expected = OrderRange(OrderRangeInner::Fragment(VecDeque::from([2..4, 6..8, 10..12])));
        assert_eq!(OrderRange::from(vec![10..12, 2..4, 6..8]), expected);
        assert_eq!(OrderRange::from(VecDeque::from([6..8, 10..12, 2..4])), expected);
        assert_eq!([2..4, 10..12, 6..8].into_iter().collect::<OrderRange>(), expected);

        // overlapping, touching and empty ranges fold away
        let range = OrderRange::from(vec![10..12, 0..0, 3..6, 0..4, 12..14, 20..20]);
        assert_eq!(
            range,
            OrderRange(OrderRangeInner::Fragment(VecDeque::from([0..6, 10..14])))
        );
        assert_canonical(&range);
        assert_eq!(OrderRange::from(vec![0..10, 10..20, 20..30]), OrderRange::from(0..30));
        assert_eq!(OrderRange::from(vec![20..30, 0..10, 10..20]), OrderRange::from(0..30));
        assert_eq!(OrderRange::from(vec![5..9, 0..5]).0, OrderRangeInner::Range(0..9));
        assert_eq!(OrderRange::from(vec![5..9]).0, OrderRangeInner::Range(5..9));

        // nothing left
        for empty in [
            OrderRange::from(vec![3..3, 9..9]),
            OrderRange::from(Vec::new()),
            OrderRange::from(VecDeque::new()),
            OrderRange::from(7..7),
            std::iter::empty().collect(),
            OrderRange::new(),
        ] {
            assert_eq!(empty.0, OrderRangeInner::Range(0..0));
            assert!(empty.is_empty());
            assert_eq!(empty.ranges_len(), 0);
            assert_eq!(empty.into_iter().count(), 0);
        }
    }

    #[test]
    fn test_ranges_len() {
        assert_eq!(OrderRange::new().ranges_len(), 0);
        assert_eq!(OrderRange::from(1..2).ranges_len(), 1);
        assert_eq!(OrderRange::from(vec![1..2, 2..3]).ranges_len(), 1);
        assert_eq!(OrderRange::from(vec![1..2, 3..4, 8..9]).ranges_len(), 3);
    }

    #[test]
    fn test_range_contains() {
        let range = OrderRange::from(vec![10..12, 2..4, 6..8]);
        let inside = [2, 3, 6, 7, 10, 11];
        for clock in 0..14 {
            assert_eq!(range.contains(clock), inside.contains(&clock), "clock {clock}");
        }
        assert!(!OrderRange::new().contains(0));
        assert!(OrderRange::from(0..1).contains(0));
        assert!(!OrderRange::from(0..1).contains(1));
    }

    #[test]
    fn test_range_push_after_any_order_from() {
        // pushes after building from unsorted ranges keep every clock,
        // whatever order the ranges came in
        let ranges = [10..12, 2..4, 6..8, 14..15, 0..1];
        let mut rev = ranges.to_vec();
        rev.reverse();
        let orders = [ranges.to_vec(), rev, vec![6..8, 14..15, 0..1, 10..12, 2..4]];

        for order in orders {
            let mut range = OrderRange::from(order.clone());
            assert_canonical(&range);
            range.push(4..5);
            range.push(12..13);
            range.extend([8..9, 20..22, 1..2]);
            assert_canonical(&range);
            assert_eq!(
                range,
                OrderRange::from(vec![0..5, 6..9, 10..13, 14..15, 20..22]),
                "{order:?}"
            );
            assert_eq!(range.ranges_len(), 5);

            let mut range = OrderRange::from(VecDeque::from(order.clone()));
            range.extend([0..30]);
            assert_eq!(range.0, OrderRangeInner::Range(0..30), "{order:?}");
        }
    }

    #[test]
    fn test_range_covered() {
        assert!(!OrderRange::check_range_covered(&[0..1], &[2..3]));
        assert!(OrderRange::check_range_covered(&[0..1], &[0..3]));
        assert!(!OrderRange::check_range_covered(&[0..1], &[1..3]));
        assert!(OrderRange::check_range_covered(&[0..1], &[0..3]));
        assert!(OrderRange::check_range_covered(&[1..2], &[0..3]));
        assert!(OrderRange::check_range_covered(&[1..2, 2..3], &[0..3]));
        assert!(!OrderRange::check_range_covered(&[1..2, 2..3, 3..4], &[0..3]));
        assert!(OrderRange::check_range_covered(&[0..1, 2..3], &[0..2, 2..4]));
        assert!(OrderRange::check_range_covered(&[0..1, 2..3, 3..4], &[0..2, 2..4]),);
    }

    #[test]
    fn test_range_diff() {
        {
            let old = OrderRange::from(0..1);
            let new = OrderRange::from(2..3);
            let ranges = old.diff_range(&new);
            assert_eq!(ranges, vec![]);
        }

        {
            let old = OrderRange::from(0..10);
            let new = OrderRange::from(0..11);
            let ranges = old.diff_range(&new);
            assert_eq!(ranges, vec![(10..11)]);
        }

        {
            let old: OrderRange = vec![(0..10), (20..30)].into();
            let new: OrderRange = vec![(0..15), (20..30)].into();
            let ranges = old.diff_range(&new);
            assert_eq!(ranges, vec![(10..15)]);
        }

        {
            let old: OrderRange = vec![(0..3), (5..7), (8..10), (16..18), (21..23)].into();
            let new: OrderRange = vec![(0..12), (15..23)].into();
            let ranges = old.diff_range(&new);
            assert_eq!(ranges, vec![(3..5), (7..8), (10..12), (15..16), (18..21)]);
        }

        {
            let old: OrderRange = vec![(1..6), (8..12)].into();
            let new: OrderRange = vec![(0..12), (15..23), (24..28)].into();
            let ranges = old.diff_range(&new);
            assert_eq!(ranges, vec![(0..1), (6..8), (15..23), (24..28)]);
        }

        {
            // built out of order, diffed like the sorted form
            let old: OrderRange = vec![(20..30), (0..10)].into();
            let new: OrderRange = vec![(20..35), (0..15)].into();
            assert_eq!(old.diff_range(&new), vec![(10..15), (30..35)]);
        }

        {
            // the empty set
            let new: OrderRange = vec![(0..2), (4..6)].into();
            assert_eq!(OrderRange::new().diff_range(&new), vec![(0..2), (4..6)]);
            assert_eq!(new.diff_range(&OrderRange::new()), vec![]);
            assert_eq!(OrderRange::new().diff_range(&OrderRange::new()), vec![]);
        }
    }

    #[test]
    fn test_range_extend() {
        let mut range: OrderRange = (0..10).into();
        range.merge((20..30).into());
        assert_eq!(range, OrderRange::from(vec![(0..10), (20..30)]));

        let mut range: OrderRange = (0..10).into();
        range.merge(vec![(10..15), (20..30)].into());
        assert_eq!(range, OrderRange::from(vec![(0..15), (20..30)]));

        let mut range: OrderRange = vec![(0..10), (20..30)].into();
        range.merge((10..20).into());
        assert_eq!(range, OrderRange::from(0..30));

        let mut range: OrderRange = vec![(0..10), (20..30)].into();
        range.merge(vec![(10..20), (30..40)].into());
        assert_eq!(range, OrderRange::from(0..40));

        let mut range = OrderRange::new();
        range.merge(OrderRange::new());
        assert_eq!(range, OrderRange::new());
        range.extend([4..4]);
        assert_eq!(range, OrderRange::new());
        range.merge(vec![(5..6), (1..2)].into());
        assert_eq!(range, OrderRange::from(vec![(1..2), (5..6)]));
        assert_canonical(&range);
    }

    #[test]
    fn test_range_extend_keeps_ranges_when_iterator_panics() {
        let mut range: OrderRange = vec![(0..5), (10..15)].into();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            range.extend(
                [20..25, 3..12]
                    .into_iter()
                    .chain(std::iter::from_fn(|| -> Option<_> { panic!("iterator failed") })),
            );
        }));
        assert!(result.is_err());
        assert_eq!(range, OrderRange::from(vec![(0..15), (20..25)]));
        assert_canonical(&range);
    }

    #[test]
    fn iter() {
        let range: OrderRange = vec![(0..10), (20..30)].into();

        assert_eq!(range.into_iter().collect::<Vec<_>>(), vec![(0..10), (20..30)]);

        let range: OrderRange = OrderRange::from(0..10);

        assert_eq!(range.into_iter().collect::<Vec<_>>(), vec![(0..10)]);
    }

    #[test]
    fn test_from_sorted_disjoint() {
        assert_eq!(OrderRange::from_sorted_disjoint(VecDeque::new()), OrderRange::new());
        assert_eq!(
            OrderRange::from_sorted_disjoint(VecDeque::from([1..2])).0,
            OrderRangeInner::Range(1..2)
        );
        assert_eq!(
            OrderRange::from_sorted_disjoint(VecDeque::from([1..2, 3..4])),
            OrderRange::from(vec![3..4, 1..2])
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "not sorted")]
    fn test_from_sorted_disjoint_checks_order() {
        let _ = OrderRange::from_sorted_disjoint(VecDeque::from([3..4, 1..2]));
    }

    #[test]
    fn test_range_push_spanning_many_fragments() {
        let mut range: OrderRange = vec![(0..5), (10..15), (20..25), (30..35), (40..45)].into();
        range.push(0..50);
        assert_eq!(range, OrderRange::from(0..50));

        let mut range: OrderRange = vec![(0..5), (10..15), (20..25), (30..35), (40..45)].into();
        range.push(12..32);
        assert_eq!(range, OrderRange::from(vec![(0..5), (10..35), (40..45)]));

        // touching both neighbours at once
        let mut range: OrderRange = vec![(0..5), (10..15)].into();
        range.push(5..10);
        assert_eq!(range, OrderRange::from(0..15));

        let mut range: OrderRange = vec![(0..5), (10..15), (20..25)].into();
        range.extend([3..22, 30..31]);
        assert_eq!(range, OrderRange::from(vec![(0..25), (30..31)]));
    }

    #[test]
    fn test_range_push_ignores_empty() {
        let mut range: OrderRange = vec![(0..5), (10..15)].into();
        range.push(7..7);
        range.extend([8..8, 20..20]);
        assert_eq!(range, OrderRange::from(vec![(0..5), (10..15)]));

        let mut range: OrderRange = (0..5).into();
        range.push(9..9);
        assert_eq!(range, OrderRange::from(0..5));
    }

    #[test]
    fn test_range_push_keeps_fragments_canonical() {
        // deterministic pseudo random pushes and pops, checked against a
        // bitmap
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        // Miri runs a few rounds; the rest only repeat the same code paths
        let rounds = if cfg!(miri) { 8 } else { 200 };
        for _ in 0..rounds {
            let mut range = OrderRange::default();
            let mut covered = [false; 256];
            for _ in 0..40 {
                let start = next() % 250;
                let len = next() % 12;
                let end = (start + len).min(256);
                match next() % 8 {
                    0 => {
                        if let Some(popped) = range.pop() {
                            covered[popped.start as usize..popped.end as usize]
                                .iter_mut()
                                .for_each(|c| *c = false);
                        }
                        assert_canonical(&range);
                        continue;
                    }
                    1..=4 => range.push(start..end),
                    _ => range.extend([start..end]),
                }
                covered[start as usize..end as usize].iter_mut().for_each(|c| *c = true);
                assert_canonical(&range);
            }
            for (clock, covered) in covered.iter().enumerate() {
                assert_eq!(range.contains(clock as u64), *covered, "clock {clock} in {range:?}");
            }
            assert_eq!(
                range,
                OrderRange::from(range.canonical_ranges()),
                "rebuilt from its ranges"
            );
        }
    }
}
