use std::{collections::VecDeque, fmt, mem, ops::Range};

use y_octo_core::order_range::{ClockRange, OrderRange as CoreRange};

/// A set of clocks, stored as sorted, disjoint, non-adjacent half-open ranges.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct OrderRange(CoreRange);

const _: () = assert!(size_of::<OrderRange>() <= 32);

fn clock_range(r: Range<u64>) -> ClockRange {
    ClockRange {
        start: r.start,
        end: r.end,
    }
}

// Numeric order of this key is the core's lexicographic (start, end) order.
fn sort_if_needed(ranges: &mut [ClockRange], sorted: bool) {
    if !sorted {
        let key = |r: &ClockRange| (u128::from(r.start) << 64) | u128::from(r.end);
        ranges.sort_unstable_by_key(key);
    }
}

fn ordered_pair(a: ClockRange, b: ClockRange) -> bool {
    (a.start, a.end) <= (b.start, b.end)
}

fn prepare_ranges(ranges: &mut Vec<ClockRange>) {
    ranges.retain(|r| r.start < r.end);
    let sorted = ranges.is_sorted_by(|a, b| ordered_pair(*a, *b));
    sort_if_needed(ranges, sorted);
}

// Keep the canonical scan independent of the sparse-input filtering loop.
#[inline(never)]
fn from_converted(ranges: Vec<ClockRange>, hint: usize) -> OrderRange {
    match CoreRange::try_from_ordered_with_capacity(ranges, hint) {
        Ok(set) => OrderRange(set),
        Err(mut ranges) => {
            prepare_ranges(&mut ranges);
            OrderRange(CoreRange::from_vec_with_capacity(ranges, hint))
        }
    }
}

fn to_range(r: ClockRange) -> Range<u64> {
    r.start..r.end
}

// Preserve the public Debug representation independently of the physical ring.
impl fmt::Debug for OrderRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Repr<'a>(&'a OrderRange);
        struct Fragment<'a>(&'a OrderRange);

        impl fmt::Debug for Fragment<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_list().entries(self.0).finish()
            }
        }

        impl fmt::Debug for Repr<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                if self.0.ranges_len() > 1 {
                    f.debug_tuple("Fragment").field(&Fragment(self.0)).finish()
                } else {
                    let range = self.0.0.first().map_or(0..0, to_range);
                    f.debug_tuple("Range").field(&range).finish()
                }
            }
        }

        f.debug_tuple("OrderRange").field(&Repr(self)).finish()
    }
}

impl From<Range<u64>> for OrderRange {
    fn from(range: Range<u64>) -> Self {
        Self(CoreRange::from_range(range.start, range.end))
    }
}

impl From<Vec<Range<u64>>> for OrderRange {
    fn from(ranges: Vec<Range<u64>>) -> Self {
        let ranges = match ranges.as_slice() {
            [] => return Self::new(),
            [r] => return Self::from(r.clone()),
            [a, b, ..] if !a.is_empty() && !b.is_empty() => ranges,
            _ => {
                let live: Vec<_> = ranges.into_iter().filter(|r| !r.is_empty()).collect();
                match live.as_slice() {
                    [] => return Self::new(),
                    [r] => return Self::from(r.clone()),
                    _ => live,
                }
            }
        };
        let hint = ranges.capacity();
        let converted: Vec<_> = ranges.into_iter().map(clock_range).collect();
        let hint = hint.min(converted.capacity());
        from_converted(converted, hint)
    }
}

impl From<VecDeque<Range<u64>>> for OrderRange {
    fn from(ranges: VecDeque<Range<u64>>) -> Self {
        Self::from(Vec::from(ranges))
    }
}

impl FromIterator<Range<u64>> for OrderRange {
    fn from_iter<T: IntoIterator<Item = Range<u64>>>(iter: T) -> Self {
        let converted: Vec<_> = iter.into_iter().filter(|r| !r.is_empty()).map(clock_range).collect();
        let hint = converted.capacity();
        from_converted(converted, hint)
    }
}

/// Commit every range yielded before an iterator panics.
struct MergeOnDrop<'a> {
    target: &'a mut OrderRange,
    incoming: Vec<ClockRange>,
    sorted: bool,
    limit: usize,
}

impl Drop for MergeOnDrop<'_> {
    fn drop(&mut self) {
        sort_if_needed(&mut self.incoming, self.sorted);
        let hint = self.incoming.capacity();
        let result = self
            .target
            .0
            .try_extend_vec_with_limit(mem::take(&mut self.incoming), hint, self.limit);
        if result.is_err() && !std::thread::panicking() {
            panic!("clock range limit exceeded");
        }
    }
}

impl Extend<Range<u64>> for OrderRange {
    fn extend<T: IntoIterator<Item = Range<u64>>>(&mut self, iter: T) {
        self.extend_with_limit(iter, usize::MAX);
    }
}

impl OrderRange {
    fn extend_with_limit(&mut self, iter: impl IntoIterator<Item = Range<u64>>, limit: usize) {
        let mut guard = MergeOnDrop {
            target: self,
            incoming: Vec::new(),
            sorted: true,
            limit,
        };
        for range in iter {
            if !range.is_empty() {
                let next = clock_range(range);
                guard.sorted = guard.sorted && guard.incoming.last().is_none_or(|&last| ordered_pair(last, next));
                guard.incoming.push(next);
            }
        }
    }

    pub fn new() -> Self {
        Self(CoreRange::new())
    }

    pub(crate) fn from_sorted_disjoint(ranges: VecDeque<Range<u64>>) -> Self {
        let converted: Vec<_> = Vec::from(ranges).into_iter().map(clock_range).collect();
        let hint = converted.capacity();
        Self(CoreRange::from_sorted_disjoint_with_capacity(converted, hint))
    }

    pub fn ranges_len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline(always)]
    pub fn contains(&self, clock: u64) -> bool {
        let (first, second) = self.0.as_slices();
        if second.is_empty() && first.len() <= 1 {
            return self.0.contains(clock);
        }
        let ranges = if second.first().is_some_and(|r| r.start <= clock) {
            second
        } else {
            first
        };
        let i = ranges.partition_point(|r| r.end <= clock);
        ranges.get(i).is_some_and(|r| r.start <= clock)
    }

    /// The clocks newly present in new_range, if it covers this set.
    pub fn diff_range(&self, new_range: &OrderRange) -> Vec<Range<u64>> {
        self.0.diff_range(&new_range.0).into_iter().map(to_range).collect()
    }

    pub fn push(&mut self, range: Range<u64>) {
        self.0.insert(range.start, range.end);
    }

    /// Removes and returns the first range.
    pub fn pop(&mut self) -> Option<Range<u64>> {
        self.0.pop_front().map(to_range)
    }

    pub fn merge(&mut self, other: Self) {
        self.0.merge_owned(other.0);
    }

    pub(crate) fn merge_from(&mut self, other: &Self) {
        self.0.merge_from(&other.0);
    }

    pub(crate) fn extend_vec(&mut self, ranges: Vec<Range<u64>>) {
        let mut converted: Vec<_> = ranges.into_iter().map(clock_range).collect();
        let hint = converted.capacity();
        prepare_ranges(&mut converted);
        self.0.extend_vec_with_capacity(converted, hint);
    }

    pub(crate) fn canonical_ranges(&self) -> Vec<Range<u64>> {
        let mut result = Vec::with_capacity(self.ranges_len());
        let (first, second) = self.0.as_slices();
        result.extend(first.iter().chain(second).copied().map(to_range));
        result
    }
}

/// Iterates over the ranges in order. The empty set yields nothing.
pub struct OrderRangeIter<'a> {
    first: std::slice::Iter<'a, ClockRange>,
    second: std::slice::Iter<'a, ClockRange>,
}

const _: () = assert!(size_of::<OrderRangeIter<'_>>() <= 4 * size_of::<usize>());

impl Iterator for OrderRangeIter<'_> {
    type Item = Range<u64>;

    fn next(&mut self) -> Option<Self::Item> {
        self.first.next().or_else(|| self.second.next()).copied().map(to_range)
    }
}

impl<'a> IntoIterator for &'a OrderRange {
    type Item = Range<u64>;
    type IntoIter = OrderRangeIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        let (first, second) = self.0.as_slices();
        OrderRangeIter {
            first: first.iter(),
            second: second.iter(),
        }
    }
}

#[cfg(test)]
#[allow(clippy::single_range_in_vec_init)]
mod tests {
    use std::{collections::VecDeque, ops::Range};

    use super::OrderRange;

    #[test]
    fn sparse_constructors_ignore_empty_intervals_in_any_order() {
        assert!(OrderRange::from(vec![4..4, 0..0, 2..2]).is_empty());
        for i in 0..3 {
            let mut ranges = vec![4..4, 0..0, 2..2];
            ranges[i] = 1..3;
            assert_eq!(OrderRange::from(ranges), OrderRange::from(1..3));
        }
    }

    #[test]
    fn wrapped_membership_uses_half_open_endpoints() {
        let mut r = OrderRange::from(vec![1..2, 4..6, 8..9]);
        assert_eq!(r.pop(), Some(1..2));
        r.push(u64::MAX - 2..u64::MAX);
        assert!(!r.0.as_slices().1.is_empty());
        for c in [
            0,
            3,
            4,
            5,
            6,
            7,
            8,
            9,
            u64::MAX - 3,
            u64::MAX - 2,
            u64::MAX - 1,
            u64::MAX,
        ] {
            assert_eq!(r.contains(c), (&r).into_iter().any(|range| range.contains(&c)));
        }
    }

    #[test]
    fn presort_matches_core_order_with_equal_starts() {
        let first = u64::MAX - 3;
        let mut ranges =
            Vec::from([first..u64::MAX, 0..2, first..first, first..first + 1, 0..1, 0..2].map(super::clock_range));
        super::prepare_ranges(&mut ranges);
        assert_eq!(
            ranges,
            [0..1, 0..2, 0..2, first..first + 1, first..u64::MAX].map(super::clock_range),
        );
    }

    fn assert_canonical(range: &OrderRange) {
        let ranges: Vec<_> = range.into_iter().collect();
        assert_eq!(ranges.len(), range.ranges_len());
        assert!(ranges.iter().all(|r| !r.is_empty()));
        assert!(ranges.windows(2).all(|w| w[0].end < w[1].start));
    }

    #[test]
    fn unwind_at_capacity_preserves_the_original_panic() {
        const CHILD: &str = "Y_OCTO_RANGE_UNWIND_CHILD";
        if !cfg!(miri) && std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "doc::common::range::tests::unwind_at_capacity_preserves_the_original_panic",
                ])
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "child {:?}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed"));
            return;
        }
        let old: Vec<_> = (1..=8).map(|i| 10 * i..10 * i + 1).collect();
        for (incoming, expected) in [
            (vec![0..1, 20..81], vec![0..1, 10..11, 20..81]),
            (vec![0..1], old.clone()),
        ] {
            let mut r = OrderRange::from(old.clone());
            let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                r.extend_with_limit(
                    incoming
                        .into_iter()
                        .chain(std::iter::once_with(|| panic!("iterator failed"))),
                    8,
                );
            }))
            .unwrap_err();
            assert_eq!(panic.downcast_ref::<&str>(), Some(&"iterator failed"));
            assert_eq!(r.canonical_ranges(), expected);
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
        assert_eq!(range, OrderRange::from(20..30));
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
        let expected = OrderRange::from(vec![2..4, 6..8, 10..12]);
        assert_eq!(OrderRange::from(vec![10..12, 2..4, 6..8]), expected);
        assert_eq!(OrderRange::from(VecDeque::from([6..8, 10..12, 2..4])), expected);
        assert_eq!([2..4, 10..12, 6..8].into_iter().collect::<OrderRange>(), expected);

        // overlapping, touching and empty ranges fold away
        let range = OrderRange::from(vec![10..12, 0..0, 3..6, 0..4, 12..14, 20..20]);
        assert_eq!(range, OrderRange::from(vec![0..6, 10..14]));
        assert_canonical(&range);
        assert_eq!(OrderRange::from(vec![0..10, 10..20, 20..30]), OrderRange::from(0..30));
        assert_eq!(OrderRange::from(vec![20..30, 0..10, 10..20]), OrderRange::from(0..30));
        assert_eq!(OrderRange::from(vec![5..9, 0..5]), OrderRange::from(0..9));
        assert_eq!(OrderRange::from(vec![5..9]), OrderRange::from(5..9));

        // nothing left
        for empty in [
            OrderRange::from(vec![3..3, 9..9]),
            OrderRange::from(Vec::new()),
            OrderRange::from(VecDeque::new()),
            OrderRange::from(7..7),
            std::iter::empty().collect(),
            OrderRange::new(),
        ] {
            assert_eq!(empty, OrderRange::from(0..0));
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
            assert_eq!(range, OrderRange::from(0..30), "{order:?}");
        }
    }

    #[test]
    fn test_range_covered() {
        fn covered(old: &[Range<u64>], new: &[Range<u64>]) -> bool {
            let old = OrderRange::from(old.to_vec());
            let mut new = OrderRange::from(new.to_vec());
            new.push(100..101);
            old.diff_range(&new).contains(&(100..101))
        }
        assert!(!covered(&[0..1], &[2..3]));
        assert!(covered(&[0..1], &[0..3]));
        assert!(!covered(&[0..1], &[1..3]));
        assert!(covered(&[0..1], &[0..3]));
        assert!(covered(&[1..2], &[0..3]));
        assert!(covered(&[1..2, 2..3], &[0..3]));
        assert!(!covered(&[1..2, 2..3, 3..4], &[0..3]));
        assert!(covered(&[0..1, 2..3], &[0..2, 2..4]));
        assert!(covered(&[0..1, 2..3, 3..4], &[0..2, 2..4]),);
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

    /// Canonical form computed by a slow reference: every clock in a bitmap.
    fn from_bitmap(covered: &[bool]) -> OrderRange {
        let mut ranges = Vec::new();
        let mut start = None;
        for (clock, &set) in covered.iter().chain([&false]).enumerate() {
            match (set, start) {
                (true, None) => start = Some(clock as u64),
                (false, Some(from)) => {
                    ranges.push(from..clock as u64);
                    start = None;
                }
                _ => {}
            }
        }
        OrderRange::from(ranges)
    }

    #[test]
    fn test_range_extend_and_merge_match_bitmap() {
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let rounds = if cfg!(miri) { 16 } else { 2000 };
        for _ in 0..rounds {
            let mut covered = [false; 128];
            let mut batch = |count: u64, next: &mut dyn FnMut() -> u64| {
                let mut ranges = Vec::new();
                for _ in 0..next() % count {
                    let start = next() % 124;
                    let end = (start + next() % 6).min(128);
                    covered[start as usize..end as usize].iter_mut().for_each(|c| *c = true);
                    ranges.push(start..end);
                }
                ranges
            };
            let base = batch(24, &mut next);
            let extended = batch(24, &mut next);
            let merged = batch(24, &mut next);

            let mut range = OrderRange::from(base);
            range.extend(extended);
            assert_canonical(&range);
            range.merge(OrderRange::from(merged));
            assert_canonical(&range);
            assert_eq!(range, from_bitmap(&covered));
        }
    }

    #[test]
    fn test_extend_vec_matches_extend() {
        for ranges in [vec![], vec![3..3], vec![5..9], vec![12..14, 1..2, 2..3, 20..20]] {
            let mut owned = OrderRange::from(vec![0..1, 10..12]);
            let mut iterated = owned.clone();
            owned.extend_vec(ranges.clone());
            iterated.extend(ranges.clone());
            assert_eq!(owned, iterated, "{ranges:?}");
            assert_canonical(&owned);
        }
    }

    #[test]
    fn test_range_extend_and_merge_at_u64_max() {
        const MAX: u64 = u64::MAX;
        let mut range = OrderRange::from(vec![0..1, MAX - 4..MAX - 2]);
        range.extend([MAX - 1..MAX, MAX - 2..MAX - 1, 3..4]);
        assert_eq!(range, OrderRange::from(vec![0..1, 3..4, MAX - 4..MAX]));
        assert_canonical(&range);

        range.merge(OrderRange::from(vec![1..3, 5..MAX - 4]));
        assert_eq!(range, OrderRange::from(vec![0..4, 5..MAX]));
        range.merge(OrderRange::from(vec![0..1, 4..5]));
        assert_eq!(range, OrderRange::from(0..MAX));
        assert_canonical(&range);
    }

    #[test]
    fn test_range_merge_shapes() {
        // empty on either side, single against fragment, in both directions
        let fragment = || OrderRange::from(vec![2..4, 8..10]);

        let mut range = OrderRange::new();
        range.merge(fragment());
        assert_eq!(range, fragment());

        let mut range = fragment();
        range.merge(OrderRange::new());
        assert_eq!(range, fragment());

        let mut range = OrderRange::from(4..8);
        range.merge(fragment());
        assert_eq!(range, OrderRange::from(2..10));

        let mut range = fragment();
        range.merge(OrderRange::from(4..8));
        assert_eq!(range, OrderRange::from(2..10));

        let mut range = fragment();
        range.merge(OrderRange::from(vec![0..20, 30..31]));
        assert_eq!(range, OrderRange::from(vec![0..20, 30..31]));
        assert_canonical(&range);

        // a batch that folds to one range collapses a fragment too
        let mut range = fragment();
        range.extend([4..6, 6..8]);
        assert_eq!(range, OrderRange::from(2..10));
    }

    #[test]
    fn test_range_extend_panic_on_first_item_changes_nothing() {
        let mut range: OrderRange = vec![(0..5), (10..15)].into();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            range.extend(std::iter::from_fn(|| -> Option<_> { panic!("iterator failed") }));
        }));
        assert!(result.is_err());
        assert_eq!(range, OrderRange::from(vec![(0..5), (10..15)]));
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
            OrderRange::from_sorted_disjoint(VecDeque::from([1..2])),
            OrderRange::from(1..2)
        );
        assert_eq!(
            OrderRange::from_sorted_disjoint(VecDeque::from([1..2, 3..4])),
            OrderRange::from(vec![3..4, 1..2])
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic]
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
