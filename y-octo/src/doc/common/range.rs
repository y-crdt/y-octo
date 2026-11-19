use std::{collections::VecDeque, mem, ops::Range};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum OrderRange {
    Range(Range<u64>),
    Fragment(VecDeque<Range<u64>>),
}

impl Default for OrderRange {
    fn default() -> Self {
        Self::Range(0..0)
    }
}

impl From<Range<u64>> for OrderRange {
    fn from(range: Range<u64>) -> Self {
        Self::Range(range)
    }
}

impl From<Vec<Range<u64>>> for OrderRange {
    fn from(value: Vec<Range<u64>>) -> Self {
        Self::Fragment(value.into_iter().collect())
    }
}

impl From<VecDeque<Range<u64>>> for OrderRange {
    fn from(value: VecDeque<Range<u64>>) -> Self {
        Self::Fragment(value)
    }
}

#[inline]
fn is_continuous_range(lhs: &Range<u64>, rhs: &Range<u64>) -> bool {
    lhs.end >= rhs.start && lhs.start <= rhs.end
}

impl OrderRange {
    pub fn ranges_len(&self) -> usize {
        match self {
            OrderRange::Range(_) => 1,
            OrderRange::Fragment(ranges) => ranges.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            OrderRange::Range(range) => range.is_empty(),
            OrderRange::Fragment(vec) => vec.is_empty(),
        }
    }

    pub fn contains(&self, clock: u64) -> bool {
        match self {
            OrderRange::Range(range) => range.contains(&clock),
            OrderRange::Fragment(ranges) => ranges.iter().any(|r| r.contains(&clock)),
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
        let old_vec = self.clone().into_iter().collect::<Vec<_>>();
        let new_vec = new_range.clone().into_iter().collect::<Vec<_>>();

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
        // an empty range covers nothing; storing it would break the
        // sorted, non-overlapping fragment invariant
        if range.is_empty() {
            return;
        }
        match self {
            OrderRange::Range(r) => {
                if r.start == r.end {
                    *self = range.into();
                } else if is_continuous_range(r, &range) {
                    r.end = r.end.max(range.end);
                    r.start = r.start.min(range.start);
                } else {
                    *self = OrderRange::Fragment(if r.start < range.start {
                        VecDeque::from([r.clone(), range])
                    } else {
                        VecDeque::from([range, r.clone()])
                    });
                }
            }
            OrderRange::Fragment(ranges) => {
                if ranges.is_empty() {
                    *self = OrderRange::Range(range);
                } else {
                    OrderRange::push_inner(ranges, range);
                    self.make_single();
                }
            }
        }
    }

    pub fn pop(&mut self) -> Option<Range<u64>> {
        if self.is_empty() {
            None
        } else {
            match self {
                OrderRange::Range(range) => Some(mem::replace(range, 0..0)),
                OrderRange::Fragment(list) => list.pop_front(),
            }
        }
    }

    pub fn merge(&mut self, other: Self) {
        self.extend(&other);
    }

    fn make_fragment(&mut self) {
        if let OrderRange::Range(range) = self {
            *self = OrderRange::Fragment(if range.is_empty() {
                VecDeque::new()
            } else {
                VecDeque::from([range.clone()])
            });
        }
    }

    fn make_single(&mut self) {
        if let OrderRange::Fragment(ranges) = self
            && ranges.len() == 1
        {
            *self = OrderRange::Range(ranges[0].clone());
        }
    }

    /// Ranges sorted by start with all continuous ranges merged, mirroring
    /// what yjs does when encoding delete sets (sortAndMergeDeleteSet), so the
    /// wire format stays canonical regardless of insertion or decoding order.
    pub(crate) fn canonical_ranges(&self) -> Vec<Range<u64>> {
        let mut ranges: Vec<Range<u64>> = self.into_iter().collect();
        ranges.sort_by(|a, b| a.start.cmp(&b.start).then(a.end.cmp(&b.end)));

        let mut merged: Vec<Range<u64>> = Vec::with_capacity(ranges.len());
        for range in ranges {
            // empty ranges delete nothing; dropping them keeps the wire
            // format canonical (mirrors yjs' sortAndMergeDeleteSet)
            if range.is_empty() {
                continue;
            }
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

    /// Merge all available ranges list into one.
    pub fn squash(&mut self) {
        // merge all available ranges
        if let OrderRange::Fragment(ranges) = self {
            if ranges.is_empty() {
                *self = OrderRange::Range(0..0);
                return;
            }

            let mut changed = false;
            let mut merged = VecDeque::with_capacity(ranges.len());
            let mut cur = ranges[0].clone();

            for next in ranges.iter().skip(1) {
                if is_continuous_range(&cur, next) {
                    cur.start = cur.start.min(next.start);
                    cur.end = cur.end.max(next.end);
                    changed = true;
                } else {
                    merged.push_back(cur);
                    cur = next.clone();
                }
            }
            merged.push_back(cur);

            if merged.len() == 1 {
                *self = OrderRange::Range(merged[0].clone());
            } else if changed {
                mem::swap(ranges, &mut merged);
            }
        }
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
        self.make_fragment();
        match self {
            OrderRange::Fragment(ranges) => {
                for range in other {
                    OrderRange::push_inner(ranges, range);
                }

                self.make_single();
            }
            _ => unreachable!(),
        }
    }
}

pub struct OrderRangeIter<'a> {
    range: &'a OrderRange,
    idx: usize,
}

impl Iterator for OrderRangeIter<'_> {
    type Item = Range<u64>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.range {
            OrderRange::Range(range) => {
                if self.idx == 0 {
                    self.idx += 1;
                    Some(range.clone())
                } else {
                    None
                }
            }
            OrderRange::Fragment(ranges) => {
                if self.idx < ranges.len() {
                    let range = ranges[self.idx].clone();
                    self.idx += 1;
                    Some(range)
                } else {
                    None
                }
            }
        }
    }
}

#[cfg(test)]
#[allow(clippy::single_range_in_vec_init)]
mod tests {
    use super::OrderRange;
    #[test]
    fn test_range_push() {
        let mut range: OrderRange = (0..10).into();

        range.push(5..15);
        assert_eq!(range, OrderRange::Range(0..15));

        // turn to fragment
        range.push(20..30);
        assert_eq!(range, OrderRange::from(vec![(0..15), (20..30)]));

        // auto merge
        range.push(15..16);
        assert_eq!(range, OrderRange::from(vec![(0..16), (20..30)]));

        // squash
        range.push(16..20);
        assert_eq!(range, OrderRange::Range(0..30));
    }

    #[test]
    fn test_range_pop() {
        let mut range: OrderRange = vec![(0..10), (20..30)].into();
        assert_eq!(range.pop(), Some(0..10));

        let mut range: OrderRange = (0..10).into();
        assert_eq!(range.pop(), Some(0..10));
        assert!(range.is_empty());
        assert_eq!(range.pop(), None);
    }

    #[test]
    fn test_ranges_squash() {
        let mut range = OrderRange::from(vec![(0..10), (20..30)]);

        // do nothing
        range.squash();
        assert_eq!(range, OrderRange::from(vec![(0..10), (20..30)]));

        // merged into list
        range = OrderRange::from(vec![(0..10), (10..20), (30..40)]);
        range.squash();
        assert_eq!(range, OrderRange::from(vec![(0..20), (30..40)]));

        // turn to range
        range = OrderRange::from(vec![(0..10), (10..20), (20..30)]);
        range.squash();
        assert_eq!(range, OrderRange::Range(0..30));
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
            let old = OrderRange::Range(0..1);
            let new = OrderRange::Range(2..3);
            let ranges = old.diff_range(&new);
            assert_eq!(ranges, vec![]);
        }

        {
            let old = OrderRange::Range(0..10);
            let new = OrderRange::Range(0..11);
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
        assert_eq!(range, OrderRange::Range(0..30));

        let mut range: OrderRange = vec![(0..10), (20..30)].into();
        range.merge(vec![(10..20), (30..40)].into());
        assert_eq!(range, OrderRange::Range(0..40));
    }

    #[test]
    fn iter() {
        let range: OrderRange = vec![(0..10), (20..30)].into();

        assert_eq!(range.into_iter().collect::<Vec<_>>(), vec![(0..10), (20..30)]);

        let range: OrderRange = OrderRange::Range(0..10);

        assert_eq!(range.into_iter().collect::<Vec<_>>(), vec![(0..10)]);
    }

    fn assert_canonical(range: &OrderRange) {
        let ranges = range.into_iter().collect::<Vec<_>>();
        for r in &ranges {
            assert!(!r.is_empty() || ranges.len() == 1, "empty fragment in {range:?}");
        }
        for pair in ranges.windows(2) {
            assert!(
                pair[0].end < pair[1].start,
                "unsorted or touching fragments in {range:?}"
            );
        }
    }

    #[test]
    fn test_range_push_spanning_many_fragments() {
        let mut range: OrderRange = vec![(0..5), (10..15), (20..25), (30..35), (40..45)].into();
        range.push(0..50);
        assert_eq!(range, OrderRange::Range(0..50));

        let mut range: OrderRange = vec![(0..5), (10..15), (20..25), (30..35), (40..45)].into();
        range.push(12..32);
        assert_eq!(range, OrderRange::from(vec![(0..5), (10..35), (40..45)]));

        // touching both neighbours at once
        let mut range: OrderRange = vec![(0..5), (10..15)].into();
        range.push(5..10);
        assert_eq!(range, OrderRange::Range(0..15));

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
        assert_eq!(range, OrderRange::Range(0..5));
    }

    #[test]
    fn test_range_push_keeps_fragments_canonical() {
        // deterministic pseudo random pushes, checked against a bitmap
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
                if next() % 2 == 0 {
                    range.push(start..end);
                } else {
                    range.extend([start..end]);
                }
                covered[start as usize..end as usize].iter_mut().for_each(|c| *c = true);
                assert_canonical(&range);
            }
            for (clock, covered) in covered.iter().enumerate() {
                assert_eq!(range.contains(clock as u64), *covered, "clock {clock} in {range:?}");
            }
        }
    }
}
