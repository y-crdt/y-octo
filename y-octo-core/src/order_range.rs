use alloc::vec::Vec;

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
pub struct ClockRange {
    pub start: u64,
    pub end: u64,
}

/// Canonical sorted, disjoint, non-adjacent, non-empty intervals `[start, end)`
/// backed by `Vec<ClockRange>`.
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
pub struct OrderRange {
    pub ranges: Vec<ClockRange>,
}

impl Default for OrderRange {
    fn default() -> Self {
        Self::new()
    }
}

impl OrderRange {
    pub fn new() -> Self {
        Self { ranges: Vec::new() }
    }

    pub fn from_range(start: u64, end: u64) -> Self {
        let mut r = Self::new();
        r.insert(start, end);
        r
    }

    pub fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    pub fn len(&self) -> usize {
        self.ranges.len()
    }

    pub fn contains(&self, clock: u64) -> bool {
        let mut low = 0usize;
        let mut high = self.ranges.len();
        while low < high {
            let mid = low + (high - low) / 2;
            let r = self.ranges[mid];
            if clock < r.start {
                high = mid;
            } else if clock >= r.end {
                low = mid + 1;
            } else {
                return true;
            }
        }
        false
    }

    /// Inserts `[start, end)` while maintaining canonical sorted, disjoint,
    /// non-adjacent, non-empty intervals. Tail insertions use `Vec::push` and
    /// interior non-merging insertions use `Vec::insert` only when `at < len`.
    pub fn insert(&mut self, start: u64, end: u64) {
        if start >= end {
            return;
        }
        let mut first = 0usize;
        let mut hi = self.ranges.len();
        while first < hi {
            let mid = first + (hi - first) / 2;
            if self.ranges[mid].end < start {
                first = mid + 1;
            } else {
                hi = mid;
            }
        }

        let mut last = first;
        let mut hi2 = self.ranges.len();
        while last < hi2 {
            let mid = last + (hi2 - last) / 2;
            if self.ranges[mid].start <= end {
                last = mid + 1;
            } else {
                hi2 = mid;
            }
        }

        if first == last {
            let item = ClockRange { start, end };
            if first == self.ranges.len() {
                self.ranges.push(item);
            } else {
                self.ranges.insert(first, item);
            }
        } else {
            let f = self.ranges[first];
            let l = self.ranges[last - 1];
            let merged_start = if start < f.start { start } else { f.start };
            let merged_end = if end > l.end { end } else { l.end };
            let merged = ClockRange {
                start: merged_start,
                end: merged_end,
            };
            if last == first + 1 {
                self.ranges[first] = merged;
            } else {
                let mut out = Vec::new();
                let mut i = 0usize;
                while i < first {
                    out.push(self.ranges[i]);
                    i += 1;
                }
                out.push(merged);
                let mut j = last;
                while j < self.ranges.len() {
                    out.push(self.ranges[j]);
                    j += 1;
                }
                self.ranges = out;
            }
        }
    }

    pub fn merge(&mut self, other: &OrderRange) {
        let mut i = 0usize;
        while i < other.ranges.len() {
            let r = other.ranges[i];
            self.insert(r.start, r.end);
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_insert_and_merge() {
        let mut r = OrderRange::new();
        r.insert(10, 10);
        assert!(r.is_empty());

        r.insert(20, 30);
        r.insert(0, 10);
        r.insert(12, 15);
        assert_eq!(
            r.ranges,
            vec![
                ClockRange { start: 0, end: 10 },
                ClockRange { start: 12, end: 15 },
                ClockRange { start: 20, end: 30 },
            ]
        );
        r.insert(10, 20);
        assert_eq!(r.ranges, vec![ClockRange { start: 0, end: 30 }]);
        assert!(r.contains(0));
        assert!(r.contains(29));
        assert!(!r.contains(30));
    }
}
