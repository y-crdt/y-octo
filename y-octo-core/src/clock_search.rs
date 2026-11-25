/// Binary-searches sorted non-overlapping `(start, len)` clock segments for
/// the segment containing `clock`, using explicit midpoint `low + (high - low)
/// / 2`.
pub fn find_clock_segment(segments: &[(u64, u64)], clock: u64) -> Option<usize> {
    let mut low = 0usize;
    let mut high = segments.len();
    while low < high {
        let mid = low + (high - low) / 2;
        let (start, len) = segments[mid];
        let end = if len > u64::MAX - start { u64::MAX } else { start + len };
        if clock < start {
            high = mid;
        } else if clock >= end {
            low = mid + 1;
        } else {
            return Some(mid);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lookup_cases() {
        let segs = [(0, 10), (10, 5), (20, 10)];
        assert_eq!(find_clock_segment(&[], 0), None);
        assert_eq!(find_clock_segment(&segs, 0), Some(0));
        assert_eq!(find_clock_segment(&segs, 9), Some(0));
        assert_eq!(find_clock_segment(&segs, 10), Some(1));
        assert_eq!(find_clock_segment(&segs, 15), None);
        assert_eq!(find_clock_segment(&segs, 19), None);
        assert_eq!(find_clock_segment(&segs, 20), Some(2));
        assert_eq!(find_clock_segment(&segs, 29), Some(2));
        assert_eq!(find_clock_segment(&segs, 30), None);
    }
}
