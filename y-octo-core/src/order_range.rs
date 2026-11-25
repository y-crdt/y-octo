use alloc::vec::Vec;

use crate::CodecError;

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
pub struct ClockRange {
    pub start: u64,
    pub end: u64,
}

const EMPTY: ClockRange = ClockRange { start: 0, end: 0 };
const MAX_RANGES: usize = 1 << 30;

#[inline]
fn before(a: ClockRange, b: ClockRange) -> bool {
    #[cfg(test)]
    COMPARISONS.with(|count| count.set(count.get() + 1));
    a.start < b.start || (a.start == b.start && a.end < b.end)
}

/// Restore the max-heap below root. The bound on root also bounds 2 * root + 1.
#[allow(clippy::ptr_arg, reason = "Aeneas cannot join the mutable slice borrow in this loop")]
fn sift_down(buf: &mut Vec<ClockRange>, mut root: usize, end: usize) {
    let item = buf[root];
    while root < end / 2 {
        let mut child = root * 2 + 1;
        if child + 1 < end && before(buf[child], buf[child + 1]) {
            child += 1;
        }
        if !before(item, buf[child]) {
            break;
        }
        let next = buf[child];
        buf[root] = next;
        root = child;
    }
    buf[root] = item;
}

#[allow(
    clippy::manual_swap,
    reason = "keep both indexed writes visible in the extracted heap proof"
)]
fn heapsort(buf: &mut Vec<ClockRange>, mut end: usize) {
    let mut root = end / 2;
    while root > 0 {
        root -= 1;
        sift_down(buf, root, end);
    }
    while end > 1 {
        end -= 1;
        let last = buf[end];
        buf[end] = buf[0];
        buf[0] = last;
        sift_down(buf, 0, end);
    }
}

// A short unsorted suffix is common when a map and its children are deleted
// together. Shifting at most eight elements avoids building a heap for it.
#[allow(clippy::ptr_arg, reason = "keep Aeneas loop joins on the modeled Vec")]
fn insert_sorted(buf: &mut Vec<ClockRange>, mut i: usize) {
    let r = buf[i];
    while i > 0 && before(r, buf[i - 1]) {
        let previous = buf[i - 1];
        buf[i] = previous;
        i -= 1;
    }
    buf[i] = r;
}

fn sort_short_suffix(buf: &mut Vec<ClockRange>, mut i: usize, end: usize) {
    while i < end {
        insert_sorted(buf, i);
        i += 1;
    }
}

// Keep the backing allocation, including its spare capacity. After the first
// empty interval every retained interval moves into a strictly earlier slot.
#[allow(clippy::ptr_arg, reason = "keep Aeneas loop joins on the modeled Vec")]
fn nonempty_prefix(buf: &mut Vec<ClockRange>) -> usize {
    let mut kept = 0;
    while kept < buf.len() && buf[kept].start < buf[kept].end {
        kept += 1;
    }
    let mut read = kept;
    while read < buf.len() {
        let r = buf[read];
        if r.start < r.end {
            buf[kept] = r;
            kept += 1;
        }
        read += 1;
    }
    kept
}

#[allow(
    clippy::ptr_arg,
    clippy::manual_swap,
    reason = "keep both indexed writes visible to Aeneas"
)]
fn reverse_prefix(buf: &mut Vec<ClockRange>, end: usize) {
    let mut i = 0;
    while i < end / 2 {
        let j = end - 1 - i;
        let left = buf[i];
        buf[i] = buf[j];
        buf[j] = left;
        i += 1;
    }
}

fn sort_prefix(buf: &mut Vec<ClockRange>, end: usize) {
    let mut i = 1;
    while i < end {
        if before(buf[i], buf[i - 1]) {
            // The prefix before the first inversion is nondecreasing. It
            // can start a descending run only if all its elements are equal.
            if i == 1 || !before(buf[0], buf[i - 1]) {
                let mut j = i + 1;
                while j < end && !before(buf[j - 1], buf[j]) {
                    j += 1;
                }
                if j == end {
                    reverse_prefix(buf, end);
                    return;
                }
            }
            if end <= 8 {
                sort_short_suffix(buf, i, end);
            } else {
                heapsort(buf, end);
            }
            return;
        }
        i += 1;
    }
}

// A canonical batch can become the backing ring without copying any ranges.
fn is_canonical(buf: &[ClockRange]) -> bool {
    let mut i = 0;
    while i < buf.len() {
        let r = buf[i];
        if r.start >= r.end || (i != 0 && buf[i - 1].end >= r.start) {
            return false;
        }
        i += 1;
    }
    true
}

// Check the original slice before coalescing so a late inversion preserves even
// duplicate intervals and empty entries in the vector returned to the caller.
#[inline]
fn ordered_needs_filter(buf: &[ClockRange]) -> Option<bool> {
    let mut needs_filter = false;
    let mut i = 0;
    while i < buf.len() {
        let r = buf[i];
        if i != 0 && before(r, buf[i - 1]) {
            return None;
        }
        needs_filter |= r.start >= r.end;
        i += 1;
    }
    Some(needs_filter)
}

fn canonicalize(buf: &mut Vec<ClockRange>) -> usize {
    if is_canonical(buf) {
        return buf.len();
    }
    let end = nonempty_prefix(buf);
    if end < 2 {
        return end;
    }
    sort_prefix(buf, end);
    coalesce_sorted_prefix(buf, end)
}

// The prefix is nonempty, contains only valid intervals, and is ordered by
// start.
#[allow(clippy::ptr_arg, reason = "keep the indexed writes visible to Aeneas")]
fn coalesce_sorted_prefix(buf: &mut Vec<ClockRange>, end: usize) -> usize {
    let mut used = 1;
    let mut read = 1;
    while read < end {
        let r = buf[read];
        if r.start <= buf[used - 1].end {
            if r.end > buf[used - 1].end {
                buf[used - 1].end = r.end;
            }
        } else {
            buf[used] = r;
            used += 1;
        }
        read += 1;
    }
    used
}

/// The allocated slots are all initialized. Only the len slots starting at
/// head are part of the set; inactive slots may contain old values.
#[cfg_attr(not(aeneas_extract), derive(Debug))]
struct Ring {
    buf: Vec<ClockRange>,
    head: u32,
    len: u32,
}

// Clone just the active ranges, as VecDeque does after front removals.
impl Clone for Ring {
    fn clone(&self) -> Self {
        let len = self.len as usize;
        let mut buf = Vec::with_capacity(len);
        let (first, second) = self.slices();
        buf.extend_from_slice(first);
        buf.extend_from_slice(second);
        Self {
            buf,
            head: 0,
            len: self.len,
        }
    }
}

#[inline]
fn physical(cap: usize, head: usize, index: usize) -> usize {
    let tail = cap - head;
    if index < tail { head + index } else { index - tail }
}

const MOVE_BLOCK: usize = 512;

// Both copies use the same subslice, so release LLVM can lower the snapshot
// to one variable-length memmove. The bound limits stack use in debug builds.
#[inline(never)]
fn move_block(buf: &mut [ClockRange], from: usize, to: usize, count: usize) {
    let mut block = [EMPTY; MOVE_BLOCK];
    let active = &mut block[..count];
    active.copy_from_slice(&buf[from..from + count]);
    buf[to..to + count].copy_from_slice(active);
}

#[inline]
fn move_segment(buf: &mut [ClockRange], from: usize, to: usize, count: usize) {
    if from + count <= to {
        let (left, right) = buf.split_at_mut(to);
        right[..count].copy_from_slice(&left[from..from + count]);
    } else if to + count <= from {
        let (left, right) = buf.split_at_mut(from);
        left[to..to + count].copy_from_slice(&right[..count]);
    } else {
        let mut remaining = count;
        while remaining > MOVE_BLOCK {
            let offset = if from < to {
                remaining - MOVE_BLOCK
            } else {
                count - remaining
            };
            move_block(buf, from + offset, to + offset, MOVE_BLOCK);
            remaining -= MOVE_BLOCK;
        }
        let offset = if from < to { 0 } else { count - remaining };
        move_block(buf, from + offset, to + offset, remaining);
    }
}

#[cfg(test)]
std::thread_local! { static COMPARISONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }

#[cfg(test)]
std::thread_local! { static MOVED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }

impl Ring {
    #[inline]
    fn at(&self, i: usize) -> ClockRange {
        self.buf[physical(self.buf.len(), self.head as usize, i)]
    }

    #[inline]
    fn set(&mut self, i: usize, r: ClockRange) {
        let pos = physical(self.buf.len(), self.head as usize, i);
        self.buf[pos] = r;
    }

    // A marker may occupy the first inactive slot. Its value only guides
    // allocation; logical indices and ordering never depend on it.
    fn capacity_hint(&self) -> usize {
        if self.len as usize == self.buf.len() {
            return 0;
        }
        let slot = self.at(self.len as usize);
        if slot.end == 0 && slot.start > self.buf.len() as u64 && slot.start <= MAX_RANGES as u64 {
            slot.start as usize
        } else {
            0
        }
    }

    fn grow(&mut self, needed: usize, hint: usize) {
        let cap = self.buf.len();
        if needed < cap || (needed == cap && hint == 0) {
            return;
        }
        assert!(needed <= MAX_RANGES);
        // A series of push operations would grow past this exact-size batch.
        // Allocate its destination once, placing wrapped ranges in logical
        // order.
        if needed > 2 * cap.max(hint) {
            let mut target = Vec::with_capacity(needed);
            let mut i = 0;
            while i < self.len as usize {
                target.push(self.at(i));
                i += 1;
            }
            while target.len() < needed {
                target.push(EMPTY);
            }
            self.buf = target;
            self.head = 0;
            return;
        }
        let next = if hint > cap && needed <= hint {
            // Preserve a marker when this update itself uses the whole
            // geometric increment, unless the budget is already exhausted.
            (cap * 2).max(needed + 1).min(hint)
        } else {
            needed.max((cap.max(hint) * 2).min(MAX_RANGES))
        };
        while self.buf.len() < next {
            self.buf.push(EMPTY);
        }
        let head = self.head as usize;
        let tail = cap - head;
        if tail < self.len as usize {
            let wrapped = self.len as usize - tail;
            let added = next - cap;
            if wrapped <= tail && wrapped <= added {
                let mut i = 0;
                while i < wrapped {
                    self.buf[cap + i] = self.buf[i];
                    i += 1;
                }
            } else {
                let mut i = cap;
                while i > head {
                    i -= 1;
                    self.buf[i + added] = self.buf[i];
                }
                self.head = (head + added) as u32;
            }
        }
    }

    // Advance from the side whose unread slots cannot be overwritten. A
    // contiguous copy ends when either physical index reaches the seam.
    fn move_slots(&mut self, src: usize, dst: usize, count: usize) {
        if count == 0 || src == dst {
            return;
        }
        let cap = self.buf.len();
        let head = self.head as usize;
        let mut remaining = count;
        while remaining != 0 {
            let (from, to, n) = if dst < src {
                let done = count - remaining;
                let from = physical(cap, head, src + done);
                let to = physical(cap, head, dst + done);
                (from, to, remaining.min(cap - from).min(cap - to))
            } else {
                let end = physical(cap, head, src + (remaining - 1)) + 1;
                let dest_end = physical(cap, head, dst + (remaining - 1)) + 1;
                let n = remaining.min(end).min(dest_end);
                (end - n, dest_end - n, n)
            };
            move_segment(&mut self.buf, from, to, n);
            remaining -= n;
        }
    }

    /// Change the width of [lo, hi), leaving space for the caller's
    /// replacement. Move the shorter surviving side. Both ends are
    /// constant-time apart from growth.
    fn make_gap(&mut self, lo: usize, hi: usize, width: usize) {
        let len = self.len as usize;
        let taken = hi - lo;
        let suffix = len - hi;
        #[cfg(test)]
        MOVED.with(|moved| moved.set(moved.get() + taken + if width != taken { lo.min(suffix) } else { 0 }));
        if width == taken {
            return;
        }
        let hint = self.capacity_hint();
        if width > taken {
            let added = width - taken;
            self.grow(len + added, hint);
            if lo < suffix {
                self.head = physical(self.buf.len(), self.head as usize, self.buf.len() - added) as u32;
                self.move_slots(added, 0, lo);
            } else {
                self.move_slots(hi, hi + added, suffix);
            }
        } else if width < taken {
            let cut = taken - width;
            if lo < suffix {
                self.move_slots(0, cut, lo);
                self.head = physical(self.buf.len(), self.head as usize, cut) as u32;
            } else {
                self.move_slots(hi, hi - cut, suffix);
            }
        }
        self.len = (len - taken + width) as u32;
        if (self.len as usize) < self.buf.len() {
            self.set(
                self.len as usize,
                ClockRange {
                    start: hint as u64,
                    end: 0,
                },
            );
        }
    }

    #[inline]
    fn slices(&self) -> (&[ClockRange], &[ClockRange]) {
        let head = self.head as usize;
        let len = self.len as usize;
        let first = len.min(self.buf.len() - head);
        (&self.buf[head..head + first], &self.buf[..len - first])
    }

    // The search stays on one side of the physical wrap.
    fn lower(&self, start: u64) -> usize {
        let (first, second) = self.slices();
        let (ranges, offset) = if !first.is_empty() && first[first.len() - 1].end < start {
            (second, first.len())
        } else {
            (first, 0)
        };
        let mut lo = 0;
        let mut hi = ranges.len();
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if ranges[mid].end < start {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        offset + lo
    }

    // First range whose start is greater than end.
    fn upper(&self, end: u64, mut lo: usize) -> usize {
        let mut hi = self.len as usize;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.at(mid).start <= end {
                lo = mid + 1
            } else {
                hi = mid
            }
        }
        lo
    }

    fn try_insert(&mut self, mut r: ClockRange, limit: usize) -> Result<(), CodecError> {
        let lo = self.lower(r.start);
        let hi = if lo == self.len as usize || self.at(lo).start > r.end {
            lo
        } else {
            self.upper(r.end, lo)
        };
        if lo < hi {
            r.start = r.start.min(self.at(lo).start);
            r.end = r.end.max(self.at(hi - 1).end);
        } else if self.len as usize == limit {
            return Err(CodecError::LimitExceeded);
        }
        self.make_gap(lo, hi, 1);
        self.set(lo, r);
        Ok(())
    }
}

#[derive(Clone)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
enum Repr {
    Single([ClockRange; 1]),
    Many(Ring),
}

/// Canonical, nonempty, separated half-open clock intervals, in ascending
/// order.
#[derive(Clone)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
pub struct OrderRange {
    repr: Repr,
}

impl Default for OrderRange {
    fn default() -> Self {
        Self::new()
    }
}

// Compare one continuous run on each side, without recomputing ring indices.
#[inline]
fn equal_run(a: &[ClockRange], b: &[ClockRange]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

// The left ring wraps first. The right ring's wrap splits the left tail.
#[inline]
fn equal_runs(a: &[ClockRange], tail: &[ClockRange], b: &[ClockRange], rest: &[ClockRange]) -> bool {
    let split = b.len() - a.len();
    equal_run(a, &b[..a.len()]) && equal_run(&tail[..split], &b[a.len()..]) && equal_run(&tail[split..], rest)
}

impl PartialEq for OrderRange {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        let (a, tail) = self.as_slices();
        let (b, rest) = other.as_slices();
        if a.len() <= b.len() {
            equal_runs(a, tail, b, rest)
        } else {
            equal_runs(b, rest, a, tail)
        }
    }
}

impl Eq for OrderRange {}

impl OrderRange {
    pub fn new() -> Self {
        Self {
            repr: Repr::Single([EMPTY]),
        }
    }

    pub fn from_range(start: u64, end: u64) -> Self {
        let r = if start < end { ClockRange { start, end } } else { EMPTY };
        Self {
            repr: Repr::Single([r]),
        }
    }

    pub fn from_vec(ranges: Vec<ClockRange>) -> Self {
        Self::from_vec_with_capacity(ranges, 0)
    }

    /// Adopt or coalesce an ordered batch. On an inversion or an oversized
    /// input the caller receives the original vector, including its spare
    /// capacity.
    #[inline]
    pub fn try_from_ordered_with_capacity(mut ranges: Vec<ClockRange>, hint: usize) -> Result<Self, Vec<ClockRange>> {
        let len = ranges.len();
        if len > MAX_RANGES {
            return Err(ranges);
        }
        if is_canonical(&ranges) {
            return Ok(Self::from_prefix(ranges, len, hint));
        }

        let Some(needs_filter) = ordered_needs_filter(&ranges) else {
            return Err(ranges);
        };
        let end = if needs_filter {
            nonempty_prefix(&mut ranges)
        } else {
            len
        };
        let used = if end < 2 {
            end
        } else {
            coalesce_sorted_prefix(&mut ranges, end)
        };
        Ok(Self::from_prefix(ranges, used, hint))
    }

    pub fn from_vec_with_capacity(mut ranges: Vec<ClockRange>, capacity_hint: usize) -> Self {
        let kept = canonicalize(&mut ranges);
        Self::from_prefix(ranges, kept, capacity_hint)
    }

    fn from_prefix(mut ranges: Vec<ClockRange>, len: usize, capacity_hint: usize) -> Self {
        match len {
            0 => Self::new(),
            1 => Self::from_range(ranges[0].start, ranges[0].end),
            _ => {
                assert!(len <= MAX_RANGES);
                if ranges.len() > MAX_RANGES {
                    let mut prefix = Vec::with_capacity(len);
                    let mut i = 0;
                    while i < len {
                        prefix.push(ranges[i]);
                        i += 1;
                    }
                    ranges = prefix;
                }
                let hint = capacity_hint.min(MAX_RANGES);
                if hint > ranges.len() {
                    let marker = ClockRange {
                        start: hint as u64,
                        end: 0,
                    };
                    if len == ranges.len() {
                        ranges.push(marker);
                    } else {
                        ranges[len] = marker;
                    }
                } else if len < ranges.len() {
                    ranges[len] = EMPTY;
                }
                Self {
                    repr: Repr::Many(Ring {
                        buf: ranges,
                        head: 0,
                        len: len as u32,
                    }),
                }
            }
        }
    }

    pub fn len(&self) -> usize {
        match &self.repr {
            Repr::Single(a) => {
                if a[0].start < a[0].end {
                    1
                } else {
                    0
                }
            }
            Repr::Many(r) => r.len as usize,
        }
    }

    pub fn is_empty(&self) -> bool {
        match &self.repr {
            Repr::Single(a) => a[0].start >= a[0].end,
            Repr::Many(_) => false,
        }
    }

    fn at(&self, index: usize) -> ClockRange {
        match &self.repr {
            Repr::Single(a) => a[0],
            Repr::Many(r) => r.at(index),
        }
    }

    pub fn get(&self, index: usize) -> Option<ClockRange> {
        if index < self.len() { Some(self.at(index)) } else { None }
    }

    pub fn first(&self) -> Option<ClockRange> {
        self.get(0)
    }

    pub fn last(&self) -> Option<ClockRange> {
        let len = self.len();
        if len == 0 { None } else { Some(self.at(len - 1)) }
    }

    #[inline]
    pub fn as_slices(&self) -> (&[ClockRange], &[ClockRange]) {
        match &self.repr {
            Repr::Single(a) if a[0].start < a[0].end => (a, &[]),
            Repr::Single(_) => (&[], &[]),
            Repr::Many(r) => r.slices(),
        }
    }

    #[inline]
    pub fn contains(&self, clock: u64) -> bool {
        match &self.repr {
            Repr::Single(a) => a[0].start <= clock && clock < a[0].end,
            Repr::Many(r) => {
                let hi = r.upper(clock, 0);
                hi > 0 && clock < r.at(hi - 1).end
            }
        }
    }

    pub fn insert(&mut self, start: u64, end: u64) {
        assert!(self.try_insert(start, end).is_ok());
    }

    /// Fails without changing the set if a disjoint insertion would exceed
    /// the per-client limit. Overlapping and adjacent inserts still fit.
    pub fn try_insert(&mut self, start: u64, end: u64) -> Result<(), CodecError> {
        if start >= end {
            return Ok(());
        }
        let item = ClockRange { start, end };
        match &mut self.repr {
            Repr::Single(a) => {
                let old = a[0];
                if old.start >= old.end {
                    a[0] = item;
                } else if start <= old.end && old.start <= end {
                    a[0] = ClockRange {
                        start: old.start.min(start),
                        end: old.end.max(end),
                    };
                } else {
                    let mut buf = Vec::with_capacity(2);
                    if start < old.start {
                        buf.push(item);
                        buf.push(old);
                    } else {
                        buf.push(old);
                        buf.push(item);
                    }
                    self.repr = Repr::Many(Ring { buf, head: 0, len: 2 });
                }
            }
            Repr::Many(r) => {
                r.try_insert(item, MAX_RANGES)?;
                if r.len == 1 {
                    self.repr = Repr::Single([r.at(0)]);
                }
            }
        }
        Ok(())
    }

    fn pop_end(&mut self, front: bool) -> Option<ClockRange> {
        match &mut self.repr {
            Repr::Single(a) => {
                let r = a[0];
                if r.start >= r.end {
                    return None;
                }
                a[0] = EMPTY;
                Some(r)
            }
            Repr::Many(r) => {
                let value = if front {
                    let head = r.head as usize;
                    let value = r.buf[head];
                    // Advancing head and shortening the range leave the first
                    // spare slot in place.
                    let next = head + 1;
                    r.head = if next == r.buf.len() { 0 } else { next as u32 };
                    r.len -= 1;
                    value
                } else {
                    let last = r.len as usize - 1;
                    let value = r.at(last);
                    r.make_gap(last, last + 1, 0);
                    value
                };
                if r.len == 1 {
                    self.repr = Repr::Single([r.buf[r.head as usize]]);
                }
                Some(value)
            }
        }
    }

    pub fn pop_front(&mut self) -> Option<ClockRange> {
        self.pop_end(true)
    }

    pub fn pop_back(&mut self) -> Option<ClockRange> {
        self.pop_end(false)
    }
}

impl Ring {
    /// Install the union of this window with incoming[a..b], preserving the
    /// untouched prefix and suffix in their ring whenever their lengths allow.
    fn merge_window(&mut self, lo: usize, hi: usize, incoming: &OrderRange, a: usize, b: usize) {
        if a == b {
            return;
        }
        if lo == hi {
            self.make_gap(lo, hi, b - a);
            let mut i = a;
            while i < b {
                self.set(lo + (i - a), incoming.at(i));
                i += 1;
            }
            return;
        }
        // For a single incoming range the window contains exactly its
        // overlapping or adjacent old ranges. Its union is one interval.
        if b - a == 1 {
            let r = incoming.at(a);
            let joined = ClockRange {
                start: self.at(lo).start.min(r.start),
                end: self.at(hi - 1).end.max(r.end),
            };
            self.make_gap(lo, hi, 1);
            self.set(lo, joined);
            return;
        }
        let mut merged: Vec<ClockRange> = Vec::with_capacity((hi - lo) + (b - a));
        let mut old = lo;
        let mut new = a;
        while old < hi || new < b {
            let r = if old == hi {
                let item = incoming.at(new);
                new += 1;
                item
            } else {
                let old_item = self.at(old);
                if new < b {
                    let new_item = incoming.at(new);
                    if new_item.start < old_item.start {
                        new += 1;
                        new_item
                    } else {
                        old += 1;
                        old_item
                    }
                } else {
                    old += 1;
                    old_item
                }
            };
            let n = merged.len();
            if n > 0 && merged[n - 1].end >= r.start {
                merged[n - 1].end = merged[n - 1].end.max(r.end);
            } else {
                merged.push(r);
            }
        }
        let count = merged.len();
        if lo == 0 && hi == self.len as usize && self.buf.len() <= count && self.capacity_hint() <= count {
            self.buf = merged;
            self.head = 0;
            self.len = count as u32;
            return;
        }
        self.make_gap(lo, hi, count);
        let start = physical(self.buf.len(), self.head as usize, lo);
        let first = count.min(self.buf.len() - start);
        self.buf[start..start + first].copy_from_slice(&merged[..first]);
        self.buf[..count - first].copy_from_slice(&merged[first..]);
    }

    fn splice(&mut self, incoming: &OrderRange) {
        let count = incoming.len();
        let first_end = self.at(0).end;
        let mut low = 0;
        while low < count && incoming.at(low).start <= first_end {
            low += 1;
        }
        if low > 0 {
            let reach = incoming.at(low - 1).end;
            let mut joined = 0;
            while joined < self.len as usize && self.at(joined).start <= reach {
                joined += 1;
            }
            self.merge_window(0, joined, incoming, 0, low);
        }
        if low == count {
            return;
        }
        let back_start = self.at(self.len as usize - 1).start;
        let mut high = count;
        while low < high && incoming.at(high - 1).end >= back_start {
            high -= 1;
        }
        if high < count {
            let reach = incoming.at(high).start;
            let mut kept = self.len as usize;
            while kept > 0 && self.at(kept - 1).end >= reach {
                kept -= 1;
            }
            self.merge_window(kept, self.len as usize, incoming, high, count);
        }
        if low == high {
            return;
        }
        let n = self.len as usize;
        let lo = self.lower(incoming.at(low).start);
        let hi = self.upper(incoming.at(high - 1).end, lo);
        let window = (hi - lo) as u64 + (high - low) as u64 + 3 * (lo.min(n - hi) as u64);
        let mut steps = 0;
        let mut span = n;
        while span != 0 {
            steps += 2;
            span /= 2;
        }
        let mut current = n;
        let mut added = 0;
        let mut removed = 0;
        let mut cost = 0u64;
        let mut i = low;
        while i < high && cost <= window {
            let r = incoming.at(i);
            let first = self.lower(r.start);
            let past = self.upper(r.end, first);
            let overlap = past - first;
            let now = (first + added).saturating_sub(removed);
            cost += steps;
            if overlap == 0 {
                cost += now.min(current - now) as u64;
                added += 1;
                current += 1;
            } else if overlap == 1 {
                cost += 1;
            } else {
                // Earlier members of this canonical batch may also have
                // touched the first old range. Include that survivor at now.
                cost += overlap as u64 + (now + 1).min(current - (now + overlap)) as u64;
                removed += overlap - 1;
                current -= overlap - 1;
            }
            i += 1;
        }
        if cost <= window {
            let mut i = low;
            while i < high {
                assert!(self.try_insert(incoming.at(i), MAX_RANGES).is_ok());
                i += 1;
            }
        } else {
            self.merge_window(lo, hi, incoming, low, high);
        }
    }
}

impl OrderRange {
    pub fn from_sorted_disjoint(ranges: Vec<ClockRange>) -> Self {
        Self::from_sorted_disjoint_with_capacity(ranges, 0)
    }

    pub fn from_sorted_disjoint_with_capacity(ranges: Vec<ClockRange>, hint: usize) -> Self {
        assert!(is_canonical(&ranges));
        let len = ranges.len();
        Self::from_prefix(ranges, len, hint)
    }

    // Merge in order into a fresh result. Once a disjoint interval starts,
    // no later input can connect it to the completed prefix. This makes the
    // final count decidable before changing the receiver.
    fn try_union_slices(
        &mut self,
        first: &[ClockRange],
        second: &[ClockRange],
        limit: usize,
    ) -> Result<(), CodecError> {
        let mut result: Vec<ClockRange> = Vec::new();
        let mut old = 0;
        let mut new = 0;
        let n = self.len();
        let count = first.len() + second.len();
        while old < n || new < count {
            let item = if new == count {
                let r = self.at(old);
                old += 1;
                r
            } else {
                let r = if new < first.len() {
                    first[new]
                } else {
                    second[new - first.len()]
                };
                if old < n && self.at(old).start < r.start {
                    let r = self.at(old);
                    old += 1;
                    r
                } else {
                    new += 1;
                    r
                }
            };
            let used = result.len();
            if used > 0 && result[used - 1].end >= item.start {
                result[used - 1].end = result[used - 1].end.max(item.end);
            } else if used == limit {
                return Err(CodecError::LimitExceeded);
            } else {
                result.push(item);
            }
        }
        let len = result.len();
        *self = Self::from_prefix(result, len, 0);
        Ok(())
    }

    fn merge_with_room(&mut self, other: &Self) {
        if <Self as PartialEq>::eq(self, other) {
            return;
        }
        match &other.repr {
            Repr::Single(a) => self.insert(a[0].start, a[0].end),
            Repr::Many(_) => match &mut self.repr {
                Repr::Single(a) => {
                    let old = a[0];
                    *self = other.clone();
                    self.insert(old.start, old.end);
                }
                Repr::Many(r) => {
                    r.splice(other);
                    if r.len == 1 {
                        self.repr = Repr::Single([r.at(0)]);
                    }
                }
            },
        }
    }

    pub fn try_merge_from(&mut self, other: &Self) -> Result<(), CodecError> {
        if other.len() > MAX_RANGES - self.len() {
            let (first, second) = other.as_slices();
            return self.try_union_slices(first, second, MAX_RANGES);
        }
        self.merge_with_room(other);
        Ok(())
    }

    pub fn merge_from(&mut self, other: &Self) {
        assert!(self.try_merge_from(other).is_ok());
    }

    pub fn merge(&mut self, other: &Self) {
        self.merge_from(other);
    }

    pub fn try_merge_owned(&mut self, other: Self) -> Result<(), CodecError> {
        if other.len() > MAX_RANGES - self.len() {
            let (first, second) = other.as_slices();
            return self.try_union_slices(first, second, MAX_RANGES);
        }
        if let Repr::Single(a) = &self.repr {
            let old = a[0];
            *self = other;
            self.insert(old.start, old.end);
        } else {
            self.merge_with_room(&other);
        }
        Ok(())
    }

    pub fn merge_owned(&mut self, other: Self) {
        assert!(self.try_merge_owned(other).is_ok());
    }

    pub fn extend_vec(&mut self, ranges: Vec<ClockRange>) {
        self.extend_vec_with_capacity(ranges, 0);
    }

    pub fn extend_vec_with_capacity(&mut self, ranges: Vec<ClockRange>, hint: usize) {
        assert!(self.try_extend_vec_with_capacity(ranges, hint).is_ok());
    }

    pub fn try_extend_vec_with_capacity(&mut self, ranges: Vec<ClockRange>, hint: usize) -> Result<(), CodecError> {
        self.try_extend_vec_with_limit(ranges, hint, MAX_RANGES)
    }

    /// Apply a caller's fragment limit to the final union. On rejection
    /// the receiver retains its original representation and contents.
    pub fn try_extend_vec_with_limit(
        &mut self,
        mut ranges: Vec<ClockRange>,
        hint: usize,
        limit: usize,
    ) -> Result<(), CodecError> {
        let limit = limit.min(MAX_RANGES);
        if self.len() > limit || ranges.len() > limit - self.len() {
            let kept = canonicalize(&mut ranges);
            return self.try_union_slices(&ranges[..kept], &[], limit);
        }
        match ranges.len() {
            0 => {}
            1 => self.insert(ranges[0].start, ranges[0].end),
            _ => self.merge_owned(Self::from_vec_with_capacity(ranges, hint)),
        }
        Ok(())
    }

    fn diff_one(&self, mut i: usize, r: ClockRange, out: &mut Vec<ClockRange>) -> Option<usize> {
        let mut pos = r.start;
        while i < self.len() && self.at(i).start < r.end {
            let old = self.at(i);
            if old.start < pos || old.end > r.end {
                return None;
            }
            if pos < old.start {
                out.push(ClockRange {
                    start: pos,
                    end: old.start,
                });
            }
            pos = old.end;
            i += 1;
        }
        if pos < r.end {
            out.push(ClockRange { start: pos, end: r.end });
        }
        Some(i)
    }

    /// Return new minus old if new covers old, and the empty list otherwise.
    pub fn diff_range(&self, new: &Self) -> Vec<ClockRange> {
        let mut out = Vec::new();
        let mut i = 0;
        let mut j = 0;
        while j < new.len() {
            match self.diff_one(i, new.at(j), &mut out) {
                None => return Vec::new(),
                Some(next) => i = next,
            }
            j += 1;
        }
        if i < self.len() { Vec::new() } else { out }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equality_compares_contiguous_and_wrapped_runs() {
        fn at_head(head: usize, last_end: u64) -> OrderRange {
            let mut buf = vec![
                ClockRange { start: 1, end: 2 },
                ClockRange { start: 4, end: 5 },
                ClockRange {
                    start: 7,
                    end: last_end,
                },
            ];
            buf.rotate_right(head);
            OrderRange {
                repr: Repr::Many(Ring {
                    buf,
                    head: head as u32,
                    len: 3,
                }),
            }
        }
        for a in 0..3 {
            for b in 0..3 {
                assert_eq!(at_head(a, 8), at_head(b, 8));
                assert_ne!(at_head(a, 8), at_head(b, 9));
            }
        }
    }

    #[test]
    fn full_ring_accepts_unions_and_refuses_a_new_fragment_without_mutation() {
        let lower = ClockRange { start: 1, end: 3 };
        let upper = ClockRange { start: 5, end: 7 };
        let mut ring = Ring {
            buf: vec![upper, lower],
            head: 1,
            len: 2,
        };
        let gap = ClockRange { start: 8, end: 9 };
        assert_eq!(ring.try_insert(gap, 2), Err(CodecError::LimitExceeded));
        assert_eq!(ring.buf, [upper, lower]);
        assert_eq!((ring.head, ring.len), (1, 2));
        assert_eq!(ring.try_insert(lower, 2), Ok(()));
        assert_eq!(ring.try_insert(ClockRange { start: 3, end: 5 }, 2), Ok(()));
        assert_eq!(ring.len, 1);
        assert_eq!(ring.at(0), ClockRange { start: 1, end: 7 });
    }

    #[test]
    fn sorted_overlapping_batch_needs_one_comparison_per_neighbour() {
        let mut v: Vec<_> = (0..24)
            .rev()
            .map(|i| ClockRange {
                start: i / 3,
                end: i + 1,
            })
            .collect();
        v.sort_unstable_by(|a, b| a.start.cmp(&b.start).then(a.end.cmp(&b.end)));
        COMPARISONS.with(|count| count.set(0));
        let r = OrderRange::from_vec(v);
        assert_eq!(r, OrderRange::from_range(0, 24));
        COMPARISONS.with(|count| assert_eq!(count.get(), 23));
    }

    #[test]
    fn ordered_batches_coalesce_and_return_the_original_on_a_late_inversion() {
        let range = |start, end| ClockRange { start, end };
        let mut input = vec![range(1, 3), range(1, 3), range(2, 2), range(2, 7), range(7, 8)];
        let set = OrderRange::try_from_ordered_with_capacity(input.clone(), 0).unwrap();
        assert_eq!(set, OrderRange::from_range(1, 8));

        input.push(range(7, 7));
        input.reserve(10);
        let address = input.as_ptr();
        let capacity = input.capacity();
        let expected = input.clone();
        let returned = OrderRange::try_from_ordered_with_capacity(input, capacity).unwrap_err();
        assert_eq!(returned, expected);
        assert_eq!(returned.as_ptr(), address);
        assert_eq!(returned.capacity(), capacity);
    }

    #[test]
    fn capacity_is_applied_to_the_completed_union() {
        let unit = |start| ClockRange { start, end: start + 1 };
        let mut full = OrderRange::from_vec((1..=8).map(|i| unit(10 * i)).collect());
        assert_eq!(
            full.try_extend_vec_with_limit(vec![unit(0), ClockRange { start: 20, end: 81 }], 0, 8),
            Ok(())
        );
        assert_eq!(
            full,
            OrderRange::from_vec(vec![unit(0), unit(10), ClockRange { start: 20, end: 81 }])
        );
        let mut single = OrderRange::from_range(0, 100);
        assert_eq!(
            single.try_extend_vec_with_limit((0..9).map(|i| unit(2 * i)).collect(), 0, 8),
            Ok(())
        );
        assert_eq!(single, OrderRange::from_range(0, 100));
    }

    #[test]
    fn canonicalize_only_sorts_the_nonempty_prefix() {
        let mut input = Vec::new();
        for i in (0..32).rev() {
            let start = i * 4;
            input.push(ClockRange { start, end: start });
            let valid = ClockRange { start, end: start + 1 };
            input.push(valid);
            input.push(valid);
        }
        let mut expected: Vec<_> = input.iter().copied().filter(|r| r.start < r.end).collect();
        expected.sort_unstable_by_key(|r| (r.start, r.end));
        let kept = nonempty_prefix(&mut input);
        let tail = input[kept..].to_vec();
        sort_prefix(&mut input, kept);
        assert_eq!(input[..kept], expected);
        assert_eq!(input[kept..], tail);
        assert_eq!(canonicalize(&mut input), 32);
    }

    #[test]
    fn canonical_insert_and_merge() {
        let mut r = OrderRange::new();
        r.insert(10, 10);
        assert!(r.is_empty());

        r.insert(20, 30);
        r.insert(0, 10);
        r.insert(12, 15);
        assert_eq!(
            [r.as_slices().0, r.as_slices().1].concat(),
            vec![
                ClockRange { start: 0, end: 10 },
                ClockRange { start: 12, end: 15 },
                ClockRange { start: 20, end: 30 },
            ]
        );
        r.insert(10, 20);
        assert_eq!(r.as_slices().0, vec![ClockRange { start: 0, end: 30 }]);
        assert!(r.contains(0));
        assert!(r.contains(29));
        assert!(!r.contains(30));
    }
}

#[cfg(test)]
#[allow(clippy::single_range_in_vec_init)]
mod splice_tests {
    use std::{collections::VecDeque, ops::Range};

    use super::*;

    fn to_clock(r: Range<u64>) -> ClockRange {
        ClockRange {
            start: r.start,
            end: r.end,
        }
    }

    fn to_core(list: VecDeque<Range<u64>>) -> OrderRange {
        OrderRange::from_sorted_disjoint(list.into_iter().map(to_clock).collect())
    }

    fn to_ranges(range: &OrderRange) -> VecDeque<Range<u64>> {
        let (a, b) = range.as_slices();
        a.iter().chain(b).map(|r| r.start..r.end).collect()
    }

    fn splice_canonical(list: &mut VecDeque<Range<u64>>, batch: Vec<Range<u64>>) {
        let mut value = to_core(std::mem::take(list));
        value.extend_vec(batch.into_iter().map(to_clock).collect());
        *list = to_ranges(&value);
    }

    fn is_canonical(list: &VecDeque<Range<u64>>) -> bool {
        list.iter().all(|r| !r.is_empty()) && list.iter().zip(list.iter().skip(1)).all(|(a, b)| a.end < b.start)
    }

    // Independent reference implementation for the randomized splice oracle.
    fn canonical_vec(input: impl IntoIterator<Item = Range<u64>>) -> Vec<Range<u64>> {
        let mut v: Vec<_> = input.into_iter().filter(|r| !r.is_empty()).collect();
        v.sort_unstable_by_key(|r| (r.start, r.end));
        v.dedup_by(|b, a| {
            if a.end < b.start {
                false
            } else {
                a.end = a.end.max(b.end);
                true
            }
        });
        v
    }

    fn window_cost(lo: usize, hi: usize, n: usize, k: usize) -> usize {
        (hi - lo) + k + 3 * lo.min(n - hi)
    }
    #[test]
    fn test_splice_keeps_ranges_outside_window() {
        let base = || VecDeque::from([0..2, 4..6, 8..10, 12..14, 16..18]);
        let cases = [
            // before, after and between every range
            (
                vec![20..21, 23..24],
                vec![0..2, 4..6, 8..10, 12..14, 16..18, 20..21, 23..24],
            ),
            (vec![18..19, 21..22], vec![0..2, 4..6, 8..10, 12..14, 16..19, 21..22]),
            (vec![2..3, 7..8], vec![0..3, 4..6, 7..10, 12..14, 16..18]),
            (vec![6..7, 10..11], vec![0..2, 4..7, 8..11, 12..14, 16..18]),
            (vec![3..4, 14..16], vec![0..2, 3..6, 8..10, 12..18]),
            (vec![1..3, 5..17], vec![0..3, 4..18]),
        ];
        for (incoming, expected) in cases {
            let mut list = base();
            splice_canonical(&mut list, incoming.clone());
            assert_eq!(list, VecDeque::from(expected), "{incoming:?}");
            assert!(is_canonical(&list));
        }

        let mut list = VecDeque::from([10..12, 14..16]);
        splice_canonical(&mut list, vec![0..1, 3..4]);
        assert_eq!(list, VecDeque::from([0..1, 3..4, 10..12, 14..16]));
    }

    #[test]
    fn test_splice_sparse_batch_keeps_every_range() {
        let base = || (0..64u64).map(|i| i * 4..i * 4 + 1).collect::<VecDeque<_>>();

        // one range joins the lowest, one lands past the highest
        let mut list = base();
        splice_canonical(&mut list, vec![1..2, 1000..1001]);
        let mut expected = base();
        expected[0] = 0..2;
        expected.push_back(1000..1001);
        assert_eq!(list, expected);

        // a new range between two old ones, and one bridging a pair
        let mut list = base();
        splice_canonical(&mut list, vec![2..3, 201..204]);
        let mut expected = base();
        expected.insert(1, 2..3);
        let bridged = expected.iter().position(|r| r.start == 200).unwrap();
        expected[bridged] = 200..205;
        expected.remove(bridged + 1);
        assert_eq!(list, expected);
        assert!(is_canonical(&list));

        // nine ranges inside, same result
        let batch: Vec<_> = (0..9u64).map(|i| i * 24 + 2..i * 24 + 3).collect();
        let mut list = base();
        splice_canonical(&mut list, batch.clone());
        let mut rebuilt: Vec<_> = base().into();
        rebuilt.extend(batch);
        assert_eq!(list, VecDeque::from(canonical_vec(rebuilt)));
    }

    /// Existing ranges moved by `f`, see `MOVED`.
    fn count_moved(f: impl FnOnce()) -> usize {
        super::MOVED.with(|moved| moved.set(0));
        f();
        super::MOVED.with(|moved| moved.get())
    }

    fn spaced(count: u64) -> VecDeque<Range<u64>> {
        (0..count).map(|i| i * 4..i * 4 + 1).collect()
    }

    fn splice_reference(list: &VecDeque<Range<u64>>, incoming: &[Range<u64>]) -> VecDeque<Range<u64>> {
        canonical_vec(list.iter().chain(incoming).cloned()).into()
    }

    #[test]
    fn test_end_batches_leave_middle_in_place() {
        let count = if cfg!(miri) { 64 } else { 4096 };
        let past = count * 4 + 100;
        for high in [1u64, 7, 8, 9, 16, 17, 64] {
            // one range joining the first old range, the rest past the last
            let mut batch = vec![1..2];
            batch.extend((0..high).map(|j| past + 4 * j..past + 4 * j + 1));
            let mut list = spaced(count);
            let expected = splice_reference(&list, &batch);
            let moved = count_moved(|| splice_canonical(&mut list, batch.clone()));
            assert_eq!(list, expected, "1 + {high}");
            // only the first old range is joined
            assert_eq!(moved, 1, "1 + {high}");

            // one range before the first, one joining the last and the rest
            // past it
            let mut list: VecDeque<_> = (1..=count).map(|i| i * 4..i * 4 + 1).collect();
            let back = count * 4;
            let mut batch = vec![0..1, back + 1..back + 2];
            batch.extend((0..high).map(|j| back + 10 + 4 * j..back + 11 + 4 * j));
            let expected = splice_reference(&list, &batch);
            let moved = count_moved(|| splice_canonical(&mut list, batch.clone()));
            assert_eq!(list, expected, "low + {high} high");
            assert!(moved <= 1, "low + {high} high moved {moved}");
        }
    }

    #[test]
    fn test_repeated_end_batches_stay_linear() {
        let batches = if cfg!(miri) { 32 } else { 4000 };
        for high in [8u64, 16] {
            let mut range = OrderRange::new();
            let total = count_moved(|| {
                for i in 0..batches {
                    let mut batch = vec![i..i + 1];
                    batch.extend((0..high).map(|j| (1 << 40) + 4 * (i * high + j)..(1 << 40) + 4 * (i * high + j) + 1));
                    range.extend_vec(batch.into_iter().map(to_clock).collect());
                }
            });
            assert_eq!(range.len() as u64, 1 + batches * high);
            assert!(is_canonical(&to_ranges(&range)));
            // a constant per batch, not the size of the set
            assert!(total <= 4 * batches as usize, "1 + {high}: moved {total}");
        }
    }

    #[test]
    fn test_range_spanning_both_ends_is_merged_once() {
        let base = || spaced(16);
        for batch in [
            vec![0..61],
            vec![0..100],
            vec![2..58],
            vec![0..1, 2..60],
            vec![1..63, 70..71],
            vec![0..1, 2..3, 5..59, 61..62, 80..81],
        ] {
            let mut list = base();
            let expected = splice_reference(&list, &batch);
            let moved = count_moved(|| splice_canonical(&mut list, batch.clone()));
            assert_eq!(list, expected, "{batch:?}");
            assert!(is_canonical(&list), "{batch:?}");
            // at most every old range once, a shift per new range, and the
            // three shifts of the shorter side when rebuilding a window
            assert!(moved <= 16 + batch.len() + 3, "{batch:?} moved {moved}");
        }
        let mut range = to_core(base());
        range.insert(0, 64);
        assert_eq!(range, OrderRange::from_range(0, 64));
    }

    #[test]
    fn test_inside_batches_move_no_more_than_pushing() {
        let count = if cfg!(miri) { 64 } else { 4096 };
        let len = count as usize;
        // sparse: nine new ranges between old ones, spread over the list
        let step = count / 9;
        let sparse: Vec<_> = (0..9).map(|i| (1 + i * step) * 4 + 2..(1 + i * step) * 4 + 3).collect();
        // dense: a new range after every old one in the middle half
        let dense: Vec<_> = (count / 4..count * 3 / 4).map(|i| i * 4 + 2..i * 4 + 3).collect();
        for batch in [sparse, dense] {
            let mut list = spaced(count);
            let expected = splice_reference(&list, &batch);
            let pushing: usize = {
                let mut list = to_core(spaced(count));
                count_moved(|| batch.iter().for_each(|r| list.insert(r.start, r.end)))
            };
            let lo = list.partition_point(|r| r.end < batch[0].start);
            let hi = list.partition_point(|r| r.start <= batch[batch.len() - 1].end);
            let window = window_cost(lo, hi, len, batch.len());
            let moved = count_moved(|| splice_canonical(&mut list, batch.clone()));
            assert_eq!(list, expected);
            // the one-by-one estimate counts each push's binary searches too
            let searches = 2 * (usize::BITS - len.leading_zeros()) as usize * batch.len();
            assert!(
                moved <= window.min(pushing + searches),
                "moved {moved}, pushing {pushing}, window {window}"
            );
            assert!(moved <= 4 * len + batch.len());
        }
    }

    /// What [splice_canonical] may move at most for `batch`: the window
    /// between its lowest and highest range, plus a shift per new range.
    fn window_bound(list: &VecDeque<Range<u64>>, batch: &[Range<u64>]) -> usize {
        let lo = list.partition_point(|r| r.end < batch[0].start);
        let hi = list.partition_point(|r| r.start <= batch[batch.len() - 1].end);
        window_cost(lo, hi, list.len(), batch.len()) + batch.len()
    }

    #[test]
    fn test_one_gap_batch_is_linear() {
        let k = if cfg!(miri) { 32 } else { 2048 };
        let gap = 1 << 40;
        let mut list = VecDeque::from([0..1]);
        list.extend((0..2 * k).map(|i| gap + 4 * i..gap + 4 * i + 1));
        // every new range lands in the gap after the first old one, each next
        // to the one before it
        let batch: Vec<_> = (0..k).map(|i| 10 + 4 * i..10 + 4 * i + 1).collect();
        let expected = splice_reference(&list, &batch);
        let bound = window_bound(&list, &batch);
        let moved = count_moved(|| splice_canonical(&mut list, batch.clone()));
        assert_eq!(list, expected);
        // pushing them one by one would move 1 + 2 + ... + k ranges
        assert!(moved <= bound, "moved {moved}, bound {bound}");
        assert!(moved <= 4 * (k as usize) + 8, "moved {moved}");
    }

    #[test]
    fn test_splice_moves_stay_within_window() {
        const GAP: u64 = 64;
        let mut seed = 0x6a09_e667_f3bc_c908u64;
        let mut next = move |bound: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % bound
        };
        let rounds = if cfg!(miri) { 24 } else { 3000 };
        let mut shapes = [0usize; 4];
        for _ in 0..rounds {
            // old range i at i * GAP, gap g between old g and old g + 1
            let count = 2 + next(if cfg!(miri) { 16 } else { 200 });
            let base: VecDeque<_> = (1..=count).map(|i| i * GAP..i * GAP + 1 + next(2)).collect();
            // 0: one inner gap, 1: two or three inner gaps, 2: inner gaps
            // and the ends, 3: one gap, all touching its old ranges
            let shape = next(4) as usize;
            shapes[shape] += 1;
            let gaps: Vec<u64> = match shape {
                0 | 3 => vec![1 + next(count - 1)],
                1 => (0..2 + next(2)).map(|_| 1 + next(count - 1)).collect(),
                _ => [0, count]
                    .into_iter()
                    .chain((0..1 + next(2)).map(|_| 1 + next(count - 1)))
                    .collect(),
            };
            let mut batch = Vec::new();
            for g in gaps {
                let at = g * GAP;
                if shape == 3 {
                    // joins the old range on the left, or the one on the right
                    batch.push(at + 1..at + 3);
                    batch.push(at + GAP - 1..at + GAP);
                    continue;
                }
                for j in 0..next(31) {
                    batch.push(at + 4 + 2 * j..at + 5 + 2 * j);
                }
                // sometimes touching the old ranges on either side
                if next(2) == 0 {
                    batch.push(at + 2..at + 3);
                }
                if next(2) == 0 && g > 0 {
                    batch.push(at + GAP - 1..at + GAP);
                }
            }
            let batch = canonical_vec(batch);
            if batch.is_empty() {
                continue;
            }
            let mut list = base.clone();
            let expected = splice_reference(&base, &batch);
            let bound = window_bound(&base, &batch);
            let moved = count_moved(|| splice_canonical(&mut list, batch.clone()));
            assert_eq!(list, expected, "{base:?} + {batch:?}");
            let (n, k) = (base.len(), batch.len());
            assert!(moved <= 4 * (n + k), "moved {moved} for {n} + {k}: {batch:?}");
            if shape != 2 {
                assert!(moved <= 2 * bound, "moved {moved}, bound {bound}: {batch:?}");
            }
        }
        assert!(shapes.iter().all(|&count| count > 0), "{shapes:?}");
    }

    #[test]
    fn test_splice_matches_reference_at_ends_and_inside() {
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut next = move |bound: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % bound
        };
        let rounds = if cfg!(miri) { 32 } else { 4000 };
        for _ in 0..rounds {
            let base: Vec<_> = (0..2 + next(20))
                .map(|_| {
                    let start = 20 + next(100);
                    start..start + 1 + next(4)
                })
                .collect();
            let base: VecDeque<_> = canonical_vec(base).into();
            if base.len() < 2 {
                continue;
            }
            // ranges before, inside, after, and across the old ones
            let batch: Vec<_> = (0..next(24))
                .map(|_| {
                    let start = next(150);
                    let long = next(4) == 0;
                    start..start + 1 + next(if long { 120 } else { 5 })
                })
                .collect();
            let batch = canonical_vec(batch);
            let mut list = base.clone();
            splice_canonical(&mut list, batch.clone());
            assert_eq!(list, splice_reference(&base, &batch), "{base:?} + {batch:?}");
        }
    }
}
