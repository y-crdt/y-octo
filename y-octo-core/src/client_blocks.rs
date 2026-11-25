//! The block timeline of one client: the index half of `ClientBlocks` in
//! `y-octo/src/doc/store/client_blocks.rs`.
//!
//! A block ends where its successor starts and the last one ends at
//! `end_clock`, so a block holds no length of its own. The core refuses a
//! zero-length block, as the store of `y-octo` refuses a zero-length struct:
//! clocks are strictly increasing.
//!
//! `y-octo` keeps the timeline of every client in a `ClientBlocksCore` and
//! edits it through the methods below only; the fields cannot be read or
//! written from outside this module.
//!
//! The blocks are kept in a ring: a block is one word of `buf`, the first
//! block is in the slot `head`, and the blocks follow each other from there to
//! the last slot and on from slot 0. A block that is put between two others or
//! taken away moves the blocks on the shorter side of it only, so an edit near
//! either end of a long timeline is cheap. A timeline that only ever grew at
//! its end has `head == 0` and a block in every slot, and grows by
//! `Vec::push`.
//!
//! Every function reads any values of the fields as a timeline (`ring`), so
//! none of them has a precondition on the representation.

use alloc::vec::Vec;

/// A timeline never holds more blocks than a `u32` slot index can name.
pub const MAX_BLOCKS: usize = 4_294_967_295;

/// One more than the largest clock: a word is the clock of a block plus this
/// many times its kind.
const CLOCKS: u128 = 18_446_744_073_709_551_616;

/// One more than the largest slot: the kind of an item block is its tag plus
/// this many times the slot of its item.
const SLOTS: u64 = 4_294_967_296;

/// A full ring takes on this many slots at least.
/// Up to this many blocks, a run of blocks moves up a block at a time
/// (`push_up_few`): a pass is one `memmove`.
const FEW_PASSES: usize = 4;

const MORE_SLOTS: usize = 64;

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum StoreError {
    ZeroLength,
    ClockMismatch,
    ClockOverflow,
    MissingStruct,
    NotAnItem,
    InvalidSplit,
    InvalidOrigin,
    NotMergeable,
    Capacity,
}

/// What a block of the timeline is: an item of the arena (live or deleted),
/// a collected range, or a gap of an update.
#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum BlockKindCore {
    Item(u32),
    DeletedItem(u32),
    Gc,
    Skip,
}

impl BlockKindCore {
    /// Everything but a live item counts as deleted.
    #[inline]
    pub fn deleted(self) -> bool {
        match self {
            BlockKindCore::Item(_) => false,
            BlockKindCore::DeletedItem(_) => true,
            BlockKindCore::Gc => true,
            BlockKindCore::Skip => true,
        }
    }

    /// The arena slot of an item block.
    #[inline]
    pub fn item(self) -> Option<u32> {
        match self {
            BlockKindCore::Item(idx) => Some(idx),
            BlockKindCore::DeletedItem(idx) => Some(idx),
            BlockKindCore::Gc => None,
            BlockKindCore::Skip => None,
        }
    }

    /// Whether two neighbours of a timeline are of the same kind
    /// (`merge_with_lefts` of `y-octo`): only those can become one block.
    #[inline]
    pub fn same_kind(self, other: BlockKindCore) -> bool {
        match self {
            BlockKindCore::Item(_) => match other {
                BlockKindCore::Item(_) => true,
                BlockKindCore::DeletedItem(_) => false,
                BlockKindCore::Gc => false,
                BlockKindCore::Skip => false,
            },
            BlockKindCore::DeletedItem(_) => match other {
                BlockKindCore::Item(_) => false,
                BlockKindCore::DeletedItem(_) => true,
                BlockKindCore::Gc => false,
                BlockKindCore::Skip => false,
            },
            BlockKindCore::Gc => match other {
                BlockKindCore::Item(_) => false,
                BlockKindCore::DeletedItem(_) => false,
                BlockKindCore::Gc => true,
                BlockKindCore::Skip => false,
            },
            BlockKindCore::Skip => match other {
                BlockKindCore::Item(_) => false,
                BlockKindCore::DeletedItem(_) => false,
                BlockKindCore::Gc => false,
                BlockKindCore::Skip => true,
            },
        }
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct BlockRefCore {
    pub clock: u64,
    pub kind: BlockKindCore,
}

/// The number a kind is kept as: its tag, and for an item block `SLOTS` times
/// the slot of its item.
#[inline]
fn kind_code(kind: BlockKindCore) -> u64 {
    match kind {
        BlockKindCore::Item(slot) => (slot as u64) * SLOTS,
        BlockKindCore::DeletedItem(slot) => (slot as u64) * SLOTS + 1,
        BlockKindCore::Gc => 2,
        BlockKindCore::Skip => 3,
    }
}

/// The word of a block: its clock below `CLOCKS` and its kind above. The
/// blocks are kept as words because a run of words is moved by one slot as
/// fast as memory is copied (`slide_up`, `slide_down`).
#[inline]
fn pack(block: BlockRefCore) -> u128 {
    (kind_code(block.kind) as u128) * CLOCKS + (block.clock as u128)
}

/// The clock of the block of a word.
#[inline]
pub fn clock_of(word: u128) -> u64 {
    (word % CLOCKS) as u64
}

/// The kind of the block of a word. Every word is the word of a block: a tag
/// above 2 reads as a gap.
#[inline]
fn kind_of(word: u128) -> BlockKindCore {
    let kind = (word / CLOCKS) as u64;
    let slot = (kind / SLOTS) as u32;
    let tag = kind % SLOTS;
    if tag == 0 {
        BlockKindCore::Item(slot)
    } else if tag == 1 {
        BlockKindCore::DeletedItem(slot)
    } else if tag == 2 {
        BlockKindCore::Gc
    } else {
        BlockKindCore::Skip
    }
}

/// The block of a word: `unpack(pack(block))` is `block`.
#[inline]
pub fn unpack(word: u128) -> BlockRefCore {
    BlockRefCore {
        clock: clock_of(word),
        kind: kind_of(word),
    }
}

/// The slot of the block `index` of a ring of `cap` slots whose first block
/// is in the slot `head`, `head <= cap` and `index < cap`.
#[inline]
fn slot_of(cap: usize, head: usize, index: usize) -> usize {
    let tail = cap - head;
    if index < tail { head + index } else { index - tail }
}

/// The slot before the slot `head` of a ring of `cap` slots, `head < cap`.
#[inline]
fn slot_before(cap: usize, head: usize) -> usize {
    if head == 0 { cap - 1 } else { head - 1 }
}

#[inline]
fn at_most(n: usize, most: usize) -> usize {
    if n > most { most } else { n }
}

#[inline]
fn at_least(n: usize, least: usize) -> usize {
    if n < least { least } else { n }
}

/// The words of a slice move up by one: `words[1..]` becomes what
/// `words[..len - 1]` was, and the first word stays.
///
/// Kept out of line and in this shape the loop is compiled to one `memmove`.
/// Inlined into its caller, or over blocks instead of words, it is compiled
/// to a load and a store per block: more than twice the instructions.
#[inline(never)]
fn slide_up(words: &mut [u128]) {
    if words.is_empty() {
        return;
    }
    let mut j = words.len() - 1;
    while j > 0 {
        words[j] = words[j - 1];
        j -= 1;
    }
}

/// The words of a slice move down by one: `words[..len - 1]` becomes what
/// `words[1..]` was, and the last word stays. One `memmove`, as `slide_up`.
#[inline(never)]
fn slide_down(words: &mut [u128]) {
    if words.is_empty() {
        return;
    }
    let stop = words.len() - 1;
    let mut i = 0;
    while i < stop {
        words[i] = words[i + 1];
        i += 1;
    }
}

/// How many of the words, whose blocks follow each other on the timeline,
/// are of a block that starts at or before `clock`.
#[inline]
fn count_before(words: &[u128], clock: u64) -> usize {
    let mut lo = 0;
    let mut hi = words.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if clock_of(words[mid]) <= clock {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

/// The tag of the kind of a word, where every tag above 2 is the gap's.
#[inline]
fn tag_of(word: u128) -> u64 {
    let tag = ((word / CLOCKS) as u64) % SLOTS;
    if tag > 3 { 3 } else { tag }
}

/// Whether the blocks of two words are of the same kind: `same_kind` of what
/// `kind_of` reads, without reading it.
#[inline]
fn same_kind_words(a: u128, b: u128) -> bool {
    tag_of(a) == tag_of(b)
}

/// Whether the block of a word is anything but a live item.
#[inline]
pub fn deleted_word(word: u128) -> bool {
    tag_of(word) != 0
}

/// The slots a ring of `cap` slots, `cap < MAX_BLOCKS`, can take on within
/// the allocation behind it, whose size is the next power of two: a ring that
/// takes on no more never asks for memory before a deque of the same blocks
/// would.
fn room(cap: usize) -> usize {
    let mut size: usize = 4;
    while size <= cap && size <= MAX_BLOCKS / 2 {
        size *= 2;
    }
    if size > cap { size - cap } else { MAX_BLOCKS - cap }
}

/// How many slots a full ring of `cap` slots, `cap < MAX_BLOCKS`, takes on:
/// as many as the blocks it moves for them (`wrapped`) and `MORE_SLOTS` at
/// least, so that the moves of a growing ring stay within a constant per
/// block; and no more than the allocation has room for.
fn growth(cap: usize, wrapped: usize) -> usize {
    at_most(at_least(wrapped, MORE_SLOTS), room(cap))
}

/// Where slot `slot` of a compacted arena went: `moved[slot]` is one more than
/// its new slot, and `0` for a slot that held no item.
fn moved_slot(moved: &[u32], slot: u32) -> Option<u32> {
    let at = slot as usize;
    if at >= moved.len() {
        return None;
    }
    let to = moved[at];
    if to == 0 { None } else { Some(to - 1) }
}

/// The kind of a block once the slots moved: an item block names the slot
/// `moved` gives for its item, if it gives one.
fn moved_kind(moved: &[u32], kind: BlockKindCore) -> BlockKindCore {
    match kind {
        BlockKindCore::Item(slot) => match moved_slot(moved, slot) {
            Some(to) => BlockKindCore::Item(to),
            None => kind,
        },
        BlockKindCore::DeletedItem(slot) => match moved_slot(moved, slot) {
            Some(to) => BlockKindCore::DeletedItem(to),
            None => kind,
        },
        BlockKindCore::Gc => kind,
        BlockKindCore::Skip => kind,
    }
}

#[cfg_attr(not(aeneas_extract), derive(Clone, Debug))]
pub struct ClientBlocksCore {
    /// The slots of the ring, a word a block.
    buf: Vec<u128>,
    /// The slot of the first block.
    head: u32,
    /// The number of blocks.
    len: u32,
    end_clock: u64,
}

impl Default for ClientBlocksCore {
    fn default() -> Self {
        Self::new()
    }
}

impl ClientBlocksCore {
    pub fn new() -> Self {
        Self {
            buf: Vec::new(),
            head: 0,
            len: 0,
            end_clock: 0,
        }
    }

    /// The ring as every function reads it: the slots it has, the slot of its
    /// first block and the number of its blocks. A ring has `MAX_BLOCKS`
    /// slots at most, its first block is in one of them, and it has no more
    /// blocks than slots: fields that say otherwise are read as the nearest
    /// ring that does not.
    #[inline]
    fn ring(&self) -> (usize, usize, usize) {
        let cap = at_most(self.buf.len(), MAX_BLOCKS);
        let head = self.head as usize;
        let len = at_most(self.len as usize, cap);
        if head < cap { (cap, head, len) } else { (cap, 0, len) }
    }

    /// Where the last block ends: the next clock of the client.
    #[inline]
    pub fn end_clock(&self) -> u64 {
        self.end_clock
    }

    /// The number of blocks: no more than there are slots (`len` itself is
    /// no more than `MAX_BLOCKS`).
    #[inline]
    pub fn len(&self) -> usize {
        at_most(self.len as usize, self.buf.len())
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The block at `index`.
    #[inline]
    pub fn get(&self, index: usize) -> Option<BlockRefCore> {
        match self.word_at(index) {
            Some(word) => Some(unpack(word)),
            None => None,
        }
    }

    /// The slot of the block at `index`.
    #[inline]
    fn slot_at(&self, index: usize) -> Option<usize> {
        if self.head == 0 {
            if index >= self.len as usize || index >= self.buf.len() {
                return None;
            }
            return Some(index);
        }
        let (cap, head, len) = self.ring();
        if index >= len {
            return None;
        }
        Some(slot_of(cap, head, index))
    }

    /// The clock the block at `index` starts at.
    #[inline]
    pub fn clock_at(&self, index: usize) -> Option<u64> {
        match self.word_at(index) {
            Some(word) => Some(clock_of(word)),
            None => None,
        }
    }

    /// The block at `index` for a caller that knows it to be there
    /// (`yata_store` has the index from `find` or below `len`): past the
    /// last block it answers a gap at clock 0, so that this is a total
    /// function.
    #[inline]
    pub(crate) fn block_at(&self, index: usize) -> BlockRefCore {
        match self.get(index) {
            Some(block) => block,
            None => BlockRefCore {
                clock: 0,
                kind: BlockKindCore::Skip,
            },
        }
    }

    /// Whether a block that starts at `clock` continues the timeline: the
    /// first block may start at any clock.
    #[inline]
    pub fn continues(&self, clock: u64) -> bool {
        if self.is_empty() { true } else { clock == self.end_clock }
    }

    /// `continues` for a caller that has the number of blocks.
    #[inline]
    fn follows(&self, blocks: usize, clock: u64) -> bool {
        if blocks == 0 { true } else { clock == self.end_clock }
    }

    /// Makes room in a full ring, `len == cap == buf.len() < MAX_BLOCKS`: it
    /// takes on slots at its end. Unless the blocks are in the order of the
    /// slots (`head == 0`), the blocks from the slot `head` to the end, which
    /// are the first blocks of the timeline, move up behind the new slots.
    /// Returns the slots the ring has now and the slot of its first block.
    fn grow(&mut self, cap: usize, head: usize) -> (usize, usize) {
        if head == 0 {
            let slots = cap + growth(cap, 0);
            self.buf.resize(slots, 0);
            self.head = 0;
            (slots, 0)
        } else {
            let more = growth(cap, cap - head);
            let slots = cap + more;
            self.buf.resize(slots, 0);
            // from the last block down: a word is read before its slot is
            // written
            let mut from = cap;
            while from > head {
                from -= 1;
                let word = self.buf[from];
                self.buf[from + more] = word;
            }
            let head = head + more;
            self.head = head as u32;
            (slots, head)
        }
    }

    /// A ring with a free slot: the ring itself, or the ring it grows to when
    /// every one of its slots holds a block (`len == cap`). Returns its slots
    /// and the slot of its first block.
    fn make_room(&mut self, cap: usize, head: usize, len: usize) -> (usize, usize) {
        if len == cap { self.grow(cap, head) } else { (cap, head) }
    }

    /// Puts `word` in as the block after the `len` blocks of the ring,
    /// `len < MAX_BLOCKS`.
    #[inline]
    fn put_last(&mut self, cap: usize, head: usize, len: usize, word: u128) {
        if len < cap {
            let slot = slot_of(cap, head, len);
            self.buf[slot] = word;
        } else if head == 0 {
            // a block in every slot, in the order of the slots
            self.buf.push(word);
            self.head = 0;
        } else {
            let (cap, head) = self.grow(cap, head);
            let slot = slot_of(cap, head, len);
            self.buf[slot] = word;
        }
    }

    /// Appends a block of `len` clocks. The first block of a timeline may
    /// start at any clock; every other one has to continue the timeline.
    #[inline]
    pub fn append(&mut self, block: BlockRefCore, len: u64) -> Result<(), StoreError> {
        if len == 0 {
            return Err(StoreError::ZeroLength);
        }
        if self.head == 0 {
            let slots = self.buf.len();
            let blocks = at_most(self.len as usize, slots);
            if !self.follows(blocks, block.clock) {
                return Err(StoreError::ClockMismatch);
            }
            if len > u64::MAX - block.clock {
                return Err(StoreError::ClockOverflow);
            }
            if blocks >= MAX_BLOCKS {
                return Err(StoreError::Capacity);
            }
            if blocks < slots {
                self.buf[blocks] = pack(block);
            } else {
                self.buf.push(pack(block));
            }
            self.len = (blocks + 1) as u32;
            self.end_clock = block.clock + len;
            return Ok(());
        }
        let (cap, head, blocks) = self.ring();
        if !self.follows(blocks, block.clock) {
            return Err(StoreError::ClockMismatch);
        }
        if len > u64::MAX - block.clock {
            return Err(StoreError::ClockOverflow);
        }
        if blocks >= MAX_BLOCKS {
            return Err(StoreError::Capacity);
        }
        self.put_last(cap, head, blocks, pack(block));
        self.len = (blocks + 1) as u32;
        self.end_clock = block.clock + len;
        Ok(())
    }

    /// The clocks `start..end` of the block at `index`.
    #[inline]
    pub fn range(&self, index: usize) -> Option<(u64, u64)> {
        match self.word_end_at(index) {
            Some((word, end)) => Some((clock_of(word), end)),
            None => None,
        }
    }

    /// The words of the blocks in the order of the timeline: those of the
    /// first slice, then those of the second. `unpack` and `clock_of` read a
    /// word.
    #[inline]
    pub fn words(&self) -> (&[u128], &[u128]) {
        if self.head == 0 {
            let len = self.len();
            return (&self.buf[0..len], &self.buf[0..0]);
        }
        let (cap, head, len) = self.ring();
        let tail = cap - head;
        if len > tail {
            (&self.buf[head..cap], &self.buf[0..len - tail])
        } else {
            (&self.buf[head..head + len], &self.buf[0..0])
        }
    }

    /// The first of the slots `low..high`, `low <= high <= buf.len()`, whose
    /// block starts after `clock`, and `high` when none does: the blocks of
    /// these slots follow each other on the timeline.
    #[inline]
    fn first_after(&self, clock: u64, low: usize, high: usize) -> usize {
        low + count_before(&self.buf[low..high], clock)
    }

    /// The slots to look for the block of `clock` in, `low..high`, and the
    /// number of blocks before them: the blocks from `cap - head` on are in
    /// the slots from 0, the ones before them in the slots from `head`.
    #[inline]
    fn span(&self, clock: u64, cap: usize, head: usize, len: usize) -> (usize, usize, usize) {
        let tail = cap - head;
        if len > tail {
            if clock_of(self.buf[0]) <= clock {
                (0, len - tail, tail)
            } else {
                (head, cap, 0)
            }
        } else {
            (head, head + len, 0)
        }
    }

    /// How many blocks of a timeline in the order of its slots start at or
    /// before `clock`, of its `len` blocks.
    #[inline]
    fn plain_before(&self, len: usize, clock: u64) -> usize {
        if len > 0 && clock_of(self.buf[len - 1]) <= clock {
            return len;
        }
        count_before(&self.buf[0..len], clock)
    }

    /// Index of the block that holds `clock`: the last block that starts at
    /// or before it.
    #[inline]
    pub fn find(&self, clock: u64) -> Option<usize> {
        if clock >= self.end_clock {
            return None;
        }
        if self.head == 0 {
            let after = self.plain_before(self.len(), clock);
            return if after == 0 { None } else { Some(after - 1) };
        }
        let (cap, head, len) = self.ring();
        self.locate(cap, head, len, clock)
    }

    /// `find` on the ring as `ring` reads it, for a clock before the end of
    /// the timeline.
    #[inline]
    fn locate(&self, cap: usize, head: usize, len: usize, clock: u64) -> Option<usize> {
        if len == 0 {
            return None;
        }
        let last = len - 1;
        if clock_of(self.buf[slot_of(cap, head, last)]) <= clock {
            return Some(last);
        }
        let (low, high, before) = self.span(clock, cap, head, len);
        let after = self.first_after(clock, low, high);
        if after == low {
            None
        } else {
            Some(before + (after - low) - 1)
        }
    }

    /// The word of the block at `index` and the clock the block ends at;
    /// `unpack` reads the word.
    #[inline]
    pub fn word_end_at(&self, index: usize) -> Option<(u128, u64)> {
        if self.head == 0 {
            let len = self.len();
            if index >= len {
                return None;
            }
            let word = self.buf[index];
            let next = index + 1;
            if next < len {
                return Some((word, clock_of(self.buf[next])));
            }
            return Some((word, self.end_clock));
        }
        let (cap, head, len) = self.ring();
        if index >= len {
            return None;
        }
        let word = self.buf[slot_of(cap, head, index)];
        let next = index + 1;
        if next < len {
            Some((word, clock_of(self.buf[slot_of(cap, head, next)])))
        } else {
            Some((word, self.end_clock))
        }
    }

    /// The word of the block at `index`; `unpack` reads it.
    #[inline]
    pub fn word_at(&self, index: usize) -> Option<u128> {
        match self.slot_at(index) {
            Some(slot) => Some(self.buf[slot]),
            None => None,
        }
    }

    /// The words of the blocks `a..b` of the ring move to the next block
    /// each, `a <= b < cap`: the blocks `a + 1..=b` become what the blocks
    /// `a..b` were, and every other slot stays.
    fn move_up(&mut self, cap: usize, head: usize, a: usize, b: usize) {
        let tail = cap - head;
        if b < tail {
            slide_up(&mut self.buf[head + a..head + b + 1]);
        } else if a >= tail {
            slide_up(&mut self.buf[a - tail..b - tail + 1]);
        } else {
            // the blocks from `tail` on are in the slots from 0
            slide_up(&mut self.buf[0..b - tail + 1]);
            let word = self.buf[cap - 1];
            self.buf[0] = word;
            slide_up(&mut self.buf[head + a..cap]);
        }
    }

    /// The words of the blocks `a + 1..=b` of the ring move to the block
    /// before each, `a <= b < cap`: the blocks `a..b` become what the blocks
    /// `a + 1..=b` were, and every other slot stays.
    fn move_down(&mut self, cap: usize, head: usize, a: usize, b: usize) {
        let tail = cap - head;
        if b < tail {
            slide_down(&mut self.buf[head + a..head + b + 1]);
        } else if a >= tail {
            slide_down(&mut self.buf[a - tail..b - tail + 1]);
        } else {
            slide_down(&mut self.buf[head + a..cap]);
            let word = self.buf[0];
            self.buf[cap - 1] = word;
            slide_down(&mut self.buf[0..b - tail + 1]);
        }
    }

    /// Puts `word` in as the block `at` of the `len` blocks, `at <= len`:
    /// the blocks from `at` on move up.
    fn put_moving_up(&mut self, cap: usize, head: usize, len: usize, at: usize, word: u128) {
        let (cap, head) = self.make_room(cap, head, len);
        self.move_up(cap, head, at, len);
        let slot = slot_of(cap, head, at);
        self.buf[slot] = word;
    }

    /// Puts `word` in as the block `at` of the `len` blocks, `at <= len`:
    /// the ring starts a slot earlier, and the blocks before `at` move down
    /// into it.
    fn put_moving_down(&mut self, cap: usize, head: usize, len: usize, at: usize, word: u128) {
        let (cap, head) = self.make_room(cap, head, len);
        let head = slot_before(cap, head);
        self.head = head as u32;
        self.move_down(cap, head, 0, at);
        let slot = slot_of(cap, head, at);
        self.buf[slot] = word;
    }

    /// Puts `word` in as the block `at` of the `len` blocks,
    /// `0 < at <= len < MAX_BLOCKS`: the blocks on the shorter side of it
    /// make room. A ring with a block in every slot and the blocks in the
    /// order of the slots stays one when the blocks after `at` are the
    /// shorter side.
    #[inline]
    fn put(&mut self, cap: usize, head: usize, len: usize, at: usize, word: u128) {
        let after = len - at;
        if after > at {
            self.put_moving_down(cap, head, len, at, word);
        } else if len < cap {
            self.put_moving_up(cap, head, len, at, word);
        } else if head == 0 {
            // a block in every slot, in the order of the slots
            if after == 0 {
                self.buf.push(word);
            } else {
                self.buf.insert(at, word);
            }
            self.head = 0;
        } else {
            self.put_moving_up(cap, head, len, at, word);
        }
    }

    /// Splits the block at `index` in two at `clock`, which has to lie
    /// strictly inside it; the new right half is of kind `kind`. The blocks
    /// on the shorter side of the new block make room for it.
    #[inline]
    pub fn split_boundary(&mut self, index: usize, clock: u64, kind: BlockKindCore) -> Result<(), StoreError> {
        let (start, end) = match self.range(index) {
            Some(range) => range,
            None => return Err(StoreError::MissingStruct),
        };
        if clock <= start || clock >= end {
            return Err(StoreError::InvalidSplit);
        }
        let (cap, head, len) = self.ring();
        if len >= MAX_BLOCKS {
            return Err(StoreError::Capacity);
        }
        self.put(cap, head, len, index + 1, pack(BlockRefCore { clock, kind }));
        self.len = (len + 1) as u32;
        Ok(())
    }

    /// Whether every two neighbours among the blocks `first..=last`,
    /// `last < len`, are of the same kind.
    fn same_kind_run(&self, cap: usize, head: usize, first: usize, last: usize) -> bool {
        // the tag of the first block, and every block after it has the same
        let tag = tag_of(self.buf[slot_of(cap, head, first)]);
        let mut i = first;
        while i < last {
            i += 1;
            if tag_of(self.buf[slot_of(cap, head, i)]) != tag {
                return false;
            }
        }
        true
    }

    /// The words of the blocks `from..len` move `gap` blocks down each,
    /// `gap <= from` and `len <= cap`, the first of them first.
    fn pull_down(&mut self, cap: usize, head: usize, from: usize, len: usize, gap: usize) {
        let mut i = from;
        while i < len {
            let word = self.buf[slot_of(cap, head, i)];
            let slot = slot_of(cap, head, i - gap);
            self.buf[slot] = word;
            i += 1;
        }
    }

    /// The words of the blocks `0..count` move `gap` blocks up each,
    /// `count + gap <= cap`, the last of them first.
    fn push_up(&mut self, cap: usize, head: usize, count: usize, gap: usize) {
        let mut i = count;
        while i > 0 {
            i -= 1;
            let word = self.buf[slot_of(cap, head, i)];
            let slot = slot_of(cap, head, i + gap);
            self.buf[slot] = word;
        }
    }

    /// `push_up` for a small `gap`, a block at a time: `gap` passes, each as
    /// fast as memory is copied. The slots of the first `gap` blocks are left
    /// with what the passes put there.
    fn push_up_few(&mut self, cap: usize, head: usize, count: usize, gap: usize) {
        let mut pass = 0;
        while pass < gap {
            self.move_up(cap, head, pass, count + pass);
            pass += 1;
        }
    }

    /// Takes the `gap` blocks before the block `from` away, `gap <= from` and
    /// `from <= len`: the blocks from `from` on move down.
    fn close_from_end(&mut self, cap: usize, head: usize, len: usize, from: usize, gap: usize) {
        if from == len {
            // the last blocks of the timeline: nothing moves
        } else if gap == 1 {
            self.move_down(cap, head, from - 1, len - 1);
        } else {
            self.pull_down(cap, head, from, len, gap);
        }
    }

    /// Takes the `gap` blocks after the first `count` blocks away,
    /// `count + gap <= len`: the first `count` blocks move up, and the ring
    /// starts where the first of them is now.
    fn close_from_start(&mut self, cap: usize, head: usize, count: usize, gap: usize) {
        if gap <= FEW_PASSES {
            self.push_up_few(cap, head, count, gap);
        } else {
            self.push_up(cap, head, count, gap);
        }
        let head = slot_of(cap, head, gap);
        self.head = head as u32;
    }

    /// Takes the blocks `first + 1..=last` away, `first < last < len`: the
    /// blocks on the shorter side of them close the gap.
    #[inline]
    fn close(&mut self, cap: usize, head: usize, len: usize, first: usize, last: usize) {
        let after = len - 1 - last;
        if after <= first {
            self.close_from_end(cap, head, len, last + 1, last - first);
        } else {
            self.close_from_start(cap, head, first + 1, last - first);
        }
    }

    /// Makes the blocks `first..=last` one block of the kind of the first
    /// (`merge_with_lefts` of `y-octo`): every two neighbours among them have
    /// to be of the same kind. `first == last` changes nothing. The blocks on
    /// the shorter side of the run close the gap, and nothing is allocated.
    #[inline]
    pub fn merge_range(&mut self, first: usize, last: usize) -> Result<(), StoreError> {
        if first > last {
            return Err(StoreError::MissingStruct);
        }
        if self.last_two(first, last) {
            self.merge_last_two(first, last)
        } else {
            self.merge_run(first, last)
        }
    }

    /// Whether the blocks `first <= last` are the last two blocks of a
    /// timeline in the order of its slots: what typing merges.
    #[inline]
    fn last_two(&self, first: usize, last: usize) -> bool {
        if self.head != 0 {
            return false;
        }
        let len = self.len();
        if last >= len || last - first != 1 {
            return false;
        }
        len - last == 1
    }

    /// `merge_range` of the last two blocks of a timeline in the order of
    /// its slots (`last_two`): nothing moves.
    #[inline]
    fn merge_last_two(&mut self, first: usize, last: usize) -> Result<(), StoreError> {
        if !same_kind_words(self.buf[first], self.buf[last]) {
            return Err(StoreError::NotMergeable);
        }
        self.len = last as u32;
        Ok(())
    }

    /// `merge_range` of any blocks `first <= last`.
    #[inline]
    fn merge_run(&mut self, first: usize, last: usize) -> Result<(), StoreError> {
        let (cap, head, len) = self.ring();
        if last >= len {
            return Err(StoreError::MissingStruct);
        }
        if !self.same_kind_run(cap, head, first, last) {
            return Err(StoreError::NotMergeable);
        }
        if first < last {
            self.close(cap, head, len, first, last);
            self.len = (len - (last - first)) as u32;
        }
        Ok(())
    }

    /// Makes the blocks at `index` and `index + 1` one block of the kind of
    /// the first; they have to be of the same kind.
    pub fn merge_adjacent(&mut self, index: usize) -> Result<(), StoreError> {
        if index >= self.len() {
            return Err(StoreError::MissingStruct);
        }
        self.merge_range(index, index + 1)
    }

    /// Whether `moved` names a new slot for the item of every item block.
    fn slots_moved(&self, cap: usize, head: usize, len: usize, moved: &[u32]) -> bool {
        let mut i = 0usize;
        while i < len {
            match kind_of(self.buf[slot_of(cap, head, i)]).item() {
                Some(slot) => match moved_slot(moved, slot) {
                    Some(_) => {}
                    None => return false,
                },
                None => {}
            }
            i += 1;
        }
        true
    }

    /// Gives every item block the slot `moved` names for its item.
    fn rename_slots(&mut self, cap: usize, head: usize, len: usize, moved: &[u32]) {
        let mut i = 0usize;
        while i < len {
            let slot = slot_of(cap, head, i);
            let block = unpack(self.buf[slot]);
            self.buf[slot] = pack(BlockRefCore {
                clock: block.clock,
                kind: moved_kind(moved, block.kind),
            });
            i += 1;
        }
    }

    /// Renames the slots of the item blocks after the arena was compacted
    /// (`ItemSpace::finish` of `y-octo`): `moved[slot]` is one more than the
    /// slot that `slot` moved to, and `0` for a slot that held no item. A
    /// block of such a slot, or of one past the end of `moved`, is refused and
    /// nothing is changed. A block keeps its clock and whether it is deleted.
    pub fn remap_slots(&mut self, moved: &[u32]) -> Result<(), StoreError> {
        let (cap, head, len) = self.ring();
        if !self.slots_moved(cap, head, len, moved) {
            return Err(StoreError::MissingStruct);
        }
        self.rename_slots(cap, head, len, moved);
        Ok(())
    }

    /// Marks the item block at `index` deleted.
    #[inline]
    pub fn mark_deleted(&mut self, index: usize) -> Result<(), StoreError> {
        let slot = match self.slot_at(index) {
            Some(slot) => slot,
            None => return Err(StoreError::MissingStruct),
        };
        let block = unpack(self.buf[slot]);
        match block.kind {
            BlockKindCore::Item(idx) => {
                self.buf[slot] = pack(BlockRefCore {
                    clock: block.clock,
                    kind: BlockKindCore::DeletedItem(idx),
                });
                Ok(())
            }
            BlockKindCore::DeletedItem(_) => Ok(()),
            BlockKindCore::Gc => Err(StoreError::NotAnItem),
            BlockKindCore::Skip => Err(StoreError::NotAnItem),
        }
    }

    /// Replaces the deleted item block at `index` by a collected range and
    /// returns the slot it held. A live item is not collected.
    #[inline]
    pub fn mark_gc(&mut self, index: usize) -> Result<u32, StoreError> {
        let slot = match self.slot_at(index) {
            Some(slot) => slot,
            None => return Err(StoreError::MissingStruct),
        };
        let block = unpack(self.buf[slot]);
        match block.kind {
            BlockKindCore::DeletedItem(idx) => {
                self.buf[slot] = pack(BlockRefCore {
                    clock: block.clock,
                    kind: BlockKindCore::Gc,
                });
                Ok(idx)
            }
            BlockKindCore::Item(_) => Err(StoreError::NotAnItem),
            BlockKindCore::Gc => Err(StoreError::NotAnItem),
            BlockKindCore::Skip => Err(StoreError::NotAnItem),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use super::*;

    /// Two timelines are equal when they hold the same blocks and end at the
    /// same clock, wherever in their rings the blocks are. Only the tests
    /// compare timelines.
    impl PartialEq for ClientBlocksCore {
        fn eq(&self, other: &Self) -> bool {
            self.end_clock == other.end_clock
                && self.len() == other.len()
                && (0..self.len()).all(|index| self.get(index) == other.get(index))
        }
    }

    fn block(clock: u64, kind: BlockKindCore) -> BlockRefCore {
        BlockRefCore { clock, kind }
    }

    fn blocks_of(timeline: &ClientBlocksCore) -> Vec<BlockRefCore> {
        (0..timeline.len()).map(|index| timeline.get(index).unwrap()).collect()
    }

    #[test]
    fn a_timeline_is_40_bytes() {
        if size_of::<usize>() == 8 {
            assert_eq!(size_of::<ClientBlocksCore>(), 40);
        }
        assert_eq!(size_of::<BlockRefCore>(), 16);
    }

    #[test]
    fn words_are_blocks_and_back() {
        use BlockKindCore::{DeletedItem, Gc, Item, Skip};
        for clock in [
            0,
            1,
            7,
            u64::from(u32::MAX),
            u64::from(u32::MAX) + 1,
            u64::MAX - 1,
            u64::MAX,
        ] {
            for kind in [
                Item(0),
                Item(1),
                Item(u32::MAX - 1),
                Item(u32::MAX),
                DeletedItem(0),
                DeletedItem(9),
                DeletedItem(u32::MAX),
                Gc,
                Skip,
            ] {
                let word = pack(block(clock, kind));
                assert_eq!(unpack(word), block(clock, kind));
                assert_eq!(clock_of(word), clock);
                assert_eq!(kind_of(word), kind);
            }
        }
        // the layout: the clock in the low half, the tag and the slot above
        assert_eq!(pack(block(5, Item(0))), 5);
        assert_eq!(pack(block(5, DeletedItem(3))), 5 | (1 << 64) | (3 << 96));
        assert_eq!(pack(block(u64::MAX, Gc)), u128::from(u64::MAX) | (2 << 64));
        assert_eq!(pack(block(0, Skip)), 3 << 64);
        // every word is the word of a block
        for word in [0, u128::MAX, 4 << 64, (u128::from(u32::MAX) << 64) | 9, 1 << 127] {
            let read = unpack(word);
            assert_eq!(read.clock, word as u64);
            assert_eq!(pack(read) as u64, word as u64);
            assert_eq!(unpack(pack(read)), read);
        }
        assert_eq!(unpack(u128::MAX), block(u64::MAX, Skip));
        assert_eq!(unpack((7 << 96) | (1 << 64)), block(0, DeletedItem(7)));
    }

    #[test]
    fn slides_move_every_word_but_one() {
        for len in 0..9u128 {
            let words: Vec<u128> = (0..len).map(|i| 100 + i).collect();
            let mut up = words.clone();
            slide_up(&mut up);
            let mut down = words.clone();
            slide_down(&mut down);
            for i in 0..len as usize {
                assert_eq!(up[i], if i == 0 { words[0] } else { words[i - 1] });
                assert_eq!(down[i], if i + 1 == len as usize { words[i] } else { words[i + 1] });
            }
        }
    }

    #[test]
    fn a_ring_grows_within_the_next_power_of_two() {
        for cap in (1..300usize).chain([1000, 4095, 4096, 4097, 200_000, 1 << 20, (1 << 20) + 1]) {
            let next = (cap + 1).next_power_of_two().max(4);
            for wrapped in [0, 1, 63, 64, 65, cap / 2, cap] {
                let more = growth(cap, wrapped);
                assert!(more >= 1, "{cap} {wrapped}");
                assert!(cap + more <= next, "{cap} {wrapped}");
                // as many slots as blocks to move, when the allocation has them
                assert_eq!(more, wrapped.max(MORE_SLOTS).min(next - cap), "{cap} {wrapped}");
            }
        }
        // the last sizes: up to `MAX_BLOCKS` and never past it
        if size_of::<usize>() == 8 {
            assert_eq!(growth(1 << 31, 0), 64);
            assert_eq!(growth((1 << 31) - 1, 0), 1);
            assert_eq!(growth(MAX_BLOCKS - 1, 0), 1);
            assert_eq!(growth(MAX_BLOCKS - 70, 1000), 70);
            assert_eq!(growth(1 << 31, 1 << 31), (1 << 31) - 1);
        }
    }

    #[test]
    fn append_checks_length_continuity_and_overflow() {
        let mut timeline = ClientBlocksCore::new();
        assert_eq!(
            timeline.append(block(4, BlockKindCore::Gc), 0),
            Err(StoreError::ZeroLength)
        );
        // the first block may start anywhere
        assert_eq!(timeline.append(block(4, BlockKindCore::Item(0)), 3), Ok(()));
        assert_eq!(
            timeline.append(block(8, BlockKindCore::Item(1)), 1),
            Err(StoreError::ClockMismatch)
        );
        assert_eq!(timeline.append(block(7, BlockKindCore::Skip), u64::MAX - 7), Ok(()));
        assert_eq!(timeline.end_clock(), u64::MAX);
        assert_eq!(
            timeline.append(block(u64::MAX, BlockKindCore::Gc), 1),
            Err(StoreError::ClockOverflow)
        );
        assert_eq!(timeline.len(), 2);
        assert_eq!(timeline.range(0), Some((4, 7)));
        assert_eq!(timeline.range(1), Some((7, u64::MAX)));
        assert_eq!(timeline.range(2), None);
        assert_eq!(timeline.get(1), Some(block(7, BlockKindCore::Skip)));
        assert_eq!(timeline.get(2), None);
    }

    #[test]
    fn find_is_the_last_block_at_or_before_the_clock() {
        let mut timeline = ClientBlocksCore::new();
        assert_eq!(timeline.find(0), None);
        timeline.append(block(2, BlockKindCore::Item(0)), 3).unwrap();
        timeline.append(block(5, BlockKindCore::DeletedItem(1)), 1).unwrap();
        timeline.append(block(6, BlockKindCore::Gc), 10).unwrap();
        assert_eq!(timeline.find(0), None);
        assert_eq!(timeline.find(1), None);
        assert_eq!(timeline.find(2), Some(0));
        assert_eq!(timeline.find(4), Some(0));
        assert_eq!(timeline.find(5), Some(1));
        assert_eq!(timeline.find(6), Some(2));
        assert_eq!(timeline.find(15), Some(2));
        assert_eq!(timeline.find(16), None);
        assert_eq!(timeline.find(u64::MAX), None);
    }

    #[test]
    fn split_merge_and_marks() {
        let mut timeline = ClientBlocksCore::new();
        timeline.append(block(0, BlockKindCore::Item(0)), 10).unwrap();
        timeline.append(block(10, BlockKindCore::Item(1)), 5).unwrap();
        assert_eq!(
            timeline.split_boundary(0, 0, BlockKindCore::Item(2)),
            Err(StoreError::InvalidSplit)
        );
        assert_eq!(
            timeline.split_boundary(0, 10, BlockKindCore::Item(2)),
            Err(StoreError::InvalidSplit)
        );
        assert_eq!(
            timeline.split_boundary(2, 12, BlockKindCore::Item(2)),
            Err(StoreError::MissingStruct)
        );
        // an interior split and one of the last block
        assert_eq!(timeline.split_boundary(0, 4, BlockKindCore::Item(2)), Ok(()));
        assert_eq!(timeline.split_boundary(2, 12, BlockKindCore::Item(3)), Ok(()));
        assert_eq!(
            blocks_of(&timeline),
            [
                block(0, BlockKindCore::Item(0)),
                block(4, BlockKindCore::Item(2)),
                block(10, BlockKindCore::Item(1)),
                block(12, BlockKindCore::Item(3)),
            ]
        );
        assert_eq!(timeline.end_clock(), 15);

        assert_eq!(timeline.mark_gc(1), Err(StoreError::NotAnItem));
        assert_eq!(timeline.mark_deleted(1), Ok(()));
        assert_eq!(timeline.mark_deleted(1), Ok(()));
        assert_eq!(timeline.mark_deleted(4), Err(StoreError::MissingStruct));
        assert_eq!(timeline.get(1).unwrap().kind, BlockKindCore::DeletedItem(2));
        assert_eq!(timeline.merge_adjacent(0), Err(StoreError::NotMergeable));
        assert_eq!(timeline.merge_adjacent(3), Err(StoreError::MissingStruct));
        assert_eq!(timeline.merge_adjacent(2), Ok(()));
        assert_eq!(timeline.range(2), Some((10, 15)));
        assert_eq!(timeline.mark_gc(1), Ok(2));
        assert_eq!(timeline.mark_gc(1), Err(StoreError::NotAnItem));
        assert_eq!(timeline.mark_deleted(1), Err(StoreError::NotAnItem));
        assert_eq!(timeline.find(9), Some(1));
        assert_eq!(timeline.len(), 3);
    }

    fn timeline_of(kinds: &[BlockKindCore]) -> ClientBlocksCore {
        let mut timeline = ClientBlocksCore::new();
        for (i, kind) in kinds.iter().enumerate() {
            timeline.append(block(10 + 2 * i as u64, *kind), 2).unwrap();
        }
        timeline
    }

    /// The same blocks in a ring that starts at the slot `head` of `slots`.
    fn turned(timeline: &ClientBlocksCore, slots: usize, head: usize) -> ClientBlocksCore {
        let blocks = blocks_of(timeline);
        assert!(blocks.len() <= slots && (head < slots || slots == 0));
        // what the free slots hold is never read
        let mut buf = vec![u128::MAX; slots];
        for (i, block) in blocks.iter().enumerate() {
            buf[(head + i) % slots] = pack(*block);
        }
        ClientBlocksCore {
            buf,
            head: head as u32,
            len: blocks.len() as u32,
            end_clock: timeline.end_clock,
        }
    }

    #[test]
    fn merge_range_closes_the_gap_in_place() {
        use BlockKindCore::{DeletedItem, Gc, Item, Skip};
        let kinds = [Item(0), Gc, Gc, Gc, DeletedItem(1), DeletedItem(2), Skip, Item(3)];
        let whole = timeline_of(&kinds);

        // refused, and nothing changes
        for (first, last, err) in [
            (3, 2, StoreError::MissingStruct),
            (0, 8, StoreError::MissingStruct),
            (8, 8, StoreError::MissingStruct),
            (usize::MAX, usize::MAX, StoreError::MissingStruct),
            (0, 1, StoreError::NotMergeable),
            (1, 4, StoreError::NotMergeable),
            (0, 7, StoreError::NotMergeable),
            (6, 7, StoreError::NotMergeable),
        ] {
            let mut timeline = timeline_of(&kinds);
            assert_eq!(timeline.merge_range(first, last), Err(err), "{first}..={last}");
            assert_eq!(timeline, whole);
        }

        // one block is a range of its own
        for at in 0..kinds.len() {
            let mut timeline = timeline_of(&kinds);
            assert_eq!(timeline.merge_range(at, at), Ok(()));
            assert_eq!(timeline, whole);
        }

        // every mergeable range against the same range merged pair by pair,
        // wherever the ring starts
        for head in 0..11 {
            for first in 0..kinds.len() {
                for last in first + 1..kinds.len() {
                    let mut ranged = turned(&whole, 11, head);
                    let capacity = ranged.buf.capacity();
                    let pointer = ranged.buf.as_ptr();
                    let result = ranged.merge_range(first, last);
                    let mut paired = turned(&whole, 11, head);
                    let mergeable = (first..last).all(|i| kinds[i].same_kind(kinds[i + 1]));
                    if mergeable {
                        assert_eq!(result, Ok(()));
                        for _ in first..last {
                            assert_eq!(paired.merge_adjacent(first), Ok(()));
                        }
                        assert_eq!(ranged.len(), kinds.len() - (last - first));
                        assert_eq!(ranged.range(first).unwrap().1, whole.range(last).unwrap().1);
                    } else {
                        assert_eq!(result, Err(StoreError::NotMergeable));
                    }
                    assert_eq!(ranged, paired);
                    assert_eq!(ranged.end_clock(), whole.end_clock());
                    // in place: the buffer is the one the timeline had
                    assert_eq!(ranged.buf.capacity(), capacity);
                    assert_eq!(ranged.buf.as_ptr(), pointer);
                    assert_eq!(ranged.buf.len(), 11);
                }
            }
        }

        let mut timeline = timeline_of(&kinds);
        assert_eq!(timeline.merge_range(1, 3), Ok(()));
        assert_eq!(timeline.merge_range(2, 3), Ok(()));
        assert_eq!(
            blocks_of(&timeline),
            [
                block(10, Item(0)),
                block(12, Gc),
                block(18, DeletedItem(1)),
                block(22, Skip),
                block(24, Item(3)),
            ]
        );
        assert_eq!(timeline.end_clock(), 26);
    }

    #[test]
    fn remap_slots_renames_every_item_block_or_none() {
        use BlockKindCore::{DeletedItem, Gc, Item, Skip};
        let kinds = [Item(4), Gc, DeletedItem(0), Skip, Item(2)];
        let whole = timeline_of(&kinds);

        for head in 0..7 {
            // slot 0 -> 0, slot 2 -> 1, slot 4 -> 2; slots 1 and 3 held nothing
            let mut moved = turned(&whole, 7, head);
            let pointer = moved.buf.as_ptr();
            assert_eq!(moved.remap_slots(&[1, 0, 2, 0, 3]), Ok(()));
            assert_eq!(
                blocks_of(&moved),
                [
                    block(10, Item(2)),
                    block(12, Gc),
                    block(14, DeletedItem(0)),
                    block(16, Skip),
                    block(18, Item(1)),
                ]
            );
            assert_eq!(moved.end_clock(), whole.end_clock());
            assert_eq!(moved.buf.as_ptr(), pointer);

            // a block of a slot that held nothing, or of one past the table:
            // refused before any block is renamed
            for table in [&[1, 0, 0, 0, 3][..], &[1, 0, 2, 0][..], &[0, 0, 2, 0, 3][..], &[][..]] {
                let mut timeline = turned(&whole, 7, head);
                assert_eq!(timeline.remap_slots(table), Err(StoreError::MissingStruct));
                assert_eq!(timeline, whole);
            }
        }

        // no item block, no table needed
        let mut collected = timeline_of(&[Gc, Skip]);
        assert_eq!(collected.remap_slots(&[]), Ok(()));
        assert_eq!(collected, timeline_of(&[Gc, Skip]));
        let mut empty = ClientBlocksCore::new();
        assert_eq!(empty.remap_slots(&[]), Ok(()));
        assert_eq!(empty.remap_slots(&[u32::MAX]), Ok(()));

        // the largest slot
        let mut last = timeline_of(&[Item(0)]);
        assert_eq!(last.remap_slots(&[u32::MAX]), Ok(()));
        assert_eq!(last.get(0).unwrap().kind, Item(u32::MAX - 1));
    }

    /// A timeline the plain way: the blocks in a deque.
    #[derive(Clone, Debug)]
    struct Model {
        blocks: VecDeque<BlockRefCore>,
        end_clock: u64,
    }

    impl Model {
        fn range(&self, index: usize) -> Option<(u64, u64)> {
            let start = self.blocks.get(index)?.clock;
            Some((
                start,
                self.blocks.get(index + 1).map_or(self.end_clock, |next| next.clock),
            ))
        }

        fn find(&self, clock: u64) -> Option<usize> {
            if clock >= self.end_clock {
                return None;
            }
            self.blocks.partition_point(|b| b.clock <= clock).checked_sub(1)
        }
    }

    fn assert_same(timeline: &ClientBlocksCore, model: &Model, what: &str) {
        assert_eq!(timeline.len(), model.blocks.len(), "{what}");
        assert_eq!(timeline.is_empty(), model.blocks.is_empty(), "{what}");
        assert_eq!(timeline.end_clock(), model.end_clock, "{what}");
        for index in 0..model.blocks.len() + 2 {
            assert_eq!(timeline.get(index), model.blocks.get(index).copied(), "{what} {index}");
            assert_eq!(timeline.range(index), model.range(index), "{what} {index}");
        }
        // the ring holds its blocks
        assert!(timeline.len as usize <= timeline.buf.len(), "{what}");
        assert!((timeline.head as usize) < timeline.buf.len().max(1), "{what}");
    }

    fn assert_finds(timeline: &ClientBlocksCore, model: &Model, what: &str) {
        let first = model.blocks.front().map_or(0, |b| b.clock);
        for clock in first.saturating_sub(2)..model.end_clock + 2 {
            assert_eq!(timeline.find(clock), model.find(clock), "{what} {clock}");
        }
        assert_eq!(timeline.find(u64::MAX), None);
    }

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// One edit on the timeline and on the model, which have to agree on
    /// whether it is taken and on what it does.
    fn edit(timeline: &mut ClientBlocksCore, model: &mut Model, rng: &mut Rng, slots: &mut u32) -> &'static str {
        use BlockKindCore::{DeletedItem, Gc, Item, Skip};
        let len = model.blocks.len();
        // where an edit is: mostly near one of the two ends
        let place = |rng: &mut Rng| match rng.below(4) {
            0 => rng.below(len.min(3) + 1).min(len.saturating_sub(1)),
            1 => len.saturating_sub(1 + rng.below(len.min(3) + 1)),
            _ => rng.below(len.max(1)),
        };
        match rng.below(16) {
            0..=3 => {
                let kind = match rng.below(6) {
                    0 => Gc,
                    1 => Skip,
                    2 => DeletedItem(*slots),
                    _ => Item(*slots),
                };
                *slots += 1;
                let clock = if len == 0 { rng.next() % 50 } else { model.end_clock };
                let clocks = 1 + rng.next() % 6;
                assert_eq!(timeline.append(block(clock, kind), clocks), Ok(()));
                model.blocks.push_back(block(clock, kind));
                model.end_clock = clock + clocks;
                "append"
            }
            4..=9 => {
                if len == 0 {
                    assert_eq!(timeline.split_boundary(0, 1, Gc), Err(StoreError::MissingStruct));
                    return "split of nothing";
                }
                let index = place(rng);
                let (start, end) = model.range(index).unwrap();
                let clock = start + rng.next() % (end - start + 1);
                let kind = match model.blocks[index].kind {
                    Item(_) => Item(*slots),
                    DeletedItem(_) => DeletedItem(*slots),
                    other => other,
                };
                *slots += 1;
                let result = timeline.split_boundary(index, clock, kind);
                if clock > start && clock < end {
                    assert_eq!(result, Ok(()));
                    model.blocks.insert(index + 1, block(clock, kind));
                    "split"
                } else {
                    assert_eq!(result, Err(StoreError::InvalidSplit));
                    "split outside"
                }
            }
            10..=12 => {
                if len == 0 {
                    assert_eq!(timeline.merge_range(0, 0), Err(StoreError::MissingStruct));
                    return "merge of nothing";
                }
                let first = place(rng);
                let last = (first + rng.below(4)).min(len - 1);
                let mergeable = (first..last).all(|i| model.blocks[i].kind.same_kind(model.blocks[i + 1].kind));
                let result = timeline.merge_range(first, last);
                if mergeable {
                    assert_eq!(result, Ok(()));
                    model.blocks.drain(first + 1..=last);
                    "merge"
                } else {
                    assert_eq!(result, Err(StoreError::NotMergeable));
                    "merge refused"
                }
            }
            13 => {
                let index = place(rng);
                let result = timeline.mark_deleted(index);
                match model.blocks.get(index).map(|b| b.kind) {
                    None => assert_eq!(result, Err(StoreError::MissingStruct)),
                    Some(Item(slot)) => {
                        assert_eq!(result, Ok(()));
                        model.blocks[index].kind = DeletedItem(slot);
                    }
                    Some(DeletedItem(_)) => assert_eq!(result, Ok(())),
                    Some(_) => assert_eq!(result, Err(StoreError::NotAnItem)),
                }
                "delete"
            }
            14 => {
                let index = place(rng);
                let result = timeline.mark_gc(index);
                match model.blocks.get(index).map(|b| b.kind) {
                    None => assert_eq!(result, Err(StoreError::MissingStruct)),
                    Some(DeletedItem(slot)) => {
                        assert_eq!(result, Ok(slot));
                        model.blocks[index].kind = Gc;
                    }
                    Some(_) => assert_eq!(result, Err(StoreError::NotAnItem)),
                }
                "collect"
            }
            _ => {
                // every slot moves up by 3, or the table is a slot short
                let short = rng.below(3) == 0 && model.blocks.iter().any(|b| b.kind.item() == Some(*slots - 1));
                let table: Vec<u32> = (0..*slots - u32::from(short)).map(|slot| slot + 4).collect();
                let result = timeline.remap_slots(&table);
                if short {
                    assert_eq!(result, Err(StoreError::MissingStruct));
                    "remap refused"
                } else {
                    assert_eq!(result, Ok(()));
                    for block in model.blocks.iter_mut() {
                        block.kind = match block.kind {
                            Item(slot) => Item(slot + 3),
                            DeletedItem(slot) => DeletedItem(slot + 3),
                            other => other,
                        };
                    }
                    *slots += 3;
                    "remap"
                }
            }
        }
    }

    #[test]
    fn every_edit_agrees_with_a_deque() {
        let rounds = if cfg!(miri) { 3 } else { 60 };
        let steps = if cfg!(miri) { 120 } else { 700 };
        for seed in 1..=rounds {
            let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ (seed as u64).wrapping_mul(0x1234_5678_9ABC_DEF1));
            let mut timeline = ClientBlocksCore::new();
            let mut model = Model {
                blocks: VecDeque::new(),
                end_clock: 0,
            };
            let mut slots = 0u32;
            // some start as a long timeline that only ever grew at its end
            for _ in 0..(seed % 4) * 37 {
                let clock = model.end_clock;
                timeline.append(block(clock, BlockKindCore::Item(slots)), 3).unwrap();
                model.blocks.push_back(block(clock, BlockKindCore::Item(slots)));
                model.end_clock = clock + 3;
                slots += 1;
            }
            for step in 0..steps {
                let what = edit(&mut timeline, &mut model, &mut rng, &mut slots);
                assert_same(&timeline, &model, what);
                if step % 16 == 0 || model.blocks.len() < 12 {
                    assert_finds(&timeline, &model, what);
                }
                // the allocation is the one a deque of these blocks has
                assert_eq!(timeline.buf.capacity(), model.blocks.capacity(), "{what} {step}");
            }
            assert_finds(&timeline, &model, "at the end");
        }
    }

    #[test]
    fn edits_at_the_front_of_a_long_timeline_leave_the_rest_where_it_is() {
        let mut timeline = ClientBlocksCore::new();
        let mut model = Model {
            blocks: VecDeque::new(),
            end_clock: 0,
        };
        let count = if cfg!(miri) { 300 } else { 5000 };
        for i in 0..count {
            timeline.append(block(4 * i, BlockKindCore::Item(i as u32)), 4).unwrap();
            model.blocks.push_back(block(4 * i, BlockKindCore::Item(i as u32)));
        }
        model.end_clock = 4 * count;
        assert_eq!(timeline.head, 0);
        assert_eq!(timeline.buf.len(), count as usize);

        // splits of the first blocks, each of them once: the slots of the
        // blocks after them are never written
        let old: Vec<u128> = timeline.buf.clone();
        let splits = 200usize.min(count as usize / 4);
        for i in 0..splits {
            let index = 2 * i;
            let (start, _) = model.range(index).unwrap();
            let kind = BlockKindCore::Item(1_000_000 + i as u32);
            assert_eq!(timeline.split_boundary(index, start + 1, kind), Ok(()));
            model.blocks.insert(index + 1, block(start + 1, kind));
            assert_eq!(timeline.buf[2 * splits..count as usize], old[2 * splits..]);
        }
        assert_same(&timeline, &model, "front splits");
        assert_finds(&timeline, &model, "front splits");
        assert!(timeline.head > 0);

        // appends after that write one slot each
        for i in 0..300u64 {
            let before = timeline.buf.clone();
            let clock = model.end_clock;
            timeline.append(block(clock, BlockKindCore::Gc), 2).unwrap();
            model.blocks.push_back(block(clock, BlockKindCore::Gc));
            model.end_clock = clock + 2;
            if timeline.buf.len() == before.len() {
                let written = (0..before.len())
                    .filter(|&slot| before[slot] != timeline.buf[slot])
                    .count();
                assert!(written <= 1, "append {i} wrote {written} slots");
            }
        }
        assert_same(&timeline, &model, "appends after front splits");
        assert_finds(&timeline, &model, "appends after front splits");
        assert_eq!(timeline.buf.capacity(), model.blocks.capacity());

        // merges at the front move the front
        for _ in 0..50 {
            if model.blocks[0].kind.same_kind(model.blocks[1].kind) {
                assert_eq!(timeline.merge_range(0, 1), Ok(()));
                model.blocks.remove(1);
            } else {
                assert_eq!(timeline.mark_deleted(0), Ok(()));
                let slot = model.blocks[0].kind.item().unwrap();
                model.blocks[0].kind = BlockKindCore::DeletedItem(slot);
            }
        }
        assert_same(&timeline, &model, "front merges");
        assert_finds(&timeline, &model, "front merges");
    }

    #[test]
    fn any_fields_read_as_a_timeline() {
        use BlockKindCore::{DeletedItem, Gc, Item};
        let words: Vec<u128> = [
            block(3, Item(0)),
            block(9, DeletedItem(1)),
            block(10, Gc),
            block(14, Item(2)),
            block(20, DeletedItem(3)),
        ]
        .iter()
        .map(|b| pack(*b))
        .collect();
        for slots in 0..=5usize {
            for head in [0u32, 1, 2, 4, 5, 6, u32::MAX] {
                for len in [0u32, 1, 3, 5, 6, u32::MAX] {
                    let odd = ClientBlocksCore {
                        buf: words[..slots].to_vec(),
                        head,
                        len,
                        end_clock: 30,
                    };
                    // the ring the fields are read as, and the same blocks in
                    // a ring whose fields say what it is
                    let start = if (head as usize) < slots { head as usize } else { 0 };
                    let count = (len as usize).min(slots);
                    let blocks: Vec<BlockRefCore> = (0..count).map(|i| unpack(words[(start + i) % slots])).collect();
                    assert_eq!(odd.len(), count);
                    assert_eq!(blocks_of(&odd), blocks);
                    let plain = ClientBlocksCore {
                        buf: blocks.iter().map(|b| pack(*b)).collect(),
                        head: 0,
                        len: count as u32,
                        end_clock: 30,
                    };
                    assert_eq!(odd, plain);
                    for clock in 0..32 {
                        // the blocks of a ring that was turned by hand are
                        // not sorted: only the lookups that do not need them
                        // to be are compared
                        if start == 0 {
                            assert_eq!(odd.find(clock), plain.find(clock));
                        } else {
                            let _ = odd.find(clock);
                        }
                    }
                    for index in 0..7 {
                        assert_eq!(odd.range(index), plain.range(index));
                        let (mut a, mut b) = (odd.clone(), plain.clone());
                        assert_eq!(a.mark_deleted(index), b.mark_deleted(index));
                        assert_eq!(a, b);
                        let (mut a, mut b) = (odd.clone(), plain.clone());
                        assert_eq!(a.mark_gc(index), b.mark_gc(index));
                        assert_eq!(a, b);
                        for last in index..7 {
                            let (mut a, mut b) = (odd.clone(), plain.clone());
                            assert_eq!(a.merge_range(index, last), b.merge_range(index, last));
                            assert_eq!(a, b);
                        }
                        for clock in [0, 4, 9, 12, 15, 25, 29, 30] {
                            let (mut a, mut b) = (odd.clone(), plain.clone());
                            assert_eq!(a.split_boundary(index, clock, Gc), b.split_boundary(index, clock, Gc));
                            assert_eq!(a, b);
                        }
                    }
                    for clock in [0, 30, 31] {
                        let (mut a, mut b) = (odd.clone(), plain.clone());
                        assert_eq!(a.append(block(clock, Gc), 2), b.append(block(clock, Gc), 2));
                        assert_eq!(a, b);
                        assert_eq!(a.len(), blocks_of(&a).len());
                    }
                    let (mut a, mut b) = (odd.clone(), plain.clone());
                    assert_eq!(a.remap_slots(&[4, 3, 2, 1]), b.remap_slots(&[4, 3, 2, 1]));
                    assert_eq!(a, b);
                    let (mut a, mut b) = (odd.clone(), plain.clone());
                    assert_eq!(a.remap_slots(&[4, 3]), b.remap_slots(&[4, 3]));
                    assert_eq!(a, b);
                }
            }
        }
    }
}
