use y_octo_core::client_blocks::{
    BlockKindCore, BlockRefCore, ClientBlocksCore, MAX_BLOCKS, StoreError, clock_of, deleted_word,
};

use super::{
    item_space::{ItemIdx, Moved},
    *,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BlockKind {
    Item(ItemIdx),
    DeletedItem(ItemIdx),
    Gc,
    Skip,
}

impl BlockKind {
    pub fn deleted(self) -> bool {
        // Matches the integrated-store semantics of Node::flags for GC and
        // Skip. A wire Skip is never integrated by apply_update.
        !matches!(self, Self::Item(_))
    }

    #[inline]
    fn core(self) -> BlockKindCore {
        match self {
            Self::Item(idx) => BlockKindCore::Item(idx.core_slot()),
            Self::DeletedItem(idx) => BlockKindCore::DeletedItem(idx.core_slot()),
            Self::Gc => BlockKindCore::Gc,
            Self::Skip => BlockKindCore::Skip,
        }
    }

    /// The kind of the block of a word of the core: the tag in the low half
    /// of its upper 64 bits, the slot of the item above it. One match where
    /// `of_core(unpack(word).kind)` takes two; the tests hold the two
    /// together.
    #[inline]
    fn of_word(word: u128) -> Self {
        let code = (word >> 64) as u64;
        let idx = ItemIdx::of_core_slot((code >> 32) as u32);
        match code as u32 {
            0 => Self::Item(idx),
            1 => Self::DeletedItem(idx),
            2 => Self::Gc,
            _ => Self::Skip,
        }
    }

    /// The kind of a block the core unpacked: what `of_word` has to agree
    /// with.
    #[cfg(test)]
    fn of_core(kind: BlockKindCore) -> Self {
        match kind {
            BlockKindCore::Item(slot) => Self::Item(ItemIdx::of_core_slot(slot)),
            BlockKindCore::DeletedItem(slot) => Self::DeletedItem(ItemIdx::of_core_slot(slot)),
            BlockKindCore::Gc => Self::Gc,
            BlockKindCore::Skip => Self::Skip,
        }
    }
}

/// A block handed to [ClientBlocks::append]; the timeline stores it as a
/// `BlockRefCore` of the same size.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BlockRef {
    pub clock: Clock,
    pub kind: BlockKind,
}

const _: () = assert!(size_of::<BlockRef>() == 16);
const _: () = assert!(size_of::<BlockRefCore>() == 16);
// a timeline is no larger than the deque of blocks and the end clock it was
#[cfg(target_pointer_width = "64")]
const _: () = assert!(size_of::<ClientBlocks>() == 40);

/// The block timeline of one client: `ClientBlocksCore` of `y-octo-core`,
/// whose functions are the ones proved in `proofs/` (block starts strictly
/// increase below the end of the timeline; every edit keeps that). A block
/// ends exactly where its successor starts. The final boundary is kept
/// separately so the complete V1 u64 range needs no per-block length.
///
/// Every edit of a timeline is one of the calls below, each a single call of
/// the core; an item block names its item by the slot of its [ItemIdx].
#[derive(Debug, Default)]
pub(crate) struct ClientBlocks {
    core: ClientBlocksCore,
}

/// The kinds of the blocks of a timeline, by index.
pub(crate) struct Kinds<'a> {
    first: &'a [u128],
    second: &'a [u128],
}

impl Kinds<'_> {
    /// The kind of the block at `index`, which has to be a block.
    #[inline]
    pub fn at(&self, index: usize) -> BlockKind {
        BlockKind::of_word(match self.first.get(index) {
            Some(word) => *word,
            None => self.second[index - self.first.len()],
        })
    }
}

/// The blocks of a run of a timeline in order, each with the clock it ends
/// at: the words of the two slices of the ring, the next one read ahead for
/// the end of the block before it.
struct Blocks<'a> {
    first: std::slice::Iter<'a, u128>,
    second: std::slice::Iter<'a, u128>,
    next: Option<u128>,
    end: Clock,
}

impl Iterator for Blocks<'_> {
    type Item = (u128, Clock);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let word = self.next?;
        self.next = match self.first.next() {
            Some(next) => Some(*next),
            None => {
                // the second slice from here on, and nothing after it
                self.first = std::mem::take(&mut self.second);
                self.first.next().copied()
            }
        };
        Some((word, self.next.map_or(self.end, clock_of)))
    }
}

#[cfg(test)]
thread_local! {
    /// The most blocks a timeline holds in the tests of this thread.
    static BLOCK_LIMIT: std::cell::Cell<usize> = const { std::cell::Cell::new(MAX_BLOCKS) };
}

/// Puts the block limit of the tests of this thread back when it goes.
#[cfg(all(test, not(loom)))]
pub(crate) struct BlockLimit(usize);

#[cfg(all(test, not(loom)))]
impl Drop for BlockLimit {
    fn drop(&mut self) {
        BLOCK_LIMIT.with(|limit| limit.set(self.0));
    }
}

impl ClientBlocks {
    /// The most blocks a timeline holds: as many as the core takes.
    #[inline]
    pub fn limit() -> usize {
        #[cfg(test)]
        return BLOCK_LIMIT.with(|limit| limit.get());
        #[cfg(not(test))]
        MAX_BLOCKS
    }

    /// Makes every timeline of this thread refuse a block past `limit` until
    /// the guard is dropped, so that a test reaches a full timeline.
    #[cfg(all(test, not(loom)))]
    pub(crate) fn set_limit(limit: usize) -> BlockLimit {
        BlockLimit(BLOCK_LIMIT.with(|cell| cell.replace(limit.min(MAX_BLOCKS))))
    }

    /// Whether the timeline takes `additional` more blocks, for callers that
    /// add several and have to know before they add the first.
    #[inline]
    pub fn check_capacity(&self, additional: usize) -> JwstCodecResult {
        if self.len().checked_add(additional).is_none_or(|n| n > Self::limit()) {
            return Err(Self::full());
        }
        Ok(())
    }

    #[cold]
    fn full() -> JwstCodecError {
        JwstCodecError::IncompleteDocument(TOO_MANY_STRUCTS.into())
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.core.len()
    }

    /// The next clock of the client: where the last block ends.
    #[inline]
    pub fn end_clock(&self) -> Clock {
        self.core.end_clock()
    }

    /// The clock the first block starts at.
    #[inline]
    pub fn first_clock(&self) -> Option<Clock> {
        self.core.clock_at(0)
    }

    /// The clock the block at `index` starts at.
    #[inline]
    pub fn clock_at(&self, index: usize) -> Clock {
        self.core.clock_at(index).expect("block index")
    }

    #[inline]
    pub fn kind_at(&self, index: usize) -> BlockKind {
        BlockKind::of_word(self.core.word_at(index).expect("block index"))
    }

    #[inline]
    pub fn node(&self, client: Client, index: usize) -> Option<Node> {
        let (word, end) = self.core.word_end_at(index)?;
        let start = clock_of(word);
        Some(Node {
            id: Id::new(client, start),
            len: end - start,
            kind: BlockKind::of_word(word),
        })
    }

    /// The block that holds `clock`: its index, its word and the clock it
    /// ends at. The search is `partition_point` of the standard library on
    /// the one slice of the ring the block is in, which the first word of
    /// the second slice tells; `ClientBlocksCore::find` is the same search,
    /// proved, and the tests hold the two together.
    #[inline]
    fn locate(&self, clock: Clock) -> Option<(usize, u128, Clock)> {
        let end = self.core.end_clock();
        if clock >= end {
            return None;
        }
        let (first, second) = self.core.words();
        let (words, before, rest) = match second.first() {
            Some(word) if clock_of(*word) <= clock => (second, first.len(), &second[..0]),
            _ => (first, 0, second),
        };
        let after = match words.last() {
            Some(last) if clock_of(*last) <= clock => words.len(),
            _ => words.partition_point(|word| clock_of(*word) <= clock),
        };
        let at = after.checked_sub(1)?;
        let stop = words.get(after).or(rest.first()).map_or(end, |next| clock_of(*next));
        Some((before + at, words[at], stop))
    }

    /// The node that holds `clock`, and its index.
    #[inline]
    pub fn find_node(&self, client: Client, clock: Clock) -> Option<(Node, usize)> {
        let (index, word, end) = self.locate(clock)?;
        let start = clock_of(word);
        Some((
            Node {
                id: Id::new(client, start),
                len: end - start,
                kind: BlockKind::of_word(word),
            },
            index,
        ))
    }

    pub fn nodes(&self, client: Client) -> impl Iterator<Item = Node> + '_ {
        self.nodes_from(client, 0)
    }

    /// The nodes of the blocks from `start` on. Unlike `nodes(..).skip(start)`
    /// it does not visit the blocks before `start`.
    pub fn nodes_from(&self, client: Client, start: usize) -> impl Iterator<Item = Node> + '_ {
        self.blocks_from(start).map(move |(word, end)| {
            let start = clock_of(word);
            Node {
                id: Id::new(client, start),
                len: end - start,
                kind: BlockKind::of_word(word),
            }
        })
    }

    /// The blocks from `start` on, each with the clock it ends at. A scan
    /// reads the ring once and then a word a block.
    fn blocks_from(&self, start: usize) -> Blocks<'_> {
        let (first, second) = self.core.words();
        let (first, second) = match first.get(start..) {
            Some(first) => (first, second),
            None => (&first[..0], second.get(start - first.len()..).unwrap_or(&[])),
        };
        let (mut first, mut second) = (first.iter(), second.iter());
        let next = first.next().or_else(|| second.next()).copied();
        Blocks {
            first,
            second,
            next,
            end: self.core.end_clock(),
        }
    }

    /// Renames the item slots after [ItemSpace::finish] moved the items.
    pub(in crate::doc) fn remap(&mut self, moved: &Moved) {
        self.core
            .remap_slots(moved.table())
            .expect("timeline refers to a live item");
    }

    /// Whether [ClientBlocks::append] takes a block of `len` clocks at
    /// `clock`, for callers that have to know before they change anything
    /// else.
    pub fn check_append(&self, clock: Clock, len: u64) -> JwstCodecResult {
        if len == 0 {
            return Err(Self::append_error(StoreError::ZeroLength, self.end_clock(), clock));
        }
        if !self.core.continues(clock) {
            return Err(Self::append_error(StoreError::ClockMismatch, self.end_clock(), clock));
        }
        if clock.checked_add(len).is_none() {
            return Err(Self::append_error(StoreError::ClockOverflow, self.end_clock(), clock));
        }
        if self.is_full() {
            return Err(Self::append_error(StoreError::Capacity, self.end_clock(), clock));
        }
        Ok(())
    }

    pub fn append(&mut self, block: BlockRef, len: u64) -> JwstCodecResult {
        // the core refuses a block past `MAX_BLOCKS`; a test may ask for less
        #[cfg(test)]
        self.check_append(block.clock, len)?;
        let core = BlockRefCore {
            clock: block.clock,
            kind: block.kind.core(),
        };
        self.core
            .append(core, len)
            .map_err(|err| Self::append_error(err, self.core.end_clock(), block.clock))
    }

    #[cold]
    fn append_error(err: StoreError, expect: Clock, actually: Clock) -> JwstCodecError {
        match err {
            StoreError::ZeroLength => JwstCodecError::IncompleteDocument("zero-length struct".into()),
            StoreError::ClockMismatch => JwstCodecError::StructClockInvalid { expect, actually },
            StoreError::ClockOverflow => JwstCodecError::IncompleteDocument("struct clock overflow".into()),
            _ => Self::full(),
        }
    }

    /// No block can be added: the timeline holds as many as a slot index can
    /// name.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.core.len() >= Self::limit()
    }

    #[cfg(test)]
    pub fn range(&self, index: usize) -> Option<Range<Clock>> {
        self.core.word_end_at(index).map(|(word, end)| clock_of(word)..end)
    }

    #[inline]
    pub fn find(&self, clock: Clock) -> Option<usize> {
        self.locate(clock).map(|(index, ..)| index)
    }

    /// `find` for a clock that is most likely in the last block, as what a
    /// transaction just wrote is: the search of the core, which reads the
    /// last block before anything else.
    #[inline]
    pub fn find_recent(&self, clock: Clock) -> Option<usize> {
        self.core.find(clock)
    }

    /// The kinds of the blocks for a run of reads: the ring is read once.
    #[inline]
    pub fn kinds(&self) -> Kinds<'_> {
        let (first, second) = self.core.words();
        Kinds { first, second }
    }

    /// Splits the block at `index` at `clock`, strictly inside it; the right
    /// half is of kind `kind`.
    #[inline]
    pub fn split(&mut self, index: usize, clock: Clock, kind: BlockKind) -> Result<(), StoreError> {
        #[cfg(test)]
        if self.is_full()
            && self
                .range(index)
                .is_some_and(|range| range.start < clock && clock < range.end)
        {
            return Err(StoreError::Capacity);
        }
        self.core.split_boundary(index, clock, kind.core())
    }

    /// Marks the item block at `index` deleted.
    #[inline]
    pub fn mark_deleted(&mut self, index: usize) -> Result<(), StoreError> {
        self.core.mark_deleted(index)
    }

    /// Replaces the item block at `index` by a collected range.
    #[inline]
    pub fn collect(&mut self, index: usize) -> Result<(), StoreError> {
        // the core collects deleted items only; the block of an item that is
        // collected is marked deleted already, and this keeps it so
        self.core.mark_deleted(index)?;
        self.core.mark_gc(index).map(|_| ())
    }

    /// Makes the blocks `first..=last`, neighbours of the same kind, one
    /// block.
    #[inline]
    pub fn merge_range(&mut self, first: usize, last: usize) -> Result<(), StoreError> {
        self.core.merge_range(first, last)
    }

    /// Hands `f` the clocks of every block that is not a live item, in
    /// order: a scan of the two slices of the ring that reads a word and its
    /// tag for a live block and nothing else.
    pub fn each_deleted(&self, mut f: impl FnMut(Range<Clock>)) {
        fn scan(words: &[u128], end: Clock, f: &mut impl FnMut(Range<Clock>)) {
            let mut rest = words.iter();
            let Some(mut word) = rest.next() else { return };
            for next in rest {
                if deleted_word(*word) && clock_of(*word) < clock_of(*next) {
                    f(clock_of(*word)..clock_of(*next));
                }
                word = next;
            }
            if deleted_word(*word) && clock_of(*word) < end {
                f(clock_of(*word)..end);
            }
        }
        let (first, second) = self.core.words();
        let end = self.core.end_clock();
        scan(first, second.first().map_or(end, |next| clock_of(*next)), &mut f);
        scan(second, end, &mut f);
    }

    #[cfg(test)]
    pub fn deleted_ranges(&self) -> impl Iterator<Item = Range<Clock>> + '_ {
        self.blocks_from(0).filter_map(|(word, end)| {
            deleted_word(word)
                .then(|| clock_of(word)..end)
                .filter(|r| !r.is_empty())
        })
    }
}

#[cfg(test)]
mod tests {
    use y_octo_core::client_blocks::unpack;

    use super::*;

    #[test]
    fn the_search_agrees_with_the_core_on_every_clock() {
        // timelines in the order of their slots (`front == 0`) and ones a few
        // splits at the front turned into a ring of two slices
        for front in [0usize, 1, 3, 40] {
            let mut timeline = ClientBlocks::default();
            let mut clock = 5;
            for i in 0..200u64 {
                let len = 2 + i % 4;
                let kind = if i % 3 == 0 { BlockKind::Gc } else { BlockKind::Skip };
                timeline.append(BlockRef { clock, kind }, len).unwrap();
                clock += len;
            }
            for split in 0..front {
                let index = 2 * split;
                let start = timeline.clock_at(index);
                timeline.split(index, start + 1, BlockKind::Skip).unwrap();
            }
            let (first, second) = timeline.core.words();
            assert_eq!(first.len() + second.len(), timeline.len());
            assert_eq!(second.is_empty(), front == 0, "{front} splits at the front");

            let kinds = timeline.kinds();
            for index in 0..timeline.len() {
                assert_eq!(kinds.at(index), timeline.kind_at(index));
                let block = timeline.core.get(index).unwrap();
                assert_eq!(timeline.clock_at(index), block.clock);
                assert_eq!(timeline.kind_at(index), BlockKind::of_core(block.kind));
                let (start, end) = timeline.core.range(index).unwrap();
                assert_eq!(timeline.range(index), Some(start..end));
            }
            assert_eq!(timeline.nodes(9).count(), timeline.len());
            for (index, node) in timeline.nodes(9).enumerate() {
                assert_eq!(Some(node), timeline.node(9, index));
            }

            for clock in 0..timeline.end_clock() + 3 {
                let found = timeline.core.find(clock);
                assert_eq!(timeline.find(clock), found, "clock {clock}, {front} splits");
                assert_eq!(timeline.find_recent(clock), found);
                let node = timeline.find_node(9, clock);
                assert_eq!(node.map(|(_, index)| index), found);
                assert_eq!(
                    node.map(|(node, _)| node),
                    found.and_then(|index| timeline.node(9, index))
                );
            }
        }
    }

    #[test]
    fn a_word_reads_as_the_kind_the_core_unpacks() {
        let mut timeline = ClientBlocks::default();
        let idx = |slot: usize| ItemIdx::of_core_slot(slot as u32);
        let kinds = [
            BlockKind::Item(idx(0)),
            BlockKind::DeletedItem(idx(0)),
            BlockKind::Gc,
            BlockKind::Skip,
            BlockKind::Item(idx(7)),
            BlockKind::DeletedItem(idx(u32::MAX as usize - 1)),
            BlockKind::Item(idx(u32::MAX as usize - 1)),
        ];
        for (clock, kind) in kinds.into_iter().enumerate() {
            let clock = clock as u64;
            timeline.append(BlockRef { clock, kind }, 1).unwrap();
        }
        for (index, kind) in kinds.into_iter().enumerate() {
            let word = timeline.core.word_at(index).unwrap();
            assert_eq!(BlockKind::of_word(word), kind);
            assert_eq!(BlockKind::of_word(word), BlockKind::of_core(unpack(word).kind));
            assert_eq!(timeline.kind_at(index), kind);
        }
        // a tag no block has reads as a gap, as the core reads it
        for tag in [3u128, 4, 0xffff_ffff] {
            let word = (((9u128 << 32) | tag) << 64) | 5;
            assert_eq!(BlockKind::of_word(word), BlockKind::of_core(unpack(word).kind));
            assert_eq!(BlockKind::of_word(word), BlockKind::Skip);
        }
    }

    #[test]
    fn full_width_ranges_and_refused_blocks() {
        let mut timeline = ClientBlocks::default();
        let long = u64::from(u32::MAX) + 11;
        let block = |clock, kind| BlockRef { clock, kind };
        assert_eq!(timeline.first_clock(), None);
        timeline.append(block(0, BlockKind::Gc), long).unwrap();
        // the core holds no empty block
        assert!(timeline.check_append(long, 0).is_err());
        assert!(matches!(
            timeline.append(block(long, BlockKind::Skip), 0),
            Err(JwstCodecError::IncompleteDocument(_))
        ));
        assert!(timeline.check_append(long + 1, 1).is_err());
        assert!(matches!(
            timeline.append(block(long + 1, BlockKind::Skip), 1),
            Err(JwstCodecError::StructClockInvalid { expect, actually }) if expect == long && actually == long + 1
        ));
        assert!(timeline.check_append(long, u64::MAX - long).is_ok());
        timeline.append(block(long, BlockKind::Skip), u64::MAX - long).unwrap();
        assert_eq!(timeline.first_clock(), Some(0));
        assert_eq!(timeline.clock_at(1), long);
        assert_eq!(timeline.kind_at(1), BlockKind::Skip);
        assert_eq!(timeline.range(0), Some(0..long));
        assert_eq!(timeline.range(1), Some(long..u64::MAX));
        assert_eq!(timeline.range(2), None);
        assert_eq!(timeline.find(long - 1), Some(0));
        assert_eq!(timeline.find(long), Some(1));
        assert_eq!(timeline.find(u64::MAX - 1), Some(1));
        assert_eq!(timeline.find(u64::MAX), None);
        assert!(timeline.check_append(u64::MAX, 1).is_err());
        assert!(timeline.append(block(u64::MAX, BlockKind::Gc), 1).is_err());
        assert_eq!(timeline.len(), 2);
        assert_eq!(timeline.end_clock(), u64::MAX);
        assert_eq!(timeline.deleted_ranges().collect::<Vec<_>>(), [0..long, long..u64::MAX]);
    }

    #[test]
    fn item_blocks_keep_their_item_through_the_core() {
        let mut types = TypeArena::default();
        let mut idx = |clock| {
            types
                .items
                .alloc(Item {
                    id: Id::new(1, clock),
                    len: 2,
                    ..Item::default()
                })
                .unwrap()
        };
        let (a, b, c) = (idx(0), idx(2), idx(4));
        let mut timeline = ClientBlocks::default();
        let block = |clock, kind| BlockRef { clock, kind };
        timeline.append(block(0, BlockKind::Item(a)), 2).unwrap();
        timeline.append(block(2, BlockKind::DeletedItem(b)), 4).unwrap();
        assert_eq!(timeline.kind_at(0), BlockKind::Item(a));
        assert_eq!(timeline.kind_at(1), BlockKind::DeletedItem(b));
        assert_eq!(
            timeline.node(1, 1),
            Some(Node {
                id: Id::new(1, 2),
                len: 4,
                kind: BlockKind::DeletedItem(b),
            })
        );
        assert_eq!(timeline.node(1, 2), None);

        // a split strictly inside a block only
        assert_eq!(
            timeline.split(1, 2, BlockKind::DeletedItem(c)),
            Err(StoreError::InvalidSplit)
        );
        assert_eq!(
            timeline.split(1, 6, BlockKind::DeletedItem(c)),
            Err(StoreError::InvalidSplit)
        );
        assert_eq!(timeline.split(1, 4, BlockKind::DeletedItem(c)), Ok(()));
        assert_eq!(
            timeline.nodes(1).map(|n| (n.clock(), n.len())).collect::<Vec<_>>(),
            [(0, 2), (2, 2), (4, 2)]
        );
        assert_eq!(timeline.kind_at(2), BlockKind::DeletedItem(c));
        assert_eq!(timeline.nodes_from(1, 1).map(|n| n.clock()).collect::<Vec<_>>(), [2, 4]);
        assert_eq!(timeline.nodes_from(1, 3).count(), 0);
        assert_eq!(timeline.nodes_from(1, 9).count(), 0);

        assert_eq!(timeline.mark_deleted(0), Ok(()));
        assert_eq!(timeline.kind_at(0), BlockKind::DeletedItem(a));
        assert_eq!(timeline.merge_range(0, 2), Ok(()));
        assert_eq!(timeline.len(), 1);
        assert_eq!(timeline.range(0), Some(0..6));
        assert_eq!(timeline.kind_at(0), BlockKind::DeletedItem(a));
        assert_eq!(timeline.collect(0), Ok(()));
        assert_eq!(timeline.kind_at(0), BlockKind::Gc);
        assert_eq!(timeline.collect(0), Err(StoreError::NotAnItem));
        assert_eq!(timeline.merge_range(0, 1), Err(StoreError::MissingStruct));
    }
}

#[cfg(all(test, not(loom)))]
mod regressions;
