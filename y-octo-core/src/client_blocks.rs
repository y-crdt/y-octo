//! The block timeline of one client: the index half of `ClientBlocks` in
//! `y-octo/src/doc/store/client_blocks.rs`.
//!
//! A block ends where its successor starts and the last one ends at
//! `end_clock`, so a block holds no length of its own. Unlike the store of
//! `y-octo`, which keeps the zero-length `Skip` boundaries of an update, this
//! core refuses a zero-length block: clocks are strictly increasing.

use alloc::vec::Vec;

/// A timeline never holds more blocks than a `u32` slot index can name.
pub const MAX_BLOCKS: usize = 4_294_967_295;

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
    pub fn deleted(self) -> bool {
        match self {
            BlockKindCore::Item(_) => false,
            BlockKindCore::DeletedItem(_) => true,
            BlockKindCore::Gc => true,
            BlockKindCore::Skip => true,
        }
    }

    /// The arena slot of an item block.
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

#[cfg_attr(not(aeneas_extract), derive(Clone, Debug, PartialEq, Eq))]
pub struct ClientBlocksCore {
    pub blocks: Vec<BlockRefCore>,
    pub end_clock: u64,
}

impl Default for ClientBlocksCore {
    fn default() -> Self {
        Self::new()
    }
}

impl ClientBlocksCore {
    pub fn new() -> Self {
        Self {
            blocks: Vec::new(),
            end_clock: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Whether a block that starts at `clock` continues the timeline: the
    /// first block may start at any clock.
    pub fn continues(&self, clock: u64) -> bool {
        if self.blocks.is_empty() {
            true
        } else {
            clock == self.end_clock
        }
    }

    /// Appends a block of `len` clocks. The first block of a timeline may
    /// start at any clock; every other one has to continue the timeline.
    pub fn append(&mut self, block: BlockRefCore, len: u64) -> Result<(), StoreError> {
        if len == 0 {
            return Err(StoreError::ZeroLength);
        }
        if !self.continues(block.clock) {
            return Err(StoreError::ClockMismatch);
        }
        if len > u64::MAX - block.clock {
            return Err(StoreError::ClockOverflow);
        }
        if self.blocks.len() >= MAX_BLOCKS {
            return Err(StoreError::Capacity);
        }
        self.blocks.push(block);
        self.end_clock = block.clock + len;
        Ok(())
    }

    /// The clocks `start..end` of the block at `index`.
    pub fn range(&self, index: usize) -> Option<(u64, u64)> {
        if index >= self.blocks.len() {
            return None;
        }
        let start = self.blocks[index].clock;
        let next = index + 1;
        let end = if next < self.blocks.len() {
            self.blocks[next].clock
        } else {
            self.end_clock
        };
        Some((start, end))
    }

    /// Index of the block that holds `clock`: the last block that starts at
    /// or before it.
    pub fn find(&self, clock: u64) -> Option<usize> {
        if clock >= self.end_clock {
            return None;
        }
        let mut low = 0usize;
        let mut high = self.blocks.len();
        while low < high {
            let mid = low + (high - low) / 2;
            if self.blocks[mid].clock <= clock {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        if low == 0 { None } else { Some(low - 1) }
    }

    /// Splits the block at `index` in two at `clock`, which has to lie
    /// strictly inside it; the new right half is of kind `kind`.
    pub fn split_boundary(&mut self, index: usize, clock: u64, kind: BlockKindCore) -> Result<(), StoreError> {
        let (start, end) = match self.range(index) {
            Some(range) => range,
            None => return Err(StoreError::MissingStruct),
        };
        if clock <= start || clock >= end {
            return Err(StoreError::InvalidSplit);
        }
        if self.blocks.len() >= MAX_BLOCKS {
            return Err(StoreError::Capacity);
        }
        let block = BlockRefCore { clock, kind };
        let at = index + 1;
        if at == self.blocks.len() {
            self.blocks.push(block);
        } else {
            self.blocks.insert(at, block);
        }
        Ok(())
    }

    /// Makes the blocks at `index` and `index + 1` one block of the kind of
    /// the first; they have to be of the same kind.
    pub fn merge_adjacent(&mut self, index: usize) -> Result<(), StoreError> {
        if index >= self.blocks.len() {
            return Err(StoreError::MissingStruct);
        }
        let next = index + 1;
        if next >= self.blocks.len() {
            return Err(StoreError::MissingStruct);
        }
        if !self.blocks[index].kind.same_kind(self.blocks[next].kind) {
            return Err(StoreError::NotMergeable);
        }
        let mut out = Vec::new();
        let mut i = 0usize;
        while i < next {
            out.push(self.blocks[i]);
            i += 1;
        }
        let mut j = next + 1;
        while j < self.blocks.len() {
            out.push(self.blocks[j]);
            j += 1;
        }
        self.blocks = out;
        Ok(())
    }

    /// Marks the item block at `index` deleted.
    pub fn mark_deleted(&mut self, index: usize) -> Result<(), StoreError> {
        if index >= self.blocks.len() {
            return Err(StoreError::MissingStruct);
        }
        match self.blocks[index].kind {
            BlockKindCore::Item(idx) => {
                self.blocks[index].kind = BlockKindCore::DeletedItem(idx);
                Ok(())
            }
            BlockKindCore::DeletedItem(_) => Ok(()),
            BlockKindCore::Gc => Err(StoreError::NotAnItem),
            BlockKindCore::Skip => Err(StoreError::NotAnItem),
        }
    }

    /// Replaces the deleted item block at `index` by a collected range and
    /// returns the slot it held. A live item is not collected.
    pub fn mark_gc(&mut self, index: usize) -> Result<u32, StoreError> {
        if index >= self.blocks.len() {
            return Err(StoreError::MissingStruct);
        }
        match self.blocks[index].kind {
            BlockKindCore::DeletedItem(idx) => {
                self.blocks[index].kind = BlockKindCore::Gc;
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
    use super::*;

    fn block(clock: u64, kind: BlockKindCore) -> BlockRefCore {
        BlockRefCore { clock, kind }
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
        assert_eq!(timeline.end_clock, u64::MAX);
        assert_eq!(
            timeline.append(block(u64::MAX, BlockKindCore::Gc), 1),
            Err(StoreError::ClockOverflow)
        );
        assert_eq!(timeline.len(), 2);
        assert_eq!(timeline.range(0), Some((4, 7)));
        assert_eq!(timeline.range(1), Some((7, u64::MAX)));
        assert_eq!(timeline.range(2), None);
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
            timeline.blocks,
            [
                block(0, BlockKindCore::Item(0)),
                block(4, BlockKindCore::Item(2)),
                block(10, BlockKindCore::Item(1)),
                block(12, BlockKindCore::Item(3)),
            ]
        );
        assert_eq!(timeline.end_clock, 15);

        assert_eq!(timeline.mark_gc(1), Err(StoreError::NotAnItem));
        assert_eq!(timeline.mark_deleted(1), Ok(()));
        assert_eq!(timeline.mark_deleted(1), Ok(()));
        assert_eq!(timeline.mark_deleted(4), Err(StoreError::MissingStruct));
        assert_eq!(timeline.blocks[1].kind, BlockKindCore::DeletedItem(2));
        assert_eq!(timeline.merge_adjacent(0), Err(StoreError::NotMergeable));
        assert_eq!(timeline.merge_adjacent(3), Err(StoreError::MissingStruct));
        assert_eq!(timeline.merge_adjacent(2), Ok(()));
        assert_eq!(timeline.range(2), Some((10, 15)));
        assert_eq!(timeline.mark_gc(1), Ok(2));
        assert_eq!(timeline.mark_gc(1), Err(StoreError::NotAnItem));
        assert_eq!(timeline.mark_deleted(1), Err(StoreError::NotAnItem));
        assert_eq!(timeline.find(9), Some(1));
        assert_eq!(timeline.blocks.len(), 3);
    }
}
