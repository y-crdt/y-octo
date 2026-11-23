use super::{item_space::ItemIdx, *};

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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BlockRef {
    pub clock: Clock,
    pub kind: BlockKind,
}

const _: () = assert!(size_of::<BlockRef>() == 16);

/// A block ends exactly where its successor starts. The final boundary is
/// kept separately so the complete V1 u64 range needs no per-block length.
#[derive(Debug, Default)]
pub(crate) struct ClientBlocks {
    pub(super) blocks: VecDeque<BlockRef>,
    pub end_clock: Clock,
}

impl ClientBlocks {
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    pub fn node(&self, client: Client, index: usize) -> Option<Node> {
        let block = self.blocks.get(index)?;
        let end = self.blocks.get(index + 1).map_or(self.end_clock, |next| next.clock);
        Some(Node {
            id: Id::new(client, block.clock),
            len: end - block.clock,
            kind: block.kind,
        })
    }

    pub fn nodes(&self, client: Client) -> impl DoubleEndedIterator<Item = Node> + '_ {
        (0..self.len()).map(move |i| self.node(client, i).expect("block index"))
    }

    pub(in crate::doc) fn remap(&mut self, moved: &[ItemRef]) {
        for block in &mut self.blocks {
            match &mut block.kind {
                BlockKind::Item(i) | BlockKind::DeletedItem(i) => {
                    *i = moved[i.slot()].expect("timeline refers to a live item");
                }
                _ => {}
            }
        }
    }

    pub fn append(&mut self, block: BlockRef, len: u64) -> JwstCodecResult {
        if !self.blocks.is_empty() && block.clock != self.end_clock {
            return Err(JwstCodecError::StructClockInvalid {
                expect: self.end_clock,
                actually: block.clock,
            });
        }
        let end = block
            .clock
            .checked_add(len)
            .ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
        self.blocks.push_back(block);
        self.end_clock = end;
        Ok(())
    }

    #[inline]
    pub fn range(&self, index: usize) -> Option<Range<Clock>> {
        let start = self.blocks.get(index)?.clock;
        let end = self.blocks.get(index + 1).map_or(self.end_clock, |next| next.clock);
        Some(start..end)
    }

    pub fn find(&self, clock: Clock) -> Option<usize> {
        if clock >= self.end_clock {
            return None;
        }
        self.blocks.partition_point(|b| b.clock <= clock).checked_sub(1)
    }

    pub fn deleted_ranges(&self) -> impl Iterator<Item = Range<Clock>> + '_ {
        self.blocks.iter().enumerate().filter_map(|(i, b)| {
            b.kind
                .deleted()
                .then(|| self.range(i).expect("block index"))
                .filter(|r| !r.is_empty())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_width_ranges_and_empty_boundaries() {
        let mut timeline = ClientBlocks::default();
        let long = u64::from(u32::MAX) + 11;
        let block = |clock, kind| BlockRef { clock, kind };
        timeline.append(block(0, BlockKind::Gc), long).unwrap();
        timeline.append(block(long, BlockKind::Skip), 0).unwrap();
        timeline.append(block(long, BlockKind::Skip), u64::MAX - long).unwrap();
        assert_eq!(timeline.range(0), Some(0..long));
        assert_eq!(timeline.range(2), Some(long..u64::MAX));
        assert_eq!(timeline.find(long - 1), Some(0));
        assert_eq!(timeline.find(long), Some(2));
        assert_eq!(timeline.find(u64::MAX - 1), Some(2));
        assert_eq!(timeline.find(u64::MAX), None);
        assert!(timeline.append(block(u64::MAX, BlockKind::Gc), 1).is_err());
        assert_eq!(timeline.blocks.len(), 3);
        assert_eq!(timeline.deleted_ranges().collect::<Vec<_>>(), [0..long, long..u64::MAX]);
    }
}
