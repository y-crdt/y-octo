use std::{
    collections::hash_map::Entry,
    ops::{Deref, DerefMut, Range},
};

use super::*;
use crate::doc::OrderRange;

impl<W: CrdtWriter> CrdtWrite<W> for Range<u64> {
    fn write(&self, encoder: &mut W) -> JwstCodecResult {
        encoder.write_var_u64(self.start)?;
        encoder.write_var_u64(self.end - self.start)?;
        Ok(())
    }
}

impl<W: CrdtWriter> CrdtWrite<W> for OrderRange {
    fn write(&self, encoder: &mut W) -> JwstCodecResult {
        // canonicalize like yjs' sortAndMergeDeleteSet so the wire format is
        // stable no matter how the ranges were inserted or decoded
        write_ranges(&self.canonical_ranges(), encoder)
    }
}

fn write_ranges<W: CrdtWriter>(ranges: &[Range<u64>], encoder: &mut W) -> JwstCodecResult {
    encoder.write_var_u64(ranges.len() as u64)?;
    for range in ranges {
        range.write(encoder)?;
    }
    Ok(())
}

#[derive(Debug, Default, Clone, PartialEq)]
pub struct DeleteSet(pub ClientMap<OrderRange>);

impl Deref for DeleteSet {
    type Target = ClientMap<OrderRange>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const N: usize> From<[(Client, Vec<Range<u64>>); N]> for DeleteSet {
    fn from(value: [(Client, Vec<Range<u64>>); N]) -> Self {
        let mut map = ClientMap::with_capacity(N);
        for (client, ranges) in value {
            map.insert(client, ranges.into());
        }
        Self(map)
    }
}

impl DerefMut for DeleteSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl DeleteSet {
    pub fn add(&mut self, client: Client, from: Clock, len: Clock) {
        self.add_range(client, from..from + len);
    }

    pub fn add_range(&mut self, client: Client, range: Range<u64>) {
        match self.0.entry(client) {
            Entry::Occupied(e) => {
                let r = e.into_mut();
                if r.is_empty() {
                    *r = range.into();
                } else {
                    r.push(range);
                }
            }
            Entry::Vacant(e) => {
                e.insert(range.into());
            }
        }
    }

    pub fn batch_add_ranges(&mut self, client: Client, ranges: Vec<Range<u64>>) {
        match self.0.entry(client) {
            Entry::Occupied(e) => {
                e.into_mut().extend(ranges);
            }
            Entry::Vacant(e) => {
                e.insert(ranges.into());
            }
        }
    }

    pub fn merge(&mut self, other: &Self) {
        for (client, range) in &other.0 {
            match self.0.entry(*client) {
                Entry::Occupied(e) => {
                    e.into_mut().merge(range.clone());
                }
                Entry::Vacant(e) => {
                    e.insert(range.clone());
                }
            }
        }
    }
}

impl<W: CrdtWriter> CrdtWrite<W> for DeleteSet {
    fn write(&self, encoder: &mut W) -> JwstCodecResult {
        // skip clients whose ranges canonicalize to nothing (e.g. only
        // zero-length ranges), keeping the wire format minimal and stable
        let mut clients = self
            .iter()
            .filter_map(|(&client, ranges)| {
                let ranges = ranges.canonical_ranges();
                (!ranges.is_empty()).then_some((client, ranges))
            })
            .collect::<Vec<_>>();
        clients.sort_unstable_by_key(|entry| std::cmp::Reverse(entry.0));

        encoder.write_var_u64(clients.len() as u64)?;

        for (client, ranges) in clients {
            encoder.write_var_u64(client)?;
            write_ranges(&ranges, encoder)?;
        }

        Ok(())
    }
}

#[cfg(test)]
#[allow(clippy::single_range_in_vec_init)]
mod tests {
    use super::*;

    #[test]
    fn test_delete_set_add() {
        let delete_set = DeleteSet::from([
            (1, vec![0..10, 20..30]),
            (2, vec![0..5, 10..20]),
            (3, vec![15..20, 30..35]),
            (4, vec![0..10]),
        ]);

        {
            let mut delete_set = delete_set.clone();
            delete_set.add(1, 5, 25);
            assert_eq!(delete_set.get(&1), Some(&OrderRange::Range(0..30)));
        }

        {
            let mut delete_set = delete_set;
            delete_set.add(1, 5, 10);
            assert_eq!(delete_set.get(&1), Some(&OrderRange::from(vec![0..15, 20..30])));
        }
    }

    #[test]
    fn test_delete_set_batch_push() {
        let delete_set = DeleteSet::from([
            (1, vec![0..10, 20..30]),
            (2, vec![0..5, 10..20]),
            (3, vec![15..20, 30..35]),
            (4, vec![0..10]),
        ]);

        {
            let mut delete_set = delete_set.clone();
            delete_set.batch_add_ranges(1, vec![0..5, 10..20]);
            assert_eq!(delete_set.get(&1), Some(&OrderRange::Range(0..30)));
        }

        {
            let mut delete_set = delete_set;
            delete_set.batch_add_ranges(1, vec![40..50, 10..20]);
            assert_eq!(delete_set.get(&1), Some(&OrderRange::from(vec![0..30, 40..50])));
        }
    }

    #[test]
    fn test_encode_decode() {
        let delete_set = DeleteSet::from([(1, vec![0..10, 20..30]), (2, vec![0..5, 10..20])]);
        let update = Update {
            delete_set: delete_set.clone(),
            ..Update::default()
        };
        let decoded = Update::decode_v1(update.encode_v1().unwrap()).unwrap();
        assert_eq!(delete_set, decoded.delete_set);
    }
}
