use alloc::vec::Vec;

use crate::{CodecError, order_range::OrderRange};

#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
pub struct DeleteSetEntry {
    pub client: u64,
    pub range: OrderRange,
}

/// Pure sorted-`Vec` delete set (`entries` sorted strictly by `client`, each
/// with a non-empty canonical `OrderRange`).
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
pub struct DeleteSetCore {
    pub entries: Vec<DeleteSetEntry>,
}

impl Default for DeleteSetCore {
    fn default() -> Self {
        Self::new()
    }
}

impl DeleteSetCore {
    pub fn new() -> Self {
        Self { entries: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    fn find_index(&self, client: u64) -> (bool, usize) {
        let mut low = 0usize;
        let mut high = self.entries.len();
        while low < high {
            let mid = low + (high - low) / 2;
            let c = self.entries[mid].client;
            if c == client {
                return (true, mid);
            } else if c < client {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        (false, low)
    }

    pub fn contains(&self, client: u64, clock: u64) -> bool {
        let (found, idx) = self.find_index(client);
        if found {
            self.entries[idx].range.contains(clock)
        } else {
            false
        }
    }

    pub fn insert(&mut self, client: u64, start: u64, end: u64) {
        assert!(self.try_insert(client, start, end).is_ok());
    }

    pub fn try_insert(&mut self, client: u64, start: u64, end: u64) -> Result<(), CodecError> {
        if start >= end {
            return Ok(());
        }
        let (found, idx) = self.find_index(client);
        if found {
            return self.entries[idx].range.try_insert(start, end);
        }
        let entry = DeleteSetEntry {
            client,
            range: OrderRange::from_range(start, end),
        };
        if idx == self.entries.len() {
            self.entries.push(entry);
        } else {
            self.entries.insert(idx, entry);
        }
        Ok(())
    }

    pub fn merge(&mut self, other: &DeleteSetCore) {
        let mut i = 0usize;
        while i < other.entries.len() {
            let client = other.entries[i].client;
            let mut j = 0usize;
            while let Some(r) = other.entries[i].range.get(j) {
                self.insert(client, r.start, r.end);
                j += 1;
            }
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn delete_set_ops() {
        let mut a = DeleteSetCore::new();
        a.insert(2, 10, 20);
        a.insert(1, 0, 5);
        a.insert(1, 5, 10);

        let mut b = DeleteSetCore::new();
        b.insert(1, 8, 12);
        b.insert(3, 0, 3);

        a.merge(&b);
        assert!(a.contains(1, 0));
        assert!(a.contains(1, 11));
        assert!(!a.contains(1, 12));
        assert!(a.contains(2, 15));
        assert!(a.contains(3, 2));
    }
}
