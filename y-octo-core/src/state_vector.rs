use alloc::vec::Vec;

/// Pure sorted-`Vec` state vector (`(client, clock)` sorted strictly by
/// `client`).
#[derive(Clone)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct StateVectorCore {
    pub entries: Vec<(u64, u64)>,
}

impl Default for StateVectorCore {
    fn default() -> Self {
        Self::new()
    }
}

impl StateVectorCore {
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
            let c = self.entries[mid].0;
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

    pub fn get(&self, client: u64) -> u64 {
        let (found, idx) = self.find_index(client);
        if found { self.entries[idx].1 } else { 0 }
    }

    /// Mirrors `y_octo::StateVector::contains`: `clock <= self.get(client)`.
    pub fn contains(&self, client: u64, clock: u64) -> bool {
        clock <= self.get(client)
    }

    /// Overwrites `client`'s clock with `clock` (or inserts `(client, clock)`
    /// if absent), matching V1 wire decoding's last-write-wins semantics.
    pub fn set(&mut self, client: u64, clock: u64) {
        let (found, idx) = self.find_index(client);
        if found {
            self.entries[idx].1 = clock;
        } else if idx == self.entries.len() {
            self.entries.push((client, clock));
        } else {
            self.entries.insert(idx, (client, clock));
        }
    }

    /// Inserts or raises `client`'s clock to `max(existing, clock)`.
    pub fn set_max(&mut self, client: u64, clock: u64) {
        let (found, idx) = self.find_index(client);
        if found {
            if self.entries[idx].1 < clock {
                self.entries[idx].1 = clock;
            }
        } else if idx == self.entries.len() {
            self.entries.push((client, clock));
        } else {
            self.entries.insert(idx, (client, clock));
        }
    }

    /// Mirrors `y_octo::StateVector::set_min`: if `client` is present, sets
    /// `min(existing, clock)`; otherwise inserts `(client, clock)`.
    pub fn set_min(&mut self, client: u64, clock: u64) {
        let (found, idx) = self.find_index(client);
        if found {
            if self.entries[idx].1 > clock {
                self.entries[idx].1 = clock;
            }
        } else if idx == self.entries.len() {
            self.entries.push((client, clock));
        } else {
            self.entries.insert(idx, (client, clock));
        }
    }

    /// Mirrors `y_octo::StateVector::merge_with`: applies `set_min` for every
    /// entry in `other`.
    pub fn merge_with(&mut self, other: &StateVectorCore) {
        let mut i = 0usize;
        while i < other.entries.len() {
            let (c, clk) = other.entries[i];
            self.set_min(c, clk);
            i += 1;
        }
    }

    /// Applies `set_max` for every entry in `other`.
    pub fn merge_max(&mut self, other: &StateVectorCore) {
        let mut i = 0usize;
        while i < other.entries.len() {
            let (c, clk) = other.entries[i];
            self.set_max(c, clk);
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn state_vector_ops() {
        let mut sv = StateVectorCore::new();
        sv.set_max(3, 10);
        sv.set_max(1, 4);
        sv.set_max(2, 6);
        sv.set_max(1, 2);
        assert_eq!(sv.get(1), 4);
        assert_eq!(sv.get(99), 0);
        assert!(sv.contains(1, 4));
        assert!(!sv.contains(1, 5));

        let mut other = StateVectorCore::new();
        other.set_max(1, 2);
        other.set_max(4, 7);
        sv.merge_with(&other);
        assert_eq!(sv.get(1), 2);
        assert_eq!(sv.get(4), 7);
    }
}
