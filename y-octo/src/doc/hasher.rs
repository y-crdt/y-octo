use std::{collections::HashMap, hash::BuildHasher};

use super::Client;

// Client IDs come from remote peers. An unseeded identity hash lets a peer pick
// IDs that collide in every probe sequence (O(n²) decoding), so client maps are
// keyed with a seeded hasher like the rest of the crate.
#[cfg(not(loom))]
type ClientHasherState = ahash::RandomState;
// Loom needs every execution of a model to iterate maps in the same order; see
// `doc::HashMap`.
#[cfg(loom)]
type ClientHasherState = std::hash::BuildHasherDefault<ahash::AHasher>;

#[derive(Default, Clone)]
pub struct ClientHasherBuilder(ClientHasherState);

impl BuildHasher for ClientHasherBuilder {
    type Hasher = ahash::AHasher;

    fn build_hasher(&self) -> Self::Hasher {
        self.0.build_hasher()
    }
}

// use ClientID as key
pub type ClientMap<V> = HashMap<Client, V, ClientHasherBuilder>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(not(loom))]
    fn client_hashes_are_seeded() {
        // the old identity hash returned the client ID itself
        let state = ClientHasherBuilder::default();
        let clients = [0u64, 1 << 20, 2 << 20, 3 << 20];
        assert!(clients.iter().any(|client| state.hash_one(client) != *client));
        assert_ne!(
            ClientHasherBuilder::default().hash_one(1u64),
            ClientHasherBuilder::default().hash_one(1u64)
        );
    }
}
