mod awareness;
mod codec;
mod common;
#[cfg(test)]
mod concurrency;
mod document;
mod hasher;
mod history;
#[cfg(all(test, not(loom)))]
mod live_edit_tests;
#[cfg(all(test, not(loom)))]
mod local_update_tests;
mod read;
mod redo;
mod relative_position;
mod retention;
mod store;
mod transaction;
#[cfg(all(test, not(loom)))]
mod transaction_tests;
pub(crate) mod types;
mod undo;
mod utils;

#[cfg(not(loom))]
pub use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
#[cfg(loom)]
pub use ahash::{HashMapExt, HashSetExt};
// Under loom every execution of a model must perform the same synchronization
// operations in the same order. ahash seeds each map randomly, so iteration
// and drop order (and with it the order of `Somr` refcount updates) would
// change between executions; use fixed keys instead.
#[cfg(loom)]
pub type HashMap<K, V> = std::collections::HashMap<K, V, std::hash::BuildHasherDefault<ahash::AHasher>>;
#[cfg(loom)]
pub type HashSet<K> = std::collections::HashSet<K, std::hash::BuildHasherDefault<ahash::AHasher>>;
pub use awareness::{Awareness, AwarenessEvent};
pub use codec::*;
pub use common::*;
pub use document::{Doc, DocOptions, LocalUpdate};
#[cfg(feature = "debug")]
pub use document::{DocMemoryLayout, memory_layout, profiling_counters, reset_profiling_counters};
pub use hasher::ClientMap;
pub use history::{History, HistoryOptions, StoreHistory};
pub use read::*;
pub(crate) use redo::RedoMap;
pub use relative_position::{AbsolutePosition, RelativePosition};
use smol_str::SmolStr;
pub(crate) use store::DocStore;
pub use transaction::{
    ArrayRead, ArrayWrite, ChangedType, CommitEvent, CommitSummary, IncomingUpdate, MapRead, MapWrite, Origin,
    Subscription, TextRead, TextWrite, Transaction, TransactionMut,
};
pub(crate) use transaction::{
    CommitHook, EventHub, after_unlock, or_released, read_store, read_store_or_panic, transact_mut_with, write_store,
};
pub use types::*;
pub use undo::{UndoItem, UndoManager, UndoOptions, UndoOrigin, UndoScope, UndoStack};
pub use utils::*;

use super::*;

/// NOTE:
///   - We do not use [HashMap::with_capacity(num_of_clients)] directly here
///     because we don't trust the input data.
///   - For instance, what if the first u64 was somehow set a very big value?
///     - A pre-allocated HashMap with a big capacity may cause OOM.
///     - A kinda safer approach is give it a max capacity of 1024 at first
///       allocation, and then let std makes the growth as need.
pub const HASHMAP_SAFE_CAPACITY: usize = 1 << 10;

#[cfg(test)]
pub(crate) fn yjs_fixture(name: &str) -> Vec<u8> {
    use std::io::Read;
    let mut text = String::new();
    flate2::read::GzDecoder::new(include_bytes!("../fixtures/yjs-legacy.jsonl.gz").as_slice())
        .read_to_string(&mut text)
        .unwrap();
    let fixture = text
        .lines()
        .skip(1)
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .find(|record| record["name"] == name)
        .unwrap();
    let hex = fixture["update"].as_str().unwrap();
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
}
