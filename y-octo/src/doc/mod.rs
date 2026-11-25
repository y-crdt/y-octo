mod awareness;
mod codec;
mod common;
mod document;
mod hasher;
mod history;
mod read;
mod redo;
mod relative_position;
mod retention;
#[cfg(feature = "session")]
pub mod session;
mod store;
#[cfg(test)]
mod tests;
mod transaction;
pub(crate) mod types;
mod undo;
mod utils;

#[cfg(not(loom))]
pub use ahash::{HashMap, HashSet};
pub use ahash::{HashMapExt, HashSetExt};
// Replaying a model must visit entries in the same order on every run.
#[cfg(loom)]
pub type HashMap<K, V> = std::collections::HashMap<K, V, std::hash::BuildHasherDefault<ahash::AHasher>>;
#[cfg(loom)]
pub type HashSet<K> = std::collections::HashSet<K, std::hash::BuildHasherDefault<ahash::AHasher>>;
pub use awareness::{Awareness, AwarenessEvent};
pub use codec::*;
pub use common::*;
pub(crate) use document::subdocument;
pub use document::{Doc, DocOptions, LocalUpdate, revert_update_v1};
#[cfg(feature = "debug")]
pub use document::{DocMemoryLayout, memory_layout, profiling_counters, reset_profiling_counters};
pub use hasher::ClientMap;
pub use history::{History, HistoryOptions, StoreHistory};
pub use read::*;
pub(crate) use redo::RedoMap;
pub use relative_position::{AbsolutePosition, RelativePosition};
use smol_str::SmolStr;
#[cfg(any(test, feature = "debug"))]
pub(crate) use store::BlockRef;
pub(crate) use store::{BlockKind, ClientBlocks, DocStore, ItemIdx, ItemSpace, Moved};
pub use transaction::{
    ArrayRead, ArrayWrite, ChangedType, CommitEvent, CommitSummary, IncomingUpdate, MapRead, MapWrite, Origin,
    Subscription, TextRead, TextWrite, Transaction, TransactionMut, XMLElementRead, XMLElementWrite, XMLFragmentRead,
    XMLFragmentWrite, XMLHookRead, XMLHookWrite, XMLTextRead, XMLTextWrite,
};
pub(crate) use transaction::{
    CommitHook, EventHub, after_unlock, or_released, read_store, read_store_or_panic, transact_local_implicit,
    transact_maintenance, transact_mut_with, transact_mut_with_events, write_store,
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
    use std::{collections::HashMap, io::Read, sync::OnceLock};
    static FIXTURES: OnceLock<HashMap<String, Vec<u8>>> = OnceLock::new();
    let fixtures = FIXTURES.get_or_init(|| {
        let mut text = String::new();
        flate2::read::GzDecoder::new(include_bytes!("../fixtures/yjs-legacy.jsonl.gz").as_slice())
            .read_to_string(&mut text)
            .unwrap();
        text.lines()
            .skip(1)
            .filter_map(|line| {
                let record: serde_json::Value = serde_json::from_str(line).unwrap();
                let name = record["name"].as_str()?.to_owned();
                let hex = record["update"].as_str()?;
                let bytes = (0..hex.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
                    .collect();
                Some((name, bytes))
            })
            .collect()
    });
    fixtures.get(name).unwrap().clone()
}
