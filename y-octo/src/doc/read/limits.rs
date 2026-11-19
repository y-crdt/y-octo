use thiserror::Error;

use crate::JwstCodecError;

#[derive(Debug, Clone)]
pub struct ReadLimits {
    pub max_input_bytes: usize,
    pub max_structs: usize,
    pub max_clients: usize,
    pub max_collection_entries: usize,
    /// Deepest `Any` nesting accepted, [crate::Any::DEFAULT_MAX_DEPTH] by
    /// default. Values above [crate::Any::MAX_CONFIGURABLE_DEPTH] act as that
    /// limit, and 0 accepts scalars and empty containers only. Deeper values
    /// fail with `ReadError::ResourceLimit("Any nesting depth")`. Yjs puts no
    /// limit on the wire, so trusted callers reading deeper documents raise it
    /// here.
    pub max_any_depth: usize,
    pub max_content_bytes: usize,
}

impl Default for ReadLimits {
    fn default() -> Self {
        Self {
            max_input_bytes: 1 << 30,
            max_structs: 2_000_000,
            max_clients: 100_000,
            max_collection_entries: 10_000_000,
            max_any_depth: crate::Any::DEFAULT_MAX_DEPTH,
            max_content_bytes: 1 << 30,
        }
    }
}

#[derive(Debug, Error)]
pub enum ReadError {
    #[error("invalid update: {0}")]
    InvalidUpdate(#[source] JwstCodecError),
    #[error("incomplete snapshot: {0}")]
    IncompleteSnapshot(&'static str),
    #[error("read resource limit exceeded: {0}")]
    ResourceLimit(&'static str),
}

impl From<JwstCodecError> for ReadError {
    fn from(value: JwstCodecError) -> Self {
        Self::InvalidUpdate(value)
    }
}
