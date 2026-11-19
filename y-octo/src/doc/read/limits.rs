use thiserror::Error;

use crate::JwstCodecError;

#[derive(Debug, Clone)]
pub struct ReadLimits {
    pub max_input_bytes: usize,
    pub max_structs: usize,
    pub max_clients: usize,
    pub max_collection_entries: usize,
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
            max_any_depth: 128,
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
