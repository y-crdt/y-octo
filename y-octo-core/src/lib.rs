#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]
// The code is written the way Aeneas extracts without external stubs; the
// lints below ask for the shapes it has no model of (`Vec::clear` is one:
// `new_instead_of_clear` is a nightly lint, hence `unknown_lints`; so are
// `Option::take`, `mem::take`, `usize::is_multiple_of` and `vec![x]` of a
// value that is not `Clone`, which the last six stand for). A negation as the
// value of a branch is extracted as a proposition where a `bool` is meant, so
// such an answer is spelled out (`needless_bool`).
#![allow(
    unknown_lints,
    clippy::needless_bool,
    clippy::manual_range_contains,
    clippy::if_same_then_else,
    clippy::implicit_saturating_sub,
    clippy::manual_map,
    clippy::redundant_pattern_matching,
    clippy::question_mark,
    clippy::single_match,
    clippy::new_instead_of_clear,
    clippy::mem_replace_option_with_none,
    clippy::mem_replace_with_default,
    clippy::collapsible_match,
    clippy::manual_is_multiple_of,
    clippy::vec_init_then_push,
    clippy::vec_resize_to_zero
)]

extern crate alloc;

pub mod client_blocks;
pub mod clock_search;
pub mod decoder_v1;
pub mod delete_set;
pub mod doc_kernel;
pub mod id_order;
pub mod id_set;
pub mod item_space;
pub mod order_range;
pub mod pending;
pub mod state_vector;
pub mod utf16;
pub mod varint;
pub mod yata_store;

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum LimitKind {
    Clients,
    DeleteClients,
    Structs,
    CollectionEntries,
    ContentBytes,
    AnyDepth,
    ContentEntries,
    AnyObjectEntries,
    AnyArrayEntries,
    DeleteRanges,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum CodecError {
    UnexpectedEof,
    VarintOverflow,
    LengthOverflow,
    ZeroLengthStruct,
    ClockOverflow,
    DuplicateClient,
    TrailingBytes,
    InvalidUtf8,
    UnknownContentTag,
    UnknownAnyTag,
    UnknownTypeKind,
    LimitExceeded,
    UnexpectedByteEof,
    BufferTooLarge,
    BufferLengthOverflow,
    BufferExceedsUpdate,
    UnknownContentTagByte(u8),
    UnknownAnyTagByte(u8),
    ResourceLimit(LimitKind),
    CountTooLarge(LimitKind),
    SinkAborted,
}

#[cfg(test)]
mod tests {
    use super::CodecError;

    #[test]
    fn codec_error_is_at_most_two_bytes() {
        assert!(core::mem::size_of::<CodecError>() <= 2);
    }
}
