#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]
// The code is written the way Aeneas extracts without external stubs; the
// lints below ask for the shapes it has no model of (`Vec::clear` is one:
// `new_instead_of_clear` is a nightly lint, hence `unknown_lints`).
#![allow(
    unknown_lints,
    clippy::manual_range_contains,
    clippy::if_same_then_else,
    clippy::implicit_saturating_sub,
    clippy::manual_map,
    clippy::redundant_pattern_matching,
    clippy::question_mark,
    clippy::single_match,
    clippy::new_instead_of_clear
)]

extern crate alloc;

pub mod client_blocks;
pub mod clock_search;
pub mod decoder_v1;
pub mod delete_set;
pub mod order_range;
pub mod state_vector;
pub mod utf16;
pub mod varint;
pub mod yata_store;

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
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
}
