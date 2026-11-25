use alloc::vec::Vec;

use crate::{
    CodecError, LimitKind,
    delete_set::DeleteSetCore,
    state_vector::StateVectorCore,
    utf16::{is_valid_utf8, utf16_len},
    varint::{decode_var_i32_with_sign, decode_var_u64},
};

const MIN_CLIENT_BYTES: u64 = 3;
const MIN_STRUCT_BYTES: u64 = 2;
const MIN_DELETE_CLIENT_BYTES: u64 = 2;
const MIN_DELETE_RANGE_BYTES: u64 = 2;
const MIN_ENTRY_BYTES: u64 = 1;
const MIN_OBJECT_ENTRY_BYTES: u64 = 2;

const ITEM_HAS_PARENT_SUB: u8 = 0b0010_0000;
const ITEM_HAS_RIGHT_ID: u8 = 0b0100_0000;
const ITEM_HAS_LEFT_ID: u8 = 0b1000_0000;

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct DecodeLimitsCore {
    pub max_structs: usize,
    pub max_clients: usize,
    pub max_collection_entries: usize,
    pub max_any_depth: usize,
    pub max_content_bytes: usize,
}

impl DecodeLimitsCore {
    pub fn default_update() -> Self {
        Self {
            max_structs: usize::MAX,
            max_clients: usize::MAX,
            max_collection_entries: usize::MAX,
            max_any_depth: 128,
            max_content_bytes: usize::MAX,
        }
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct UpdateSummary {
    pub clients: usize,
    pub structs: usize,
    pub delete_clients: usize,
    pub delete_ranges: usize,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct WireId {
    pub client: u64,
    pub clock: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub enum WireParentCore {
    Root(Span),
    Item(WireId),
    Inherit,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(aeneas_extract), derive(Debug, PartialEq, Eq))]
pub struct ItemMetaCore {
    pub origin_left: Option<WireId>,
    pub origin_right: Option<WireId>,
    pub parent: WireParentCore,
    pub parent_sub: Option<Span>,
    pub raw_range: Span,
}

/// Event-driven V1 Update decoder sink with zero lifetime parameters.
///
/// All variable-length strings, byte slices and raw item ranges are delivered
/// as validated [`Span`] offsets into `input` satisfying
/// `start <= end <= input.len()`.
///
/// # UTF-8 validation responsibility
///
/// - When [`V1Sink::core_validates_utf8`] returns `true` (e.g.
///   [`SummarySink`]), the core validates RFC 3629 UTF-8 on every string span
///   before emitting callbacks and does not call
///   [`V1Sink::validate_utf8_early`].
/// - When `core_validates_utf8` returns `false` (e.g. production `Adapter`),
///   spans consumed later (`Root`, `parent_sub`, `Format` key, subdoc `guid`)
///   are checked eagerly via [`V1Sink::validate_utf8_early`] (`slot` `0..=3`)
///   at parse time so error precedence is unchanged while remaining strings are
///   validated once by the sink itself.
///
/// # Error reporting and callback totality
///
/// Methods are assumed total (panic-free) on valid [`Span`]s. On selected
/// framing/limit failures (`UnexpectedEof`, `VarintOverflow`, `ClockOverflow`,
/// `TrailingBytes`, `UnknownTypeKind`, `CountTooLarge`), the decoder invokes
/// [`V1Sink::on_decode_error`] on a cold path with auxiliary context `(a, b)`
/// before returning the compact `<= 2`-byte [`CodecError`].
pub trait V1Sink {
    fn core_validates_utf8(&self) -> bool;
    fn validate_utf8_early(&mut self, slot: u8, value: Span) -> Result<(), CodecError>;
    fn on_decode_error(&mut self, err: CodecError, a: usize, b: u64);

    fn record_client(&mut self, client: u64) -> Result<bool, CodecError>;
    fn begin_client(&mut self, client: u64, count: usize) -> Result<(), CodecError>;

    fn on_gc(&mut self, id: WireId, len: u64) -> Result<(), CodecError>;
    fn on_skip(&mut self, id: WireId, len: u64) -> Result<(), CodecError>;
    fn on_item(&mut self, id: WireId, len: u64, meta: ItemMetaCore) -> Result<(), CodecError>;

    fn on_deleted(&mut self, len: u64) -> Result<(), CodecError>;
    fn on_json_start(&mut self, count: usize) -> Result<(), CodecError>;
    fn on_json_value(&mut self, value: Span) -> Result<(), CodecError>;
    fn on_json_finish(&mut self) -> Result<(), CodecError>;
    fn on_binary(&mut self, value: Span) -> Result<(), CodecError>;
    fn on_string(&mut self, value: Span) -> Result<(), CodecError>;
    fn on_embed(&mut self, value: Span) -> Result<(), CodecError>;
    fn on_format(&mut self, key: Span, value: Span) -> Result<(), CodecError>;
    fn on_type(&mut self, kind: u64, tag: Option<Span>) -> Result<(), CodecError>;
    fn on_any_content_start(&mut self, count: usize) -> Result<(), CodecError>;
    fn on_any_content_value(&mut self) -> Result<(), CodecError>;
    fn on_any_content_finish(&mut self) -> Result<(), CodecError>;
    fn on_doc(&mut self, guid: Span) -> Result<(), CodecError>;

    fn on_any_start(&mut self) -> Result<(), CodecError>;
    fn on_any_undefined(&mut self) -> Result<(), CodecError>;
    fn on_any_null(&mut self) -> Result<(), CodecError>;
    fn on_any_i32(&mut self, value: i32) -> Result<(), CodecError>;
    fn on_any_f32_bits(&mut self, bits: u32) -> Result<(), CodecError>;
    fn on_any_f64_bits(&mut self, bits: u64) -> Result<(), CodecError>;
    fn on_any_i64_bits(&mut self, bits: u64) -> Result<(), CodecError>;
    fn on_any_bool(&mut self, value: bool) -> Result<(), CodecError>;
    fn on_any_str(&mut self, value: Span) -> Result<(), CodecError>;
    fn on_any_bytes(&mut self, value: Span) -> Result<(), CodecError>;
    fn on_any_begin_object(&mut self, count: usize) -> Result<(), CodecError>;
    fn on_any_object_key(&mut self, key: Span) -> Result<(), CodecError>;
    fn on_any_begin_array(&mut self, count: usize) -> Result<(), CodecError>;
    fn on_any_end_container(&mut self) -> Result<(), CodecError>;
    fn on_any_finish(&mut self, range: Span) -> Result<(), CodecError>;

    fn begin_delete_client(&mut self, client: u64, count: usize) -> Result<(), CodecError>;
    fn on_delete_range(&mut self, client: u64, start: u64, end: u64) -> Result<(), CodecError>;
}

/// Sink for streaming V1 `StateVector` decoding.
pub trait SvSink {
    fn on_sv_len(&mut self, count: usize) -> Result<(), CodecError>;
    fn on_sv_entry(&mut self, client: u64, clock: u64) -> Result<(), CodecError>;
}

impl SvSink for StateVectorCore {
    fn on_sv_len(&mut self, _count: usize) -> Result<(), CodecError> {
        Ok(())
    }

    fn on_sv_entry(&mut self, client: u64, clock: u64) -> Result<(), CodecError> {
        self.set(client, clock);
        Ok(())
    }
}

#[inline]
fn checked_usize_from_u64(v: u64) -> Result<usize, CodecError> {
    if v > (usize::MAX as u64) {
        Err(CodecError::LimitExceeded)
    } else {
        Ok(v as usize)
    }
}

#[inline]
fn checked_usize_limit(v: u64, kind: LimitKind) -> Result<usize, CodecError> {
    if v > (usize::MAX as u64) {
        Err(CodecError::ResourceLimit(kind))
    } else {
        Ok(v as usize)
    }
}

#[inline]
fn check_fits(remaining: usize, count: usize, min_bytes: u64) -> Result<(), CodecError> {
    let available = (remaining as u64) / min_bytes;
    if (count as u64) > available {
        Err(CodecError::UnexpectedEof)
    } else {
        Ok(())
    }
}

#[inline]
fn check_fits_kind(remaining: usize, count: usize, min_bytes: u64, kind: LimitKind) -> Result<(), CodecError> {
    let available = (remaining as u64) / min_bytes;
    if (count as u64) > available {
        Err(CodecError::CountTooLarge(kind))
    } else {
        Ok(())
    }
}

#[cold]
#[cfg_attr(not(debug_assertions), inline(always))]
fn fail_with<S: V1Sink>(sink: &mut S, err: CodecError, a: usize, b: u64) -> CodecError {
    sink.on_decode_error(err, a, b);
    err
}

#[inline]
fn check_fits_kind_sink<S: V1Sink>(
    remaining: usize,
    count: usize,
    min_bytes: u64,
    kind: LimitKind,
    sink: &mut S,
) -> Result<(), CodecError> {
    let available = (remaining as u64) / min_bytes;
    if (count as u64) > available {
        Err(fail_with(sink, CodecError::CountTooLarge(kind), count, available))
    } else {
        Ok(())
    }
}

#[inline]
fn checked_add_usize(a: usize, b: usize) -> Result<usize, CodecError> {
    if b > usize::MAX - a {
        Err(CodecError::LimitExceeded)
    } else {
        Ok(a + b)
    }
}

#[inline]
fn checked_add_limit(a: usize, b: usize, kind: LimitKind) -> Result<usize, CodecError> {
    if b > usize::MAX - a {
        Err(CodecError::ResourceLimit(kind))
    } else {
        Ok(a + b)
    }
}

#[inline]
fn read_u8_at(input: &[u8], pos: usize) -> Result<(u8, usize), CodecError> {
    if pos >= input.len() {
        return Err(CodecError::UnexpectedByteEof);
    }
    Ok((input[pos], pos + 1))
}

#[inline]
fn read_u32_be_at(input: &[u8], pos: usize) -> Result<(u32, usize), CodecError> {
    if pos > input.len() || input.len() - pos < 4 {
        return Err(CodecError::UnexpectedByteEof);
    }
    let b0 = (input[pos] as u32) << 24;
    let b1 = (input[pos + 1] as u32) << 16;
    let b2 = (input[pos + 2] as u32) << 8;
    let b3 = input[pos + 3] as u32;
    Ok((b0 | b1 | b2 | b3, pos + 4))
}

#[inline]
fn read_u64_be_at(input: &[u8], pos: usize) -> Result<(u64, usize), CodecError> {
    if pos > input.len() || input.len() - pos < 8 {
        return Err(CodecError::UnexpectedByteEof);
    }
    let b0 = (input[pos] as u64) << 56;
    let b1 = (input[pos + 1] as u64) << 48;
    let b2 = (input[pos + 2] as u64) << 40;
    let b3 = (input[pos + 3] as u64) << 32;
    let b4 = (input[pos + 4] as u64) << 24;
    let b5 = (input[pos + 5] as u64) << 16;
    let b6 = (input[pos + 6] as u64) << 8;
    let b7 = input[pos + 7] as u64;
    Ok((b0 | b1 | b2 | b3 | b4 | b5 | b6 | b7, pos + 8))
}

#[inline]
fn read_var_u64_at(input: &[u8], pos: usize) -> Result<(u64, usize), CodecError> {
    if pos >= input.len() {
        return Err(CodecError::UnexpectedEof);
    }
    let first = input[pos];
    if first < 0x80 {
        return Ok((first as u64, pos + 1));
    }
    let (val, used) = decode_var_u64(&input[pos..])?;
    if used > input.len() - pos {
        return Err(CodecError::UnexpectedEof);
    }
    Ok((val, pos + used))
}

#[inline]
fn read_var_i32_with_sign_at(input: &[u8], pos: usize) -> Result<((i32, bool), usize), CodecError> {
    if pos > input.len() {
        return Err(CodecError::UnexpectedEof);
    }
    let (val, used) = decode_var_i32_with_sign(&input[pos..])?;
    if used > input.len() - pos {
        return Err(CodecError::UnexpectedEof);
    }
    Ok((val, pos + used))
}

#[inline]
fn read_var_u64_sink<S: V1Sink>(input: &[u8], pos: usize, sink: &mut S) -> Result<(u64, usize), CodecError> {
    match read_var_u64_at(input, pos) {
        Ok(v) => Ok(v),
        Err(e) => {
            let rem = if pos <= input.len() { input.len() - pos } else { 0 };
            Err(fail_with(sink, e, rem, 0))
        }
    }
}

#[inline]
fn read_var_i32_with_sign_sink<S: V1Sink>(
    input: &[u8],
    pos: usize,
    sink: &mut S,
) -> Result<((i32, bool), usize), CodecError> {
    match read_var_i32_with_sign_at(input, pos) {
        Ok(v) => Ok(v),
        Err(e) => {
            let rem = if pos <= input.len() { input.len() - pos } else { 0 };
            Err(fail_with(sink, e, rem, 0))
        }
    }
}

#[inline]
fn read_bytes_slice_at<S: V1Sink>(input: &[u8], pos: usize, sink: &mut S) -> Result<Span, CodecError> {
    let (len_u64, next) = read_var_u64_sink(input, pos, sink)?;
    if len_u64 > (usize::MAX as u64) {
        return Err(CodecError::BufferTooLarge);
    }
    let len = len_u64 as usize;
    if next > usize::MAX - len {
        return Err(CodecError::BufferLengthOverflow);
    }
    if len > input.len() - next {
        return Err(CodecError::BufferExceedsUpdate);
    }
    Ok(Span {
        start: next,
        end: next + len,
    })
}

#[inline]
fn read_str_slice_at<S: V1Sink>(input: &[u8], pos: usize, sink: &mut S) -> Result<Span, CodecError> {
    let span = read_bytes_slice_at(input, pos, sink)?;
    if sink.core_validates_utf8() && !is_valid_utf8(&input[span.start..span.end]) {
        return Err(CodecError::InvalidUtf8);
    }
    Ok(span)
}

#[cfg_attr(not(debug_assertions), inline(always))]
fn read_early_str_slice_at<S: V1Sink>(input: &[u8], pos: usize, slot: u8, sink: &mut S) -> Result<Span, CodecError> {
    let span = read_bytes_slice_at(input, pos, sink)?;
    if sink.core_validates_utf8() {
        if !is_valid_utf8(&input[span.start..span.end]) {
            return Err(CodecError::InvalidUtf8);
        }
    } else {
        sink.validate_utf8_early(slot, span)?;
    }
    Ok(span)
}

#[cfg_attr(not(debug_assertions), inline(always))]
fn read_wire_id_at<S: V1Sink>(input: &[u8], pos: usize, sink: &mut S) -> Result<(WireId, usize), CodecError> {
    let (client, p1) = read_var_u64_sink(input, pos, sink)?;
    let (clock, p2) = read_var_u64_sink(input, p1, sink)?;
    Ok((WireId { client, clock }, p2))
}

#[inline]
fn advance_clock_sink<S: V1Sink>(clock: u64, len: u64, sink: &mut S) -> Result<u64, CodecError> {
    if len == 0 {
        return Err(CodecError::ZeroLengthStruct);
    }
    if len > u64::MAX - clock {
        return Err(fail_with(sink, CodecError::ClockOverflow, 0, clock));
    }
    Ok(clock + len)
}

#[inline]
fn read_sv_entry(input: &[u8], cur: usize) -> Result<(u64, u64, usize), CodecError> {
    let (client, p1) = read_var_u64_at(input, cur)?;
    let (clock, p2) = read_var_u64_at(input, p1)?;
    Ok((client, clock, p2))
}

/// Decodes a V1 `StateVector` from `input[pos..]` into `sink`, returning
/// `next_pos`.
pub fn read_state_vector_v1_with<S: SvSink>(input: &[u8], pos: usize, sink: &mut S) -> Result<usize, CodecError> {
    if pos > input.len() {
        return Err(CodecError::UnexpectedEof);
    }
    let (count_u64, mut cur) = read_var_u64_at(input, pos)?;
    if count_u64 > ((input.len() - cur) as u64) / 2 {
        return Err(CodecError::CountTooLarge(LimitKind::Clients));
    }
    let count = checked_usize_limit(count_u64, LimitKind::Clients)?;
    sink.on_sv_len(count)?;
    let mut err: Option<CodecError> = None;
    let mut i = 0usize;
    while i < count && err.is_none() {
        match read_sv_entry(input, cur) {
            Err(e) => err = Some(e),
            Ok((client, clock, p2)) => match sink.on_sv_entry(client, clock) {
                Err(e) => err = Some(e),
                Ok(()) => {
                    cur = p2;
                    i += 1;
                }
            },
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(cur) }
}

/// Decodes a V1 `StateVector` from `input[pos..]`, returning `(sv, next_pos)`.
///
/// Duplicate client IDs overwrite earlier entries (last-write-wins), matching
/// `y_octo::StateVector::read`.
pub fn read_state_vector_v1(input: &[u8], pos: usize) -> Result<(StateVectorCore, usize), CodecError> {
    if pos > input.len() {
        return Err(CodecError::UnexpectedEof);
    }
    let (count_u64, mut cur) = read_var_u64_at(input, pos)?;
    let count = checked_usize_from_u64(count_u64)?;
    check_fits(input.len() - cur, count, 2)?;
    let mut sv = StateVectorCore::new();
    let mut err: Option<CodecError> = None;
    let mut i = 0usize;
    while i < count && err.is_none() {
        match read_sv_entry(input, cur) {
            Err(e) => err = Some(e),
            Ok((client, clock, p2)) => {
                sv.set(client, clock);
                cur = p2;
                i += 1;
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok((sv, cur)) }
}

/// Decodes a complete V1 `StateVector` buffer, rejecting trailing bytes.
pub fn decode_state_vector_v1(input: &[u8]) -> Result<StateVectorCore, CodecError> {
    let (sv, end) = read_state_vector_v1(input, 0)?;
    if end != input.len() {
        return Err(CodecError::TrailingBytes);
    }
    Ok(sv)
}

#[inline]
fn read_one_delete_range(input: &[u8], cur: usize) -> Result<(u64, u64, usize), CodecError> {
    let (start, q1) = read_var_u64_at(input, cur)?;
    let (len, q2) = read_var_u64_at(input, q1)?;
    if len > u64::MAX - start {
        return Err(CodecError::ClockOverflow);
    }
    Ok((start, start + len, q2))
}

#[inline]
fn read_one_delete_range_sink<S: V1Sink>(
    input: &[u8],
    cur: usize,
    sink: &mut S,
) -> Result<(u64, u64, usize), CodecError> {
    let (start, q1) = read_var_u64_sink(input, cur, sink)?;
    let (len, q2) = read_var_u64_sink(input, q1, sink)?;
    if len > u64::MAX - start {
        return Err(fail_with(sink, CodecError::ClockOverflow, 0, start));
    }
    Ok((start, start + len, q2))
}

#[inline]
fn read_delete_ranges_for_client(
    input: &[u8],
    start_pos: usize,
    client: u64,
    range_count: usize,
    ds: &mut DeleteSetCore,
) -> Result<usize, CodecError> {
    let mut cur = start_pos;
    let mut r_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while r_idx < range_count && err.is_none() {
        match read_one_delete_range(input, cur) {
            Err(e) => err = Some(e),
            Ok((start, end, q2)) => {
                if start != end
                    && let Err(e) = ds.try_insert(client, start, end)
                {
                    err = Some(e);
                }
                cur = q2;
                r_idx += 1;
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(cur) }
}

#[inline]
fn read_delete_client_header(
    input: &[u8],
    cur: usize,
    limits: &DecodeLimitsCore,
    total_entries: usize,
) -> Result<(u64, usize, usize, usize), CodecError> {
    let (client, p1) = read_var_u64_at(input, cur)?;
    let (ranges_u64, p2) = read_var_u64_at(input, p1)?;
    let range_count = checked_usize_limit(ranges_u64, LimitKind::DeleteRanges)?;
    let next_entries = checked_add_limit(total_entries, range_count, LimitKind::CollectionEntries)?;
    if next_entries > limits.max_collection_entries {
        return Err(CodecError::ResourceLimit(LimitKind::CollectionEntries));
    }
    Ok((client, range_count, next_entries, p2))
}

/// Decodes a V1 `DeleteSet` from `input[pos..]`, returning `(ds,
/// ranges_decoded, delete_clients, next_pos)`.
pub fn read_delete_set_v1(
    input: &[u8],
    pos: usize,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
) -> Result<(DeleteSetCore, usize, usize, usize), CodecError> {
    if pos > input.len() {
        return Err(CodecError::UnexpectedEof);
    }
    let (clients_u64, mut cur) = read_var_u64_at(input, pos)?;
    let delete_clients = checked_usize_limit(clients_u64, LimitKind::DeleteClients)?;
    if delete_clients > limits.max_clients {
        return Err(CodecError::ResourceLimit(LimitKind::DeleteClients));
    }
    check_fits_kind(
        input.len() - cur,
        delete_clients,
        MIN_DELETE_CLIENT_BYTES,
        LimitKind::DeleteClients,
    )?;

    let mut ds = DeleteSetCore::new();
    let mut total_entries = entries_acc;
    let mut total_ranges = 0usize;
    let mut c_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while c_idx < delete_clients && err.is_none() {
        match read_delete_client_header(input, cur, limits, total_entries) {
            Err(e) => err = Some(e),
            Ok((client, range_count, next_entries, p2)) => match check_fits_kind(
                input.len() - p2,
                range_count,
                MIN_DELETE_RANGE_BYTES,
                LimitKind::DeleteRanges,
            ) {
                Err(e) => err = Some(e),
                Ok(()) => {
                    total_entries = next_entries;
                    match read_delete_ranges_for_client(input, p2, client, range_count, &mut ds) {
                        Err(e) => err = Some(e),
                        Ok(next_cur) => match checked_add_usize(total_ranges, range_count) {
                            Err(e) => err = Some(e),
                            Ok(next_ranges) => {
                                cur = next_cur;
                                total_ranges = next_ranges;
                                c_idx += 1;
                            }
                        },
                    }
                }
            },
        }
    }
    if let Some(e) = err {
        Err(e)
    } else {
        Ok((ds, total_ranges, delete_clients, cur))
    }
}

#[inline]
fn decode_delete_ranges_for_client<S: V1Sink>(
    input: &[u8],
    start_pos: usize,
    client: u64,
    range_count: usize,
    sink: &mut S,
) -> Result<usize, CodecError> {
    let mut cur = start_pos;
    let mut r_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while r_idx < range_count && err.is_none() {
        match read_one_delete_range_sink(input, cur, sink) {
            Err(e) => err = Some(e),
            Ok((start, end, q2)) => {
                if start != end {
                    match sink.on_delete_range(client, start, end) {
                        Err(e) => err = Some(e),
                        Ok(()) => {
                            cur = q2;
                            r_idx += 1;
                        }
                    }
                } else {
                    cur = q2;
                    r_idx += 1;
                }
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(cur) }
}

#[inline]
fn decode_delete_client_header<S: V1Sink>(
    input: &[u8],
    cur: usize,
    limits: &DecodeLimitsCore,
    total_entries: usize,
    sink: &mut S,
) -> Result<(u64, usize, usize, usize), CodecError> {
    let (client, p1) = read_var_u64_sink(input, cur, sink)?;
    let (ranges_u64, p2) = read_var_u64_sink(input, p1, sink)?;
    let range_count = checked_usize_limit(ranges_u64, LimitKind::DeleteRanges)?;
    let next_entries = checked_add_limit(total_entries, range_count, LimitKind::CollectionEntries)?;
    if next_entries > limits.max_collection_entries {
        return Err(CodecError::ResourceLimit(LimitKind::CollectionEntries));
    }
    Ok((client, range_count, next_entries, p2))
}

#[inline]
fn decode_delete_set_v1<S: V1Sink>(
    input: &[u8],
    pos: usize,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
    sink: &mut S,
) -> Result<usize, CodecError> {
    if pos > input.len() {
        return Err(fail_with(sink, CodecError::UnexpectedEof, 0, 0));
    }
    let (clients_u64, mut cur) = read_var_u64_sink(input, pos, sink)?;
    let delete_clients = checked_usize_limit(clients_u64, LimitKind::DeleteClients)?;
    if delete_clients > limits.max_clients {
        return Err(CodecError::ResourceLimit(LimitKind::DeleteClients));
    }
    check_fits_kind_sink(
        input.len() - cur,
        delete_clients,
        MIN_DELETE_CLIENT_BYTES,
        LimitKind::DeleteClients,
        sink,
    )?;

    let mut total_entries = entries_acc;
    let mut c_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while c_idx < delete_clients && err.is_none() {
        match decode_delete_client_header(input, cur, limits, total_entries, sink) {
            Err(e) => err = Some(e),
            Ok((client, range_count, next_entries, p2)) => match check_fits_kind_sink(
                input.len() - p2,
                range_count,
                MIN_DELETE_RANGE_BYTES,
                LimitKind::DeleteRanges,
                sink,
            ) {
                Err(e) => err = Some(e),
                Ok(()) => {
                    total_entries = next_entries;
                    match sink.begin_delete_client(client, range_count) {
                        Err(e) => err = Some(e),
                        Ok(()) => match decode_delete_ranges_for_client(input, p2, client, range_count, sink) {
                            Err(e) => err = Some(e),
                            Ok(next_cur) => {
                                cur = next_cur;
                                c_idx += 1;
                            }
                        },
                    }
                }
            },
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(cur) }
}

#[inline]
fn decode_any_scalar<S: V1Sink>(input: &[u8], tag: u8, cur: usize, sink: &mut S) -> Result<usize, CodecError> {
    if tag == 0 {
        sink.on_any_undefined()?;
        Ok(cur)
    } else if tag == 1 {
        sink.on_any_null()?;
        Ok(cur)
    } else if tag == 2 {
        let ((val, negative), p) = read_var_i32_with_sign_sink(input, cur, sink)?;
        if val == 0 && negative {
            sink.on_any_f32_bits(0x8000_0000u32)?;
        } else {
            sink.on_any_i32(val)?;
        }
        Ok(p)
    } else if tag == 3 {
        let (bits, p) = read_u32_be_at(input, cur)?;
        sink.on_any_f32_bits(bits)?;
        Ok(p)
    } else if tag == 4 {
        let (bits, p) = read_u64_be_at(input, cur)?;
        sink.on_any_f64_bits(bits)?;
        Ok(p)
    } else if tag == 5 {
        let (bits, p) = read_u64_be_at(input, cur)?;
        sink.on_any_i64_bits(bits)?;
        Ok(p)
    } else if tag == 6 {
        sink.on_any_bool(false)?;
        Ok(cur)
    } else if tag == 7 {
        sink.on_any_bool(true)?;
        Ok(cur)
    } else if tag == 8 {
        let span = read_str_slice_at(input, cur, sink)?;
        sink.on_any_str(span)?;
        Ok(span.end)
    } else if tag == 11 {
        let span = read_bytes_slice_at(input, cur, sink)?;
        sink.on_any_bytes(span)?;
        Ok(span.end)
    } else {
        Err(CodecError::UnknownAnyTagByte(tag))
    }
}

#[allow(clippy::too_many_arguments)]
#[inline]
fn open_any_container<S: V1Sink>(
    input: &[u8],
    is_obj: bool,
    cur: usize,
    limits: &DecodeLimitsCore,
    entries: usize,
    depth: usize,
    open: &mut Vec<(usize, bool)>,
    sink: &mut S,
) -> Result<(usize, usize, usize, bool), CodecError> {
    let kind = if is_obj {
        LimitKind::AnyObjectEntries
    } else {
        LimitKind::AnyArrayEntries
    };
    let min_bytes = if is_obj {
        MIN_OBJECT_ENTRY_BYTES
    } else {
        MIN_ENTRY_BYTES
    };
    let (cnt_u64, p) = read_var_u64_sink(input, cur, sink)?;
    let count = checked_usize_limit(cnt_u64, kind)?;
    let total_entries = checked_add_limit(entries, count, LimitKind::CollectionEntries)?;
    if total_entries > limits.max_collection_entries {
        return Err(CodecError::ResourceLimit(LimitKind::CollectionEntries));
    }
    check_fits_kind_sink(input.len() - p, count, min_bytes, kind, sink)?;
    if depth == usize::MAX {
        return Err(CodecError::ResourceLimit(LimitKind::AnyDepth));
    }
    if is_obj {
        sink.on_any_begin_object(count)?;
    } else {
        sink.on_any_begin_array(count)?;
    }
    if depth < open.len() {
        open[depth] = (count, is_obj);
    } else {
        open.push((count, is_obj));
    }
    Ok((p, total_entries, depth + 1, count == 0))
}

#[inline]
fn close_finished_containers<S: V1Sink>(
    open: &[(usize, bool)],
    start_depth: usize,
    sink: &mut S,
) -> Result<usize, CodecError> {
    let mut depth = start_depth;
    let mut stop = false;
    let mut err: Option<CodecError> = None;
    while depth > 0 && !stop && err.is_none() {
        let top = open[depth - 1];
        if top.0 == 0 {
            match sink.on_any_end_container() {
                Err(e) => err = Some(e),
                Ok(()) => depth -= 1,
            }
        } else {
            stop = true;
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(depth) }
}

#[inline]
fn decode_any_step<S: V1Sink>(
    input: &[u8],
    start_cur: usize,
    limits: &DecodeLimitsCore,
    entries: usize,
    depth: usize,
    open: &mut Vec<(usize, bool)>,
    sink: &mut S,
) -> Result<(usize, usize, usize), CodecError> {
    let top = open[depth - 1];
    if top.0 == 0 {
        sink.on_any_end_container()?;
        return Ok((start_cur, entries, depth - 1));
    }
    open[depth - 1].0 = top.0 - 1;
    let cur = if top.1 {
        let key = read_str_slice_at(input, start_cur, sink)?;
        sink.on_any_object_key(key)?;
        key.end
    } else {
        start_cur
    };
    if depth > limits.max_any_depth {
        return Err(CodecError::ResourceLimit(LimitKind::AnyDepth));
    }
    let (raw_tag, after_tag) = read_u8_at(input, cur)?;
    let tag = 127u8.wrapping_sub(raw_tag);
    if tag == 9 || tag == 10 {
        let (next_cur, next_entries, next_depth, empty) =
            open_any_container(input, tag == 9, after_tag, limits, entries, depth, open, sink)?;
        if empty {
            let final_depth = close_finished_containers(open, next_depth, sink)?;
            Ok((next_cur, next_entries, final_depth))
        } else {
            Ok((next_cur, next_entries, next_depth))
        }
    } else {
        let next_cur = decode_any_scalar(input, tag, after_tag, sink)?;
        let final_depth = if open[depth - 1].0 == 0 {
            close_finished_containers(open, depth, sink)?
        } else {
            depth
        };
        Ok((next_cur, entries, final_depth))
    }
}

#[inline]
fn decode_any_v1<S: V1Sink>(
    input: &[u8],
    start_pos: usize,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
    sink: &mut S,
) -> Result<(usize, usize), CodecError> {
    sink.on_any_start()?;
    let (raw_tag, after_tag) = read_u8_at(input, start_pos)?;
    let first_tag = 127u8.wrapping_sub(raw_tag);
    if first_tag != 9 && first_tag != 10 {
        let end_cur = decode_any_scalar(input, first_tag, after_tag, sink)?;
        sink.on_any_finish(Span {
            start: start_pos,
            end: end_cur,
        })?;
        return Ok((end_cur, entries_acc));
    }

    let mut open: Vec<(usize, bool)> = Vec::new();
    let (mut cur, mut entries, mut depth, empty) = open_any_container(
        input,
        first_tag == 9,
        after_tag,
        limits,
        entries_acc,
        0,
        &mut open,
        sink,
    )?;
    if empty {
        depth = close_finished_containers(&open, depth, sink)?;
    }

    let rem = if input.len() >= cur { input.len() - cur } else { 0 };
    let rem2 = if rem <= usize::MAX / 2 { rem * 2 } else { usize::MAX };
    let rem_d = if limits.max_any_depth <= usize::MAX - rem2 {
        rem2 + limits.max_any_depth
    } else {
        usize::MAX
    };
    let max_steps = if 2 <= usize::MAX - rem_d { rem_d + 2 } else { usize::MAX };

    let mut step = 0usize;
    let mut err: Option<CodecError> = None;
    while step < max_steps && depth > 0 && err.is_none() {
        step += 1;
        match decode_any_step(input, cur, limits, entries, depth, &mut open, sink) {
            Err(e) => err = Some(e),
            Ok((next_cur, next_entries, next_depth)) => {
                cur = next_cur;
                entries = next_entries;
                depth = next_depth;
            }
        }
    }
    if let Some(e) = err {
        Err(e)
    } else if depth != 0 {
        Err(CodecError::ResourceLimit(LimitKind::AnyDepth))
    } else {
        sink.on_any_finish(Span {
            start: start_pos,
            end: cur,
        })?;
        Ok((cur, entries))
    }
}

#[inline]
fn decode_json_entries<S: V1Sink>(
    input: &[u8],
    start_pos: usize,
    count: usize,
    sink: &mut S,
) -> Result<usize, CodecError> {
    let mut cur = start_pos;
    let mut i = 0usize;
    let mut err: Option<CodecError> = None;
    while i < count && err.is_none() {
        match read_str_slice_at(input, cur, sink) {
            Err(e) => err = Some(e),
            Ok(span) => match sink.on_json_value(span) {
                Err(e) => err = Some(e),
                Ok(()) => {
                    cur = span.end;
                    i += 1;
                }
            },
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(cur) }
}

#[inline]
fn decode_any_entries<S: V1Sink>(
    input: &[u8],
    start_pos: usize,
    count: usize,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
    sink: &mut S,
) -> Result<(usize, usize), CodecError> {
    let mut cur = start_pos;
    let mut entries = entries_acc;
    let mut i = 0usize;
    let mut err: Option<CodecError> = None;
    while i < count && err.is_none() {
        match decode_any_v1(input, cur, limits, entries, sink) {
            Err(e) => err = Some(e),
            Ok((next_c, next_e)) => match sink.on_any_content_value() {
                Err(e) => err = Some(e),
                Ok(()) => {
                    cur = next_c;
                    entries = next_e;
                    i += 1;
                }
            },
        }
    }
    if let Some(e) = err { Err(e) } else { Ok((cur, entries)) }
}

#[derive(Clone, Copy)]
struct ItemHeader {
    origin_left: Option<WireId>,
    origin_right: Option<WireId>,
    parent: WireParentCore,
    parent_sub: Option<Span>,
}

#[derive(Clone, Copy)]
struct DecodeAcc {
    structs: usize,
    entries: usize,
    content_bytes: usize,
}

#[inline]
fn decode_item_header<S: V1Sink>(
    input: &[u8],
    start_pos: usize,
    info: u8,
    sink: &mut S,
) -> Result<(ItemHeader, usize), CodecError> {
    let mut cur = start_pos;
    let has_left = (info & ITEM_HAS_LEFT_ID) != 0;
    let has_right = (info & ITEM_HAS_RIGHT_ID) != 0;
    let explicit_parent = (info & (ITEM_HAS_LEFT_ID | ITEM_HAS_RIGHT_ID)) == 0;
    let origin_left = if has_left {
        let (id, next) = read_wire_id_at(input, cur, sink)?;
        cur = next;
        Some(id)
    } else {
        None
    };
    let origin_right = if has_right {
        let (id, next) = read_wire_id_at(input, cur, sink)?;
        cur = next;
        Some(id)
    } else {
        None
    };
    let parent = if explicit_parent {
        let (p_kind, p1) = read_var_u64_sink(input, cur, sink)?;
        if p_kind == 1 {
            let span = read_early_str_slice_at(input, p1, 0, sink)?;
            cur = span.end;
            WireParentCore::Root(span)
        } else {
            let (id, next) = read_wire_id_at(input, p1, sink)?;
            cur = next;
            WireParentCore::Item(id)
        }
    } else {
        WireParentCore::Inherit
    };
    let parent_sub = if explicit_parent && (info & ITEM_HAS_PARENT_SUB) != 0 {
        let span = read_early_str_slice_at(input, cur, 1, sink)?;
        cur = span.end;
        Some(span)
    } else {
        None
    };
    Ok((
        ItemHeader {
            origin_left,
            origin_right,
            parent,
            parent_sub,
        },
        cur,
    ))
}

#[inline]
fn decode_item_content<S: V1Sink>(
    input: &[u8],
    cur: usize,
    tag: u8,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
    sink: &mut S,
) -> Result<(u64, usize, usize), CodecError> {
    if tag == 1 {
        let (len, p) = read_var_u64_sink(input, cur, sink)?;
        sink.on_deleted(len)?;
        return Ok((len, p, entries_acc));
    }
    if tag == 2 {
        let (len, p) = read_var_u64_sink(input, cur, sink)?;
        let count = checked_usize_limit(len, LimitKind::ContentEntries)?;
        let entries = checked_add_limit(entries_acc, count, LimitKind::CollectionEntries)?;
        if entries > limits.max_collection_entries {
            return Err(CodecError::ResourceLimit(LimitKind::CollectionEntries));
        }
        check_fits_kind_sink(input.len() - p, count, MIN_ENTRY_BYTES, LimitKind::ContentEntries, sink)?;
        sink.on_json_start(count)?;
        let end = decode_json_entries(input, p, count, sink)?;
        sink.on_json_finish()?;
        return Ok((len, end, entries));
    }
    if tag == 3 {
        let span = read_bytes_slice_at(input, cur, sink)?;
        sink.on_binary(span)?;
        return Ok((1, span.end, entries_acc));
    }
    if tag == 4 {
        let span = read_str_slice_at(input, cur, sink)?;
        sink.on_string(span)?;
        let len = utf16_len(&input[span.start..span.end]) as u64;
        return Ok((len, span.end, entries_acc));
    }
    if tag == 5 {
        let span = read_str_slice_at(input, cur, sink)?;
        sink.on_embed(span)?;
        return Ok((1, span.end, entries_acc));
    }
    if tag == 6 {
        let key = read_early_str_slice_at(input, cur, 2, sink)?;
        let value = read_str_slice_at(input, key.end, sink)?;
        sink.on_format(key, value)?;
        return Ok((1, value.end, entries_acc));
    }
    if tag == 7 {
        let (kind, p) = read_var_u64_sink(input, cur, sink)?;
        if kind > 6 {
            return Err(fail_with(sink, CodecError::UnknownTypeKind, 0, kind));
        }
        if kind == 3 || kind == 5 {
            let type_tag = read_str_slice_at(input, p, sink)?;
            sink.on_type(kind, Some(type_tag))?;
            return Ok((1, type_tag.end, entries_acc));
        }
        sink.on_type(kind, None)?;
        return Ok((1, p, entries_acc));
    }
    if tag == 8 {
        let (len, p) = read_var_u64_sink(input, cur, sink)?;
        let count = checked_usize_limit(len, LimitKind::ContentEntries)?;
        let entries = checked_add_limit(entries_acc, count, LimitKind::CollectionEntries)?;
        if entries > limits.max_collection_entries {
            return Err(CodecError::ResourceLimit(LimitKind::CollectionEntries));
        }
        check_fits_kind_sink(input.len() - p, count, MIN_ENTRY_BYTES, LimitKind::ContentEntries, sink)?;
        sink.on_any_content_start(count)?;
        let (next_c, next_e) = decode_any_entries(input, p, count, limits, entries, sink)?;
        sink.on_any_content_finish()?;
        return Ok((len, next_c, next_e));
    }
    if tag == 9 {
        let guid = read_early_str_slice_at(input, cur, 3, sink)?;
        let (next_c, next_e) = decode_any_v1(input, guid.end, limits, entries_acc, sink)?;
        sink.on_doc(guid)?;
        return Ok((1, next_c, next_e));
    }
    Err(CodecError::UnknownContentTagByte(tag))
}

#[inline]
fn decode_struct_frame<S: V1Sink>(
    input: &[u8],
    pos: usize,
    id: WireId,
    limits: &DecodeLimitsCore,
    acc: DecodeAcc,
    sink: &mut S,
) -> Result<(u64, usize, DecodeAcc), CodecError> {
    let (info, cur) = read_u8_at(input, pos)?;
    let tag = info & 0b1_1111;
    if tag == 0 {
        let (len, p) = read_var_u64_sink(input, cur, sink)?;
        let next_clock = advance_clock_sink(id.clock, len, sink)?;
        sink.on_gc(id, len)?;
        return Ok((next_clock, p, acc));
    }
    if tag == 10 {
        let (len, p) = read_var_u64_sink(input, cur, sink)?;
        let next_clock = advance_clock_sink(id.clock, len, sink)?;
        sink.on_skip(id, len)?;
        return Ok((next_clock, p, acc));
    }

    let (hdr, content_start) = decode_item_header(input, cur, info, sink)?;
    let (len, content_end, entries) = decode_item_content(input, content_start, tag, limits, acc.entries, sink)?;
    let delta = if content_end >= content_start {
        content_end - content_start
    } else {
        0
    };
    let content_bytes = checked_add_limit(acc.content_bytes, delta, LimitKind::ContentBytes)?;
    if content_bytes > limits.max_content_bytes {
        return Err(CodecError::ResourceLimit(LimitKind::ContentBytes));
    }
    let next_clock = advance_clock_sink(id.clock, len, sink)?;
    sink.on_item(
        id,
        len,
        ItemMetaCore {
            origin_left: hdr.origin_left,
            origin_right: hdr.origin_right,
            parent: hdr.parent,
            parent_sub: hdr.parent_sub,
            raw_range: Span {
                start: pos,
                end: content_end,
            },
        },
    )?;
    Ok((
        next_clock,
        content_end,
        DecodeAcc {
            structs: acc.structs,
            entries,
            content_bytes,
        },
    ))
}

#[inline]
fn decode_client_structs<S: V1Sink>(
    input: &[u8],
    start_pos: usize,
    start_id: WireId,
    count: usize,
    limits: &DecodeLimitsCore,
    start_acc: DecodeAcc,
    sink: &mut S,
) -> Result<(usize, DecodeAcc), CodecError> {
    let mut cur = start_pos;
    let mut clock = start_id.clock;
    let mut acc = start_acc;
    let mut s_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while s_idx < count && err.is_none() {
        let id = WireId {
            client: start_id.client,
            clock,
        };
        match decode_struct_frame(input, cur, id, limits, acc, sink) {
            Err(e) => err = Some(e),
            Ok((next_clock, next_cur, next_acc)) => {
                clock = next_clock;
                cur = next_cur;
                acc = next_acc;
                s_idx += 1;
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok((cur, acc)) }
}

#[inline]
fn decode_one_client_block<S: V1Sink>(
    input: &[u8],
    cur: usize,
    limits: &DecodeLimitsCore,
    acc: DecodeAcc,
    sink: &mut S,
) -> Result<(usize, DecodeAcc), CodecError> {
    let (count_u64, p1) = read_var_u64_sink(input, cur, sink)?;
    let count = checked_usize_limit(count_u64, LimitKind::Structs)?;
    let next_structs = checked_add_limit(acc.structs, count, LimitKind::Structs)?;
    if next_structs > limits.max_structs {
        return Err(CodecError::ResourceLimit(LimitKind::Structs));
    }
    let next_entries_hdr = checked_add_limit(acc.entries, count, LimitKind::CollectionEntries)?;
    if next_entries_hdr > limits.max_collection_entries {
        return Err(CodecError::ResourceLimit(LimitKind::CollectionEntries));
    }
    check_fits_kind_sink(input.len() - p1, count, MIN_STRUCT_BYTES, LimitKind::Structs, sink)?;

    let (client, p2) = read_var_u64_sink(input, p1, sink)?;
    if !sink.record_client(client)? {
        return Err(CodecError::DuplicateClient);
    }
    let (clock, p3) = read_var_u64_sink(input, p2, sink)?;
    sink.begin_client(client, count)?;
    let hdr_acc = DecodeAcc {
        structs: next_structs,
        entries: next_entries_hdr,
        content_bytes: acc.content_bytes,
    };
    decode_client_structs(input, p3, WireId { client, clock }, count, limits, hdr_acc, sink)
}

/// Validates and streams a complete Yjs V1 Update frame into `sink` with
/// bounded loops and checked `u64 -> usize` conversions. Never panics on
/// arbitrary `&[u8]`.
///
/// Validates V1 frame structure and checked bounds/limits; UTF-8 validation is
/// handled here when [`V1Sink::core_validates_utf8`] returns `true` or
/// delegated to [`V1Sink::validate_utf8_early`] and sink callbacks when
/// `false`. Inner JSON syntax parsing for `Embed` (tag 5) and `Format` (tag 6)
/// values may be performed by `sink.on_embed` / `sink.on_format`.
#[inline]
pub fn decode_update_v1<S: V1Sink>(input: &[u8], sink: &mut S, limits: &DecodeLimitsCore) -> Result<(), CodecError> {
    let (clients_u64, mut cur) = read_var_u64_sink(input, 0, sink)?;
    let clients = checked_usize_limit(clients_u64, LimitKind::Clients)?;
    if clients > limits.max_clients {
        return Err(CodecError::ResourceLimit(LimitKind::Clients));
    }
    check_fits_kind_sink(input.len() - cur, clients, MIN_CLIENT_BYTES, LimitKind::Clients, sink)?;

    let mut acc = DecodeAcc {
        structs: 0,
        entries: 0,
        content_bytes: 0,
    };

    let mut c_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while c_idx < clients && err.is_none() {
        match decode_one_client_block(input, cur, limits, acc, sink) {
            Err(e) => err = Some(e),
            Ok((next_cur, next_acc)) => {
                cur = next_cur;
                acc = next_acc;
                c_idx += 1;
            }
        }
    }
    if let Some(e) = err {
        return Err(e);
    }

    let end_pos = decode_delete_set_v1(input, cur, limits, acc.entries, sink)?;
    if end_pos != input.len() {
        return Err(fail_with(sink, CodecError::TrailingBytes, input.len() - end_pos, 0));
    }
    Ok(())
}

fn find_u64_index(items: &[u64], target: u64) -> (bool, usize) {
    let mut low = 0usize;
    let mut high = items.len();
    while low < high {
        let mid = low + (high - low) / 2;
        let c = items[mid];
        if c == target {
            return (true, mid);
        } else if c < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    (false, low)
}

fn insert_u64_sorted(items: &mut Vec<u64>, target: u64) -> bool {
    let (found, idx) = find_u64_index(items, target);
    if found {
        false
    } else {
        if idx == items.len() {
            items.push(target);
        } else {
            items.insert(idx, target);
        }
        true
    }
}

struct SummarySink {
    seen_clients: Vec<u64>,
    summary: UpdateSummary,
}

impl SummarySink {
    fn new() -> Self {
        Self {
            seen_clients: Vec::new(),
            summary: UpdateSummary {
                clients: 0,
                structs: 0,
                delete_clients: 0,
                delete_ranges: 0,
            },
        }
    }
}

impl V1Sink for SummarySink {
    #[inline]
    fn core_validates_utf8(&self) -> bool {
        true
    }

    #[inline]
    fn validate_utf8_early(&mut self, _slot: u8, _value: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline(always)]
    fn on_decode_error(&mut self, _err: CodecError, _a: usize, _b: u64) {}

    #[inline]
    fn record_client(&mut self, client: u64) -> Result<bool, CodecError> {
        if self.seen_clients.len() == usize::MAX {
            return Err(CodecError::LimitExceeded);
        }
        Ok(insert_u64_sorted(&mut self.seen_clients, client))
    }

    #[inline]
    fn begin_client(&mut self, _client: u64, _count: usize) -> Result<(), CodecError> {
        if self.summary.clients == usize::MAX {
            return Err(CodecError::LimitExceeded);
        }
        self.summary.clients += 1;
        Ok(())
    }

    #[inline]
    fn on_gc(&mut self, _id: WireId, _len: u64) -> Result<(), CodecError> {
        if self.summary.structs == usize::MAX {
            return Err(CodecError::LimitExceeded);
        }
        self.summary.structs += 1;
        Ok(())
    }

    #[inline]
    fn on_skip(&mut self, _id: WireId, _len: u64) -> Result<(), CodecError> {
        if self.summary.structs == usize::MAX {
            return Err(CodecError::LimitExceeded);
        }
        self.summary.structs += 1;
        Ok(())
    }

    #[inline]
    fn on_item(&mut self, _id: WireId, _len: u64, _meta: ItemMetaCore) -> Result<(), CodecError> {
        if self.summary.structs == usize::MAX {
            return Err(CodecError::LimitExceeded);
        }
        self.summary.structs += 1;
        Ok(())
    }

    #[inline]
    fn on_deleted(&mut self, _len: u64) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_json_start(&mut self, _count: usize) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_json_value(&mut self, _value: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_json_finish(&mut self) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_binary(&mut self, _value: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_string(&mut self, _value: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_embed(&mut self, _value: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_format(&mut self, _key: Span, _value: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_type(&mut self, _kind: u64, _tag: Option<Span>) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_content_start(&mut self, _count: usize) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_content_value(&mut self) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_content_finish(&mut self) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_doc(&mut self, _guid: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_start(&mut self) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_undefined(&mut self) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_null(&mut self) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_i32(&mut self, _value: i32) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_f32_bits(&mut self, _bits: u32) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_f64_bits(&mut self, _bits: u64) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_i64_bits(&mut self, _bits: u64) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_bool(&mut self, _value: bool) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_str(&mut self, _value: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_bytes(&mut self, _value: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_begin_object(&mut self, _count: usize) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_object_key(&mut self, _key: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_begin_array(&mut self, _count: usize) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_end_container(&mut self) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_any_finish(&mut self, _range: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn begin_delete_client(&mut self, _client: u64, count: usize) -> Result<(), CodecError> {
        if self.summary.delete_clients == usize::MAX {
            return Err(CodecError::LimitExceeded);
        }
        self.summary.delete_clients += 1;
        self.summary.delete_ranges = checked_add_usize(self.summary.delete_ranges, count)?;
        Ok(())
    }

    #[inline]
    fn on_delete_range(&mut self, _client: u64, _start: u64, _end: u64) -> Result<(), CodecError> {
        Ok(())
    }
}

/// Validates and summarizes a complete Yjs V1 Update frame using the same
/// [`decode_update_v1`] engine used in production.
pub fn decode_update_v1_frame(input: &[u8], limits: &DecodeLimitsCore) -> Result<UpdateSummary, CodecError> {
    let mut sink = SummarySink::new();
    decode_update_v1(input, &mut sink, limits)?;
    Ok(sink.summary)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_update_and_sv() {
        let summary = decode_update_v1_frame(&[0, 0], &DecodeLimitsCore::default_update()).unwrap();
        assert_eq!(
            summary,
            UpdateSummary {
                clients: 0,
                structs: 0,
                delete_clients: 0,
                delete_ranges: 0,
            }
        );
        assert!(decode_update_v1_frame(&[], &DecodeLimitsCore::default_update()).is_err());
        let sv = decode_state_vector_v1(&[2, 7, 4, 1, 2]).unwrap();
        assert_eq!(sv.get(7), 4);
        assert_eq!(sv.get(1), 2);
    }

    #[test]
    fn fuzz_like_arbitrary_inputs_never_panic() {
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        for len in 0..64 {
            let mut buf = vec![0u8; len];
            for b in &mut buf {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                *b = (seed & 0xff) as u8;
            }
            let _ = decode_update_v1_frame(&buf, &DecodeLimitsCore::default_update());
            let _ = decode_state_vector_v1(&buf);
        }
    }
}
