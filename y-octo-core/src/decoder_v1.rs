use alloc::vec::Vec;

use crate::{
    CodecError, LimitKind,
    delete_set::DeleteSetCore,
    order_range::ClockRange,
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
    fn on_skipped_zero_origin(&mut self, _origin_left: WireId) {}

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
        if len > 0 {
            sink.on_deleted(len)?;
        }
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
        if span.start == span.end {
            return Ok((0, span.end, entries_acc));
        }
        sink.on_string(span)?;
        let len = utf16_len(&input[span.start..span.end]) as u64;
        if len == 0 {
            return Err(CodecError::InvalidUtf8);
        }
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
fn seq_ranges_find(ranges: &[ClockRange], clock: u64) -> Option<ClockRange> {
    let n = ranges.len();
    if n == 0 {
        return None;
    }
    let last = ranges[n - 1];
    if clock >= last.start {
        return if clock < last.end { Some(last) } else { None };
    }
    let mut low = 0usize;
    let mut high = n - 1;
    while low < high {
        let mid = low + (high - low) / 2;
        let r = ranges[mid];
        if clock < r.start {
            high = mid;
        } else if clock >= r.end {
            low = mid + 1;
        } else {
            return Some(r);
        }
    }
    None
}

#[inline]
fn seq_ranges_push(ranges: &mut Vec<ClockRange>, start: u64, end: u64) {
    let n = ranges.len();
    if n > 0 {
        let last = ranges[n - 1];
        if last.end == start {
            ranges[n - 1] = ClockRange { start: last.start, end };
            return;
        }
    }
    // Capacity guard satisfies Aeneas's `Vec::push` precondition.
    if n < usize::MAX {
        ranges.push(ClockRange { start, end });
    }
}

const Y_TYPE_TEXT: u8 = 2;

struct ClientSeqState {
    active: bool,
    ytext_types: Vec<ClockRange>,
    seq_ranges: Vec<ClockRange>,
    just_skipped_ol: Option<WireId>,
}

#[inline]
fn is_ytext_content(input: &[u8], start: usize, end: usize, tag: u8) -> bool {
    tag == 7 && start < end && end <= input.len() && input[start] == Y_TYPE_TEXT
}

#[inline]
fn same_wire_id_opt(a: Option<WireId>, b: Option<WireId>) -> bool {
    match (a, b) {
        (Some(x), Some(y)) => x.client == y.client && x.clock == y.clock,
        _ => false,
    }
}

#[inline]
fn lookup_ytext_parent(id: WireId, parent: WireParentCore, ytext_types: &[ClockRange]) -> bool {
    match parent {
        WireParentCore::Item(p) => {
            if p.client == id.client && p.clock < id.clock {
                seq_ranges_find(ytext_types, p.clock).is_some()
            } else {
                false
            }
        }
        _ => false,
    }
}

#[inline]
fn lookup_proven_origin(id: WireId, origin: Option<WireId>, seq_ranges: &[ClockRange]) -> Option<ClockRange> {
    match origin {
        Some(o) => {
            if o.client == id.client && o.clock < id.clock {
                seq_ranges_find(seq_ranges, o.clock)
            } else {
                None
            }
        }
        None => None,
    }
}

#[inline]
fn origin_left_at_range_end(id: WireId, origin: Option<WireId>, range: Option<ClockRange>) -> bool {
    match (origin, range) {
        (Some(o), Some(r)) => o.clock < r.end && r.end - o.clock == 1 && r.end == id.clock,
        _ => false,
    }
}

#[inline]
fn should_skip_zero_len_item(tag: u8, len: u64, has_parent_sub_bit: bool, or_none: bool, ol_boundary: bool) -> bool {
    len == 0 && !has_parent_sub_bit && or_none && ol_boundary && (tag == 1 || tag == 4)
}

#[inline]
fn is_item_proven_seq(
    has_parent_sub_bit: bool,
    ol_none: bool,
    or_none: bool,
    ol_proven: bool,
    or_proven: bool,
    wire_parent_sub_none: bool,
    parent_is_ytext: bool,
) -> bool {
    if ol_none && or_none {
        wire_parent_sub_none && parent_is_ytext
    } else if !ol_none {
        ol_proven && !has_parent_sub_bit
    } else {
        or_proven && !has_parent_sub_bit
    }
}

#[inline]
fn classify_item_seq_provenance(
    id: WireId,
    info: u8,
    tag: u8,
    len: u64,
    hdr: &ItemHeader,
    ytext_types: &[ClockRange],
    seq_ranges: &[ClockRange],
) -> (bool, bool) {
    let has_parent_sub_bit = (info & ITEM_HAS_PARENT_SUB) != 0;
    let ol_range = lookup_proven_origin(id, hdr.origin_left, seq_ranges);
    let or_range = lookup_proven_origin(id, hdr.origin_right, seq_ranges);
    let ol_proven = ol_range.is_some();
    let or_proven = or_range.is_some();
    let ol_boundary = origin_left_at_range_end(id, hdr.origin_left, ol_range);
    let ol_none = hdr.origin_left.is_none();
    let or_none = hdr.origin_right.is_none();
    let parent_is_ytext = lookup_ytext_parent(id, hdr.parent, ytext_types);
    let skip_zero = should_skip_zero_len_item(tag, len, has_parent_sub_bit, or_none, ol_boundary);
    let proven_seq = is_item_proven_seq(
        has_parent_sub_bit,
        ol_none,
        or_none,
        ol_proven,
        or_proven,
        hdr.parent_sub.is_none(),
        parent_is_ytext,
    );
    (skip_zero, proven_seq)
}

#[inline]
fn push_wire_id(dst: &mut Vec<WireId>, id: WireId) {
    // Capacity guard satisfies Aeneas's `Vec::push` precondition.
    if dst.len() < usize::MAX {
        dst.push(id);
    }
}

#[inline]
fn extend_wire_ids(dst: &mut Vec<WireId>, src: &[WireId]) {
    let mut i = 0usize;
    while i < src.len() {
        push_wire_id(dst, src[i]);
        i += 1;
    }
}

#[inline]
fn wire_id_lt(a: WireId, b: WireId) -> bool {
    a.client < b.client || (a.client == b.client && a.clock < b.clock)
}

#[allow(clippy::manual_swap)]
fn sift_down_wire_ids(items: &mut [WireId], start: usize, end: usize) {
    let half = end / 2;
    let mut root = start;
    while root < half {
        let left = root * 2 + 1;
        let mut swap_idx = root;
        if wire_id_lt(items[swap_idx], items[left]) {
            swap_idx = left;
        }
        if left + 1 < end {
            let right = left + 1;
            if wire_id_lt(items[swap_idx], items[right]) {
                swap_idx = right;
            }
        }
        if swap_idx == root {
            root = half;
        } else {
            let tmp = items[root];
            items[root] = items[swap_idx];
            items[swap_idx] = tmp;
            root = swap_idx;
        }
    }
}

#[allow(clippy::manual_swap)]
fn sort_wire_ids(items: &mut [WireId]) {
    let n = items.len();
    if n <= 1 {
        return;
    }
    let mut start = n / 2;
    while start > 0 {
        start -= 1;
        sift_down_wire_ids(items, start, n);
    }
    let mut end = n;
    while end > 1 {
        end -= 1;
        let tmp = items[0];
        items[0] = items[end];
        items[end] = tmp;
        sift_down_wire_ids(items, 0, end);
    }
}

fn find_wire_id_lower_bound(items: &[WireId], target: WireId) -> usize {
    let mut low = 0usize;
    let mut high = items.len();
    while low < high {
        let mid = low + (high - low) / 2;
        if wire_id_lt(items[mid], target) {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}

#[inline]
fn contains_wire_id_sorted(items: &[WireId], target: WireId) -> bool {
    let idx = find_wire_id_lower_bound(items, target);
    if idx < items.len() {
        let found = items[idx];
        found.client == target.client && found.clock == target.clock
    } else {
        false
    }
}

#[inline]
fn opt_wire_id_in_sorted(items: &[WireId], opt: Option<WireId>) -> bool {
    match opt {
        Some(w) => contains_wire_id_sorted(items, w),
        None => false,
    }
}

#[inline]
fn parent_item_in_sorted(items: &[WireId], parent: WireParentCore) -> bool {
    match parent {
        WireParentCore::Item(w) => contains_wire_id_sorted(items, w),
        _ => false,
    }
}

fn alloc_zero_max_hi(len: usize) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::new();
    let mut i = 0usize;
    while i < len && out.len() < usize::MAX {
        out.push(0);
        i += 1;
    }
    out
}

fn mark_zero_strings_covered(pending: &[WireId], max_hi: &mut [usize], client: u64, start: u64, end: u64) {
    // In Yjs `readAndApplyDeleteSet`, each raw wire delete range `[start, end)`
    // is applied individually and marks a zero-length item at `clock` deleted
    // iff `start < clock < end` (requiring `end - start >= 2`).
    if end <= start || end - start < 2 {
        return;
    }
    let lo = find_wire_id_lower_bound(
        pending,
        WireId {
            client,
            clock: start + 1,
        },
    );
    let hi = find_wire_id_lower_bound(pending, WireId { client, clock: end });
    if lo < hi && lo < max_hi.len() && hi > max_hi[lo] {
        max_hi[lo] = hi;
    }
}

fn mark_point_ids_covered(pending: &[WireId], max_hi: &mut [usize], client: u64, start: u64, end: u64) {
    // A single-clock item at `clock` is deleted by a raw wire delete range
    // `[start, end)` iff `start <= clock < end`.
    if end <= start {
        return;
    }
    let lo = find_wire_id_lower_bound(pending, WireId { client, clock: start });
    let hi = find_wire_id_lower_bound(pending, WireId { client, clock: end });
    if lo < hi && lo < max_hi.len() && hi > max_hi[lo] {
        max_hi[lo] = hi;
    }
}

fn all_zero_strings_covered(max_hi: &[usize]) -> bool {
    let mut reach = 0usize;
    let mut i = 0usize;
    while i < max_hi.len() {
        if max_hi[i] > reach {
            reach = max_hi[i];
        }
        if reach <= i {
            return false;
        }
        i += 1;
    }
    true
}

struct NoopSink;

impl V1Sink for NoopSink {
    #[inline]
    fn core_validates_utf8(&self) -> bool {
        false
    }

    #[inline]
    fn validate_utf8_early(&mut self, _slot: u8, _value: Span) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline(always)]
    fn on_decode_error(&mut self, _err: CodecError, _a: usize, _b: u64) {}

    #[inline(always)]
    fn on_skipped_zero_origin(&mut self, _origin_left: WireId) {}

    #[inline]
    fn record_client(&mut self, _client: u64) -> Result<bool, CodecError> {
        Ok(true)
    }

    #[inline]
    fn begin_client(&mut self, _client: u64, _count: usize) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_gc(&mut self, _id: WireId, _len: u64) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_skip(&mut self, _id: WireId, _len: u64) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_item(&mut self, _id: WireId, _len: u64, _meta: ItemMetaCore) -> Result<(), CodecError> {
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
    fn begin_delete_client(&mut self, _client: u64, _count: usize) -> Result<(), CodecError> {
        Ok(())
    }

    #[inline]
    fn on_delete_range(&mut self, _client: u64, _start: u64, _end: u64) -> Result<(), CodecError> {
        Ok(())
    }
}

#[cold]
fn replay_client_seq_state(
    input: &[u8],
    start_pos: usize,
    start_id: WireId,
    target_idx: usize,
    limits: &DecodeLimitsCore,
    state: &mut ClientSeqState,
) -> Result<(), CodecError> {
    let mut noop = NoopSink;
    let mut cur = start_pos;
    let mut clock = start_id.clock;
    let mut idx = 0usize;
    let mut err: Option<CodecError> = None;
    while idx < target_idx && err.is_none() {
        let id = WireId {
            client: start_id.client,
            clock,
        };
        match read_u8_at(input, cur) {
            Err(e) => err = Some(e),
            Ok((info, after_info)) => {
                let tag = info & 0b1_1111;
                if tag == 0 || tag == 10 {
                    match read_var_u64_sink(input, after_info, &mut noop) {
                        Err(e) => err = Some(e),
                        Ok((len, next_cur)) => match advance_clock_sink(clock, len, &mut noop) {
                            Err(e) => err = Some(e),
                            Ok(next_clock) => {
                                clock = next_clock;
                                cur = next_cur;
                                idx += 1;
                            }
                        },
                    }
                } else {
                    match decode_item_header(input, after_info, info, &mut noop) {
                        Err(e) => err = Some(e),
                        Ok((hdr, content_start)) => {
                            match decode_item_content(input, content_start, tag, limits, 0, &mut noop) {
                                Err(e) => err = Some(e),
                                Ok((len, content_end, _)) => match advance_clock_sink(clock, len, &mut noop) {
                                    Err(e) => err = Some(e),
                                    Ok(next_clock) => {
                                        let (_, is_proven_seq) = classify_item_seq_provenance(
                                            id,
                                            info,
                                            tag,
                                            len,
                                            &hdr,
                                            &state.ytext_types,
                                            &state.seq_ranges,
                                        );
                                        if is_ytext_content(input, content_start, content_end, tag) {
                                            seq_ranges_push(&mut state.ytext_types, id.clock, next_clock);
                                        }
                                        if is_proven_seq {
                                            seq_ranges_push(&mut state.seq_ranges, id.clock, next_clock);
                                        }
                                        clock = next_clock;
                                        cur = content_end;
                                        idx += 1;
                                    }
                                },
                            }
                        }
                    }
                }
            }
        }
    }
    if let Some(e) = err {
        Err(e)
    } else {
        state.active = true;
        Ok(())
    }
}

#[cold]
#[allow(clippy::too_many_arguments)]
fn emit_tracked_item<S: V1Sink>(
    input: &[u8],
    pos: usize,
    id: WireId,
    tag: u8,
    hdr: ItemHeader,
    content_start: usize,
    len: u64,
    content_end: usize,
    entries: usize,
    content_bytes: usize,
    acc: DecodeAcc,
    is_proven_seq: bool,
    state: &mut ClientSeqState,
    sink: &mut S,
) -> Result<(u64, usize, DecodeAcc, Option<WireId>, bool), CodecError> {
    if same_wire_id_opt(state.just_skipped_ol, hdr.origin_left) {
        return Err(fail_with(sink, CodecError::ZeroLengthStruct, 0, 0));
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
    if is_ytext_content(input, content_start, content_end, tag) {
        seq_ranges_push(&mut state.ytext_types, id.clock, next_clock);
    }
    if is_proven_seq {
        seq_ranges_push(&mut state.seq_ranges, id.clock, next_clock);
    }
    state.just_skipped_ol = None;
    Ok((
        next_clock,
        content_end,
        DecodeAcc {
            structs: acc.structs,
            entries,
            content_bytes,
        },
        None,
        false,
    ))
}

#[cold]
#[allow(clippy::too_many_arguments)]
fn decode_struct_frame_tracked<S: V1Sink>(
    input: &[u8],
    pos: usize,
    id: WireId,
    info: u8,
    tag: u8,
    hdr: ItemHeader,
    content_start: usize,
    len: u64,
    content_end: usize,
    entries: usize,
    content_bytes: usize,
    acc: DecodeAcc,
    state: &mut ClientSeqState,
    sink: &mut S,
) -> Result<(u64, usize, DecodeAcc, Option<WireId>, bool), CodecError> {
    // Historical Yjs `Y.Text` updates can contain deleted zero-length items:
    // `ContentString("")` (tag 4, strictly covered by a raw wire delete range)
    // and `ContentDeleted(0)` (tag 1, emitted when Yjs re-encodes a deleted
    // empty string). Zero-length items violate Yjs's own `length >= 1`
    // invariant (`Item.lastId = clock - 1`), so stripping them heals corrupt
    // historical updates rather than attempting an impossible multi-peer
    // isomorphism. Only skip `tag == 1 || tag == 4` when:
    // 1. `ITEM_HAS_PARENT_SUB` is clear,
    // 2. `origin_right` is absent and `origin_left` is immediately adjacent to
    //    `id` (`r.end == id.clock` and `o.clock == id.clock - 1`) at the outer
    //    end of a proven `ContentType(Y.Text, kind=2)` range in this client
    //    block (rejecting untyped roots, `Y.Array`, `Y.Map`, surrogate splits,
    //    and non-adjacent `Z.lastId` gaps),
    // 3. at most one zero-length item is skipped at any clock and no same-clock
    //    struct shares its `origin_left`, and
    // 4. `verify_skipped_zero_items` confirms strict raw-range DS coverage for
    //    `tag == 4` and that every colliding item sharing `origin_left` across
    //    all clients is a single-clock deleted tombstone with no dependents.
    let (skip_zero, is_proven_seq) =
        classify_item_seq_provenance(id, info, tag, len, &hdr, &state.ytext_types, &state.seq_ranges);
    if skip_zero && state.just_skipped_ol.is_none() {
        state.just_skipped_ol = hdr.origin_left;
        return Ok((
            id.clock,
            content_end,
            DecodeAcc {
                structs: acc.structs,
                entries,
                content_bytes,
            },
            hdr.origin_left,
            tag == 4,
        ));
    }
    emit_tracked_item(
        input,
        pos,
        id,
        tag,
        hdr,
        content_start,
        len,
        content_end,
        entries,
        content_bytes,
        acc,
        is_proven_seq,
        state,
        sink,
    )
}

#[cold]
#[allow(clippy::too_many_arguments)]
fn decode_struct_frame_slow<S: V1Sink>(
    input: &[u8],
    pos: usize,
    client_start_pos: usize,
    client_start_clock: u64,
    s_idx: usize,
    id: WireId,
    info: u8,
    tag: u8,
    hdr: ItemHeader,
    content_start: usize,
    len: u64,
    content_end: usize,
    entries: usize,
    content_bytes: usize,
    limits: &DecodeLimitsCore,
    acc: DecodeAcc,
    state: &mut ClientSeqState,
    sink: &mut S,
) -> Result<(u64, usize, DecodeAcc, Option<WireId>, bool), CodecError> {
    if !state.active {
        replay_client_seq_state(
            input,
            client_start_pos,
            WireId {
                client: id.client,
                clock: client_start_clock,
            },
            s_idx,
            limits,
            state,
        )?;
    }
    decode_struct_frame_tracked(
        input,
        pos,
        id,
        info,
        tag,
        hdr,
        content_start,
        len,
        content_end,
        entries,
        content_bytes,
        acc,
        state,
        sink,
    )
}

#[cold]
#[allow(clippy::too_many_arguments)]
fn collect_colliding_in_client(
    input: &[u8],
    start_pos: usize,
    start_id: WireId,
    count: usize,
    limits: &DecodeLimitsCore,
    skipped_ols: &[WireId],
    colliding_ids: &mut Vec<WireId>,
    pending_colliding: &mut Vec<WireId>,
) -> Result<usize, CodecError> {
    let mut noop = NoopSink;
    let mut cur = start_pos;
    let mut clock = start_id.clock;
    let mut s_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while s_idx < count && err.is_none() {
        let id = WireId {
            client: start_id.client,
            clock,
        };
        match read_u8_at(input, cur) {
            Err(e) => err = Some(e),
            Ok((info, after_info)) => {
                let tag = info & 0b1_1111;
                if tag == 0 || tag == 10 {
                    match read_var_u64_sink(input, after_info, &mut noop) {
                        Err(e) => err = Some(e),
                        Ok((len, next_cur)) => match advance_clock_sink(clock, len, &mut noop) {
                            Err(e) => err = Some(e),
                            Ok(next_clock) => {
                                clock = next_clock;
                                cur = next_cur;
                                s_idx += 1;
                            }
                        },
                    }
                } else {
                    match decode_item_header(input, after_info, info, &mut noop) {
                        Err(e) => err = Some(e),
                        Ok((hdr, content_start)) => {
                            match decode_item_content(input, content_start, tag, limits, 0, &mut noop) {
                                Err(e) => err = Some(e),
                                Ok((len, content_end, _)) => {
                                    if len == 0 {
                                        cur = content_end;
                                        s_idx += 1;
                                    } else {
                                        match advance_clock_sink(clock, len, &mut noop) {
                                            Err(e) => err = Some(e),
                                            Ok(next_clock) => {
                                                if opt_wire_id_in_sorted(skipped_ols, hdr.origin_left) {
                                                    if len != 1 {
                                                        err = Some(CodecError::ZeroLengthStruct);
                                                    } else {
                                                        push_wire_id(colliding_ids, id);
                                                        if tag != 1 {
                                                            push_wire_id(pending_colliding, id);
                                                        }
                                                    }
                                                }
                                                clock = next_clock;
                                                cur = content_end;
                                                s_idx += 1;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(cur) }
}

#[cold]
fn collect_colliding_origin_items(
    input: &[u8],
    clients_start: usize,
    clients: usize,
    limits: &DecodeLimitsCore,
    skipped_ols: &[WireId],
) -> Result<(Vec<WireId>, Vec<WireId>), CodecError> {
    let mut noop = NoopSink;
    let mut cur = clients_start;
    let mut colliding_ids: Vec<WireId> = Vec::new();
    let mut pending_colliding: Vec<WireId> = Vec::new();
    let mut c_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while c_idx < clients && err.is_none() {
        match read_var_u64_sink(input, cur, &mut noop) {
            Err(e) => err = Some(e),
            Ok((count_u64, p1)) => match checked_usize_limit(count_u64, LimitKind::Structs) {
                Err(e) => err = Some(e),
                Ok(count) => match read_var_u64_sink(input, p1, &mut noop) {
                    Err(e) => err = Some(e),
                    Ok((client, p2)) => match read_var_u64_sink(input, p2, &mut noop) {
                        Err(e) => err = Some(e),
                        Ok((clock, p3)) => match collect_colliding_in_client(
                            input,
                            p3,
                            WireId { client, clock },
                            count,
                            limits,
                            skipped_ols,
                            &mut colliding_ids,
                            &mut pending_colliding,
                        ) {
                            Err(e) => err = Some(e),
                            Ok(next_cur) => {
                                cur = next_cur;
                                c_idx += 1;
                            }
                        },
                    },
                },
            },
        }
    }
    if let Some(e) = err {
        Err(e)
    } else {
        Ok((colliding_ids, pending_colliding))
    }
}

#[cold]
fn client_has_origin_in(
    input: &[u8],
    start_pos: usize,
    count: usize,
    limits: &DecodeLimitsCore,
    target_ids: &[WireId],
) -> Result<(usize, bool), CodecError> {
    let mut noop = NoopSink;
    let mut cur = start_pos;
    let mut s_idx = 0usize;
    let mut found = false;
    let mut err: Option<CodecError> = None;
    while s_idx < count && !found && err.is_none() {
        match read_u8_at(input, cur) {
            Err(e) => err = Some(e),
            Ok((info, after_info)) => {
                let tag = info & 0b1_1111;
                if tag == 0 || tag == 10 {
                    match read_var_u64_sink(input, after_info, &mut noop) {
                        Err(e) => err = Some(e),
                        Ok((_, next_cur)) => {
                            cur = next_cur;
                            s_idx += 1;
                        }
                    }
                } else {
                    match decode_item_header(input, after_info, info, &mut noop) {
                        Err(e) => err = Some(e),
                        Ok((hdr, content_start)) => {
                            if opt_wire_id_in_sorted(target_ids, hdr.origin_left)
                                || opt_wire_id_in_sorted(target_ids, hdr.origin_right)
                                || parent_item_in_sorted(target_ids, hdr.parent)
                            {
                                found = true;
                            } else {
                                match decode_item_content(input, content_start, tag, limits, 0, &mut noop) {
                                    Err(e) => err = Some(e),
                                    Ok((_, content_end, _)) => {
                                        cur = content_end;
                                        s_idx += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok((cur, found)) }
}

#[cold]
fn has_origin_referencing(
    input: &[u8],
    clients_start: usize,
    clients: usize,
    limits: &DecodeLimitsCore,
    target_ids: &[WireId],
) -> Result<bool, CodecError> {
    let mut noop = NoopSink;
    let mut cur = clients_start;
    let mut c_idx = 0usize;
    let mut found = false;
    let mut err: Option<CodecError> = None;
    while c_idx < clients && !found && err.is_none() {
        match read_var_u64_sink(input, cur, &mut noop) {
            Err(e) => err = Some(e),
            Ok((count_u64, p1)) => match checked_usize_limit(count_u64, LimitKind::Structs) {
                Err(e) => err = Some(e),
                Ok(count) => match read_var_u64_sink(input, p1, &mut noop) {
                    Err(e) => err = Some(e),
                    Ok((_, p2)) => match read_var_u64_sink(input, p2, &mut noop) {
                        Err(e) => err = Some(e),
                        Ok((_, p3)) => match client_has_origin_in(input, p3, count, limits, target_ids) {
                            Err(e) => err = Some(e),
                            Ok((next_cur, hit)) => {
                                cur = next_cur;
                                found = hit;
                                c_idx += 1;
                            }
                        },
                    },
                },
            },
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(found) }
}

#[cold]
#[allow(clippy::too_many_arguments)]
fn scan_delete_ranges_coverage(
    input: &[u8],
    start_pos: usize,
    client: u64,
    range_count: usize,
    pending_zeros: &[WireId],
    zero_max_hi: &mut [usize],
    pending_colliding: &[WireId],
    coll_max_hi: &mut [usize],
) -> Result<usize, CodecError> {
    let mut noop = NoopSink;
    let mut cur = start_pos;
    let mut r_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while r_idx < range_count && err.is_none() {
        match read_one_delete_range_sink(input, cur, &mut noop) {
            Err(e) => err = Some(e),
            Ok((start, end, q2)) => {
                if start != end {
                    if !pending_zeros.is_empty() {
                        mark_zero_strings_covered(pending_zeros, zero_max_hi, client, start, end);
                    }
                    if !pending_colliding.is_empty() {
                        mark_point_ids_covered(pending_colliding, coll_max_hi, client, start, end);
                    }
                }
                cur = q2;
                r_idx += 1;
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(cur) }
}

#[cold]
#[allow(clippy::too_many_arguments)]
fn scan_delete_set_coverage(
    input: &[u8],
    ds_start: usize,
    pending_zeros: &[WireId],
    zero_max_hi: &mut [usize],
    pending_colliding: &[WireId],
    coll_max_hi: &mut [usize],
) -> Result<(), CodecError> {
    let mut noop = NoopSink;
    let (clients_u64, mut cur) = read_var_u64_sink(input, ds_start, &mut noop)?;
    let delete_clients = checked_usize_limit(clients_u64, LimitKind::DeleteClients)?;
    let mut c_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while c_idx < delete_clients && err.is_none() {
        match read_var_u64_sink(input, cur, &mut noop) {
            Err(e) => err = Some(e),
            Ok((client, p1)) => match read_var_u64_sink(input, p1, &mut noop) {
                Err(e) => err = Some(e),
                Ok((ranges_u64, p2)) => match checked_usize_limit(ranges_u64, LimitKind::DeleteRanges) {
                    Err(e) => err = Some(e),
                    Ok(range_count) => match scan_delete_ranges_coverage(
                        input,
                        p2,
                        client,
                        range_count,
                        pending_zeros,
                        zero_max_hi,
                        pending_colliding,
                        coll_max_hi,
                    ) {
                        Err(e) => err = Some(e),
                        Ok(next_cur) => {
                            cur = next_cur;
                            c_idx += 1;
                        }
                    },
                },
            },
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(()) }
}

#[cold]
fn verify_delete_set_coverage(
    input: &[u8],
    ds_start: usize,
    pending_zero_strings: &mut [WireId],
    pending_colliding: &mut [WireId],
) -> Result<(), CodecError> {
    if pending_zero_strings.is_empty() && pending_colliding.is_empty() {
        return Ok(());
    }
    let mut zero_max_hi = if pending_zero_strings.is_empty() {
        Vec::new()
    } else {
        sort_wire_ids(pending_zero_strings);
        alloc_zero_max_hi(pending_zero_strings.len())
    };
    let mut coll_max_hi = if pending_colliding.is_empty() {
        Vec::new()
    } else {
        sort_wire_ids(pending_colliding);
        alloc_zero_max_hi(pending_colliding.len())
    };
    scan_delete_set_coverage(
        input,
        ds_start,
        pending_zero_strings,
        &mut zero_max_hi,
        pending_colliding,
        &mut coll_max_hi,
    )?;
    if !pending_zero_strings.is_empty() && !all_zero_strings_covered(&zero_max_hi) {
        return Err(CodecError::ZeroLengthStruct);
    }
    if !pending_colliding.is_empty() && !all_zero_strings_covered(&coll_max_hi) {
        return Err(CodecError::ZeroLengthStruct);
    }
    Ok(())
}

#[cold]
#[allow(clippy::too_many_arguments)]
fn verify_skipped_zero_items(
    input: &[u8],
    clients_start: usize,
    clients: usize,
    ds_start: usize,
    limits: &DecodeLimitsCore,
    skipped_ols: &mut [WireId],
    pending_zero_strings: &mut [WireId],
) -> Result<(), CodecError> {
    sort_wire_ids(skipped_ols);
    let (mut colliding_ids, mut pending_colliding) =
        collect_colliding_origin_items(input, clients_start, clients, limits, skipped_ols)?;
    if !colliding_ids.is_empty() {
        sort_wire_ids(&mut colliding_ids);
        if has_origin_referencing(input, clients_start, clients, limits, &colliding_ids)? {
            return Err(CodecError::ZeroLengthStruct);
        }
    }
    verify_delete_set_coverage(input, ds_start, pending_zero_strings, &mut pending_colliding)
}

#[inline]
#[allow(clippy::too_many_arguments)]
fn decode_struct_frame<S: V1Sink>(
    input: &[u8],
    pos: usize,
    client_start_pos: usize,
    client_start_clock: u64,
    s_idx: usize,
    id: WireId,
    limits: &DecodeLimitsCore,
    acc: DecodeAcc,
    state: &mut ClientSeqState,
    sink: &mut S,
) -> Result<(u64, usize, DecodeAcc, Option<WireId>, bool), CodecError> {
    let (info, cur) = read_u8_at(input, pos)?;
    let tag = info & 0b1_1111;
    if tag == 0 {
        let (len, p) = read_var_u64_sink(input, cur, sink)?;
        let next_clock = advance_clock_sink(id.clock, len, sink)?;
        sink.on_gc(id, len)?;
        if state.active {
            state.just_skipped_ol = None;
        }
        return Ok((next_clock, p, acc, None, false));
    }
    if tag == 10 {
        let (len, p) = read_var_u64_sink(input, cur, sink)?;
        let next_clock = advance_clock_sink(id.clock, len, sink)?;
        sink.on_skip(id, len)?;
        if state.active {
            state.just_skipped_ol = None;
        }
        return Ok((next_clock, p, acc, None, false));
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
    if len == 0 || state.active {
        return decode_struct_frame_slow(
            input,
            pos,
            client_start_pos,
            client_start_clock,
            s_idx,
            id,
            info,
            tag,
            hdr,
            content_start,
            len,
            content_end,
            entries,
            content_bytes,
            limits,
            acc,
            state,
            sink,
        );
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
        None,
        false,
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
) -> Result<(usize, DecodeAcc, Vec<WireId>, Vec<WireId>), CodecError> {
    let mut cur = start_pos;
    let mut clock = start_id.clock;
    let mut acc = start_acc;
    let mut state = ClientSeqState {
        active: false,
        ytext_types: Vec::new(),
        seq_ranges: Vec::new(),
        just_skipped_ol: None,
    };
    let mut skipped_ols: Vec<WireId> = Vec::new();
    let mut pending_zero_strings: Vec<WireId> = Vec::new();
    let mut s_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while s_idx < count && err.is_none() {
        let id = WireId {
            client: start_id.client,
            clock,
        };
        match decode_struct_frame(
            input,
            cur,
            start_pos,
            start_id.clock,
            s_idx,
            id,
            limits,
            acc,
            &mut state,
            sink,
        ) {
            Err(e) => err = Some(e),
            Ok((next_clock, next_cur, next_acc, skipped_ol, needs_delete_check)) => {
                if let Some(ol) = skipped_ol {
                    sink.on_skipped_zero_origin(ol);
                    push_wire_id(&mut skipped_ols, ol);
                }
                if needs_delete_check {
                    push_wire_id(&mut pending_zero_strings, id);
                }
                clock = next_clock;
                cur = next_cur;
                acc = next_acc;
                s_idx += 1;
            }
        }
    }
    if let Some(e) = err {
        Err(e)
    } else {
        Ok((cur, acc, skipped_ols, pending_zero_strings))
    }
}

#[inline]
fn decode_one_client_block<S: V1Sink>(
    input: &[u8],
    cur: usize,
    limits: &DecodeLimitsCore,
    acc: DecodeAcc,
    sink: &mut S,
) -> Result<(usize, DecodeAcc, Vec<WireId>, Vec<WireId>), CodecError> {
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
///
/// # Historical zero-length item recovery contract
///
/// Valid Yjs / YATA items always have `length >= 1`. Historical Yjs documents
/// can nevertheless contain a deleted zero-length `ContentString("")` (tag 4)
/// or re-encoded `ContentDeleted(0)` (tag 1) immediately following a proven
/// `Y.Text` sequence boundary. When strictly validated (adjacent `origin_left`
/// at `r.end == id.clock`, `origin_right == None`, no `parent_sub` bit,
/// `ContentString("")` strictly covered by a raw DeleteSet range
/// `start < clock < end`, and every same-`origin_left` colliding item across
/// the frame is single-clock, deleted, and unreferenced), the decoder strips
/// the zero-length item and notifies [`V1Sink::on_skipped_zero_origin`].
///
/// This is an explicit **valid-struct (`gc: false`) recovery transformation**,
/// not bit-for-bit emulation of Yjs 13.6.33 bugs on `length == 0` structs:
/// - Yjs 13.6.33 computes `Item.lastId = clock + length - 1` (underflowing to
///   `clock - 1` when `length == 0`), causing pure Yjs replicas to diverge on
///   concurrent appends; stripping repairs the snapshot to valid-struct order.
/// - Under `gc: true`, Yjs 13.6.33's `ContentType.gc -> replaceStruct` calls
///   `findIndexSS(clock)`, skipping the zero-length item and overwriting an
///   unrelated live struct at the same clock (dropping unrelated map keys on
///   re-encode and shrinking the state vector). Stripping preserves the valid
///   `gc: false` state and state vector instead of replicating that data loss.
/// - Collision and reference checks apply within each self-contained V1 update
///   frame and across batches in `merge_updates_v1`. Once a historical snapshot
///   is healed into a live `Doc`, subsequent incremental updates operate on the
///   healed valid-struct document.
#[inline]
pub fn decode_update_v1<S: V1Sink>(input: &[u8], sink: &mut S, limits: &DecodeLimitsCore) -> Result<(), CodecError> {
    let (clients_u64, clients_start) = read_var_u64_sink(input, 0, sink)?;
    let mut cur = clients_start;
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
    let mut skipped_ols: Vec<WireId> = Vec::new();
    let mut pending_zero_strings: Vec<WireId> = Vec::new();

    let mut c_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while c_idx < clients && err.is_none() {
        match decode_one_client_block(input, cur, limits, acc, sink) {
            Err(e) => err = Some(e),
            Ok((next_cur, next_acc, client_ols, client_zeros)) => {
                if !client_ols.is_empty() {
                    extend_wire_ids(&mut skipped_ols, &client_ols);
                }
                if !client_zeros.is_empty() {
                    extend_wire_ids(&mut pending_zero_strings, &client_zeros);
                }
                cur = next_cur;
                acc = next_acc;
                c_idx += 1;
            }
        }
    }
    if let Some(e) = err {
        return Err(e);
    }

    let ds_start = cur;
    let end_pos = decode_delete_set_v1(input, ds_start, limits, acc.entries, sink)?;
    if end_pos != input.len() {
        return Err(fail_with(sink, CodecError::TrailingBytes, input.len() - end_pos, 0));
    }
    if !skipped_ols.is_empty() {
        match verify_skipped_zero_items(
            input,
            clients_start,
            clients,
            ds_start,
            limits,
            &mut skipped_ols,
            &mut pending_zero_strings,
        ) {
            Ok(()) => {}
            Err(e) => return Err(fail_with(sink, e, 0, 0)),
        }
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

    #[inline(always)]
    fn on_skipped_zero_origin(&mut self, _origin_left: WireId) {}

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

    #[test]
    fn zero_length_items_are_skipped_while_unsafe_forms_fail() {
        // client=1, start=0, 10 structs -> 8 emitted (skips clock 5 "" and
        // clock 9 ContentDeleted(0)), with overlapping raw wire DS
        // [2,5)+[3,7) strictly covering clock 5 (`3 < 5 < 7`) and deleting the
        // colliding `\n` at clock 6 (`3 <= 6 < 7`).
        let update = [
            1u8, 10, 1, 0, // 1 client, 10 structs, client=1, start_clock=0
            0x27, 1, 1, b'b', 1, b't', 2, // 0..1: b["t"] = ContentType(Y.Text)
            0x04, 0, 1, 0, 2, b'a', b'b', // 1..3: Y.Text "ab"
            0x24, 1, 1, b'm', 1, b'k', 1, b'v', // 3..4: map "m"["k"] = "v"
            0x84, 1, 2, 1, b'c', // 4..5: Y.Text "c" with ol=(1,2)
            0x84, 1, 4, 0, // 5..5: Y.Text ContentString("") with ol=(1,4)
            0x24, 1, 1, b'm', 1, b'j', 1, b'w', // 5..6: map "m"["j"] = "w"
            0x84, 1, 4, 1, b'\n', // 6..7: colliding "\n" deleted by [3,7)
            0x27, 1, 1, b'b', 1, b'u', 2, // 7..8: b["u"] = ContentType(Y.Text)
            0x04, 0, 1, 7, 1, b'd', // 8..9: Y.Text "d"
            0x81, 1, 8, 0, // 9..9: Y.Text ContentDeleted(0) with ol=(1,8)
            1, 1, 2, 2, 3, 3, 4, // DS: client 1, overlapping [2,5) + [3,7)
        ];
        let summary = decode_update_v1_frame(&update, &DecodeLimitsCore::default_update()).unwrap();
        assert_eq!(summary.clients, 1);
        assert_eq!(summary.structs, 8);

        // Limits still count skipped zero-length structs and their content
        // bytes.
        let mut tight_structs = DecodeLimitsCore::default_update();
        tight_structs.max_structs = 9;
        assert_eq!(
            decode_update_v1_frame(&update, &tight_structs),
            Err(CodecError::ResourceLimit(LimitKind::Structs))
        );

        let mut tight_bytes = DecodeLimitsCore::default_update();
        tight_bytes.max_content_bytes = 15;
        assert_eq!(
            decode_update_v1_frame(&update, &tight_bytes),
            Err(CodecError::ResourceLimit(LimitKind::ContentBytes))
        );

        // Invalid UTF-8 in the header of a zero-length item is still rejected.
        let bad_parent = [1u8, 1, 1, 0, 0x04, 1, 1, 0xff, 0, 0];
        assert_eq!(
            decode_update_v1_frame(&bad_parent, &DecodeLimitsCore::default_update()),
            Err(CodecError::InvalidUtf8)
        );

        // All unproven, non-YText, live (not strictly covered by a single raw
        // wire delete range), colliding-origin, or side-effecting zero-length
        // forms remain rejected.
        let rejected_cases: &[&[u8]] = &[
            // same-client later live item sharing skipped Z origin_left
            &[
                1, 5, 10, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 10, 0, 4, 0xf0, 0x9f, 0x98, 0x80, 0x81, 10, 2, 0,
                0x24, 1, 1, b'm', 1, b'k', 1, b'v', 0x84, 10, 2, 1, b'x', 0,
            ],
            // cross-client live item sharing skipped Z origin_left
            &[
                2, 4, 10, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 10, 0, 4, 0xf0, 0x9f, 0x98, 0x80, 0x81, 10, 2, 0,
                0x24, 1, 1, b'm', 1, b'k', 1, b'v', 1, 5, 0, 0x84, 10, 2, 1, b'x', 0,
            ],
            // 2-hop live descendant of deleted colliding item
            &[
                1, 6, 10, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 10, 0, 4, 0xf0, 0x9f, 0x98, 0x80, 0x81, 10, 2, 0,
                0x24, 1, 1, b'm', 1, b'k', 1, b'v', 0x81, 10, 2, 1, 0x84, 10, 4, 1, b'w', 0,
            ],
            // non-adjacent Z where origin_left.clock != Z.clock - 1
            &[
                1, 4, 10, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 10, 0, 1, b'a', 0x24, 1, 1, b'm', 1, b'k', 1, b'v',
                0x81, 10, 1, 0, 0,
            ],
            // adjacent raw wire DS [2,3) + [3,4) leaves clock 3 live in Yjs
            &[
                0x01, 0x06, 0x01, 0x00, 0x06, 0x01, 0x01, 0x74, 0x04, 0x62, 0x6f, 0x6c, 0x64, 0x04, 0x6e, 0x75, 0x6c,
                0x6c, 0x46, 0x01, 0x00, 0x04, 0x62, 0x6f, 0x6c, 0x64, 0x04, 0x74, 0x72, 0x75, 0x65, 0x28, 0x01, 0x01,
                0x6d, 0x01, 0x6b, 0x01, 0x77, 0x01, 0x76, 0x84, 0x01, 0x01, 0x00, 0x84, 0x01, 0x00, 0x01, 0x77, 0x84,
                0x01, 0x03, 0x01, 0x61, 0x01, 0x01, 0x02, 0x02, 0x01, 0x03, 0x01,
            ],
            // nested Y.Text with adjacent raw wire DS [4,5) + [5,6)
            &[
                1, 6, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 2, b'a', b'b', 0x24, 1, 1, b'm', 1, b'k', 1,
                b'v', 0x84, 1, 2, 1, b'c', 0x84, 1, 4, 0, 0x24, 1, 1, b'm', 1, b'j', 1, b'w', 1, 1, 2, 4, 1, 5, 1,
            ],
            // deleted ContentDeleted(0) right-anchor in Y.Array
            &[
                0x01, 0x04, 0x0a, 0x00, 0x08, 0x01, 0x01, 0x74, 0x01, 0x77, 0x01, 0x61, 0x48, 0x0a, 0x00, 0x01, 0x77,
                0x01, 0x62, 0x81, 0x0a, 0x01, 0x00, 0xc8, 0x0a, 0x01, 0x0a, 0x00, 0x01, 0x77, 0x01, 0x64, 0x00,
            ],
            // nested ContentType(Y.Array, kind=0) with ContentDeleted(0)
            &[
                1, 3, 1, 0, 0x27, 1, 1, b'b', 1, b'a', 0, 0x08, 0, 1, 0, 1, 0x77, 1, b'x', 0x81, 1, 1, 0, 0,
            ],
            // untyped root "t" with ContentString + ContentDeleted(0)
            &[1, 2, 1, 0, 0x04, 1, 1, b't', 1, b'a', 0x81, 1, 0, 0, 0],
            // nested Y.Text with same-clock colliding successor
            &[
                1, 4, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 1, b'a', 0x81, 1, 1, 0, 0x84, 1, 1, 1, b'b', 0,
            ],
            // nested Y.Text with two consecutive zero-length items at clock 5
            &[
                1, 7, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 2, b'a', b'b', 0x24, 1, 1, b'm', 1, b'k', 1,
                b'v', 0x84, 1, 2, 1, b'c', 0x81, 1, 4, 0, 0x81, 1, 2, 0, 0x84, 1, 4, 1, b'd', 0,
            ],
            // live ContentString("") ASCII next-insert anchor (empty DS)
            &[
                0x01, 0x04, 0x0a, 0x00, 0x04, 0x01, 0x01, 0x74, 0x01, 0x61, 0x44, 0x0a, 0x00, 0x01, 0x62, 0x84, 0x0a,
                0x01, 0x00, 0xc4, 0x0a, 0x01, 0x0a, 0x00, 0x01, 0x64, 0x00,
            ],
            // live ContentString("") with DS [2,3) starting AT clock 2
            &[
                0x01, 0x04, 0x0a, 0x00, 0x04, 0x01, 0x01, 0x74, 0x01, 0x61, 0x44, 0x0a, 0x00, 0x01, 0x62, 0x84, 0x0a,
                0x01, 0x00, 0xc4, 0x0a, 0x01, 0x0a, 0x00, 0x01, 0x64, 0x01, 0x0a, 0x01, 0x02, 0x01,
            ],
            // live ContentString("") with DS [1,2) ending AT clock 2
            &[
                0x01, 0x04, 0x0a, 0x00, 0x04, 0x01, 0x01, 0x74, 0x01, 0x61, 0x44, 0x0a, 0x00, 0x01, 0x62, 0x84, 0x0a,
                0x01, 0x00, 0xc4, 0x0a, 0x01, 0x0a, 0x00, 0x01, 0x64, 0x01, 0x0a, 0x01, 0x01, 0x01,
            ],
            // live ContentString("") between bold=true and bold=null
            &[
                0x01, 0x04, 0x01, 0x00, 0x06, 0x01, 0x01, 0x74, 0x04, 0x62, 0x6f, 0x6c, 0x64, 0x04, 0x6e, 0x75, 0x6c,
                0x6c, 0x46, 0x01, 0x00, 0x04, 0x62, 0x6f, 0x6c, 0x64, 0x04, 0x74, 0x72, 0x75, 0x65, 0xc4, 0x01, 0x01,
                0x01, 0x00, 0x00, 0x84, 0x01, 0x00, 0x01, 0x61, 0x00,
            ],
            // ContentDeleted(0) with origin_right present in nested Y.Text
            &[
                1, 4, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 1, b'a', 0x41, 1, 1, 0, 0x24, 1, 1, b'm', 1,
                b'k', 1, b'v', 0,
            ],
            // Root ContentString("")
            &[1, 2, 1, 0, 0x04, 1, 1, b't', 0, 0x04, 1, 1, b't', 1, b'a', 0],
            // Root ContentDeleted(0)
            &[1, 2, 1, 0, 0x01, 1, 1, b't', 0, 0x04, 1, 1, b't', 1, b'a', 0],
            // explicit parent_sub ContentString("")
            &[1, 2, 1, 0, 0x24, 0, 1, 0, 1, b'k', 0, 0x04, 1, 1, b't', 1, b'a', 0],
            // explicit parent_sub ContentDeleted(0)
            &[1, 2, 1, 0, 0x21, 0, 1, 0, 1, b'k', 0, 0x04, 1, 1, b't', 1, b'a', 0],
            // missing nested Item((3,0)) parent
            &[1, 2, 1, 0, 0x04, 0, 3, 0, 0, 0x04, 1, 1, b't', 1, b'a', 0],
            // missing/cross-client origin_left=(3,0)
            &[1, 2, 1, 0, 0x84, 3, 0, 0, 0x04, 1, 1, b't', 1, b'a', 0],
            // cross-client origin_right=(3,0)
            &[
                1, 3, 1, 0, 0x04, 1, 1, b't', 1, b'a', 0xc4, 1, 0, 3, 0, 0, 0x84, 1, 0, 1, b'b', 0,
            ],
            // same-client inherited map key
            &[1, 2, 1, 0, 0x24, 1, 1, b'm', 1, b'k', 1, b'v', 0x81, 1, 0, 0, 0],
            // ITEM_HAS_PARENT_SUB set with origin_left in nested Y.Text
            &[
                1, 3, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 1, b'a', 0xa1, 1, 1, 0, 0,
            ],
            // origin_left points to GC
            &[1, 2, 1, 0, 0x00, 1, 0x81, 1, 0, 0, 0],
            // Inherit ContentAny([]) in nested Y.Text
            &[
                1, 3, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 1, b'a', 0x88, 1, 1, 0, 0,
            ],
            // Inherit ContentJSON([]) in nested Y.Text
            &[
                1, 3, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 1, b'a', 0x82, 1, 1, 0, 0,
            ],
            // zero-len-only client (start=0)
            &[1, 1, 1, 0, 0x81, 1, 0, 0, 0],
            // zero-len-only client (start=7)
            &[1, 1, 1, 7, 0x81, 1, 6, 0, 0],
            // origin_left splits surrogate pair (😀 at 1..3, ol=(1,1))
            &[
                1, 3, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 4, 0xf0, 0x9f, 0x98, 0x80, 0x81, 1, 1, 0, 0,
            ],
            // origin_right splits surrogate pair (😀 at 1..3, or=(1,2))
            &[
                1, 3, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 4, 0xf0, 0x9f, 0x98, 0x80, 0x41, 1, 2, 0, 0,
            ],
            // GC(0)
            &[1, 1, 1, 0, 0x00, 0, 0],
            // Skip(0)
            &[1, 1, 1, 0, 0x0a, 0, 0],
        ];
        for case in rejected_cases {
            assert_eq!(
                decode_update_v1_frame(case, &DecodeLimitsCore::default_update()),
                Err(CodecError::ZeroLengthStruct)
            );
        }
    }

    #[test]
    fn zero_length_delete_set_check_is_linearithmic_on_interleaved_ds() {
        fn push_var_u64(buf: &mut Vec<u8>, mut v: u64) {
            while v >= 0x80 {
                buf.push(((v as u8) & 0x7f) | 0x80);
                v >>= 7;
            }
            buf.push(v as u8);
        }

        // 64 descending struct clients each with 2 deleted ContentString("")
        // items (128 pending zero-length items exercising multi-element
        // heapsort + binary search + overlapping length>=2 range union), plus
        // 500 extra descending DS clients and 2,000 interleaved length>=2 DS
        // ranges.
        let struct_clients = if cfg!(miri) { 8u64 } else { 64u64 };
        let mut buf = Vec::new();
        push_var_u64(&mut buf, struct_clients);
        for c in (1..=struct_clients).rev() {
            // 8 structs -> 6 emitted (clocks 2 and 6 skipped):
            // 0..1 Y.Text, 1..2 "a", 2..2 "", 2..3 m["k"]="v",
            // 3..4 Y.Text, 4..6 "bc", 6..6 "", 6..7 m["j"]="w"
            push_var_u64(&mut buf, 8);
            push_var_u64(&mut buf, c);
            push_var_u64(&mut buf, 0);
            buf.extend_from_slice(&[0x27, 1, 1, b'b', 1, b't', 2]);
            buf.push(0x04);
            buf.push(0);
            push_var_u64(&mut buf, c);
            buf.push(0);
            buf.extend_from_slice(&[1, b'a']);
            buf.push(0x84);
            push_var_u64(&mut buf, c);
            buf.push(1);
            buf.push(0);
            buf.extend_from_slice(&[0x24, 1, 1, b'm', 1, b'k', 1, b'v']);
            buf.extend_from_slice(&[0x27, 1, 1, b'b', 1, b'u', 2]);
            buf.push(0x04);
            buf.push(0);
            push_var_u64(&mut buf, c);
            buf.push(3);
            buf.extend_from_slice(&[2, b'b', b'c']);
            buf.push(0x84);
            push_var_u64(&mut buf, c);
            buf.push(5);
            buf.push(0);
            buf.extend_from_slice(&[0x24, 1, 1, b'm', 1, b'j', 1, b'w']);
        }

        let extra_clients = if cfg!(miri) { 16u64 } else { 500u64 };
        let interleaved_ranges = if cfg!(miri) { 64u64 } else { 2_000u64 };
        push_var_u64(&mut buf, extra_clients + struct_clients);
        for c in ((struct_clients + 1)..=(struct_clients + extra_clients)).rev() {
            push_var_u64(&mut buf, c);
            push_var_u64(&mut buf, 1);
            push_var_u64(&mut buf, 0);
            push_var_u64(&mut buf, 2);
        }
        // Client 1 gets 2,000 interleaved length-2 ranges + overlapping [1,4)
        // and [3,7) covering clocks 2 and 6.
        push_var_u64(&mut buf, 1);
        push_var_u64(&mut buf, interleaved_ranges + 2);
        for i in 0..interleaved_ranges {
            let clk = if i % 2 == 0 {
                20 + i * 3
            } else {
                20 + (interleaved_ranges - i) * 3
            };
            push_var_u64(&mut buf, clk);
            push_var_u64(&mut buf, 2);
        }
        push_var_u64(&mut buf, 1);
        push_var_u64(&mut buf, 3); // [1, 4) covers clock 2
        push_var_u64(&mut buf, 3);
        push_var_u64(&mut buf, 4); // [3, 7) covers clock 6
        // Clients 2..=struct_clients each get overlapping [1,4) + [5,7).
        for c in 2..=struct_clients {
            push_var_u64(&mut buf, c);
            push_var_u64(&mut buf, 2);
            push_var_u64(&mut buf, 1);
            push_var_u64(&mut buf, 3);
            push_var_u64(&mut buf, 5);
            push_var_u64(&mut buf, 2);
        }

        let summary = decode_update_v1_frame(&buf, &DecodeLimitsCore::default_update()).unwrap();
        assert_eq!(summary.clients, struct_clients as usize);
        assert_eq!(summary.structs, (struct_clients * 6) as usize);
        assert_eq!(summary.delete_clients, (extra_clients + struct_clients) as usize);
        assert_eq!(
            summary.delete_ranges,
            (extra_clients + interleaved_ranges + struct_clients * 2) as usize
        );
    }
}
