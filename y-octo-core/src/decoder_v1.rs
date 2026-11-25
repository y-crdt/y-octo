use alloc::vec::Vec;

use crate::{
    CodecError,
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

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
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

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(aeneas_extract), derive(Debug))]
pub struct UpdateSummary {
    pub clients: usize,
    pub structs: usize,
    pub delete_clients: usize,
    pub delete_ranges: usize,
}

fn checked_usize_from_u64(v: u64) -> Result<usize, CodecError> {
    if v > (usize::MAX as u64) {
        Err(CodecError::LimitExceeded)
    } else {
        Ok(v as usize)
    }
}

fn check_fits(remaining: usize, count: usize, min_bytes: u64) -> Result<(), CodecError> {
    let available = (remaining as u64) / min_bytes;
    if (count as u64) > available {
        Err(CodecError::UnexpectedEof)
    } else {
        Ok(())
    }
}

fn checked_add_usize(a: usize, b: usize) -> Result<usize, CodecError> {
    if b > usize::MAX - a {
        Err(CodecError::LimitExceeded)
    } else {
        Ok(a + b)
    }
}

fn read_u8_at(input: &[u8], pos: usize) -> Result<(u8, usize), CodecError> {
    if pos >= input.len() {
        return Err(CodecError::UnexpectedEof);
    }
    Ok((input[pos], pos + 1))
}

fn read_var_u64_at(input: &[u8], pos: usize) -> Result<(u64, usize), CodecError> {
    if pos > input.len() {
        return Err(CodecError::UnexpectedEof);
    }
    let (val, used) = decode_var_u64(&input[pos..])?;
    if used > input.len() - pos {
        return Err(CodecError::UnexpectedEof);
    }
    Ok((val, pos + used))
}

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

fn read_bytes_slice_at(input: &[u8], pos: usize) -> Result<(usize, usize), CodecError> {
    let (len_u64, next) = read_var_u64_at(input, pos)?;
    let len = checked_usize_from_u64(len_u64)?;
    if len > input.len() - next {
        return Err(CodecError::UnexpectedEof);
    }
    Ok((next, next + len))
}

fn read_str_slice_at(input: &[u8], pos: usize) -> Result<(usize, usize), CodecError> {
    let (start, end) = read_bytes_slice_at(input, pos)?;
    if !is_valid_utf8(&input[start..end]) {
        return Err(CodecError::InvalidUtf8);
    }
    Ok((start, end))
}

fn skip_fixed_at(input: &[u8], pos: usize, width: usize) -> Result<usize, CodecError> {
    if pos > input.len() || input.len() - pos < width {
        return Err(CodecError::UnexpectedEof);
    }
    Ok(pos + width)
}

fn advance_clock(clock: u64, len: u64) -> Result<u64, CodecError> {
    if len == 0 {
        return Err(CodecError::ZeroLengthStruct);
    }
    if len > u64::MAX - clock {
        return Err(CodecError::ClockOverflow);
    }
    Ok(clock + len)
}

fn contains_u64(items: &[u64], target: u64) -> bool {
    let mut i = 0usize;
    while i < items.len() {
        if items[i] == target {
            return true;
        }
        i += 1;
    }
    false
}

fn read_sv_entry(input: &[u8], cur: usize) -> Result<(u64, u64, usize), CodecError> {
    let (client, p1) = read_var_u64_at(input, cur)?;
    let (clock, p2) = read_var_u64_at(input, p1)?;
    Ok((client, clock, p2))
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

fn read_one_delete_range(input: &[u8], cur: usize) -> Result<(u64, u64, usize), CodecError> {
    let (start, q1) = read_var_u64_at(input, cur)?;
    let (len, q2) = read_var_u64_at(input, q1)?;
    if len > u64::MAX - start {
        return Err(CodecError::ClockOverflow);
    }
    Ok((start, start + len, q2))
}

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
                if start != end {
                    ds.insert(client, start, end);
                }
                cur = q2;
                r_idx += 1;
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(cur) }
}

fn read_delete_client_header(
    input: &[u8],
    cur: usize,
    limits: &DecodeLimitsCore,
    total_entries: usize,
) -> Result<(u64, usize, usize, usize), CodecError> {
    let (client, p1) = read_var_u64_at(input, cur)?;
    let (ranges_u64, p2) = read_var_u64_at(input, p1)?;
    let range_count = checked_usize_from_u64(ranges_u64)?;
    let next_entries = checked_add_usize(total_entries, range_count)?;
    if next_entries > limits.max_collection_entries {
        return Err(CodecError::LimitExceeded);
    }
    check_fits(input.len() - p2, range_count, MIN_DELETE_RANGE_BYTES)?;
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
    let delete_clients = checked_usize_from_u64(clients_u64)?;
    if delete_clients > limits.max_clients {
        return Err(CodecError::LimitExceeded);
    }
    check_fits(input.len() - cur, delete_clients, MIN_DELETE_CLIENT_BYTES)?;

    let mut ds = DeleteSetCore::new();
    let mut total_entries = entries_acc;
    let mut total_ranges = 0usize;
    let mut c_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while c_idx < delete_clients && err.is_none() {
        match read_delete_client_header(input, cur, limits, total_entries) {
            Err(e) => err = Some(e),
            Ok((client, range_count, next_entries, p2)) => {
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
        }
    }
    if let Some(e) = err {
        Err(e)
    } else {
        Ok((ds, total_ranges, delete_clients, cur))
    }
}

fn pop_open_stack(open: &[(usize, bool)]) -> Vec<(usize, bool)> {
    let mut next_open = Vec::new();
    let mut k = 0usize;
    let target = open.len() - 1;
    while k < target {
        next_open.push(open[k]);
        k += 1;
    }
    next_open
}

fn skip_any_atom(
    input: &[u8],
    pos: usize,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
    open: &mut Vec<(usize, bool)>,
) -> Result<(usize, usize, bool), CodecError> {
    if open.len() > limits.max_any_depth {
        return Err(CodecError::LimitExceeded);
    }
    let (raw_tag, mut cur) = read_u8_at(input, pos)?;
    let tag = 127u8.wrapping_sub(raw_tag);
    let mut total_entries = entries_acc;
    if tag == 0 || tag == 1 || tag == 6 || tag == 7 {
        return Ok((cur, total_entries, open.is_empty()));
    } else if tag == 2 {
        let (_, p) = read_var_i32_with_sign_at(input, cur)?;
        cur = p;
        return Ok((cur, total_entries, open.is_empty()));
    } else if tag == 3 {
        cur = skip_fixed_at(input, cur, 4)?;
        return Ok((cur, total_entries, open.is_empty()));
    } else if tag == 4 || tag == 5 {
        cur = skip_fixed_at(input, cur, 8)?;
        return Ok((cur, total_entries, open.is_empty()));
    } else if tag == 8 {
        let (_, end_s) = read_str_slice_at(input, cur)?;
        return Ok((end_s, total_entries, open.is_empty()));
    } else if tag == 9 || tag == 10 {
        let is_obj = tag == 9;
        let min_bytes = if is_obj {
            MIN_OBJECT_ENTRY_BYTES
        } else {
            MIN_ENTRY_BYTES
        };
        let (cnt_u64, p) = read_var_u64_at(input, cur)?;
        cur = p;
        let count = checked_usize_from_u64(cnt_u64)?;
        total_entries = checked_add_usize(total_entries, count)?;
        if total_entries > limits.max_collection_entries {
            return Err(CodecError::LimitExceeded);
        }
        check_fits(input.len() - cur, count, min_bytes)?;
        open.push((count, is_obj));
        return Ok((cur, total_entries, false));
    } else if tag == 11 {
        let (_, end_b) = read_bytes_slice_at(input, cur)?;
        return Ok((end_b, total_entries, open.is_empty()));
    }
    Err(CodecError::UnknownAnyTag)
}

fn skip_any_step(
    input: &[u8],
    cur: usize,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
    open: &mut Vec<(usize, bool)>,
) -> Result<(usize, usize, bool), CodecError> {
    let open_len = open.len();
    if open_len > 0 {
        let top = open[open_len - 1];
        if top.0 == 0 {
            *open = pop_open_stack(open);
            return Ok((cur, entries_acc, open.is_empty()));
        }
        open[open_len - 1].0 = top.0 - 1;
        let next_cur = if top.1 {
            let (_, end_k) = read_str_slice_at(input, cur)?;
            end_k
        } else {
            cur
        };
        return skip_any_atom(input, next_cur, limits, entries_acc, open);
    }
    skip_any_atom(input, cur, limits, entries_acc, open)
}

fn skip_any_v1(
    input: &[u8],
    start_pos: usize,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
) -> Result<(usize, usize), CodecError> {
    let mut cur = start_pos;
    let mut total_entries = entries_acc;
    let mut open: Vec<(usize, bool)> = Vec::new();
    let rem = if input.len() >= start_pos {
        input.len() - start_pos
    } else {
        0
    };
    let rem2 = if rem <= usize::MAX / 2 { rem * 2 } else { usize::MAX };
    let rem_d = if limits.max_any_depth <= usize::MAX - rem2 {
        rem2 + limits.max_any_depth
    } else {
        usize::MAX
    };
    let max_steps = if 2 <= usize::MAX - rem_d { rem_d + 2 } else { usize::MAX };

    let mut step = 0usize;
    let mut done = false;
    let mut err: Option<CodecError> = None;
    while step < max_steps && !done && err.is_none() {
        step += 1;
        match skip_any_step(input, cur, limits, total_entries, &mut open) {
            Err(e) => err = Some(e),
            Ok((next_c, next_e, is_done)) => {
                cur = next_c;
                total_entries = next_e;
                done = is_done;
            }
        }
    }
    if let Some(e) = err {
        Err(e)
    } else if !done {
        Err(CodecError::LimitExceeded)
    } else {
        Ok((cur, total_entries))
    }
}

fn skip_id_at(input: &[u8], pos: usize) -> Result<usize, CodecError> {
    let (_, p1) = read_var_u64_at(input, pos)?;
    let (_, p2) = read_var_u64_at(input, p1)?;
    Ok(p2)
}

fn read_json_entries(input: &[u8], start_pos: usize, count: usize) -> Result<usize, CodecError> {
    let mut cur = start_pos;
    let mut i = 0usize;
    let mut err: Option<CodecError> = None;
    while i < count && err.is_none() {
        match read_str_slice_at(input, cur) {
            Err(e) => err = Some(e),
            Ok((_, end_j)) => {
                cur = end_j;
                i += 1;
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok(cur) }
}

fn read_any_entries(
    input: &[u8],
    start_pos: usize,
    count: usize,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
) -> Result<(usize, usize), CodecError> {
    let mut cur = start_pos;
    let mut entries = entries_acc;
    let mut i = 0usize;
    let mut err: Option<CodecError> = None;
    while i < count && err.is_none() {
        match skip_any_v1(input, cur, limits, entries) {
            Err(e) => err = Some(e),
            Ok((next_c, next_e)) => {
                cur = next_c;
                entries = next_e;
                i += 1;
            }
        }
    }
    if let Some(e) = err { Err(e) } else { Ok((cur, entries)) }
}

fn skip_item_header(input: &[u8], start_pos: usize, info: u8) -> Result<usize, CodecError> {
    let mut cur = start_pos;
    let has_left = (info & ITEM_HAS_LEFT_ID) != 0;
    let has_right = (info & ITEM_HAS_RIGHT_ID) != 0;
    let explicit_parent = (info & (ITEM_HAS_LEFT_ID | ITEM_HAS_RIGHT_ID)) == 0;
    if has_left {
        cur = skip_id_at(input, cur)?;
    }
    if has_right {
        cur = skip_id_at(input, cur)?;
    }
    if explicit_parent {
        let (p_kind, p1) = read_var_u64_at(input, cur)?;
        if p_kind == 1 {
            let (_, end_s) = read_str_slice_at(input, p1)?;
            cur = end_s;
        } else {
            cur = skip_id_at(input, p1)?;
        }
        if (info & ITEM_HAS_PARENT_SUB) != 0 {
            let (_, end_sub) = read_str_slice_at(input, cur)?;
            cur = end_sub;
        }
    }
    Ok(cur)
}

fn skip_item_content(
    input: &[u8],
    cur: usize,
    tag: u8,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
) -> Result<(u64, usize, usize), CodecError> {
    if tag == 1 {
        let (len, p) = read_var_u64_at(input, cur)?;
        return Ok((len, p, entries_acc));
    }
    if tag == 2 {
        let (len, p) = read_var_u64_at(input, cur)?;
        let count = checked_usize_from_u64(len)?;
        let entries = checked_add_usize(entries_acc, count)?;
        if entries > limits.max_collection_entries {
            return Err(CodecError::LimitExceeded);
        }
        check_fits(input.len() - p, count, MIN_ENTRY_BYTES)?;
        let end = read_json_entries(input, p, count)?;
        return Ok((len, end, entries));
    }
    if tag == 3 {
        let (_, end_b) = read_bytes_slice_at(input, cur)?;
        return Ok((1, end_b, entries_acc));
    }
    if tag == 4 {
        let (s, e) = read_str_slice_at(input, cur)?;
        let len = utf16_len(&input[s..e]) as u64;
        return Ok((len, e, entries_acc));
    }
    if tag == 5 {
        let (_, e) = read_str_slice_at(input, cur)?;
        return Ok((1, e, entries_acc));
    }
    if tag == 6 {
        let (_, e1) = read_str_slice_at(input, cur)?;
        let (_, e2) = read_str_slice_at(input, e1)?;
        return Ok((1, e2, entries_acc));
    }
    if tag == 7 {
        let (kind, p) = read_var_u64_at(input, cur)?;
        if kind > 6 {
            return Err(CodecError::UnknownTypeKind);
        }
        if kind == 3 || kind == 5 {
            let (_, e) = read_str_slice_at(input, p)?;
            return Ok((1, e, entries_acc));
        }
        return Ok((1, p, entries_acc));
    }
    if tag == 8 {
        let (len, p) = read_var_u64_at(input, cur)?;
        let count = checked_usize_from_u64(len)?;
        let entries = checked_add_usize(entries_acc, count)?;
        if entries > limits.max_collection_entries {
            return Err(CodecError::LimitExceeded);
        }
        check_fits(input.len() - p, count, MIN_ENTRY_BYTES)?;
        let (next_c, next_e) = read_any_entries(input, p, count, limits, entries)?;
        return Ok((len, next_c, next_e));
    }
    if tag == 9 {
        let (_, e) = read_str_slice_at(input, cur)?;
        let (next_c, next_e) = skip_any_v1(input, e, limits, entries_acc)?;
        return Ok((1, next_c, next_e));
    }
    Err(CodecError::UnknownContentTag)
}

fn read_struct_frame(
    input: &[u8],
    pos: usize,
    clock: u64,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
    content_bytes_acc: usize,
) -> Result<(u64, usize, usize, usize), CodecError> {
    let (info, cur) = read_u8_at(input, pos)?;
    let tag = info & 0b1_1111;
    if tag == 0 || tag == 10 {
        let (len, p) = read_var_u64_at(input, cur)?;
        let next_clock = advance_clock(clock, len)?;
        return Ok((next_clock, p, entries_acc, content_bytes_acc));
    }

    let content_start = skip_item_header(input, cur, info)?;
    let (len, content_end, entries) = skip_item_content(input, content_start, tag, limits, entries_acc)?;
    let delta = if content_end >= content_start {
        content_end - content_start
    } else {
        0
    };
    let content_bytes = checked_add_usize(content_bytes_acc, delta)?;
    if content_bytes > limits.max_content_bytes {
        return Err(CodecError::LimitExceeded);
    }
    let next_clock = advance_clock(clock, len)?;
    Ok((next_clock, content_end, entries, content_bytes))
}

fn read_client_structs(
    input: &[u8],
    start_pos: usize,
    start_clock: u64,
    count: usize,
    limits: &DecodeLimitsCore,
    entries_acc: usize,
    content_bytes_acc: usize,
) -> Result<(usize, usize, usize), CodecError> {
    let mut cur = start_pos;
    let mut clock = start_clock;
    let mut entries = entries_acc;
    let mut content_bytes = content_bytes_acc;
    let mut s_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while s_idx < count && err.is_none() {
        match read_struct_frame(input, cur, clock, limits, entries, content_bytes) {
            Err(e) => err = Some(e),
            Ok((next_clock, next_cur, next_entries, next_bytes)) => {
                clock = next_clock;
                cur = next_cur;
                entries = next_entries;
                content_bytes = next_bytes;
                s_idx += 1;
            }
        }
    }
    if let Some(e) = err {
        Err(e)
    } else {
        Ok((cur, entries, content_bytes))
    }
}

fn decode_one_client_block(
    input: &[u8],
    cur: usize,
    limits: &DecodeLimitsCore,
    seen_clients: &mut Vec<u64>,
    total_structs: usize,
    total_entries: usize,
    total_content_bytes: usize,
) -> Result<(usize, usize, usize, usize), CodecError> {
    let (count_u64, p1) = read_var_u64_at(input, cur)?;
    let count = checked_usize_from_u64(count_u64)?;
    let next_structs = checked_add_usize(total_structs, count)?;
    if next_structs > limits.max_structs {
        return Err(CodecError::LimitExceeded);
    }
    let next_entries_hdr = checked_add_usize(total_entries, count)?;
    if next_entries_hdr > limits.max_collection_entries {
        return Err(CodecError::LimitExceeded);
    }
    check_fits(input.len() - p1, count, MIN_STRUCT_BYTES)?;

    let (client, p2) = read_var_u64_at(input, p1)?;
    if contains_u64(seen_clients, client) {
        return Err(CodecError::DuplicateClient);
    }
    seen_clients.push(client);
    let (clock, p3) = read_var_u64_at(input, p2)?;
    let (next_cur, next_entries, next_bytes) =
        read_client_structs(input, p3, clock, count, limits, next_entries_hdr, total_content_bytes)?;
    Ok((next_cur, next_structs, next_entries, next_bytes))
}

/// Validates and summarizes a complete Yjs V1 Update frame with bounded loops
/// and checked `u64 -> usize` conversions. Never panics on arbitrary `&[u8]`.
///
/// M1 scope boundary: validates V1 frame structure, checked bounds/limits, and
/// RFC 3629 UTF-8 validity for all string payloads, including `Embed` (tag 5)
/// and `Format` (tag 6) strings, **without** parsing their inner JSON syntax
/// (JSON syntax validation remains in `y-octo`).
pub fn decode_update_v1_frame(input: &[u8], limits: &DecodeLimitsCore) -> Result<UpdateSummary, CodecError> {
    let (clients_u64, mut cur) = read_var_u64_at(input, 0)?;
    let clients = checked_usize_from_u64(clients_u64)?;
    if clients > limits.max_clients {
        return Err(CodecError::LimitExceeded);
    }
    check_fits(input.len() - cur, clients, MIN_CLIENT_BYTES)?;

    let mut seen_clients: Vec<u64> = Vec::new();
    let mut total_structs = 0usize;
    let mut total_entries = 0usize;
    let mut total_content_bytes = 0usize;

    let mut c_idx = 0usize;
    let mut err: Option<CodecError> = None;
    while c_idx < clients && err.is_none() {
        match decode_one_client_block(
            input,
            cur,
            limits,
            &mut seen_clients,
            total_structs,
            total_entries,
            total_content_bytes,
        ) {
            Err(e) => err = Some(e),
            Ok((next_cur, next_structs, next_entries, next_bytes)) => {
                cur = next_cur;
                total_structs = next_structs;
                total_entries = next_entries;
                total_content_bytes = next_bytes;
                c_idx += 1;
            }
        }
    }
    if let Some(e) = err {
        return Err(e);
    }

    let (_, delete_ranges, delete_clients, end_pos) = read_delete_set_v1(input, cur, limits, total_entries)?;
    if end_pos != input.len() {
        return Err(CodecError::TrailingBytes);
    }

    Ok(UpdateSummary {
        clients,
        structs: total_structs,
        delete_clients,
        delete_ranges,
    })
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
