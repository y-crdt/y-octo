//! Zero-import `wasm32-unknown-unknown` Scheme C binary binding for `y-octo`:
//! 4-byte aligned little-endian binary tape + reusable scratch buffers with
//! high-water auto-trim + high-frequency direct scalar C-ABI hot paths.
//!
//! No `serde`, no `serde_json`, and no JS host imports are required.

#![allow(clippy::not_unsafe_ptr_arg_deref)]

use std::{cell::RefCell, collections::BTreeMap};

use ordered_float::OrderedFloat;
use smol_str::SmolStr;
use y_octo::{
    AHashMap, AbsolutePosition, Any, Awareness, AwarenessEvent, DocOptions, DocSession, HashMapExt, Id, JwstCodecError,
    JwstCodecResult, PathSegment, RelativePosition, SessionChangedType, SessionCommit, SessionConfig,
    SessionOriginKind, SessionReadValue, SessionTxOrigin, SessionUndoConfig, SessionValue, TextAttributes, TextDeltaOp,
    TextInsert, TypeIdentity, TypePath, TypeStatus, TypeTarget, UndoStack, UndoStackId, YTypeKind, diff_update_v1,
    encode_state_vector_from_update_v1, merge_updates_v1, revert_update_v1, validate_update_v1,
};

const INITIAL_SCRATCH: usize = 64 * 1024;
const TRIM_TARGET: usize = 256 * 1024;
const HIGH_WATER: usize = 4 * 1024 * 1024;
const MAX_PREALLOC: usize = 16_384;
const WASM_ABI_VERSION: u32 = 1;

#[unsafe(no_mangle)]
pub extern "C" fn wasm_abi_version() -> u32 {
    WASM_ABI_VERSION
}

struct WasmRuntime {
    sessions: Vec<Option<DocSession<Vec<u8>>>>,
    awarenesses: Vec<Option<Awareness>>,
    in_buf: Vec<u8>,
    out_buf: Vec<u8>,
    error: String,
}

impl Default for WasmRuntime {
    fn default() -> Self {
        Self {
            sessions: Vec::new(),
            awarenesses: Vec::new(),
            in_buf: vec![0u8; INITIAL_SCRATCH],
            out_buf: Vec::with_capacity(INITIAL_SCRATCH),
            error: String::new(),
        }
    }
}

impl WasmRuntime {
    fn trim_out_if_high_water(&mut self) {
        self.out_buf.clear();
        if self.out_buf.capacity() > HIGH_WATER {
            self.out_buf.shrink_to(TRIM_TARGET);
        }
    }

    fn trim_scratch(&mut self) {
        if self.in_buf.len() > TRIM_TARGET {
            self.in_buf.truncate(TRIM_TARGET);
        }
        if self.in_buf.capacity() > TRIM_TARGET {
            self.in_buf.shrink_to(TRIM_TARGET);
        }
        self.out_buf.clear();
        if self.out_buf.capacity() > TRIM_TARGET {
            self.out_buf.shrink_to(TRIM_TARGET);
        }
    }
}

thread_local! {
    static RUNTIME: RefCell<WasmRuntime> = RefCell::new(WasmRuntime::default());
}

fn set_error(msg: impl Into<String>) -> u32 {
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        rt.trim_out_if_high_water();
        rt.error = msg.into();
    });
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn in_buf_ensure(min_cap: usize) -> *mut u8 {
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        if min_cap <= TRIM_TARGET && rt.in_buf.capacity() > HIGH_WATER {
            rt.in_buf.truncate(TRIM_TARGET);
            rt.in_buf.shrink_to(TRIM_TARGET);
        }
        if rt.in_buf.len() < min_cap {
            let new_len = min_cap
                .checked_next_power_of_two()
                .unwrap_or(min_cap)
                .max(INITIAL_SCRATCH);
            rt.in_buf.resize(new_len, 0);
        }
        rt.in_buf.as_mut_ptr()
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn runtime_trim_scratch() {
    RUNTIME.with(|rt| rt.borrow_mut().trim_scratch());
}

#[unsafe(no_mangle)]
pub extern "C" fn out_buf_ptr() -> *const u8 {
    RUNTIME.with(|rt| rt.borrow().out_buf.as_ptr())
}

#[unsafe(no_mangle)]
pub extern "C" fn out_buf_len() -> usize {
    RUNTIME.with(|rt| rt.borrow().out_buf.len())
}

#[unsafe(no_mangle)]
pub extern "C" fn error_ptr() -> *const u8 {
    RUNTIME.with(|rt| rt.borrow().error.as_ptr())
}

#[unsafe(no_mangle)]
pub extern "C" fn error_len() -> usize {
    RUNTIME.with(|rt| rt.borrow().error.len())
}

// ---------------------------------------------------------------------------
// 4-byte aligned little-endian binary tape reader & writer (overflow & OOM
// safe)

struct TapeReader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> TapeReader<'a> {
    #[inline]
    fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    #[inline]
    fn remaining(&self) -> usize {
        self.buf.len().saturating_sub(self.pos)
    }

    #[inline]
    fn safe_cap(&self, count: usize) -> usize {
        count.min(self.remaining() / 4).min(MAX_PREALLOC)
    }

    #[inline]
    fn read_u32(&mut self) -> JwstCodecResult<u32> {
        let end = self.pos.checked_add(4).ok_or(JwstCodecError::Unexpected)?;
        let slice = self
            .buf
            .get(self.pos..end)
            .ok_or_else(|| JwstCodecError::IncompleteDocument("tape eof u32".into()))?;
        self.pos = end;
        Ok(u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]))
    }

    #[inline]
    fn read_i32(&mut self) -> JwstCodecResult<i32> {
        Ok(self.read_u32()? as i32)
    }

    #[inline]
    fn read_f32(&mut self) -> JwstCodecResult<f32> {
        Ok(f32::from_bits(self.read_u32()?))
    }

    #[inline]
    fn read_u64(&mut self) -> JwstCodecResult<u64> {
        let end = self.pos.checked_add(8).ok_or(JwstCodecError::Unexpected)?;
        let slice = self
            .buf
            .get(self.pos..end)
            .ok_or_else(|| JwstCodecError::IncompleteDocument("tape eof u64".into()))?;
        self.pos = end;
        Ok(u64::from_le_bytes([
            slice[0], slice[1], slice[2], slice[3], slice[4], slice[5], slice[6], slice[7],
        ]))
    }

    #[inline]
    fn read_i64(&mut self) -> JwstCodecResult<i64> {
        Ok(self.read_u64()? as i64)
    }

    #[inline]
    fn read_f64(&mut self) -> JwstCodecResult<f64> {
        Ok(f64::from_bits(self.read_u64()?))
    }

    #[inline]
    fn read_bytes(&mut self) -> JwstCodecResult<&'a [u8]> {
        let len = usize::try_from(self.read_u32()?)
            .map_err(|_| JwstCodecError::IncompleteDocument("tape len overflow".into()))?;
        let padded = len
            .checked_add(3)
            .ok_or_else(|| JwstCodecError::IncompleteDocument("tape len overflow".into()))?
            & !3;
        let end = self
            .pos
            .checked_add(padded)
            .ok_or_else(|| JwstCodecError::IncompleteDocument("tape pos overflow".into()))?;
        if end > self.buf.len() {
            return Err(JwstCodecError::IncompleteDocument("tape eof bytes".into()));
        }
        let slice = &self.buf[self.pos..self.pos + len];
        self.pos = end;
        Ok(slice)
    }

    #[inline]
    fn read_str(&mut self) -> JwstCodecResult<&'a str> {
        let bytes = self.read_bytes()?;
        std::str::from_utf8(bytes).map_err(|_| JwstCodecError::IncompleteDocument("invalid utf8".into()))
    }
}

struct TapeWriter<'a> {
    buf: &'a mut Vec<u8>,
}

impl<'a> TapeWriter<'a> {
    #[inline]
    fn new(buf: &'a mut Vec<u8>) -> Self {
        buf.clear();
        if buf.capacity() > HIGH_WATER {
            buf.shrink_to(TRIM_TARGET);
        }
        Self { buf }
    }

    #[inline]
    fn write_u32(&mut self, v: u32) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn write_i32(&mut self, v: i32) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn write_f32(&mut self, v: f32) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn write_u64(&mut self, v: u64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn write_i64(&mut self, v: i64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn write_f64(&mut self, v: f64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn write_bytes(&mut self, b: &[u8]) {
        self.write_u32(b.len() as u32);
        self.buf.extend_from_slice(b);
        let pad = (4 - (b.len() & 3)) & 3;
        if pad != 0 {
            static ZEROS: [u8; 3] = [0; 3];
            self.buf.extend_from_slice(&ZEROS[..pad]);
        }
    }

    #[inline]
    fn write_str(&mut self, s: &str) {
        self.write_bytes(s.as_bytes());
    }
}

// ---------------------------------------------------------------------------
// Domain encoders / decoders on 4B-aligned LE tape

fn decode_any(r: &mut TapeReader<'_>, depth: usize) -> JwstCodecResult<Any> {
    if depth > Any::DEFAULT_MAX_DEPTH {
        return Err(JwstCodecError::IncompleteDocument(
            "tape Any nesting exceeds max depth".into(),
        ));
    }
    match r.read_u32()? {
        0 => Ok(Any::Undefined),
        1 => Ok(Any::Null),
        2 => Ok(Any::False),
        3 => Ok(Any::True),
        4 => Ok(Any::Integer(r.read_i32()?)),
        5 => Ok(Any::Float32(OrderedFloat(r.read_f32()?))),
        6 => Ok(Any::Float64(OrderedFloat(r.read_f64()?))),
        7 => Ok(Any::BigInt64(r.read_i64()?)),
        8 => Ok(Any::String(r.read_str()?.to_string())),
        9 => Ok(Any::Binary(r.read_bytes()?.to_vec())),
        10 => {
            let count = r.read_u32()? as usize;
            let mut out = Vec::with_capacity(r.safe_cap(count));
            for _ in 0..count {
                out.push(decode_any(r, depth + 1)?);
            }
            Ok(Any::Array(out))
        }
        11 => {
            let count = r.read_u32()? as usize;
            let mut map = AHashMap::with_capacity(r.safe_cap(count));
            for _ in 0..count {
                let k = r.read_str()?.to_string();
                let v = decode_any(r, depth + 1)?;
                map.insert(k, v);
            }
            Ok(Any::Object(Box::new(map)))
        }
        _ => Err(JwstCodecError::IncompleteDocument("bad Any tag".into())),
    }
}

fn encode_any(w: &mut TapeWriter<'_>, any: &Any) {
    match any {
        Any::Undefined => w.write_u32(0),
        Any::Null => w.write_u32(1),
        Any::False => w.write_u32(2),
        Any::True => w.write_u32(3),
        Any::Integer(v) => {
            w.write_u32(4);
            w.write_i32(*v);
        }
        Any::Float32(v) => {
            w.write_u32(5);
            w.write_f32(v.into_inner());
        }
        Any::Float64(v) => {
            w.write_u32(6);
            w.write_f64(v.into_inner());
        }
        Any::BigInt64(v) => {
            w.write_u32(7);
            w.write_i64(*v);
        }
        Any::String(s) => {
            w.write_u32(8);
            w.write_str(s);
        }
        Any::Binary(b) => {
            w.write_u32(9);
            w.write_bytes(b);
        }
        Any::Array(arr) => {
            w.write_u32(10);
            w.write_u32(arr.len() as u32);
            for item in arr {
                encode_any(w, item);
            }
        }
        Any::Object(map) => {
            w.write_u32(11);
            w.write_u32(map.len() as u32);
            for (k, v) in map.iter() {
                w.write_str(k);
                encode_any(w, v);
            }
        }
    }
}

fn decode_tx_origin(r: &mut TapeReader<'_>) -> JwstCodecResult<SessionTxOrigin> {
    match r.read_u32()? {
        0 => Ok(SessionTxOrigin::Tracked),
        1 => Ok(SessionTxOrigin::Untracked),
        2 => Ok(SessionTxOrigin::Named(SmolStr::new(r.read_str()?))),
        _ => Err(JwstCodecError::IncompleteDocument("bad SessionTxOrigin tag".into())),
    }
}

fn decode_identity(r: &mut TapeReader<'_>) -> JwstCodecResult<TypeIdentity> {
    match r.read_u32()? {
        0 => Ok(TypeIdentity::Root(r.read_str()?.to_string())),
        1 => {
            let client = r.read_u64()?;
            let clock = r.read_u64()?;
            Ok(TypeIdentity::Item(Id::new(client, clock)))
        }
        _ => Err(JwstCodecError::IncompleteDocument("bad TypeIdentity tag".into())),
    }
}

fn encode_identity(w: &mut TapeWriter<'_>, id: &TypeIdentity) {
    match id {
        TypeIdentity::Root(name) => {
            w.write_u32(0);
            w.write_str(name);
        }
        TypeIdentity::Item(id) => {
            w.write_u32(1);
            w.write_u64(id.client);
            w.write_u64(id.clock);
        }
    }
}

fn decode_path(r: &mut TapeReader<'_>) -> JwstCodecResult<TypePath> {
    let root = r.read_str()?.to_string();
    let count = r.read_u32()? as usize;
    let mut segments = Vec::with_capacity(r.safe_cap(count));
    for _ in 0..count {
        match r.read_u32()? {
            0 => segments.push(PathSegment::Key(r.read_str()?.to_string())),
            1 => segments.push(PathSegment::Index(r.read_u64()?)),
            _ => return Err(JwstCodecError::IncompleteDocument("bad PathSegment tag".into())),
        }
    }
    Ok(TypePath { root, segments })
}

fn encode_path(w: &mut TapeWriter<'_>, path: &TypePath) {
    w.write_str(&path.root);
    w.write_u32(path.segments.len() as u32);
    for seg in &path.segments {
        match seg {
            PathSegment::Key(k) => {
                w.write_u32(0);
                w.write_str(k);
            }
            PathSegment::Index(idx) => {
                w.write_u32(1);
                w.write_u64(*idx);
            }
        }
    }
}

fn decode_target(r: &mut TapeReader<'_>) -> JwstCodecResult<TypeTarget> {
    match r.read_u32()? {
        0 => Ok(TypeTarget::Identity(decode_identity(r)?)),
        1 => Ok(TypeTarget::Path(decode_path(r)?)),
        _ => Err(JwstCodecError::IncompleteDocument("bad TypeTarget tag".into())),
    }
}

fn encode_type_kind(kind: YTypeKind) -> u32 {
    match kind {
        YTypeKind::Array => 0,
        YTypeKind::Map => 1,
        YTypeKind::Text => 2,
        YTypeKind::XMLElement => 3,
        YTypeKind::XMLFragment => 4,
        YTypeKind::XMLHook => 5,
        YTypeKind::XMLText => 6,
        YTypeKind::Unknown => 7,
    }
}

fn encode_type_status(w: &mut TapeWriter<'_>, status: &TypeStatus) {
    w.write_u32(u32::from(status.alive));
    match status.kind {
        None => w.write_u32(0),
        Some(k) => {
            w.write_u32(1);
            w.write_u32(encode_type_kind(k));
        }
    }
    match &status.path {
        None => w.write_u32(0),
        Some(p) => {
            w.write_u32(1);
            encode_path(w, p);
        }
    }
}

fn decode_format(r: &mut TapeReader<'_>, depth: usize) -> JwstCodecResult<Option<TextAttributes>> {
    if depth > Any::DEFAULT_MAX_DEPTH {
        return Err(JwstCodecError::IncompleteDocument(
            "tape format nesting exceeds max depth".into(),
        ));
    }
    let count = r.read_u32()? as usize;
    if count == 0 {
        return Ok(None);
    }
    let mut map = BTreeMap::new();
    for _ in 0..count {
        let k = r.read_str()?.to_string();
        let v = decode_any(r, depth + 1)?;
        map.insert(k, v);
    }
    Ok(Some(map))
}

fn encode_format(w: &mut TapeWriter<'_>, fmt: &Option<TextAttributes>) {
    match fmt {
        None => w.write_u32(0),
        Some(map) => {
            w.write_u32(map.len() as u32);
            for (k, v) in map {
                w.write_str(k);
                encode_any(w, v);
            }
        }
    }
}

fn decode_delta(r: &mut TapeReader<'_>, depth: usize) -> JwstCodecResult<Vec<TextDeltaOp>> {
    if depth > Any::DEFAULT_MAX_DEPTH {
        return Err(JwstCodecError::IncompleteDocument(
            "tape delta nesting exceeds max depth".into(),
        ));
    }
    let count = r.read_u32()? as usize;
    let mut ops = Vec::with_capacity(r.safe_cap(count));
    for _ in 0..count {
        match r.read_u32()? {
            0 => {
                let s = r.read_str()?.to_string();
                let format = decode_format(r, depth + 1)?;
                ops.push(TextDeltaOp::Insert {
                    insert: TextInsert::Text(s),
                    format,
                });
            }
            1 => {
                let elen = r.read_u32()? as usize;
                let mut items = Vec::with_capacity(r.safe_cap(elen));
                for _ in 0..elen {
                    items.push(decode_any(r, depth + 1)?);
                }
                let format = decode_format(r, depth + 1)?;
                ops.push(TextDeltaOp::Insert {
                    insert: TextInsert::Embed(items),
                    format,
                });
            }
            2 => {
                let retain = r.read_u64()?;
                let format = decode_format(r, depth + 1)?;
                ops.push(TextDeltaOp::Retain { retain, format });
            }
            3 => {
                let delete = r.read_u64()?;
                ops.push(TextDeltaOp::Delete { delete });
            }
            _ => return Err(JwstCodecError::IncompleteDocument("bad TextDeltaOp tag".into())),
        }
    }
    Ok(ops)
}

fn encode_delta(w: &mut TapeWriter<'_>, ops: &[TextDeltaOp]) {
    w.write_u32(ops.len() as u32);
    for op in ops {
        match op {
            TextDeltaOp::Insert {
                insert: TextInsert::Text(s),
                format,
            } => {
                w.write_u32(0);
                w.write_str(s);
                encode_format(w, format);
            }
            TextDeltaOp::Insert {
                insert: TextInsert::Embed(items),
                format,
            } => {
                w.write_u32(1);
                w.write_u32(items.len() as u32);
                for item in items {
                    encode_any(w, item);
                }
                encode_format(w, format);
            }
            TextDeltaOp::Retain { retain, format } => {
                w.write_u32(2);
                w.write_u64(*retain);
                encode_format(w, format);
            }
            TextDeltaOp::Delete { delete } => {
                w.write_u32(3);
                w.write_u64(*delete);
            }
        }
    }
}

fn decode_session_value(r: &mut TapeReader<'_>, depth: usize) -> JwstCodecResult<SessionValue> {
    if depth > Any::DEFAULT_MAX_DEPTH {
        return Err(JwstCodecError::IncompleteDocument(
            "tape SessionValue nesting exceeds max depth".into(),
        ));
    }
    match r.read_u32()? {
        0 => Ok(SessionValue::Any(decode_any(r, depth + 1)?)),
        1 => {
            let count = r.read_u32()? as usize;
            let mut entries = Vec::with_capacity(r.safe_cap(count));
            for _ in 0..count {
                let k = r.read_str()?.to_string();
                let v = decode_session_value(r, depth + 1)?;
                entries.push((k, v));
            }
            Ok(SessionValue::Map(entries))
        }
        2 => {
            let count = r.read_u32()? as usize;
            let mut items = Vec::with_capacity(r.safe_cap(count));
            for _ in 0..count {
                items.push(decode_session_value(r, depth + 1)?);
            }
            Ok(SessionValue::Array(items))
        }
        3 => Ok(SessionValue::Text(decode_delta(r, depth + 1)?)),
        4 => {
            let guid = r.read_str()?.to_string();
            let gc = r.read_u32()? != 0;
            Ok(SessionValue::Doc { guid, gc })
        }
        5 => {
            let tag = r.read_str()?.to_string();
            let attr_count = r.read_u32()? as usize;
            let mut attrs = Vec::with_capacity(r.safe_cap(attr_count));
            for _ in 0..attr_count {
                let k = r.read_str()?.to_string();
                let v = decode_any(r, depth + 1)?;
                attrs.push((k, v));
            }
            let child_count = r.read_u32()? as usize;
            let mut children = Vec::with_capacity(r.safe_cap(child_count));
            for _ in 0..child_count {
                children.push(decode_session_value(r, depth + 1)?);
            }
            Ok(SessionValue::XmlElement { tag, attrs, children })
        }
        6 => {
            let count = r.read_u32()? as usize;
            let mut children = Vec::with_capacity(r.safe_cap(count));
            for _ in 0..count {
                children.push(decode_session_value(r, depth + 1)?);
            }
            Ok(SessionValue::XmlFragment(children))
        }
        7 => Ok(SessionValue::XmlText(decode_delta(r, depth + 1)?)),
        8 => {
            let name = r.read_str()?.to_string();
            let count = r.read_u32()? as usize;
            let mut entries = Vec::with_capacity(r.safe_cap(count));
            for _ in 0..count {
                let k = r.read_str()?.to_string();
                let v = decode_session_value(r, depth + 1)?;
                entries.push((k, v));
            }
            Ok(SessionValue::XmlHook { name, entries })
        }
        _ => Err(JwstCodecError::IncompleteDocument("bad SessionValue tag".into())),
    }
}

fn encode_read_value(w: &mut TapeWriter<'_>, v: &SessionReadValue) {
    match v {
        SessionReadValue::Any(any) => {
            w.write_u32(0);
            encode_any(w, any);
        }
        SessionReadValue::Map(id) => {
            w.write_u32(1);
            encode_identity(w, id);
        }
        SessionReadValue::Array(id) => {
            w.write_u32(2);
            encode_identity(w, id);
        }
        SessionReadValue::Text(id) => {
            w.write_u32(3);
            encode_identity(w, id);
        }
        SessionReadValue::Doc { guid, gc } => {
            w.write_u32(4);
            w.write_str(guid);
            w.write_u32(u32::from(*gc));
        }
        SessionReadValue::XmlElement { tag, identity } => {
            w.write_u32(5);
            w.write_str(tag);
            encode_identity(w, identity);
        }
        SessionReadValue::XmlFragment(id) => {
            w.write_u32(6);
            encode_identity(w, id);
        }
        SessionReadValue::XmlText(id) => {
            w.write_u32(7);
            encode_identity(w, id);
        }
        SessionReadValue::XmlHook { name, identity } => {
            w.write_u32(8);
            w.write_str(name);
            encode_identity(w, identity);
        }
    }
}

fn encode_changed_type(w: &mut TapeWriter<'_>, c: &SessionChangedType) {
    encode_identity(w, &c.identity);
    match &c.path {
        None => w.write_u32(0),
        Some(p) => {
            w.write_u32(1);
            encode_path(w, p);
        }
    }
    w.write_u32(c.keys.len() as u32);
    for k in &c.keys {
        w.write_str(k);
    }
}

fn encode_commit(w: &mut TapeWriter<'_>, c: &SessionCommit<Vec<u8>>) {
    w.write_u64(c.revision);
    let origin_tag: u32 = match &c.origin_kind {
        SessionOriginKind::LocalTransact => 0,
        SessionOriginKind::LocalUntracked => 1,
        SessionOriginKind::RemoteSync => 2,
        SessionOriginKind::Undo { .. } => 3,
        SessionOriginKind::Redo { .. } => 4,
        SessionOriginKind::LocalNamed(_) => 5,
        SessionOriginKind::FormattingCleanup => 6,
    };
    let flags: u32 = u32::from(c.is_local)
        | (u32::from(c.can_undo) << 1)
        | (u32::from(c.can_redo) << 2)
        | (origin_tag << 4)
        | (u32::from(c.selection_meta.is_some()) << 8);
    w.write_u32(flags);
    match &c.origin_kind {
        SessionOriginKind::Undo { stack_id } | SessionOriginKind::Redo { stack_id } => {
            w.write_u32(*stack_id);
        }
        SessionOriginKind::LocalNamed(name) => {
            w.write_str(name);
        }
        _ => {}
    }
    w.write_bytes(&c.update);
    w.write_u32(c.changed.len() as u32);
    for ch in &c.changed {
        encode_changed_type(w, ch);
    }
    w.write_u32(c.subdocs_added.len() as u32);
    for s in &c.subdocs_added {
        w.write_str(s);
    }
    w.write_u32(c.subdocs_removed.len() as u32);
    for s in &c.subdocs_removed {
        w.write_str(s);
    }
    if let Some(meta) = &c.selection_meta {
        w.write_bytes(meta);
    }
}

fn encode_opt_commit(w: &mut TapeWriter<'_>, opt: &Option<SessionCommit<Vec<u8>>>) {
    match opt {
        None => w.write_u32(0),
        Some(c) => {
            w.write_u32(1);
            encode_commit(w, c);
        }
    }
}

fn encode_abs_pos(w: &mut TapeWriter<'_>, pos: &AbsolutePosition) {
    encode_identity(w, &pos.r#type);
    w.write_u64(pos.index);
    w.write_i64(pos.assoc);
}

fn encode_awareness_event(w: &mut TapeWriter<'_>, ev: &AwarenessEvent) {
    let added = ev.added();
    w.write_u32(added.len() as u32);
    for id in added {
        w.write_u64(*id);
    }
    let updated = ev.updated();
    w.write_u32(updated.len() as u32);
    for id in updated {
        w.write_u64(*id);
    }
    let removed = ev.removed();
    w.write_u32(removed.len() as u32);
    for id in removed {
        w.write_u64(*id);
    }
}

// ---------------------------------------------------------------------------
// Stateless V1 wire operators (zero alloc/dealloc via scratch buffers)

#[unsafe(no_mangle)]
pub extern "C" fn wire_validate_update_v1(len: usize) -> u32 {
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        if len > rt.in_buf.len() {
            rt.trim_out_if_high_water();
            rt.error = "input len out of bounds".into();
            return 0;
        }
        match validate_update_v1(&rt.in_buf[..len]) {
            Ok(()) => {
                rt.trim_out_if_high_water();
                rt.error.clear();
                1
            }
            Err(err) => {
                rt.trim_out_if_high_water();
                rt.error = err.to_string();
                0
            }
        }
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn wire_encode_sv_from_update_v1(len: usize) -> u32 {
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        if len > rt.in_buf.len() {
            rt.trim_out_if_high_water();
            rt.error = "input len out of bounds".into();
            return 0;
        }
        match encode_state_vector_from_update_v1(&rt.in_buf[..len]) {
            Ok(sv) => {
                rt.trim_out_if_high_water();
                rt.out_buf.extend_from_slice(&sv);
                rt.error.clear();
                1
            }
            Err(err) => {
                rt.trim_out_if_high_water();
                rt.error = err.to_string();
                0
            }
        }
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn wire_diff_update_v1(update_len: usize, sv_len: usize) -> u32 {
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        let Some(total) = update_len.checked_add(sv_len) else {
            rt.trim_out_if_high_water();
            rt.error = "input len overflow".into();
            return 0;
        };
        if total > rt.in_buf.len() {
            rt.trim_out_if_high_water();
            rt.error = "input len out of bounds".into();
            return 0;
        }
        let res = diff_update_v1(&rt.in_buf[..update_len], &rt.in_buf[update_len..total]);
        match res {
            Ok(diff) => {
                rt.trim_out_if_high_water();
                rt.out_buf.extend_from_slice(&diff);
                rt.error.clear();
                1
            }
            Err(err) => {
                rt.trim_out_if_high_water();
                rt.error = err.to_string();
                0
            }
        }
    })
}

/// Merges length-prefixed (`u32` little-endian length followed by payload) V1
/// updates stored in `in_buf[..len]` into a single V1 update.
#[unsafe(no_mangle)]
pub extern "C" fn wire_merge_updates_v1(len: usize) -> u32 {
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        if len > rt.in_buf.len() {
            rt.trim_out_if_high_water();
            rt.error = "input len out of bounds".into();
            return 0;
        }
        let mut cursor = &rt.in_buf[..len];
        let mut updates: Vec<&[u8]> = Vec::new();
        while !cursor.is_empty() {
            if cursor.len() < 4 {
                rt.trim_out_if_high_water();
                rt.error = "truncated length prefix in wire_merge_updates_v1".into();
                return 0;
            }
            let item_len = u32::from_le_bytes([cursor[0], cursor[1], cursor[2], cursor[3]]) as usize;
            cursor = &cursor[4..];
            if cursor.len() < item_len {
                rt.trim_out_if_high_water();
                rt.error = "truncated update payload in wire_merge_updates_v1".into();
                return 0;
            }
            updates.push(&cursor[..item_len]);
            cursor = &cursor[item_len..];
        }
        let res = merge_updates_v1(&updates).and_then(|u| u.encode_v1());
        match res {
            Ok(merged) => {
                rt.trim_out_if_high_water();
                rt.out_buf.extend_from_slice(&merged);
                rt.error.clear();
                1
            }
            Err(err) => {
                rt.trim_out_if_high_water();
                rt.error = err.to_string();
                0
            }
        }
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn wire_revert_update_v1(cur_len: usize, tgt_len: usize) -> u32 {
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        let Some(total) = cur_len.checked_add(tgt_len) else {
            rt.trim_out_if_high_water();
            rt.error = "input len overflow".into();
            return 0;
        };
        if total > rt.in_buf.len() {
            rt.trim_out_if_high_water();
            rt.error = "input len out of bounds".into();
            return 0;
        }
        let res = revert_update_v1(&rt.in_buf[..cur_len], &rt.in_buf[cur_len..total]);
        match res {
            Ok(delta) => {
                rt.trim_out_if_high_water();
                rt.out_buf.extend_from_slice(&delta);
                rt.error.clear();
                1
            }
            Err(err) => {
                rt.trim_out_if_high_water();
                rt.error = err.to_string();
                0
            }
        }
    })
}

// ---------------------------------------------------------------------------
// Session lifecycle

/// Creates a new `DocSession`.
/// `undo_mode`: `0` = Global(`capture_timeout_ms`), `1` = Disabled, `2` =
/// Custom.
#[unsafe(no_mangle)]
pub extern "C" fn session_create(
    client_id: u64,
    guid_len: usize,
    gc: u32,
    undo_mode: u32,
    capture_timeout_ms: u64,
) -> u32 {
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        if guid_len > rt.in_buf.len() {
            rt.error = "guid_len out of bounds".into();
            return 0;
        }
        let Ok(guid) = std::str::from_utf8(&rt.in_buf[..guid_len]) else {
            rt.error = "guid must be valid UTF-8".into();
            return 0;
        };
        let undo = match undo_mode {
            0 => SessionUndoConfig::Global { capture_timeout_ms },
            1 => SessionUndoConfig::Disabled,
            2 => SessionUndoConfig::Custom,
            _ => {
                rt.error = format!("invalid undo_mode {undo_mode}");
                return 0;
            }
        };
        let opts = DocOptions::from_identity(client_id, guid.to_string()).auto_gc(gc != 0);
        let session = DocSession::<Vec<u8>>::with_config(opts, SessionConfig { undo });
        for (i, slot) in rt.sessions.iter_mut().enumerate() {
            if slot.is_none() {
                *slot = Some(session);
                return (i + 1) as u32;
            }
        }
        rt.sessions.push(Some(session));
        rt.sessions.len() as u32
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_free(handle: u32) {
    if handle == 0 {
        return;
    }
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        if let Some(slot) = rt.sessions.get_mut((handle - 1) as usize) {
            *slot = None;
        }
    });
}

// ---------------------------------------------------------------------------
// Direct Scalar C-ABI hot paths

fn reset_out_buf(out_buf: &mut Vec<u8>) {
    out_buf.clear();
    if out_buf.capacity() > HIGH_WATER {
        out_buf.shrink_to(TRIM_TARGET);
    }
}

fn with_session_mut(
    handle: u32,
    f: impl FnOnce(&mut DocSession<Vec<u8>>, &[u8], &mut Vec<u8>, &mut String) -> u32,
) -> u32 {
    if handle == 0 {
        return set_error("invalid session handle 0");
    }
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        let WasmRuntime {
            sessions,
            in_buf,
            out_buf,
            error,
            ..
        } = &mut *rt;
        let Some(Some(session)) = sessions.get_mut((handle - 1) as usize) else {
            reset_out_buf(out_buf);
            *error = format!("session handle {handle} not found");
            return 0;
        };
        f(session, in_buf, out_buf, error)
    })
}

fn finish_bytes(res: JwstCodecResult<Vec<u8>>, out_buf: &mut Vec<u8>, error: &mut String) -> u32 {
    reset_out_buf(out_buf);
    match res {
        Ok(bytes) => {
            out_buf.extend_from_slice(&bytes);
            error.clear();
            1
        }
        Err(err) => {
            *error = err.to_string();
            0
        }
    }
}

#[inline]
fn finish_opt_commit(
    res: JwstCodecResult<Option<SessionCommit<Vec<u8>>>>,
    out_buf: &mut Vec<u8>,
    error: &mut String,
) -> u32 {
    match res {
        Ok(None) => {
            error.clear();
            1
        }
        Ok(Some(c)) => {
            let mut w = TapeWriter::new(out_buf);
            encode_commit(&mut w, &c);
            error.clear();
            2
        }
        Err(err) => {
            reset_out_buf(out_buf);
            *error = err.to_string();
            0
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn session_begin_tx(handle: u32, origin: u32) -> u32 {
    with_session_mut(handle, |session, _, _, error| {
        let orig = if origin == 0 {
            SessionTxOrigin::Tracked
        } else {
            SessionTxOrigin::Untracked
        };
        match session.begin_tx(orig) {
            Ok(depth) => {
                error.clear();
                depth as u32
            }
            Err(err) => {
                *error = err.to_string();
                0
            }
        }
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_commit_tx(handle: u32) -> u32 {
    with_session_mut(handle, |session, _, out_buf, error| {
        finish_opt_commit(session.commit_tx(), out_buf, error)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_tx_depth(handle: u32) -> u32 {
    if handle == 0 {
        return 0;
    }
    RUNTIME.with(|rt| {
        let rt = rt.borrow();
        rt.sessions
            .get((handle - 1) as usize)
            .and_then(|s| s.as_ref())
            .map_or(0, |s| s.tx_depth() as u32)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_can_undo(handle: u32) -> u32 {
    if handle == 0 {
        return 0;
    }
    RUNTIME.with(|rt| {
        let rt = rt.borrow();
        rt.sessions
            .get((handle - 1) as usize)
            .and_then(|s| s.as_ref())
            .map_or(0, |s| u32::from(s.can_undo()))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_can_redo(handle: u32) -> u32 {
    if handle == 0 {
        return 0;
    }
    RUNTIME.with(|rt| {
        let rt = rt.borrow();
        rt.sessions
            .get((handle - 1) as usize)
            .and_then(|s| s.as_ref())
            .map_or(0, |s| u32::from(s.can_redo()))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_text_insert_root(handle: u32, root_len: u32, index: u32, text_len: u32) -> u32 {
    with_session_mut(handle, |session, in_buf, out_buf, error| {
        let rlen = root_len as usize;
        let tlen = text_len as usize;
        let Some(total) = rlen.checked_add(tlen) else {
            reset_out_buf(out_buf);
            *error = "in_buf bounds overflow".into();
            return 0;
        };
        if total > in_buf.len() {
            reset_out_buf(out_buf);
            *error = "in_buf bounds".into();
            return 0;
        }
        let (Ok(root), Ok(text)) = (
            std::str::from_utf8(&in_buf[..rlen]),
            std::str::from_utf8(&in_buf[rlen..total]),
        ) else {
            reset_out_buf(out_buf);
            *error = "invalid utf8".into();
            return 0;
        };
        let target = TypeTarget::Identity(TypeIdentity::Root(root.to_string()));
        finish_opt_commit(session.text_insert(&target, index as u64, text), out_buf, error)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_text_insert_id(
    handle: u32,
    client_lo: u32,
    client_hi: u32,
    clock: u32,
    index: u32,
    text_len: u32,
) -> u32 {
    with_session_mut(handle, |session, in_buf, out_buf, error| {
        let tlen = text_len as usize;
        if tlen > in_buf.len() {
            reset_out_buf(out_buf);
            *error = "in_buf bounds".into();
            return 0;
        }
        let Ok(text) = std::str::from_utf8(&in_buf[..tlen]) else {
            reset_out_buf(out_buf);
            *error = "invalid utf8".into();
            return 0;
        };
        let client = (client_lo as u64) | ((client_hi as u64) << 32);
        let target = TypeTarget::Identity(TypeIdentity::Item(Id::new(client, clock as u64)));
        finish_opt_commit(session.text_insert(&target, index as u64, text), out_buf, error)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_text_remove_id(
    handle: u32,
    client_lo: u32,
    client_hi: u32,
    clock: u32,
    index: u32,
    len: u32,
) -> u32 {
    with_session_mut(handle, |session, _, out_buf, error| {
        let client = (client_lo as u64) | ((client_hi as u64) << 32);
        let target = TypeTarget::Identity(TypeIdentity::Item(Id::new(client, clock as u64)));
        finish_opt_commit(session.text_remove(&target, index as u64, len as u64), out_buf, error)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_map_set_f64_id(
    handle: u32,
    client_lo: u32,
    client_hi: u32,
    clock: u32,
    key_len: u32,
    value: f64,
) -> u32 {
    with_session_mut(handle, |session, in_buf, out_buf, error| {
        let klen = key_len as usize;
        if klen > in_buf.len() {
            reset_out_buf(out_buf);
            *error = "in_buf bounds".into();
            return 0;
        }
        let Ok(key) = std::str::from_utf8(&in_buf[..klen]) else {
            reset_out_buf(out_buf);
            *error = "invalid utf8".into();
            return 0;
        };
        let client = (client_lo as u64) | ((client_hi as u64) << 32);
        let target = TypeTarget::Identity(TypeIdentity::Item(Id::new(client, clock as u64)));
        finish_opt_commit(
            session.map_set(
                &target,
                key.to_string(),
                SessionValue::Any(Any::Float64(OrderedFloat(value))),
            ),
            out_buf,
            error,
        )
    })
}

// ---------------------------------------------------------------------------
// Generic aligned-tape command dispatch

fn dispatch_aligned(session: &mut DocSession<Vec<u8>>, input: &[u8], out: &mut Vec<u8>) -> JwstCodecResult {
    let mut r = TapeReader::new(input);
    let op = r.read_u32()?;
    let mut w = TapeWriter::new(out);
    match op {
        1 => {
            let origin = decode_tx_origin(&mut r)?;
            let depth = session.begin_tx(origin)?;
            w.write_u32(depth as u32);
        }
        2 => {
            let commit = session.commit_tx()?;
            encode_opt_commit(&mut w, &commit);
        }
        3 => {
            w.write_u32(session.tx_depth() as u32);
        }
        4 => {
            w.write_u32(u32::from(session.can_undo()));
        }
        5 => {
            let name = r.read_str()?;
            let kind = YTypeKind::from(r.read_u32()? as u64);
            let id = session.ensure_root(name, kind)?;
            encode_identity(&mut w, &id);
        }
        6 => {
            let path = decode_path(&mut r)?;
            match session.resolve_path(&path) {
                None => w.write_u32(0),
                Some(id) => {
                    w.write_u32(1);
                    encode_identity(&mut w, &id);
                }
            }
        }
        7 => {
            let target = decode_target(&mut r)?;
            let key = r.read_str()?;
            match session.get_map_value(&target, key)? {
                None => w.write_u32(0),
                Some(v) => {
                    w.write_u32(1);
                    encode_read_value(&mut w, &v);
                }
            }
        }
        8 => {
            let target = decode_target(&mut r)?;
            let entries = session.read_map(&target)?;
            w.write_u32(entries.len() as u32);
            for (k, v) in &entries {
                w.write_str(k);
                encode_read_value(&mut w, v);
            }
        }
        9 => {
            let target = decode_target(&mut r)?;
            let items = session.read_array(&target)?;
            w.write_u32(items.len() as u32);
            for item in &items {
                encode_read_value(&mut w, item);
            }
        }
        10 => {
            let target = decode_target(&mut r)?;
            let s = session.read_text_string(&target)?;
            w.write_str(&s);
        }
        11 => {
            let target = decode_target(&mut r)?;
            let delta = session.read_text_delta(&target)?;
            encode_delta(&mut w, &delta);
        }
        12 => {
            let target = decode_target(&mut r)?;
            let key = r.read_str()?.to_string();
            let val = decode_session_value(&mut r, 0)?;
            let commit = session.map_set(&target, key, val)?;
            encode_opt_commit(&mut w, &commit);
        }
        13 => {
            let target = decode_target(&mut r)?;
            let key = r.read_str()?;
            let commit = session.map_remove(&target, key)?;
            encode_opt_commit(&mut w, &commit);
        }
        14 => {
            let target = decode_target(&mut r)?;
            let index = r.read_u64()?;
            let count = r.read_u32()? as usize;
            let mut vals = Vec::with_capacity(r.safe_cap(count));
            for _ in 0..count {
                vals.push(decode_session_value(&mut r, 0)?);
            }
            let commit = session.array_insert(&target, index, vals)?;
            encode_opt_commit(&mut w, &commit);
        }
        15 => {
            let target = decode_target(&mut r)?;
            let count = r.read_u32()? as usize;
            let mut vals = Vec::with_capacity(r.safe_cap(count));
            for _ in 0..count {
                vals.push(decode_session_value(&mut r, 0)?);
            }
            let commit = session.array_push(&target, vals)?;
            encode_opt_commit(&mut w, &commit);
        }
        16 => {
            let target = decode_target(&mut r)?;
            let index = r.read_u64()?;
            let text = r.read_str()?;
            let commit = session.text_insert(&target, index, text)?;
            encode_opt_commit(&mut w, &commit);
        }
        17 => {
            let target = decode_target(&mut r)?;
            let index = r.read_u64()?;
            let len = r.read_u64()?;
            let commit = session.text_remove(&target, index, len)?;
            encode_opt_commit(&mut w, &commit);
        }
        18 => {
            let target = decode_target(&mut r)?;
            let delta = decode_delta(&mut r, 0)?;
            let commit = session.text_apply_delta(&target, &delta)?;
            encode_opt_commit(&mut w, &commit);
        }
        19 => {
            let commit = session.undo()?;
            encode_opt_commit(&mut w, &commit);
        }
        20 => {
            let commit = session.redo()?;
            encode_opt_commit(&mut w, &commit);
        }
        21 => {
            w.write_u64(session.client());
        }
        22 => {
            w.write_u32(u32::from(session.client_required()));
        }
        23 => {
            let client_id = r.read_u64()?;
            session.set_client(client_id);
            w.write_u32(1);
        }
        24 => {
            w.write_str(session.guid());
        }
        25 => {
            let id = decode_identity(&mut r)?;
            let status = session.type_status(&id);
            encode_type_status(&mut w, &status);
        }
        26 => {
            let target = decode_target(&mut r)?;
            let index = r.read_u64()?;
            match session.read_array_at(&target, index)? {
                None => w.write_u32(0),
                Some(v) => {
                    w.write_u32(1);
                    encode_read_value(&mut w, &v);
                }
            }
        }
        27 => {
            let target = decode_target(&mut r)?;
            w.write_u64(session.read_text_len(&target)?);
        }
        28 => {
            let target = decode_target(&mut r)?;
            let commit = session.map_clear(&target)?;
            encode_opt_commit(&mut w, &commit);
        }
        29 => {
            let target = decode_target(&mut r)?;
            let index = r.read_u64()?;
            let len = r.read_u64()?;
            let commit = session.array_remove(&target, index, len)?;
            encode_opt_commit(&mut w, &commit);
        }
        30 => {
            let target = decode_target(&mut r)?;
            let index = r.read_u64()?;
            let len = r.read_u64()?;
            let attrs = decode_format(&mut r, 0)?.unwrap_or_default();
            let commit = session.text_format(&target, index, len, attrs)?;
            encode_opt_commit(&mut w, &commit);
        }
        31 => {
            let target = decode_target(&mut r)?;
            let index = r.read_u64()?;
            let embed = decode_any(&mut r, 0)?;
            let commit = session.text_insert_embed(&target, index, embed)?;
            encode_opt_commit(&mut w, &commit);
        }
        34 => {
            let target = decode_target(&mut r)?;
            let name = session.xml_name(&target)?;
            w.write_str(&name);
        }
        35 => {
            let target = decode_target(&mut r)?;
            let key = r.read_str()?.to_string();
            let val = decode_any(&mut r, 0)?;
            let commit = session.xml_set_attr(&target, key, val)?;
            encode_opt_commit(&mut w, &commit);
        }
        36 => {
            let target = decode_target(&mut r)?;
            let key = r.read_str()?;
            match session.xml_get_attr(&target, key)? {
                None => w.write_u32(0),
                Some(v) => {
                    w.write_u32(1);
                    encode_any(&mut w, &v);
                }
            }
        }
        37 => {
            let target = decode_target(&mut r)?;
            let key = r.read_str()?;
            let commit = session.xml_remove_attr(&target, key)?;
            encode_opt_commit(&mut w, &commit);
        }
        38 => {
            let target = decode_target(&mut r)?;
            let attrs = session.xml_attrs(&target)?;
            w.write_u32(attrs.len() as u32);
            for (k, v) in &attrs {
                w.write_str(k);
                encode_any(&mut w, v);
            }
        }
        39 => {
            let target = decode_target(&mut r)?;
            let xml_str = session.xml_to_string(&target)?;
            w.write_str(&xml_str);
        }
        40 => {
            let target = decode_target(&mut r)?;
            let index = r.read_u64()?;
            let assoc = r.read_i64()?;
            let rpos = session.create_relative_position(&target, index, assoc)?;
            let bytes = rpos.encode()?;
            w.write_bytes(&bytes);
        }
        41 => {
            let bytes = r.read_bytes()?.to_vec();
            let follow = r.read_u32()? != 0;
            let rpos = RelativePosition::decode(bytes)?;
            match session.resolve_relative_position(&rpos, follow) {
                None => w.write_u32(0),
                Some(abs) => {
                    w.write_u32(1);
                    encode_abs_pos(&mut w, &abs);
                }
            }
        }
        42 => {
            let now_ms = r.read_u64()?;
            session.advance_time(now_ms);
            w.write_u32(1);
        }
        43 => {
            let meta = r.read_bytes()?.to_vec();
            w.write_u32(u32::from(session.set_undo_selection_meta(meta)?));
        }
        44 => {
            session.stop_capturing()?;
            w.write_u32(1);
        }
        45 => {
            let undo = r.read_u32()? != 0;
            let redo = r.read_u32()? != 0;
            session.clear_history(undo, redo)?;
            w.write_u32(1);
        }
        46 => {
            w.write_u32(u32::from(session.can_redo()));
        }
        47 => {
            let scope_count = r.read_u32()? as usize;
            let mut scopes = Vec::with_capacity(r.safe_cap(scope_count));
            for _ in 0..scope_count {
                scopes.push(decode_target(&mut r)?);
            }
            let capture_timeout_ms = r.read_u64()?;
            let origin_count = r.read_u32()? as usize;
            let mut origins = Vec::with_capacity(r.safe_cap(origin_count));
            for _ in 0..origin_count {
                origins.push(decode_tx_origin(&mut r)?);
            }
            let stack_id = session.create_undo_stack(&scopes, capture_timeout_ms, &origins)?;
            w.write_u32(stack_id.0);
        }
        48 => {
            let stack_id = UndoStackId(r.read_u32()?);
            let commit = session.undo_stack(stack_id)?;
            encode_opt_commit(&mut w, &commit);
        }
        49 => {
            let stack_id = UndoStackId(r.read_u32()?);
            let commit = session.redo_stack(stack_id)?;
            encode_opt_commit(&mut w, &commit);
        }
        50 => {
            let stack_id = UndoStackId(r.read_u32()?);
            w.write_u32(u32::from(session.can_undo_stack(stack_id)));
        }
        51 => {
            let stack_id = UndoStackId(r.read_u32()?);
            w.write_u32(u32::from(session.can_redo_stack(stack_id)));
        }
        52 => {
            let stack_id = UndoStackId(r.read_u32()?);
            let which = if r.read_u32()? == 0 {
                UndoStack::Undo
            } else {
                UndoStack::Redo
            };
            let meta = r.read_bytes()?.to_vec();
            w.write_u32(u32::from(session.set_stack_selection_meta(stack_id, which, meta)?));
        }
        53 => {
            let stack_id = UndoStackId(r.read_u32()?);
            session.stop_capturing_stack(stack_id)?;
            w.write_u32(1);
        }
        54 => {
            let stack_id = UndoStackId(r.read_u32()?);
            let undo = r.read_u32()? != 0;
            let redo = r.read_u32()? != 0;
            session.clear_stack_history(stack_id, undo, redo)?;
            w.write_u32(1);
        }
        55 => {
            let stack_id = UndoStackId(r.read_u32()?);
            w.write_u32(u32::from(session.destroy_undo_stack(stack_id)?));
        }
        _ => return Err(JwstCodecError::IncompleteDocument("unknown op".into())),
    }
    Ok(())
}

#[unsafe(no_mangle)]
pub extern "C" fn session_exec(handle: u32, len: usize) -> u32 {
    with_session_mut(handle, |session, in_buf, out_buf, error| {
        if len > in_buf.len() {
            reset_out_buf(out_buf);
            *error = "input len out of bounds".into();
            return 0;
        }
        match dispatch_aligned(session, &in_buf[..len], out_buf) {
            Ok(()) => {
                error.clear();
                1
            }
            Err(err) => {
                reset_out_buf(out_buf);
                *error = err.to_string();
                0
            }
        }
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_apply_update_v1(handle: u32, len: usize) -> u32 {
    with_session_mut(handle, |session, in_buf, out_buf, error| {
        if len > in_buf.len() {
            reset_out_buf(out_buf);
            *error = "input len out of bounds".into();
            return 0;
        }
        match session.apply_update_v1(&in_buf[..len]) {
            Ok(commits) => {
                let count = commits.len();
                if count == 0 {
                    reset_out_buf(out_buf);
                } else {
                    let mut w = TapeWriter::new(out_buf);
                    for c in &commits {
                        encode_commit(&mut w, c);
                    }
                }
                error.clear();
                1 + count as u32
            }
            Err(err) => {
                reset_out_buf(out_buf);
                *error = err.to_string();
                0
            }
        }
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_encode_update_v1(handle: u32) -> u32 {
    with_session_mut(handle, |session, _, out_buf, error| {
        finish_bytes(session.encode_update_v1(), out_buf, error)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_encode_sv_v1(handle: u32) -> u32 {
    with_session_mut(handle, |session, _, out_buf, error| {
        finish_bytes(session.encode_state_vector_v1(), out_buf, error)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn session_encode_diff_v1(handle: u32, sv_len: usize) -> u32 {
    with_session_mut(handle, |session, in_buf, out_buf, error| {
        if sv_len > in_buf.len() {
            reset_out_buf(out_buf);
            *error = "sv_len out of bounds".into();
            return 0;
        }
        finish_bytes(session.encode_diff_v1(&in_buf[..sv_len]), out_buf, error)
    })
}

// ---------------------------------------------------------------------------
// Awareness exports (4B-aligned binary tape, zero serde_json)

#[unsafe(no_mangle)]
pub extern "C" fn awareness_create(local_id: u64) -> u32 {
    let awareness = Awareness::new(local_id);
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        for (i, slot) in rt.awarenesses.iter_mut().enumerate() {
            if slot.is_none() {
                *slot = Some(awareness);
                return (i + 1) as u32;
            }
        }
        rt.awarenesses.push(Some(awareness));
        rt.awarenesses.len() as u32
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn awareness_free(handle: u32) {
    if handle == 0 {
        return;
    }
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        if let Some(slot) = rt.awarenesses.get_mut((handle - 1) as usize) {
            *slot = None;
        }
    });
}

#[unsafe(no_mangle)]
pub extern "C" fn awareness_local_id(handle: u32) -> u64 {
    if handle == 0 {
        return 0;
    }
    RUNTIME.with(|rt| {
        rt.borrow()
            .awarenesses
            .get((handle - 1) as usize)
            .and_then(|a| a.as_ref())
            .map_or(0, Awareness::local_id)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn awareness_set_local_id(handle: u32, new_local_id: u64) -> u32 {
    if handle == 0 {
        return set_error("invalid awareness handle 0");
    }
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        let WasmRuntime {
            awarenesses,
            out_buf,
            error,
            ..
        } = &mut *rt;
        let Some(Some(awareness)) = awarenesses.get_mut((handle - 1) as usize) else {
            *error = format!("awareness handle {handle} not found");
            return 0;
        };
        let ev = awareness.set_local_id(new_local_id);
        let mut w = TapeWriter::new(out_buf);
        encode_awareness_event(&mut w, &ev);
        error.clear();
        1
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn awareness_set_local_state(handle: u32, len: usize) -> u32 {
    if handle == 0 {
        return set_error("invalid awareness handle 0");
    }
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        let WasmRuntime {
            awarenesses,
            in_buf,
            out_buf,
            error,
            ..
        } = &mut *rt;
        if len > in_buf.len() {
            *error = "input len out of bounds".into();
            return 0;
        }
        let Ok(text) = std::str::from_utf8(&in_buf[..len]) else {
            *error = "awareness state must be valid UTF-8".into();
            return 0;
        };
        let Some(Some(awareness)) = awarenesses.get_mut((handle - 1) as usize) else {
            *error = format!("awareness handle {handle} not found");
            return 0;
        };
        awareness.set_local_state(text.to_string());
        out_buf.clear();
        error.clear();
        1
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn awareness_clear_local_state(handle: u32) -> u32 {
    if handle == 0 {
        return set_error("invalid awareness handle 0");
    }
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        let WasmRuntime {
            awarenesses,
            out_buf,
            error,
            ..
        } = &mut *rt;
        let Some(Some(awareness)) = awarenesses.get_mut((handle - 1) as usize) else {
            *error = format!("awareness handle {handle} not found");
            return 0;
        };
        awareness.clear_local_state();
        out_buf.clear();
        error.clear();
        1
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn awareness_get_states(handle: u32) -> u32 {
    if handle == 0 {
        return set_error("invalid awareness handle 0");
    }
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        let WasmRuntime {
            awarenesses,
            out_buf,
            error,
            ..
        } = &mut *rt;
        let Some(Some(awareness)) = awarenesses.get_mut((handle - 1) as usize) else {
            *error = format!("awareness handle {handle} not found");
            return 0;
        };
        let mut entries: Vec<(u64, u64, &str, bool)> = awareness
            .get_states()
            .iter()
            .map(|(id, st)| (*id, st.clock(), st.content(), st.is_deleted()))
            .collect();
        entries.sort_by_key(|(id, _, _, _)| *id);
        let mut w = TapeWriter::new(out_buf);
        w.write_u32(entries.len() as u32);
        for (id, clock, content, deleted) in entries {
            w.write_u64(id);
            w.write_u64(clock);
            w.write_str(content);
            w.write_u32(u32::from(deleted));
        }
        error.clear();
        1
    })
}

/// Encodes an awareness update.
/// - `has_filter == 0`: encodes all clients (`None`).
/// - `has_filter != 0 && clients_count == 0`: encodes an empty client list
///   (`Some(&[])`).
/// - `has_filter != 0 && clients_count > 0`: reads `clients_count`
///   little-endian `u64` client IDs from `in_buf` (`Some(&ids)`).
#[unsafe(no_mangle)]
pub extern "C" fn awareness_encode_update(handle: u32, has_filter: u32, clients_count: usize) -> u32 {
    if handle == 0 {
        return set_error("invalid awareness handle 0");
    }
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        let WasmRuntime {
            awarenesses,
            in_buf,
            out_buf,
            error,
            ..
        } = &mut *rt;
        let clients: Option<Vec<u64>> = if has_filter == 0 {
            None
        } else if clients_count == 0 {
            Some(Vec::new())
        } else {
            let Some(byte_len) = clients_count.checked_mul(8) else {
                *error = "clients_count overflow".into();
                return 0;
            };
            if byte_len > in_buf.len() {
                *error = "clients buffer out of bounds".into();
                return 0;
            }
            let mut r = TapeReader::new(&in_buf[..byte_len]);
            let mut ids = Vec::with_capacity(clients_count.min(MAX_PREALLOC));
            for _ in 0..clients_count {
                match r.read_u64() {
                    Ok(id) => ids.push(id),
                    Err(e) => {
                        *error = e.to_string();
                        return 0;
                    }
                }
            }
            Some(ids)
        };
        let Some(Some(awareness)) = awarenesses.get_mut((handle - 1) as usize) else {
            *error = format!("awareness handle {handle} not found");
            return 0;
        };
        match awareness.encode_update(clients.as_deref()) {
            Ok(bytes) => {
                out_buf.clear();
                if out_buf.capacity() > HIGH_WATER {
                    out_buf.shrink_to(TRIM_TARGET);
                }
                out_buf.extend_from_slice(&bytes);
                error.clear();
                1
            }
            Err(err) => {
                out_buf.clear();
                *error = err.to_string();
                0
            }
        }
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn awareness_apply_update_v1(handle: u32, len: usize) -> u32 {
    if handle == 0 {
        return set_error("invalid awareness handle 0");
    }
    RUNTIME.with(|rt| {
        let mut rt = rt.borrow_mut();
        let WasmRuntime {
            awarenesses,
            in_buf,
            out_buf,
            error,
            ..
        } = &mut *rt;
        if len > in_buf.len() {
            *error = "input len out of bounds".into();
            return 0;
        }
        let Some(Some(awareness)) = awarenesses.get_mut((handle - 1) as usize) else {
            *error = format!("awareness handle {handle} not found");
            return 0;
        };
        match awareness.apply_update_v1(&in_buf[..len]) {
            Ok(ev) => {
                let mut w = TapeWriter::new(out_buf);
                encode_awareness_event(&mut w, &ev);
                error.clear();
                1
            }
            Err(err) => {
                out_buf.clear();
                *error = err.to_string();
                0
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wasm_scheme_c_smoke_and_wire_native() {
        let guid = b"test-doc";
        let ptr = in_buf_ensure(guid.len());
        unsafe { std::ptr::copy_nonoverlapping(guid.as_ptr(), ptr, guid.len()) };
        let h = session_create(42, guid.len(), 1, 0, 500);
        assert_ne!(h, 0);

        // EnsureRoot("text", Text)
        let mut cmd = Vec::new();
        {
            let mut w = TapeWriter::new(&mut cmd);
            w.write_u32(5);
            w.write_str("text");
            w.write_u32(2); // Text
        }
        let ptr = in_buf_ensure(cmd.len());
        unsafe { std::ptr::copy_nonoverlapping(cmd.as_ptr(), ptr, cmd.len()) };
        assert_eq!(session_exec(h, cmd.len()), 1);

        // Direct scalar hot path: text insert on root
        let payload = b"texthi";
        let ptr = in_buf_ensure(payload.len());
        unsafe { std::ptr::copy_nonoverlapping(payload.as_ptr(), ptr, payload.len()) };
        assert_eq!(session_text_insert_root(h, 4, 0, 2), 2);

        // Encode update and validate via wire_validate_update_v1
        assert_eq!(session_encode_update_v1(h), 1);
        let update = RUNTIME.with(|rt| rt.borrow().out_buf.clone());
        let ptr = in_buf_ensure(update.len());
        unsafe { std::ptr::copy_nonoverlapping(update.as_ptr(), ptr, update.len()) };
        assert_eq!(wire_validate_update_v1(update.len()), 1);

        session_free(h);
    }

    #[test]
    fn tape_rejects_len_overflow_oom_count_and_excessive_depth() {
        // 1. len = u32::MAX must not wrap around in (len + 3) & !3
        let mut buf = Vec::new();
        {
            let mut w = TapeWriter::new(&mut buf);
            w.write_u32(u32::MAX);
        }
        let mut r = TapeReader::new(&buf);
        assert!(r.read_bytes().is_err());

        // 2. Huge array count must not OOM before hitting EOF
        buf.clear();
        {
            let mut w = TapeWriter::new(&mut buf);
            w.write_u32(10); // Any::Array
            w.write_u32(u32::MAX);
        }
        let mut r = TapeReader::new(&buf);
        assert!(decode_any(&mut r, 0).is_err());

        // 3. Huge object count must not OOM before hitting EOF
        buf.clear();
        {
            let mut w = TapeWriter::new(&mut buf);
            w.write_u32(11); // Any::Object
            w.write_u32(u32::MAX);
        }
        let mut r = TapeReader::new(&buf);
        assert!(decode_any(&mut r, 0).is_err());

        // 4. Deeply nested Any (> Any::DEFAULT_MAX_DEPTH) rejected
        buf.clear();
        {
            let mut w = TapeWriter::new(&mut buf);
            for _ in 0..(Any::DEFAULT_MAX_DEPTH + 2) {
                w.write_u32(10); // Any::Array
                w.write_u32(1);
            }
            w.write_u32(1); // Any::Null
        }
        let mut r = TapeReader::new(&buf);
        assert!(decode_any(&mut r, 0).is_err());

        // 5. Deeply nested SessionValue (> Any::DEFAULT_MAX_DEPTH) rejected
        buf.clear();
        {
            let mut w = TapeWriter::new(&mut buf);
            for _ in 0..(Any::DEFAULT_MAX_DEPTH + 2) {
                w.write_u32(2); // SessionValue::Array
                w.write_u32(1);
            }
            w.write_u32(0); // SessionValue::Any
            w.write_u32(1); // Any::Null
        }
        let mut r = TapeReader::new(&buf);
        assert!(decode_session_value(&mut r, 0).is_err());

        // 6. Combined depth across SessionValue::Array -> SessionValue::Text ->
        //    format Any
        buf.clear();
        {
            let mut w = TapeWriter::new(&mut buf);
            let outer_arrays = Any::DEFAULT_MAX_DEPTH / 2;
            let inner_any_arrays = Any::DEFAULT_MAX_DEPTH - outer_arrays + 2;
            for _ in 0..outer_arrays {
                w.write_u32(2); // SessionValue::Array
                w.write_u32(1);
            }
            w.write_u32(3); // SessionValue::Text
            w.write_u32(1); // 1 delta op
            w.write_u32(0); // Insert Text
            w.write_str("x");
            w.write_u32(1); // 1 format attr
            w.write_str("k");
            for _ in 0..inner_any_arrays {
                w.write_u32(10); // Any::Array
                w.write_u32(1);
            }
            w.write_u32(1); // Any::Null
        }
        let mut r = TapeReader::new(&buf);
        assert!(decode_session_value(&mut r, 0).is_err());
    }

    #[test]
    fn scratch_high_water_auto_trims() {
        let _ = in_buf_ensure(HIGH_WATER + 1024);
        RUNTIME.with(|rt| {
            assert!(rt.borrow().in_buf.capacity() > HIGH_WATER);
        });
        let _ = in_buf_ensure(1024);
        RUNTIME.with(|rt| {
            assert!(rt.borrow().in_buf.capacity() <= HIGH_WATER);
        });
        runtime_trim_scratch();
        RUNTIME.with(|rt| {
            assert!(rt.borrow().in_buf.len() <= TRIM_TARGET);
        });
    }
}
