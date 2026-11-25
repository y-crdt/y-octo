use std::ops::Range;

use serde::Deserialize;
use y_octo_core::{CodecError, LimitKind, decoder_v1 as core_v1};

use super::{Id, JwstCodecError};

#[derive(Clone, Copy)]
pub(crate) struct DecodeLimits {
    pub(crate) max_structs: usize,
    pub(crate) max_clients: usize,
    pub(crate) max_collection_entries: usize,
    pub(crate) max_any_depth: usize,
    pub(crate) max_content_bytes: usize,
}

impl DecodeLimits {
    /// Limits of [crate::Update] decoding: sizes are bounded by the input,
    /// but nested `Any` values are owned trees whose clone, drop and
    /// comparison recurse, so their depth is capped like [crate::Any] reads.
    /// Callers raising `max_any_depth` clamp it with
    /// [crate::Any::MAX_CONFIGURABLE_DEPTH] first.
    pub(crate) const UPDATE: Self = Self {
        max_structs: usize::MAX,
        max_clients: usize::MAX,
        max_collection_entries: usize::MAX,
        max_any_depth: crate::Any::DEFAULT_MAX_DEPTH,
        max_content_bytes: usize::MAX,
    };

    #[cfg(test)]
    pub(crate) const UNRESTRICTED: Self = Self {
        max_any_depth: usize::MAX,
        ..Self::UPDATE
    };
}

#[derive(Debug)]
pub(crate) enum Error {
    Codec(JwstCodecError),
    Resource(&'static str),
}

impl From<JwstCodecError> for Error {
    fn from(value: JwstCodecError) -> Self {
        Self::Codec(value)
    }
}

pub(crate) type Result<T> = std::result::Result<T, Error>;

#[derive(Clone)]
pub(crate) struct WireStr<'a> {
    pub(crate) value: &'a str,
    pub(crate) range: Range<usize>,
}

#[derive(Clone)]
pub(crate) struct WireBytes<'a> {
    pub(crate) value: &'a [u8],
    pub(crate) range: Range<usize>,
}

#[derive(Clone)]
pub(crate) enum WireParent<'a> {
    Root(WireStr<'a>),
    Item(Id),
    Inherit,
}

#[derive(Clone)]
pub(crate) struct ItemMeta<'a> {
    pub(crate) origin_left: Option<Id>,
    pub(crate) origin_right: Option<Id>,
    pub(crate) parent: WireParent<'a>,
    pub(crate) parent_sub: Option<WireStr<'a>>,
    pub(crate) raw_range: Range<usize>,
}

pub(crate) enum ContentAtom<'a> {
    Deleted(u64),
    Binary(WireBytes<'a>),
    String(WireStr<'a>),
    Embed(WireStr<'a>),
    Format { key: WireStr<'a>, value: WireStr<'a> },
    Type { kind: u64, tag: Option<WireStr<'a>> },
}

pub(crate) enum AnyEvent<'a> {
    Undefined,
    Null,
    Integer(i32),
    Float32(f32),
    Float64(f64),
    BigInt64(i64),
    False,
    True,
    String(WireStr<'a>),
    Binary(WireBytes<'a>),
    BeginObject(usize),
    ObjectKey(WireStr<'a>),
    BeginArray(usize),
    EndContainer,
}

pub(crate) trait Sink<'a>: Sized {
    type Output;
    type Content;
    type Any;

    fn begin_client(&mut self, client: u64, count: usize) -> Result<()>;
    fn gc(&mut self, id: Id, len: u64) -> Result<()>;
    fn skip(&mut self, id: Id, len: u64) -> Result<()>;
    fn item(&mut self, id: Id, len: u64, meta: ItemMeta<'a>, content: Self::Content) -> Result<()>;
    fn skipped_zero_origin(&mut self, _origin_left: Id) {}

    fn content_atom(&mut self, atom: ContentAtom<'a>) -> Result<Self::Content>;
    fn json_start(&mut self, count: usize) -> Result<()>;
    fn json_value(&mut self, value: WireStr<'a>) -> Result<()>;
    fn json_finish(&mut self) -> Result<Self::Content>;
    fn any_content_start(&mut self, count: usize) -> Result<()>;
    fn any_content_value(&mut self, value: Self::Any) -> Result<()>;
    fn any_content_finish(&mut self) -> Result<Self::Content>;
    fn doc_content(&mut self, guid: WireStr<'a>, options: Self::Any) -> Result<Self::Content>;

    fn any_start(&mut self) -> Result<()>;
    fn any_event(&mut self, event: AnyEvent<'a>) -> Result<()>;
    fn any_finish(&mut self, range: Range<usize>) -> Result<Self::Any>;

    fn delete_range(&mut self, client: u64, range: Range<u64>) -> Result<()>;
    fn finish(self) -> Result<Self::Output>;
}

#[cfg_attr(not(debug_assertions), inline(always))]
pub(crate) fn decode<'a, S: Sink<'a>>(input: &'a [u8], sink: S, limits: DecodeLimits) -> Result<S::Output> {
    let core_limits = core_v1::DecodeLimitsCore {
        max_structs: limits.max_structs,
        max_clients: limits.max_clients,
        max_collection_entries: limits.max_collection_entries,
        max_any_depth: limits.max_any_depth,
        max_content_bytes: limits.max_content_bytes,
    };
    let mut adapter = Adapter::new(input, sink);
    match core_v1::decode_update_v1(input, &mut adapter, &core_limits) {
        Ok(()) => adapter.sink.finish(),
        Err(err) => Err(adapter.error.take().unwrap_or_else(|| map_core_error(err))),
    }
}

pub(crate) fn limit_name(kind: LimitKind) -> &'static str {
    match kind {
        LimitKind::Clients => "clients",
        LimitKind::DeleteClients => "delete clients",
        LimitKind::Structs => "structs",
        LimitKind::CollectionEntries => "collection entries",
        LimitKind::ContentBytes => "content bytes",
        LimitKind::AnyDepth => "Any nesting depth",
        LimitKind::ContentEntries => "content entries",
        LimitKind::AnyObjectEntries => "Any object entries",
        LimitKind::AnyArrayEntries => "Any array entries",
        LimitKind::DeleteRanges => "delete ranges",
    }
}

pub(crate) fn map_core_error(err: CodecError) -> Error {
    match err {
        CodecError::UnexpectedEof => {
            Error::Codec(JwstCodecError::UpdateInvalid(nom::Err::Incomplete(nom::Needed::new(1))))
        }
        CodecError::VarintOverflow => Error::Codec(JwstCodecError::UpdateInvalid(nom::Err::Failure(
            nom::error::Error::new(0, nom::error::ErrorKind::TooLarge),
        ))),
        CodecError::UnexpectedByteEof => Error::Codec(JwstCodecError::IncompleteDocument(
            "failed to fill whole buffer".to_owned(),
        )),
        CodecError::BufferTooLarge => Error::Codec(JwstCodecError::IncompleteDocument("buffer too large".to_owned())),
        CodecError::BufferLengthOverflow => {
            Error::Codec(JwstCodecError::IncompleteDocument("buffer length overflow".to_owned()))
        }
        CodecError::BufferExceedsUpdate => {
            Error::Codec(JwstCodecError::IncompleteDocument("buffer exceeds update".to_owned()))
        }
        CodecError::LengthOverflow => Error::Resource("length"),
        CodecError::ZeroLengthStruct => {
            Error::Codec(JwstCodecError::IncompleteDocument("zero-length struct".to_owned()))
        }
        CodecError::ClockOverflow => Error::Codec(JwstCodecError::StructClockInvalid {
            expect: u64::MAX,
            actually: u64::MAX,
        }),
        CodecError::DuplicateClient => {
            Error::Codec(JwstCodecError::IncompleteDocument("duplicate struct block".to_owned()))
        }
        CodecError::TrailingBytes => Error::Codec(JwstCodecError::UpdateNotFullyConsumed(0)),
        CodecError::InvalidUtf8 => Error::Codec(JwstCodecError::IncompleteDocument("invalid utf-8".to_owned())),
        CodecError::UnknownContentTag => {
            Error::Codec(JwstCodecError::IncompleteDocument("Unknown content type".to_owned()))
        }
        CodecError::UnknownContentTagByte(tag) => Error::Codec(JwstCodecError::IncompleteDocument(format!(
            "Unknown content type: {tag}"
        ))),
        CodecError::UnknownAnyTag => Error::Codec(JwstCodecError::IncompleteDocument("unknown Any tag".to_owned())),
        CodecError::UnknownAnyTagByte(tag) => {
            Error::Codec(JwstCodecError::IncompleteDocument(format!("unknown Any tag: {tag}")))
        }
        CodecError::UnknownTypeKind => Error::Codec(JwstCodecError::IncompleteDocument("Unknown y type".to_owned())),
        CodecError::LimitExceeded => Error::Resource("limit exceeded"),
        CodecError::ResourceLimit(kind) => Error::Resource(limit_name(kind)),
        CodecError::CountTooLarge(kind) => Error::Codec(JwstCodecError::IncompleteDocument(format!(
            "{}: declared count exceeds remaining bytes",
            limit_name(kind)
        ))),
        CodecError::SinkAborted => Error::Codec(JwstCodecError::Unexpected),
    }
}

struct Adapter<'a, S: Sink<'a>> {
    input: &'a [u8],
    sink: S,
    seen_clients: crate::doc::HashSet<u64>,
    pending_content: Option<S::Content>,
    pending_any: Option<S::Any>,
    early_strs: [Option<&'a str>; 4],
    error: Option<Error>,
}

impl<'a, S: Sink<'a>> Adapter<'a, S> {
    fn new(input: &'a [u8], sink: S) -> Self {
        Self {
            input,
            sink,
            seen_clients: crate::doc::HashSet::default(),
            pending_content: None,
            pending_any: None,
            early_strs: [None; 4],
            error: None,
        }
    }

    #[cold]
    #[inline(never)]
    fn abort(&mut self, err: Error) -> CodecError {
        self.error = Some(err);
        CodecError::SinkAborted
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn forward(&mut self, res: Result<()>) -> core::result::Result<(), CodecError> {
        match res {
            Ok(()) => Ok(()),
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn wire_id(id: core_v1::WireId) -> Id {
        Id::new(id.client, id.clock)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn wire_str(&mut self, span: core_v1::Span) -> core::result::Result<WireStr<'a>, CodecError> {
        let range = span.start..span.end;
        match std::str::from_utf8(&self.input[range.clone()]) {
            Ok(value) => Ok(WireStr { value, range }),
            Err(e) => Err(self.abort(Error::Codec(JwstCodecError::IncompleteDocument(e.to_string())))),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn take_early_str(&mut self, slot: usize, span: core_v1::Span) -> core::result::Result<WireStr<'a>, CodecError> {
        let range = span.start..span.end;
        let slice = &self.input[range.clone()];
        let value = match self.early_strs[slot].take() {
            Some(s) => {
                debug_assert!(
                    std::ptr::eq(s.as_ptr(), slice.as_ptr()) && s.len() == slice.len(),
                    "early_strs slot {slot} reused for a different span"
                );
                s
            }
            None => match std::str::from_utf8(slice) {
                Ok(s) => s,
                Err(e) => return Err(self.abort(Error::Codec(JwstCodecError::IncompleteDocument(e.to_string())))),
            },
        };
        Ok(WireStr { value, range })
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn wire_bytes(&self, span: core_v1::Span) -> WireBytes<'a> {
        let range = span.start..span.end;
        let value = &self.input[range.clone()];
        WireBytes { value, range }
    }

    fn validate_json(&mut self, span: core_v1::Span) -> core::result::Result<WireStr<'a>, CodecError> {
        let value = self.wire_str(span)?;
        let mut decoder = serde_json::Deserializer::from_str(value.value);
        if JsonAnyValidator::deserialize(&mut decoder)
            .and_then(|_| decoder.end())
            .is_err()
        {
            return Err(self.abort(Error::Codec(JwstCodecError::DamagedDocumentJson)));
        }
        Ok(value)
    }
}

impl<'a, S: Sink<'a>> core_v1::V1Sink for Adapter<'a, S> {
    #[cfg_attr(not(debug_assertions), inline(always))]
    fn core_validates_utf8(&self) -> bool {
        false
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn validate_utf8_early(&mut self, slot: u8, span: core_v1::Span) -> core::result::Result<(), CodecError> {
        let s = match std::str::from_utf8(&self.input[span.start..span.end]) {
            Ok(s) => s,
            Err(e) => return Err(self.abort(Error::Codec(JwstCodecError::IncompleteDocument(e.to_string())))),
        };
        if let Some(cell) = self.early_strs.get_mut(slot as usize) {
            *cell = Some(s);
        }
        Ok(())
    }

    #[cold]
    #[inline(never)]
    fn on_decode_error(&mut self, err: CodecError, a: usize, b: u64) {
        let mapped = match err {
            CodecError::UnexpectedEof => Error::Codec(JwstCodecError::UpdateInvalid(nom::Err::Incomplete(
                nom::Needed::new(a.saturating_add(1)),
            ))),
            CodecError::VarintOverflow => Error::Codec(JwstCodecError::UpdateInvalid(nom::Err::Failure(
                nom::error::Error::new(a, nom::error::ErrorKind::TooLarge),
            ))),
            CodecError::ClockOverflow => Error::Codec(JwstCodecError::StructClockInvalid {
                expect: b,
                actually: u64::MAX,
            }),
            CodecError::TrailingBytes => Error::Codec(JwstCodecError::UpdateNotFullyConsumed(a)),
            CodecError::UnknownTypeKind => {
                Error::Codec(JwstCodecError::IncompleteDocument(format!("Unknown y type: {b}")))
            }
            CodecError::CountTooLarge(kind) => Error::Codec(JwstCodecError::IncompleteDocument(format!(
                "{}: {a} declared, at most {b} fit in the rest of the update",
                limit_name(kind)
            ))),
            other => map_core_error(other),
        };
        self.error = Some(mapped);
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn record_client(&mut self, client: u64) -> core::result::Result<bool, CodecError> {
        if !self.seen_clients.insert(client) {
            return Err(self.abort(Error::Codec(JwstCodecError::IncompleteDocument(format!(
                "duplicate struct block for client {client}"
            )))));
        }
        Ok(true)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn begin_client(&mut self, client: u64, count: usize) -> core::result::Result<(), CodecError> {
        let res = self.sink.begin_client(client, count);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_gc(&mut self, id: core_v1::WireId, len: u64) -> core::result::Result<(), CodecError> {
        let res = self.sink.gc(Self::wire_id(id), len);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_skip(&mut self, id: core_v1::WireId, len: u64) -> core::result::Result<(), CodecError> {
        let res = self.sink.skip(Self::wire_id(id), len);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_item(
        &mut self,
        id: core_v1::WireId,
        len: u64,
        meta: core_v1::ItemMetaCore,
    ) -> core::result::Result<(), CodecError> {
        let Some(content) = self.pending_content.take() else {
            return Err(self.abort(Error::Codec(JwstCodecError::Unexpected)));
        };
        let parent = match meta.parent {
            core_v1::WireParentCore::Root(span) => WireParent::Root(self.take_early_str(0, span)?),
            core_v1::WireParentCore::Item(pid) => WireParent::Item(Self::wire_id(pid)),
            core_v1::WireParentCore::Inherit => WireParent::Inherit,
        };
        let parent_sub = match meta.parent_sub {
            Some(span) => Some(self.take_early_str(1, span)?),
            None => None,
        };
        let mapped_meta = ItemMeta {
            origin_left: meta.origin_left.map(Self::wire_id),
            origin_right: meta.origin_right.map(Self::wire_id),
            parent,
            parent_sub,
            raw_range: meta.raw_range.start..meta.raw_range.end,
        };
        let res = self.sink.item(Self::wire_id(id), len, mapped_meta, content);
        self.forward(res)
    }

    #[cold]
    #[inline(never)]
    fn on_skipped_zero_origin(&mut self, origin_left: core_v1::WireId) {
        self.sink.skipped_zero_origin(Self::wire_id(origin_left));
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_deleted(&mut self, len: u64) -> core::result::Result<(), CodecError> {
        let res = self.sink.content_atom(ContentAtom::Deleted(len));
        match res {
            Ok(c) => {
                self.pending_content = Some(c);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_json_start(&mut self, count: usize) -> core::result::Result<(), CodecError> {
        let res = self.sink.json_start(count);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_json_value(&mut self, value: core_v1::Span) -> core::result::Result<(), CodecError> {
        let ws = self.wire_str(value)?;
        let res = self.sink.json_value(ws);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_json_finish(&mut self) -> core::result::Result<(), CodecError> {
        let res = self.sink.json_finish();
        match res {
            Ok(c) => {
                self.pending_content = Some(c);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_binary(&mut self, value: core_v1::Span) -> core::result::Result<(), CodecError> {
        let wb = self.wire_bytes(value);
        let res = self.sink.content_atom(ContentAtom::Binary(wb));
        match res {
            Ok(c) => {
                self.pending_content = Some(c);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_string(&mut self, value: core_v1::Span) -> core::result::Result<(), CodecError> {
        let ws = self.wire_str(value)?;
        let res = self.sink.content_atom(ContentAtom::String(ws));
        match res {
            Ok(c) => {
                self.pending_content = Some(c);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_embed(&mut self, value: core_v1::Span) -> core::result::Result<(), CodecError> {
        let ws = self.validate_json(value)?;
        let res = self.sink.content_atom(ContentAtom::Embed(ws));
        match res {
            Ok(c) => {
                self.pending_content = Some(c);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_format(&mut self, key: core_v1::Span, value: core_v1::Span) -> core::result::Result<(), CodecError> {
        let key_str = self.take_early_str(2, key)?;
        let val_str = self.validate_json(value)?;
        let res = self.sink.content_atom(ContentAtom::Format {
            key: key_str,
            value: val_str,
        });
        match res {
            Ok(c) => {
                self.pending_content = Some(c);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_type(&mut self, kind: u64, tag: Option<core_v1::Span>) -> core::result::Result<(), CodecError> {
        let tag_str = match tag {
            Some(span) => Some(self.wire_str(span)?),
            None => None,
        };
        let res = self.sink.content_atom(ContentAtom::Type { kind, tag: tag_str });
        match res {
            Ok(c) => {
                self.pending_content = Some(c);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_content_start(&mut self, count: usize) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_content_start(count);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_content_value(&mut self) -> core::result::Result<(), CodecError> {
        let Some(any) = self.pending_any.take() else {
            return Err(self.abort(Error::Codec(JwstCodecError::Unexpected)));
        };
        let res = self.sink.any_content_value(any);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_content_finish(&mut self) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_content_finish();
        match res {
            Ok(c) => {
                self.pending_content = Some(c);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_doc(&mut self, guid: core_v1::Span) -> core::result::Result<(), CodecError> {
        let guid_str = self.take_early_str(3, guid)?;
        let Some(options) = self.pending_any.take() else {
            return Err(self.abort(Error::Codec(JwstCodecError::Unexpected)));
        };
        let res = self.sink.doc_content(guid_str, options);
        match res {
            Ok(c) => {
                self.pending_content = Some(c);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_start(&mut self) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_start();
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_undefined(&mut self) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_event(AnyEvent::Undefined);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_null(&mut self) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_event(AnyEvent::Null);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_i32(&mut self, value: i32) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_event(AnyEvent::Integer(value));
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_f32_bits(&mut self, bits: u32) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_event(AnyEvent::Float32(f32::from_bits(bits)));
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_f64_bits(&mut self, bits: u64) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_event(AnyEvent::Float64(f64::from_bits(bits)));
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_i64_bits(&mut self, bits: u64) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_event(AnyEvent::BigInt64(bits as i64));
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_bool(&mut self, value: bool) -> core::result::Result<(), CodecError> {
        let ev = if value { AnyEvent::True } else { AnyEvent::False };
        let res = self.sink.any_event(ev);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_str(&mut self, value: core_v1::Span) -> core::result::Result<(), CodecError> {
        let ws = self.wire_str(value)?;
        let res = self.sink.any_event(AnyEvent::String(ws));
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_bytes(&mut self, value: core_v1::Span) -> core::result::Result<(), CodecError> {
        let wb = self.wire_bytes(value);
        let res = self.sink.any_event(AnyEvent::Binary(wb));
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_begin_object(&mut self, count: usize) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_event(AnyEvent::BeginObject(count));
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_object_key(&mut self, key: core_v1::Span) -> core::result::Result<(), CodecError> {
        let ws = self.wire_str(key)?;
        let res = self.sink.any_event(AnyEvent::ObjectKey(ws));
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_begin_array(&mut self, count: usize) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_event(AnyEvent::BeginArray(count));
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_end_container(&mut self) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_event(AnyEvent::EndContainer);
        self.forward(res)
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_any_finish(&mut self, range: core_v1::Span) -> core::result::Result<(), CodecError> {
        let res = self.sink.any_finish(range.start..range.end);
        match res {
            Ok(a) => {
                self.pending_any = Some(a);
                Ok(())
            }
            Err(e) => Err(self.abort(e)),
        }
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn begin_delete_client(&mut self, _client: u64, _count: usize) -> core::result::Result<(), CodecError> {
        Ok(())
    }

    #[cfg_attr(not(debug_assertions), inline(always))]
    fn on_delete_range(&mut self, client: u64, start: u64, end: u64) -> core::result::Result<(), CodecError> {
        let res = self.sink.delete_range(client, start..end);
        self.forward(res)
    }
}

/// Zero-allocation JSON validator whose acceptance set matches
/// `serde_json::from_str::<Any>`: unlike `IgnoredAny`, `deserialize_any`
/// invokes `serde_json`'s number range parsing and 128-level recursion limit.
struct JsonAnyValidator;

impl<'de> Deserialize<'de> for JsonAnyValidator {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct ValidatorVisitor;

        impl<'de> serde::de::Visitor<'de> for ValidatorVisitor {
            type Value = JsonAnyValidator;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("any valid JSON value")
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_bool<E>(self, _value: bool) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_i64<E>(self, _value: i64) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_u64<E>(self, _value: u64) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_f64<E>(self, _value: f64) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_str<E>(self, _value: &str) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_borrowed_str<E>(self, _value: &'de str) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_none<E>(self) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_unit<E>(self) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            fn visit_seq<V>(self, mut visitor: V) -> std::result::Result<Self::Value, V::Error>
            where
                V: serde::de::SeqAccess<'de>,
            {
                while visitor.next_element::<JsonAnyValidator>()?.is_some() {}
                Ok(JsonAnyValidator)
            }

            fn visit_map<V>(self, mut visitor: V) -> std::result::Result<Self::Value, V::Error>
            where
                V: serde::de::MapAccess<'de>,
            {
                while visitor.next_entry::<JsonKeyValidator, JsonAnyValidator>()?.is_some() {}
                Ok(JsonAnyValidator)
            }
        }

        deserializer.deserialize_any(ValidatorVisitor)
    }
}

struct JsonKeyValidator;

impl<'de> Deserialize<'de> for JsonKeyValidator {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct KeyVisitor;

        impl<'de> serde::de::Visitor<'de> for KeyVisitor {
            type Value = JsonKeyValidator;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a JSON object key string")
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_str<E>(self, _value: &str) -> std::result::Result<Self::Value, E> {
                Ok(JsonKeyValidator)
            }

            #[cfg_attr(not(debug_assertions), inline(always))]
            fn visit_borrowed_str<E>(self, _value: &'de str) -> std::result::Result<Self::Value, E> {
                Ok(JsonKeyValidator)
            }
        }

        deserializer.deserialize_str(KeyVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        super::{CrdtWriter, RawEncoder},
        *,
    };
    use crate::JwstCodecResult;

    #[derive(Default, Debug)]
    struct ProbeSink {
        structs: Vec<(Id, u64)>,
    }

    impl<'a> Sink<'a> for ProbeSink {
        type Any = ();
        type Content = ();
        type Output = Self;

        fn begin_client(&mut self, _client: u64, _count: usize) -> Result<()> {
            Ok(())
        }

        fn gc(&mut self, id: Id, len: u64) -> Result<()> {
            self.structs.push((id, len));
            Ok(())
        }

        fn skip(&mut self, id: Id, len: u64) -> Result<()> {
            self.structs.push((id, len));
            Ok(())
        }

        fn item(&mut self, id: Id, len: u64, _meta: ItemMeta<'a>, _content: Self::Content) -> Result<()> {
            self.structs.push((id, len));
            Ok(())
        }

        fn content_atom(&mut self, _atom: ContentAtom<'a>) -> Result<Self::Content> {
            Ok(())
        }

        fn json_start(&mut self, _count: usize) -> Result<()> {
            Ok(())
        }

        fn json_value(&mut self, _value: WireStr<'a>) -> Result<()> {
            Ok(())
        }

        fn json_finish(&mut self) -> Result<Self::Content> {
            Ok(())
        }

        fn any_content_start(&mut self, _count: usize) -> Result<()> {
            Ok(())
        }

        fn any_content_value(&mut self, _value: Self::Any) -> Result<()> {
            Ok(())
        }

        fn any_content_finish(&mut self) -> Result<Self::Content> {
            Ok(())
        }

        fn doc_content(&mut self, _guid: WireStr<'a>, _options: Self::Any) -> Result<Self::Content> {
            Ok(())
        }

        fn any_start(&mut self) -> Result<()> {
            Ok(())
        }

        fn any_event(&mut self, _event: AnyEvent<'a>) -> Result<()> {
            Ok(())
        }

        fn any_finish(&mut self, _range: Range<usize>) -> Result<Self::Any> {
            Ok(())
        }

        fn delete_range(&mut self, _client: u64, _range: Range<u64>) -> Result<()> {
            Ok(())
        }

        fn finish(self) -> Result<Self::Output> {
            Ok(self)
        }
    }

    struct Encoder(Vec<u8>);

    fn enc() -> Encoder {
        Encoder(Vec::new())
    }

    impl Encoder {
        fn write(mut self, f: impl FnOnce(&mut RawEncoder) -> JwstCodecResult) -> Self {
            let mut enc = RawEncoder::default();
            f(&mut enc).unwrap();
            self.0.extend_from_slice(&enc.into_inner());
            self
        }

        fn byte(self, b: u8) -> Self {
            self.write(|e| e.write_u8(b))
        }

        fn varu(self, n: u64) -> Self {
            self.write(|e| e.write_var_u64(n))
        }

        fn vstr(self, s: &str) -> Self {
            self.write(|e| e.write_var_string(s))
        }

        fn raw(mut self, bytes: &[u8]) -> Self {
            self.0.extend_from_slice(bytes);
            self
        }

        fn bytes(self) -> Vec<u8> {
            self.0
        }
    }

    enum ExpectedError {
        Codec(JwstCodecError),
        Resource(&'static str),
    }

    fn assert_decode_err(name: &str, input: &[u8], limits: DecodeLimits, expected: &ExpectedError) {
        let err = decode(input, ProbeSink::default(), limits).expect_err("decode should fail");
        match (&err, expected) {
            (Error::Codec(err), ExpectedError::Codec(expected)) => assert_eq!(err, expected, "{name}"),
            (Error::Resource(err), ExpectedError::Resource(expected)) => assert_eq!(err, expected, "{name}"),
            _ => panic!("{name}: unexpected error {err:?}"),
        }
    }

    /// One client (id 0, clock 0) holding a single item whose parent is the
    /// root `r`, followed by an empty delete set.
    fn root_item_update(info: u8, payload: Vec<u8>) -> Vec<u8> {
        enc()
            .varu(1)
            .varu(1)
            .varu(0)
            .varu(0)
            .byte(info)
            .varu(1)
            .vstr("r")
            .raw(&payload)
            .varu(0)
            .bytes()
    }

    /// `depth` arrays nested around a single null, e.g. depth 1 is `[null]`.
    fn nested_arrays(depth: usize) -> Vec<u8> {
        let mut inner = vec![126];
        for _ in 0..depth {
            inner = enc().byte(117).varu(1).raw(&inner).bytes();
        }
        inner
    }

    fn limited(f: impl FnOnce(&mut DecodeLimits)) -> DecodeLimits {
        let mut limits = DecodeLimits::UNRESTRICTED;
        f(&mut limits);
        limits
    }

    #[test]
    fn test_struct_dispatch_and_clock() {
        // one client with three structs: gc, skip, item with deleted content
        let input = enc()
            .varu(1) // clients
            .varu(3) // structs
            .varu(7) // client id
            .varu(10) // start clock
            .byte(0)
            .varu(5) // gc, len 5
            .byte(10)
            .varu(3) // skip, len 3
            .byte(1)
            .varu(1)
            .vstr("r")
            .varu(4) // item: root parent, deleted len 4
            .varu(0) // delete clients
            .bytes();

        let decoded = decode(&input, ProbeSink::default(), DecodeLimits::UNRESTRICTED).unwrap();
        assert_eq!(
            decoded.structs,
            [(Id::new(7, 10), 5), (Id::new(7, 15), 3), (Id::new(7, 18), 4)]
        );
    }

    #[test]
    fn test_decode_errors() {
        let max_clock = enc().varu(u64::MAX).bytes();
        let cases: [(&str, Vec<u8>, ExpectedError); 13] = [
            (
                "truncated varint",
                vec![0x80],
                ExpectedError::Codec(JwstCodecError::UpdateInvalid(nom::Err::Incomplete(nom::Needed::new(2)))),
            ),
            (
                "truncated info byte",
                vec![1, 1, 0, 0],
                ExpectedError::Codec(JwstCodecError::IncompleteDocument(
                    "failed to fill whole buffer".to_owned(),
                )),
            ),
            (
                "truncated buffer",
                root_item_update(4, vec![5, b'a', b'b']),
                ExpectedError::Codec(JwstCodecError::IncompleteDocument("buffer exceeds update".to_owned())),
            ),
            (
                "zero-length gc",
                vec![1, 1, 0, 0, 0, 0, 0],
                ExpectedError::Codec(JwstCodecError::IncompleteDocument("zero-length struct".to_owned())),
            ),
            (
                "struct clock overflow",
                enc().varu(1).varu(1).varu(7).raw(&max_clock).byte(0).varu(1).bytes(),
                ExpectedError::Codec(JwstCodecError::StructClockInvalid {
                    expect: u64::MAX,
                    actually: u64::MAX,
                }),
            ),
            (
                "trailing bytes",
                vec![0, 0, 1],
                ExpectedError::Codec(JwstCodecError::UpdateNotFullyConsumed(1)),
            ),
            (
                "delete range end overflow",
                enc().varu(0).varu(1).varu(0).varu(1).raw(&max_clock).varu(1).bytes(),
                ExpectedError::Codec(JwstCodecError::StructClockInvalid {
                    expect: u64::MAX,
                    actually: u64::MAX,
                }),
            ),
            (
                "invalid embed json",
                root_item_update(5, enc().vstr("{").bytes()),
                ExpectedError::Codec(JwstCodecError::DamagedDocumentJson),
            ),
            (
                "trailing data after embed json",
                root_item_update(5, enc().vstr("[1] x").bytes()),
                ExpectedError::Codec(JwstCodecError::DamagedDocumentJson),
            ),
            (
                "invalid format json",
                root_item_update(6, enc().vstr("k").vstr("oops").bytes()),
                ExpectedError::Codec(JwstCodecError::DamagedDocumentJson),
            ),
            (
                "unknown content tag",
                root_item_update(11, vec![]),
                ExpectedError::Codec(JwstCodecError::IncompleteDocument(
                    "Unknown content type: 11".to_owned(),
                )),
            ),
            (
                "unknown any tag",
                root_item_update(8, enc().varu(1).byte(100).bytes()),
                ExpectedError::Codec(JwstCodecError::IncompleteDocument("unknown Any tag: 27".to_owned())),
            ),
            (
                "unknown y type",
                root_item_update(7, enc().varu(7).bytes()),
                ExpectedError::Codec(JwstCodecError::IncompleteDocument("Unknown y type: 7".to_owned())),
            ),
        ];

        for (name, input, expected) in &cases {
            assert_decode_err(name, input, DecodeLimits::UNRESTRICTED, expected);
        }
    }

    #[test]
    fn test_decode_limits() {
        let two_clients = enc()
            .varu(2) // clients
            .varu(0)
            .varu(1)
            .varu(0) // client 1: no structs
            .varu(0)
            .varu(2)
            .varu(0) // client 2: no structs
            .varu(0) // delete clients
            .bytes();
        let two_structs = enc()
            .varu(1) // clients
            .varu(2) // structs
            .varu(0)
            .varu(0) // client 0 @ 0
            .byte(0)
            .varu(1) // gc, len 1
            .byte(0)
            .varu(1) // gc, len 1
            .varu(0) // delete clients
            .bytes();
        let hello = root_item_update(4, enc().vstr("hello").bytes());
        let array_of_null = root_item_update(8, enc().varu(1).raw(&nested_arrays(1)).bytes());

        // values exactly at the limit pass
        assert!(decode(&two_clients, ProbeSink::default(), limited(|l| l.max_clients = 2)).is_ok());
        assert!(decode(&two_structs, ProbeSink::default(), limited(|l| l.max_structs = 2)).is_ok());
        assert!(decode(&hello, ProbeSink::default(), limited(|l| l.max_content_bytes = 6)).is_ok());
        assert!(decode(&array_of_null, ProbeSink::default(), limited(|l| l.max_any_depth = 1)).is_ok());

        let cases: [(&str, Vec<u8>, DecodeLimits, ExpectedError); 9] = [
            (
                "clients over limit",
                two_clients,
                limited(|l| l.max_clients = 1),
                ExpectedError::Resource("clients"),
            ),
            (
                "delete clients over limit",
                enc().varu(0).varu(2).varu(1).varu(0).varu(2).varu(0).bytes(),
                limited(|l| l.max_clients = 1),
                ExpectedError::Resource("delete clients"),
            ),
            (
                "structs over limit",
                two_structs,
                limited(|l| l.max_structs = 1),
                ExpectedError::Resource("structs"),
            ),
            // the struct count itself already contributes one collection entry
            (
                "json entries over limit",
                root_item_update(2, enc().varu(2).bytes()),
                limited(|l| l.max_collection_entries = 1),
                ExpectedError::Resource("collection entries"),
            ),
            (
                "any entries over limit",
                root_item_update(8, enc().varu(2).bytes()),
                limited(|l| l.max_collection_entries = 1),
                ExpectedError::Resource("collection entries"),
            ),
            (
                "delete ranges over limit",
                enc()
                    .varu(0) // clients
                    .varu(1) // delete clients
                    .varu(5) // client id
                    .varu(2) // ranges
                    .varu(0)
                    .varu(1)
                    .varu(2)
                    .varu(1)
                    .bytes(),
                limited(|l| l.max_collection_entries = 1),
                ExpectedError::Resource("collection entries"),
            ),
            (
                "content bytes over limit",
                hello,
                limited(|l| l.max_content_bytes = 5),
                ExpectedError::Resource("content bytes"),
            ),
            (
                "any nesting over limit",
                array_of_null,
                limited(|l| l.max_any_depth = 0),
                ExpectedError::Resource("Any nesting depth"),
            ),
            (
                "deep any nesting over limit",
                root_item_update(8, enc().varu(1).raw(&nested_arrays(2)).bytes()),
                limited(|l| l.max_any_depth = 1),
                ExpectedError::Resource("Any nesting depth"),
            ),
        ];

        for (name, input, limits, expected) in &cases {
            assert_decode_err(name, input, *limits, expected);
        }

        // limits are enforced before the payload is touched: an unrestricted
        // huge count reaches the truncated payload instead of a
        // resource error
        let huge_json = root_item_update(2, enc().varu(1 << 40).bytes());
        assert_decode_err(
            "huge json count unrestricted",
            &huge_json,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::IncompleteDocument(
                "content entries: 1099511627776 declared, at most 1 fit in the rest of the update".to_owned(),
            )),
        );
        assert_decode_err(
            "huge json count restricted",
            &huge_json,
            limited(|l| l.max_collection_entries = 5),
            &ExpectedError::Resource("collection entries"),
        );
        // a count that overflows the cumulative entry counter is a resource
        // error even when unrestricted
        assert_decode_err(
            "json count usize overflow",
            &root_item_update(2, enc().varu(u64::MAX).bytes()),
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Resource("collection entries"),
        );
    }

    #[test]
    fn test_counts_must_fit_in_input() {
        // every declared count is checked against the bytes left before a
        // sink can reserve memory for it
        let cases: [(&str, Vec<u8>); 7] = [
            ("clients", enc().varu(1 << 30).bytes()),
            ("structs", enc().varu(1).varu(1 << 30).varu(0).varu(0).bytes()),
            ("delete clients", enc().varu(0).varu(1 << 30).bytes()),
            ("delete ranges", enc().varu(0).varu(1).varu(0).varu(1 << 30).bytes()),
            ("content entries", root_item_update(8, enc().varu(1 << 30).bytes())),
            (
                "Any array entries",
                root_item_update(8, enc().varu(1).byte(117).varu(1 << 30).bytes()),
            ),
            (
                "Any object entries",
                root_item_update(8, enc().varu(1).byte(118).varu(1 << 30).bytes()),
            ),
        ];
        for (name, input) in &cases {
            let err = decode(input, ProbeSink::default(), DecodeLimits::UNRESTRICTED).expect_err(name);
            assert!(
                matches!(&err, Error::Codec(JwstCodecError::IncompleteDocument(message)) if message.starts_with(name)),
                "{name}: {err:?}"
            );
        }
    }

    #[test]
    fn test_duplicate_client_block_rejected() {
        let block = |clock: u64| enc().varu(1).varu(9).varu(clock).byte(0).varu(1).bytes();
        let input = enc().varu(2).raw(&block(0)).raw(&block(1)).varu(0).bytes();
        assert_decode_err(
            "duplicate client",
            &input,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::IncompleteDocument(
                "duplicate struct block for client 9".to_owned(),
            )),
        );

        let distinct = enc()
            .varu(2)
            .raw(&block(0))
            .raw(&enc().varu(1).varu(8).varu(0).byte(0).varu(1).bytes())
            .varu(0)
            .bytes();
        assert!(decode(&distinct, ProbeSink::default(), DecodeLimits::UNRESTRICTED).is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_deep_any_does_not_recurse() {
        // far deeper than any thread stack could recurse
        let depth = 200_000;
        // built directly: `nested_arrays` copies the buffer once per level
        let mut nested = [117u8, 1].repeat(depth);
        nested.push(126);
        let input = root_item_update(8, enc().varu(1).raw(&nested).bytes());
        assert!(decode(&input, ProbeSink::default(), DecodeLimits::UNRESTRICTED).is_ok());
        assert!(decode(&input, ProbeSink::default(), limited(|l| l.max_any_depth = depth)).is_ok());
        assert_decode_err(
            "deep any",
            &input,
            DecodeLimits::UPDATE,
            &ExpectedError::Resource("Any nesting depth"),
        );
    }

    #[test]
    fn test_error_detail_parity_with_main() {
        // 1. Invalid UTF-8 across early-validated (Root), immediate (String),
        //    and take_early_str cache-miss paths.
        let bad_early = [b'a', 0xff];
        let early_msg = std::str::from_utf8(std::hint::black_box(&bad_early[..]))
            .unwrap_err()
            .to_string();
        let invalid_root = enc()
            .varu(1)
            .varu(1)
            .varu(7)
            .varu(0)
            .byte(4)
            .varu(1)
            .varu(bad_early.len() as u64)
            .raw(&bad_early)
            .varu(1)
            .vstr("x")
            .varu(0)
            .bytes();
        assert_decode_err(
            "invalid root utf-8",
            &invalid_root,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::IncompleteDocument(early_msg)),
        );

        let bad_str = [0xe2, 0x82];
        let str_msg = std::str::from_utf8(std::hint::black_box(&bad_str[..]))
            .unwrap_err()
            .to_string();
        let invalid_str = root_item_update(4, enc().varu(bad_str.len() as u64).raw(&bad_str).bytes());
        assert_decode_err(
            "invalid content utf-8",
            &invalid_str,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::IncompleteDocument(str_msg)),
        );

        let raw_miss = b"ok\xfftail";
        let miss_msg = std::str::from_utf8(std::hint::black_box(&raw_miss[2..]))
            .unwrap_err()
            .to_string();
        let mut adapter = Adapter::new(raw_miss, ProbeSink::default());
        assert_eq!(
            adapter
                .take_early_str(0, core_v1::Span { start: 0, end: 2 })
                .unwrap()
                .value,
            "ok"
        );
        match adapter.take_early_str(0, core_v1::Span { start: 2, end: 7 }) {
            Err(e) => assert_eq!(e, CodecError::SinkAborted),
            Ok(_) => panic!("take_early_str cache miss should fail on invalid utf-8"),
        }
        match adapter.error.take().unwrap() {
            Error::Codec(JwstCodecError::IncompleteDocument(msg)) => assert_eq!(msg, miss_msg),
            other => panic!("unexpected miss error: {other:?}"),
        }

        // 2. Buffer length 3-way distinction: BufferTooLarge vs
        //    BufferLengthOverflow vs BufferExceedsUpdate.
        assert!(matches!(
            map_core_error(CodecError::BufferTooLarge),
            Error::Codec(JwstCodecError::IncompleteDocument(ref msg)) if msg == "buffer too large"
        ));
        #[cfg(target_pointer_width = "32")]
        {
            for oversized in [u64::MAX, u32::MAX as u64 + 1] {
                let buf_too_large = root_item_update(3, enc().varu(oversized).bytes());
                assert_decode_err(
                    "buffer too large on 32-bit at non-zero pos",
                    &buf_too_large,
                    DecodeLimits::UNRESTRICTED,
                    &ExpectedError::Codec(JwstCodecError::IncompleteDocument("buffer too large".to_owned())),
                );
            }
        }
        let buf_len_overflow = root_item_update(3, enc().varu(usize::MAX as u64).bytes());
        assert_decode_err(
            "buffer length overflow at non-zero pos",
            &buf_len_overflow,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::IncompleteDocument("buffer length overflow".to_owned())),
        );
        let buf_exceeds = root_item_update(3, vec![10, 1, 2]);
        assert_decode_err(
            "buffer exceeds update",
            &buf_exceeds,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::IncompleteDocument("buffer exceeds update".to_owned())),
        );

        // 3. Varint UnexpectedEof (`Incomplete(Needed::new(rem + 1))`) at
        //    non-zero offsets.
        let upd_varint_eof = vec![1, 1, 7, 0x80]; // 1 byte remaining at failed clock field
        assert_decode_err(
            "update unsigned varint eof at non-zero offset",
            &upd_varint_eof,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::UpdateInvalid(nom::Err::Incomplete(nom::Needed::new(2)))),
        );
        let mut any_signed_eof = root_item_update(8, enc().varu(1).byte(125).bytes());
        any_signed_eof.pop();
        any_signed_eof.extend_from_slice(&[0x80, 0x80]);
        assert_decode_err(
            "any signed varint eof at non-zero offset",
            &any_signed_eof,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::UpdateInvalid(nom::Err::Incomplete(nom::Needed::new(3)))),
        );

        // 4. Varint VarintOverflow (`Failure(Error { input: rem, code: TooLarge
        //    })`) at non-zero offsets.
        let overflow_u64 = [0xffu8; 11];
        let upd_overflow = enc().varu(1).varu(1).varu(7).raw(&overflow_u64).bytes();
        assert_decode_err(
            "update unsigned varint overflow at non-zero offset",
            &upd_overflow,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::UpdateInvalid(nom::Err::Failure(
                nom::error::Error::new(overflow_u64.len(), nom::error::ErrorKind::TooLarge),
            ))),
        );
        let any_signed_overflow = root_item_update(8, enc().varu(1).byte(125).raw(&overflow_u64).bytes());
        // Overflow slice includes trailing `varu(0)` delete_clients byte => 12
        // bytes remain from signed varint start.
        assert_decode_err(
            "any signed varint overflow at non-zero offset",
            &any_signed_overflow,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::UpdateInvalid(nom::Err::Failure(
                nom::error::Error::new(overflow_u64.len() + 1, nom::error::ErrorKind::TooLarge),
            ))),
        );
    }

    #[test]
    fn test_zero_length_items_skipped_across_all_pipelines() {
        use crate::{
            Doc, DocOptions, ReadDoc, StateVector, Update, diff_update_v1, encode_state_vector_from_update_v1,
            merge_updates_v1, revert_update_v1, validate_update_v1,
        };

        // Reproduce the historical Yjs ZWJ-emoji + deleted empty
        // ContentString("") + deleted colliding "\n" pattern inside a real
        // nested `ContentType(Y.Text)` stored under `Y.Map` `"blocks"["b1"]`,
        // with an interleaved map key update splitting `seq_ranges` and a
        // zero-length item sharing clock 9 strictly inside DeleteSet `[4, 11)`.
        let emoji_prefix = "😮\u{200d}"; // 3 UTF-16 code units: clocks 4..7
        let emoji_suffix = "💨"; // 2 UTF-16 code units: clocks 7..9

        for (label, zero_tag) in [("ContentString(\"\")", 4u8), ("ContentDeleted(0)", 1u8)] {
            let update = enc()
                .varu(1) // 1 client
                // Client 1 (start_clock = 0, 9 structs total -> 8 emitted):
                //  0..1:  blocks["b1"] = ContentType(Y.Text, kind=2)
                //  1..3:  nested Y.Text (parent=Item((1,0))) "hi"
                //  3..4:  meta["k"] = "v" (splits seq_ranges)
                //  4..7:  nested Y.Text emoji_prefix with origin_left=(1,2)
                //  7..9:  nested Y.Text emoji_suffix with origin_left=(1,6)
                //  9..9:  zero-len item with origin_left=(1,8), origin_right=None
                //         (adjacent outer end of [4, 9), strictly inside DS [4, 11))
                //  9..10: meta["k2"] = "w" (non-colliding map entry at clock 9)
                //  10..11: nested Y.Text "\n" with origin_left=(1,8) (deleted by
                //          DS [4, 11), no dependents, matching empty-string.bin)
                //  11..12: root "t" "!" (independent root text)
                .varu(9)
                .varu(1)
                .varu(0)
                // 0..1: blocks["b1"] = Y.Text (tag=7, parent_sub="b1", type_ref=2)
                .byte(0x27)
                .varu(1)
                .vstr("blocks")
                .vstr("b1")
                .varu(2)
                // 1..3: nested Y.Text "hi" (parent=Item((1,0)), no parent_sub)
                .byte(0x04)
                .varu(0)
                .varu(1)
                .varu(0)
                .vstr("hi")
                // 3..4: interleaved map entry meta["k"] = "v"
                .byte(0x24)
                .varu(1)
                .vstr("meta")
                .vstr("k")
                .vstr("v")
                // 4..7: nested Y.Text emoji_prefix (origin_left=(1,2))
                .byte(0x84)
                .varu(1)
                .varu(2)
                .vstr(emoji_prefix)
                // 7..9: nested Y.Text emoji_suffix (origin_left=(1,6))
                .byte(0x84)
                .varu(1)
                .varu(6)
                .vstr(emoji_suffix)
                // 9..9: zero-length item with origin_left=(1,8) (adjacent end of [4,9))
                .byte(0x80 | zero_tag)
                .varu(1)
                .varu(8)
                .varu(0)
                // 9..10: non-colliding map entry meta["k2"] = "w"
                .byte(0x24)
                .varu(1)
                .vstr("meta")
                .vstr("k2")
                .vstr("w")
                // 10..11: colliding "\n" (origin_left=(1,8)), deleted by DS [4, 11)
                .byte(0x84)
                .varu(1)
                .varu(8)
                .vstr("\n")
                // 11..12: root "t" "!"
                .byte(0x04)
                .varu(1)
                .vstr("t")
                .vstr("!")
                // DeleteSet: client 1 [4, 11) strictly covers clock 9 and deletes 10.
                .varu(1)
                .varu(1)
                .varu(1)
                .varu(4)
                .varu(7)
                .bytes();

            // 1. Raw probe sink sees only the 8 positive-length structs.
            let probed = decode(&update, ProbeSink::default(), DecodeLimits::UNRESTRICTED).expect(label);
            assert_eq!(
                probed.structs,
                [
                    (Id::new(1, 0), 1),
                    (Id::new(1, 1), 2),
                    (Id::new(1, 3), 1),
                    (Id::new(1, 4), 3),
                    (Id::new(1, 7), 2),
                    (Id::new(1, 9), 1),
                    (Id::new(1, 10), 1),
                    (Id::new(1, 11), 1),
                ],
                "{label}"
            );

            // 2. Wire validator & state-vector extractor.
            validate_update_v1(&update).expect(label);
            let sv_bytes = encode_state_vector_from_update_v1(&update).expect(label);
            let sv = StateVector::decode_v1(&sv_bytes).unwrap();
            assert_eq!(sv.get(&1), 12, "{label}");

            // 3. Diff extractor at empty SV, mid-client SV (clock 9), and full
            //    SV.
            let diff_all = diff_update_v1(&update, &StateVector::default().encode_v1().unwrap()).expect(label);
            let mut mid_sv = StateVector::default();
            mid_sv.set_max(1, 9);
            let diff_mid = diff_update_v1(&update, &mid_sv.encode_v1().unwrap()).expect(label);
            validate_update_v1(&diff_mid).expect(label);
            let diff_done = diff_update_v1(&update, &sv.encode_v1().unwrap()).expect(label);
            let decoded_done = Update::decode_v1(&diff_done).expect(label);
            assert!(decoded_done.structs.is_empty(), "{label}");

            // 4. Update decode/encode + merge_updates_v1 strip zero-length
            //    items.
            let decoded = Update::decode_v1(&update).expect(label);
            assert_eq!(decoded.structs.get(&1).unwrap().len(), 8, "{label}");
            let merged = merge_updates_v1([&update]).expect(label).encode_v1().unwrap();
            let merged_probe = decode(&merged, ProbeSink::default(), DecodeLimits::UNRESTRICTED).expect(label);
            assert_eq!(merged_probe.structs, probed.structs, "{label}");

            // 5. ReadDoc snapshot reader.
            let read_doc = ReadDoc::from_full_update_v1(update.clone()).expect(label);
            assert_eq!(read_doc.text("t").unwrap().to_string(), "!", "{label}");

            // 6. Doc integration, mid-SV diff application, and revert_update_v1
            //    (wrapped in loom_model! so Loom CI runs these checks too).
            let prefix_only = enc()
                .varu(1)
                .varu(5)
                .varu(1)
                .varu(0)
                .byte(0x27)
                .varu(1)
                .vstr("blocks")
                .vstr("b1")
                .varu(2)
                .byte(0x04)
                .varu(0)
                .varu(1)
                .varu(0)
                .vstr("hi")
                .byte(0x24)
                .varu(1)
                .vstr("meta")
                .vstr("k")
                .vstr("v")
                .byte(0x84)
                .varu(1)
                .varu(2)
                .vstr(emoji_prefix)
                .byte(0x84)
                .varu(1)
                .varu(6)
                .vstr(emoji_suffix)
                .varu(0)
                .bytes();
            let update_clone = update.clone();
            let diff_all_clone = diff_all.clone();
            let diff_mid_clone = diff_mid.clone();
            let sv_clone = sv.clone();
            crate::loom_model!({
                let read_b1 = |doc: &Doc| {
                    doc.get_or_create_map("blocks")
                        .unwrap()
                        .get("b1")
                        .and_then(|v| match v {
                            crate::Value::Text(t) => Some(t.to_string()),
                            _ => None,
                        })
                };
                let mut doc = Doc::with_options(DocOptions {
                    client_id: 100,
                    ..Default::default()
                });
                doc.apply_update_from_binary_v1(&update_clone).expect(label);
                assert_eq!(read_b1(&doc), Some("hi".to_owned()), "{label}");
                assert_eq!(doc.get_or_create_text("t").unwrap().to_string(), "!", "{label}");
                assert_eq!(doc.get_state_vector(), sv_clone, "{label}");

                let mut doc_from_diff = Doc::with_options(DocOptions {
                    client_id: 99,
                    ..Default::default()
                });
                doc_from_diff.apply_update_from_binary_v1(&diff_all_clone).expect(label);
                assert_eq!(read_b1(&doc_from_diff), Some("hi".to_owned()), "{label}");

                let mut doc_mid = Doc::with_options(DocOptions {
                    client_id: 98,
                    ..Default::default()
                });
                doc_mid.apply_update_from_binary_v1(&prefix_only).expect(label);
                doc_mid.apply_update_from_binary_v1(&diff_mid_clone).expect(label);
                assert_eq!(read_b1(&doc_mid), Some("hi".to_owned()), "{label}");
                assert_eq!(doc_mid.get_state_vector(), sv_clone, "{label}");

                let revert = revert_update_v1(&update_clone, &prefix_only).expect(label);
                doc.apply_update_from_binary_v1(&revert).expect(label);
                assert_eq!(
                    read_b1(&doc),
                    Some(format!("hi{emoji_prefix}{emoji_suffix}")),
                    "{label}"
                );
            });
        }

        // Positive control for non-splitting surrogate-pair boundary inside a
        // proven ContentType(Y.Text): `😀` (1..3) followed by adjacent deleted
        // zero-length `ContentDeleted(0)` with `origin_left=(1,2)` and
        // non-colliding map entry at clock 3 yields `"😀"` and SV `{1: 4}`.
        let emoji_boundary_ok = enc()
            .varu(1)
            .varu(4)
            .varu(1)
            .varu(0)
            .byte(0x27)
            .varu(1)
            .vstr("blocks")
            .vstr("b1")
            .varu(2)
            .byte(0x04)
            .varu(0)
            .varu(1)
            .varu(0)
            .vstr("😀")
            .byte(0x81)
            .varu(1)
            .varu(2)
            .varu(0)
            .byte(0x24)
            .varu(1)
            .vstr("meta")
            .vstr("k")
            .vstr("v")
            .varu(0)
            .bytes();
        let _emoji_read = ReadDoc::from_full_update_v1(emoji_boundary_ok.clone()).unwrap();
        crate::loom_model!({
            let mut doc = Doc::with_options(DocOptions {
                client_id: 101,
                ..Default::default()
            });
            doc.apply_update_from_binary_v1(&emoji_boundary_ok).unwrap();
            assert_eq!(
                doc.get_or_create_map("blocks")
                    .unwrap()
                    .get("b1")
                    .and_then(|v| match v {
                        crate::Value::Text(t) => Some(t.to_string()),
                        _ => None,
                    }),
                Some("😀".to_owned())
            );
            assert_eq!(doc.get_state_vector().get(&1), 4);
        });

        // Unsafe / unproven / non-YText / live / colliding zero-length forms
        // MUST remain rejected with "zero-length struct".
        let zero_len_err = ExpectedError::Codec(JwstCodecError::IncompleteDocument("zero-length struct".to_owned()));
        let rejected: [(&str, Vec<u8>); 32] = [
            (
                "same-client later live item sharing skipped Z origin_left (Yjs 😀yx vs 😀xy)",
                enc()
                    .varu(1)
                    .varu(5)
                    .varu(10)
                    .varu(0)
                    .byte(0x27)
                    .varu(1)
                    .vstr("blocks")
                    .vstr("b1")
                    .varu(2)
                    .byte(0x04)
                    .varu(0)
                    .varu(10)
                    .varu(0)
                    .vstr("😀")
                    .byte(0x81)
                    .varu(10)
                    .varu(2)
                    .varu(0)
                    .byte(0x24)
                    .varu(1)
                    .vstr("meta")
                    .vstr("k")
                    .vstr("v")
                    .byte(0x84)
                    .varu(10)
                    .varu(2)
                    .vstr("x")
                    .varu(0)
                    .bytes(),
            ),
            (
                "cross-client live item sharing skipped Z origin_left",
                enc()
                    .varu(2)
                    .varu(4)
                    .varu(10)
                    .varu(0)
                    .byte(0x27)
                    .varu(1)
                    .vstr("blocks")
                    .vstr("b1")
                    .varu(2)
                    .byte(0x04)
                    .varu(0)
                    .varu(10)
                    .varu(0)
                    .vstr("😀")
                    .byte(0x81)
                    .varu(10)
                    .varu(2)
                    .varu(0)
                    .byte(0x24)
                    .varu(1)
                    .vstr("meta")
                    .vstr("k")
                    .vstr("v")
                    .varu(1)
                    .varu(5)
                    .varu(0)
                    .byte(0x84)
                    .varu(10)
                    .varu(2)
                    .vstr("x")
                    .varu(0)
                    .bytes(),
            ),
            (
                "2-hop live descendant of deleted colliding item sharing Z origin_left",
                enc()
                    .varu(1)
                    .varu(6)
                    .varu(10)
                    .varu(0)
                    .byte(0x27)
                    .varu(1)
                    .vstr("blocks")
                    .vstr("b1")
                    .varu(2)
                    .byte(0x04)
                    .varu(0)
                    .varu(10)
                    .varu(0)
                    .vstr("😀")
                    .byte(0x81)
                    .varu(10)
                    .varu(2)
                    .varu(0)
                    .byte(0x24)
                    .varu(1)
                    .vstr("meta")
                    .vstr("k")
                    .vstr("v")
                    .byte(0x81)
                    .varu(10)
                    .varu(2)
                    .varu(1)
                    .byte(0x84)
                    .varu(10)
                    .varu(4)
                    .vstr("w")
                    .varu(0)
                    .bytes(),
            ),
            (
                "non-adjacent Z where origin_left.clock != Z.clock - 1 (Z.lastId gap)",
                enc()
                    .varu(1)
                    .varu(4)
                    .varu(10)
                    .varu(0)
                    .byte(0x27)
                    .varu(1)
                    .vstr("blocks")
                    .vstr("b1")
                    .varu(2)
                    .byte(0x04)
                    .varu(0)
                    .varu(10)
                    .varu(0)
                    .vstr("a")
                    .byte(0x24)
                    .varu(1)
                    .vstr("meta")
                    .vstr("k")
                    .vstr("v")
                    .byte(0x81)
                    .varu(10)
                    .varu(1)
                    .varu(0)
                    .varu(0)
                    .bytes(),
            ),
            (
                "nested ContentType(Y.Text) with two consecutive zero-length items at same clock",
                vec![
                    1, 7, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 2, b'a', b'b', 0x24, 1, 1, b'm', 1, b'k',
                    1, b'v', 0x84, 1, 2, 1, b'c', 0x81, 1, 4, 0, 0x81, 1, 2, 0, 0x84, 1, 4, 1, b'd', 0,
                ],
            ),
            (
                "adjacent raw wire DS [2,3)+[3,4) leaves ContentString(\"\") live in Yjs",
                vec![
                    0x01, 0x06, 0x01, 0x00, 0x06, 0x01, 0x01, 0x74, 0x04, 0x62, 0x6f, 0x6c, 0x64, 0x04, 0x6e, 0x75,
                    0x6c, 0x6c, 0x46, 0x01, 0x00, 0x04, 0x62, 0x6f, 0x6c, 0x64, 0x04, 0x74, 0x72, 0x75, 0x65, 0x28,
                    0x01, 0x01, 0x6d, 0x01, 0x6b, 0x01, 0x77, 0x01, 0x76, 0x84, 0x01, 0x01, 0x00, 0x84, 0x01, 0x00,
                    0x01, 0x77, 0x84, 0x01, 0x03, 0x01, 0x61, 0x01, 0x01, 0x02, 0x02, 0x01, 0x03, 0x01,
                ],
            ),
            (
                "deleted ContentDeleted(0) right-anchor in Y.Array",
                vec![
                    0x01, 0x04, 0x0a, 0x00, 0x08, 0x01, 0x01, 0x74, 0x01, 0x77, 0x01, 0x61, 0x48, 0x0a, 0x00, 0x01,
                    0x77, 0x01, 0x62, 0x81, 0x0a, 0x01, 0x00, 0xc8, 0x0a, 0x01, 0x0a, 0x00, 0x01, 0x77, 0x01, 0x64,
                    0x00,
                ],
            ),
            (
                "nested ContentType(Y.Text) with adjacent raw wire DS [4,5)+[5,6)",
                vec![
                    1, 6, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 2, b'a', b'b', 0x24, 1, 1, b'm', 1, b'k',
                    1, b'v', 0x84, 1, 2, 1, b'c', 0x84, 1, 4, 0, 0x24, 1, 1, b'm', 1, b'j', 1, b'w', 1, 1, 2, 4, 1, 5,
                    1,
                ],
            ),
            (
                "nested ContentType(Y.Text) with same-clock colliding successor",
                vec![
                    1, 4, 1, 0, 0x27, 1, 1, b'b', 1, b't', 2, 0x04, 0, 1, 0, 1, b'a', 0x81, 1, 1, 0, 0x84, 1, 1, 1,
                    b'b', 0,
                ],
            ),
            (
                "live ContentString(\"\") pure ASCII next-insert anchor (bdXa vs bXda)",
                vec![
                    0x01, 0x04, 0x0a, 0x00, 0x04, 0x01, 0x01, 0x74, 0x01, 0x61, 0x44, 0x0a, 0x00, 0x01, 0x62, 0x84,
                    0x0a, 0x01, 0x00, 0xc4, 0x0a, 0x01, 0x0a, 0x00, 0x01, 0x64, 0x00,
                ],
            ),
            (
                "live ContentString(\"\") with DS [2,3) starting at clock 2 (Yjs leaves it live)",
                vec![
                    0x01, 0x04, 0x0a, 0x00, 0x04, 0x01, 0x01, 0x74, 0x01, 0x61, 0x44, 0x0a, 0x00, 0x01, 0x62, 0x84,
                    0x0a, 0x01, 0x00, 0xc4, 0x0a, 0x01, 0x0a, 0x00, 0x01, 0x64, 0x01, 0x0a, 0x01, 0x02, 0x01,
                ],
            ),
            (
                "live ContentString(\"\") between bold=true and bold=null (format cleanup barrier)",
                vec![
                    0x01, 0x04, 0x01, 0x00, 0x06, 0x01, 0x01, 0x74, 0x04, 0x62, 0x6f, 0x6c, 0x64, 0x04, 0x6e, 0x75,
                    0x6c, 0x6c, 0x46, 0x01, 0x00, 0x04, 0x62, 0x6f, 0x6c, 0x64, 0x04, 0x74, 0x72, 0x75, 0x65, 0xc4,
                    0x01, 0x01, 0x01, 0x00, 0x00, 0x84, 0x01, 0x00, 0x01, 0x61, 0x00,
                ],
            ),
            (
                "ContentDeleted(0) with origin_right present",
                enc()
                    .varu(1)
                    .varu(3)
                    .varu(1)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    .byte(0x41)
                    .varu(1)
                    .varu(0)
                    .varu(0)
                    .byte(0x84)
                    .varu(1)
                    .varu(0)
                    .vstr("b")
                    .varu(0)
                    .bytes(),
            ),
            (
                "origin_left splits inside UTF-16 surrogate pair (😀 at 0..2, ol=(1,0))",
                enc()
                    .varu(1)
                    .varu(3)
                    .varu(1)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("😀")
                    .byte(0x81)
                    .varu(1)
                    .varu(0)
                    .varu(0)
                    .byte(0x84)
                    .varu(1)
                    .varu(1)
                    .vstr("x")
                    .varu(0)
                    .bytes(),
            ),
            (
                "origin_right splits inside UTF-16 surrogate pair (😀 at 0..2, or=(1,1))",
                enc()
                    .varu(1)
                    .varu(3)
                    .varu(1)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("😀")
                    .byte(0x41)
                    .varu(1)
                    .varu(1)
                    .varu(0)
                    .byte(0x84)
                    .varu(1)
                    .varu(1)
                    .vstr("x")
                    .varu(0)
                    .bytes(),
            ),
            (
                "inbound Yjs incremental diff whose origin lies outside the block",
                vec![
                    0x01, 0x03, 0x01, 0x01, 0x84, 0x01, 0x00, 0x01, b'b', 0x84, 0x01, 0x01, 0x00, 0x84, 0x01, 0x01,
                    0x01, b'c', 0x00,
                ],
            ),
            ("explicit root ContentString(\"\")", root_item_update(4, vec![0])),
            ("explicit root ContentDeleted(0)", root_item_update(1, vec![0])),
            (
                "map key ContentAny([])",
                enc()
                    .varu(1)
                    .varu(2)
                    .varu(1)
                    .varu(0)
                    .byte(0x28)
                    .varu(1)
                    .vstr("m")
                    .vstr("k")
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    .varu(0)
                    .bytes(),
            ),
            (
                "map key ContentString(\"\")",
                enc()
                    .varu(1)
                    .varu(2)
                    .varu(1)
                    .varu(0)
                    .byte(0x24)
                    .varu(0)
                    .varu(1)
                    .varu(0)
                    .vstr("k")
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    .varu(0)
                    .bytes(),
            ),
            (
                "cross-client inherited map key ContentString(\"\")",
                enc()
                    .varu(2)
                    // client 2: zero-len inheriting map key from (1,0), then "a" to "t"
                    .varu(2)
                    .varu(2)
                    .varu(0)
                    .byte(0x84)
                    .varu(1)
                    .varu(0)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    // client 1: m["k"] = "v"
                    .varu(1)
                    .varu(1)
                    .varu(0)
                    .byte(0x24)
                    .varu(1)
                    .vstr("m")
                    .vstr("k")
                    .vstr("v")
                    .varu(0)
                    .bytes(),
            ),
            (
                "same-client inherited map key ContentString(\"\")",
                enc()
                    .varu(1)
                    .varu(2)
                    .varu(1)
                    .varu(0)
                    .byte(0x24)
                    .varu(1)
                    .vstr("m")
                    .vstr("k")
                    .vstr("v")
                    .byte(0x84)
                    .varu(1)
                    .varu(0)
                    .varu(0)
                    .varu(0)
                    .bytes(),
            ),
            (
                "2-hop cross-client inherited map key ContentString(\"\")",
                enc()
                    .varu(2)
                    // client 2: positive item inheriting (1,0) at (2,0..1), then zero-len at (2,1) inheriting (2,0)
                    .varu(2)
                    .varu(2)
                    .varu(0)
                    .byte(0x84)
                    .varu(1)
                    .varu(0)
                    .vstr("x")
                    .byte(0x84)
                    .varu(2)
                    .varu(0)
                    .varu(0)
                    // client 1: m["k"] = "v"
                    .varu(1)
                    .varu(1)
                    .varu(0)
                    .byte(0x24)
                    .varu(1)
                    .vstr("m")
                    .vstr("k")
                    .vstr("v")
                    .varu(0)
                    .bytes(),
            ),
            (
                "mixed block missing nested Item((3,0)) parent",
                enc()
                    .varu(1)
                    .varu(2)
                    .varu(2)
                    .varu(0)
                    .byte(0x04)
                    .varu(0)
                    .varu(3)
                    .varu(0)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    .varu(0)
                    .bytes(),
            ),
            (
                "mixed block missing origin_left=(3,0)",
                enc()
                    .varu(1)
                    .varu(2)
                    .varu(2)
                    .varu(0)
                    .byte(0x84)
                    .varu(3)
                    .varu(0)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    .varu(0)
                    .bytes(),
            ),
            (
                "mixed block missing origin_right=(3,0)",
                enc()
                    .varu(1)
                    .varu(3)
                    .varu(1)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    .byte(0xc4)
                    .varu(1)
                    .varu(0)
                    .varu(3)
                    .varu(0)
                    .varu(0)
                    .byte(0x84)
                    .varu(1)
                    .varu(0)
                    .vstr("b")
                    .varu(0)
                    .bytes(),
            ),
            (
                "ITEM_HAS_PARENT_SUB set alongside origin_left",
                enc()
                    .varu(1)
                    .varu(2)
                    .varu(1)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    .byte(0xa4)
                    .varu(1)
                    .varu(0)
                    .varu(0)
                    .varu(0)
                    .bytes(),
            ),
            (
                "inherited ContentAny([])",
                enc()
                    .varu(1)
                    .varu(2)
                    .varu(1)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    .byte(0x88)
                    .varu(1)
                    .varu(0)
                    .varu(0)
                    .varu(0)
                    .bytes(),
            ),
            (
                "inherited ContentJSON([])",
                enc()
                    .varu(1)
                    .varu(2)
                    .varu(1)
                    .varu(0)
                    .byte(0x04)
                    .varu(1)
                    .vstr("t")
                    .vstr("a")
                    .byte(0x82)
                    .varu(1)
                    .varu(0)
                    .varu(0)
                    .varu(0)
                    .bytes(),
            ),
            (
                "zero-length-only client start_clock=0",
                enc()
                    .varu(1)
                    .varu(1)
                    .varu(1)
                    .varu(0)
                    .byte(0x84)
                    .varu(1)
                    .varu(0)
                    .varu(0)
                    .varu(0)
                    .bytes(),
            ),
            (
                "zero-length-only client start_clock=7",
                enc()
                    .varu(1)
                    .varu(1)
                    .varu(1)
                    .varu(7)
                    .byte(0x84)
                    .varu(1)
                    .varu(6)
                    .varu(0)
                    .varu(0)
                    .bytes(),
            ),
            ("zero-length skip", vec![1, 1, 0, 0, 10, 0, 0]),
        ];
        for (name, bytes) in &rejected {
            assert_decode_err(name, bytes, DecodeLimits::UNRESTRICTED, &zero_len_err);
            assert!(
                ReadDoc::from_full_update_v1(bytes.clone()).is_err(),
                "{name}: ReadDoc must reject"
            );
            assert!(
                merge_updates_v1([bytes]).is_err(),
                "{name}: merge_updates_v1 must reject"
            );
        }

        // Clock boundary: a deleted zero-length ContentDeleted(0) at u64::MAX
        // inside a proven ContentType(Y.Text) succeeds, while a subsequent
        // non-colliding positive struct overflows with StructClockInvalid.
        let near_max = u64::MAX - 2;
        let at_max_ok = enc()
            .varu(1)
            .varu(3)
            .varu(1)
            .varu(near_max)
            .byte(0x27)
            .varu(1)
            .vstr("b")
            .vstr("t")
            .varu(2)
            .byte(0x04)
            .varu(0)
            .varu(1)
            .varu(near_max)
            .vstr("a")
            .byte(0x81)
            .varu(1)
            .varu(near_max + 1)
            .varu(0)
            .varu(0)
            .bytes();
        let probed_max = decode(&at_max_ok, ProbeSink::default(), DecodeLimits::UNRESTRICTED).unwrap();
        assert_eq!(
            probed_max.structs,
            [(Id::new(1, near_max), 1), (Id::new(1, near_max + 1), 1)]
        );

        let at_max_overflow = enc()
            .varu(1)
            .varu(4)
            .varu(1)
            .varu(near_max)
            .byte(0x27)
            .varu(1)
            .vstr("b")
            .vstr("t")
            .varu(2)
            .byte(0x04)
            .varu(0)
            .varu(1)
            .varu(near_max)
            .vstr("a")
            .byte(0x81)
            .varu(1)
            .varu(near_max + 1)
            .varu(0)
            .byte(0x24)
            .varu(1)
            .vstr("m")
            .vstr("k")
            .vstr("v")
            .varu(0)
            .bytes();
        assert_decode_err(
            "zero-length at u64::MAX followed by positive item overflows",
            &at_max_overflow,
            DecodeLimits::UNRESTRICTED,
            &ExpectedError::Codec(JwstCodecError::StructClockInvalid {
                expect: u64::MAX,
                actually: u64::MAX,
            }),
        );

        // Invalid UTF-8 in the parent name of a zero-length item is still
        // rejected with a UTF-8 error before zero-length handling.
        let bad_parent = enc()
            .varu(1)
            .varu(1)
            .varu(1)
            .varu(0)
            .byte(0x04)
            .varu(1)
            .varu(1)
            .byte(0xff)
            .varu(0)
            .varu(0)
            .bytes();
        let err = decode(&bad_parent, ProbeSink::default(), DecodeLimits::UNRESTRICTED).unwrap_err();
        assert!(
            matches!(&err, Error::Codec(JwstCodecError::IncompleteDocument(msg)) if msg.contains("invalid utf-8")),
            "expected utf-8 error, got {err:?}"
        );

        // `max_structs` still bounds zero-length items (no DoS bypass).
        let many_empty = enc()
            .varu(1)
            .varu(3)
            .varu(1)
            .varu(0)
            .byte(0x04)
            .varu(1)
            .vstr("t")
            .vstr("a")
            .byte(0x84)
            .varu(1)
            .varu(0)
            .varu(0)
            .byte(0x84)
            .varu(1)
            .varu(0)
            .varu(0)
            .varu(0)
            .bytes();
        let tight = DecodeLimits {
            max_structs: 2,
            ..DecodeLimits::UNRESTRICTED
        };
        assert_decode_err(
            "zero-length items count toward max_structs",
            &many_empty,
            tight,
            &ExpectedError::Resource("structs"),
        );

        // Cross-frame `merge_updates_v1` consistency: if Frame A strips a
        // deleted zero-length item at `ol=(10,1)` and Frame B adds a live
        // colliding item at `ol=(10,1)` (or a 2-hop dependent of a deleted
        // colliding item), `merge_updates_v1([A, B])` rejects the batch just
        // like single-frame decoding of `A+B`.
        let frame_a = enc()
            .varu(1)
            .varu(4)
            .varu(10)
            .varu(0)
            .byte(0x27)
            .varu(1)
            .vstr("b")
            .vstr("t")
            .varu(2)
            .byte(0x04)
            .varu(0)
            .varu(10)
            .varu(0)
            .vstr("a")
            .byte(0x81)
            .varu(10)
            .varu(1)
            .varu(0)
            .byte(0x24)
            .varu(1)
            .vstr("m")
            .vstr("k")
            .vstr("v")
            .varu(0)
            .bytes();
        let frame_b_live_collider = enc()
            .varu(1)
            .varu(1)
            .varu(10)
            .varu(3)
            .byte(0x84)
            .varu(10)
            .varu(1)
            .vstr("x")
            .varu(0)
            .bytes();
        assert!(
            crate::merge_updates_v1([frame_a.as_slice(), frame_b_live_collider.as_slice()]).is_err(),
            "merge_updates_v1 must reject cross-frame live collider sharing skipped zero-length origin_left"
        );
        // Reversed order `[B, A]` is also rejected.
        assert!(
            crate::merge_updates_v1([frame_b_live_collider.as_slice(), frame_a.as_slice()]).is_err(),
            "merge_updates_v1 must reject cross-frame live collider regardless of frame order"
        );
        // Cross-frame deleted single-clock collider with a 2-hop live
        // dependent in Frame B is rejected.
        let frame_b_deleted_collider_with_dep = enc()
            .varu(1)
            .varu(2)
            .varu(10)
            .varu(3)
            .byte(0x84)
            .varu(10)
            .varu(1)
            .vstr("x")
            .byte(0x84)
            .varu(10)
            .varu(3)
            .vstr("y")
            .varu(1)
            .varu(10)
            .varu(1)
            .varu(3)
            .varu(1)
            .bytes();
        assert!(
            crate::merge_updates_v1([frame_a.as_slice(), frame_b_deleted_collider_with_dep.as_slice()]).is_err(),
            "merge_updates_v1 must reject cross-frame 2-hop dependent of deleted collider"
        );
        // Cross-frame deleted single-clock collider with no dependents is
        // accepted cleanly.
        let frame_b_deleted_collider_clean = enc()
            .varu(1)
            .varu(1)
            .varu(10)
            .varu(3)
            .byte(0x84)
            .varu(10)
            .varu(1)
            .vstr("\n")
            .varu(1)
            .varu(10)
            .varu(1)
            .varu(3)
            .varu(1)
            .bytes();
        assert!(
            crate::merge_updates_v1([frame_a.as_slice(), frame_b_deleted_collider_clean.as_slice()]).is_ok(),
            "merge_updates_v1 must accept cross-frame unreferenced deleted single-clock collider"
        );
        // Overlap slicing across a skipped zero-length clock boundary:
        // Frame A ends with `Z = ContentDeleted(0)` at `(10,2)` (`ol=(10,1)`),
        // Frame B has `"ax"` at `(10,1..3)` (which crosses `(10,1) -> (10,2)`
        // and would slice into live `"x"` at `(10,2)` with synthesized
        // `ol=(10,1)`). Rejected in both frame orders.
        let frame_a_trailing_z = enc()
            .varu(1)
            .varu(3)
            .varu(10)
            .varu(0)
            .byte(0x27)
            .varu(1)
            .vstr("b")
            .vstr("t")
            .varu(2)
            .byte(0x04)
            .varu(0)
            .varu(10)
            .varu(0)
            .vstr("a")
            .byte(0x81)
            .varu(10)
            .varu(1)
            .varu(0)
            .varu(0)
            .bytes();
        let frame_b_overlap_ax = enc()
            .varu(1)
            .varu(1)
            .varu(10)
            .varu(1)
            .byte(0x04)
            .varu(0)
            .varu(10)
            .varu(0)
            .vstr("ax")
            .varu(0)
            .bytes();
        assert!(
            crate::merge_updates_v1([frame_a_trailing_z.as_slice(), frame_b_overlap_ax.as_slice()]).is_err(),
            "merge_updates_v1 must reject overlap crossing a skipped zero-length boundary"
        );
        assert!(
            crate::merge_updates_v1([frame_b_overlap_ax.as_slice(), frame_a_trailing_z.as_slice()]).is_err(),
            "merge_updates_v1 must reject overlap crossing a skipped zero-length boundary in reversed order"
        );
        // Same-client same-clock `(10,2)` successor with `ol=(10,1)`, even if
        // `ContentDeleted(1)`, must be unconditionally rejected in both frame
        // orders to match single-frame `emit_tracked_item`.
        let frame_b_same_clock_deleted = enc()
            .varu(1)
            .varu(1)
            .varu(10)
            .varu(2)
            .byte(0x81)
            .varu(10)
            .varu(1)
            .varu(1)
            .varu(0)
            .bytes();
        assert!(
            crate::merge_updates_v1([frame_a_trailing_z.as_slice(), frame_b_same_clock_deleted.as_slice()]).is_err(),
            "merge_updates_v1 must unconditionally reject same-clock successor with skipped origin_left"
        );
        assert!(
            crate::merge_updates_v1([frame_b_same_clock_deleted.as_slice(), frame_a_trailing_z.as_slice()]).is_err(),
            "merge_updates_v1 must unconditionally reject same-clock successor in reversed order"
        );
        // Cross-frame reference from another stripped zero-length item:
        // Frame 1 strips `Z1` at `(10,2)` with `ol=(10,1)`; Frame 2 has
        // deleted collider `C` at `(10,3)` (`ol=(10,1)`) followed by stripped
        // `Z2` at `(10,4)` with `ol=(10,3)` referencing `C`. Both frames pass
        // alone, while packed and `merge_updates_v1` in either order reject
        // (and removing `Z2` is an accepting control).
        let text_hdr: &[u8] = &[0x27, 1, 1, b'b', 1, b't', 2];
        let item_a: &[u8] = &[4, 0, 10, 0, 1, b'a'];
        let z1: &[u8] = &[0x81, 10, 1, 0];
        let map_kv: &[u8] = &[0x24, 1, 1, b'm', 1, b'k', 1, b'v'];
        let collider_c: &[u8] = &[0x81, 10, 1, 1];
        let z2: &[u8] = &[0x81, 10, 3, 0];
        let mk_frame = |items: &[&[u8]]| -> Vec<u8> {
            let mut bytes = vec![1, u8::try_from(items.len()).unwrap(), 10, 0];
            for item in items {
                bytes.extend_from_slice(item);
            }
            bytes.push(0);
            bytes
        };
        let ref_first = mk_frame(&[text_hdr, item_a, z1]);
        let ref_second = mk_frame(&[text_hdr, item_a, map_kv, collider_c, z2]);
        let ref_packed = mk_frame(&[text_hdr, item_a, z1, map_kv, collider_c, z2]);
        let ref_clean_second = mk_frame(&[text_hdr, item_a, map_kv, collider_c]);
        assert!(crate::Update::decode_v1(&ref_first).is_ok());
        assert!(crate::Update::decode_v1(&ref_second).is_ok());
        assert!(crate::Update::decode_v1(&ref_packed).is_err());
        assert!(crate::merge_updates_v1([&ref_first, &ref_clean_second]).is_ok());
        assert!(crate::merge_updates_v1([&ref_first, &ref_second]).is_err());
        assert!(crate::merge_updates_v1([&ref_second, &ref_first]).is_err());

        // Recovery contract (`gc: false` valid-struct preservation): if the
        // containing `Y.Text` is deleted in the DS, stripping the zero-length
        // item preserves unrelated same-clock map entries (`m.k = "v"`) and
        // `SV[10] = 3` rather than replicating Yjs 13.6.33's `gc: true`
        // `findIndexSS` struct-overwrite bug.
        let deleted_parent_with_zero = enc()
            .varu(1)
            .varu(4)
            .varu(10)
            .varu(0)
            .byte(0x27)
            .varu(1)
            .vstr("b")
            .vstr("t")
            .varu(2)
            .byte(0x04)
            .varu(0)
            .varu(10)
            .varu(0)
            .vstr("a")
            .byte(0x81)
            .varu(10)
            .varu(1)
            .varu(0)
            .byte(0x24)
            .varu(1)
            .vstr("m")
            .vstr("k")
            .vstr("v")
            .varu(1)
            .varu(10)
            .varu(1)
            .varu(0)
            .varu(1)
            .bytes();
        assert!(
            decode(
                &deleted_parent_with_zero,
                ProbeSink::default(),
                DecodeLimits::UNRESTRICTED
            )
            .is_ok()
        );
        #[cfg(not(loom))]
        {
            let mut doc = crate::Doc::default();
            doc.apply_update_from_binary_v1(&deleted_parent_with_zero).unwrap();
            let map_m = doc.get_or_create_map("m").unwrap();
            assert_eq!(map_m.get("k"), Some(crate::Value::Any(crate::Any::String("v".into()))));
            assert_eq!(doc.get_state_vector().get(&10), 3);
        }
    }
}
