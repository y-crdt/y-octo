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
}
