use std::ops::Range;

use serde::Deserialize;

use super::{CrdtReader, Id, JwstCodecError, JwstCodecResult, RawDecoder, item_flags};

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

// Smallest wire size of each declared entry. Counts are checked against the
// remaining input before anything is reserved for them, so a few bytes cannot
// make a sink allocate for millions of entries.
/// client block: struct count, client and clock
const MIN_CLIENT_BYTES: u64 = 3;
/// struct: info byte plus at least one more byte (length, parent or origin)
const MIN_STRUCT_BYTES: u64 = 2;
/// delete set client: client and range count
const MIN_DELETE_CLIENT_BYTES: u64 = 2;
/// delete range: start and length
const MIN_DELETE_RANGE_BYTES: u64 = 2;
/// JSON or Any content entry, or Any array element
const MIN_ENTRY_BYTES: u64 = 1;
/// Any object entry: key and value
const MIN_OBJECT_ENTRY_BYTES: u64 = 2;

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

struct Decoder<'a> {
    raw: RawDecoder<'a>,
    limits: DecodeLimits,
    structs: usize,
    entries: usize,
    content_bytes: usize,
}

pub(crate) fn decode<'a, S: Sink<'a>>(input: &'a [u8], sink: S, limits: DecodeLimits) -> Result<S::Output> {
    Decoder {
        raw: RawDecoder::new(input),
        limits,
        structs: 0,
        entries: 0,
        content_bytes: 0,
    }
    .decode(sink)
}

impl<'a> Decoder<'a> {
    fn decode<S: Sink<'a>>(mut self, mut sink: S) -> Result<S::Output> {
        let clients = Self::usize(self.raw.read_var_u64()?, "clients")?;
        if clients > self.limits.max_clients {
            return Err(Error::Resource("clients"));
        }
        self.check_fits(clients, MIN_CLIENT_BYTES, "clients")?;
        // Yjs writes each client once. Sinks key structs by client, so a
        // repeated block would silently replace the structs of the first one
        // (and leave them orphaned in a ReadDoc).
        let mut seen_clients = crate::doc::HashSet::default();
        for _ in 0..clients {
            let count = Self::usize(self.raw.read_var_u64()?, "structs")?;
            self.add_structs(count)?;
            self.add_entries(count)?;
            self.check_fits(count, MIN_STRUCT_BYTES, "structs")?;
            let client = self.raw.read_var_u64()?;
            if !seen_clients.insert(client) {
                return Err(
                    JwstCodecError::IncompleteDocument(format!("duplicate struct block for client {client}")).into(),
                );
            }
            let mut clock = self.raw.read_var_u64()?;
            sink.begin_client(client, count)?;
            for _ in 0..count {
                let id = Id::new(client, clock);
                clock = self.read_struct(&mut sink, id)?;
            }
        }

        let delete_clients = Self::usize(self.raw.read_var_u64()?, "delete clients")?;
        if delete_clients > self.limits.max_clients {
            return Err(Error::Resource("delete clients"));
        }
        self.check_fits(delete_clients, MIN_DELETE_CLIENT_BYTES, "delete clients")?;
        for _ in 0..delete_clients {
            let client = self.raw.read_var_u64()?;
            let count = Self::usize(self.raw.read_var_u64()?, "delete ranges")?;
            self.add_entries(count)?;
            self.check_fits(count, MIN_DELETE_RANGE_BYTES, "delete ranges")?;
            for _ in 0..count {
                let start = self.raw.read_var_u64()?;
                let len = self.raw.read_var_u64()?;
                let end = start.checked_add(len).ok_or(JwstCodecError::StructClockInvalid {
                    expect: start,
                    actually: u64::MAX,
                })?;
                if start != end {
                    sink.delete_range(client, start..end)?;
                }
            }
        }
        if !self.raw.is_empty() {
            return Err(JwstCodecError::UpdateNotFullyConsumed(self.raw.len() as usize).into());
        }
        sink.finish()
    }

    fn advance_clock(clock: u64, len: u64) -> Result<u64> {
        if len == 0 {
            return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()).into());
        }
        clock.checked_add(len).ok_or_else(|| {
            JwstCodecError::StructClockInvalid {
                expect: clock,
                actually: u64::MAX,
            }
            .into()
        })
    }

    fn read_struct<S: Sink<'a>>(&mut self, sink: &mut S, id: Id) -> Result<u64> {
        let struct_start = self.raw.position();
        let info = self.raw.read_info()?;
        let tag = info & 0b1_1111;
        match tag {
            0 => {
                let len = self.raw.read_var_u64()?;
                let next_clock = Self::advance_clock(id.clock, len)?;
                sink.gc(id, len)?;
                Ok(next_clock)
            }
            10 => {
                let len = self.raw.read_var_u64()?;
                let next_clock = Self::advance_clock(id.clock, len)?;
                sink.skip(id, len)?;
                Ok(next_clock)
            }
            _ => {
                let has_left = info & item_flags::ITEM_HAS_LEFT_ID != 0;
                let has_right = info & item_flags::ITEM_HAS_RIGHT_ID != 0;
                let explicit_parent = !has_left && !has_right;
                let origin_left = has_left.then(|| self.read_id()).transpose()?;
                let origin_right = has_right.then(|| self.read_id()).transpose()?;
                let parent = if explicit_parent {
                    if self.raw.read_var_u64()? == 1 {
                        WireParent::Root(self.read_str()?)
                    } else {
                        WireParent::Item(self.read_id()?)
                    }
                } else {
                    WireParent::Inherit
                };
                let parent_sub = if explicit_parent && info & item_flags::ITEM_HAS_PARENT_SUB != 0 {
                    Some(self.read_str()?)
                } else {
                    None
                };
                let content_start = self.raw.position();
                let (content, len) = self.read_content(sink, tag)?;
                let struct_end = self.raw.position();
                self.add_content_bytes(struct_end - content_start)?;
                let next_clock = Self::advance_clock(id.clock, len)?;
                sink.item(
                    id,
                    len,
                    ItemMeta {
                        origin_left,
                        origin_right,
                        parent,
                        parent_sub,
                        raw_range: struct_start..struct_end,
                    },
                    content,
                )?;
                Ok(next_clock)
            }
        }
    }

    fn read_content<S: Sink<'a>>(&mut self, sink: &mut S, tag: u8) -> Result<(S::Content, u64)> {
        match tag {
            1 => {
                let len = self.raw.read_var_u64()?;
                Ok((sink.content_atom(ContentAtom::Deleted(len))?, len))
            }
            2 => {
                let len = self.raw.read_var_u64()?;
                let count = Self::usize(len, "content entries")?;
                self.add_entries(count)?;
                self.check_fits(count, MIN_ENTRY_BYTES, "content entries")?;
                sink.json_start(count)?;
                for _ in 0..count {
                    sink.json_value(self.read_str()?)?;
                }
                Ok((sink.json_finish()?, len))
            }
            3 => Ok((sink.content_atom(ContentAtom::Binary(self.read_bytes()?))?, 1)),
            4 => {
                let value = self.read_str()?;
                let len = value.value.encode_utf16().count() as u64;
                Ok((sink.content_atom(ContentAtom::String(value))?, len))
            }
            5 => {
                let value = self.read_json()?;
                Ok((sink.content_atom(ContentAtom::Embed(value))?, 1))
            }
            6 => {
                let key = self.read_str()?;
                let value = self.read_json()?;
                Ok((sink.content_atom(ContentAtom::Format { key, value })?, 1))
            }
            7 => {
                let kind = self.raw.read_var_u64()?;
                if crate::doc::YTypeKind::from(kind) == crate::doc::YTypeKind::Unknown {
                    return Err(JwstCodecError::IncompleteDocument(format!("Unknown y type: {kind}")).into());
                }
                let tag = matches!(kind, 3 | 5).then(|| self.read_str()).transpose()?;
                Ok((sink.content_atom(ContentAtom::Type { kind, tag })?, 1))
            }
            8 => {
                let len = self.raw.read_var_u64()?;
                let count = Self::usize(len, "content entries")?;
                self.add_entries(count)?;
                self.check_fits(count, MIN_ENTRY_BYTES, "content entries")?;
                sink.any_content_start(count)?;
                for _ in 0..count {
                    let value = self.read_any(sink)?;
                    sink.any_content_value(value)?;
                }
                Ok((sink.any_content_finish()?, len))
            }
            9 => {
                let guid = self.read_str()?;
                let options = self.read_any(sink)?;
                Ok((sink.doc_content(guid, options)?, 1))
            }
            _ => Err(JwstCodecError::IncompleteDocument(format!("Unknown content type: {tag}")).into()),
        }
    }

    fn read_any<S: Sink<'a>>(&mut self, sink: &mut S) -> Result<S::Any> {
        let start = self.raw.position();
        sink.any_start()?;
        self.read_any_value(sink)?;
        sink.any_finish(start..self.raw.position())
    }

    /// Reads one `Any` value with an explicit stack, so the nesting depth is
    /// bounded only by `max_any_depth` and never by the thread stack.
    fn read_any_value<S: Sink<'a>>(&mut self, sink: &mut S) -> Result<()> {
        // entries left in each open container, and whether it is an object
        let mut open: Vec<(usize, bool)> = Vec::new();
        loop {
            if let Some((remaining, is_object)) = open.last_mut() {
                if *remaining == 0 {
                    open.pop();
                    sink.any_event(AnyEvent::EndContainer)?;
                    if open.is_empty() {
                        return Ok(());
                    }
                    continue;
                }
                *remaining -= 1;
                if *is_object {
                    let key = self.read_str()?;
                    sink.any_event(AnyEvent::ObjectKey(key))?;
                }
            }
            if open.len() > self.limits.max_any_depth {
                return Err(Error::Resource("Any nesting depth"));
            }
            let tag = 127u8.wrapping_sub(self.raw.read_u8()?);
            let event = match tag {
                0 => AnyEvent::Undefined,
                1 => AnyEvent::Null,
                2 => {
                    let (value, negative) = self.raw.read_var_i32_with_sign()?;
                    // Preserve the same signed-zero semantics as the owned Any
                    // decoder.
                    if value == 0 && negative {
                        AnyEvent::Float32(-0.0)
                    } else {
                        AnyEvent::Integer(value)
                    }
                }
                3 => AnyEvent::Float32(self.raw.read_f32_be()?),
                4 => AnyEvent::Float64(self.raw.read_f64_be()?),
                5 => AnyEvent::BigInt64(self.raw.read_i64_be()?),
                6 => AnyEvent::False,
                7 => AnyEvent::True,
                8 => AnyEvent::String(self.read_str()?),
                9 => {
                    let count = Self::usize(self.raw.read_var_u64()?, "Any object entries")?;
                    self.add_entries(count)?;
                    self.check_fits(count, MIN_OBJECT_ENTRY_BYTES, "Any object entries")?;
                    sink.any_event(AnyEvent::BeginObject(count))?;
                    open.push((count, true));
                    continue;
                }
                10 => {
                    let count = Self::usize(self.raw.read_var_u64()?, "Any array entries")?;
                    self.add_entries(count)?;
                    self.check_fits(count, MIN_ENTRY_BYTES, "Any array entries")?;
                    sink.any_event(AnyEvent::BeginArray(count))?;
                    open.push((count, false));
                    continue;
                }
                11 => AnyEvent::Binary(self.read_bytes()?),
                _ => return Err(JwstCodecError::IncompleteDocument(format!("unknown Any tag: {tag}")).into()),
            };
            sink.any_event(event)?;
            if open.is_empty() {
                return Ok(());
            }
        }
    }

    fn read_id(&mut self) -> JwstCodecResult<Id> {
        Ok(Id::new(self.raw.read_var_u64()?, self.raw.read_var_u64()?))
    }

    fn read_str(&mut self) -> JwstCodecResult<WireStr<'a>> {
        let start = self.raw.position();
        let value = self.raw.read_var_str_ref()?;
        let end = self.raw.position();
        Ok(WireStr {
            value,
            range: end - value.len()..end.max(start),
        })
    }

    fn read_json(&mut self) -> JwstCodecResult<WireStr<'a>> {
        let value = self.read_str()?;
        let mut decoder = serde_json::Deserializer::from_str(value.value);
        JsonAnyValidator::deserialize(&mut decoder)
            .and_then(|_| decoder.end())
            .map_err(|_| JwstCodecError::DamagedDocumentJson)?;
        Ok(value)
    }

    fn read_bytes(&mut self) -> JwstCodecResult<WireBytes<'a>> {
        let start = self.raw.position();
        let value = self.raw.read_var_buffer_ref()?;
        let end = self.raw.position();
        Ok(WireBytes {
            value,
            range: end - value.len()..end.max(start),
        })
    }

    fn usize(value: u64, name: &'static str) -> Result<usize> {
        value.try_into().map_err(|_| Error::Resource(name))
    }

    /// Rejects a declared entry count that the rest of the input cannot hold
    /// when every entry takes at least `min_bytes`, before a sink reserves
    /// memory for it.
    fn check_fits(&self, count: usize, min_bytes: u64, name: &'static str) -> Result<()> {
        let available = self.raw.len() / min_bytes;
        if count as u64 > available {
            return Err(JwstCodecError::IncompleteDocument(format!(
                "{name}: {count} declared, at most {available} fit in the rest of the update"
            ))
            .into());
        }
        Ok(())
    }

    fn add_structs(&mut self, count: usize) -> Result<()> {
        self.structs = self.structs.checked_add(count).ok_or(Error::Resource("structs"))?;
        if self.structs > self.limits.max_structs {
            return Err(Error::Resource("structs"));
        }
        Ok(())
    }

    fn add_entries(&mut self, count: usize) -> Result<()> {
        self.entries = self
            .entries
            .checked_add(count)
            .ok_or(Error::Resource("collection entries"))?;
        if self.entries > self.limits.max_collection_entries {
            return Err(Error::Resource("collection entries"));
        }
        Ok(())
    }

    fn add_content_bytes(&mut self, count: usize) -> Result<()> {
        self.content_bytes = self
            .content_bytes
            .checked_add(count)
            .ok_or(Error::Resource("content bytes"))?;
        if self.content_bytes > self.limits.max_content_bytes {
            return Err(Error::Resource("content bytes"));
        }
        Ok(())
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

            #[inline]
            fn visit_bool<E>(self, _value: bool) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[inline]
            fn visit_i64<E>(self, _value: i64) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[inline]
            fn visit_u64<E>(self, _value: u64) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[inline]
            fn visit_f64<E>(self, _value: f64) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[inline]
            fn visit_str<E>(self, _value: &str) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[inline]
            fn visit_borrowed_str<E>(self, _value: &'de str) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[inline]
            fn visit_none<E>(self) -> std::result::Result<Self::Value, E> {
                Ok(JsonAnyValidator)
            }

            #[inline]
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

            #[inline]
            fn visit_str<E>(self, _value: &str) -> std::result::Result<Self::Value, E> {
                Ok(JsonKeyValidator)
            }

            #[inline]
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
        TruncatedRead,
        Resource(&'static str),
    }

    fn assert_decode_err(name: &str, input: &[u8], limits: DecodeLimits, expected: &ExpectedError) {
        let err = decode(input, ProbeSink::default(), limits).expect_err("decode should fail");
        match (&err, expected) {
            (Error::Codec(err), ExpectedError::Codec(expected)) => assert_eq!(err, expected, "{name}"),
            (Error::Codec(JwstCodecError::UpdateInvalid(_)), ExpectedError::TruncatedRead) => {}
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
            ("truncated varint", vec![0x80], ExpectedError::TruncatedRead),
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
}
