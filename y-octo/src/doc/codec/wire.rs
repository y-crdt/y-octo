use std::{cmp::Reverse, ops::Range};

use super::{
    Client, Clock, CrdtWrite, CrdtWriter, DeleteSet, Id, JwstCodecError, JwstCodecResult, RawEncoder,
    decoder::v1 as decoder, item_flags,
};
use crate::doc::{HASHMAP_SAFE_CAPACITY, StateVector, utf16_slice};

fn map_decoder_error(error: decoder::Error) -> JwstCodecError {
    match error {
        decoder::Error::Codec(error) => error,
        decoder::Error::Resource(name) => JwstCodecError::IncompleteDocument(format!("{name} exceeds limit")),
    }
}

/// Validates a Yjs Update V1 binary payload without allocating a document or
/// `Update` struct tree.
///
/// The acceptance set matches [`crate::Update::decode_v1`]: structural counts,
/// strictly increasing non-overlapping clocks, UTF-8 strings, JSON payloads,
/// `Any` nesting depth ([`crate::Any::DEFAULT_MAX_DEPTH`]), delete-set
/// integrity, and rejection of trailing bytes. `[0, 0]` is valid; `&[]` is
/// rejected.
pub fn validate_update_v1(update: &[u8]) -> JwstCodecResult<()> {
    decoder::decode(update, ValidateSink, decoder::DecodeLimits::UPDATE).map_err(map_decoder_error)
}

/// Extracts and encodes a Yjs V1 [`StateVector`] directly from a Yjs Update V1
/// payload without decoding into a [`crate::Doc`].
///
/// For each client, counts only the contiguous prefix of real structs (`Item`
/// and `GC`) starting at clock `0`. Clients whose first struct starts at a
/// nonzero clock or is a `Skip` are omitted, and scanning for a client stops at
/// the first `Skip`. The entire update (including the trailing `DeleteSet`) is
/// validated before returning.
pub fn encode_state_vector_from_update_v1(update: &[u8]) -> JwstCodecResult<Vec<u8>> {
    decoder::decode(update, StateVectorSink::default(), decoder::DecodeLimits::UPDATE).map_err(map_decoder_error)
}

/// Computes the Yjs V1 diff update containing all structs in `update` that are
/// not yet covered by the V1-encoded state vector `sv`, plus the full
/// canonicalized `DeleteSet`.
///
/// An empty state vector is encoded as `&[0]`; an empty slice `&[]` returns a
/// decode error. Operates directly on the V1 wire stream without constructing a
/// [`crate::Doc`] or [`crate::Update`].
pub fn diff_update_v1(update: &[u8], sv: &[u8]) -> JwstCodecResult<Vec<u8>> {
    let target = StateVector::decode_v1(sv)?;
    decoder::decode(update, DiffSink::new(update, target), decoder::DecodeLimits::UPDATE).map_err(map_decoder_error)
}

struct ValidateSink;

impl<'a> decoder::Sink<'a> for ValidateSink {
    type Output = ();
    type Content = ();
    type Any = ();

    fn begin_client(&mut self, _client: u64, _count: usize) -> decoder::Result<()> {
        Ok(())
    }

    fn gc(&mut self, _id: Id, _len: u64) -> decoder::Result<()> {
        Ok(())
    }

    fn skip(&mut self, _id: Id, _len: u64) -> decoder::Result<()> {
        Ok(())
    }

    fn item(&mut self, _id: Id, _len: u64, _meta: decoder::ItemMeta<'a>, _content: ()) -> decoder::Result<()> {
        Ok(())
    }

    fn content_atom(&mut self, _atom: decoder::ContentAtom<'a>) -> decoder::Result<()> {
        Ok(())
    }

    fn json_start(&mut self, _count: usize) -> decoder::Result<()> {
        Ok(())
    }

    fn json_value(&mut self, _value: decoder::WireStr<'a>) -> decoder::Result<()> {
        Ok(())
    }

    fn json_finish(&mut self) -> decoder::Result<()> {
        Ok(())
    }

    fn any_content_start(&mut self, _count: usize) -> decoder::Result<()> {
        Ok(())
    }

    fn any_content_value(&mut self, _value: ()) -> decoder::Result<()> {
        Ok(())
    }

    fn any_content_finish(&mut self) -> decoder::Result<()> {
        Ok(())
    }

    fn doc_content(&mut self, _guid: decoder::WireStr<'a>, _options: ()) -> decoder::Result<()> {
        Ok(())
    }

    fn any_start(&mut self) -> decoder::Result<()> {
        Ok(())
    }

    fn any_event(&mut self, _event: decoder::AnyEvent<'a>) -> decoder::Result<()> {
        Ok(())
    }

    fn any_finish(&mut self, _range: Range<usize>) -> decoder::Result<()> {
        Ok(())
    }

    fn delete_range(&mut self, _client: u64, _range: Range<u64>) -> decoder::Result<()> {
        Ok(())
    }

    fn finish(self) -> decoder::Result<()> {
        Ok(())
    }
}

#[derive(Default)]
struct StateVectorSink {
    sv: StateVector,
    current_clock: Clock,
    stopped: bool,
}

impl StateVectorSink {
    fn advance_real(&mut self, id: Id, len: u64) -> decoder::Result<()> {
        if self.stopped {
            return Ok(());
        }
        // `decoder::v1` validates `len > 0` and `id.clock.checked_add(len)`
        // before calling the sink; keep checked arithmetic here as defense in
        // depth.
        if id.clock == self.current_clock {
            self.current_clock = self
                .current_clock
                .checked_add(len)
                .ok_or(JwstCodecError::StructClockInvalid {
                    expect: self.current_clock,
                    actually: u64::MAX,
                })?;
            if self.current_clock > 0 {
                self.sv.insert(id.client, self.current_clock);
            }
        } else {
            self.stopped = true;
        }
        Ok(())
    }
}

impl<'a> decoder::Sink<'a> for StateVectorSink {
    type Output = Vec<u8>;
    type Content = ();
    type Any = ();

    fn begin_client(&mut self, _client: u64, _count: usize) -> decoder::Result<()> {
        self.current_clock = 0;
        self.stopped = false;
        Ok(())
    }

    fn gc(&mut self, id: Id, len: u64) -> decoder::Result<()> {
        self.advance_real(id, len)
    }

    fn skip(&mut self, _id: Id, _len: u64) -> decoder::Result<()> {
        self.stopped = true;
        Ok(())
    }

    fn item(&mut self, id: Id, len: u64, _meta: decoder::ItemMeta<'a>, _content: ()) -> decoder::Result<()> {
        self.advance_real(id, len)
    }

    fn content_atom(&mut self, _atom: decoder::ContentAtom<'a>) -> decoder::Result<()> {
        Ok(())
    }

    fn json_start(&mut self, _count: usize) -> decoder::Result<()> {
        Ok(())
    }

    fn json_value(&mut self, _value: decoder::WireStr<'a>) -> decoder::Result<()> {
        Ok(())
    }

    fn json_finish(&mut self) -> decoder::Result<()> {
        Ok(())
    }

    fn any_content_start(&mut self, _count: usize) -> decoder::Result<()> {
        Ok(())
    }

    fn any_content_value(&mut self, _value: ()) -> decoder::Result<()> {
        Ok(())
    }

    fn any_content_finish(&mut self) -> decoder::Result<()> {
        Ok(())
    }

    fn doc_content(&mut self, _guid: decoder::WireStr<'a>, _options: ()) -> decoder::Result<()> {
        Ok(())
    }

    fn any_start(&mut self) -> decoder::Result<()> {
        Ok(())
    }

    fn any_event(&mut self, _event: decoder::AnyEvent<'a>) -> decoder::Result<()> {
        Ok(())
    }

    fn any_finish(&mut self, _range: Range<usize>) -> decoder::Result<()> {
        Ok(())
    }

    fn delete_range(&mut self, _client: u64, _range: Range<u64>) -> decoder::Result<()> {
        Ok(())
    }

    fn finish(self) -> decoder::Result<Vec<u8>> {
        self.sv.encode_v1().map_err(decoder::Error::Codec)
    }
}

enum WireContent<'a> {
    Deleted(u64),
    String(&'a str),
    Json(Vec<&'a str>),
    Any(Vec<Range<usize>>),
    Unsplittable,
}

struct EmittedClient {
    client: Client,
    start_clock: Clock,
    count: usize,
    bytes: Vec<u8>,
}

struct ActiveClient {
    client: Client,
    target_clock: Clock,
    start_clock: Option<Clock>,
    count: usize,
    encoder: RawEncoder,
}

impl ActiveClient {
    fn new(client: Client, target_clock: Clock) -> Self {
        Self {
            client,
            target_clock,
            start_clock: None,
            count: 0,
            encoder: RawEncoder::default(),
        }
    }

    fn finish(self) -> Option<EmittedClient> {
        let start_clock = self.start_clock?;
        if self.count == 0 {
            return None;
        }
        Some(EmittedClient {
            client: self.client,
            start_clock,
            count: self.count,
            bytes: self.encoder.into_inner(),
        })
    }
}

struct DiffSink<'a> {
    input: &'a [u8],
    target: StateVector,
    active: Option<ActiveClient>,
    emitted: Vec<EmittedClient>,
    delete_set: DeleteSet,
    json_buf: Vec<&'a str>,
    any_buf: Vec<Range<usize>>,
}

impl<'a> DiffSink<'a> {
    fn new(input: &'a [u8], target: StateVector) -> Self {
        Self {
            input,
            target,
            active: None,
            emitted: Vec::new(),
            delete_set: DeleteSet::default(),
            json_buf: Vec::new(),
            any_buf: Vec::new(),
        }
    }

    fn flush_active(&mut self) {
        if let Some(active) = self.active.take()
            && let Some(emitted) = active.finish()
        {
            self.emitted.push(emitted);
        }
    }
}

impl<'a> decoder::Sink<'a> for DiffSink<'a> {
    type Output = Vec<u8>;
    type Content = WireContent<'a>;
    type Any = Range<usize>;

    fn begin_client(&mut self, client: u64, _count: usize) -> decoder::Result<()> {
        self.flush_active();
        let target_clock = self.target.get(&client);
        self.active = Some(ActiveClient::new(client, target_clock));
        Ok(())
    }

    fn gc(&mut self, id: Id, len: u64) -> decoder::Result<()> {
        let active = self.active.as_mut().unwrap();
        // `decoder::v1` validates `len > 0` and `id.clock.checked_add(len)`
        // before invoking sink callbacks.
        let end = id.clock.checked_add(len).ok_or(JwstCodecError::StructClockInvalid {
            expect: id.clock,
            actually: u64::MAX,
        })?;
        if end <= active.target_clock {
            return Ok(());
        }
        let offset = active.target_clock.saturating_sub(id.clock);
        let out_clock = id.clock + offset;
        let out_len = len - offset;
        if active.start_clock.is_none() {
            active.start_clock = Some(out_clock);
        }
        active.encoder.write_info(0)?;
        active.encoder.write_var_u64(out_len)?;
        active.count += 1;
        Ok(())
    }

    fn skip(&mut self, id: Id, len: u64) -> decoder::Result<()> {
        let active = self.active.as_mut().unwrap();
        let end = id.clock.checked_add(len).ok_or(JwstCodecError::StructClockInvalid {
            expect: id.clock,
            actually: u64::MAX,
        })?;
        if end <= active.target_clock || active.start_clock.is_none() {
            return Ok(());
        }
        active.encoder.write_info(10)?;
        active.encoder.write_var_u64(len)?;
        active.count += 1;
        Ok(())
    }

    fn item(&mut self, id: Id, len: u64, meta: decoder::ItemMeta<'a>, content: WireContent<'a>) -> decoder::Result<()> {
        let active = self.active.as_mut().unwrap();
        let end = id.clock.checked_add(len).ok_or(JwstCodecError::StructClockInvalid {
            expect: id.clock,
            actually: u64::MAX,
        })?;
        if end <= active.target_clock {
            return Ok(());
        }

        let raw = &self.input[meta.raw_range];
        let offset = active.target_clock.saturating_sub(id.clock);
        let out_clock = id.clock + offset;
        if active.start_clock.is_none() {
            active.start_clock = Some(out_clock);
        }

        if offset == 0 {
            let mut out_info = raw[0] & !item_flags::ITEM_HAS_PARENT_SUB;
            if meta.parent_sub.is_some() {
                out_info |= item_flags::ITEM_HAS_PARENT_SUB;
            }
            active.encoder.write_info(out_info)?;
            active.encoder.write_raw(&raw[1..])?;
        } else {
            let tag = raw[0] & 0b1_1111;
            let mut out_info = tag | item_flags::ITEM_HAS_LEFT_ID;
            if meta.origin_right.is_some() {
                out_info |= item_flags::ITEM_HAS_RIGHT_ID;
            }
            if meta.parent_sub.is_some() {
                out_info |= item_flags::ITEM_HAS_PARENT_SUB;
            }
            let origin_left = Id::new(id.client, out_clock - 1);

            active.encoder.write_info(out_info)?;
            active.encoder.write_item_id(&origin_left)?;
            if let Some(origin_right) = meta.origin_right {
                active.encoder.write_item_id(&origin_right)?;
            }

            match content {
                WireContent::Deleted(total) => {
                    active.encoder.write_var_u64(total - offset)?;
                }
                WireContent::String(s) => {
                    let tail = utf16_slice(s, offset, u64::MAX);
                    active.encoder.write_var_string(tail.as_ref())?;
                }
                WireContent::Json(strings) => {
                    let start = usize::try_from(offset)
                        .map_err(|_| decoder::Error::Codec(JwstCodecError::ContentSplitNotSupport(offset)))?;
                    let tail = strings
                        .get(start..)
                        .ok_or(decoder::Error::Codec(JwstCodecError::ContentSplitNotSupport(offset)))?;
                    active.encoder.write_var_u64(tail.len() as u64)?;
                    for s in tail {
                        active.encoder.write_var_string(s)?;
                    }
                }
                WireContent::Any(ranges) => {
                    let start = usize::try_from(offset)
                        .map_err(|_| decoder::Error::Codec(JwstCodecError::ContentSplitNotSupport(offset)))?;
                    let tail = ranges
                        .get(start..)
                        .ok_or(decoder::Error::Codec(JwstCodecError::ContentSplitNotSupport(offset)))?;
                    active.encoder.write_var_u64(tail.len() as u64)?;
                    for range in tail {
                        active.encoder.write_raw(&self.input[range.clone()])?;
                    }
                }
                WireContent::Unsplittable => {
                    return Err(decoder::Error::Codec(JwstCodecError::ContentSplitNotSupport(offset)));
                }
            }
        }

        active.count += 1;
        Ok(())
    }

    fn content_atom(&mut self, atom: decoder::ContentAtom<'a>) -> decoder::Result<WireContent<'a>> {
        Ok(match atom {
            decoder::ContentAtom::Deleted(len) => WireContent::Deleted(len),
            decoder::ContentAtom::String(s) => WireContent::String(s.value),
            decoder::ContentAtom::Binary(_)
            | decoder::ContentAtom::Embed(_)
            | decoder::ContentAtom::Format { .. }
            | decoder::ContentAtom::Type { .. } => WireContent::Unsplittable,
        })
    }

    fn json_start(&mut self, count: usize) -> decoder::Result<()> {
        self.json_buf.clear();
        self.json_buf.reserve(count.min(HASHMAP_SAFE_CAPACITY));
        Ok(())
    }

    fn json_value(&mut self, value: decoder::WireStr<'a>) -> decoder::Result<()> {
        self.json_buf.push(value.value);
        Ok(())
    }

    fn json_finish(&mut self) -> decoder::Result<WireContent<'a>> {
        Ok(WireContent::Json(std::mem::take(&mut self.json_buf)))
    }

    fn any_content_start(&mut self, count: usize) -> decoder::Result<()> {
        self.any_buf.clear();
        self.any_buf.reserve(count.min(HASHMAP_SAFE_CAPACITY));
        Ok(())
    }

    fn any_content_value(&mut self, value: Range<usize>) -> decoder::Result<()> {
        self.any_buf.push(value);
        Ok(())
    }

    fn any_content_finish(&mut self) -> decoder::Result<WireContent<'a>> {
        Ok(WireContent::Any(std::mem::take(&mut self.any_buf)))
    }

    fn doc_content(&mut self, _guid: decoder::WireStr<'a>, _options: Range<usize>) -> decoder::Result<WireContent<'a>> {
        Ok(WireContent::Unsplittable)
    }

    fn any_start(&mut self) -> decoder::Result<()> {
        Ok(())
    }

    fn any_event(&mut self, _event: decoder::AnyEvent<'a>) -> decoder::Result<()> {
        Ok(())
    }

    fn any_finish(&mut self, range: Range<usize>) -> decoder::Result<Range<usize>> {
        Ok(range)
    }

    fn delete_range(&mut self, client: u64, range: Range<u64>) -> decoder::Result<()> {
        self.delete_set.add_range(client, range);
        Ok(())
    }

    fn finish(mut self) -> decoder::Result<Vec<u8>> {
        self.flush_active();
        self.emitted.sort_unstable_by_key(|entry| Reverse(entry.client));

        let mut out = RawEncoder::default();
        out.write_var_u64(self.emitted.len() as u64)?;
        for entry in self.emitted {
            out.write_var_u64(entry.count as u64)?;
            out.write_var_u64(entry.client)?;
            out.write_var_u64(entry.start_clock)?;
            out.write_raw(&entry.bytes)?;
        }
        self.delete_set.write(&mut out)?;
        Ok(out.into_inner())
    }
}
