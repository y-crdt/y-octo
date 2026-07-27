use std::{ops::Range, sync::Arc};

use super::{Builder, KeyTable, RawContent, RawNode, RawNodeKind, RawParent, RawType, ReadError, ReadLimits, Span};
use crate::{
    Id, YTypeKind,
    doc::{ClientMap, HashMap, codec::decoder::v1 as decoder},
};

pub(super) fn scan(input: Arc<[u8]>, limits: ReadLimits) -> Result<Builder, ReadError> {
    if input.len() > limits.max_input_bytes || input.len() > u32::MAX as usize {
        return Err(ReadError::ResourceLimit("input bytes"));
    }
    let decoder_limits = decoder::DecodeLimits {
        max_structs: limits.max_structs,
        max_clients: limits.max_clients,
        max_collection_entries: limits.max_collection_entries,
        max_any_depth: limits.max_any_depth,
        max_content_bytes: limits.max_content_bytes,
    };
    let sink = ReadOnlySink {
        input: &input,
        backing: input.clone(),
        nodes: Vec::new(),
        clients: ClientMap::default(),
        types: Vec::new(),
        keys: KeyTable::default(),
        parts: Vec::new(),
        deletes: Vec::new(),
        limits,
        parts_start: 0,
    };
    decoder::decode(&input, sink, decoder_limits).map_err(|error| match error {
        decoder::Error::Codec(error) => ReadError::InvalidUpdate(error),
        decoder::Error::Resource(name) => ReadError::ResourceLimit(name),
    })
}

struct ReadOnlySink<'a> {
    input: &'a [u8],
    backing: Arc<[u8]>,
    nodes: Vec<RawNode>,
    clients: ClientMap<Vec<u32>>,
    types: Vec<RawType>,
    keys: KeyTable,
    parts: Vec<Span>,
    deletes: Vec<(u64, Range<u64>)>,
    limits: ReadLimits,
    parts_start: usize,
}

impl ReadOnlySink<'_> {
    fn node_id(&self) -> decoder::Result<u32> {
        self.nodes
            .len()
            .try_into()
            .map_err(|_| decoder::Error::Resource("structs"))
    }

    fn span(range: Range<usize>) -> decoder::Result<Span> {
        Span::new(range).map_err(|error| match error {
            ReadError::ResourceLimit(name) => decoder::Error::Resource(name),
            ReadError::InvalidUpdate(error) => decoder::Error::Codec(error),
            ReadError::IncompleteSnapshot(name) => {
                decoder::Error::Codec(crate::JwstCodecError::IncompleteDocument(name.into()))
            }
        })
    }

    fn part_range(&self) -> decoder::Result<Range<u32>> {
        Ok(self
            .parts_start
            .try_into()
            .map_err(|_| decoder::Error::Resource("content entries"))?
            ..self
                .parts
                .len()
                .try_into()
                .map_err(|_| decoder::Error::Resource("content entries"))?)
    }

    fn push_node(&mut self, node: RawNode) -> decoder::Result<()> {
        let node_id = self.node_id()?;
        self.clients
            .get_mut(&node.id.client)
            .expect("wire decoder begins a client before its structs")
            .push(node_id);
        self.nodes.push(node);
        Ok(())
    }
}

impl<'a> decoder::Sink<'a> for ReadOnlySink<'a> {
    type Output = Builder;
    type Content = RawContent;
    type Any = Span;

    fn begin_client(&mut self, client: u64, count: usize) -> decoder::Result<()> {
        let mut nodes = Vec::new();
        nodes
            .try_reserve_exact(count)
            .map_err(|_| decoder::Error::Resource("structs"))?;
        self.clients.insert(client, nodes);
        self.nodes
            .try_reserve_exact(count)
            .map_err(|_| decoder::Error::Resource("structs"))?;
        Ok(())
    }

    fn gc(&mut self, id: Id, len: u64) -> decoder::Result<()> {
        self.push_node(RawNode::new(
            RawNodeKind::Gc,
            id,
            len,
            None,
            None,
            RawParent::Inherit,
            None,
            None,
            false,
            true,
        ))
    }

    fn skip(&mut self, id: Id, len: u64) -> decoder::Result<()> {
        self.push_node(RawNode::new(
            RawNodeKind::Skip,
            id,
            len,
            None,
            None,
            RawParent::Inherit,
            None,
            None,
            false,
            true,
        ))
    }

    fn item(&mut self, id: Id, len: u64, meta: decoder::ItemMeta<'a>, content: RawContent) -> decoder::Result<()> {
        let parent = match meta.parent {
            decoder::WireParent::Root(value) => {
                let span = Self::span(value.range)?;
                RawParent::Root(
                    self.keys
                        .intern(self.input, span)
                        .map_err(|_| decoder::Error::Resource("map keys"))?,
                )
            }
            decoder::WireParent::Item(id) => RawParent::Item(id),
            decoder::WireParent::Inherit => RawParent::Inherit,
        };
        let parent_sub = meta
            .parent_sub
            .map(|value| {
                let span = Self::span(value.range)?;
                self.keys
                    .intern(self.input, span)
                    .map_err(|_| decoder::Error::Resource("map keys"))
            })
            .transpose()?;
        let countable = !matches!(content, RawContent::Deleted | RawContent::Format { .. });
        let deleted = matches!(content, RawContent::Deleted);
        self.push_node(RawNode::new(
            RawNodeKind::Item,
            id,
            len,
            meta.origin_left,
            meta.origin_right,
            parent,
            parent_sub,
            Some(content),
            countable,
            deleted,
        ))
    }

    fn content_atom(&mut self, atom: decoder::ContentAtom<'a>) -> decoder::Result<RawContent> {
        Ok(match atom {
            decoder::ContentAtom::Deleted(_) => RawContent::Deleted,
            decoder::ContentAtom::Binary(value) => RawContent::Binary(Self::span(value.range)?),
            decoder::ContentAtom::String(value) => RawContent::String(Self::span(value.range)?),
            decoder::ContentAtom::Embed(value) => RawContent::Embed(Self::span(value.range)?),
            decoder::ContentAtom::Format { key, value } => RawContent::Format {
                key: Self::span(key.range)?,
                value: Self::span(value.range)?,
            },
            decoder::ContentAtom::Type { kind, tag } => {
                let owner = self.node_id()?;
                let ty: u32 = self
                    .types
                    .len()
                    .try_into()
                    .map_err(|_| decoder::Error::Resource("types"))?;
                self.types.push(RawType::nested(
                    YTypeKind::from(kind),
                    tag.map(|value| Self::span(value.range)).transpose()?,
                    owner,
                ));
                RawContent::Type(ty)
            }
        })
    }

    fn json_start(&mut self, count: usize) -> decoder::Result<()> {
        self.parts_start = self.parts.len();
        self.parts
            .try_reserve_exact(count)
            .map_err(|_| decoder::Error::Resource("content entries"))
    }

    fn json_value(&mut self, value: decoder::WireStr<'a>) -> decoder::Result<()> {
        self.parts.push(Self::span(value.range)?);
        Ok(())
    }

    fn json_finish(&mut self) -> decoder::Result<RawContent> {
        Ok(RawContent::Json(self.part_range()?))
    }

    fn any_content_start(&mut self, count: usize) -> decoder::Result<()> {
        self.parts_start = self.parts.len();
        self.parts
            .try_reserve_exact(count)
            .map_err(|_| decoder::Error::Resource("content entries"))
    }

    fn any_content_value(&mut self, value: Span) -> decoder::Result<()> {
        self.parts.push(value);
        Ok(())
    }

    fn any_content_finish(&mut self) -> decoder::Result<RawContent> {
        Ok(RawContent::Any(self.part_range()?))
    }

    fn doc_content(&mut self, guid: decoder::WireStr<'a>, options: Span) -> decoder::Result<RawContent> {
        Ok(RawContent::Doc {
            guid: Self::span(guid.range)?,
            options,
        })
    }

    fn any_start(&mut self) -> decoder::Result<()> {
        Ok(())
    }

    fn any_event(&mut self, _event: decoder::AnyEvent<'a>) -> decoder::Result<()> {
        Ok(())
    }

    fn any_finish(&mut self, range: Range<usize>) -> decoder::Result<Span> {
        Self::span(range)
    }

    fn delete_range(&mut self, client: u64, range: Range<u64>) -> decoder::Result<()> {
        self.deletes.push((client, range));
        Ok(())
    }

    fn finish(self) -> decoder::Result<Builder> {
        Ok(Builder {
            input: self.backing,
            nodes: self.nodes,
            clients: self.clients,
            types: self.types,
            roots: HashMap::default(),
            keys: self.keys,
            parts: self.parts,
            deletes: self.deletes,
            limits: self.limits,
        })
    }
}
