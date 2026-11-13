use std::{borrow::Cow, ops::Range};

use super::{
    AnyId, Builder, FrozenContent, FrozenType, NodeId, RawContent, RawNode, ReadDoc, ReadError, Span, Utf16Slices,
};
use crate::{Any, CrdtRead, CrdtReader, JwstCodecError, RawDecoder};

impl Builder {
    fn freeze_strings(&mut self, any: &mut Vec<Any>) -> Result<(), ReadError> {
        // Client clock order keeps each original span's fragments consecutive
        // for one text scan.
        for nodes in self.clients.values() {
            let mut current = None;
            for &node_id in nodes {
                let node = &self.nodes[node_id as usize];
                let RawContent::String(span) = node.content else {
                    continue;
                };
                if node.deleted() {
                    continue;
                }
                if current.as_ref().is_none_or(|(source, _)| *source != span) {
                    current = Some((span, Utf16Slices::new(span.str(&self.input))));
                }
                let selected = current.as_mut().unwrap().1.slice(node.content_offset, node.len);
                let content = match selected {
                    Cow::Borrowed(selected) => {
                        let start = selected.as_ptr() as usize - self.input.as_ptr() as usize;
                        RawContent::String(Span::new(start..start + selected.len())?)
                    }
                    Cow::Owned(selected) => RawContent::StringOwned(self.push_any(Any::String(selected), any)?),
                };
                self.nodes[node_id as usize].content = content;
            }
        }
        Ok(())
    }

    pub(super) fn freeze(mut self) -> Result<ReadDoc, ReadError> {
        let mut any = Vec::new();
        self.freeze_strings(&mut any)?;
        let mut types = Vec::with_capacity(self.types.len());
        for type_id in 0..self.types.len() {
            let raw = &self.types[type_id];
            let mut map = Vec::with_capacity(raw.map.len());
            for (key, node_id) in &raw.map {
                let node = &self.nodes[*node_id as usize];
                if !node.deleted()
                    && let Some(value) = self.freeze_value(*node_id, &mut any)?
                {
                    map.push((*key, value));
                }
            }
            map.sort_unstable_by_key(|(key, _)| *key);

            let mut list = Vec::new();
            let mut len = 0u64;
            let mut cursor = raw.start;
            let mut remaining = self.nodes.len();
            while let Some(node_id) = cursor {
                let node = &self.nodes[node_id as usize];
                if !node.deleted()
                    && let Some(value) = self.freeze_value(node_id, &mut any)?
                {
                    if node.countable() {
                        len = len
                            .checked_add(node.len)
                            .ok_or(ReadError::ResourceLimit("visible type length"))?;
                    }
                    list.push(value);
                }
                cursor = node.right();
                if remaining == 0 {
                    return Err(ReadError::InvalidUpdate(JwstCodecError::InvalidParent));
                }
                remaining -= 1;
            }
            types.push(FrozenType {
                kind: raw.kind,
                tag: raw.tag,
                map,
                list,
                len,
            });
        }

        Ok(ReadDoc {
            input: self.input,
            roots: self.roots,
            keys: self.keys,
            any,
            types,
        })
    }

    fn freeze_value(&self, node_id: NodeId, any: &mut Vec<Any>) -> Result<Option<FrozenContent>, ReadError> {
        let node = &self.nodes[node_id as usize];
        let content = match &node.content {
            RawContent::None | RawContent::Deleted => return Ok(None),
            RawContent::Json(parts) => {
                let range = self.selected_parts(parts, node)?;
                let start = any.len();
                for span in &self.parts[range] {
                    let value = span.str(&self.input);
                    any.push(if value == "undefined" {
                        Any::Undefined
                    } else {
                        Any::String(value.to_string())
                    });
                }
                FrozenContent::Any(self.any_range(start, any.len())?)
            }
            RawContent::Binary(span) => FrozenContent::Binary(*span),
            RawContent::String(span) => FrozenContent::String(*span),
            RawContent::StringOwned(id) => FrozenContent::StringOwned(*id),
            RawContent::Embed(span) => {
                let start = any.len();
                any.push(serde_json::from_str(span.str(&self.input)).map_err(|_| JwstCodecError::DamagedDocumentJson)?);
                FrozenContent::Any(self.any_range(start, any.len())?)
            }
            RawContent::Format { key, value } => {
                let value = self.push_json_any(*value, any)?;
                FrozenContent::Format { key: *key, value }
            }
            RawContent::Type(ty) => FrozenContent::Type(*ty),
            RawContent::Any(parts) => {
                let range = self.selected_parts(parts, node)?;
                let start = any.len();
                for span in &self.parts[range] {
                    let mut decoder = RawDecoder::new(span.bytes(&self.input));
                    let value = Any::read(&mut decoder)?;
                    if !decoder.is_empty() {
                        return Err(JwstCodecError::UpdateNotFullyConsumed(decoder.len() as usize).into());
                    }
                    any.push(value);
                }
                FrozenContent::Any(self.any_range(start, any.len())?)
            }
            RawContent::Doc { guid, options } => FrozenContent::Doc {
                guid: *guid,
                options: self.push_encoded_any(*options, any)?,
            },
        };
        Ok(Some(content))
    }

    fn selected_parts(&self, parts: &Range<u32>, node: &RawNode) -> Result<Range<usize>, ReadError> {
        let start = parts.start as usize + node.content_offset as usize;
        let end = start
            .checked_add(node.len as usize)
            .ok_or(ReadError::ResourceLimit("content entries"))?;
        if end > parts.end as usize {
            return Err(ReadError::InvalidUpdate(JwstCodecError::IndexOutOfBound(node.len)));
        }
        Ok(start..end)
    }

    fn push_encoded_any(&self, span: super::Span, any: &mut Vec<Any>) -> Result<AnyId, ReadError> {
        let mut decoder = RawDecoder::new(span.bytes(&self.input));
        let value = Any::read(&mut decoder)?;
        if !decoder.is_empty() {
            return Err(JwstCodecError::UpdateNotFullyConsumed(decoder.len() as usize).into());
        }
        self.push_any(value, any)
    }

    fn push_json_any(&self, span: super::Span, any: &mut Vec<Any>) -> Result<AnyId, ReadError> {
        let value = serde_json::from_str(span.str(&self.input)).map_err(|_| JwstCodecError::DamagedDocumentJson)?;
        self.push_any(value, any)
    }

    fn push_any(&self, value: Any, any: &mut Vec<Any>) -> Result<AnyId, ReadError> {
        let id = any
            .len()
            .try_into()
            .map_err(|_| ReadError::ResourceLimit("visible Any values"))?;
        any.push(value);
        Ok(id)
    }

    fn any_range(&self, start: usize, end: usize) -> Result<Range<u32>, ReadError> {
        Ok(start
            .try_into()
            .map_err(|_| ReadError::ResourceLimit("visible Any values"))?
            ..end
                .try_into()
                .map_err(|_| ReadError::ResourceLimit("visible Any values"))?)
    }
}
