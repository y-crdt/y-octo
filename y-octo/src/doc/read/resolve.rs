use std::ops::Range;

use super::{
    AnyId, Builder, FrozenContent, FrozenType, FrozenValue, NodeId, RawContent, RawNode, RawNodeKind, RawParent,
    RawType, ReadDoc, ReadError, TypeId,
};
use crate::{
    Any, CrdtRead, CrdtReader, Id, JwstCodecError, RawDecoder, StateVector,
    doc::{
        ClientMap, ConflictItem, HashMap, OrderRange, find_clock_segment, find_conflict_left, find_missing_dependency,
    },
};

pub(super) fn resolve(mut builder: Builder) -> Result<ReadDoc, ReadError> {
    builder.integrate_all()?;
    builder.apply_delete_set()?;
    builder.freeze()
}

impl Builder {
    fn integrate_all(&mut self) -> Result<(), ReadError> {
        let mut order = IntegrationOrder::new(&self.clients);
        let mut state = StateVector::default();
        let mut stack = Vec::new();
        let mut current = order.next(self);

        while let Some(node_id) = current.take() {
            let node = &self.nodes[node_id as usize];
            if node.kind() == RawNodeKind::Skip {
                current = stack.pop().or_else(|| order.next(self));
                continue;
            }

            let local_clock = state.get(&node.id.client);
            if node.id.clock > local_clock {
                return Err(ReadError::IncompleteSnapshot("client clock gap"));
            }
            if node.id.clock.saturating_add(node.len) <= local_clock {
                current = stack.pop().or_else(|| order.next(self));
                continue;
            }

            if let Some(dependency) = self.missing_dependency(node_id, &state) {
                stack.push(node_id);
                current = order.next_for(self, dependency);
                if current.is_none() {
                    return Err(ReadError::IncompleteSnapshot("missing struct dependency"));
                }
                continue;
            }

            if node.id.clock != local_clock {
                return Err(ReadError::IncompleteSnapshot("overlapping client structs"));
            }
            let end = node.id.clock.checked_add(node.len).ok_or(ReadError::InvalidUpdate(
                JwstCodecError::StructClockInvalid {
                    expect: node.id.clock,
                    actually: u64::MAX,
                },
            ))?;
            state.set_max(node.id.client, end);
            if self.nodes[node_id as usize].kind() == RawNodeKind::Item {
                self.repair(node_id)?;
                self.integrate_item(node_id)?;
            } else {
                self.nodes[node_id as usize].set_integrated(true);
            }

            current = stack.pop().or_else(|| order.next(self));
        }

        if !stack.is_empty() {
            return Err(ReadError::IncompleteSnapshot("unresolved struct dependencies"));
        }
        for (client, nodes) in &self.clients {
            let Some(last) = nodes.last().map(|id| &self.nodes[*id as usize]) else {
                continue;
            };
            let expected = last.id.clock.saturating_add(last.len);
            if state.get(client) < expected
                && nodes
                    .iter()
                    .any(|id| self.nodes[*id as usize].kind() != RawNodeKind::Skip)
            {
                return Err(ReadError::IncompleteSnapshot("unintegrated client structs"));
            }
        }
        Ok(())
    }

    fn missing_dependency(&self, node_id: NodeId, state: &StateVector) -> Option<u64> {
        let node = &self.nodes[node_id as usize];
        let parent = match node.wire_parent() {
            RawParent::Item(parent) => Some(parent),
            _ => None,
        };
        find_missing_dependency(node.id, node.origin_left(), node.origin_right(), parent, state)
    }

    fn repair(&mut self, node_id: NodeId) -> Result<(), ReadError> {
        let (origin_left, origin_right, wire_parent) = {
            let node = &self.nodes[node_id as usize];
            (node.origin_left(), node.origin_right(), node.wire_parent())
        };

        if let Some(id) = origin_left {
            let left = self.split_left(id)?;
            if self.nodes[left as usize].kind() == RawNodeKind::Item {
                let id = self.nodes[left as usize].last_id();
                self.nodes[node_id as usize].set_origin_left(Some(id));
                self.nodes[node_id as usize].set_left(Some(left));
            } else {
                self.nodes[node_id as usize].set_origin_left(None);
            }
        }
        if let Some(id) = origin_right {
            let right = self.split_right(id)?;
            if self.nodes[right as usize].kind() == RawNodeKind::Item {
                let id = self.nodes[right as usize].id;
                self.nodes[node_id as usize].set_origin_right(Some(id));
                self.nodes[node_id as usize].set_right(Some(right));
            } else {
                self.nodes[node_id as usize].set_origin_right(None);
            }
        }

        let parent = match wire_parent {
            RawParent::Root(key) => Some(self.get_or_create_root(key)?),
            RawParent::Item(id) => {
                self.locate(id)
                    .ok()
                    .and_then(|(_, target)| match &self.nodes[target as usize].content {
                        RawContent::Type(ty) => Some(*ty),
                        _ => None,
                    })
            }
            RawParent::Inherit => self.nodes[node_id as usize]
                .left()
                .and_then(|left| self.nodes[left as usize].parent())
                .or_else(|| {
                    self.nodes[node_id as usize]
                        .right()
                        .and_then(|right| self.nodes[right as usize].parent())
                }),
        };
        if matches!(wire_parent, RawParent::Inherit) {
            let inherited_sub = self.nodes[node_id as usize]
                .left()
                .and_then(|left| self.nodes[left as usize].parent_sub())
                .or_else(|| {
                    self.nodes[node_id as usize]
                        .right()
                        .and_then(|right| self.nodes[right as usize].parent_sub())
                });
            self.nodes[node_id as usize].set_parent_sub(inherited_sub);
        }
        self.nodes[node_id as usize].set_parent(parent);

        if let (Some(parent), RawContent::Type(inner)) = (parent, &self.nodes[node_id as usize].content)
            && self.type_is_ancestor(*inner, parent)
        {
            return Err(ReadError::InvalidUpdate(JwstCodecError::InvalidParent));
        }
        Ok(())
    }

    fn type_is_ancestor(&self, target: TypeId, mut current: TypeId) -> bool {
        let mut remaining = self.types.len();
        while remaining > 0 {
            if current == target {
                return true;
            }
            let Some(owner) = self.types[current as usize].owner else {
                return false;
            };
            let Some(parent) = self.nodes[owner as usize].parent() else {
                return false;
            };
            current = parent;
            remaining -= 1;
        }
        true
    }

    fn get_or_create_root(&mut self, key: u32) -> Result<TypeId, ReadError> {
        if let Some(id) = self.roots.get(&key) {
            return Ok(*id);
        }
        let id = self
            .types
            .len()
            .try_into()
            .map_err(|_| ReadError::ResourceLimit("types"))?;
        self.types.push(RawType::root());
        self.roots.insert(key, id);
        Ok(id)
    }

    fn integrate_item(&mut self, node_id: NodeId) -> Result<(), ReadError> {
        let Some(parent_id) = self.nodes[node_id as usize].parent() else {
            let node = &mut self.nodes[node_id as usize];
            node.set_kind(RawNodeKind::Gc);
            node.content = RawContent::None;
            node.set_deleted(true);
            node.set_countable(false);
            node.set_integrated(true);
            return Ok(());
        };

        let mut left = self.nodes[node_id as usize].left();
        let mut right = self.nodes[node_id as usize].right();
        let parent_sub = self.nodes[node_id as usize].parent_sub();
        let right_is_null_or_has_left =
            right.is_none() || right.is_some_and(|id| self.nodes[id as usize].left().is_some());
        let left_has_other_right = left.is_some_and(|id| self.nodes[id as usize].right() != right);

        if (left.is_none() && right_is_null_or_has_left) || left_has_other_right {
            let conflict = if let Some(left) = left {
                self.nodes[left as usize].right()
            } else if let Some(key) = parent_sub {
                self.types[parent_id as usize].map.get(&key).copied()
            } else {
                self.types[parent_id as usize].start
            };
            let this = self.conflict_item(node_id);
            left = find_conflict_left(
                this,
                left,
                conflict,
                right,
                |id| Some(self.conflict_item(*id)),
                |id| self.nodes[*id as usize].right(),
                |id| self.locate(id).ok().map(|(_, node_id)| self.nodes[node_id as usize].id),
            );
        }

        if let Some(left_id) = left {
            right = self.nodes[left_id as usize].right();
            self.nodes[left_id as usize].set_right(Some(node_id));
            self.nodes[node_id as usize].set_left(Some(left_id));
        } else if parent_sub.is_some() {
            right = None;
            self.nodes[node_id as usize].set_left(None);
        } else {
            right = self.types[parent_id as usize].start.replace(node_id);
            self.nodes[node_id as usize].set_left(None);
        }

        if let Some(right_id) = right {
            self.nodes[right_id as usize].set_left(Some(node_id));
        }
        self.nodes[node_id as usize].set_right(right);
        self.nodes[node_id as usize].set_integrated(true);

        let mut overwritten = None;
        if right.is_none()
            && let Some(key) = parent_sub
        {
            self.types[parent_id as usize].map.insert(key, node_id);
            overwritten = self.nodes[node_id as usize].left();
        }

        let parent_deleted = self.types[parent_id as usize]
            .owner
            .is_some_and(|owner| self.nodes[owner as usize].deleted());
        if parent_deleted || (parent_sub.is_some() && right.is_some()) {
            self.delete_node(node_id)?;
        } else if let Some(overwritten) = overwritten {
            self.delete_node(overwritten)?;
        }
        Ok(())
    }

    fn conflict_item(&self, node_id: NodeId) -> ConflictItem {
        let node = &self.nodes[node_id as usize];
        ConflictItem {
            id: node.id,
            origin_left: node.origin_left(),
            origin_right: node.origin_right(),
        }
    }

    fn locate(&self, id: Id) -> Result<(usize, NodeId), ReadError> {
        let nodes = self
            .clients
            .get(&id.client)
            .ok_or(ReadError::IncompleteSnapshot("struct client not found"))?;
        let index = find_clock_segment(nodes.len(), id.clock, |index| {
            nodes.get(index).map(|id| {
                let node = &self.nodes[*id as usize];
                (node.id.clock, node.len)
            })
        })
        .ok_or(ReadError::IncompleteSnapshot("struct clock not found"))?;
        Ok((index, nodes[index]))
    }

    fn split_right(&mut self, id: Id) -> Result<NodeId, ReadError> {
        let (index, node_id) = self.locate(id)?;
        let node = &self.nodes[node_id as usize];
        let offset = id.clock - node.id.clock;
        if offset > 0 && node.kind() == RawNodeKind::Item {
            return self.split_node(id.client, index, offset).map(|(_, right)| right);
        }
        Ok(node_id)
    }

    fn split_left(&mut self, id: Id) -> Result<NodeId, ReadError> {
        let (index, node_id) = self.locate(id)?;
        let node = &self.nodes[node_id as usize];
        let offset = id.clock - node.id.clock;
        if offset + 1 < node.len && node.kind() == RawNodeKind::Item {
            return self.split_node(id.client, index, offset + 1).map(|(left, _)| left);
        }
        Ok(node_id)
    }

    fn split_node(&mut self, client: u64, index: usize, offset: u64) -> Result<(NodeId, NodeId), ReadError> {
        if self.nodes.len() >= self.limits.max_structs {
            return Err(ReadError::ResourceLimit("virtual struct splits"));
        }
        let left_id = self.clients[&client][index];
        let original = self.nodes[left_id as usize].clone();
        if offset == 0 || offset >= original.len || original.kind() != RawNodeKind::Item {
            return Err(ReadError::InvalidUpdate(JwstCodecError::ItemSplitNotSupport));
        }
        if matches!(original.content, RawContent::Type(_)) {
            return Err(ReadError::InvalidUpdate(JwstCodecError::ContentSplitNotSupport(offset)));
        }
        let right_id: NodeId = self
            .nodes
            .len()
            .try_into()
            .map_err(|_| ReadError::ResourceLimit("virtual struct splits"))?;
        let right_clock = original.id.clock.checked_add(offset).ok_or(ReadError::InvalidUpdate(
            JwstCodecError::StructClockInvalid {
                expect: original.id.clock,
                actually: u64::MAX,
            },
        ))?;
        let mut right = original.clone();
        right.id = Id::new(client, right_clock);
        right.len = original.len - offset;
        right.content_offset = original.content_offset + offset;
        right.set_origin_left(Some(Id::new(client, right_clock - 1)));
        right.set_origin_right(original.origin_right());
        right.set_left(original.integrated().then_some(left_id));
        right.set_right(original.right());
        {
            let left = &mut self.nodes[left_id as usize];
            left.len = offset;
            if left.integrated() {
                left.set_right(Some(right_id));
            }
        }
        if original.integrated()
            && let Some(old_right) = original.right()
        {
            self.nodes[old_right as usize].set_left(Some(right_id));
        }
        self.nodes.push(right);
        self.clients.get_mut(&client).unwrap().insert(index + 1, right_id);
        Ok((left_id, right_id))
    }

    fn apply_delete_set(&mut self) -> Result<(), ReadError> {
        let mut delete_sets = ClientMap::<OrderRange>::default();
        for (client, range) in std::mem::take(&mut self.deletes) {
            delete_sets.entry(client).or_default().push(range);
        }
        let mut clients = delete_sets.keys().copied().collect::<Vec<_>>();
        clients.sort_unstable();
        for client in clients {
            for range in delete_sets[&client].canonical_ranges() {
                let Some(nodes) = self.clients.get(&client) else {
                    return Err(ReadError::IncompleteSnapshot("delete-set client not found"));
                };
                let state = nodes
                    .last()
                    .map(|id| {
                        let node = &self.nodes[*id as usize];
                        node.id.clock.saturating_add(node.len)
                    })
                    .unwrap_or(0);
                if range.end > state {
                    return Err(ReadError::IncompleteSnapshot("delete-set range exceeds state"));
                }
                self.split_right(Id::new(client, range.start))?;
                self.split_left(Id::new(client, range.end - 1))?;
                let start = self.locate(Id::new(client, range.start))?.0;
                let end = self.locate(Id::new(client, range.end - 1))?.0;
                let ids = self.clients[&client][start..=end].to_vec();
                for id in ids {
                    if self.nodes[id as usize].kind() == RawNodeKind::Item {
                        self.delete_node(id)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn delete_node(&mut self, node_id: NodeId) -> Result<(), ReadError> {
        let mut pending = vec![node_id];
        let mut visited = 0usize;
        while let Some(node_id) = pending.pop() {
            if self.nodes[node_id as usize].deleted() {
                continue;
            }
            self.nodes[node_id as usize].set_deleted(true);
            visited += 1;
            if visited > self.nodes.len() {
                return Err(ReadError::InvalidUpdate(JwstCodecError::InvalidParent));
            }
            let RawContent::Type(ty) = &self.nodes[node_id as usize].content else {
                continue;
            };
            let ty = *ty;
            let mut cursor = self.types[ty as usize].start;
            let mut remaining = self.nodes.len();
            while let Some(child) = cursor {
                pending.push(child);
                cursor = self.nodes[child as usize].right();
                if remaining == 0 {
                    return Err(ReadError::InvalidUpdate(JwstCodecError::InvalidParent));
                }
                remaining -= 1;
            }
            pending.extend(self.types[ty as usize].map.values().copied());
        }
        Ok(())
    }

    fn freeze(self) -> Result<ReadDoc, ReadError> {
        let mut any = Vec::new();
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

    fn freeze_value(&self, node_id: NodeId, any: &mut Vec<Any>) -> Result<Option<FrozenValue>, ReadError> {
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
        Ok(Some(FrozenValue {
            content,
            content_offset: node.content_offset,
            len: node.len,
        }))
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

struct IntegrationOrder {
    clients: Vec<u64>,
    current: Option<u64>,
    cursors: HashMap<u64, usize>,
}

impl IntegrationOrder {
    fn new(clients: &crate::doc::ClientMap<Vec<NodeId>>) -> Self {
        let mut ids = clients.keys().copied().collect::<Vec<_>>();
        ids.sort_unstable();
        let current = ids.pop();
        Self {
            clients: ids,
            current,
            cursors: HashMap::default(),
        }
    }

    fn next(&mut self, builder: &Builder) -> Option<NodeId> {
        while let Some(client) = self.current {
            if let Some(node) = self.next_for(builder, client) {
                return Some(node);
            }
            self.current = self.clients.pop();
        }
        None
    }

    fn next_for(&mut self, builder: &Builder, client: u64) -> Option<NodeId> {
        let cursor = self.cursors.entry(client).or_default();
        let result = builder.clients.get(&client)?.get(*cursor).copied();
        if result.is_some() {
            *cursor += 1;
        }
        result
    }
}
