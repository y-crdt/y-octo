mod client_blocks;

mod item_space;
use std::{collections::VecDeque, mem, ops::Range};

pub(crate) use client_blocks::{BlockKind, BlockRef, ClientBlocks};
pub(crate) use item_space::{ItemIdx, ItemSpace};

use super::*;
use crate::{
    doc::StateVector,
    sync::{Arc, RwLock, Weak},
};

pub type ChangedTypeRefs = HashMap<TypeIdx, Vec<SmolStr>>;

/// What one transaction changed, collected by the store's mutation paths.
#[derive(Debug, Default)]
pub(crate) struct Collector {
    /// changed item's parent, value is the parent's sub key if exists
    pub changed: ChangedTypeRefs,
    /// Ranges deleted for the first time: the only ranges GC looks at.
    pub deleted: DeleteSet,
    /// Merge candidates besides `deleted` and the new structs: right halves
    /// of split structs, already deleted children of deleted types, and
    /// children replaced by GC structs.
    pub merges: Vec<Id>,
    /// Subdocument items integrated by this transaction, with their GUIDs.
    pub subdocs_added: Vec<(Id, String)>,
    /// GUIDs of subdocument items integrated before this transaction and
    /// deleted by it.
    pub subdocs_removed: Vec<String>,
}

impl Collector {
    pub fn is_empty(&self) -> bool {
        self.changed.is_empty()
            && self.deleted.is_empty()
            && self.merges.is_empty()
            && self.subdocs_added.is_empty()
            && self.subdocs_removed.is_empty()
    }
}

/// A type whose children [DocStore::delete_item_inner] is deleting.
struct DeleteFrame {
    ty: TypeIdx,
    /// next list item to visit
    cursor: ItemRef,
    /// map values left to visit, once the list is done
    map_values: Option<std::vec::IntoIter<ItemRef>>,
}

impl DeleteFrame {
    fn new(types: &TypeArena, ty: TypeIdx) -> Self {
        let cursor = types.get(ty).map(|ty| ty.start).unwrap_or_default();
        Self {
            ty,
            cursor,
            map_values: None,
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct DocStore {
    client: Client,
    pub items: ClientMap<ClientBlocks>,
    // Monotonic for integrated structs, including wire GC and ContentDeleted
    // that never pass through the ordinary delete collector.
    has_deleted_structs: bool,

    // following fields are only used in memory
    /// Every type of the document: named roots, nested types, and
    /// preliminary types that are not inserted yet.
    pub type_arena: TypeArena,
    /// The named roots, by name.
    pub types: HashMap<String, TypeIdx>,
    pub pending: Option<Update>,
    pub last_optimized_state: StateVector,
    // local redo mapping, old id range -> recreated id range
    pub redone: RedoMap,
    /// What the running transaction changed; empty between transactions.
    pub collector: Collector,
    /// ID ranges garbage collection must keep, see
    /// [DocStore::set_retained]. Owned by the history layer.
    pub retained: DeleteSet,
    /// Whether commits garbage-collect deleted content.
    pub gc: bool,
    /// Without the `random` feature: local transactions are refused until the
    /// host sets a client ID, because none was assigned (a subdocument read
    /// from a document) or a remote update showed another replica using this
    /// one. See [Doc::client_required].
    pub client_required: bool,
    /// This is the private editing store of a preliminary subtree, see
    /// [DocStore::edit_type]: it never commits and holds no types of its own.
    pub(crate) staging: bool,
    /// Sequence number of the last commit.
    pub commit_seq: u64,
    pub events: Arc<EventHub>,
    /// History stage of the commit pipeline.
    pub history_hook: Option<Box<dyn CommitHook>>,
}

pub(crate) type StoreRef = Arc<RwLock<DocStore>>;
pub(crate) type WeakStoreRef = Weak<RwLock<DocStore>>;

impl PartialEq for DocStore {
    fn eq(&self, other: &Self) -> bool {
        self.client == other.client
    }
}

impl DocStore {
    pub fn with_client(client: Client) -> Self {
        Self {
            client,
            ..Default::default()
        }
    }

    /// The private editing store of a preliminary subtree.
    pub(crate) fn staging() -> Self {
        Self {
            staging: true,
            ..Default::default()
        }
    }

    pub fn client(&self) -> Client {
        self.client
    }

    pub fn set_client(&mut self, client: Client) {
        self.client = client;
        self.client_required = false;
    }

    pub fn clients(&self) -> Vec<Client> {
        self.items.keys().cloned().collect()
    }

    #[cfg(feature = "debug")]
    pub fn total_nodes(&self) -> usize {
        self.items.values().map(|v| v.len()).sum()
    }

    #[cfg(feature = "debug")]
    pub fn total_delete_sets(&self) -> usize {
        Self::generate_delete_set(&self.items)
            .values()
            .map(|v| v.ranges_len())
            .sum()
    }

    #[cfg(feature = "debug")]
    pub fn total_types(&self) -> usize {
        self.types.len()
    }

    /// Types the store holds besides its named roots: nested, preliminary
    /// and retired ones.
    #[cfg(feature = "debug")]
    pub fn total_dangling_types(&self) -> usize {
        self.type_arena.len().saturating_sub(self.types.len())
    }

    #[cfg(feature = "debug")]
    pub fn total_pending_nodes(&self) -> usize {
        self.pending.as_ref().map(|p| p.structs.len()).unwrap_or(0)
    }

    pub fn get_state(&self, client: Client) -> Clock {
        self.items.get(&client).map_or(0, |blocks| blocks.end_clock)
    }

    pub fn get_state_vector(&self) -> StateVector {
        Self::items_as_state_vector(&self.items)
    }

    pub fn get_delete_sets(&self) -> DeleteSet {
        Self::generate_delete_set(&self.items)
    }

    fn items_as_state_vector(items: &ClientMap<ClientBlocks>) -> StateVector {
        let mut state = StateVector::default();
        for (&client, blocks) in items {
            if blocks.len() != 0 {
                state.insert(client, blocks.end_clock);
            }
        }
        state
    }

    pub fn add_node(&mut self, node: Node) -> JwstCodecResult {
        if node.len() == 0 {
            return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()));
        }
        self.items.entry(node.client()).or_default().append(
            BlockRef {
                clock: node.clock(),
                kind: node.kind,
            },
            node.len(),
        )?;
        self.has_deleted_structs |= node.deleted();
        Ok(())
    }

    pub fn get_node_index(blocks: &ClientBlocks, clock: Clock) -> Option<usize> {
        blocks.find(clock)
    }

    pub fn create_item(
        &self,
        content: Content,
        left: ItemRef,
        right: ItemRef,
        parent: Option<TypeIdx>,
        parent_sub: Option<SmolStr>,
    ) -> Item {
        Item::new(
            &self.type_arena.items,
            Id::new(self.client(), self.get_state(self.client())),
            content,
            left,
            right,
            parent,
            parent_sub,
        )
    }

    pub fn get_node<I: Into<Id>>(&self, id: I) -> Option<Node> {
        self.get_node_with_idx(id).map(|(node, _)| node)
    }

    pub(crate) fn get_node_id(&self, id: Id) -> Option<Id> {
        let blocks = self.items.get(&id.client)?;
        Some(Id::new(id.client, blocks.blocks[blocks.find(id.clock)?].clock))
    }

    pub fn get_node_with_idx<I: Into<Id>>(&self, id: I) -> Option<(Node, usize)> {
        let id = id.into();
        let blocks = self.items.get(&id.client)?;
        let pos = blocks.find(id.clock)?;
        Some((blocks.node(id.client, pos)?, pos))
    }

    pub fn split_node<I: Into<Id>>(&mut self, id: I, diff: u64) -> JwstCodecResult<(Node, Node)> {
        let id = id.into();
        let (left, pos) = self
            .get_node_with_idx(id)
            .ok_or(JwstCodecError::StructSequenceNotExists(id.client))?;
        let left_idx = left.as_item().ok_or(JwstCodecError::ItemSplitNotSupport)?;
        let items = &mut self.type_arena.items;
        items.check_capacity(1)?;
        let item = items.get_mut(left_idx).expect("stored item");
        debug_assert!(diff > 0 && diff < item.len);
        let content = item.content.split_in_place(diff)?;
        let len = item.len - diff;
        item.len = diff;
        let id = Id::new(id.client, item.id.clock + diff);
        let next = item.right;
        let mut right = Item {
            id,
            len,
            content,
            parent: item.parent,
            parent_sub: item.parent_sub.clone(),
            left: Some(left_idx),
            right: next,
            flags: item.flags,
            ..Item::default()
        };
        right.set_origin_left_id(Some(item.last_id()));
        right.set_origin_right_id(item.origin_right_id());
        let update_key = if next.is_none() {
            match (&right.parent, &right.parent_sub) {
                (Some(parent), Some(key)) => Some((*parent, key.clone())),
                _ => None,
            }
        } else {
            None
        };
        let right_idx = items.alloc(right)?;
        items.get_mut(left_idx).expect("left item").right = Some(right_idx);
        if let Some(next) = next {
            items.get_mut(next).expect("right neighbor").left = Some(right_idx);
        }
        if let Some((parent, key)) = update_key {
            self.type_arena[parent].map_set(key, Some(right_idx));
        }
        let kind = if left.deleted() {
            BlockKind::DeletedItem(right_idx)
        } else {
            BlockKind::Item(right_idx)
        };
        self.items
            .get_mut(&id.client)
            .expect("stored client")
            .blocks
            .insert(pos + 1, BlockRef { clock: id.clock, kind });
        self.collector.merges.push(id);
        Ok((Node { len: diff, ..left }, Node { id, len, kind }))
    }

    pub fn split_at_and_get_right<I: Into<Id>>(&mut self, id: I) -> JwstCodecResult<Node> {
        let id = id.into();
        let node = self
            .get_node(id)
            .ok_or(JwstCodecError::StructSequenceNotExists(id.client))?;
        let offset = id.clock - node.clock();
        if offset != 0 && node.is_item() {
            Ok(self.split_node(id, offset)?.1)
        } else {
            Ok(node)
        }
    }

    pub fn split_at_and_get_left<I: Into<Id>>(&mut self, id: I) -> JwstCodecResult<Node> {
        let id = id.into();
        let node = self
            .get_node(id)
            .ok_or(JwstCodecError::StructSequenceNotExists(id.client))?;
        let cut = id.clock - node.clock() + 1;
        if cut < node.len() && node.is_item() {
            Ok(self.split_node(id, cut)?.0)
        } else {
            Ok(node)
        }
    }

    #[cfg(test)]
    pub fn self_check(&self) -> JwstCodecResult {
        let mut owned = HashSet::new();
        let timelines = std::iter::once(self).chain(self.type_arena.types().filter_map(|ty| ty.preliminary.as_deref()));
        for timeline in timelines {
            for (&client, blocks) in &timeline.items {
                for n in blocks.nodes(client) {
                    if let Some(idx) = n.as_item() {
                        let item = self
                            .type_arena
                            .items
                            .get(idx)
                            .ok_or(JwstCodecError::StructSequenceNotExists(client))?;
                        if item.id != n.id || item.len != n.len || item.deleted() != n.deleted() || !owned.insert(idx) {
                            return Err(JwstCodecError::StructSequenceInvalid {
                                client_id: client,
                                clock: n.clock(),
                            });
                        }
                    }
                }
            }
        }
        let check = |idx| {
            if owned.contains(&idx) {
                Ok(())
            } else {
                Err(JwstCodecError::IncompleteDocument(
                    "item slot has no timeline owner".into(),
                ))
            }
        };
        for (idx, item) in self.type_arena.items.live() {
            check(idx)?;
            for link in [item.left, item.right].into_iter().flatten() {
                check(link)?;
            }
        }
        for ty in self.type_arena.types() {
            for link in [ty.start, ty.carrier_ref()]
                .into_iter()
                .flatten()
                .chain(ty.map_iter().filter_map(|(_, link)| *link))
                .chain(
                    ty.markers
                        .iter()
                        .flat_map(|markers| markers.iter().filter_map(|marker| marker.ptr)),
                )
            {
                check(link)?;
            }
        }
        Ok(())
    }

    // only for creating named type
    pub fn get_or_create_type(&mut self, name: &str) -> JwstCodecResult<TypeIdx> {
        if let Some(ty) = self.types.get(name) {
            return Ok(*ty);
        }

        let ty = self
            .type_arena
            .alloc(YType::new_root(YTypeKind::Unknown, None, name.to_string()))?;
        self.types.insert(name.to_string(), ty);
        Ok(ty)
    }

    /// Resolve the wire origins and parent before publishing an item.
    fn repair(&mut self, item: &mut Item, parent: Option<WireParent>, offset: u64) -> JwstCodecResult {
        // Same-client origins are never deferred by the update iterator, which
        // assumes they precede the item; an item cannot anchor to a struct
        // created at or after itself (as `ReadDoc` checks).
        for origin in [item.origin_left_id(), item.origin_right_id()].into_iter().flatten() {
            if origin.client == item.id.client && origin.clock >= item.id.clock {
                return Err(JwstCodecError::InvalidParent);
            }
        }

        if let Some(left_id) = item.origin_left_id() {
            if let Some(left_ref) = self.split_at_and_get_left(left_id)?.as_item() {
                item.set_origin_left_id(self.type_arena.items.get(left_ref).map(|left| left.last_id()));
                item.left = Some(left_ref);
            } else {
                item.set_origin_left_id(None);
            }
        }

        if let Some(right_id) = item.origin_right_id() {
            if let Some(right_ref) = self.split_at_and_get_right(right_id)?.as_item() {
                item.set_origin_right_id(self.type_arena.items.get(right_ref).map(|right| right.id));
                item.right = Some(right_ref);
            } else {
                item.set_origin_right_id(None);
            }
        }

        match &parent {
            // root level named type
            // doc.get_or_create_text("content");
            //                         ^^^^^^^ WireParent::Root("content")
            Some(WireParent::Root(str)) => {
                if !self.types.contains_key(str.as_str()) {
                    self.type_arena.items.check_capacity(1 + usize::from(offset > 0))?;
                }
                let ty = self.get_or_create_type(str)?;
                item.parent.replace(ty);
            }
            // type as item
            // let text = doc.create_text();
            // let mut map = doc.get_or_create_map("content");
            // map.insert("p1", text);
            //
            // Item { id: (1, 0), content: Content::Type(_) }
            //        ^^ WireParent::Item((1, 0))
            // A same-client parent at or after the item cannot have been
            // created before it. Only a partially integrated item (offset > 0)
            // could find such a struct in the store, possibly its own prefix;
            // treat the parent as missing, like any parent not yet integrated,
            // so the item is kept as a GC range instead of being linked.
            Some(WireParent::Item(parent_id))
                if parent_id.client == item.id.client && parent_id.clock >= item.id.clock =>
            {
                item.parent = None;
            }
            Some(WireParent::Item(parent_id)) => {
                // Only an integrated carrier can back a stored parent identity.
                // The update iterator defers missing cross-client dependencies.
                item.parent = self.get_node(*parent_id).and_then(|node| {
                    let carrier = node.as_item();
                    match &self.type_arena.items.get(carrier?)?.content {
                        Content::Type(ty) => Some(*ty),
                        _ => None,
                    }
                });
            }
            // no item.parent, borrow left.parent or right.parent
            None => {
                if let Some(left) = item.left.and_then(|i| self.type_arena.items.get(i)) {
                    item.parent = left.parent;
                    item.parent_sub = left.parent_sub.clone();
                } else if let Some(right) = item.right.and_then(|i| self.type_arena.items.get(i)) {
                    item.parent = right.parent;
                    item.parent_sub = right.parent_sub.clone();
                }
            }
        };

        Ok(())
    }

    pub(crate) fn integrate_wire(&mut self, wire: WireStruct, offset: u64) -> JwstCodecResult {
        let wire = match wire {
            WireStruct::Gc { id, len } => {
                let len = len
                    .checked_sub(offset)
                    .filter(|&n| n > 0)
                    .ok_or_else(|| JwstCodecError::IncompleteDocument("zero-length struct".into()))?;
                return self.add_node(Node::new_gc(id + offset, len));
            }
            WireStruct::Skip { id, len } => return self.add_node(Node::new_skip(id, len)),
            WireStruct::Item(wire) => *wire,
        };
        let WireItem {
            id,
            len,
            origin_left_id,
            origin_right_id,
            parent,
            parent_sub,
            content,
            flags,
        } = wire;
        let mut item = Item {
            id,
            len,
            left: None,
            right: None,
            parent: None,
            parent_sub,
            // repair resolves neighbors and the parent, never the content,
            // which is stored only once those are known to exist
            content: Content::Deleted(len),
            flags: flags.into(),
            ..Item::default()
        };
        item.set_origin_left_id(origin_left_id);
        item.set_origin_right_id(origin_right_id);
        // Every type this struct adds, its own and the root it may name for
        // the first time, fits or none is added: a root is not left behind
        // for a type that found no slot.
        let new_root = matches!(&parent, Some(WireParent::Root(name)) if !self.types.contains_key(name.as_str()));
        let new_type = matches!(content, WireContent::Type { .. });
        self.type_arena
            .check_capacity(usize::from(new_root) + usize::from(new_type))?;
        if len <= offset {
            return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()));
        }
        self.repair(&mut item, parent, offset)?;

        // A type decoded from the wire enters the arena with its carrier and
        // leaves it again unless that carrier ends up in the store: nothing
        // else can refer to the new slot before then.
        let types_before = self.type_arena.len();
        item.content = content.into_content(&mut self.type_arena)?;
        let child = match &item.content {
            Content::Type(ty) => Some(*ty),
            _ => None,
        };
        let result = self.integrate_item(item, offset, None);
        if child.is_some() && !matches!(result, Ok(Some(_))) {
            self.type_arena.rollback(types_before);
        }
        result.map(|_| ())
    }

    pub fn integrate_item(&mut self, mut this: Item, offset: u64, parent: Option<TypeIdx>) -> JwstCodecResult<ItemRef> {
        if this.len() <= offset {
            return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()));
        }
        if offset > 0 {
            this.id.clock += offset;
            if let Some(left_ref) = self
                .split_at_and_get_left(Id::new(this.id.client, this.id.clock - 1))?
                .as_item()
            {
                // The integrated prefix of this item becomes its left
                // neighbor. In honest updates it is the same item, so
                // it lives in the same list; a byzantine update can
                // claim another container for the remainder, which
                // would splice two lists together (or delete the
                // parent's own carrier as the "previous map value").
                if let Some(left) = self.type_arena.items.get(left_ref)
                    && !Self::same_container(left, &this)
                {
                    return Err(JwstCodecError::InvalidParent);
                }
                this.set_origin_left_id(self.type_arena.items.get(left_ref).map(|left| left.last_id()));
                this.left = Some(left_ref);
            }
            let right_content = this.content.split(offset)?.1;
            this.replace_content_with_len(right_content, this.len - offset);
        }

        if let Some(ty) = &this.parent {
            // Corrupt updates may nest a type into itself or one of its
            // own descendants. Deleting or collecting the items of
            // such cyclic types would never end, so reject the cycle
            // here instead.
            if let Content::Type(inner) = &this.content {
                if inner == ty {
                    return Err(JwstCodecError::InvalidParent);
                }
                // An update can claim any stored type as the parent,
                // so walk its ancestors. Local callers insert a type
                // they checked before (`check_insertable`) and can
                // only create direct loops, checked above.
                if parent.is_none() {
                    let mut visited = HashSet::new();
                    let mut ancestor = self.type_arena.parent_of(*ty);
                    while let Some(current) = ancestor {
                        if !visited.insert(current) {
                            break;
                        }
                        if current == *inner {
                            return Err(JwstCodecError::InvalidParent);
                        }
                        ancestor = self.type_arena.parent_of(current);
                    }
                }
            }
        }

        let parent = parent.or(this.parent);

        let parent = parent.and_then(|parent| {
            let ty = self.type_arena.get(parent)?;
            let deleted = match ty.carrier(&self.type_arena.items) {
                Carrier::Live(item) => item.deleted(),
                // Named roots and private staging roots have no
                // carrier.
                Carrier::Unset if ty.root_name().is_some() || ty.is_preliminary() => false,
                // Collection either replaced the containing item or
                // dropped its type content.
                _ => return None,
            };
            Some((parent, deleted))
        });

        if let (Some(ty), Some((parent, parent_deleted))) = (this.parent, parent) {
            // Neighbors resolved from origins must share this item's
            // list; otherwise linking would cross containers.
            for neighbor in [&this.left, &this.right] {
                if let Some(neighbor) = neighbor.and_then(|i| self.type_arena.items.get(i))
                    && !Self::same_container(neighbor, &this)
                {
                    return Err(JwstCodecError::InvalidParent);
                }
            }
            let publish_child = self.type_arena[parent].published;
            let is_format = matches!(this.content, Content::Format(_));
            let mut left = this.left;
            let right = this.right;

            let right_is_null_or_has_left = match right.and_then(|i| self.type_arena.items.get(i)) {
                None => true,
                Some(r) => r.left.is_some(),
            };

            let left_has_other_right_than_self = match left.and_then(|i| self.type_arena.items.get(i)) {
                Some(left) => left.right != right,
                _ => false,
            };

            // conflicts
            if left.is_none() && right_is_null_or_has_left || left_has_other_right_than_self {
                // set the first conflicting item
                let conflict = if let Some(left) = left.and_then(|i| self.type_arena.items.get(i)) {
                    left.right
                } else if let Some(parent_sub) = &this.parent_sub {
                    // The map stores the winning tail; conflict
                    // scanning without a left neighbor must start at
                    // the chain head.
                    self.type_arena[parent]
                        .map_get(parent_sub)
                        .and_then(|item| self.head(*item))
                } else {
                    self.type_arena[parent].start
                };

                left = find_conflict_left(
                    ConflictItem {
                        id: this.id,
                        origin_left: this.origin_left_id(),
                        origin_right: this.origin_right_id(),
                    },
                    left,
                    conflict,
                    right,
                    |item| {
                        self.type_arena.items.get(*item).map(|item| ConflictItem {
                            id: item.id,
                            origin_left: item.origin_left_id(),
                            origin_right: item.origin_right_id(),
                        })
                    },
                    |item| self.type_arena.items.get(*item).and_then(|item| item.right),
                    |id| self.get_node_id(id),
                );
            }

            let right = if let Some(left) = left {
                self.type_arena.items.get(left).expect("left neighbor").right
            } else if let Some(ref key) = this.parent_sub {
                self.type_arena[parent].map_get(key).and_then(|i| self.head(*i))
            } else {
                self.type_arena[parent].start
            };
            this.left = left;
            this.right = right;
            let id = this.id;
            let len = this.len;
            let key = this.parent_sub.clone();
            let child = if let Content::Type(child) = this.content {
                Some(child)
            } else {
                None
            };
            let deleted = this.deleted();
            let countable = this.countable();
            let new_subdoc = match &this.content {
                Content::Doc(doc) => Some(doc.guid.clone()),
                _ => None,
            };
            self.check_append(id, len)?;
            let prepared = child
                .filter(|child| self.type_arena[*child].preliminary.is_some())
                .map(|child| self.prepare_preliminary(child, id, len))
                .transpose()?;
            let idx = self.type_arena.items.alloc(this)?;
            if is_format {
                self.type_arena[parent].has_formatting = true;
            }
            let kind = if deleted {
                BlockKind::DeletedItem(idx)
            } else {
                BlockKind::Item(idx)
            };
            self.add_node(Node { id, len, kind })?;
            if let Some(left) = left {
                self.type_arena.items.get_mut(left).expect("left neighbor").right = Some(idx);
            } else if key.is_none() {
                self.type_arena[parent].start = Some(idx);
            }
            if let Some(right) = right {
                self.type_arena.items.get_mut(right).expect("right neighbor").left = Some(idx);
            } else if let Some(key) = &key {
                self.type_arena[parent].map_set(key.clone(), Some(idx));
                if let Some(left) = left {
                    self.delete_item(left, Some(parent));
                }
            }
            if let Some(child) = child {
                self.type_arena[child].attach(Some(idx), Some(parent));
                if publish_child {
                    self.type_arena[child].published = true;
                }
            }
            if let Some(guid) = new_subdoc {
                self.collector.subdocs_added.push((id, guid));
            }
            if parent_deleted || key.is_some() && right.is_some() {
                self.delete_item(idx, Some(parent));
            } else if key.is_none() && countable {
                self.type_arena[parent].len += len;
            }
            Self::mark_changed(&mut self.collector.changed, ty, key);
            if let Some(prepared) = prepared {
                prepared.mount(self)?;
            }
            Ok(Some(idx))
        } else {
            self.add_node(Node::new_gc(this.id, this.len()))?;
            Ok(None)
        }
    }

    fn check_append(&self, id: Id, len: u64) -> JwstCodecResult {
        if let Some(blocks) = self.items.get(&id.client)
            && blocks.len() != 0
            && blocks.end_clock != id.clock
        {
            return Err(JwstCodecError::StructClockInvalid {
                expect: blocks.end_clock,
                actually: id.clock,
            });
        }
        id.clock
            .checked_add(len)
            .ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
        Ok(())
    }

    fn head(&self, mut cursor: ItemRef) -> ItemRef {
        while let Some(left) = cursor
            .and_then(|i| self.type_arena.items.get(i))
            .and_then(|item| item.left)
        {
            cursor = Some(left);
        }
        cursor
    }

    /// Whether two items are in the same list: the same parent type and, for
    /// map entries, the same key. An item whose parent was not resolved is
    /// collected instead of linked, so it matches anything.
    fn same_container(other: &Item, this: &Item) -> bool {
        match (&other.parent, &this.parent) {
            (Some(a), Some(b)) => a == b && other.parent_sub == this.parent_sub,
            (_, Some(_)) => false,
            _ => true,
        }
    }

    pub fn delete_item(&mut self, idx: ItemIdx, parent: Option<TypeIdx>) {
        let mut deleted = HashMap::new();
        self.delete_item_inner(idx, parent, &mut deleted);
        self.add_deleted(deleted);
    }

    fn add_deleted(&mut self, ranges: HashMap<Client, Vec<Range<u64>>>) {
        for (client, ranges) in ranges {
            self.collector.deleted.batch_add_ranges(client, ranges);
        }
    }

    fn delete_item_inner(
        &mut self,
        idx: ItemIdx,
        parent: Option<TypeIdx>,
        deleted: &mut HashMap<Client, Vec<Range<Clock>>>,
    ) {
        let Some(ty) = self.delete_one(idx, parent, deleted) else {
            return;
        };
        let mut stack = vec![DeleteFrame::new(&self.type_arena, ty)];
        while let Some(frame) = stack.last_mut() {
            let ty = frame.ty;
            let next = if let Some(cursor) = frame.cursor {
                frame.cursor = self.type_arena.items.get(cursor).expect("child").right;
                Some(cursor)
            } else {
                frame
                    .map_values
                    .get_or_insert_with(|| {
                        self.type_arena[ty]
                            .map_values()
                            .copied()
                            .collect::<Vec<_>>()
                            .into_iter()
                    })
                    .next()
                    .flatten()
            };
            let Some(child) = next else {
                stack.pop();
                continue;
            };
            let item = self.type_arena.items.get(child).expect("child");
            if item.deleted() {
                self.collector.merges.push(item.id);
            } else if let Some(nested) = self.delete_one(child, Some(ty), deleted) {
                stack.push(DeleteFrame::new(&self.type_arena, nested));
            }
        }
    }

    fn delete_one(
        &mut self,
        idx: ItemIdx,
        parent: Option<TypeIdx>,
        deleted: &mut HashMap<Client, Vec<Range<Clock>>>,
    ) -> Option<TypeIdx> {
        let item = self.type_arena.items.get_mut(idx).expect("stored item");
        if !item.delete() {
            return None;
        }
        let id = item.id;
        let len = item.len;
        let blocks = self.items.get_mut(&id.client).expect("stored client");
        let pos = blocks.find(id.clock).expect("stored clock");
        debug_assert_eq!(blocks.blocks[pos].clock, id.clock);
        debug_assert!(matches!(blocks.blocks[pos].kind, BlockKind::Item(i) | BlockKind::DeletedItem(i) if i == idx));
        blocks.blocks[pos].kind = BlockKind::DeletedItem(idx);
        self.has_deleted_structs = true;
        deleted.entry(id.client).or_default().push(id.clock..id.clock + len);
        let owner = item.parent;
        let visible = item.parent_sub.is_none() && item.countable();
        if let Some(owner) = owner {
            Self::mark_changed(&mut self.collector.changed, owner, item.parent_sub.clone());
        }
        let nested = match &item.content {
            Content::Type(ty) => Some(*ty),
            Content::Doc(doc) => {
                let guid = &doc.guid;
                if let Some(pos) = self.collector.subdocs_added.iter().position(|(old, _)| *old == id) {
                    self.collector.subdocs_added.swap_remove(pos);
                } else {
                    self.collector.subdocs_removed.push(guid.clone());
                }
                None
            }
            _ => None,
        };
        if visible
            && let Some(ty) = parent.or(owner)
            && self.type_arena[ty].len != 0
        {
            self.type_arena[ty].len -= len;
        }
        nested
    }

    pub fn delete_range(&mut self, client: Client, range: Range<Clock>) -> JwstCodecResult {
        let Some(node) = self.get_node(Id::new(client, range.start)) else {
            return Ok(());
        };
        if range.is_empty() {
            return Ok(());
        }
        let split_start = !node.deleted() && node.is_item() && range.start > node.clock();
        let split_end = self
            .get_node(Id::new(client, range.end))
            .is_some_and(|n| n.is_item() && !n.deleted() && range.end > n.clock());
        self.type_arena
            .items
            .check_capacity(usize::from(split_start) + usize::from(split_end))?;
        if split_start {
            self.split_at_and_get_right(Id::new(client, range.start))?;
        }
        let mut clock = range.start;
        let mut deleted = HashMap::new();
        while clock < range.end {
            let Some(node) = self.get_node(Id::new(client, clock)) else {
                break;
            };
            let end = node.clock() + node.len();
            if !node.deleted()
                && let Some(idx) = node.as_item()
            {
                // An earlier carrier may already have deleted this entire item.
                if range.end < end
                    && let Err(err) = self.split_node(node.id, range.end - node.clock())
                {
                    self.add_deleted(deleted);
                    return Err(err);
                }
                self.delete_item_inner(idx, None, &mut deleted);
            }
            clock = end;
        }
        self.add_deleted(deleted);
        Ok(())
    }

    pub fn write_state_as_update<W: CrdtWriter>(&self, sv: &StateVector, encoder: &mut W) -> JwstCodecResult {
        if self.pending.is_some() {
            return self.diff_state_vector(sv)?.write(encoder);
        }

        self.write_structs_since(sv, encoder)?;
        if self.has_deleted_structs {
            Self::generate_delete_set(&self.items).write(encoder)
        } else {
            encoder.write_var_u64(0)
        }
    }

    pub(crate) fn write_structs_since<W: CrdtWriter>(&self, sv: &StateVector, encoder: &mut W) -> JwstCodecResult {
        // The store read lock keeps the borrowed structs alive until encoding
        // finishes. Only a recipient clock inside a struct needs a split.
        let mut clients = Vec::new();
        for (&client, nodes) in &self.items {
            let Some(first) = nodes.blocks.front() else { continue };
            let clock = sv.get(&client).max(first.clock);
            let Some(start) = nodes.find(clock) else { continue };
            let count = nodes.nodes(client).skip(start).filter(|node| node.len > 0).count();
            clients.push((client, clock, nodes, start, count));
        }
        clients.sort_unstable_by_key(|entry| std::cmp::Reverse(entry.0));

        encoder.write_var_u64(clients.len() as u64)?;
        for (client, clock, nodes, start, count) in clients {
            encoder.write_var_u64(count as u64)?;
            encoder.write_var_u64(client)?;
            encoder.write_var_u64(clock)?;
            let first = nodes.node(client, start).expect("first block");
            let offset = clock - first.clock();
            if offset == 0 {
                first.write(&self.type_arena, encoder)?;
            } else {
                WireStruct::from_node(&self.type_arena, &first)?
                    .split_at(offset)?
                    .1
                    .write(encoder)?;
            }
            for node in nodes.nodes(client).skip(start + 1).filter(|node| node.len() > 0) {
                node.write(&self.type_arena, encoder)?;
            }
        }
        Ok(())
    }

    fn diff_state_vector(&self, sv: &StateVector) -> JwstCodecResult<Update> {
        let update_structs = Self::diff_structs(&self.type_arena, &self.items, sv)?;

        let mut update = Update {
            structs: update_structs,
            delete_set: Self::generate_delete_set(&self.items),
            ..Update::default()
        };

        if let Some(pending) = &self.pending {
            // Pending does not mean unknown to the recipient. Apply its SV to
            // these ranges too, while retaining deletions for missing targets.
            let pending = Update {
                structs: Self::diff_ranges(&pending.structs, sv, |n| (n.clock(), n.len()), |n| Ok(n.clone()))?,
                delete_set: pending.delete_set.clone(),
                pending_structs: pending.pending_structs.clone(),
                missing_state: pending.missing_state.clone(),
                pending_delete_set: pending.pending_delete_set.clone(),
            };
            Update::merge_into(&mut update, [pending]);
        }

        Ok(update)
    }

    fn mark_changed(changed: &mut ChangedTypeRefs, parent: TypeIdx, parent_sub: Option<SmolStr>) {
        let vec = changed.entry(parent).or_default();
        if let Some(parent_sub) = parent_sub {
            // only record the sub key if exists
            vec.push(parent_sub);
        }
    }

    #[cfg(test)]
    pub fn get_changed(&mut self) -> ChangedTypeRefs {
        mem::take(&mut self.collector.changed)
    }

    pub(crate) fn diff_structs(
        types: &TypeArena,
        map: &ClientMap<ClientBlocks>,
        sv: &StateVector,
    ) -> JwstCodecResult<ClientMap<VecDeque<WireStruct>>> {
        let mut diff = ClientMap::new();
        for (&client, blocks) in map {
            let Some(first) = blocks.blocks.front() else { continue };
            let clock = sv.get(&client).max(first.clock);
            let Some(start) = blocks.find(clock) else { continue };
            let mut tail = VecDeque::with_capacity(blocks.len() - start);
            for node in blocks.nodes(client).skip(start) {
                let wire = WireStruct::from_node(types, &node)?;
                let offset = clock.saturating_sub(node.clock());
                tail.push_back(if offset != 0 { wire.split_at(offset)?.1 } else { wire });
            }
            diff.insert(client, tail);
        }
        Ok(diff)
    }

    fn diff_ranges<T>(
        map: &ClientMap<VecDeque<T>>,
        sv: &StateVector,
        range: impl Fn(&T) -> (Clock, u64),
        copy: impl Fn(&T) -> JwstCodecResult<WireStruct>,
    ) -> JwstCodecResult<ClientMap<VecDeque<WireStruct>>> {
        let mut diff = ClientMap::new();
        for (&client, nodes) in map {
            let Some((first, last)) = nodes.front().zip(nodes.back()) else {
                continue;
            };
            let clock = sv.get(&client).max(range(first).0);
            let (last_start, last_len) = range(last);
            if clock >= last_start + last_len {
                continue;
            }
            let Some(start) = find_clock_segment(nodes.len(), clock, |idx| nodes.get(idx).map(&range)) else {
                continue;
            };
            let mut tail = VecDeque::with_capacity(nodes.len() - start);
            let first = copy(&nodes[start])?;
            let offset = clock - first.clock();
            tail.push_back(if offset == 0 { first } else { first.split_at(offset)?.1 });
            for n in nodes.range(start + 1..) {
                tail.push_back(copy(n)?);
            }
            diff.insert(client, tail);
        }
        Ok(diff)
    }

    fn generate_delete_set(refs: &ClientMap<ClientBlocks>) -> DeleteSet {
        let mut delete_set = DeleteSet::default();

        for (&client, nodes) in refs {
            let mut deleted = nodes.deleted_ranges();
            let Some(mut current) = deleted.next() else { continue };
            let mut previous = VecDeque::new();
            for node in deleted {
                let start = node.start;
                let end = node.end;
                if start <= current.end {
                    current.end = current.end.max(end);
                } else {
                    previous.push_back(current);
                    current = start..end;
                }
            }
            previous.push_back(current);
            delete_set
                .clients
                .insert(client, OrderRange::from_sorted_disjoint(previous));
        }

        delete_set
    }

    /// Garbage-collects and merges what changed since the last call, after
    /// Yjs v13.6.33 `cleanupTransactions`: GC of the ranges deleted since
    /// then (`tryGcDeleteSet`), merge around them (`tryMergeDeleteSet`),
    /// merge of the structs added since `last_optimized_state` and of the
    /// recorded split points (`_mergeStructs`). The cost follows the size of
    /// the change, not of the document.
    pub fn optimize(&mut self, gc: bool, state: StateVector) {
        let deleted = mem::take(&mut self.collector.deleted);

        if gc {
            self.gc_delete_set(&deleted);
        }
        // includes the children GC just replaced
        let merges = mem::take(&mut self.collector.merges);
        self.merge_delete_set(&deleted);
        self.make_continuous(state);
        self.merge_split_points(&merges);
        if let Some(moved) = self.type_arena.items.finish() {
            for blocks in self.items.values_mut() {
                blocks.remap(&moved);
            }
            self.type_arena.remap_items(&moved);
        }
    }

    /// Full GC and merge over the whole delete set and every struct.
    pub fn optimize_all(&mut self) {
        self.collector.deleted = Self::generate_delete_set(&self.items);
        self.last_optimized_state = StateVector::default();
        self.optimize(true, self.get_state_vector())
    }

    /// Whether GC must keep any part of `len` structs starting at `id`.
    fn is_retained(&self, id: Id, len: u64) -> bool {
        self.retained
            .get(&id.client)
            .is_some_and(|ranges| ranges.into_iter().any(|r| r.start < id.clock + len && id.clock < r.end))
    }

    pub(super) fn gc_delete_set(&mut self, deleted: &DeleteSet) {
        for (client, ranges) in deleted.iter() {
            for range in ranges {
                let Some(mut idx) = self
                    .items
                    .get(client)
                    .and_then(|items| Self::get_node_index(items, range.start))
                else {
                    continue;
                };

                while let Some(node) = self.items.get(client).and_then(|items| items.node(*client, idx)) {
                    if range.end <= node.clock() {
                        break;
                    }

                    if let Some(item_ref) = node.as_item()
                        && let Some(item) = self.type_arena.items.get(item_ref)
                        && item.deleted()
                        && !item.keep()
                        && !self.is_retained(item.id, item.len())
                    {
                        self.gc_item(item_ref, false);
                    }

                    idx += 1;
                }
            }
        }
    }

    /// Yjs `Item.gc`: the content of a type item drops its children (which
    /// become GC structs), then the item either keeps its place with
    /// `ContentDeleted` or, when its parent type is being collected too, is
    /// replaced by a GC struct.
    /// `item_ref` is a live item of this store.
    fn gc_item(&mut self, item_ref: ItemIdx, parent_gced: bool) {
        // An explicit stack instead of recursing through nested types:
        // `Visit` collects an item's children (Yjs `ContentType.gc`) and queues
        // them before its own `Finish`, so children are collected first, in
        // the order Yjs recurses.
        enum Step {
            Visit(ItemIdx, bool),
            Finish(ItemIdx, bool),
        }

        let mut steps = vec![Step::Visit(item_ref, parent_gced)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(item_ref, parent_gced) => {
                    let children = match &self
                        .type_arena
                        .items
                        .get(item_ref)
                        .expect("collected items are live")
                        .content
                    {
                        Content::Type(ty) => self.take_type_children(*ty),
                        _ => Vec::new(),
                    };
                    steps.push(Step::Finish(item_ref, parent_gced));
                    steps.extend(children.into_iter().rev().map(|child| Step::Visit(child, true)));
                }
                Step::Finish(item_ref, parent_gced) => self.gc_item_content(item_ref, parent_gced),
            }
        }
    }

    /// The item half of Yjs `Item.gc`, once the children of its type have
    /// been collected.
    fn gc_item_content(&mut self, item_ref: ItemIdx, parent_gced: bool) {
        let item = self.type_arena.items.get(item_ref).expect("collected items are live");
        debug_assert!(item.deleted());
        let (id, len) = (item.id, item.len());

        // Either way the carrier stops holding its type: retire the type
        // before its item is replaced, or merged away as plain deleted
        // content, so nothing is left pointing at it.
        if let Content::Type(ty) = &item.content
            && let Some(ty) = self.type_arena.get_mut(*ty)
        {
            ty.retire();
        }

        if parent_gced {
            let items = self.items.get_mut(&id.client).expect("live items are in the store");
            let idx = Self::get_node_index(items, id.clock).expect("live items are in the store");
            debug_assert_eq!(items.blocks[idx].clock, id.clock);
            items.blocks[idx].kind = BlockKind::Gc;
            self.type_arena.items.retire(item_ref);
            // Overwritten map values are neither in this delete set nor queued
            // by `delete_item_inner`, so Yjs leaves their GC structs unmerged;
            // queue every replaced child instead.
            self.collector.merges.push(id);
        } else {
            let item = self.type_arena.items.get_mut(item_ref).expect("live item");
            item.replace_content(Content::Deleted(len));
            item.flags.clear_countable();
        }
    }

    /// Yjs `ContentType.gc`: detaches every child of a type whose item is
    /// being collected and returns them for collection.
    pub(crate) fn take_type_children(&mut self, ty: TypeIdx) -> Vec<ItemIdx> {
        let mut children = Vec::new();
        let parent = &self.type_arena[ty];
        let mut next = parent.start;
        while let Some(idx) = next {
            children.push(idx);
            next = self.type_arena.items.get(idx).expect("list child").right;
        }
        for value in parent.map_values() {
            let mut next = *value;
            while let Some(idx) = next {
                children.push(idx);
                next = self.type_arena.items.get(idx).expect("map child").left;
            }
        }
        let parent = &mut self.type_arena[ty];
        parent.start = None;
        parent.clear_map();
        if let Some(markers) = &mut parent.markers {
            markers.clear();
        }
        children
    }

    /// Yjs `tryMergeDeleteSet`: merges the structs in and right after each
    /// deleted range, from right to left.
    pub(super) fn merge_delete_set(&mut self, deleted: &DeleteSet) {
        for (client, ranges) in deleted.iter() {
            let ranges = ranges.into_iter().collect::<Vec<_>>();
            let Some(nodes) = self.items.get_mut(client) else {
                continue;
            };
            for range in ranges.into_iter().rev() {
                let Some(last) = range
                    .end
                    .checked_sub(1)
                    .and_then(|clock| Self::get_node_index(nodes, clock))
                else {
                    continue;
                };
                let mut si = (nodes.len() - 1).min(last + 1);
                while si > 0 && nodes.blocks[si].clock >= range.start {
                    si = si.saturating_sub(1 + Self::merge_with_lefts(&mut self.type_arena, nodes, si));
                }
            }
        }
    }

    /// Merges every struct added since `last_optimized_state`.
    fn make_continuous(&mut self, state: StateVector) {
        for (client, state) in state.iter() {
            let before_state = self.last_optimized_state.get(client);
            if before_state == *state {
                continue;
            }

            let nodes = self.items.get_mut(client).unwrap();
            let first_change = Self::get_node_index(nodes, before_state).unwrap_or(1).max(1);
            let mut idx = nodes.len() - 1;

            while idx > 0 && idx >= first_change {
                idx = idx.saturating_sub(Self::merge_with_lefts(&mut self.type_arena, nodes, idx) + 1);
            }
        }

        self.last_optimized_state = state;
    }

    /// Merges recorded split points with their neighbors (Yjs
    /// `_mergeStructs`).
    fn merge_split_points(&mut self, merges: &[Id]) {
        for id in merges.iter().rev() {
            let Some(nodes) = self.items.get_mut(&id.client) else {
                continue;
            };
            let Some(pos) = Self::get_node_index(nodes, id.clock) else {
                continue;
            };
            if pos + 1 < nodes.len() && Self::merge_with_lefts(&mut self.type_arena, nodes, pos + 1) > 1 {
                // both neighbors are already merged
                continue;
            }
            if pos > 0 {
                Self::merge_with_lefts(&mut self.type_arena, nodes, pos);
            }
        }
    }

    /// Yjs `tryToMergeWithLefts`: merges `nodes[idx]` into its left
    /// neighbors as far as possible and returns how many were merged.
    fn merge_with_lefts(types: &mut TypeArena, nodes: &mut ClientBlocks, idx: usize) -> usize {
        let mut pos = idx;
        while pos > 0 {
            let left = nodes.blocks[pos - 1];
            let right = nodes.blocks[pos];
            match (left.kind, right.kind) {
                (BlockKind::Gc, BlockKind::Gc) | (BlockKind::Skip, BlockKind::Skip) => {}
                (BlockKind::Item(l), BlockKind::Item(r)) | (BlockKind::DeletedItem(l), BlockKind::DeletedItem(r)) => {
                    if !Self::merge_items(types, l, r) {
                        break;
                    }
                }
                _ => break,
            }
            pos -= 1;
        }
        nodes.blocks.drain(pos + 1..=idx);
        idx - pos
    }

    fn merge_items(types: &mut TypeArena, l: ItemIdx, r: ItemIdx) -> bool {
        let parent = types.items.get(l).expect("stored item").parent;
        let merge_strings = parent.is_some_and(|t| matches!(types[t].kind(), YTypeKind::Text | YTypeKind::XMLText));
        let (left, right) = types.items.get_two_mut(l, r).expect("distinct live neighbors");
        if left.right != Some(r)
            || right.left != Some(l)
            || left.id.client != right.id.client
            || left.id.clock + left.len != right.id.clock
            || Some(left.last_id()) != right.origin_left_id()
            || left.origin_right_id() != right.origin_right_id()
            || !Self::same_container(left, right)
        {
            return false;
        }
        let shift = if left.indexable() { -(left.len as i64) } else { 0 };
        match (&mut left.content, &mut right.content) {
            (Content::Deleted(a), Content::Deleted(b)) => *a += *b,
            (Content::Json(a), Content::Json(b)) => a.append(b),
            (Content::Any(a), Content::Any(b)) => a.append(b),
            (Content::String(a), Content::String(b)) if merge_strings => a.push_str(b),
            _ => return false,
        }
        if right.keep() {
            left.flags.set_keep();
        }
        left.len += right.len;
        let next = right.right;
        left.right = next;
        let key = right.parent_sub.clone();
        if let Some(next) = next {
            types.items.get_mut(next).expect("neighbor").left = Some(l);
        }
        if let Some(parent) = parent {
            let parent = &mut types[parent];
            if let Some(markers) = &mut parent.markers {
                markers.replace_marker(Some(r), Some(l), shift);
            }
            if let Some(key) = key
                && parent.map_get(&key) == Some(&Some(r))
            {
                parent.map_set(key, Some(l));
            }
        }
        types.items.retire(r);
        true
    }

    pub fn deep_compare(&self, other: &Self) -> bool {
        self.items.len() == other.items.len()
            && self.items.iter().all(|(&client, blocks)| {
                let Some(others) = other.items.get(&client) else {
                    return false;
                };
                blocks.len() == others.len()
                    && blocks.nodes(client).zip(others.nodes(client)).all(|(a, b)| {
                        if a.id != b.id || a.len != b.len {
                            return false;
                        }
                        match (a.as_item(), b.as_item()) {
                            (Some(l), Some(r)) => self.type_arena.items.get(l).expect("item").deep_compare(
                                &self.type_arena.items,
                                other.type_arena.items.get(r).expect("item"),
                                &other.type_arena.items,
                            ),
                            (None, None) => a.kind == b.kind,
                            _ => false,
                        }
                    })
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_delete_set_includes_tombstones_received_in_structs() {
        loom_model!({
            let source = DocOptions::from_identity(101, "source".into()).auto_gc(true).build();
            let mut receiver = DocOptions::from_identity(202, "receiver".into()).auto_gc(true).build();
            let mut text = source.get_or_create_text("body").unwrap();
            text.insert(0, "abc").unwrap();
            let state = source.get_state_vector();
            text.remove(1, 1).unwrap();

            let snapshot = source.encode_update_v1().unwrap();
            receiver.apply_update_from_binary_v1(&snapshot).unwrap();
            assert_eq!(receiver.encode_update_v1().unwrap(), snapshot);
            assert_eq!(receiver.get_or_create_text("body").unwrap().to_string(), "ac");

            let deletions = receiver.encode_state_as_update_v1(&state).unwrap();
            let update = Update::decode_v1(&deletions).unwrap();
            assert!(update.structs.is_empty());
            let store = receiver.store.read().unwrap();
            let generated = DocStore::generate_delete_set(&store.items);
            assert_eq!(generated[&101], OrderRange::from(1..2));
            assert_eq!(generated, update.delete_set);
        });
    }

    #[test]
    fn borrowed_update_matches_materialized_diff_at_mid_struct_clock() {
        loom_model!({
            let source = Doc::with_client(101);
            let mut receiver = Doc::with_client(202);
            let mut text = source.get_or_create_text("body").unwrap();
            text.insert(0, "ab").unwrap();
            receiver
                .apply_update_from_binary_v1(source.encode_update_v1().unwrap())
                .unwrap();
            let receiver_state = receiver.get_state_vector();

            text.insert(2, "😀c").unwrap();
            {
                // Both inserts were merged, so the receiver's clock falls
                // inside the struct being written.
                let store = source.store.read().unwrap();
                assert_eq!(store.items[&101].len(), 1);
                assert_eq!(store.items[&101].node(101, 0).unwrap().len(), 5);
            }
            for state in [
                StateVector::default(),
                StateVector::from([(101, 0)]),
                receiver_state.clone(),
            ] {
                let materialized = source
                    .store
                    .read()
                    .unwrap()
                    .diff_state_vector(&state)
                    .unwrap()
                    .encode_v1()
                    .unwrap();
                assert_eq!(source.encode_state_as_update_v1(&state).unwrap(), materialized);
            }

            receiver
                .apply_update_from_binary_v1(source.encode_state_as_update_v1(&receiver_state).unwrap())
                .unwrap();
            assert_eq!(receiver.get_or_create_text("body").unwrap().to_string(), "ab😀c");
            assert_eq!(receiver.get_state_vector(), source.get_state_vector());
            assert_eq!(
                source.encode_state_as_update_v1(&receiver.get_state_vector()).unwrap(),
                [0, 0]
            );
        });
    }

    #[test]
    fn test_get_state() {
        loom_model!({
            let doc_store = DocStore::with_client(1);
            let state = doc_store.get_state(1);
            assert_eq!(state, 0);
        });

        loom_model!({
            let mut doc_store = DocStore::with_client(1);

            let client_id = 1;

            let struct_info1 = Node::new_gc(Id::new(1, 1), 5);
            let struct_info2 = Node::new_skip(Id::new(1, 6), 7);

            for node in [struct_info1, struct_info2] {
                doc_store.add_node(node).unwrap();
            }

            let state = doc_store.get_state(client_id);

            assert_eq!(state, struct_info2.clock() + struct_info2.len());

            assert!(doc_store.self_check().is_ok());
        });
    }

    #[test]
    fn test_get_state_vector() {
        loom_model!({
            let doc_store = DocStore::with_client(1);
            let state_map = doc_store.get_state_vector();
            assert!(state_map.is_empty());
        });

        loom_model!({
            let mut doc_store = DocStore::with_client(1);

            let client1 = 1;
            let struct_info1 = Node::new_gc((1, 0).into(), 5);

            let client2 = 2;
            let struct_info2 = Node::new_gc((2, 0).into(), 6);
            let struct_info3 = Node::new_skip((2, 6).into(), 1);

            {
                let node = struct_info1;
                doc_store.add_node(node).unwrap();
            }
            for node in [struct_info2, struct_info3] {
                doc_store.add_node(node).unwrap();
            }

            let state_map = doc_store.get_state_vector();

            assert_eq!(state_map.get(&client1), struct_info1.clock() + struct_info1.len());
            assert_eq!(state_map.get(&client2), struct_info3.clock() + struct_info3.len());

            assert!(doc_store.self_check().is_ok());
        });
    }

    #[test]
    fn test_add_item() {
        loom_model!({
            let mut doc_store = DocStore::with_client(1);

            let struct_info1 = Node::new_gc(Id::new(1, 0), 5);
            let struct_info2 = Node::new_skip(Id::new(1, 5), 1);
            let struct_info3_err = Node::new_skip(Id::new(1, 5), 1);
            let struct_info3 = Node::new_skip(Id::new(1, 6), 1);

            assert!(doc_store.add_node(struct_info1).is_ok());
            assert!(doc_store.add_node(struct_info2).is_ok());
            assert_eq!(
                doc_store.add_node(struct_info3_err),
                Err(JwstCodecError::StructClockInvalid { expect: 6, actually: 5 })
            );
            assert!(doc_store.add_node(struct_info3).is_ok());
            assert_eq!(
                doc_store.get_state(struct_info1.client()),
                struct_info3.clock() + struct_info3.len()
            );
        });
    }

    #[test]
    fn test_get_item() {
        loom_model!({
            let mut doc_store = DocStore::with_client(1);
            let struct_info = Node::new_gc(Id::new(1, 0), 10);
            doc_store.add_node(struct_info).unwrap();

            assert_eq!(doc_store.get_node(Id::new(1, 9)), Some(struct_info));
        });

        loom_model!({
            let mut doc_store = DocStore::with_client(1);
            let struct_info1 = Node::new_gc(Id::new(1, 0), 10);
            let struct_info2 = Node::new_gc(Id::new(1, 10), 20);
            doc_store.add_node(struct_info1).unwrap();
            doc_store.add_node(struct_info2).unwrap();

            assert_eq!(doc_store.get_node(Id::new(1, 25)), Some(struct_info2));
        });

        loom_model!({
            let doc_store = DocStore::with_client(1);

            assert_eq!(doc_store.get_node(Id::new(1, 0)), None);
        });

        loom_model!({
            let mut doc_store = DocStore::with_client(1);
            let struct_info1 = Node::new_gc(Id::new(1, 0), 10);
            let struct_info2 = Node::new_gc(Id::new(1, 10), 20);
            doc_store.add_node(struct_info1).unwrap();
            doc_store.add_node(struct_info2).unwrap();

            assert_eq!(doc_store.get_node(Id::new(1, 35)), None);
        });

        loom_model!({
            let mut failures: Vec<&'static str> = Vec::new();

            {
                let mut doc_store = DocStore::with_client(1);
                let struct_info = Node::new_gc(Id::new(1, 0), 1);
                doc_store.add_node(struct_info).unwrap();

                let items = doc_store.items.get(&1).unwrap();
                let result =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| DocStore::get_node_index(items, 1)));

                match result {
                    Ok(index) if index.is_none() => {}
                    Ok(_) => failures.push("len=1 clock beyond end should return None"),
                    Err(_) => failures.push("len=1 clock beyond end should not panic"),
                }
            }

            {
                let mut doc_store = DocStore::with_client(1);
                let struct_info1 = Node::new_gc(Id::new(1, 0), 1);
                let struct_info2 = Node::new_gc(Id::new(1, 1), 1);
                doc_store.add_node(struct_info1).unwrap();
                doc_store.add_node(struct_info2).unwrap();

                let items = doc_store.items.get(&1).unwrap();
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    DocStore::get_node_index(items, u64::MAX)
                }));

                match result {
                    Ok(index) if index.is_none() => {}
                    Ok(_) => failures.push("huge clock should return None"),
                    Err(_) => failures.push("huge clock should not panic"),
                }
            }

            assert!(
                failures.is_empty(),
                "get_node_index edge cases failed: {}",
                failures.join(", ")
            );
        });
    }

    #[test]
    fn test_split_node_at() {
        loom_model!({
            let mut store = DocStore::with_client(1);
            for (client, text, expected) in [(1, "octo", ["oc", "to"]), (2, "a😀b", ["a�", "�b"])] {
                let id = Id::new(client, 0);
                let item = ItemBuilder::new().id(id).content(Content::String(text.into())).build();
                let node = Node::store_item(&mut store.type_arena, item);
                store.add_node(node).unwrap();
                let (left, right) = store.split_node(id, 2).unwrap();
                assert_eq!(left.as_item(), node.as_item());
                assert_eq!((left.len, right.len), (2, 2));
                let a = left.item(&store.type_arena);
                let b = right.item(&store.type_arena);
                assert_eq!((a.right, b.left), (right.as_item(), left.as_item()));
                assert_eq!(a.content, Content::String(expected[0].into()));
                assert_eq!(b.content, Content::String(expected[1].into()));
                assert_eq!(b.origin_left_id(), Some(Id::new(client, 1)));
            }
        });
    }

    #[test]
    fn get_or_create_type_keeps_root_after_first_handle_drops() {
        loom_model!({
            let mut store = DocStore::with_client(1);
            let first = store.get_or_create_type("root").unwrap();
            let second = store.get_or_create_type("root").unwrap();
            assert_eq!(first, second);
            assert_eq!(store.types["root"], first);
            assert_eq!(store.type_arena.len(), 1);
            assert_eq!(store.type_arena[first].root_name(), Some("root"));

            let doc = Doc::with_client(1);
            {
                let _first = doc.get_or_create_text("t").unwrap();
            }
            let mut second = doc.get_or_create_text("t").unwrap();
            second.insert(0, "alive").unwrap();
            assert_eq!(second.to_string(), "alive");
        });
    }

    #[test]
    fn remote_repair_created_root_survives_item_delete_and_gc() {
        loom_model!({
            let src = Doc::with_client(1);
            let mut src_text = src.get_or_create_text("remote_root").unwrap();
            src_text.insert(0, "hi").unwrap();
            let create_update = src.encode_update_v1().unwrap();

            let mut dst = Doc::with_client(2);
            dst.apply_update_from_binary_v1(create_update).unwrap();
            let root = dst.store.read().unwrap().types["remote_root"];

            src_text.remove(0, 2).unwrap();
            let delete_update = src.encode_update_v1().unwrap();
            dst.apply_update_from_binary_v1(delete_update).unwrap();
            dst.gc().unwrap();

            {
                let store = dst.store.read().unwrap();
                assert_eq!(store.types["remote_root"], root);
                assert_eq!(store.type_arena[root].root_name(), Some("remote_root"));
            }
            let mut dst_text = dst.get_or_create_text("remote_root").unwrap();
            dst_text.insert(0, "ok").unwrap();
            assert_eq!(dst_text.to_string(), "ok");
        });
    }

    /// A struct that names a root for the first time and carries a type
    /// needs two slots: with one left, neither is taken.
    #[test]
    fn a_full_arena_refuses_a_remote_type_without_leaving_its_root() {
        loom_model!({
            let source = Doc::with_client(1);
            source
                .get_or_create_array("fresh")
                .unwrap()
                .push(source.create_map().unwrap())
                .unwrap();
            let update = source.encode_update_v1().unwrap();

            let mut target = Doc::with_client(2);
            target.store.write().unwrap().type_arena.set_limit(Some(1));
            assert!(matches!(
                target.apply_update_from_binary_v1(&update),
                Err(JwstCodecError::IncompleteDocument(_))
            ));
            {
                let store = target.store.read().unwrap();
                assert!(store.types.is_empty());
                assert_eq!(store.type_arena.len(), 0);
                assert!(store.items.is_empty());
            }

            target.store.write().unwrap().type_arena.set_limit(None);
            target.apply_update_from_binary_v1(&update).unwrap();
            assert_eq!(target.get_or_create_array("fresh").unwrap().len(), 1);
            assert_eq!(target.store.read().unwrap().type_arena.len(), 2);
        });
    }

    #[test]
    #[cfg_attr(loom, ignore)]
    fn split_node_at_repeated_splits_do_not_amplify_capacity() {
        let (n, k) = if cfg!(miri) { (1024, 8) } else { (64 * 1024, 256) };

        let mut src = Doc::with_client(1);
        src.get_or_create_text("text")
            .unwrap()
            .insert(0, "a".repeat(n))
            .unwrap();
        let base_update = src.encode_update_v1().unwrap();

        let mut dst = Doc::with_client(2);
        dst.apply_update_from_binary_v1(base_update).unwrap();
        let mut text = dst.get_or_create_text("text").unwrap();
        for i in 0..k {
            text.insert((1 + 2 * i) as u64, "x").unwrap();
        }

        let edits = dst.encode_state_as_update_v1(&src.get_state_vector()).unwrap();
        src.apply_update_from_binary_v1(edits).unwrap();
        for doc in [&dst, &src] {
            let store = doc.store.read().unwrap();
            let client1_items = store.items.get(&1).unwrap();
            let mut fragments = 0usize;
            let mut total_cap = 0usize;
            for node in client1_items.nodes(1) {
                if let Some(item) = node.as_item().and_then(|i| store.type_arena.items.get(i))
                    && let Content::String(s) = &item.content
                {
                    fragments += 1;
                    total_cap += s.capacity();
                }
            }
            assert_eq!(fragments, k + 1);
            assert!(
                total_cap <= 2 * n,
                "split fragments amplified capacity: total_cap={total_cap} > 2*n={}",
                2 * n
            );
        }
    }

    #[test]
    fn test_split_and_get() {
        loom_model!({
            let mut doc_store = DocStore::with_client(1);
            let struct_info1 = Node::store_item(
                &mut doc_store.type_arena,
                ItemBuilder::new()
                    .id((1, 0).into())
                    .content(Content::String(String::from("octo")))
                    .build(),
            );

            let struct_info2 = Node::store_item(
                &mut doc_store.type_arena,
                ItemBuilder::new()
                    .id((1, struct_info1.len()).into())
                    .left_id(Some(struct_info1.id()))
                    .content(Content::String(String::from("base")))
                    .build(),
            );
            let s1_ref = struct_info1;
            doc_store.add_node(struct_info1).unwrap();
            doc_store.add_node(struct_info2).unwrap();

            let s1 = doc_store.get_node(Id::new(1, 0)).unwrap();
            assert_eq!(s1, s1_ref);
            let left = doc_store.split_at_and_get_left((1, 1)).unwrap();
            assert_eq!(left.len(), 2); // octo => oc_to

            // s1 used to be (1, 4), but it actually ref of first item in store,
            // so now it should be (1, 2)
            assert_eq!(
                s1.as_item(),
                left.as_item(),
                "doc internal mutation should not modify the pointer"
            );
            let right = doc_store.split_at_and_get_right((1, 5)).unwrap();
            assert_eq!(right.len(), 3); // base => b_ase
        });
    }

    #[test]
    fn should_mark_changed_items() {
        loom_model!({
            let doc = DocOptions::new().with_client_id(1).build();

            let arr = doc.get_or_create_array("arr").unwrap();
            let text = doc.create_text().unwrap();
            let map = doc.create_map().unwrap();

            // what the transaction collected so far
            fn collected(tx: &mut TransactionMut<'_>) -> ChangedTypeRefs {
                tx.store_mut().get_changed()
            }

            doc.transact_mut(None, |tx| {
                tx.array(&arr)?.insert(0, Value::from(text.clone()))?;
                tx.array(&arr)?.insert(1, Value::from(map.clone()))?;
                let changed = collected(tx);
                // for array, we will only record the type ref itself
                assert_eq!(changed.len(), 1);
                assert_eq!(changed.get(&arr.0.id.unwrap()), Some(&vec![]));

                tx.text(&text)?.insert(0, "hello world")?;
                tx.text(&text)?.remove(5, 6)?;
                let changed = collected(tx);
                assert_eq!(changed.len(), 1);
                assert_eq!(changed.get(&text.0.id.unwrap()), Some(&vec![]));

                tx.map(&map)?.insert("key".into(), 123)?;
                let changed = collected(tx);
                assert_eq!(changed.len(), 1);
                assert_eq!(changed.get(&map.0.id.unwrap()), Some(&vec!["key".into()]));

                tx.map(&map)?.remove("key");
                let changed = collected(tx);
                assert_eq!(changed.len(), 1);
                assert_eq!(changed.get(&map.0.id.unwrap()), Some(&vec!["key".into()]));

                tx.array(&arr)?.remove(0, 1)?;
                let changed = collected(tx);
                assert_eq!(changed.len(), 2);
                // text's children mark parent(text) changed
                assert_eq!(changed.get(&text.0.id.unwrap()), Some(&vec![]));
                // text mark parent(arr) changed
                assert_eq!(changed.get(&arr.0.id.unwrap()), Some(&vec![]));
                Ok(())
            })
            .unwrap();

            // the collector is per transaction
            assert!(doc.store.read().unwrap().collector.is_empty());
        });
    }

    #[test]
    fn should_replace_gc_item_with_content_deleted() {
        loom_model!({
            let mut item1 = ItemBuilder::new()
                .id((1, 0).into())
                .content(Content::String(String::from("octo")))
                .build();
            let item2 = ItemBuilder::new()
                .id((1, 4).into())
                .content(Content::String(String::from("base")))
                .build();

            item1.delete();

            let mut store = DocStore::with_client(1);

            for item in [item1, item2] {
                let node = Node::store_item(&mut store.type_arena, item);
                store.add_node(node).unwrap();
            }

            let ds = store.get_delete_sets();
            store.gc_delete_set(&ds);

            assert_eq!(
                &store.get_node((1, 0)).unwrap().item(&store.type_arena).content,
                &Content::Deleted(4)
            );
        });
    }

    #[test]
    fn should_gc_type_items() {
        loom_model!({
            let doc = DocOptions::new().with_client_id(1).build();

            let mut arr = doc.get_or_create_array("arr").unwrap();
            let mut text = doc.create_text().unwrap();

            arr.insert(0, Value::from(text.clone())).unwrap();

            text.insert(0, "hello world").unwrap();
            text.remove(5, 6).unwrap();

            arr.remove(0, 1).unwrap();
            assert_eq!(arr.len(), 0);
            let mut store = doc.store.write().unwrap();
            let ds = store.get_delete_sets();
            store.gc_delete_set(&ds);

            assert_eq!(
                &store.get_node((1, 0)).unwrap().item(&store.type_arena).content,
                &Content::Deleted(1)
            );

            // "hello" and " world" GCd, and merged by the commit
            let children = store.get_node((1, 7)).unwrap();
            assert_eq!(children, Node::new_gc((1, 1).into(), 11));
            assert_eq!(children.len(), 11);
        });
    }

    /// Yjs `Item.gc(store, parentGCd)`: children become GC structs only when
    /// their parent type item is collected. A kept (or otherwise not
    /// collected) deleted parent leaves its deleted children as items with
    /// `ContentDeleted`, so the parent's item list stays linked.
    #[test]
    fn should_only_replace_children_of_collected_types() {
        loom_model!({
            let doc = DocOptions::new().with_client_id(1).auto_gc(false).build();

            let mut arr = doc.get_or_create_array("arr").unwrap();
            let mut text = doc.create_text().unwrap();
            arr.insert(0, Value::from(text.clone())).unwrap();
            text.insert(0, "hello").unwrap();
            arr.remove(0, 1).unwrap();

            let mut store = doc.store.write().unwrap();
            // keep the text item (1, 0) itself
            let idx = store.get_node((1, 0)).unwrap().as_item().unwrap();
            store.type_arena.items.get_mut(idx).unwrap().flags.set_keep();
            let ds = store.get_delete_sets();
            store.gc_delete_set(&ds);

            assert!(matches!(
                &store.get_node((1, 0)).unwrap().item(&store.type_arena).content,
                Content::Type(_)
            ));
            let hello = store.get_node((1, 1)).unwrap();
            assert!(hello.is_item());
            assert_eq!(&hello.item(&store.type_arena).content, &Content::Deleted(5));
        });
    }

    #[test]
    fn should_gc_multi_client_ds() {
        loom_model!({
            let bin = {
                let doc = DocOptions::new().with_client_id(1).build();
                let mut pages = doc.get_or_create_map("pages").unwrap();
                let page1 = doc.create_text().unwrap();
                let mut page1_ref = page1.clone();
                pages.insert("page1".to_string(), Value::from(page1)).unwrap();
                page1_ref.insert(0, "hello").unwrap();
                doc.encode_update_v1().unwrap()
            };

            let mut doc = DocOptions::new().with_client_id(2).build();
            doc.apply_update_from_binary_v1(bin).unwrap();
            let mut pages = doc.get_or_create_map("pages").unwrap();
            if let Value::Text(mut page1) = pages.get("page1").unwrap() {
                page1.insert(5, " world").unwrap();
            }

            pages.remove("page1");

            let mut store = doc.store.write().unwrap();
            let ds = store.get_delete_sets();
            store.gc_delete_set(&ds);

            assert_eq!(
                &store.get_node((1, 0)).unwrap().item(&store.type_arena).content,
                &Content::Deleted(1)
            );

            assert_eq!(
                store.get_node((1, 1)).unwrap(), // "hello" GCd
                Node::new_gc((1, 1).into(), 5)
            );

            assert_eq!(
                store.get_node((2, 0)).unwrap(), // " world" GCd
                Node::new_gc((2, 0).into(), 6)
            );
        });
    }

    /// Splitting the merged tombstones of a map key at the origin of a remote
    /// value leaves the key's last value in the right half; the next local
    /// value must go after it, not between the halves where it is deleted.
    #[test]
    fn splitting_the_last_value_of_a_key_keeps_the_key_on_it() {
        loom_model!({
            let mut doc = DocOptions::new().with_client_id(2).build();
            let mut map = doc.get_or_create_map("map").unwrap();
            map.insert("k".into(), 1).unwrap();
            map.insert("k".into(), 2).unwrap();

            // a peer with a smaller client ID overwrites the value (2, 1)
            let mut peer = DocOptions::new().with_client_id(1).build();
            peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
                .unwrap();
            peer.get_or_create_map("map")
                .unwrap()
                .insert("k".into(), "peer")
                .unwrap();

            map.insert("k".into(), 3).unwrap();
            map.remove("k");
            {
                let store = doc.store.read().unwrap();
                let node = store.get_node((2, 0)).unwrap();
                assert_eq!((node.id(), node.len()), (Id::new(2, 0), 3), "merged tombstones");
            }

            // splits (2, 0..3) after (2, 1); the peer's value lands before
            // (2, 2) and is deleted
            doc.apply_update_from_binary_v1(peer.encode_update_v1().unwrap())
                .unwrap();
            assert_eq!(map.get("k"), None);

            map.insert("k".into(), "local").unwrap();
            assert_eq!(map.get("k"), Some(Value::from("local")));

            peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
                .unwrap();
            assert_eq!(
                peer.get_or_create_map("map").unwrap().get("k"),
                Some(Value::from("local"))
            );
        });
    }

    #[test]
    fn should_merge_same_sibling_items() {
        loom_model!({
            let mut store = DocStore::with_client(1);
            let nodes = [
                Node::new_gc((1, 0).into(), 2),
                Node::new_gc((1, 2).into(), 2),
                Node::new_skip((1, 4).into(), 2),
                Node::store_item(
                    &mut store.type_arena,
                    ItemBuilder::new()
                        .id((1, 6).into())
                        .content(Content::String(String::from("hello")))
                        .build(),
                ),
                // actually not mergable, due to runtime continuous check
                // will cover it in [test_merge_same_sibling_items2]
                Node::store_item(
                    &mut store.type_arena,
                    ItemBuilder::new()
                        .id((1, 11).into())
                        .content(Content::String(String::from("world")))
                        .left_id(Some((1, 11).into()))
                        .build(),
                ),
            ];
            for node in nodes {
                store.add_node(node).unwrap();
            }

            store.make_continuous(store.get_state_vector());

            assert_eq!(store.items.get(&1).unwrap().len(), 4);
        });
    }

    #[test]
    fn test_merge_same_sibling_items2() {
        loom_model!({
            let doc = Doc::new();

            let mut text = doc.get_or_create_text("text").unwrap();
            text.insert(0, "a").unwrap();
            text.insert(1, "b").unwrap();
            text.insert(2, "c").unwrap();
            text.insert(3, ", hello").unwrap();

            assert_eq!(text.to_string(), "abc, hello");

            // every commit merges the structs it added
            assert_eq!(doc.store.read().unwrap().items.get(&1).unwrap().len(), 1);
            assert_eq!(text.to_string(), "abc, hello");
        });
    }
}
