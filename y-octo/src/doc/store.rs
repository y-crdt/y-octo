mod client_blocks;

mod item_space;
use std::{collections::VecDeque, mem, ops::Range};

pub(crate) use client_blocks::{BlockKind, BlockRef, ClientBlocks};
pub(crate) use item_space::{ItemIdx, ItemSpace, Moved};
use y_octo_core::{
    doc_kernel::{
        self, MergeSide, can_merge_items, check_direct_cycle, check_origin, cuts_live_item, decide_integrate_link,
        follows_in_list, needs_conflict_scan, parent_precedes_item, plan_delete_range_splits, plan_split_node,
    },
    id_order::MAX_IDS,
};

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
    /// No timeline of `items` holds more blocks than this: the blocks
    /// `add_node` and `split_node`, the two places a timeline grows, ever
    /// added to any of them. An edit that adds no more blocks than a timeline
    /// of that many has room for fits every timeline, and is not looked at
    /// further (`check_blocks`); past that, each timeline is asked. It stops
    /// at `u32::MAX`, the most blocks a timeline holds, and takes no room of
    /// its own beside `has_deleted_structs`.
    longest: u32,
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
    /// A smaller number of candidates than a conflict scan takes, to reach
    /// its refusal in tests.
    #[cfg(test)]
    pub(crate) scan_limit: Option<usize>,
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
        self.items.get(&client).map_or(0, |blocks| blocks.end_clock())
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
                state.insert(client, blocks.end_clock());
            }
        }
        state
    }

    pub fn add_node(&mut self, node: Node) -> JwstCodecResult {
        // refused before the client gets a timeline for it
        if node.len() == 0 {
            return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()));
        }
        let blocks = self.items.entry(node.client()).or_default();
        blocks.append(
            BlockRef {
                clock: node.clock(),
                kind: node.kind,
            },
            node.len(),
        )?;
        self.longest = self.longest.saturating_add(1);
        self.has_deleted_structs |= node.deleted();
        Ok(())
    }

    /// Whether the timelines take the blocks an edit is about to add:
    /// `appended` at the end of the timeline of `client`, and one for every
    /// struct it cuts in two, each named by the first id of its right half
    /// (`splits`, where `None` is a cut the edit does not make; an id that
    /// starts a struct already, or that no item holds, cuts nothing, and an
    /// id named twice cuts once).
    ///
    /// An edit of several blocks asks here before its first: a full timeline
    /// refuses the whole edit and the document is as it was. A struct that
    /// is collected takes a block and no item, so the room of the item arena
    /// does not answer this.
    #[inline]
    pub(crate) fn check_blocks(&self, client: Client, appended: usize, splits: &[Option<Id>]) -> JwstCodecResult {
        if appended.checked_add(splits.len()).is_some_and(|n| self.blocks_fit(n)) {
            return Ok(());
        }
        self.check_blocks_exact(client, appended, splits)
    }

    /// Whether every timeline takes `blocks` more blocks, wherever an edit
    /// puts them: one of as many blocks as were ever added does.
    #[inline]
    pub(crate) fn blocks_fit(&self, blocks: usize) -> bool {
        (self.longest as usize)
            .checked_add(blocks)
            .is_some_and(|n| n <= ClientBlocks::limit())
    }

    #[cold]
    fn check_blocks_exact(&self, client: Client, appended: usize, splits: &[Option<Id>]) -> JwstCodecResult {
        let mut needed: Vec<(Client, usize)> = vec![(client, appended)];
        let mut cuts: Vec<Id> = Vec::with_capacity(splits.len());
        for id in splits.iter().flatten() {
            if cuts.contains(id) || !self.get_node(*id).is_some_and(|node| node.is_item() && node.id != *id) {
                continue;
            }
            cuts.push(*id);
            match needed.iter_mut().find(|(client, _)| *client == id.client) {
                Some((_, blocks)) => *blocks += 1,
                None => needed.push((id.client, 1)),
            }
        }
        for (client, blocks) in needed {
            match self.items.get(&client) {
                Some(timeline) => timeline.check_capacity(blocks)?,
                None => ClientBlocks::default().check_capacity(blocks)?,
            }
        }
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
        Some(Id::new(id.client, blocks.clock_at(blocks.find(id.clock)?)))
    }

    pub fn get_node_with_idx<I: Into<Id>>(&self, id: I) -> Option<(Node, usize)> {
        let id = id.into();
        self.items.get(&id.client)?.find_node(id.client, id.clock)
    }

    pub fn split_node<I: Into<Id>>(&mut self, id: I, diff: u64) -> JwstCodecResult<(Node, Node)> {
        let id = id.into();
        let blocks = self
            .items
            .get(&id.client)
            .ok_or(JwstCodecError::StructSequenceNotExists(id.client))?;
        let (left, pos) = blocks
            .find_node(id.client, id.clock)
            .ok_or(JwstCodecError::StructSequenceNotExists(id.client))?;
        let left_idx = left.as_item().ok_or(JwstCodecError::ItemSplitNotSupport)?;
        // The timeline takes the split below, after the item is cut: refuse
        // here what it would refuse there, before the arena is asked for
        // room, so that a cut that is refused stays the first answer.
        if diff == 0 || diff >= left.len {
            return Err(JwstCodecError::ItemSplitNotSupport);
        }
        if blocks.is_full() {
            return Err(JwstCodecError::IncompleteDocument(TOO_MANY_STRUCTS.into()));
        }
        let items = &mut self.type_arena.items;
        items.check_capacity(1)?;
        let item = items.get_mut(left_idx).expect("stored item");
        debug_assert!(item.id == left.id && item.len == left.len);
        // Where the item is cut, and whether its right half takes its map
        // key, is `plan_split_node` of `y-octo-core`
        // (`DocKernel.plan_split_node_spec` in `proofs/`), which refuses the
        // cuts refused above once more, on the item itself.
        let Some(plan) = plan_split_node(
            core_id(item.id),
            item.len,
            diff,
            item.right.is_some(),
            item.parent.is_some(),
            item.parent_sub.is_some(),
        ) else {
            return Err(JwstCodecError::ItemSplitNotSupport);
        };
        let content = item.content.split_in_place(diff)?;
        let len = plan.right_len;
        item.len = diff;
        let id = Id::new(plan.right_id.client, plan.right_id.clock);
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
        debug_assert_eq!(core_id(item.last_id()), plan.right_origin_left);
        right.set_origin_left_id(Some(Id::new(
            plan.right_origin_left.client,
            plan.right_origin_left.clock,
        )));
        right.set_origin_right_id(item.origin_right_id());
        let update_key = if plan.update_map_winner {
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
        let blocks = self.items.get_mut(&id.client).expect("stored client");
        blocks
            .split(pos, id.clock, kind)
            .expect("a split inside the block, checked above");
        self.longest = self.longest.saturating_add(1);
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
        // created at or after itself (as `ReadDoc` checks): `check_origin` of
        // `y-octo-core`, the check `YataStoreCore::integrate` runs.
        let id = core_id(item.id);
        for origin in [item.origin_left_id(), item.origin_right_id()] {
            if check_origin(id, origin.map(core_id)).is_err() {
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
            Some(WireParent::Item(parent_id)) if !parent_precedes_item(id, core_id(*parent_id)) => {
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
        // Every block this struct adds fits or none is added: its own (as an
        // item, or as a collected range when its parent is gone) and one for
        // each struct `repair` and `integrate_item` cut at its origins and at
        // the end of the part of it the store holds. A root is not left
        // behind either for a struct that found no block.
        self.check_blocks(
            id.client,
            1,
            &[
                origin_left_id.map(|left| Id::new(left.client, left.clock.saturating_add(1))),
                origin_right_id,
                (offset > 0).then(|| id + offset),
            ],
        )?;
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

    /// Whether the store may refuse a struct or a deletion of `update` for
    /// room ([refused_for_room]).
    ///
    /// One struct asks for no more than two types (its own and a root it is
    /// the first to name), four blocks and four items (itself, and a cut at
    /// each of its origins and at the end of the part of it the store
    /// holds), and its conflict scan walks items the arena holds, each once.
    /// One deletion asks for a block and an item at each of its two ends. A
    /// store with that much to spare for every struct and deletion of
    /// `update` refuses none of them for room.
    pub(crate) fn short_of_room_for(&self, update: &Update) -> bool {
        let structs: usize = update.structs.values().map(VecDeque::len).sum();
        let deletions: usize = update.delete_set.clients.values().map(OrderRange::ranges_len).sum();
        let types = structs.saturating_mul(2);
        let items = structs.saturating_mul(4).saturating_add(deletions.saturating_mul(2));
        #[cfg(test)]
        let candidates = self.scan_limit.map_or(MAX_IDS, |limit| limit.min(MAX_IDS));
        #[cfg(not(test))]
        let candidates = MAX_IDS;
        !(self.type_arena.check_capacity(types).is_ok()
            && self.blocks_fit(items)
            && self.type_arena.items.fits_within(items, candidates))
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
                if check_direct_cycle(inner.raw(), ty.raw()) {
                    return Err(JwstCodecError::InvalidParent);
                }
                // An update can claim any stored type as the parent,
                // so walk its ancestors. Local callers insert a type
                // they checked before (`check_insertable`) and can
                // only create direct loops, checked above.
                if parent.is_none() && self.type_arena.is_above(*inner, *ty) {
                    return Err(JwstCodecError::InvalidParent);
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

            // Other items may sit between the two neighbours unless they
            // touch (`needs_conflict_scan` of `y-octo-core`, which
            // `YataStoreCore` runs too): the right one follows the left one,
            // or is the first item when there is no left one.
            let slot = |link: ItemRef| link.map(ItemIdx::core_slot);
            let needs_scan = match left {
                Some(left) => match self.type_arena.items.get(left) {
                    Some(left) => needs_conflict_scan(true, slot(left.right), slot(right), None),
                    None => false,
                },
                None => match right.and_then(|i| self.type_arena.items.get(i)) {
                    Some(r) => needs_conflict_scan(false, None, slot(right), slot(r.left)),
                    None => needs_conflict_scan(false, None, None, None),
                },
            };

            // conflicts
            if needs_scan {
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

                // The scan fails only when the list of its candidates is
                // full; nothing of this item is linked yet, as when the
                // timeline or the arena refuse it below.
                left = scan_conflict_left(
                    self.candidates_limit(),
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
                )?;
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
            // What linking the item does besides making it the neighbour
            // of its neighbours is `decide_integrate_link` of `y-octo-core`:
            // the first item of a list, the last value of a map key (the
            // one before it is deleted), an item that is deleted as it is
            // linked, the length of its list.
            let plan = decide_integrate_link(
                left.is_some(),
                right.is_some(),
                key.is_some(),
                parent_deleted,
                countable,
            );
            if let Some(left) = left {
                self.type_arena.items.get_mut(left).expect("left neighbor").right = Some(idx);
            }
            if plan.set_list_start {
                self.type_arena[parent].start = Some(idx);
            }
            if let Some(right) = right {
                self.type_arena.items.get_mut(right).expect("right neighbor").left = Some(idx);
            }
            if let (true, Some(key)) = (plan.set_map_winner, &key) {
                self.type_arena[parent].map_set(key.clone(), Some(idx));
            }
            if let (true, Some(left)) = (plan.delete_prev_map_winner, left) {
                self.delete_item(left, Some(parent));
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
            if plan.delete_self {
                self.delete_item(idx, Some(parent));
            } else if plan.add_list_len {
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
        match self.items.get(&id.client) {
            Some(blocks) => blocks.check_append(id.clock, len),
            // the first block of a client: what an empty timeline takes
            None => ClientBlocks::default().check_append(id.clock, len),
        }
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

    /// How many candidates a conflict scan of this store takes.
    #[inline]
    fn candidates_limit(&self) -> ScanLimit {
        #[cfg(test)]
        {
            ScanLimit {
                candidates: self.scan_limit,
            }
        }
        #[cfg(not(test))]
        {
            ScanLimit::default()
        }
    }

    /// Whether two items are in the same list: the same parent type and, for
    /// map entries, the same key. An item whose parent was not resolved is
    /// collected instead of linked, so it matches anything
    /// (`same_container` of `y-octo-core`).
    #[inline]
    fn same_container(other: &Item, this: &Item) -> bool {
        doc_kernel::same_container(
            other.parent.map(TypeIdx::raw),
            this.parent.map(TypeIdx::raw),
            other.parent_sub == this.parent_sub,
        )
    }

    /// What `can_merge_items` of `y-octo-core` reads of an item.
    #[inline]
    fn merge_side(item: &Item) -> MergeSide {
        MergeSide {
            id: core_id(item.id),
            len: item.len,
            origin_left: item.origin_left_id().map(core_id),
            origin_right: item.origin_right_id().map(core_id),
            left: item.left.map(ItemIdx::core_slot),
            right: item.right.map(ItemIdx::core_slot),
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
        debug_assert_eq!(blocks.clock_at(pos), id.clock);
        debug_assert!(matches!(blocks.kind_at(pos), BlockKind::Item(i) | BlockKind::DeletedItem(i) if i == idx));
        blocks.mark_deleted(pos).expect("the block of an item");
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
        // Live items are cut at the two ends of the range, and nothing else
        // (`cuts_live_item` and `plan_delete_range_splits` of `y-octo-core`).
        let split_start = cuts_live_item(!node.deleted() && node.is_item(), node.clock(), range.start);
        let split_end = self
            .get_node(Id::new(client, range.end))
            .is_some_and(|n| cuts_live_item(n.is_item() && !n.deleted(), n.clock(), range.end));
        let plan = plan_delete_range_splits(split_start, split_end);
        self.type_arena.items.check_capacity(plan.needed_splits)?;
        // both cuts fit the timeline or neither is made; a range that cuts no
        // struct is deleted from a full timeline as from any other
        self.check_blocks(
            client,
            0,
            &[
                plan.split_start.then(|| Id::new(client, range.start)),
                plan.split_end.then(|| Id::new(client, range.end)),
            ],
        )?;
        if plan.split_start {
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
            let Some(first) = nodes.first_clock() else { continue };
            let clock = sv.get(&client).max(first);
            let Some(start) = nodes.find(clock) else { continue };
            // no block of a timeline is empty
            let count = nodes.len() - start;
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
            for node in nodes.nodes_from(client, start + 1) {
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
            let Some(first) = blocks.first_clock() else { continue };
            let clock = sv.get(&client).max(first);
            let Some(start) = blocks.find(clock) else { continue };
            let mut tail = VecDeque::with_capacity(blocks.len() - start);
            for node in blocks.nodes_from(client, start) {
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
            let mut current: Option<Range<Clock>> = None;
            let mut previous = VecDeque::new();
            nodes.each_deleted(|range| match &mut current {
                Some(run) if range.start <= run.end => run.end = run.end.max(range.end),
                run => {
                    if let Some(done) = run.replace(range) {
                        previous.push_back(done);
                    }
                }
            });
            let Some(current) = current else { continue };
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
            debug_assert_eq!(items.clock_at(idx), id.clock);
            items.collect(idx).expect("the block of an item");
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
                while si > 0 && nodes.clock_at(si) >= range.start {
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
            let first_change = nodes.find_recent(before_state).unwrap_or(1).max(1);
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
        {
            let kinds = nodes.kinds();
            let mut right = kinds.at(pos);
            while pos > 0 {
                let left = kinds.at(pos - 1);
                match (left, right) {
                    (BlockKind::Gc, BlockKind::Gc) | (BlockKind::Skip, BlockKind::Skip) => {}
                    (BlockKind::Item(l), BlockKind::Item(r))
                    | (BlockKind::DeletedItem(l), BlockKind::DeletedItem(r)) => {
                        if !Self::merge_items(types, l, r) {
                            break;
                        }
                    }
                    _ => break,
                }
                right = left;
                pos -= 1;
            }
        }
        if pos < idx {
            nodes
                .merge_range(pos, idx)
                .expect("neighbours of the same kind inside the timeline");
        }
        idx - pos
    }

    fn merge_items(types: &mut TypeArena, l: ItemIdx, r: ItemIdx) -> bool {
        let parent = types.items.get(l).expect("stored item").parent;
        let merge_strings = parent.is_some_and(|t| matches!(types[t].kind(), YTypeKind::Text | YTypeKind::XMLText));
        let (left, right) = types.items.get_two_mut(l, r).expect("distinct live neighbors");
        // `right` follows `left` in the list and continues it
        // (`can_merge_items` of `y-octo-core`, the conditions
        // `YataStoreCore::merge_adjacent` merges on), and both are in one
        // list. Whether the two are neighbours at all is asked first, on its
        // own (`follows_in_list`, the first condition of `can_merge_items`:
        // most pairs end here), and the list last, as before:
        // `can_merge_items` is its answer for one list and whether the two
        // are in one list (`DocKernel.can_merge_items_and` in `proofs/`).
        if !follows_in_list(
            left.right.map(ItemIdx::core_slot),
            l.core_slot(),
            right.left.map(ItemIdx::core_slot),
            r.core_slot(),
        ) {
            return false;
        }
        if !can_merge_items(
            Self::merge_side(left),
            l.core_slot(),
            Self::merge_side(right),
            r.core_slot(),
            true,
        ) || !Self::same_container(left, right)
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
    use y_octo_core::yata_store::{IdCore, YataStoreCore};

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

    /// A conflict scan whose list is full refuses the struct before
    /// anything of it is linked: its type leaves the arena again, and the
    /// struct is taken once the list has room.
    #[test]
    fn a_full_conflict_scan_refuses_a_struct_and_leaves_nothing_of_it() {
        loom_model!({
            // three peers put a value at the start of the same empty array
            let mut target = Doc::with_client(9);
            let mut reference = Doc::with_client(8);
            for client in 1..=3 {
                let peer = Doc::with_client(client);
                peer.get_or_create_array("list").unwrap().push(client as i32).unwrap();
                let update = peer.encode_update_v1().unwrap();
                target.apply_update_from_binary_v1(&update).unwrap();
                reference.apply_update_from_binary_v1(&update).unwrap();
            }
            // a fourth, with a larger client, puts a map there: its scan
            // walks the three values
            let late = Doc::with_client(5);
            late.get_or_create_array("list")
                .unwrap()
                .push(late.create_map().unwrap())
                .unwrap();
            let update = late.encode_update_v1().unwrap();
            reference.apply_update_from_binary_v1(&update).unwrap();

            let before = target.encode_update_v1().unwrap();
            let types_before = target.store.read().unwrap().type_arena.len();
            for limit in 0..3 {
                target.store.write().unwrap().scan_limit = Some(limit);
                assert_eq!(
                    target.apply_update_from_binary_v1(&update),
                    Err(JwstCodecError::IncompleteDocument(
                        "the conflict scan holds too many candidates".into()
                    )),
                    "a scan of {limit} candidates"
                );
                let store = target.store.read().unwrap();
                assert_eq!(store.type_arena.len(), types_before, "the map left the arena");
                assert_eq!(store.get_state(5), 0);
                assert!(store.items.get(&5).is_none_or(|blocks| blocks.len() == 0));
                store.self_check().unwrap();
                drop(store);
                assert_eq!(target.get_or_create_array("list").unwrap().len(), 3);
                assert_eq!(target.encode_update_v1().unwrap(), before);
            }

            // a list that takes the three candidates: the struct is linked
            target.store.write().unwrap().scan_limit = Some(3);
            target.apply_update_from_binary_v1(&update).unwrap();
            {
                let store = target.store.read().unwrap();
                assert_eq!(store.type_arena.len(), types_before + 1);
                store.self_check().unwrap();
            }
            assert_eq!(target.get_or_create_array("list").unwrap().len(), 4);
            assert_eq!(
                target.encode_update_v1().unwrap(),
                reference.encode_update_v1().unwrap()
            );
        });
    }

    /// The clocks under the key `k` of the root map `map`, in the order of
    /// their list, with whether each is deleted.
    fn key_clocks(doc: &Doc) -> Vec<(u64, u64, bool)> {
        let store = doc.store.read().unwrap();
        let Some(ty) = store.types.get("map") else {
            return Vec::new();
        };
        let mut cursor = store.type_arena[*ty].map_get("k").copied().flatten();
        let mut clocks = Vec::new();
        while let Some(idx) = cursor {
            let item = store.type_arena.items.get(idx).expect("an item of the key");
            for clock in (item.id.clock..item.id.clock + item.len).rev() {
                clocks.push((item.id.client, clock, item.deleted()));
            }
            cursor = item.left;
        }
        clocks.reverse();
        clocks
    }

    #[test]
    fn concurrent_values_of_a_key_leave_the_last_one_whatever_the_order_of_arrival() {
        loom_model!({
            // three replicas set the key without seeing each other
            let docs: Vec<Doc> = (1..=3u64)
                .map(|client| {
                    let doc = Doc::with_client(client);
                    doc.get_or_create_map("map")
                        .unwrap()
                        .insert("k".into(), format!("value {client}"))
                        .unwrap();
                    doc
                })
                .collect();
            let updates: Vec<Vec<u8>> = docs.iter().map(|doc| doc.encode_update_v1().unwrap()).collect();
            let orders: [[usize; 3]; 6] = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
            let mut states = Vec::new();
            for order in orders {
                let mut doc = Doc::with_client(9);
                for at in order {
                    doc.apply_update_from_binary_v1(&updates[at]).unwrap();
                    // at most the last value of the key is not deleted
                    let clocks = key_clocks(&doc);
                    let (last, before) = clocks.split_last().unwrap();
                    assert!(before.iter().all(|(_, _, deleted)| *deleted), "{clocks:?}");
                    assert!(!last.2, "{clocks:?}");
                }
                // the values are in the order of their clients: the last wins
                assert_eq!(key_clocks(&doc), [(1, 0, true), (2, 0, true), (3, 0, false)]);
                assert_eq!(
                    doc.get_or_create_map("map").unwrap().get("k"),
                    Some(Value::from("value 3"))
                );
                states.push((doc.get_delete_sets(), doc.encode_update_v1().unwrap()));
            }
            assert!(states.windows(2).all(|pair| pair[0] == pair[1]), "the orders diverged");
        });
    }

    /// A replica of one map key next to what `y-octo-core` makes of it: the
    /// list of the key as a `YataStoreCore`, linked as
    /// `decide_integrate_link` says.
    struct KeyReplica {
        doc: Doc,
        map: Map,
        core: YataStoreCore,
        /// the structs the replica holds, in the order it took them
        known: Vec<(IdCore, Option<IdCore>)>,
    }

    impl KeyReplica {
        fn new(client: u64, gc: bool, key: (u64, u64)) -> Self {
            let doc = DocOptions::new().with_client_id(client).auto_gc(gc).build();
            let map = doc.get_or_create_map("map").unwrap();
            Self {
                doc,
                map,
                core: YataStoreCore::with_key(key.0, key.1),
                known: Vec::new(),
            }
        }

        /// The clocks of the list of the core, with whether each is deleted.
        fn core_clocks(&self) -> Vec<(u64, u64, bool)> {
            let mut clocks = Vec::new();
            let mut cursor = self.core.start();
            while let Some(idx) = cursor {
                let item = self.core.items()[idx as usize];
                for clock in item.id.clock..item.id.clock + item.len {
                    clocks.push((item.id.client, clock, item.deleted));
                }
                cursor = item.right;
            }
            clocks
        }

        /// Links a value into the list of the core as `DocStore` links it
        /// under a map key.
        fn integrate(&mut self, id: IdCore, origin_left: Option<IdCore>) {
            let idx = self.core.integrate(id, 1, origin_left, None).unwrap();
            let item = self.core.items()[idx as usize];
            let plan = decide_integrate_link(item.left.is_some(), item.right.is_some(), true, false, true);
            assert!(!plan.set_list_start && !plan.add_list_len);
            assert_eq!(plan.set_map_winner, item.right.is_none());
            if plan.delete_prev_map_winner {
                let left = self.core.items()[item.left.unwrap() as usize];
                self.core
                    .delete_range(left.id.client, left.id.clock, left.id.clock + left.len)
                    .unwrap();
            }
            if plan.delete_self {
                self.core.delete_range(id.client, id.clock, id.clock + 1).unwrap();
            }
            self.known.push((id, origin_left));
        }

        /// The replica sets the key.
        fn set(&mut self, value: &str) {
            let client = self.doc.client();
            let id = IdCore {
                client,
                clock: self.core.get_state(client),
            };
            // a new value is typed after the last clock of the key
            let origin_left = self
                .core_clocks()
                .last()
                .map(|&(client, clock, _)| IdCore { client, clock });
            self.map.insert("k".into(), value).unwrap();
            assert_eq!(self.doc.get_state_vector().get(&client), id.clock + 1);
            self.integrate(id, origin_left);
        }

        /// The replica removes the key, if it has a value.
        fn remove(&mut self) {
            self.map.remove("k");
            if let Some(&(client, clock, false)) = self.core_clocks().last() {
                self.core.delete_range(client, clock, clock + 1).unwrap();
            }
        }

        /// The replica takes everything `from` holds.
        fn receive(&mut self, from: &KeyReplica) {
            self.doc
                .apply_update_from_binary_v1(from.doc.encode_update_v1().unwrap())
                .unwrap();
            for (id, origin_left) in from.known.clone() {
                if self.core.node_id(id).is_none() {
                    self.integrate(id, origin_left);
                }
            }
            for (client, clock, deleted) in from.core_clocks() {
                if deleted {
                    self.core.delete_range(client, clock, clock + 1).unwrap();
                }
            }
        }

        /// The document and the core hold the same list, and at most its
        /// last clock is not deleted.
        fn check(&self, values: &HashMap<(u64, u64), String>) {
            let clocks = key_clocks(&self.doc);
            assert_eq!(clocks, self.core_clocks());
            let expected = match clocks.split_last() {
                Some((last, before)) => {
                    assert!(before.iter().all(|(_, _, deleted)| *deleted), "{clocks:?}");
                    (!last.2).then(|| Value::from(values[&(last.0, last.1)].as_str()))
                }
                None => None,
            };
            assert_eq!(self.map.get("k"), expected);
            self.doc.store.read().unwrap().self_check().unwrap();
        }
    }

    /// Replicas set and remove one map key and exchange what they hold in
    /// any order. Each is held to a `YataStoreCore` (the list of the key,
    /// made with a key of its own) whose links are what
    /// `decide_integrate_link` says: the same clocks in the same order with
    /// the same deletions, of which at most the last one is not deleted, and
    /// that one is the value of the key.
    #[test]
    #[cfg_attr(loom, ignore)]
    fn a_map_key_is_the_list_of_the_core_linked_as_the_kernel_says() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut below = move |n: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % n
        };
        let rounds = if cfg!(miri) { 2 } else { 40 };
        let steps = if cfg!(miri) { 30 } else { 120 };
        for round in 0..rounds {
            let count = 2 + below(3) as usize;
            let mut replicas: Vec<KeyReplica> = (0..count)
                .map(|at| KeyReplica::new(at as u64 + 1, (at + round) % 2 == 0, (below(u64::MAX), below(u64::MAX))))
                .collect();
            let mut values: HashMap<(u64, u64), String> = HashMap::new();
            for step in 0..steps {
                let at = below(count as u64) as usize;
                match below(10) {
                    0..=3 => {
                        let client = at as u64 + 1;
                        let value = format!("{round}/{step}");
                        values.insert((client, replicas[at].core.get_state(client)), value.clone());
                        replicas[at].set(&value);
                    }
                    4 => replicas[at].remove(),
                    _ => {
                        let from = below(count as u64) as usize;
                        if from != at {
                            let (low, high) = replicas.split_at_mut(from.max(at));
                            if from < at {
                                high[0].receive(&low[from]);
                            } else {
                                low[at].receive(&high[0]);
                            }
                        }
                    }
                }
                replicas[at].check(&values);
            }
            // everybody takes what everybody holds: one list, one value
            for _ in 0..2 {
                for at in 0..count {
                    for from in 0..count {
                        if from != at {
                            let (low, high) = replicas.split_at_mut(from.max(at));
                            if from < at {
                                high[0].receive(&low[from]);
                            } else {
                                low[at].receive(&high[0]);
                            }
                        }
                    }
                }
            }
            let first = key_clocks(&replicas[0].doc);
            for replica in &replicas {
                replica.check(&values);
                assert_eq!(key_clocks(&replica.doc), first, "round {round}");
                assert_eq!(replica.map.get("k"), replicas[0].map.get("k"));
            }
        }
    }

    /// A struct that names a type far below a root as its parent: every
    /// type above it is asked for, and none is kept in a set.
    #[test]
    #[cfg_attr(loom, ignore)]
    fn a_remote_type_under_a_deep_parent_is_linked() {
        let depth = if cfg!(miri) { 40 } else { 400 };
        let source = Doc::with_client(1);
        let mut parent = source.get_or_create_map("root").unwrap();
        for _ in 0..depth {
            let child = source.create_map().unwrap();
            parent.insert("child".into(), child.clone()).unwrap();
            parent = child;
        }
        let mut target = Doc::with_client(2);
        target
            .apply_update_from_binary_v1(source.encode_update_v1().unwrap())
            .unwrap();
        // one more type at the bottom, sent on its own
        let state = source.get_state_vector();
        parent.insert("leaf".into(), source.create_array().unwrap()).unwrap();
        target
            .apply_update_from_binary_v1(source.encode_state_as_update_v1(&state).unwrap())
            .unwrap();
        let store = target.store.read().unwrap();
        assert_eq!(store.type_arena.len(), depth + 2);
        store.self_check().unwrap();
        drop(store);
        assert_eq!(target.encode_update_v1().unwrap(), source.encode_update_v1().unwrap());
    }
}
