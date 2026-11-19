use std::{
    collections::{VecDeque, hash_map::Entry},
    mem,
    ops::Range,
};

use super::*;
use crate::{
    doc::StateVector,
    sync::{Arc, RwLock, Weak},
};

pub type ChangedTypeRefs = HashMap<YTypeRef, Vec<SmolStr>>;

#[derive(Default, Debug)]
pub(crate) struct DocStore {
    client: Client,
    pub items: ClientMap<VecDeque<Node>>,
    pub delete_set: DeleteSet,

    // following fields are only used in memory
    pub types: HashMap<String, YTypeRef>,
    // types created from this store but with no names,
    // we store it here to keep the ownership inside store without being
    // released.
    pub dangling_types: HashMap<usize, YTypeRef>,
    pub pending: Option<Update>,
    pub last_optimized_state: StateVector,
    // changed item's parent, value is the parent's sub key if exists
    pub changed: ChangedTypeRefs,
    // local redo mapping, old id range -> recreated id range
    pub redone: RedoMap,
    /// Ranges that became deleted since the last [DocStore::optimize]: the
    /// only ranges the next optimize garbage-collects and merges around.
    pub gc_pending: DeleteSet,
    /// Merge candidates outside of `gc_pending` and the newly added structs:
    /// right halves of structs split since the last [DocStore::optimize],
    /// already deleted children of types deleted since then, and children
    /// replaced by GC structs.
    pub merge_pending: Vec<Id>,
    /// ID ranges garbage collection must keep. Owned by
    /// the history layer; empty until it is wired up.
    pub retained: DeleteSet,
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

    pub fn client(&self) -> Client {
        self.client
    }

    pub fn set_client(&mut self, client: Client) {
        self.client = client;
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
        self.delete_set
            .values()
            .map(|v| match v {
                OrderRange::Range(_) => 1,
                OrderRange::Fragment(f) => f.len(),
            })
            .sum()
    }

    #[cfg(feature = "debug")]
    pub fn total_types(&self) -> usize {
        self.types.len()
    }

    #[cfg(feature = "debug")]
    pub fn total_dangling_types(&self) -> usize {
        self.dangling_types.len()
    }

    #[cfg(feature = "debug")]
    pub fn total_pending_nodes(&self) -> usize {
        self.pending.as_ref().map(|p| p.structs.len()).unwrap_or(0)
    }

    pub fn get_state(&self, client: Client) -> Clock {
        if let Some(structs) = self.items.get(&client) {
            if let Some(last_struct) = structs.back() {
                last_struct.clock() + last_struct.len()
            } else {
                warn!("client {client} has no struct info");
                0
            }
        } else {
            0
        }
    }

    pub fn get_state_vector(&self) -> StateVector {
        Self::items_as_state_vector(&self.items)
    }

    pub fn get_delete_sets(&self) -> DeleteSet {
        self.delete_set.clone()
    }

    fn items_as_state_vector(items: &ClientMap<VecDeque<Node>>) -> StateVector {
        let mut state = StateVector::default();
        for (client, structs) in items.iter() {
            if let Some(last_struct) = structs.back() {
                state.insert(*client, last_struct.clock() + last_struct.len());
            } else {
                warn!("client {client} has no struct info");
            }
        }
        state
    }

    pub fn add_node(&mut self, item: Node) -> JwstCodecResult {
        let client_id = item.client();
        match self.items.entry(client_id) {
            Entry::Occupied(mut entry) => {
                let structs = entry.get_mut();
                if let Some(last_struct) = structs.back() {
                    let expect = last_struct.clock() + last_struct.len();
                    let actually = item.clock();
                    if expect != actually {
                        return Err(JwstCodecError::StructClockInvalid { expect, actually });
                    }
                } else {
                    warn!("client {} has no struct info", client_id);
                }
                structs.push_back(item);
            }
            Entry::Vacant(entry) => {
                entry.insert(VecDeque::from([item]));
            }
        }

        Ok(())
    }

    /// binary search struct info on a sorted array
    pub fn get_node_index(items: &VecDeque<Node>, clock: Clock) -> Option<usize> {
        find_clock_segment(items.len(), clock, |index| {
            items.get(index).map(|node| (node.clock(), node.len()))
        })
    }

    pub fn create_item(
        &self,
        content: Content,
        left: Somr<Item>,
        right: Somr<Item>,
        parent: Option<Parent>,
        parent_sub: Option<SmolStr>,
    ) -> ItemRef {
        let id = (self.client(), self.get_state(self.client())).into();
        let item = Somr::new(Item::new(id, content, left, right, parent, parent_sub));

        if let Content::Type(ty) = &item.get().unwrap().content
            // SAFETY: callers hold the store write lock and only reference the
            // parent type. Local insertion preflights this child; preliminary
            // rebuilding uses a prepared acyclic tree. In both cases it is
            // distinct from the parent and all its ancestors.
            && let Some(mut ty) = unsafe { ty.ty_mut() }
        {
            ty.item = item.clone();
        }

        item
    }

    pub fn get_node<I: Into<Id>>(&self, id: I) -> Option<Node> {
        self.get_node_with_idx(id).map(|(item, _)| item)
    }

    pub fn get_node_with_idx<I: Into<Id>>(&self, id: I) -> Option<(Node, usize)> {
        let id = id.into();
        if let Some(items) = self.items.get(&id.client)
            && let Some(index) = Self::get_node_index(items, id.clock)
        {
            return items.get(index).map(|item| (item.clone(), index));
        }

        None
    }

    pub fn split_node<I: Into<Id>>(&mut self, id: I, diff: u64) -> JwstCodecResult<(Node, Node)> {
        debug_assert!(diff > 0);

        let id = id.into();

        if let Some(items) = self.items.get_mut(&id.client)
            && let Some(idx) = Self::get_node_index(items, id.clock)
        {
            let (left, right) = Self::split_node_at(items, idx, diff)?;
            self.merge_pending.push(right.id());
            return Ok((left, right));
        }

        Err(JwstCodecError::StructSequenceNotExists(id.client))
    }

    pub fn split_node_at(items: &mut VecDeque<Node>, idx: usize, diff: u64) -> JwstCodecResult<(Node, Node)> {
        debug_assert!(diff > 0);

        let node = items.get(idx).unwrap().clone();
        debug_assert!(node.is_item());
        if let Node::Item(item_ref) = &node {
            let item = item_ref.get().unwrap();

            let (left, right) = item.split_at(diff)?;

            let left_ref = Somr::new(left);
            let right_ref = Somr::new(right);

            // SAFETY:
            // we make sure store is the only entry of mutating an item,
            // and we already hold mutable reference of store, so it's safe to
            // do so
            unsafe {
                let mut left_item = item_ref.get_mut_unchecked();
                let mut right_item = right_ref.get_mut_unchecked();
                left_item
                    .replace_content_with_len(left_ref.get_unchecked().content.clone(), left_ref.get_unchecked().len());

                // we had the correct left/right content
                // now build the references
                let right_right_ref = left_item.right.clone();
                right_item.left = if right_right_ref.is_some() {
                    let mut right_right = right_right_ref.get_mut_unchecked();
                    mem::replace(&mut right_right.left, right_ref.clone())
                } else {
                    item_ref.clone()
                };
                right_item.right = mem::replace(&mut left_item.right, right_ref.clone());
                right_item.origin_left_id = Some(left_item.last_id());
                right_item.origin_right_id = left_item.origin_right_id;
            };

            let right = Node::Item(right_ref);
            let right_ref = right.clone();
            items.insert(idx + 1, right);
            Ok((node, right_ref))
        } else {
            Err(JwstCodecError::ItemSplitNotSupport)
        }
    }

    pub fn split_at_and_get_right<I: Into<Id>>(&mut self, id: I) -> JwstCodecResult<Node> {
        let id = id.into();
        if let Some(items) = self.items.get_mut(&id.client)
            && let Some(index) = Self::get_node_index(items, id.clock)
        {
            let item = items.get(index).unwrap().clone();
            let offset = id.clock - item.clock();
            if offset > 0 && item.is_item() {
                let (_, right) = Self::split_node_at(items, index, offset)?;
                self.merge_pending.push(right.id());
                return Ok(right);
            } else {
                return Ok(item);
            }
        }

        Err(JwstCodecError::StructSequenceNotExists(id.client))
    }

    pub fn split_at_and_get_left<I: Into<Id>>(&mut self, id: I) -> JwstCodecResult<Node> {
        let id = id.into();
        if let Some(items) = self.items.get_mut(&id.client)
            && let Some(index) = Self::get_node_index(items, id.clock)
        {
            let item = items.get(index).unwrap().clone();
            let offset = id.clock - item.clock();
            if offset != item.len() - 1 && !item.is_gc() {
                let (left, right) = Self::split_node_at(items, index, offset + 1)?;
                self.merge_pending.push(right.id());
                return Ok(left);
            } else {
                return Ok(item);
            }
        }

        Err(JwstCodecError::StructSequenceNotExists(id.client))
    }

    // TODO: use function in code
    #[allow(dead_code)]
    pub fn self_check(&self) -> JwstCodecResult {
        for structs in self.items.values() {
            for i in 1..structs.len() {
                let l = &structs[i - 1];
                let r = &structs[i];
                if l.clock() + l.len() != r.clock() {
                    return Err(JwstCodecError::StructSequenceInvalid {
                        client_id: l.client(),
                        clock: l.clock(),
                    });
                }
            }
        }

        Ok(())
    }

    // only for creating named type
    pub fn get_or_create_type(&mut self, store_ref: &StoreRef, name: &str) -> YTypeRef {
        match self.types.entry(name.to_string()) {
            Entry::Occupied(e) => e.get().clone(),
            Entry::Vacant(e) => {
                let mut inner = YType::new(YTypeKind::Unknown, None);
                inner.root_name = Some(name.to_string());
                inner.published = true;

                let ty = YTypeRef {
                    store: Arc::downgrade(store_ref),
                    inner: Somr::new(inner),
                };
                let ty_ref = ty.clone();
                e.insert(ty);
                ty_ref
            }
        }
    }

    /// A repair for an item do such things:
    ///   - split left if needed  (insert in between a splitable item)
    ///   - split right if needed (insert in between a splitable item)
    ///   - recover parent to [Parent::Type]
    ///     - [Parent::String] for root level named type (e.g
    ///       `doc.get_or_create_text("content")`)
    ///     - [Parent::Id] for type as item (e.g `doc.create_text()`)
    ///     - [None] means borrow left.parent or right.parent
    pub fn repair(&mut self, item: &mut Item, store_ref: StoreRef) -> JwstCodecResult {
        if let Some(left_id) = item.origin_left_id {
            if let Node::Item(left_ref) = self.split_at_and_get_left(left_id)? {
                item.origin_left_id = left_ref.get().map(|left| left.last_id());
                item.left = left_ref;
            } else {
                item.origin_left_id = None;
            }
        }

        if let Some(right_id) = item.origin_right_id {
            if let Node::Item(right_ref) = self.split_at_and_get_right(right_id)? {
                item.origin_right_id = right_ref.get().map(|right| right.id);
                item.right = right_ref;
            } else {
                item.origin_right_id = None;
            }
        }

        match &item.parent {
            // root level named type
            // doc.get_or_create_text("content");
            //                         ^^^^^^^ Parent::String("content")
            Some(Parent::String(str)) => {
                let ty = self.get_or_create_type(&store_ref, str);
                item.parent.replace(Parent::Type(ty));
            }
            // type as item
            // let text = doc.create_text();
            // let mut map = doc.get_or_create_map("content");
            // map.insert("p1", text);
            //
            // Item { id: (1, 0), content: Content::Type(_) }
            //        ^^ Parent::Id((1, 0))
            Some(Parent::Id(parent_id)) => {
                // Only an integrated carrier can back a stored parent identity.
                // The update iterator defers missing cross-client dependencies.
                item.parent = self.get_node(*parent_id).and_then(|node| {
                    let carrier = node.as_item();
                    match &carrier.get()?.content {
                        Content::Type(ty) => Some(Parent::Type(ty.clone())),
                        _ => None,
                    }
                });
            }
            // no item.parent, borrow left.parent or right.parent
            None => {
                if let Some(left) = ItemRef::from(item.left.clone()).get() {
                    item.parent = left.parent.clone();
                    item.parent_sub = left.parent_sub.clone();
                } else if let Some(right) = ItemRef::from(item.right.clone()).get() {
                    item.parent = right.parent.clone();
                    item.parent_sub = right.parent_sub.clone();
                }
            }
            _ => {}
        };

        // assign store in ytype to ensure store exists if a ytype not has any
        // children
        if let Content::Type(ty) = &mut item.content {
            ty.store = Arc::downgrade(&store_ref);

            // we keep ty owner in dangling_types so the delete of any type will
            // not make it dropped
            if ty.inner.is_owned() {
                let owned_inner = ty.inner.swap_take();
                self.dangling_types.insert(
                    ty.inner.ptr().as_ptr() as usize,
                    YTypeRef {
                        store: ty.store.clone(),
                        inner: owned_inner,
                    },
                );
            } else {
                return Err(JwstCodecError::InvalidParent);
            }
        }

        Ok(())
    }

    pub fn integrate(&mut self, mut node: Node, offset: u64, parent: Option<&mut YType>) -> JwstCodecResult {
        let mut publish_child = false;
        match &mut node {
            Node::Item(item_owner_ref) => {
                assert!(
                    item_owner_ref.is_owned(),
                    "Required a owned Item type but got an shared reference"
                );

                // SAFETY:
                // before we integrate struct into store,
                // the struct => Arc<Item> is owned reference actually,
                // no one else refer to such item yet, we can safely mutable
                // refer to it now.
                let this = &mut *unsafe { item_owner_ref.get_mut_unchecked() };

                if offset > 0 {
                    this.id.clock += offset;
                    if let Node::Item(left_ref) =
                        self.split_at_and_get_left(Id::new(this.id.client, this.id.clock - 1))?
                    {
                        this.origin_left_id = left_ref.get().map(|left| left.last_id());
                        this.left = left_ref;
                    }
                    let right_content = this.content.split(offset)?.1;
                    this.replace_content_with_len(right_content, this.len - offset);
                }

                if let Some(Parent::Type(ty)) = &this.parent {
                    // Corrupt updates may nest a type into itself or one of its
                    // own descendants. Deleting items of such cyclic types
                    // would re-lock an already held type lock and deadlock the
                    // thread, so reject the cycle here instead.
                    if let Content::Type(inner) = &this.content {
                        if inner == ty {
                            return Err(JwstCodecError::InvalidParent);
                        }
                        // When integrating from an update no type lock is held
                        // yet, so the ancestry can be walked safely with read
                        // locks. Mutation callers already hold the parent lock
                        // and can only create direct loops, checked above.
                        if parent.is_none() {
                            let next_ancestor = |current: &YTypeRef| {
                                current.ty().and_then(|t| {
                                    t.item.get().and_then(|item| match &item.parent {
                                        Some(Parent::Type(parent_ty)) => Some(parent_ty.clone()),
                                        _ => None,
                                    })
                                })
                            };
                            let mut visited = HashSet::new();
                            let mut ancestor = next_ancestor(ty);
                            while let Some(current) = ancestor {
                                if !visited.insert(current.clone()) {
                                    break;
                                }
                                if current == *inner {
                                    return Err(JwstCodecError::InvalidParent);
                                }
                                ancestor = next_ancestor(&current);
                            }
                        }
                    }
                }

                let mut parent_ref = None;
                let parent = if let Some(parent) = parent {
                    Some(parent)
                } else {
                    if let Some(Parent::Type(ty)) = &this.parent {
                        // SAFETY: remote integration holds the store write
                        // lock and no other type reference; the cycle check
                        // above keeps `this.content` distinct from the parent.
                        parent_ref = unsafe { ty.ty_mut() };
                    }
                    parent_ref.as_deref_mut()
                };

                let parent = parent.and_then(|parent| {
                    let deleted = match parent.item.get() {
                        Some(item) if matches!(item.content, Content::Type(_)) => item.deleted(),
                        // Named roots and private staging roots have no
                        // carrier.
                        None if parent.root_name.is_some() || parent.is_preliminary() && parent.item.is_unset() => {
                            false
                        }
                        // Collection either replaced the containing item or
                        // dropped its type content.
                        _ => return None,
                    };
                    Some((parent, deleted))
                });

                if let (Some(Parent::Type(ty)), Some((parent, parent_deleted))) = (&this.parent, parent) {
                    publish_child = parent.published;
                    let mut left = this.left.clone();
                    let mut right = this.right.clone();

                    let right_is_null_or_has_left = match right.get() {
                        None => true,
                        Some(r) => r.left.is_some(),
                    };

                    let left_has_other_right_than_self = match left.get() {
                        Some(left) => left.right != right,
                        _ => false,
                    };

                    // conflicts
                    if left.is_none() && right_is_null_or_has_left || left_has_other_right_than_self {
                        // set the first conflicting item
                        let conflict = if let Some(left) = left.get() {
                            left.right.clone()
                        } else if let Some(parent_sub) = &this.parent_sub {
                            // The map stores the winning tail; conflict
                            // scanning without a left neighbor must start at
                            // the chain head.
                            parent
                                .map
                                .get(parent_sub)
                                .map(|item| Node::Item(item.clone()).head().as_item())
                                .unwrap_or_else(Somr::none)
                        } else {
                            parent.start.clone()
                        };

                        left = find_conflict_left(
                            ConflictItem {
                                id: this.id,
                                origin_left: this.origin_left_id,
                                origin_right: this.origin_right_id,
                            },
                            left.is_some().then(|| left.clone()),
                            conflict.is_some().then(|| conflict.clone()),
                            right.is_some().then(|| right.clone()),
                            |item| {
                                item.get().map(|item| ConflictItem {
                                    id: item.id,
                                    origin_left: item.origin_left_id,
                                    origin_right: item.origin_right_id,
                                })
                            },
                            |item| {
                                item.get()
                                    .and_then(|item| item.right.is_some().then(|| item.right.clone()))
                            },
                            |id| self.get_node(id).map(|node| node.id()),
                        )
                        .unwrap_or_else(Somr::none);
                    }

                    // reconnect left/right
                    // has left, connect left <-> self <-> left.right
                    if left.is_some() {
                        unsafe {
                            // SAFETY: we get store write lock, no way the left
                            // get dropped by owner
                            let mut left = left.get_mut_unchecked();
                            right = left.right.clone();
                            left.right = item_owner_ref.clone();
                        }
                        this.left = left.clone();
                    } else {
                        // no left, parent.start = this
                        right = if let Some(parent_sub) = &this.parent_sub {
                            parent.map.get(parent_sub).map(|n| Node::Item(n.clone()).head()).into()
                        } else {
                            mem::replace(&mut parent.start, item_owner_ref.clone())
                        };
                        this.left = Somr::none();
                    }

                    // has right, connect
                    if right.is_some() {
                        unsafe {
                            // SAFETY: we get store write lock, no way the left
                            // get dropped by owner
                            let mut right = right.get_mut_unchecked();
                            right.left = item_owner_ref.clone();
                        }
                    } else {
                        // no right, parent.start = this, delete this.left
                        if let Some(parent_sub) = &this.parent_sub {
                            parent.map.insert(parent_sub.clone(), item_owner_ref.clone());

                            if let Some(left) = this.left.get() {
                                self.delete_item(left, Some(parent));
                            }
                        }
                    }
                    this.right = right.clone();

                    // should delete
                    if parent_deleted || this.parent_sub.is_some() && this.right.is_some() {
                        self.delete_node(&Node::Item(item_owner_ref.clone()), Some(parent));
                    } else {
                        // adjust parent length
                        if this.parent_sub.is_none() && this.countable() {
                            parent.len += this.len();
                        }
                    }

                    // mark changed item's parent
                    Self::mark_changed(&mut self.changed, ty.clone(), this.parent_sub.clone());
                } else {
                    // Preserve the integrated clock range when the parent is
                    // missing or collected.
                    node = Node::new_gc(this.id, this.len());
                }
            }
            Node::GC(item) => {
                if offset > 0 {
                    item.id.clock += offset;
                    item.len -= offset;
                }
            }
            Node::Skip(_) => {
                // skip ignored
            }
        }
        let child = match &node {
            Node::Item(item) => match &item.get().unwrap().content {
                Content::Type(ty) => Some(ty.clone()),
                _ => None,
            },
            _ => None,
        };
        self.add_node(node)?;
        if let Some(child) = child {
            if publish_child {
                // SAFETY: the document write lock is held. The child's carrying
                // item was just added, and the acyclic child is distinct from
                // the parent. This covers local, remote and rebuilt children.
                unsafe { child.ty_mut() }.unwrap().published = true;
            }
            self.integrate_preliminary(&child)?;
        }
        Ok(())
    }

    pub fn delete_item(&mut self, item: &Item, parent: Option<&mut YType>) {
        let mut pending_delete_sets = HashMap::new();
        Self::delete_item_inner(
            &mut pending_delete_sets,
            &mut self.merge_pending,
            &mut self.changed,
            item,
            parent,
        );
        self.add_deleted(pending_delete_sets);
    }

    /// Records ranges deleted for the first time.
    fn add_deleted(&mut self, ranges: HashMap<u64, Vec<Range<u64>>>) {
        for (client, ranges) in ranges {
            self.gc_pending.batch_add_ranges(client, ranges.clone());
            self.delete_set.batch_add_ranges(client, ranges);
        }
    }

    fn delete_item_inner(
        delete_set: &mut HashMap<u64, Vec<Range<u64>>>,
        merges: &mut Vec<Id>,
        changed: &mut ChangedTypeRefs,
        item: &Item,
        parent: Option<&mut YType>,
    ) {
        // 1. mark item as deleted, if item is gced, return
        if !item.delete() {
            return;
        }

        // 2. add it to delete set
        let range = item.id.clock..item.id.clock + item.len();
        delete_set
            .entry(item.id.client)
            .and_modify(|v| v.push(range.clone()))
            .or_insert(vec![range]);

        // 3. adjust parent length
        if item.parent_sub.is_none() && item.countable() {
            if let Some(parent) = parent {
                if parent.len != 0 {
                    parent.len -= item.len();
                }
            } else if let Some(Parent::Type(ty)) = &item.parent
                // SAFETY: store write lock held; without `parent` the caller
                // holds no reference to this type.
                && let Some(mut ty) = unsafe { ty.ty_mut() }
            {
                ty.len -= item.len();
            }
        }

        match &item.content {
            Content::Type(ty) => {
                // 4. delete all children
                // SAFETY: store write lock held; the type tree is acyclic, so
                // `ty` is not the `parent` borrowed by the caller nor any
                // type borrowed further up this recursion. Local inserts keep
                // it acyclic because `check_insertable` inserts a type at most
                // once and walks its new ancestors; integrate rejects cycles
                // in remote updates.
                if let Some(mut ty) = unsafe { ty.ty_mut() } {
                    // items in ty are all refs, not owned
                    // children deleted earlier are not in this delete set; Yjs
                    // `ContentType.delete` queues them for merging
                    let mut item_ref = ty.start.clone();
                    while let Some(item) = item_ref.get() {
                        if !item.deleted() {
                            Self::delete_item_inner(delete_set, merges, changed, item, Some(&mut ty));
                        } else {
                            merges.push(item.id);
                        }

                        item_ref = item.right.clone();
                    }

                    let map_values = ty.map.values().cloned().collect::<Vec<_>>();
                    for item in map_values {
                        if let Some(item) = item.get() {
                            if !item.deleted() {
                                Self::delete_item_inner(delete_set, merges, changed, item, Some(&mut ty));
                            } else {
                                merges.push(item.id);
                            }
                        }
                    }
                }
            }
            Content::Doc { .. } => {
                // TODO: remove subdoc
            }
            _ => {}
        }

        // mark deleted item's parent
        if let Some(Parent::Type(ty)) = &item.parent {
            Self::mark_changed(changed, ty.clone(), item.parent_sub.clone());
        }
    }

    pub fn delete_node(&mut self, struct_info: &Node, parent: Option<&mut YType>) {
        if let Some(item) = struct_info.as_item().get() {
            self.delete_item(item, parent);
        }
    }

    pub fn delete_range(&mut self, client: u64, range: Range<u64>) -> JwstCodecResult {
        let start = range.start;
        let end = range.end;

        if let Some(items) = self.items.get_mut(&client)
            && let Some(mut idx) = DocStore::get_node_index(items, start)
        {
            {
                // id.clock <= range.start < id.end
                // need to split the item and delete the right part
                // -----item-----
                //    ^start
                let node = &items[idx];
                let id = node.id();

                if !node.deleted() && id.clock < start {
                    let (_, right) = DocStore::split_node_at(items, idx, start - id.clock)?;
                    self.merge_pending.push(right.id());
                    idx += 1;
                }
            };

            let mut pending_delete_sets = HashMap::new();
            while idx < items.len() {
                let node = items[idx].clone();
                let id = node.id();

                if id.clock < end {
                    if !node.deleted() && node.is_item() {
                        // need to split the item
                        // -----item-----
                        //           ^end
                        if end < id.clock + node.len() {
                            let (_, right) = DocStore::split_node_at(items, idx, end - id.clock)?;
                            self.merge_pending.push(right.id());
                        }

                        // borrow after the split: split_node_at mutates the
                        // item in place and would
                        // invalidate a guard acquired earlier
                        if let Some(item) = node.as_item().get() {
                            Self::delete_item_inner(
                                &mut pending_delete_sets,
                                &mut self.merge_pending,
                                &mut self.changed,
                                item,
                                None,
                            );
                        }
                    }
                } else {
                    break;
                }
                idx += 1;
            }
            self.add_deleted(pending_delete_sets);
        };

        Ok(())
    }

    fn diff_state_vectors(local_state_vector: &StateVector, remote_state_vector: &StateVector) -> Vec<(Client, Clock)> {
        let mut diff = Vec::new();

        for (client, &remote_clock) in remote_state_vector.iter() {
            let local_clock = local_state_vector.get(client);
            if local_clock > remote_clock {
                diff.push((*client, remote_clock));
            }
        }

        for (client, _) in local_state_vector.iter() {
            if remote_state_vector.get(client) == 0 {
                diff.push((*client, 0));
            }
        }

        diff
    }

    pub fn diff_state_vector(&self, sv: &StateVector, with_pending: bool) -> JwstCodecResult<Update> {
        let update_structs = Self::diff_structs(&self.items, sv)?;

        let mut update = Update {
            structs: update_structs,
            delete_set: Self::generate_delete_set(&self.items),
            ..Update::default()
        };

        if with_pending && let Some(pending) = &self.pending {
            // Pending does not mean unknown to the recipient. Apply its SV to
            // these ranges too, while retaining deletions for missing targets.
            // The structs are shared with `self.pending`: the result is only
            // used under the store lock.
            let pending = Update {
                structs: Self::diff_structs(&pending.structs, sv)?,
                delete_set: pending.delete_set.clone(),
                pending_structs: pending.pending_structs.clone(),
                missing_state: pending.missing_state.clone(),
                pending_delete_set: pending.pending_delete_set.clone(),
            };
            Update::merge_into(&mut update, [pending]);
        }

        Ok(update)
    }

    fn mark_changed(changed: &mut ChangedTypeRefs, parent: YTypeRef, parent_sub: Option<SmolStr>) {
        if parent.inner.is_some() {
            let vec = changed.entry(parent).or_default();
            if let Some(parent_sub) = parent_sub {
                // only record the sub key if exists
                vec.push(parent_sub);
            }
        }
    }

    #[cfg(test)]
    pub fn get_changed(&mut self) -> ChangedTypeRefs {
        mem::replace(&mut self.changed, HashMap::new())
    }

    fn diff_structs(map: &ClientMap<VecDeque<Node>>, sv: &StateVector) -> JwstCodecResult<ClientMap<VecDeque<Node>>> {
        let local_state_vector = Self::items_as_state_vector(map);
        let diff = Self::diff_state_vectors(&local_state_vector, sv);
        let mut update_structs = ClientMap::new();

        for (client, clock) in diff {
            // We have made sure that the client is in the local state vector in
            // diff_state_vectors()
            if let Some(items) = map.get(&client) {
                if items.is_empty() {
                    continue;
                }

                update_structs.insert(client, VecDeque::new());
                let vec_struct_info = update_structs.get_mut(&client).unwrap();

                // the smallest clock in items may exceed the clock
                let clock = items.front().unwrap().id().clock.max(clock);
                if let Some(index) = Self::get_node_index(items, clock) {
                    let first_block = items.get(index).unwrap();
                    // The recipient clock may fall inside a compacted struct;
                    // split a detached copy so generating a diff leaves the
                    // store unchanged.
                    let offset = clock - first_block.clock();
                    if offset != 0 {
                        vec_struct_info.push_back(first_block.split_at(offset)?.1);
                    } else {
                        vec_struct_info.push_back(first_block.clone());
                    }

                    for item in items.iter().skip(index + 1) {
                        vec_struct_info.push_back(item.clone());
                    }
                }
            }
        }

        Ok(update_structs)
    }

    fn generate_delete_set(refs: &ClientMap<VecDeque<Node>>) -> DeleteSet {
        let mut delete_set = DeleteSet::default();

        for (client, nodes) in refs {
            nodes
                .iter()
                .filter(|n| n.deleted())
                .for_each(|n| delete_set.add(*client, n.clock(), n.len()));
        }

        delete_set
    }

    /// Garbage-collects and merges what changed since the last call, after
    /// Yjs v13.6.33 `cleanupTransactions`: GC of the ranges deleted since
    /// then (`tryGcDeleteSet`), merge around them (`tryMergeDeleteSet`),
    /// merge of the structs added since `last_optimized_state` and of the
    /// recorded split points (`_mergeStructs`). The cost follows the size of
    /// the change, not of the document.
    pub fn optimize(&mut self, gc: bool) {
        let deleted = mem::take(&mut self.gc_pending);

        if gc {
            self.gc_delete_set(&deleted);
        }
        // includes the children GC just replaced
        let merges = mem::take(&mut self.merge_pending);
        self.merge_delete_set(&deleted);
        self.make_continuous();
        self.merge_split_points(&merges);
    }

    /// Full GC and merge over the whole delete set and every struct.
    pub fn optimize_all(&mut self) {
        self.gc_pending.merge(&self.delete_set.clone());
        self.last_optimized_state = StateVector::default();
        self.optimize(true)
    }

    /// Whether GC must keep any part of `len` structs starting at `id`.
    fn is_retained(&self, id: Id, len: u64) -> bool {
        self.retained
            .get(&id.client)
            .is_some_and(|ranges| ranges.into_iter().any(|r| r.start < id.clock + len && id.clock < r.end))
    }

    fn gc_delete_set(&mut self, deleted: &DeleteSet) {
        for (client, ranges) in deleted.iter() {
            for range in ranges {
                let Some(mut idx) = self
                    .items
                    .get(client)
                    .and_then(|items| Self::get_node_index(items, range.start))
                else {
                    continue;
                };

                while let Some(node) = self.items.get(client).and_then(|items| items.get(idx)).cloned() {
                    if range.end <= node.clock() {
                        break;
                    }

                    if let Node::Item(item_ref) = &node
                        && let Some(item) = item_ref.get()
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
    fn gc_item(&mut self, item_ref: &ItemRef, parent_gced: bool) {
        let item = item_ref.get().expect("collected items are live");
        debug_assert!(item.deleted());
        let (id, len) = (item.id, item.len());

        if let Content::Type(ty) = &item.content {
            self.gc_type(ty);
        }

        if parent_gced {
            let items = self.items.get_mut(&id.client).expect("live items are in the store");
            let idx = Self::get_node_index(items, id.clock).expect("live items are in the store");
            debug_assert_eq!(items[idx].id(), id);
            items[idx] = Node::new_gc(id, len);
            // Overwritten map values are neither in this delete set nor queued
            // by `delete_item_inner`, so Yjs leaves their GC structs unmerged;
            // queue every replaced child instead.
            self.merge_pending.push(id);
        } else {
            // SAFETY: GC runs under the store write lock with nothing borrowed.
            let mut item = unsafe { item_ref.get_mut_unchecked() };
            item.replace_content(Content::Deleted(len));
            item.flags.clear_countable();
        }
    }

    /// Yjs `ContentType.gc`: collects every child of a type whose item is
    /// being collected.
    fn gc_type(&mut self, ty: &YTypeRef) {
        let mut children = Vec::new();
        if let Some(ty) = ty.ty() {
            let mut item = ty.start.clone();
            while let Some(next) = item.get().map(|i| i.right.clone()) {
                children.push(item);
                item = next;
            }
            for value in ty.map.values() {
                let mut item = value.clone();
                while let Some(next) = item.get().map(|i| i.left.clone()) {
                    children.push(item);
                    item = next;
                }
            }
        }

        // SAFETY: GC runs under the store write lock with no type borrowed.
        if let Some(mut ty) = unsafe { ty.ty_mut() } {
            ty.start = Somr::none();
            ty.map.clear();
            if let Some(markers) = &mut ty.markers {
                markers.clear();
            }
        }

        for child in children {
            self.gc_item(&child, true);
        }
    }

    /// Yjs `tryMergeDeleteSet`: merges the structs in and right after each
    /// deleted range, from right to left.
    fn merge_delete_set(&mut self, deleted: &DeleteSet) {
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
                while si > 0 && nodes[si].clock() >= range.start {
                    si = si.saturating_sub(1 + Self::merge_with_lefts(nodes, si));
                }
            }
        }
    }

    /// Merges every struct added since `last_optimized_state`.
    fn make_continuous(&mut self) {
        let state = self.get_state_vector();

        for (client, state) in state.iter() {
            let before_state = self.last_optimized_state.get(client);
            if before_state == *state {
                continue;
            }

            let nodes = self.items.get_mut(client).unwrap();
            let first_change = Self::get_node_index(nodes, before_state).unwrap_or(1).max(1);
            let mut idx = nodes.len() - 1;

            while idx > 0 && idx >= first_change {
                idx = idx.saturating_sub(Self::merge_with_lefts(nodes, idx) + 1);
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
            if pos + 1 < nodes.len() && Self::merge_with_lefts(nodes, pos + 1) > 1 {
                // both neighbors are already merged
                continue;
            }
            if pos > 0 {
                Self::merge_with_lefts(nodes, pos);
            }
        }
    }

    /// Yjs `tryToMergeWithLefts`: merges `nodes[idx]` into its left
    /// neighbors as far as possible and returns how many were merged.
    fn merge_with_lefts(nodes: &mut VecDeque<Node>, idx: usize) -> usize {
        let mut pos = idx;
        loop {
            if pos == 0 {
                break;
            }

            let right = nodes.get(pos).unwrap().clone();
            let left = nodes.get_mut(pos - 1).unwrap();

            if !left.merge(right.clone()) {
                break;
            }

            // the merged right item may be the current value of its map key
            if let Node::Item(right) = &right
                && let Some(item) = right.get()
                && let (Some(Parent::Type(parent)), Some(key)) = (&item.parent, &item.parent_sub)
                // SAFETY: merging runs under the store write lock with no type
                // borrowed.
                && let Some(mut parent) = unsafe { parent.ty_mut() }
                && parent.map.get(key).is_some_and(|current| current.ptr_eq(right))
            {
                parent.map.insert(key.clone(), left.as_item());
            }

            pos -= 1;
        }
        nodes.drain(pos + 1..=idx);

        // return the index of processed items
        idx - pos
    }

    pub fn deep_compare(&self, other: &Self) -> bool {
        if self.items.len() != other.items.len() {
            return false;
        }

        for (client, structs) in self.items.iter() {
            if let Some(other_structs) = other.items.get(client) {
                if structs.len() != other_structs.len() {
                    return false;
                }

                for (struct_info, other_struct_info) in structs.iter().zip(other_structs.iter()) {
                    if struct_info != other_struct_info {
                        return false;
                    }
                    if let (Node::Item(item), Node::Item(other_item)) = (struct_info, other_struct_info)
                        && !match (item.get(), other_item.get()) {
                            (Some(item), Some(other_item)) => item.deep_compare(other_item),
                            (None, None) => true,
                            _ => false,
                        }
                    {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

            doc_store
                .items
                .insert(client_id, VecDeque::from([struct_info1, struct_info2.clone()]));

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

            doc_store.items.insert(client1, VecDeque::from([struct_info1.clone()]));
            doc_store
                .items
                .insert(client2, VecDeque::from([struct_info2, struct_info3.clone()]));

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

            assert!(doc_store.add_node(struct_info1.clone()).is_ok());
            assert!(doc_store.add_node(struct_info2).is_ok());
            assert_eq!(
                doc_store.add_node(struct_info3_err),
                Err(JwstCodecError::StructClockInvalid { expect: 6, actually: 5 })
            );
            assert!(doc_store.add_node(struct_info3.clone()).is_ok());
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
            doc_store.add_node(struct_info.clone()).unwrap();

            assert_eq!(doc_store.get_node(Id::new(1, 9)), Some(struct_info));
        });

        loom_model!({
            let mut doc_store = DocStore::with_client(1);
            let struct_info1 = Node::new_gc(Id::new(1, 0), 10);
            let struct_info2 = Node::new_gc(Id::new(1, 10), 20);
            doc_store.add_node(struct_info1).unwrap();
            doc_store.add_node(struct_info2.clone()).unwrap();

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
            let node = Node::Item(Somr::new(
                ItemBuilder::new()
                    .id((1, 0).into())
                    .content(Content::String(String::from("octo")))
                    .build(),
            ));
            let mut list = VecDeque::from([node.clone()]);

            let (left, right) = DocStore::split_node_at(&mut list, 0, 2).unwrap();

            assert_eq!(
                node.as_item().ptr().as_ptr() as usize,
                left.as_item().ptr().as_ptr() as usize
            );
            assert_eq!(node.len(), 2);
            assert_eq!(left.len(), 2);
            assert_eq!(right.len(), 2);
            assert_eq!(left.right(), Some(right.clone()));
            assert_eq!(right.left(), Some(left));
        });
    }

    #[test]
    fn test_split_and_get() {
        loom_model!({
            let mut doc_store = DocStore::with_client(1);
            let struct_info1 = Node::Item(Somr::new(
                ItemBuilder::new()
                    .id((1, 0).into())
                    .content(Content::String(String::from("octo")))
                    .build(),
            ));

            let struct_info2 = Node::Item(Somr::new(
                ItemBuilder::new()
                    .id((1, struct_info1.len()).into())
                    .left_id(Some(struct_info1.id()))
                    .content(Content::String(String::from("base")))
                    .build(),
            ));
            let s1_ref = struct_info1.clone();
            doc_store.add_node(struct_info1).unwrap();
            doc_store.add_node(struct_info2).unwrap();

            let s1 = doc_store.get_node(Id::new(1, 0)).unwrap();
            assert_eq!(s1, s1_ref);
            let left = doc_store.split_at_and_get_left((1, 1)).unwrap();
            assert_eq!(left.len(), 2); // octo => oc_to

            // s1 used to be (1, 4), but it actually ref of first item in store,
            // so now it should be (1, 2)
            assert_eq!(s1, left, "doc internal mutation should not modify the pointer");
            let right = doc_store.split_at_and_get_right((1, 5)).unwrap();
            assert_eq!(right.len(), 3); // base => b_ase
        });
    }

    #[test]
    fn should_mark_changed_items() {
        loom_model!({
            let doc = DocOptions::new().with_client_id(1).build();

            let mut arr = doc.get_or_create_array("arr").unwrap();
            let mut text = doc.create_text().unwrap();
            let mut map = doc.create_map().unwrap();

            arr.insert(0, Value::from(text.clone())).unwrap();
            arr.insert(1, Value::from(map.clone())).unwrap();
            {
                let changed = doc.store.write().unwrap().get_changed();
                // for array, we will only record the type ref itself
                assert_eq!(changed.len(), 1);
                assert_eq!(changed.get(&arr.0), Some(&vec![]));
            }

            text.insert(0, "hello world").unwrap();
            text.remove(5, 6).unwrap();
            {
                let changed = doc.store.write().unwrap().get_changed();
                assert_eq!(changed.len(), 1);
                assert_eq!(changed.get(&text.0), Some(&vec![]));
            }

            map.insert("key".into(), 123).unwrap();
            {
                let changed = doc.store.write().unwrap().get_changed();
                assert_eq!(changed.len(), 1);
                assert_eq!(changed.get(&map.0), Some(&vec!["key".into()]));
            }

            map.remove("key");
            {
                let changed = doc.store.write().unwrap().get_changed();
                assert_eq!(changed.len(), 1);
                assert_eq!(changed.get(&map.0), Some(&vec!["key".into()]));
            }

            arr.remove(0, 1).unwrap();
            {
                let changed = doc.store.write().unwrap().get_changed();
                assert_eq!(changed.len(), 2);
                // text's children mark parent(text) changed
                assert_eq!(changed.get(&text.0), Some(&vec![]));
                // text mark parent(arr) changed
                assert_eq!(changed.get(&arr.0), Some(&vec![]));
            }
        });
    }

    #[test]
    fn should_replace_gc_item_with_content_deleted() {
        loom_model!({
            let item1 = ItemBuilder::new()
                .id((1, 0).into())
                .content(Content::String(String::from("octo")))
                .build();
            let item2 = ItemBuilder::new()
                .id((1, 4).into())
                .content(Content::String(String::from("base")))
                .build();

            item1.delete();

            let mut store = DocStore::with_client(1);

            store.add_node(Node::Item(Somr::new(item1))).unwrap();
            store.add_node(Node::Item(Somr::new(item2))).unwrap();
            store.delete_set.add_range(1, 0..4);

            let ds = store.delete_set.clone();
            store.gc_delete_set(&ds);

            assert_eq!(
                &store.get_node((1, 0)).unwrap().as_item().get().unwrap().content,
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
            let ds = store.delete_set.clone();
            store.gc_delete_set(&ds);

            assert_eq!(
                &store.get_node((1, 0)).unwrap().as_item().get().unwrap().content,
                &Content::Deleted(1)
            );

            assert_eq!(
                store.get_node((1, 1)).unwrap(), // "hello" GCd
                Node::new_gc((1, 1).into(), 5)
            );

            assert_eq!(
                store.get_node((1, 7)).unwrap(), // " world" GCd
                Node::new_gc((1, 6).into(), 6)
            );
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
            store
                .get_node((1, 0))
                .unwrap()
                .as_item()
                .get()
                .unwrap()
                .flags
                .set_keep();
            let ds = store.delete_set.clone();
            store.gc_delete_set(&ds);

            assert!(matches!(
                &store.get_node((1, 0)).unwrap().as_item().get().unwrap().content,
                Content::Type(_)
            ));
            let hello = store.get_node((1, 1)).unwrap();
            assert!(hello.is_item());
            assert_eq!(&hello.as_item().get().unwrap().content, &Content::Deleted(5));
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
            let ds = store.delete_set.clone();
            store.gc_delete_set(&ds);

            assert_eq!(
                &store.get_node((1, 0)).unwrap().as_item().get().unwrap().content,
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

    #[test]
    fn should_merge_same_sibling_items() {
        loom_model!({
            let mut store = DocStore::with_client(1);
            store.items.insert(
                1,
                VecDeque::from([
                    Node::new_gc((1, 0).into(), 2),
                    Node::new_gc((1, 2).into(), 2),
                    Node::new_skip((1, 4).into(), 2),
                    Node::Item(Somr::new(
                        ItemBuilder::new()
                            .id((1, 6).into())
                            .content(Content::String(String::from("hello")))
                            .build(),
                    )),
                    // actually not mergable, due to runtime continuous check
                    // will cover it in [test_merge_same_sibling_items2]
                    Node::Item(Somr::new(
                        ItemBuilder::new()
                            .id((1, 11).into())
                            .content(Content::String(String::from("world")))
                            .left_id(Some((1, 11).into()))
                            .build(),
                    )),
                ]),
            );

            store.make_continuous();

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

            {
                let mut store = doc.store.write().unwrap();
                assert_eq!(store.items.get(&1).unwrap().len(), 4);
                store.make_continuous();
                assert_eq!(store.items.get(&1).unwrap().len(), 1);
            }
            assert_eq!(text.to_string(), "abc, hello");
        });
    }
}
