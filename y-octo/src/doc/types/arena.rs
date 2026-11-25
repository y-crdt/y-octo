use std::{
    mem,
    num::NonZeroU32,
    ops::{Deref, DerefMut, Index, IndexMut},
};

use y_octo_core::doc_kernel::{ParentWalkStep, parent_walk_step};

use super::*;

/// The slot of a [YType] in the [TypeArena] of its document.
///
/// An index is only meaningful in the store that allocated it. It stays valid
/// for the life of that store: slots are never reused, and only
/// [TypeArena::rollback] removes one, for a type nothing refers to yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct TypeIdx(NonZeroU32);

impl TypeIdx {
    /// The index of the `slot`-th type (0-based), `None` past `u32::MAX`
    /// types.
    fn from_slot(slot: usize) -> Option<Self> {
        u32::try_from(slot)
            .ok()
            .and_then(|slot| slot.checked_add(1))
            .and_then(NonZeroU32::new)
            .map(Self)
    }

    fn slot(self) -> usize {
        // u32 fits usize on every supported target
        (self.0.get() - 1) as usize
    }

    /// The index as one number: what `y_octo_core::doc_kernel` tells types
    /// apart by.
    #[inline]
    pub(in crate::doc) fn raw(self) -> u32 {
        self.0.get()
    }
}

/// Every type of a document, named roots and nested or preliminary types
/// alike, owned by its [DocStore] and addressed by [TypeIdx].
///
/// The store lock protects it like the rest of the store: readers borrow the
/// store, writers borrow it mutably, and no type data is reachable without
/// one of the two.
#[derive(Debug, Default)]
pub(crate) struct TypeArena {
    slots: Vec<YType>,
    pub items: ItemSpace,
    /// A smaller capacity, to reach the full arena in tests.
    #[cfg(test)]
    limit: Option<usize>,
}

impl TypeArena {
    /// Update item links in live types and outstanding preliminary timelines.
    pub(in crate::doc) fn remap_items(&mut self, moved: &Moved) {
        let remap = |link: &mut ItemRef| *link = link.and_then(|i| moved.get(i));
        self.items.for_each_mut(|item| {
            remap(&mut item.left);
            remap(&mut item.right);
        });
        for ty in &mut self.slots {
            remap(&mut ty.start);
            remap(&mut ty.item);
            if let Some(map) = &mut ty.map {
                map.retain(|_, link| {
                    remap(link);
                    link.is_some()
                });
            }
            if let Some(markers) = &mut ty.markers {
                markers.clear();
            }
            if let Some(staging) = &mut ty.preliminary {
                for blocks in staging.items.values_mut() {
                    blocks.remap(moved);
                }
            }
        }
    }

    #[cfg(test)]
    pub(in crate::doc) fn types(&self) -> impl Iterator<Item = &YType> {
        self.slots.iter()
    }

    pub fn type_and_items(&mut self, id: TypeIdx) -> (&mut YType, &ItemSpace) {
        (&mut self.slots[id.slot()], &self.items)
    }

    /// How many types the arena can hold: every index fits [TypeIdx].
    fn capacity(&self) -> usize {
        #[cfg(test)]
        if let Some(limit) = self.limit {
            return limit;
        }
        u32::MAX as usize
    }

    #[cfg(test)]
    pub fn set_limit(&mut self, limit: Option<usize>) {
        self.limit = limit;
    }

    /// Whether `needed` more types fit. An operation that allocates several
    /// types asks before it changes anything, so it fails as a whole.
    pub fn check_capacity(&self, needed: usize) -> JwstCodecResult {
        match self.slots.len().checked_add(needed) {
            Some(total) if total <= self.capacity() => Ok(()),
            _ => Err(JwstCodecError::IncompleteDocument(TOO_MANY_TYPES.into())),
        }
    }

    /// Stores `ty` and returns its index. Fails once the document holds
    /// `u32::MAX` types.
    pub fn alloc(&mut self, ty: YType) -> JwstCodecResult<TypeIdx> {
        self.check_capacity(1)?;
        let id = TypeIdx::from_slot(self.slots.len())
            .ok_or_else(|| JwstCodecError::IncompleteDocument(TOO_MANY_TYPES.into()))?;
        self.slots.push(ty);
        Ok(id)
    }

    #[inline]
    pub fn get(&self, id: TypeIdx) -> Option<&YType> {
        self.slots.get(id.slot())
    }

    #[inline]
    pub fn get_mut(&mut self, id: TypeIdx) -> Option<&mut YType> {
        self.slots.get_mut(id.slot())
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    /// Drops the types allocated since the arena had `len` types. Only for an
    /// operation that allocated them and failed before anything (an item, a
    /// handle given out, a root name) could refer to them.
    pub fn rollback(&mut self, len: usize) {
        debug_assert!(
            self.slots[len.min(self.slots.len())..]
                .iter()
                .all(|ty| ty.root_name().is_none() && !matches!(ty.carrier(&self.items), Carrier::Live(_)))
        );
        self.slots.truncate(len);
    }

    /// The type holding the carrier of `id`: the next step up the type tree.
    /// `None` for a root, for a type that was never inserted and for a
    /// retired one.
    pub fn parent_of(&self, id: TypeIdx) -> Option<TypeIdx> {
        let ty = self.get(id)?;
        match ty.carrier(&self.items) {
            Carrier::Live(_) => ty.parent_type,
            Carrier::Unset | Carrier::Retired => None,
        }
    }

    /// Whether `inner` is one of the types above `ty`: its parent, the
    /// parent of that one, and so on. `ty` itself is not asked for.
    ///
    /// The walk takes as many steps as the arena has types and keeps no set
    /// of the ones it met (`parent_walk_step` of `y-octo-core`): only a
    /// stored type has a parent, so a type that is above `ty` is met within
    /// that many steps, however the types above `ty` loop
    /// (`DocKernel.walk_iff_reach` in `proofs/`).
    pub fn is_above(&self, inner: TypeIdx, ty: TypeIdx) -> bool {
        let inner = inner.raw();
        let mut remaining = self.slots.len();
        let mut ancestor = self.parent_of(ty);
        while let Some(current) = ancestor {
            match parent_walk_step(inner, current.raw(), remaining) {
                ParentWalkStep::Cycle => return true,
                ParentWalkStep::Exhausted => return false,
                ParentWalkStep::Continue(rest) => remaining = rest,
            }
            ancestor = self.parent_of(current);
        }
        false
    }
}

impl Index<TypeIdx> for TypeArena {
    type Output = YType;

    /// For an index taken from this store's own items and tables, which
    /// always refer to a stored type.
    #[inline]
    fn index(&self, id: TypeIdx) -> &YType {
        &self.slots[id.slot()]
    }
}

impl IndexMut<TypeIdx> for TypeArena {
    #[inline]
    fn index_mut(&mut self, id: TypeIdx) -> &mut YType {
        &mut self.slots[id.slot()]
    }
}

/// What a reader holding the store lock needs to follow type indices and to
/// hand out public handles for the types it finds.
#[derive(Clone, Copy)]
pub(crate) struct TypeCx<'a> {
    /// The document the types belong to: the identity half of a handle.
    pub store: &'a WeakStoreRef,
    pub types: &'a TypeArena,
}

impl<'a> TypeCx<'a> {
    pub fn new(store: &'a WeakStoreRef, types: &'a TypeArena) -> Self {
        Self { store, types }
    }

    #[inline]
    pub fn get(&self, id: TypeIdx) -> Option<&'a YType> {
        self.types.get(id)
    }

    /// A public handle to the type at `id`.
    pub fn handle(&self, id: TypeIdx) -> YTypeRef {
        YTypeRef {
            store: self.store.clone(),
            id: Some(id),
        }
    }
}

/// The private editing store of a preliminary subtree, moved out of its root
/// type for one edit.
///
/// While it is alive the host's type arena is swapped into the staging store,
/// so the edit sees every type of the document through the one store it is
/// given, and the host store is not touched. Dropping it, also on unwinding,
/// swaps the arena back and returns the staging store to the root type, with
/// an empty collector: nothing commits a staging store, so what an edit
/// collected would only pile up.
pub(super) struct Staging<'a> {
    host: &'a mut DocStore,
    root: TypeIdx,
    store: Option<Box<DocStore>>,
}

impl<'a> Staging<'a> {
    /// `root` is a preliminary root of `host`, as returned by
    /// [TypeArena::preliminary_root].
    pub fn enter(host: &'a mut DocStore, root: TypeIdx) -> Self {
        // An edit running in a staging store already has the arena; entering
        // again from it would edit a second, empty store for the same root.
        debug_assert!(!host.staging, "edit of a preliminary type from inside another one");
        let mut store = host.type_arena[root]
            .preliminary
            .take()
            .unwrap_or_else(|| Box::new(DocStore::staging()));
        mem::swap(&mut host.type_arena, &mut store.type_arena);
        Self {
            host,
            root,
            store: Some(store),
        }
    }
}

impl Deref for Staging<'_> {
    type Target = DocStore;

    fn deref(&self) -> &DocStore {
        self.store.as_deref().expect("held until drop")
    }
}

impl DerefMut for Staging<'_> {
    fn deref_mut(&mut self) -> &mut DocStore {
        self.store.as_deref_mut().expect("held until drop")
    }
}

impl Drop for Staging<'_> {
    fn drop(&mut self) {
        if let Some(mut store) = self.store.take() {
            mem::swap(&mut self.host.type_arena, &mut store.type_arena);
            store.collector = Default::default();
            if let Some(root) = self.host.type_arena.get_mut(self.root) {
                root.preliminary = Some(store);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::hash::BuildHasher;

    use super::*;
    use crate::{Any, Doc, DocOptions, Text};

    // Refcount operations in a complete staging/mount/collect scenario exceed
    // loom's default 1000 branches even without a competing thread.
    fn model(body: fn()) {
        #[cfg(loom)]
        {
            let mut builder = loom::model::Builder::new();
            builder.max_branches = 1 << 20;
            builder.check(move || {
                loom::thread::Builder::new()
                    .stack_size(128 << 10)
                    .spawn(body)
                    .unwrap()
                    .join()
                    .unwrap();
            });
        }
        #[cfg(not(loom))]
        body();
    }

    #[test]
    fn handles_and_types_keep_their_compact_layout() {
        use std::mem::size_of;

        assert_eq!(size_of::<TypeIdx>(), 4);
        assert_eq!(size_of::<Option<TypeIdx>>(), 4);
        #[cfg(target_pointer_width = "64")]
        {
            assert_eq!(size_of::<YTypeRef>(), 16);
            assert_eq!(size_of::<Text>(), 16);
            assert_eq!(size_of::<YType>(), 64);
            assert_eq!(size_of::<Item>(), 128);
            assert_eq!(size_of::<Option<Item>>(), 128);
            assert_eq!(size_of::<SearchMarker>(), 16);
            assert_eq!(size_of::<ItemIdx>(), 4);
            assert_eq!(size_of::<Option<ItemIdx>>(), 4);
            assert_eq!(size_of::<BlockRef>(), 16);
        }

        // the first slot is index 1, and a handle prints only its identity
        let mut types = TypeArena::default();
        let first = types.alloc(YType::default()).unwrap();
        assert_eq!(first.slot(), 0);
        assert_eq!(format!("{first:?}"), "TypeIdx(1)");
        assert!(format!("{:?}", YTypeRef::default()).ends_with("id: None }"));
        assert_eq!(
            TypeIdx::from_slot(u32::MAX as usize - 1).map(TypeIdx::slot),
            Some(u32::MAX as usize - 1)
        );
        assert_eq!(TypeIdx::from_slot(u32::MAX as usize), None);
    }

    #[test]
    fn handles_compare_by_document_and_slot() {
        model(|| {
            let doc = Doc::with_client(1);
            let other = Doc::with_client(2);
            let text = doc.get_or_create_text("text").unwrap();
            let again = doc.get_or_create_text("text").unwrap();
            let foreign = other.get_or_create_text("text").unwrap();
            // the same slot of two documents
            assert_eq!(text.0.id, foreign.0.id);
            assert_eq!(text, again);
            assert_ne!(text, foreign);

            let state = std::collections::hash_map::RandomState::new();
            assert_eq!(state.hash_one(&text.0), state.hash_one(&again.0));

            // formatting a handle neither locks nor reads the store
            doc.transact_mut(None, |_| {
                assert!(format!("{text:?}").contains("YTypeRef"));
                Ok(())
            })
            .unwrap();
        });
    }

    /// What every operation answers in each state of a type's life.
    #[derive(Debug, PartialEq)]
    struct Probe {
        id: Option<Id>,
        identity: JwstCodecResult<TypeIdentity>,
        len: u64,
        write: JwstCodecResult,
        insert_again: JwstCodecResult,
        staging_root: JwstCodecResult<Option<TypeIdx>>,
        carrier: &'static str,
        parent: Option<TypeIdx>,
    }

    /// Probes `array`. `write` appends a value when it succeeds; `len` is read
    /// before it.
    fn probe(doc: &Doc, array: &Array, sink: &Array) -> Probe {
        let id = array.id();
        let identity = array.identity();
        let len = array.len();
        let write = array.clone().push(0);
        let insert_again = sink.clone().push(array.clone());
        let store = doc.store.read().unwrap();
        let idx = array.0.id.unwrap();
        let ty = &store.type_arena[idx];
        Probe {
            id,
            identity,
            len,
            write,
            insert_again,
            staging_root: store.type_arena.preliminary_root(idx),
            carrier: match ty.carrier(&store.type_arena.items) {
                Carrier::Unset => "unset",
                Carrier::Live(item) if item.deleted() => "deleted",
                Carrier::Live(_) => "live",
                Carrier::Retired => "retired",
            },
            parent: store.type_arena.parent_of(idx),
        }
    }

    #[test]
    fn type_lifecycle_truth_table() {
        model(|| {
            let doc = DocOptions::new().with_client_id(1).auto_gc(false).build();
            let mut root = doc.get_or_create_array("root").unwrap();
            let sink = doc.get_or_create_array("sink").unwrap();
            let root_idx = root.0.id.unwrap();

            // a named root: published from the start, never carried
            assert_eq!(
                probe(&doc, &root, &sink),
                Probe {
                    id: None,
                    identity: Ok(TypeIdentity::Root("root".into())),
                    len: 0,
                    write: Ok(()),
                    insert_again: Err(JwstCodecError::TypeAlreadyInserted),
                    staging_root: Ok(None),
                    carrier: "unset",
                    parent: None,
                }
            );

            // preliminary: a root of its own subtree, and a type nested in it
            let mut outer = doc.create_array().unwrap();
            let mut inner = doc.create_array().unwrap();
            let (outer_idx, inner_idx) = (outer.0.id.unwrap(), inner.0.id.unwrap());
            inner.push(1).unwrap();
            outer.push(inner.clone()).unwrap();
            let state = doc.get_state_vector();
            assert_eq!(
                probe(&doc, &inner, &sink),
                Probe {
                    id: None,
                    identity: Err(JwstCodecError::InvalidParent),
                    len: 1,
                    write: Ok(()),
                    insert_again: Err(JwstCodecError::TypeAlreadyInserted),
                    staging_root: Ok(Some(outer_idx)),
                    carrier: "live",
                    parent: Some(outer_idx),
                }
            );
            // nothing of the subtree reached the document
            assert_eq!(doc.get_state_vector(), state);
            assert_eq!(
                (outer.id(), outer.identity()),
                (None, Err(JwstCodecError::InvalidParent))
            );
            assert_eq!(outer.len(), 1);
            {
                let store = doc.store.read().unwrap();
                let ty = &store.type_arena[outer_idx];
                assert!(matches!(ty.carrier(&store.type_arena.items), Carrier::Unset));
                assert_eq!(store.type_arena.preliminary_root(outer_idx), Ok(Some(outer_idx)));
            }
            let types = doc.store.read().unwrap().type_arena.len();

            // published: mounted with its subtree, slots unchanged
            root.push(outer.clone()).unwrap();
            let outer_id = Id::new(1, 1);
            let inner_id = Id::new(1, 2);
            assert_eq!(
                probe(&doc, &outer, &sink),
                Probe {
                    id: Some(outer_id),
                    identity: Ok(TypeIdentity::Item(outer_id)),
                    len: 1,
                    write: Ok(()),
                    insert_again: Err(JwstCodecError::TypeAlreadyInserted),
                    staging_root: Ok(None),
                    carrier: "live",
                    parent: Some(root_idx),
                }
            );
            assert_eq!(
                probe(&doc, &inner, &sink),
                Probe {
                    id: Some(inner_id),
                    identity: Ok(TypeIdentity::Item(inner_id)),
                    len: 2,
                    write: Ok(()),
                    insert_again: Err(JwstCodecError::TypeAlreadyInserted),
                    staging_root: Ok(None),
                    carrier: "live",
                    parent: Some(outer_idx),
                }
            );
            assert_eq!(doc.store.read().unwrap().type_arena.len(), types);
            assert_eq!((outer.0.id, inner.0.id), (Some(outer_idx), Some(inner_idx)));

            // deleted, not collected: the identity stays, writes are refused
            root.remove(0, 2).unwrap();
            for (array, id, parent) in [(&outer, outer_id, root_idx), (&inner, inner_id, outer_idx)] {
                assert_eq!(
                    probe(&doc, array, &sink),
                    Probe {
                        id: Some(id),
                        identity: Ok(TypeIdentity::Item(id)),
                        len: 0,
                        write: Err(JwstCodecError::InvalidParent),
                        insert_again: Err(JwstCodecError::TypeAlreadyInserted),
                        staging_root: Err(JwstCodecError::InvalidParent),
                        carrier: "deleted",
                        parent: Some(parent),
                    }
                );
            }

            // collected: the carrier of `outer` keeps its place as deleted
            // content (its parent is not collected) and is merged into its
            // left neighbor, the carrier of `inner` becomes a GC struct
            doc.gc().unwrap();
            {
                let store = doc.store.read().unwrap();
                let merged = store.get_node(outer_id).unwrap();
                assert_eq!((merged.id(), merged.len()), (Id::new(1, 0), 2));
                assert!(merged.is_item());
                assert!(store.get_node(inner_id).unwrap().is_gc());
                assert_eq!(store.type_arena.len(), types);
            }
            for array in [&outer, &inner] {
                assert_eq!(
                    probe(&doc, array, &sink),
                    Probe {
                        id: None,
                        identity: Err(JwstCodecError::InvalidParent),
                        len: 0,
                        write: Err(JwstCodecError::InvalidParent),
                        insert_again: Err(JwstCodecError::TypeAlreadyInserted),
                        staging_root: Err(JwstCodecError::InvalidParent),
                        carrier: "retired",
                        parent: None,
                    }
                );
                assert_eq!(array.get(0), None);
                assert_eq!(array.iter().count(), 0);
            }

            // the document is gone: reads fall back, writes say so
            let released = doc.get_or_create_text("text").unwrap();
            drop((doc, root, sink));
            assert_eq!((released.len(), released.to_string()), (0, String::new()));
            assert_eq!(released.identity(), Err(JwstCodecError::DocReleased));
            assert_eq!(released.clone().insert(0, "a"), Err(JwstCodecError::DocReleased));
            assert_eq!(outer.clone().push(1), Err(JwstCodecError::DocReleased));
        });
    }

    #[test]
    fn remote_type_under_a_collected_parent_leaves_no_slot() {
        model(|| {
            let source = DocOptions::new().with_client_id(1).auto_gc(false).build();
            let mut root = source.get_or_create_map("root").unwrap();
            let mut nested = source.create_map().unwrap();
            root.insert("nested".into(), nested.clone()).unwrap();

            let mut target = Doc::with_client(2);
            target
                .apply_update_from_binary_v1(source.encode_update_v1().unwrap())
                .unwrap();
            // the root and the nested map decoded from the update
            assert_eq!(target.store.read().unwrap().type_arena.len(), 2);
            let state = target.get_state_vector();

            target.get_or_create_map("root").unwrap().remove("nested");
            target.gc().unwrap();

            // the source, unaware, nests two more types in the map
            nested.insert("text".into(), source.create_text().unwrap()).unwrap();
            nested.insert("list".into(), source.create_array().unwrap()).unwrap();
            target
                .apply_update_from_binary_v1(source.encode_state_as_update_v1(&state).unwrap())
                .unwrap();

            // their items are kept as GC structs and their types are not
            assert!(!target.has_pending_updates());
            assert_eq!(target.get_state_vector().get(&1), 3);
            let store = target.store.read().unwrap();
            assert_eq!(store.type_arena.len(), 2);
            assert!(store.get_node((1, 1)).unwrap().is_gc());
        });
    }

    #[test]
    #[cfg(not(loom))]
    fn an_edit_that_panics_returns_the_arena_and_the_staging_store() {
        let doc = Doc::with_client(1);
        let mut child = doc.create_array().unwrap();
        child.push(1).unwrap();
        let types = doc.store.read().unwrap().type_arena.len();
        let handle = child.0.clone();

        let edit = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = handle.write(|staging, _| -> JwstCodecResult {
                // the staging store sees every type of the document
                assert_eq!(staging.type_arena.len(), types);
                assert_eq!(staging.items.len(), 1);
                panic!("the edit fails");
            });
        }));
        assert!(edit.is_err());

        // the lock is poisoned, the store is whole
        let store = doc.store.write().unwrap_or_else(|poisoned| poisoned.into_inner());
        assert_eq!(store.type_arena.len(), types);
        let staging = store.type_arena[handle.id.unwrap()].preliminary.as_deref().unwrap();
        assert_eq!((staging.type_arena.len(), staging.items.len()), (0, 1));
    }

    #[test]
    fn a_preliminary_tree_is_rebuilt_in_place_when_mounted() {
        model(|| {
            let doc = Doc::with_client(7);
            let mut outer = doc.create_map().unwrap();
            let mut list = doc.create_array().unwrap();
            list.push("a").unwrap();
            // a subtree with staged edits of its own joins another one
            outer.insert("list".into(), list.clone()).unwrap();
            list.push("b").unwrap();
            let types = doc.store.read().unwrap().type_arena.len();
            {
                let store = doc.store.read().unwrap();
                let (outer_idx, list_idx) = (outer.0.id.unwrap(), list.0.id.unwrap());
                // one staging store per unmounted tree, in its root
                assert!(store.type_arena[outer_idx].preliminary.is_some());
                assert!(store.type_arena[list_idx].preliminary.is_none());
                assert_eq!(store.type_arena.preliminary_root(list_idx), Ok(Some(outer_idx)));
            }

            doc.get_or_create_map("root")
                .unwrap()
                .insert("outer".into(), outer.clone())
                .unwrap();
            let store = doc.store.read().unwrap();
            // the root was added; the mounted types kept their slots
            assert_eq!(store.type_arena.len(), types + 1);
            for ty in [&outer.0, &list.0] {
                let ty = &store.type_arena[ty.id.unwrap()];
                assert!(ty.published && ty.preliminary.is_none());
                assert!(matches!(ty.carrier(&store.type_arena.items), Carrier::Live(item) if !item.deleted()));
            }
            drop(store);
            assert_eq!(list.get(1), Some(Value::Any(Any::String("b".into()))));
            assert_eq!(doc.get_state_vector().get(&7), 4);
        });
    }

    #[test]
    fn the_arena_refuses_types_past_its_capacity() {
        let mut types = TypeArena::default();
        types.set_limit(Some(2));
        assert_eq!(types.check_capacity(2), Ok(()));
        assert!(types.check_capacity(3).is_err());
        types.alloc(YType::default()).unwrap();
        types.alloc(YType::default()).unwrap();
        assert_eq!(types.check_capacity(0), Ok(()));
        assert!(matches!(
            types.alloc(YType::default()),
            Err(JwstCodecError::IncompleteDocument(_))
        ));
        assert_eq!(types.len(), 2);
        // without a test limit the capacity is what an index can address
        assert_eq!(TypeArena::default().check_capacity(u32::MAX as usize), Ok(()));
        #[cfg(target_pointer_width = "64")]
        assert!(TypeArena::default().check_capacity(u32::MAX as usize + 1).is_err());
    }

    #[test]
    fn a_preliminary_edit_leaves_no_collected_changes_behind() {
        model(|| {
            let doc = Doc::with_client(1);
            let mut child = doc.create_array().unwrap();
            child.push(1).unwrap();
            child.push(doc.create_map().unwrap()).unwrap();
            child.remove(0, 2).unwrap();
            let store = doc.store.read().unwrap();
            let staging = store.type_arena[child.0.id.unwrap()].preliminary.as_deref().unwrap();
            assert!(staging.staging && !store.staging);
            assert!(staging.collector.is_empty());
            assert!(store.collector.is_empty());
        });
    }

    #[test]
    #[cfg(all(debug_assertions, not(loom)))]
    fn an_edit_of_a_preliminary_type_does_not_nest() {
        let doc = Doc::with_client(1);
        let child = doc.create_array().unwrap();
        let handle = child.0.clone();
        let nested = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = handle.write(|staging, id| staging.edit_type(id, |_, _| Ok(())));
        }));
        assert!(nested.is_err());
    }

    /// A type of another document is refused by every write that takes a
    /// value, also when it sits in the slot the parent has in its own
    /// document, and nothing is written.
    #[test]
    fn every_write_refuses_a_type_of_another_document() {
        model(|| {
            let doc = Doc::with_client(1);
            let other = Doc::with_client(2);
            let mut array = doc.get_or_create_array("array").unwrap();
            let mut map = doc.get_or_create_map("map").unwrap();
            let mut fragment = doc.get_or_create_xml_fragment("fragment").unwrap();
            let mut element = doc.get_or_create_xml_element("element").unwrap();
            let mut hook = doc.get_or_create_xml_hook("hook").unwrap();
            // the other document fills the same slots, 1 to 5
            let foreign = (0..5).map(|_| other.create_map().unwrap()).collect::<Vec<_>>();
            let same_slot = |parent: &YTypeRef| {
                let twin = foreign.iter().find(|twin| twin.0.id == parent.id).unwrap();
                assert_ne!(&twin.0, parent);
                twin.clone()
            };
            let before = doc.encode_update_v1().unwrap();
            let refused = Err(JwstCodecError::ForeignType);

            let twin = same_slot(&array.0);
            assert_eq!(array.push(twin.clone()), refused);
            assert_eq!(array.insert(0, twin.clone()), refused);
            // the index is still checked first
            assert_eq!(array.insert(1, twin.clone()), Err(JwstCodecError::IndexOutOfBound(1)));
            assert_eq!(
                doc.transact_mut(None, |tx| tx.array(&array)?.push(twin.clone())),
                refused
            );
            assert_eq!(
                doc.transact_mut(None, |tx| tx.array(&array)?.insert(0, twin.clone())),
                refused
            );

            let twin = same_slot(&map.0);
            assert_eq!(map.insert("k".into(), twin.clone()), refused);
            assert_eq!(
                doc.transact_mut(None, |tx| tx.map(&map)?.insert("k".into(), twin.clone())),
                refused
            );

            let twin = same_slot(&fragment.0);
            assert_eq!(fragment.push(twin.clone()), refused);
            assert_eq!(fragment.insert(0, twin.clone()), refused);
            assert_eq!(
                doc.transact_mut(None, |tx| tx.xml_fragment(&fragment)?.push(twin.clone())),
                refused
            );
            assert_eq!(
                doc.transact_mut(None, |tx| tx.xml_fragment(&fragment)?.insert(0, twin.clone())),
                refused
            );

            let twin = same_slot(&element.0);
            assert_eq!(element.push(twin.clone()), refused);
            assert_eq!(element.insert(0, twin.clone()), refused);
            assert_eq!(element.set_attribute("k", twin.clone()), refused);
            assert_eq!(
                doc.transact_mut(None, |tx| tx.xml_element(&element)?.push(twin.clone())),
                refused
            );
            assert_eq!(
                doc.transact_mut(None, |tx| tx.xml_element(&element)?.insert(0, twin.clone())),
                refused
            );
            assert_eq!(
                doc.transact_mut(None, |tx| tx.xml_element(&element)?.set_attribute("k", twin.clone())),
                refused
            );

            let twin = same_slot(&hook.0);
            assert_eq!(hook.insert("k".into(), twin.clone()), refused);
            assert_eq!(
                doc.transact_mut(None, |tx| tx.xml_hook(&hook)?.insert("k".into(), twin.clone())),
                refused
            );

            // nothing reached the document, and every type is still free to
            // be inserted where it belongs
            assert_eq!(doc.encode_update_v1().unwrap(), before);
            assert!(doc.get_state_vector().is_empty());
            assert_eq!(doc.store.read().unwrap().type_arena.len(), 5);
            let mut home = other.get_or_create_array("home").unwrap();
            for twin in foreign {
                home.push(twin).unwrap();
            }
            assert_eq!(home.len(), 5);
        });
    }

    /// The walk [TypeArena::is_above] replaced: every type it met is kept
    /// in a set.
    fn above_with_a_set(types: &TypeArena, inner: TypeIdx, ty: TypeIdx) -> bool {
        let mut visited = HashSet::new();
        let mut ancestor = types.parent_of(ty);
        while let Some(current) = ancestor {
            if !visited.insert(current) {
                break;
            }
            if current == inner {
                return true;
            }
            ancestor = types.parent_of(current);
        }
        false
    }

    /// An arena whose type `at` is carried by an item of the type
    /// `parents[at]`, whatever loops that makes.
    fn arena_of(parents: &[Option<usize>]) -> (TypeArena, Vec<TypeIdx>) {
        let mut types = TypeArena::default();
        let ids: Vec<TypeIdx> = parents.iter().map(|_| types.alloc(YType::default()).unwrap()).collect();
        for (at, parent) in parents.iter().enumerate() {
            if let Some(parent) = parent {
                let carrier = types
                    .items
                    .alloc(Item {
                        content: Content::Type(ids[at]),
                        parent: Some(ids[*parent]),
                        ..Item::default()
                    })
                    .unwrap();
                types[ids[at]].attach(Some(carrier), Some(ids[*parent]));
            }
        }
        (types, ids)
    }

    #[test]
    fn a_type_above_another_is_found_however_deep_and_without_a_set() {
        // a chain: every type is in the one before it
        let depth = if cfg!(miri) { 200 } else { 3_000 };
        let parents: Vec<Option<usize>> = (0..depth).map(|at: usize| at.checked_sub(1)).collect();
        let (types, ids) = arena_of(&parents);
        let leaf = ids[depth - 1];
        for above in [0, 1, depth / 2, depth - 2] {
            assert!(types.is_above(ids[above], leaf), "type {above}");
            assert!(!types.is_above(leaf, ids[above]), "type {above}");
        }
        // a type is not above itself, and nothing is above a root
        assert!(!types.is_above(leaf, leaf));
        assert!(!types.is_above(ids[0], ids[0]));
        assert!(!types.is_above(ids[1], ids[0]));
        // a type that is no type of the arena has no parent and is above none
        let (other, foreign) = arena_of(&vec![None; depth + 1]);
        assert_eq!(other.len(), depth + 1);
        assert!(!types.is_above(ids[0], foreign[depth]));
        assert!(!types.is_above(foreign[depth], leaf));
    }

    #[test]
    fn the_walk_above_a_type_ends_on_loops_that_are_there_already() {
        // 0 holds itself, 1 is in it
        let (types, ids) = arena_of(&[Some(0), Some(0), None]);
        assert!(types.is_above(ids[0], ids[0]));
        assert!(types.is_above(ids[0], ids[1]));
        assert!(!types.is_above(ids[1], ids[0]));
        assert!(!types.is_above(ids[2], ids[1]));
        // 4 → 3 → 2 → 1 → 3: a loop of three types above a type outside it
        let (types, ids) = arena_of(&[None, Some(3), Some(1), Some(2), Some(3)]);
        for inner in [1, 2, 3] {
            assert!(types.is_above(ids[inner], ids[4]), "in the loop: {inner}");
        }
        // a type outside the loop is not found, and the walk ends
        assert!(!types.is_above(ids[0], ids[4]));
        assert!(!types.is_above(ids[4], ids[4]));
        assert!(!types.is_above(ids[4], ids[2]));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn the_walk_above_a_type_agrees_with_the_walk_that_keeps_a_set() {
        // every graph of parent links over up to four types, every pair
        for count in 0..=4usize {
            let mut graph = vec![0usize; count];
            loop {
                let parents: Vec<Option<usize>> = graph.iter().map(|&choice| choice.checked_sub(1)).collect();
                let (types, ids) = arena_of(&parents);
                for inner in &ids {
                    for ty in &ids {
                        assert_eq!(
                            types.is_above(*inner, *ty),
                            above_with_a_set(&types, *inner, *ty),
                            "{parents:?} {inner:?} above {ty:?}"
                        );
                    }
                }
                let mut at = 0;
                while at < count {
                    graph[at] += 1;
                    if graph[at] <= count {
                        break;
                    }
                    graph[at] = 0;
                    at += 1;
                }
                if at == count {
                    break;
                }
            }
        }
        // random graphs of a few hundred types
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut below = move |n: usize| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state % n as u64) as usize
        };
        for _ in 0..60 {
            let count = 1 + below(300);
            let parents: Vec<Option<usize>> = (0..count)
                .map(|_| match below(10) {
                    0 => None,
                    _ => Some(below(count)),
                })
                .collect();
            let (types, ids) = arena_of(&parents);
            for _ in 0..200 {
                let (inner, ty) = (ids[below(count)], ids[below(count)]);
                assert_eq!(
                    types.is_above(inner, ty),
                    above_with_a_set(&types, inner, ty),
                    "{parents:?} {inner:?} above {ty:?}"
                );
            }
        }
    }
}
