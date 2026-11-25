mod search_marker;

pub(crate) use search_marker::{MarkerList, SearchMarker};

use super::*;

#[derive(Debug)]
pub(crate) struct ItemPosition {
    pub left: ItemRef,
    pub right: ItemRef,
    pub index: u64,
    pub offset: u64,
}

impl ItemPosition {
    pub fn forward(&mut self, items: &ItemSpace) {
        if let Some(right) = self.right.and_then(|i| items.get(i)) {
            if right.indexable() {
                self.index += right.len();
            }

            self.left = self.right;
            self.right = right.right;
        } else {
            // FAIL
        }
    }

    /// we found a position cursor point in between a splitable item,
    /// we need to split the item by the offset.
    ///
    /// before:
    /// ---------------------------------
    ///    ^left                ^right
    ///            ^offset
    /// after:
    /// ---------------------------------
    ///    ^left   ^right
    pub fn normalize(&mut self, store: &mut DocStore) -> JwstCodecResult {
        if self.offset > 0 {
            debug_assert!(self.left.is_some());
            if let Some(left) = self.left.and_then(|i| store.type_arena.items.get(i)) {
                let (left, right) = store.split_node(left.id, self.offset)?;
                self.left = left.as_item();
                self.right = right.as_item();
                self.index += self.offset;
                self.offset = 0;
            }
        }

        Ok(())
    }
}

/// Read-only walk over the visible (not deleted) items of a list type. It
/// borrows the [YType], so it can only live while the store lock is held.
pub(crate) struct ListIterator<'a> {
    cur: ItemRef,
    items: &'a ItemSpace,
}

impl<'a> ListIterator<'a> {
    pub fn new(items: &'a ItemSpace, ty: &YType) -> Self {
        Self { cur: ty.start, items }
    }
}

impl<'a> Iterator for ListIterator<'a> {
    type Item = &'a Item;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.cur.and_then(|i| self.items.get(i)) {
            self.cur = item.right;
            if !item.deleted() {
                return Some(item);
            }
        }

        None
    }
}

/// Finds the position of `index` for a reader holding the store read lock:
/// search markers are used but not updated.
pub(crate) fn find_pos(items: &ItemSpace, ty: &YType, index: u64) -> Option<ItemPosition> {
    let marker = ty
        .markers
        .as_ref()
        .and_then(|m| m.find_readonly(items, &ty.start, index));
    find_pos_from(items, ty, index, marker)
}

/// Finds the position of `index` for a writer holding the store write lock,
/// updating the search markers on the way.
pub(crate) fn find_pos_mut(items: &ItemSpace, ty: &mut YType, index: u64) -> Option<ItemPosition> {
    let (start, len) = (ty.start, ty.len);
    let marker = ty
        .markers
        .as_mut()
        .and_then(|m| m.find_marker(items, &start, len, index));
    find_pos_from(items, ty, index, marker)
}

fn find_pos_from(items: &ItemSpace, ty: &YType, index: u64, marker: Option<SearchMarker>) -> Option<ItemPosition> {
    let mut remaining = index;

    let mut pos = ItemPosition {
        left: None,
        right: ty.start,
        index: 0,
        offset: 0,
    };

    if pos.right.is_none() {
        return Some(pos);
    }

    if let Some(marker) = marker {
        if marker.index > remaining {
            remaining = 0
        } else {
            remaining -= marker.index;
        }
        pos.index = marker.index;
        pos.left = marker
            .ptr
            .and_then(|i| items.get(i))
            .map(|ptr| ptr.left)
            .unwrap_or_default();
        pos.right = marker.ptr;
    };

    // avoid the first item of the list being deleted
    if pos.left.is_none() {
        while let Some(item) = pos.right.and_then(|i| items.get(i)) {
            if item.deleted() {
                pos.left = pos.right;
                pos.right = item.right;
                continue;
            } else {
                break;
            }
        }
    } else if remaining == 0 {
        // Keep marker-accelerated positions identical to a scan from
        // `ty.start`: back up over any non-indexable items (tombstones and
        // live `Format` markers) so `pos` lands right after the preceding live
        // indexable item.
        while let Some(left) = pos.left.and_then(|i| items.get(i)) {
            if !left.indexable() && left.left.is_some() {
                pos.right = pos.left;
                pos.left = left.left;
            } else {
                break;
            }
        }
    }

    while remaining > 0 {
        let item = pos.right.and_then(|i| items.get(i))?;
        if item.indexable() {
            let content_len = item.len();
            if remaining < content_len {
                pos.offset = remaining;
                remaining = 0;
            } else {
                pos.index += content_len;
                remaining -= content_len;
            }
        }

        pos.left = pos.right;
        pos.right = item.right;
    }

    Some(pos)
}

/// The item covering `index` and the offset of `index` inside it. The caller
/// holds the store lock while it uses the returned item.
pub(crate) fn item_at(items: &ItemSpace, ty: &YType, index: u64) -> Option<(ItemRef, u64)> {
    if index >= ty.len {
        return None;
    }

    let pos = find_pos(items, ty, index)?;
    if pos.offset != 0 {
        return Some((pos.left, pos.offset));
    }

    // An insertion cursor can stop at a tombstone. A read needs the next
    // visible value.
    let mut item = pos.right;
    while let Some(candidate) = item.and_then(|i| items.get(i)) {
        if candidate.indexable() {
            return Some((item, 0));
        }
        item = candidate.right;
    }
    None
}

pub(crate) trait ListType: AsInner<Inner = YTypeRef> {
    #[inline(always)]
    fn _id(&self) -> Option<Id> {
        or_released(self.as_inner().read(|store, ty| ty.id(&store.type_arena.items)))
    }

    #[inline(always)]
    fn content_len(&self) -> u64 {
        or_released(self.as_inner().read(|_, ty| ty.len))
    }

    fn insert_at(&mut self, index: u64, content: impl Into<NewContent>) -> JwstCodecResult {
        let content = content.into();
        self.as_inner()
            .write(|store, ty| list_insert(store, ty, index, content))
    }

    /// [ListType::insert_at] for a value given by a caller.
    fn insert_value_at(&mut self, index: u64, value: Value) -> JwstCodecResult {
        let content = NewContent::from_value(value, &self.as_inner().store);
        self.insert_at(index, content)
    }

    /// Appends a value given by a caller.
    fn push_value(&mut self, value: Value) -> JwstCodecResult {
        let content = NewContent::from_value(value, &self.as_inner().store);
        self.as_inner().write(|store, ty| {
            if store.type_arena[ty].kind() == YTypeKind::Array {
                list_push(store, ty, content)
            } else {
                let len = store.type_arena[ty].len;
                list_insert(store, ty, len, content)
            }
        })
    }

    fn remove_at(&mut self, idx: u64, len: u64) -> JwstCodecResult {
        self.as_inner().write(|store, ty| list_remove(store, ty, idx, len))
    }
}

/// Appends `content` to the physical end of the list type `ty` of `store`,
/// advancing past any trailing tombstones (matching Yjs
/// `typeListPushGenerics`). The caller holds the store write lock.
pub(crate) fn list_push(store: &mut DocStore, ty: TypeIdx, content: impl Into<NewContent>) -> JwstCodecResult {
    let len = store.type_arena[ty].len;
    list_insert_inner(store, ty, len, content.into(), true)
}

/// Inserts `content` at `index` of the list type `ty` of `store`. The caller
/// holds the store write lock.
pub(crate) fn list_insert(
    store: &mut DocStore,
    ty: TypeIdx,
    index: u64,
    content: impl Into<NewContent>,
) -> JwstCodecResult {
    list_insert_inner(store, ty, index, content.into(), false)
}

/// Inserts `content` at `index` of the list type `ty` of `store`, advancing
/// past any deleted tombstones at the cursor when `skip_tombstones` is `true`
/// (matching Yjs `YText` insertion semantics).
pub(crate) fn list_insert_inner(
    store: &mut DocStore,
    ty: TypeIdx,
    index: u64,
    content: NewContent,
    skip_tombstones: bool,
) -> JwstCodecResult {
    if index > store.type_arena[ty].len {
        return Err(JwstCodecError::IndexOutOfBound(index));
    }
    if matches!(&content, NewContent::Local(Content::String(text)) if text.is_empty()) {
        return Ok(());
    }
    let content = check_insertable(&store.type_arena, ty, content)?;

    let (parent, items) = store.type_arena.type_and_items(ty);
    if let Some(mut pos) = find_pos_mut(items, parent, index) {
        if skip_tombstones && pos.offset == 0 {
            while let Some(item) = pos.right.and_then(|i| items.get(i)) {
                if item.deleted() {
                    pos.left = pos.right;
                    pos.right = item.right;
                } else {
                    break;
                }
            }
        }
        // inside a struct: `normalize` cuts it there
        let split = if pos.offset > 0 {
            pos.left
                .and_then(|left| items.get(left))
                .map(|left| left.id + pos.offset)
        } else {
            None
        };
        store.check_local_insert(&content, split)?;
        pos.normalize(store)?;
        insert_after(store, ty, pos, content)?;
    }

    Ok(())
}

fn insert_after(store: &mut DocStore, ty: TypeIdx, pos: ItemPosition, content: Content) -> JwstCodecResult {
    let item = store.create_item(content, pos.left, pos.right, Some(ty), None);
    let countable = item.countable();
    let clock_len = item.len();

    let inserted = store.integrate_item(item, 0, Some(ty))?;
    let (parent, items) = store.type_arena.type_and_items(ty);
    if let Some(markers) = &mut parent.markers
        && countable
    {
        markers.update_marker_changes(items, pos.index, clock_len as i64, inserted);
    }

    Ok(())
}

/// Removes `len` elements from `idx` of the list type `ty` of `store`. The
/// caller holds the store write lock.
pub(crate) fn list_remove(store: &mut DocStore, ty: TypeIdx, idx: u64, len: u64) -> JwstCodecResult {
    let ty_len = store.type_arena[ty].len;
    if len == 0 || ty_len == 0 {
        return Ok(());
    }

    if idx >= ty_len {
        return Err(JwstCodecError::IndexOutOfBound(idx));
    }

    let (parent, items) = store.type_arena.type_and_items(ty);
    if let Some(pos) = find_pos_mut(items, parent, idx) {
        remove_after(store, ty, pos, len)?;
    }

    Ok(())
}

/// Whether the document takes the cuts a removal of `len` units makes: one
/// where it starts, `skip` units into the item `first` (`start_cut`, when
/// `skip > 0`), and one where it ends inside an item. A removal deletes the
/// items before its end as it goes, so both cuts have to fit before the first
/// is made: a full arena or timeline refuses the removal and nothing is
/// deleted.
pub(crate) fn check_remove(
    store: &DocStore,
    first: ItemRef,
    skip: u64,
    len: u64,
    start_cut: Option<Id>,
) -> JwstCodecResult {
    let items = &store.type_arena.items;
    if items.check_capacity(2).is_ok() && store.blocks_fit(2) {
        return Ok(());
    }
    let mut end_cut = None;
    let mut cursor = first;
    let mut skip = skip;
    let mut remaining = len;
    while remaining > 0 {
        let Some(item) = cursor.and_then(|i| items.get(i)) else {
            break;
        };
        if item.indexable() {
            let item_len = item.len() - std::mem::take(&mut skip);
            if remaining < item_len {
                end_cut = Some(item.id + (item.len() - item_len + remaining));
                break;
            }
            remaining -= item_len;
        }
        skip = 0;
        cursor = item.right;
    }
    items.check_capacity(usize::from(start_cut.is_some()) + usize::from(end_cut.is_some()))?;
    store.check_blocks(store.client(), 0, &[start_cut, end_cut])
}

fn remove_after(store: &mut DocStore, ty: TypeIdx, mut pos: ItemPosition, len: u64) -> JwstCodecResult {
    {
        let items = &store.type_arena.items;
        let inside = pos.left.filter(|_| pos.offset > 0);
        let start_cut = inside.and_then(|left| items.get(left)).map(|left| left.id + pos.offset);
        check_remove(store, inside.or(pos.right), pos.offset, len, start_cut)?;
    }
    pos.normalize(store)?;

    let mut remaining = len;

    while remaining > 0 {
        let item_ref = pos.right;
        let Some((indexable, content_len, item_id)) = item_ref
            .and_then(|i| store.type_arena.items.get(i))
            .map(|item| (item.indexable(), item.len(), item.id))
        else {
            break;
        };

        if indexable {
            if remaining < content_len {
                store.split_node(item_id, remaining)?;
                remaining = 0;
            } else {
                remaining -= content_len;
            }

            if let Some(item) = item_ref {
                store.delete_item(item, Some(ty));
            }
        }

        pos.forward(&store.type_arena.items);
    }

    let (parent, items) = store.type_arena.type_and_items(ty);
    if let Some(markers) = &mut parent.markers {
        markers.update_marker_changes(items, pos.index, -((len - remaining) as i64), None);
    }

    Ok(())
}

/// Checks a value inserted under the type `parent` of the arena `types` and
/// returns its content: a type can only be inserted into the document it was
/// created in (an item holds the slot of its type in that document's arena),
/// only once in its life, and never into itself or its descendants.
///
/// Inserting a type at most once (as in Yjs) keeps its carrier, and so its
/// ancestor chain, fixed; with that, the ancestor walk below rejects every
/// cycle, and the type tree stays acyclic, which
/// `DocStore::delete_item_inner` relies on.
/// The caller holds the store write lock.
pub(crate) fn check_insertable(types: &TypeArena, parent: TypeIdx, content: NewContent) -> JwstCodecResult<Content> {
    let content = match content {
        NewContent::Local(content) => content,
        NewContent::Foreign => return Err(JwstCodecError::ForeignType),
    };
    let Content::Type(value) = &content else {
        return Ok(content);
    };
    let value = *value;

    if value == parent {
        return Err(JwstCodecError::InvalidParent);
    }

    // A root type, or one inserted before (its item may since have been
    // deleted or collected, but the type is never fresh again).
    if types
        .get(value)
        .is_none_or(|value| !matches!(value.carrier(&types.items), Carrier::Unset) || value.root_name().is_some())
    {
        return Err(JwstCodecError::TypeAlreadyInserted);
    }

    let mut ancestor = types.parent_of(parent);
    while let Some(current) = ancestor {
        if current == value {
            return Err(JwstCodecError::InvalidParent);
        }
        ancestor = types.parent_of(current);
    }

    Ok(content)
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use crate::{Any, Doc, Id};

    fn sync_docs(from: &Doc, to: &mut Doc) {
        let sv = to.get_state_vector();
        let update = from.encode_state_as_update_v1(&sv).unwrap();
        to.apply_update_from_binary_v1(update).unwrap();
    }

    #[test]
    fn concurrent_push_after_trailing_tombstone_matches_yjs() {
        let run_case = |push_x: fn(&Doc, &mut Array), push_y: fn(&Doc, &mut Array)| {
            let mut d9 = Doc::with_client(9);
            let mut d2 = Doc::with_client(2);
            let mut a9 = d9.get_or_create_array("a").unwrap();
            let mut a2 = d2.get_or_create_array("a").unwrap();

            a9.push("A").unwrap(); // (9, 0)
            d9.get_or_create_map("other").unwrap().insert("k".into(), 1).unwrap(); // (9, 1)
            a9.push("B").unwrap(); // (9, 2)
            sync_docs(&d9, &mut d2);

            a9.remove(1, 1).unwrap(); // delete B -> trailing tombstone at (9, 2)
            push_x(&d9, &mut a9); // X should anchor at (B=(9,2), None)
            push_y(&d2, &mut a2);

            {
                let store = d9.store.read().unwrap();
                let x_item = store.get_node(Id::new(9, 3)).unwrap().item(&store.type_arena);
                assert_eq!(x_item.origin_left_id(), Some(Id::new(9, 2)));
                assert_eq!(x_item.origin_right_id(), None);
            }

            sync_docs(&d9, &mut d2);
            sync_docs(&d2, &mut d9);

            let expected = vec![Any::from("A"), Any::from("Y"), Any::from("X")];
            let v9: Vec<Any> = a9.iter().map(|v| v.to_any().unwrap()).collect();
            let v2: Vec<Any> = a2.iter().map(|v| v.to_any().unwrap()).collect();
            assert_eq!(v9, expected);
            assert_eq!(v2, expected);
        };

        // 1. Array::push
        run_case(|_, a| a.push("X").unwrap(), |_, a| a.push("Y").unwrap());

        // 2. ArrayWrite::push
        run_case(
            |d, a| d.transact_mut(None, |tx| tx.array(a)?.push("X")).unwrap(),
            |d, a| d.transact_mut(None, |tx| tx.array(a)?.push("Y")).unwrap(),
        );

        // 3. DocSession::array_push
        #[cfg(feature = "session")]
        {
            let mut s9 = crate::DocSession::<()>::new(crate::DocOptions::new().with_client_id(9), 500);
            let mut s2 = crate::DocSession::<()>::new(crate::DocOptions::new().with_client_id(2), 500);
            let a9: crate::TypeTarget = s9.ensure_root("a", YTypeKind::Array).unwrap().into();
            let other9: crate::TypeTarget = s9.ensure_root("other", YTypeKind::Map).unwrap().into();
            let a2: crate::TypeTarget = s2.ensure_root("a", YTypeKind::Array).unwrap().into();

            s9.array_push(&a9, vec![crate::SessionValue::Any(Any::from("A"))])
                .unwrap();
            s9.map_set(&other9, "k".into(), crate::SessionValue::Any(Any::from(1)))
                .unwrap();
            s9.array_push(&a9, vec![crate::SessionValue::Any(Any::from("B"))])
                .unwrap();
            let u9 = s9.encode_update_v1().unwrap();
            s2.apply_update_v1(&u9).unwrap();

            s9.array_remove(&a9, 1, 1).unwrap();
            s9.array_push(&a9, vec![crate::SessionValue::Any(Any::from("X"))])
                .unwrap();
            s2.array_push(&a2, vec![crate::SessionValue::Any(Any::from("Y"))])
                .unwrap();

            let mut d9 = s9.into_doc().unwrap();
            let mut d2 = s2.into_doc().unwrap();
            {
                let store = d9.store.read().unwrap();
                let x_item = store.get_node(Id::new(9, 3)).unwrap().item(&store.type_arena);
                assert_eq!(x_item.origin_left_id(), Some(Id::new(9, 2)));
                assert_eq!(x_item.origin_right_id(), None);
            }
            sync_docs(&d9, &mut d2);
            sync_docs(&d2, &mut d9);
            let expected = vec![Any::from("A"), Any::from("Y"), Any::from("X")];
            let v9: Vec<Any> = d9
                .get_or_create_array("a")
                .unwrap()
                .iter()
                .map(|v| v.to_any().unwrap())
                .collect();
            let v2: Vec<Any> = d2
                .get_or_create_array("a")
                .unwrap()
                .iter()
                .map(|v| v.to_any().unwrap())
                .collect();
            assert_eq!(v9, expected);
            assert_eq!(v2, expected);
        }
    }

    #[test]
    fn xml_fragment_insert_preserves_mid_and_leading_tombstone_anchors() {
        let doc = Doc::with_client(1);
        let mut frag = doc.get_or_create_xml_fragment("f").unwrap();
        frag.push(doc.create_xml_element("a").unwrap()).unwrap(); // (1, 0)
        frag.push(doc.create_xml_element("b").unwrap()).unwrap(); // (1, 1)
        frag.push(doc.create_xml_element("c").unwrap()).unwrap(); // (1, 2)

        // Delete middle element (1, 1) and insert at index 1: must anchor
        // before (1, 1)
        frag.remove(1, 1).unwrap();
        frag.insert(1, doc.create_xml_element("mid").unwrap()).unwrap(); // (1, 3)
        {
            let store = doc.store.read().unwrap();
            let mid = store.get_node(Id::new(1, 3)).unwrap().item(&store.type_arena);
            assert_eq!(mid.origin_left_id(), Some(Id::new(1, 0)));
            assert_eq!(mid.origin_right_id(), Some(Id::new(1, 1)));
        }

        // Delete leading element (1, 0) and insert at index 0: skips leading
        // tombstone
        frag.remove(0, 1).unwrap();
        frag.insert(0, doc.create_xml_element("head").unwrap()).unwrap(); // (1, 4)
        {
            let store = doc.store.read().unwrap();
            let head = store.get_node(Id::new(1, 4)).unwrap().item(&store.type_arena);
            assert_eq!(head.origin_left_id(), Some(Id::new(1, 0)));
            assert_eq!(head.origin_right_id(), Some(Id::new(1, 3)));
        }
    }

    #[test]
    fn xml_fragment_and_element_concurrent_push_after_trailing_tombstone_matches_yjs() {
        let check_fragment = |push_x: fn(&Doc, &mut XMLFragment), push_y: fn(&Doc, &mut XMLFragment)| {
            let mut d9 = Doc::with_client(9);
            let mut d2 = Doc::with_client(2);
            let mut f9 = d9.get_or_create_xml_fragment("f").unwrap();
            let mut f2 = d2.get_or_create_xml_fragment("f").unwrap();

            f9.push(d9.create_xml_element("a").unwrap()).unwrap(); // (9, 0)
            f9.push(d9.create_xml_element("b").unwrap()).unwrap(); // (9, 1)
            sync_docs(&d9, &mut d2);

            f9.remove(1, 1).unwrap(); // delete b -> trailing tombstone at (9, 1)
            push_x(&d9, &mut f9); // x at (9, 2), must anchor (a=(9,0), b=(9,1))
            push_y(&d2, &mut f2); // y at (2, 0)

            {
                let store = d9.store.read().unwrap();
                let x_item = store.get_node(Id::new(9, 2)).unwrap().item(&store.type_arena);
                assert_eq!(x_item.origin_left_id(), Some(Id::new(9, 0)));
                assert_eq!(x_item.origin_right_id(), Some(Id::new(9, 1)));
            }

            sync_docs(&d9, &mut d2);
            sync_docs(&d2, &mut d9);

            assert_eq!(f9.to_string(), "<a></a><x></x><y></y>");
            assert_eq!(f2.to_string(), "<a></a><x></x><y></y>");
        };

        // 1. XMLFragment::push
        check_fragment(
            |d, f| f.push(d.create_xml_element("x").unwrap()).unwrap(),
            |d, f| f.push(d.create_xml_element("y").unwrap()).unwrap(),
        );
        // 2. XMLFragmentWrite::push
        check_fragment(
            |d, f| {
                let x = d.create_xml_element("x").unwrap();
                d.transact_mut(None, |tx| tx.xml_fragment(f)?.push(x)).unwrap();
            },
            |d, f| {
                let y = d.create_xml_element("y").unwrap();
                d.transact_mut(None, |tx| tx.xml_fragment(f)?.push(y)).unwrap();
            },
        );

        let check_element = |push_x: fn(&Doc, &mut XMLElement), push_y: fn(&Doc, &mut XMLElement)| {
            let mut d9 = Doc::with_client(9);
            let mut d2 = Doc::with_client(2);
            let mut e9 = d9.get_or_create_xml_element("e").unwrap();
            let mut e2 = d2.get_or_create_xml_element("e").unwrap();

            e9.push(d9.create_xml_element("a").unwrap()).unwrap(); // (9, 0)
            e9.push(d9.create_xml_element("b").unwrap()).unwrap(); // (9, 1)
            sync_docs(&d9, &mut d2);

            e9.remove(1, 1).unwrap();
            push_x(&d9, &mut e9); // x at (9, 2), must anchor (a=(9,0), b=(9,1))
            push_y(&d2, &mut e2);

            {
                let store = d9.store.read().unwrap();
                let x_item = store.get_node(Id::new(9, 2)).unwrap().item(&store.type_arena);
                assert_eq!(x_item.origin_left_id(), Some(Id::new(9, 0)));
                assert_eq!(x_item.origin_right_id(), Some(Id::new(9, 1)));
            }

            sync_docs(&d9, &mut d2);
            sync_docs(&d2, &mut d9);

            assert_eq!(e9.to_string(), "<undefined><a></a><x></x><y></y></undefined>");
            assert_eq!(e2.to_string(), "<undefined><a></a><x></x><y></y></undefined>");
        };

        // 3. XMLElement::push
        check_element(
            |d, e| e.push(d.create_xml_element("x").unwrap()).unwrap(),
            |d, e| e.push(d.create_xml_element("y").unwrap()).unwrap(),
        );
        // 4. XMLElementWrite::push
        check_element(
            |d, e| {
                let x = d.create_xml_element("x").unwrap();
                d.transact_mut(None, |tx| tx.xml_element(e)?.push(x)).unwrap();
            },
            |d, e| {
                let y = d.create_xml_element("y").unwrap();
                d.transact_mut(None, |tx| tx.xml_element(e)?.push(y)).unwrap();
            },
        );

        // 5. DocSession::array_push on XMLFragment and XMLElement targets
        #[cfg(feature = "session")]
        for kind in [YTypeKind::XMLFragment, YTypeKind::XMLElement] {
            let elem = |tag: &str| crate::SessionValue::XmlElement {
                tag: tag.to_string(),
                attrs: vec![],
                children: vec![],
            };
            let mut s9 = crate::DocSession::<()>::new(crate::DocOptions::new().with_client_id(9), 500);
            let mut s2 = crate::DocSession::<()>::new(crate::DocOptions::new().with_client_id(2), 500);
            let r9: crate::TypeTarget = s9.ensure_root("x", kind).unwrap().into();
            let r2: crate::TypeTarget = s2.ensure_root("x", kind).unwrap().into();

            s9.array_push(&r9, vec![elem("a"), elem("b")]).unwrap();
            let u9 = s9.encode_update_v1().unwrap();
            s2.apply_update_v1(&u9).unwrap();

            s9.array_remove(&r9, 1, 1).unwrap();
            s9.array_push(&r9, vec![elem("x")]).unwrap();
            s2.array_push(&r2, vec![elem("y")]).unwrap();

            let mut d9 = s9.into_doc().unwrap();
            let mut d2 = s2.into_doc().unwrap();
            {
                let store = d9.store.read().unwrap();
                let x_item = store.get_node(Id::new(9, 2)).unwrap().item(&store.type_arena);
                assert_eq!(x_item.origin_left_id(), Some(Id::new(9, 0)));
                assert_eq!(x_item.origin_right_id(), Some(Id::new(9, 1)));
            }
            sync_docs(&d9, &mut d2);
            sync_docs(&d2, &mut d9);

            if kind == YTypeKind::XMLFragment {
                assert_eq!(
                    d9.get_or_create_xml_fragment("x").unwrap().to_string(),
                    "<a></a><x></x><y></y>"
                );
                assert_eq!(
                    d2.get_or_create_xml_fragment("x").unwrap().to_string(),
                    "<a></a><x></x><y></y>"
                );
            } else {
                assert_eq!(
                    d9.get_or_create_xml_element("x").unwrap().to_string(),
                    "<undefined><a></a><x></x><y></y></undefined>"
                );
                assert_eq!(
                    d2.get_or_create_xml_element("x").unwrap().to_string(),
                    "<undefined><a></a><x></x><y></y></undefined>"
                );
            }
        }
    }
}
