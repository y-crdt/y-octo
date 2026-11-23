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
    while let Some(item) = pos.right.and_then(|i| items.get(i)) {
        if item.deleted() {
            pos.left = pos.right;
            pos.right = item.right;
            continue;
        } else {
            break;
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
            let len = store.type_arena[ty].len;
            list_insert(store, ty, len, content)
        })
    }

    fn remove_at(&mut self, idx: u64, len: u64) -> JwstCodecResult {
        self.as_inner().write(|store, ty| list_remove(store, ty, idx, len))
    }
}

/// Inserts `content` at `index` of the list type `ty` of `store`. The caller
/// holds the store write lock.
pub(crate) fn list_insert(
    store: &mut DocStore,
    ty: TypeIdx,
    index: u64,
    content: impl Into<NewContent>,
) -> JwstCodecResult {
    let content = content.into();
    if index > store.type_arena[ty].len {
        return Err(JwstCodecError::IndexOutOfBound(index));
    }
    if matches!(&content, NewContent::Local(Content::String(text)) if text.is_empty()) {
        return Ok(());
    }
    let content = check_insertable(&store.type_arena, ty, content)?;

    let (parent, items) = store.type_arena.type_and_items(ty);
    if let Some(mut pos) = find_pos_mut(items, parent, index) {
        items.check_capacity(1 + usize::from(pos.offset > 0))?;
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

fn remove_after(store: &mut DocStore, ty: TypeIdx, mut pos: ItemPosition, len: u64) -> JwstCodecResult {
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
