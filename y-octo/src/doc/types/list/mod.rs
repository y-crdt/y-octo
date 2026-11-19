mod search_marker;

pub(crate) use search_marker::{MarkerList, SearchMarker};

use super::*;

#[derive(Debug)]
pub(crate) struct ItemPosition {
    pub parent: YTypeRef,
    pub left: ItemRef,
    pub right: ItemRef,
    pub index: u64,
    pub offset: u64,
}

impl ItemPosition {
    pub fn forward(&mut self) {
        if let Some(right) = self.right.get() {
            if right.indexable() {
                self.index += right.len();
            }

            self.left = self.right.clone();
            self.right = right.right.clone();
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
            if let Some(left) = self.left.get() {
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
    cur: Option<&'a Item>,
}

impl<'a> ListIterator<'a> {
    pub fn new(ty: &'a YType) -> Self {
        Self { cur: ty.start.get() }
    }
}

impl<'a> Iterator for ListIterator<'a> {
    type Item = &'a Item;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.cur {
            self.cur = item.right.get();
            if !item.deleted() {
                return Some(item);
            }
        }

        None
    }
}

/// Finds the position of `index` for a reader holding the store read lock:
/// search markers are used but not updated.
pub(crate) fn find_pos(parent: &YTypeRef, ty: &YType, index: u64) -> Option<ItemPosition> {
    let marker = ty.markers.as_ref().and_then(|m| m.find_readonly(&ty.start, index));
    find_pos_from(parent, ty, index, marker)
}

/// Finds the position of `index` for a writer holding the store write lock,
/// updating the search markers on the way.
pub(crate) fn find_pos_mut(parent: &YTypeRef, ty: &mut YType, index: u64) -> Option<ItemPosition> {
    let (start, len) = (ty.start.clone(), ty.len);
    let marker = ty.markers.as_mut().and_then(|m| m.find_marker(&start, len, index));
    find_pos_from(parent, ty, index, marker)
}

fn find_pos_from(parent: &YTypeRef, ty: &YType, index: u64, marker: Option<SearchMarker>) -> Option<ItemPosition> {
    let mut remaining = index;

    let mut pos = ItemPosition {
        parent: parent.clone(),
        left: Somr::none(),
        right: ty.start.clone(),
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
        pos.left = marker.ptr.get().map(|ptr| ptr.left.clone()).unwrap_or_default();
        pos.right = marker.ptr;
    };

    // avoid the first item of the list being deleted
    while let Some(item) = pos.right.get() {
        if item.deleted() {
            pos.left = pos.right.clone();
            pos.right = item.right.clone();
            continue;
        } else {
            break;
        }
    }

    while remaining > 0 {
        let item = pos.right.get()?;
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

        pos.left = pos.right.clone();
        pos.right = item.right.clone();
    }

    Some(pos)
}

/// The item covering `index` and the offset of `index` inside it. The caller
/// holds the store lock while it uses the returned item.
pub(crate) fn item_at(parent: &YTypeRef, ty: &YType, index: u64) -> Option<(ItemRef, u64)> {
    if index >= ty.len {
        return None;
    }

    let pos = find_pos(parent, ty, index)?;
    if pos.offset != 0 {
        return Some((pos.left, pos.offset));
    }

    // An insertion cursor can stop at a tombstone. A read needs the next
    // visible value.
    let mut item = pos.right;
    while let Some(candidate) = item.get() {
        if candidate.indexable() {
            return Some((item, 0));
        }
        item = candidate.right.clone();
    }
    None
}

pub(crate) trait ListType: AsInner<Inner = YTypeRef> {
    #[inline(always)]
    fn _id(&self) -> Option<Id> {
        self.as_inner()
            .read(|_, ty| {
                if ty.is_preliminary() {
                    None
                } else {
                    ty.item.get().map(|item| item.id)
                }
            })
            .ok()
            .flatten()
    }

    #[inline(always)]
    fn content_len(&self) -> u64 {
        self.as_inner().read(|_, ty| ty.len).unwrap_or(0)
    }

    fn insert_at(&mut self, index: u64, content: Content) -> JwstCodecResult {
        let parent = self.as_inner();
        parent.write(|store, ty| Self::insert_locked(parent, store, ty, index, content))
    }

    /// Appends `content`: the end index is read under the same write lock
    /// that inserts, so a concurrent removal cannot move the end in between.
    fn push_back(&mut self, content: Content) -> JwstCodecResult {
        let parent = self.as_inner();
        parent.write(|store, ty| {
            let index = ty.len;
            Self::insert_locked(parent, store, ty, index, content)
        })
    }

    /// The caller holds the store write lock; `ty` is the data of `parent`.
    fn insert_locked(
        parent: &YTypeRef,
        store: &mut DocStore,
        ty: &mut YType,
        index: u64,
        content: Content,
    ) -> JwstCodecResult {
        if index > ty.len {
            return Err(JwstCodecError::IndexOutOfBound(index));
        }
        check_insertable(parent, ty, &content)?;

        if let Some(mut pos) = find_pos_mut(parent, ty, index) {
            pos.normalize(store)?;
            Self::insert_after(ty, store, pos, content)?;
        }

        Ok(())
    }

    fn insert_after(ty: &mut YType, store: &mut DocStore, pos: ItemPosition, content: Content) -> JwstCodecResult {
        if let Some(markers) = &mut ty.markers
            && content.countable()
        {
            markers.update_marker_changes(pos.index, content.clock_len() as i64);
        }

        let item = store.create_item(
            content,
            pos.left.clone(),
            pos.right.clone(),
            Some(Parent::Type(pos.parent)),
            None,
        );

        store.integrate(Node::Item(item), 0, Some(ty))?;

        Ok(())
    }

    fn remove_at(&mut self, idx: u64, len: u64) -> JwstCodecResult {
        if len == 0 {
            return Ok(());
        }

        let parent = self.as_inner();
        parent.write(|store, ty| {
            let content_len = ty.len;
            if content_len == 0 {
                return Ok(());
            }

            if idx >= content_len {
                return Err(JwstCodecError::IndexOutOfBound(idx));
            }

            if let Some(pos) = find_pos_mut(parent, ty, idx) {
                Self::remove_after(ty, store, pos, len)?;
            }

            Ok(())
        })
    }

    fn remove_after(ty: &mut YType, store: &mut DocStore, mut pos: ItemPosition, len: u64) -> JwstCodecResult {
        pos.normalize(store)?;

        let mut remaining = len;

        while remaining > 0 {
            let item_ref = pos.right.clone();
            let Some((indexable, content_len, item_id)) =
                item_ref.get().map(|item| (item.indexable(), item.len(), item.id))
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

                if let Some(item) = item_ref.get() {
                    store.delete_item(item, Some(ty));
                }
            }

            pos.forward();
        }

        if let Some(markers) = &mut ty.markers {
            markers.update_marker_changes(pos.index, -((len - remaining) as i64));
        }

        Ok(())
    }
}

/// Checks a value inserted under `parent` (whose data is `ty`): a type can only
/// be inserted into the document it was created in (its data is guarded by
/// that document's store lock), only once in its life, and never into itself
/// or its descendants.
///
/// Inserting a type at most once (as in Yjs) keeps its `item`, and so its
/// ancestor chain, fixed; with that, the ancestor walk below rejects every
/// cycle, and the type tree stays acyclic, which `DocStore::create_item` and
/// `DocStore::delete_item_inner` rely on.
/// The caller holds the store write lock.
pub(crate) fn check_insertable(parent: &YTypeRef, ty: &YType, content: &Content) -> JwstCodecResult {
    let Content::Type(value) = content else {
        return Ok(());
    };

    if !value.store.ptr_eq(&parent.store) {
        return Err(JwstCodecError::ForeignType);
    }

    // before reading `value`: the caller holds `parent`'s data mutably
    if value == parent {
        return Err(JwstCodecError::InvalidParent);
    }

    // A root type, or one inserted before (its item may since have been
    // deleted or collected, but is never unset again).
    if value
        .ty()
        .is_none_or(|value| !value.item.is_unset() || value.root_name.is_some())
    {
        return Err(JwstCodecError::TypeAlreadyInserted);
    }

    let mut item = ty.item.clone();
    while let Some(Parent::Type(ancestor)) = item.get().and_then(|i| i.parent.as_ref()) {
        if ancestor == value {
            return Err(JwstCodecError::InvalidParent);
        }
        item = ancestor.ty().map(|t| t.item.clone()).unwrap_or_default();
    }

    Ok(())
}
