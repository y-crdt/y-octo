use super::*;

impl TypeIdx {
    pub fn wire_parent(self, types: &TypeArena) -> JwstCodecResult<ParentInfo<'_>> {
        let ty = types.get(self).ok_or(JwstCodecError::InvalidParent)?;
        if let Carrier::Live(carrier) = ty.carrier(&types.items) {
            Ok(ParentInfo::Item(carrier.id))
        } else {
            ty.root_name()
                .map(ParentInfo::Root)
                .ok_or(JwstCodecError::InvalidParent)
        }
    }
}

#[derive(Clone)]
#[cfg_attr(all(test, not(loom)), derive(proptest_derive::Arbitrary))]
pub(crate) struct Item {
    pub id: Id,
    #[cfg_attr(all(test, not(loom)), proptest(value = "0"))]
    pub(crate) len: u64,
    pub(in crate::doc) origin_left: Id,
    pub(in crate::doc) origin_right: Id,
    #[cfg_attr(all(test, not(loom)), proptest(value = "None"))]
    pub left: ItemRef,
    #[cfg_attr(all(test, not(loom)), proptest(value = "None"))]
    pub right: ItemRef,
    #[cfg_attr(all(test, not(loom)), proptest(value = "None"))]
    pub parent: Option<TypeIdx>,
    #[cfg_attr(all(test, not(loom)), proptest(value = "Option::<SmolStr>::None"))]
    pub parent_sub: Option<SmolStr>,
    pub content: Content,
    #[cfg_attr(all(test, not(loom)), proptest(value = "ItemFlag::default()"))]
    pub flags: ItemFlag,
}

// make all Item readonly
pub(crate) type ItemRef = Option<ItemIdx>;

impl PartialEq for Item {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Item {}

impl std::fmt::Debug for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("Item");
        dbg.field("id", &self.id)
            .field("origin_left_id", &self.origin_left_id())
            .field("origin_right_id", &self.origin_right_id());

        dbg.field("left", &self.left).field("right", &self.right);

        dbg.field("parent", &self.parent)
            .field("parent_sub", &self.parent_sub)
            .field("content", &self.content)
            .field("flags", &self.flags)
            .finish()
    }
}

impl std::fmt::Display for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Item{}: [{:?}]", self.id, self.content)
    }
}

impl Default for Item {
    fn default() -> Self {
        Self {
            id: Id::default(),
            len: 0,
            origin_left: Id::default(),
            origin_right: Id::default(),
            left: None,
            right: None,
            parent: None,
            parent_sub: None,
            content: Content::Deleted(0),
            flags: ItemFlag::from(0),
        }
    }
}

impl Item {
    pub fn origin_left_id(&self) -> Option<Id> {
        self.flags
            .check(item_flags::ITEM_HAS_LEFT_ID)
            .then_some(self.origin_left)
    }

    pub fn set_origin_left_id(&mut self, origin: Option<Id>) {
        if let Some(id) = origin {
            self.origin_left = id;
            self.flags.set(item_flags::ITEM_HAS_LEFT_ID);
        } else {
            self.flags.clear(item_flags::ITEM_HAS_LEFT_ID);
        }
    }

    pub fn origin_right_id(&self) -> Option<Id> {
        self.flags
            .check(item_flags::ITEM_HAS_RIGHT_ID)
            .then_some(self.origin_right)
    }

    pub fn set_origin_right_id(&mut self, origin: Option<Id>) {
        if let Some(id) = origin {
            self.origin_right = id;
            self.flags.set(item_flags::ITEM_HAS_RIGHT_ID);
        } else {
            self.flags.clear(item_flags::ITEM_HAS_RIGHT_ID);
        }
    }

    pub fn new(
        items: &ItemSpace,
        id: Id,
        content: Content,
        left: ItemRef,
        right: ItemRef,
        parent: Option<TypeIdx>,
        parent_sub: Option<SmolStr>,
    ) -> Self {
        let len = content.clock_len();
        let flags = ItemFlag::from(if content.countable() {
            item_flags::ITEM_COUNTABLE
        } else {
            0
        });

        let mut item = Self {
            id,
            len,
            origin_left: Id::default(),
            left,
            origin_right: Id::default(),
            right,
            parent,
            parent_sub,
            content,
            flags,
        };
        item.set_origin_left_id(left.and_then(|i| items.get(i)).map(Item::last_id));
        item.set_origin_right_id(right.and_then(|i| items.get(i)).map(|item| item.id));
        item
    }

    // find a note that has parent info
    // in crdt tree, not all node has parent info
    // so we need to check left and right node if they have parent info
    pub fn find_node_with_parent_info<'a>(&'a self, items: &'a ItemSpace) -> Option<&'a Item> {
        if self.parent.is_some() {
            Some(self)
        } else if let Some(left) = self.left.and_then(|i| items.get(i)) {
            if left.parent.is_some() {
                Some(left)
            } else {
                left.right.and_then(|i| items.get(i))
            }
        } else {
            self.right.and_then(|i| items.get(i))
        }
    }

    pub fn len(&self) -> u64 {
        self.len
    }

    pub(crate) fn replace_content(&mut self, content: Content) {
        let len = content.clock_len();
        self.replace_content_with_len(content, len);
    }

    pub(crate) fn replace_content_with_len(&mut self, content: Content, len: u64) {
        debug_assert_eq!(content.clock_len(), len);
        self.content = content;
        self.len = len;
    }

    pub fn deleted(&self) -> bool {
        self.flags.deleted()
    }

    pub fn delete(&mut self) -> bool {
        if self.deleted() {
            return false;
        }

        self.flags.set_deleted();

        true
    }

    pub fn countable(&self) -> bool {
        self.flags.countable()
    }

    pub fn keep(&self) -> bool {
        self.flags.keep()
    }

    pub fn indexable(&self) -> bool {
        self.countable() && !self.deleted()
    }

    pub fn last_id(&self) -> Id {
        let Id { client, clock } = self.id;

        // Avoid underflowing if an item is ever constructed with zero length.
        Id::new(client, clock + self.len().saturating_sub(1))
    }

    #[cfg(test)]
    pub fn split_at(&self, offset: u64) -> JwstCodecResult<(Self, Self)> {
        debug_assert!(offset > 0 && offset < self.len());
        let (left_content, right_content) = self.content.split(offset)?;
        // Keep flags and wire origins, but detach links for the caller to
        // reconnect. Copying the items also keeps raw merge/SV slicing from
        // mutating shared inputs.
        let mut left = self.clone();
        let mut right = self.clone();
        left.left = None;
        left.right = None;
        left.replace_content_with_len(left_content, offset);
        right.id.clock += offset;
        right.set_origin_left_id(Some(Id::new(self.id.client, right.id.clock - 1)));
        right.left = None;
        right.right = None;
        right.replace_content_with_len(right_content, self.len() - offset);
        Ok((left, right))
    }

    #[cfg(all(test, not(loom)))]
    pub fn is_valid(&self) -> bool {
        let has_id = self.origin_left_id().is_some() || self.origin_right_id().is_some();
        !has_id && self.parent.is_some() || has_id && self.parent.is_none() && self.parent_sub.is_none()
    }

    /// Writes the item as a struct of the store whose type arena is `types`.
    pub fn write<W: CrdtWriter>(&self, types: &TypeArena, encoder: &mut W) -> JwstCodecResult {
        self.content.view(types)?.write_item(
            encoder,
            self.origin_left_id(),
            self.origin_right_id(),
            self.parent_sub.as_ref(),
            || {
                self.parent
                    .as_ref()
                    .ok_or(JwstCodecError::ParentNotFound)?
                    .wire_parent(types)
            },
        )
    }

    /// Writes the suffix of the item starting at UTF-16/element `offset`
    /// without cloning the full item or content. Matches
    /// `WireStruct::from_node(...).split_at(offset).1.write(encoder)` byte for
    /// byte.
    pub fn write_from<W: CrdtWriter>(&self, types: &TypeArena, offset: u64, encoder: &mut W) -> JwstCodecResult {
        if offset == 0 {
            return self.write(types, encoder);
        }
        if offset >= self.len {
            return Err(JwstCodecError::ContentSplitNotSupport(offset));
        }
        let origin_left = Some(self.id + (offset - 1));
        let origin_right = self.origin_right_id();
        let parent_sub = self.parent_sub.as_ref();
        let no_parent = || unreachable!("split suffix always has origin_left");
        match &self.content {
            Content::Deleted(len) => {
                let tail_len = len
                    .checked_sub(offset)
                    .filter(|&rem| rem > 0)
                    .ok_or(JwstCodecError::ContentSplitNotSupport(offset))?;
                ContentView::Deleted(tail_len).write_item(encoder, origin_left, origin_right, parent_sub, no_parent)
            }
            Content::Json(vec) => {
                let off = usize::try_from(offset).map_err(|_| JwstCodecError::ContentSplitNotSupport(offset))?;
                let slice = vec
                    .get(off..)
                    .filter(|s| !s.is_empty())
                    .ok_or(JwstCodecError::ContentSplitNotSupport(offset))?;
                ContentView::Json(slice).write_item(encoder, origin_left, origin_right, parent_sub, no_parent)
            }
            Content::Any(vec) => {
                let off = usize::try_from(offset).map_err(|_| JwstCodecError::ContentSplitNotSupport(offset))?;
                let slice = vec
                    .get(off..)
                    .filter(|s| !s.is_empty())
                    .ok_or(JwstCodecError::ContentSplitNotSupport(offset))?;
                ContentView::Any(slice).write_item(encoder, origin_left, origin_right, parent_sub, no_parent)
            }
            Content::String(s) => {
                debug_assert!(offset < self.len);
                let tail = utf16_tail(s, self.len, offset);
                ContentView::String(&tail).write_item(encoder, origin_left, origin_right, parent_sub, no_parent)
            }
            _ => Err(JwstCodecError::ContentSplitNotSupport(offset)),
        }
    }

    pub fn deep_compare(&self, items: &ItemSpace, other: &Self, other_items: &ItemSpace) -> bool {
        self.id == other.id
            && self.deleted() == other.deleted()
            && self.len() == other.len()
            && self.left.and_then(|i| items.get(i)).map(Item::last_id)
                == other.left.and_then(|i| other_items.get(i)).map(Item::last_id)
            && self.right.and_then(|i| items.get(i)).map(|i| i.id)
                == other.right.and_then(|i| other_items.get(i)).map(|i| i.id)
            && self.origin_left_id() == other.origin_left_id()
            && self.origin_right_id() == other.origin_right_id()
            && self.parent_sub == other.parent_sub
    }
}

const _: () = assert!(size_of::<Option<Item>>() == size_of::<Item>());

#[cfg(test)]
mod tests {
    #[cfg(not(loom))]
    use proptest::{collection::vec, prelude::*};

    #[cfg(not(loom))]
    use super::*;

    #[cfg(not(loom))]
    fn item_round_trip(item: &mut Item) -> JwstCodecResult {
        item.len = item.content.clock_len();
        let mut types = TypeArena::default();
        if item.origin_left_id().is_none() && item.origin_right_id().is_none() {
            item.parent = Some(types.alloc(YType::new_root(YTypeKind::Map, None, "parent".into()))?);
        }
        if !item.is_valid() {
            return Ok(());
        }
        if item.content.clock_len() == 0 || item.id.clock.checked_add(item.content.clock_len()).is_none() {
            return Ok(());
        }

        if item.content.countable() {
            item.flags.set_countable();
        }

        let mut update = Update::default();
        update.structs.insert(
            item.id.client,
            [WireStruct::Item(Box::new(WireItem::from_item(&types, item)?))].into(),
        );
        let decoded = Update::decode_v1(update.encode_v1()?)?;
        let decoded_item = match decoded.structs.get(&item.id.client).unwrap().front().unwrap() {
            WireStruct::Item(item) => item,
            _ => unreachable!(),
        };

        assert_eq!(item.id, decoded_item.id);
        assert_eq!(item.origin_left_id(), decoded_item.origin_left_id);
        assert_eq!(item.origin_right_id(), decoded_item.origin_right_id);

        Ok(())
    }

    #[cfg(not(loom))]
    proptest! {
        #[test]
        #[cfg_attr(miri, ignore)]
        fn test_random_content(mut items in vec((any::<Item>(), any::<Option<Id>>(), any::<Option<Id>>()), 0..10)) {
            for (item, left, right) in &mut items {
                item.set_origin_left_id(*left);
                item.set_origin_right_id(*right);
                item_round_trip(item).unwrap();
            }
        }
    }
}
