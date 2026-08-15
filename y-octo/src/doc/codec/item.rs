use super::*;

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub(crate) enum Parent {
    #[cfg_attr(test, proptest(skip))]
    Type(YTypeRef),
    #[cfg_attr(test, proptest(value = "Parent::String(SmolStr::default())"))]
    String(SmolStr),
    Id(Id),
}

#[derive(Clone)]
#[cfg_attr(all(test, not(loom)), derive(proptest_derive::Arbitrary))]
pub(crate) struct Item {
    pub id: Id,
    #[cfg_attr(all(test, not(loom)), proptest(value = "0"))]
    pub(crate) len: u64,
    pub origin_left_id: Option<Id>,
    pub origin_right_id: Option<Id>,
    #[cfg_attr(all(test, not(loom)), proptest(value = "Somr::none()"))]
    pub left: ItemRef,
    #[cfg_attr(all(test, not(loom)), proptest(value = "Somr::none()"))]
    pub right: ItemRef,
    pub parent: Option<Parent>,
    #[cfg_attr(all(test, not(loom)), proptest(value = "Option::<SmolStr>::None"))]
    pub parent_sub: Option<SmolStr>,
    pub content: Content,
    #[cfg_attr(all(test, not(loom)), proptest(value = "ItemFlag::default()"))]
    pub flags: ItemFlag,
}

// make all Item readonly
pub(crate) type ItemRef = Somr<Item>;

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
            .field("origin_left_id", &self.origin_left_id)
            .field("origin_right_id", &self.origin_right_id);

        if let Some(left) = self.left.get() {
            dbg.field("left", &left.id);
        }

        if let Some(right) = self.right.get() {
            dbg.field("right", &right.id);
        }

        dbg.field(
            "parent",
            &self.parent.as_ref().map(|p| match p {
                Parent::Type(_) => "[Type]".to_string(),
                Parent::String(name) => format!("Parent({name})"),
                Parent::Id(id) => format!("({}, {})", id.client, id.clock),
            }),
        )
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
            origin_left_id: None,
            origin_right_id: None,
            left: Somr::none(),
            right: Somr::none(),
            parent: None,
            parent_sub: None,
            content: Content::Deleted(0),
            flags: ItemFlag::from(0),
        }
    }
}

impl Item {
    pub fn new(
        id: Id,
        content: Content,
        left: Somr<Item>,
        right: Somr<Item>,
        parent: Option<Parent>,
        parent_sub: Option<SmolStr>,
    ) -> Self {
        let len = content.clock_len();
        let flags = ItemFlag::from(if content.countable() {
            item_flags::ITEM_COUNTABLE
        } else {
            0
        });

        Self {
            id,
            len,
            origin_left_id: left.get().map(|left| left.last_id()),
            left,
            origin_right_id: right.get().map(|right| right.id),
            right,
            parent,
            parent_sub,
            content,
            flags,
        }
    }

    // find a note that has parent info
    // in crdt tree, not all node has parent info
    // so we need to check left and right node if they have parent info
    pub fn find_node_with_parent_info(&self) -> Option<Item> {
        if self.parent.is_some() {
            return Some(self.clone());
        } else if let Some(item) = self.left.get() {
            if item.parent.is_none() {
                if let Some(item) = item.right.get() {
                    return Some(item.clone());
                }
            } else {
                return Some(item.clone());
            }
        } else if let Some(item) = self.right.get() {
            return Some(item.clone());
        }
        None
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

    pub fn delete(&self) -> bool {
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

        // degenerate zero-length structs are accepted on decode; avoid
        // underflowing when computing their last id
        Id::new(client, clock + self.len().saturating_sub(1))
    }

    pub fn split_at(&self, offset: u64) -> JwstCodecResult<(Self, Self)> {
        debug_assert!(offset > 0 && self.len() > 1 && offset < self.len());
        let id = self.id;
        let right_id = Id::new(id.client, id.clock + offset);
        let (left_content, right_content) = self.content.split(offset)?;

        let left_item = Item::new(
            id,
            left_content,
            // let caller connect left <-> node <-> right
            Somr::none(),
            Somr::none(),
            self.parent.clone(),
            self.parent_sub.clone(),
        );

        let right_item = Item::new(
            right_id,
            right_content,
            // let caller connect left <-> node <-> right
            Somr::none(),
            Somr::none(),
            self.parent.clone(),
            self.parent_sub.clone(),
        );

        if self.deleted() {
            left_item.flags.set_deleted();
            right_item.flags.set_deleted();
        }
        if self.keep() {
            left_item.flags.set_keep();
            right_item.flags.set_keep();
        }

        Ok((left_item, right_item))
    }

    fn get_info(&self) -> u8 {
        let mut info = self.content.get_info();

        if self.origin_left_id.is_some() {
            info |= item_flags::ITEM_HAS_LEFT_ID;
        }
        if self.origin_right_id.is_some() {
            info |= item_flags::ITEM_HAS_RIGHT_ID;
        }
        if self.parent_sub.is_some() {
            info |= item_flags::ITEM_HAS_PARENT_SUB;
        }

        info
    }

    #[cfg(test)]
    pub fn is_valid(&self) -> bool {
        let has_id = self.origin_left_id.is_some() || self.origin_right_id.is_some();
        !has_id && self.parent.is_some() || has_id && self.parent.is_none() && self.parent_sub.is_none()
    }

    pub fn write<W: CrdtWriter>(&self, encoder: &mut W) -> JwstCodecResult {
        let info = self.get_info();
        let has_not_sibling = info & item_flags::ITEM_HAS_SIBLING == 0;

        encoder.write_info(info)?;

        if let Some(left_id) = self.origin_left_id {
            encoder.write_item_id(&left_id)?;
        }
        if let Some(right_id) = self.origin_right_id {
            encoder.write_item_id(&right_id)?;
        }

        if has_not_sibling {
            if let Some(parent) = &self.parent {
                match parent {
                    Parent::String(s) => {
                        encoder.write_var_u64(1)?;
                        encoder.write_var_string(s)?;
                    }
                    Parent::Id(id) => {
                        encoder.write_var_u64(0)?;
                        encoder.write_item_id(id)?;
                    }
                    Parent::Type(ty) => {
                        let ty = ty.ty().ok_or(JwstCodecError::InvalidParent)?;
                        if let Some(item) = ty.item.get() {
                            encoder.write_var_u64(0)?;
                            encoder.write_item_id(&item.id)?;
                        } else if let Some(name) = &ty.root_name {
                            encoder.write_var_u64(1)?;
                            encoder.write_var_string(name)?;
                        } else {
                            return Err(JwstCodecError::InvalidParent);
                        }
                    }
                }
            } else {
                // if item delete, it must not exists in crdt state tree
                debug_assert!(!self.deleted());
                return Err(JwstCodecError::ParentNotFound);
            }

            if let Some(parent_sub) = &self.parent_sub {
                encoder.write_var_string(parent_sub)?;
            }
        }

        self.content.write(encoder)?;

        Ok(())
    }

    pub fn deep_compare(&self, other: &Self) -> bool {
        if self.id != other.id
            || self.deleted() != other.deleted()
            || self.len() != other.len()
            || self.left.get().map(|l| l.last_id()) != other.left.get().map(|l| l.last_id())
            || self.right.get().map(|r| r.id) != other.right.get().map(|r| r.id)
            || self.origin_left_id != other.origin_left_id
            || self.origin_right_id != other.origin_right_id
            || self.parent_sub != other.parent_sub
        {
            return false;
        }

        true
    }
}

#[allow(dead_code)]
#[cfg(any(debug, test))]
impl Item {
    pub fn print_left(&self) {
        let mut ret = vec![format!("Self{}: [{:?}]", self.id, self.content)];
        let mut left: Somr<Item> = self.left.clone();

        while let Some(item) = left.get() {
            ret.push(format!("{item}"));
            left = item.left.clone();
        }
        ret.reverse();

        println!("{}", ret.join(" <- "));
    }

    pub fn print_right(&self) {
        let mut ret = vec![format!("Self{}: [{:?}]", self.id, self.content)];
        let mut right = self.right.clone();

        while let Some(item) = right.get() {
            ret.push(format!("{item}"));
            right = item.right.clone();
        }

        println!("{}", ret.join(" -> "));
    }
}

#[cfg(test)]
mod tests {
    #[cfg(not(loom))]
    use proptest::{collection::vec, prelude::*};

    #[cfg(not(loom))]
    use super::*;

    #[cfg(not(loom))]
    fn item_round_trip(item: &mut Item) -> JwstCodecResult {
        item.len = item.content.clock_len();
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
        update.structs.insert(item.id.client, [Node::from(item.clone())].into());
        let decoded = Update::decode_v1(update.encode_v1()?)?;
        let decoded_item = match decoded.structs.get(&item.id.client).unwrap().front().unwrap() {
            Node::Item(item) => item.get().unwrap(),
            _ => unreachable!(),
        };

        assert_eq!(item, decoded_item);

        Ok(())
    }

    #[cfg(not(loom))]
    proptest! {
        #[test]
        #[cfg_attr(miri, ignore)]
        fn test_random_content(mut items in vec(any::<Item>(), 0..10)) {
            for item in &mut items {
                item_round_trip(item).unwrap();
            }
        }
    }

    #[test]
    #[cfg(not(loom))]
    fn split_at_inherits_flags() {
        let build = || {
            Item::new(
                Id::new(1, 0),
                Content::String("abc".into()),
                Somr::none(),
                Somr::none(),
                Some(Parent::String("t".into())),
                None,
            )
        };

        let (left, right) = build().split_at(1).unwrap();
        assert!(
            !left.deleted() && !right.deleted(),
            "a live item splits into live halves"
        );
        assert!(!left.keep() && !right.keep());

        let deleted = build();
        deleted.flags.set_deleted();
        let (left, right) = deleted.split_at(1).unwrap();
        assert!(left.deleted(), "left half of a deleted item stays deleted");
        assert!(right.deleted(), "right half of a deleted item stays deleted");

        let kept = build();
        kept.flags.set_keep();
        let (left, right) = kept.split_at(1).unwrap();
        assert!(left.keep() && right.keep(), "both halves stay protected from gc");

        // the halves own their flags, they do not share a flag word
        let deleted = build();
        deleted.flags.set_deleted();
        let (left, right) = deleted.split_at(1).unwrap();
        right.flags.clear_deleted();
        assert!(left.deleted() && !right.deleted());
    }
}
