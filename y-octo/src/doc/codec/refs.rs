use super::*;

// make fields Copy + Clone without much effort
#[derive(Debug, Clone)]
#[cfg_attr(all(test, not(loom)), derive(proptest_derive::Arbitrary))]
pub(crate) enum Node {
    GC(Box<NodeLen>),
    Skip(Box<NodeLen>),
    Item(ItemRef),
}

/// Simple representation of id and len struct used by GC and Skip node.
#[derive(Debug, Clone)]
#[cfg_attr(all(test, not(loom)), derive(proptest_derive::Arbitrary))]
pub(crate) struct NodeLen {
    pub id: Id,
    pub len: u64,
}

impl<W: CrdtWriter> CrdtWrite<W> for Node {
    fn write(&self, writer: &mut W) -> JwstCodecResult {
        match self {
            Node::GC(item) => {
                writer.write_info(0)?;
                writer.write_var_u64(item.len)
            }
            Node::Skip(item) => {
                writer.write_info(10)?;
                writer.write_var_u64(item.len)
            }
            Node::Item(item) => item.get().unwrap().write(writer),
        }
    }
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Node::GC(left), Node::GC(right)) => left.id == right.id,
            (Node::Skip(left), Node::Skip(right)) => left.id == right.id,
            (Node::Item(item1), Node::Item(item2)) => item1.get() == item2.get(),
            _ => false,
        }
    }
}

impl Eq for Node {}

impl From<Item> for Node {
    fn from(value: Item) -> Self {
        Self::Item(Somr::new(value))
    }
}

impl Node {
    pub fn new_skip(id: Id, len: u64) -> Self {
        Self::Skip(Box::new(NodeLen { id, len }))
    }

    pub fn new_gc(id: Id, len: u64) -> Self {
        Self::GC(Box::new(NodeLen { id, len }))
    }

    pub fn id(&self) -> Id {
        match self {
            Node::GC(item) => item.id,
            Node::Skip(item) => item.id,
            Node::Item(item) => unsafe { item.get_unchecked() }.id,
        }
    }

    pub fn client(&self) -> Client {
        self.id().client
    }

    pub fn clock(&self) -> Clock {
        self.id().clock
    }

    pub fn len(&self) -> u64 {
        match self {
            Self::GC(item) => item.len,
            Self::Skip(item) => item.len,
            Self::Item(item) => unsafe { item.get_unchecked() }.len(),
        }
    }

    pub fn is_gc(&self) -> bool {
        matches!(self, Self::GC { .. })
    }

    pub fn is_skip(&self) -> bool {
        matches!(self, Self::Skip { .. })
    }

    pub fn is_item(&self) -> bool {
        matches!(self, Self::Item(_))
    }

    pub fn as_item(&self) -> Somr<Item> {
        if let Self::Item(item) = self {
            item.clone()
        } else {
            Somr::none()
        }
    }

    // Empty Somr links must be None, not neighbors, so head/tail stop at the
    // real boundary.
    pub fn left(&self) -> Option<Self> {
        if let Node::Item(item) = self {
            item.get()
                .and_then(|item| item.left.is_some().then(|| Node::Item(item.left.clone())))
        } else {
            None
        }
    }

    pub fn right(&self) -> Option<Self> {
        if let Node::Item(item) = self {
            item.get()
                .and_then(|item| item.right.is_some().then(|| Node::Item(item.right.clone())))
        } else {
            None
        }
    }

    pub fn head(&self) -> Self {
        let mut cur = self.clone();

        while let Some(left) = cur.left() {
            if left.is_item() {
                cur = left
            } else {
                break;
            }
        }

        cur
    }

    #[allow(dead_code)]
    pub fn tail(&self) -> Self {
        let mut cur = self.clone();

        while let Some(right) = cur.right() {
            if right.is_item() {
                cur = right
            } else {
                break;
            }
        }

        cur
    }

    pub fn flags(&self) -> ItemFlag {
        if let Node::Item(item) = self {
            item.get().unwrap().flags.clone()
        } else {
            // deleted
            ItemFlag::from(4)
        }
    }

    pub fn split_at(&self, offset: u64) -> JwstCodecResult<(Self, Self)> {
        debug_assert!(offset > 0 && offset < self.len());
        match self {
            Self::GC(node) => Ok((
                Self::new_gc(node.id, offset),
                Self::new_gc(Id::new(node.id.client, node.id.clock + offset), node.len - offset),
            )),
            Self::Skip(node) => Ok((
                Self::new_skip(node.id, offset),
                Self::new_skip(Id::new(node.id.client, node.id.clock + offset), node.len - offset),
            )),
            Self::Item(item) => {
                let (left, right) = item.get().unwrap().split_at(offset)?;
                Ok((left.into(), right.into()))
            }
        }
    }

    #[inline]
    #[allow(dead_code)]
    pub fn countable(&self) -> bool {
        self.flags().countable()
    }

    #[inline]
    pub fn deleted(&self) -> bool {
        self.flags().deleted()
    }

    pub fn merge(&mut self, right: Self) -> bool {
        match (self, right) {
            (Node::GC(left), Node::GC(right)) => {
                left.len += right.len;
            }
            (Node::Skip(left), Node::Skip(right)) => {
                left.len += right.len;
            }
            (Node::Item(lref), Node::Item(rref)) => {
                let mut litem = unsafe { lref.get_mut_unchecked() };
                let mut ritem = unsafe { rref.get_mut_unchecked() };
                let llen = litem.len();
                let rlen = ritem.len();

                let parent_kind = match &litem.parent {
                    Some(Parent::Type(ty)) => ty.ty().map(|ty| ty.kind()),
                    _ => None,
                };

                if litem.id.client != ritem.id.client
                    // not same delete status
                    || litem.deleted() != ritem.deleted()
                    // not clock continuous
                    || litem.id.clock + litem.len() != ritem.id.clock
                    // not insertion continuous
                    || Some(litem.last_id()) != ritem.origin_left_id
                    // not insertion continuous
                    || litem.origin_right_id != ritem.origin_right_id
                    // not runtime continuous
                    || litem.right != rref
                {
                    return false;
                }

                match (&mut litem.content, &mut ritem.content) {
                    (Content::Deleted(l), Content::Deleted(r)) => {
                        *l += *r;
                    }
                    (Content::Json(l), Content::Json(r)) => {
                        l.extend(r.drain(0..));
                    }
                    (Content::String(l), Content::String(r)) => {
                        let allow_merge_string = matches!(parent_kind, Some(YTypeKind::Text | YTypeKind::XMLText));

                        if !allow_merge_string {
                            return false;
                        }

                        *l += r;
                    }
                    (Content::Any(l), Content::Any(r)) => {
                        l.extend(r.drain(0..));
                    }
                    _ => {
                        return false;
                    }
                }

                if let Some(Parent::Type(p)) = &litem.parent
                    && let Some(parent) = p.ty_mut()
                    && let Some(markers) = &parent.markers
                {
                    markers.replace_marker(rref.clone(), lref.clone(), -(llen as i64));
                }

                if ritem.keep() {
                    litem.flags.set_keep()
                }

                litem.len += rlen;
                litem.right = ritem.right.clone();
                unsafe {
                    if litem.right.is_some() {
                        litem.right.get_mut_unchecked().left = lref.clone();
                    }
                }
            }
            _ => {
                return false;
            }
        }

        true
    }
}

impl From<Option<Node>> for Somr<Item> {
    fn from(value: Option<Node>) -> Self {
        match value {
            Some(n) => n.as_item(),
            None => Somr::none(),
        }
    }
}

impl From<&Option<Node>> for Somr<Item> {
    fn from(value: &Option<Node>) -> Self {
        match value {
            Some(n) => n.as_item(),
            None => Somr::none(),
        }
    }
}

impl From<Option<&Node>> for Somr<Item> {
    fn from(value: Option<&Node>) -> Self {
        match value {
            Some(n) => n.as_item(),
            None => Somr::none(),
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(not(loom))]
    use proptest::{collection::vec, prelude::*};

    use super::{utils::ItemBuilder, *};

    #[test]
    fn test_struct_info() {
        loom_model!({
            {
                let struct_info = Node::new_gc(Id::new(1, 0), 10);
                assert_eq!(struct_info.len(), 10);
                assert_eq!(struct_info.client(), 1);
                assert_eq!(struct_info.clock(), 0);
            }

            {
                let struct_info = Node::new_skip(Id::new(2, 0), 20);
                assert_eq!(struct_info.len(), 20);
                assert_eq!(struct_info.client(), 2);
                assert_eq!(struct_info.clock(), 0);
            }

            {
                let item = ItemBuilder::new()
                    .id((3, 0).into())
                    .left_id(None)
                    .right_id(None)
                    .parent(Some(Parent::String(SmolStr::new_inline("parent"))))
                    .parent_sub(None)
                    .content(Content::String(String::from("content")))
                    .build();
                let struct_info = Node::Item(Somr::new(item));

                assert_eq!(struct_info.len(), 7);
                assert_eq!(struct_info.client(), 3);
                assert_eq!(struct_info.clock(), 0);
                assert_eq!(struct_info.head(), struct_info);
                assert_eq!(struct_info.tail(), struct_info);
                assert!(struct_info.left().is_none());
                assert!(struct_info.right().is_none());
            }
            for node in [Node::new_gc(Id::new(1, 5), 4), Node::new_skip(Id::new(1, 5), 4)] {
                let (left, right) = node.split_at(2).unwrap();
                assert_eq!(left.id(), Id::new(1, 5));
                assert_eq!(right.id(), Id::new(1, 7));
                assert_eq!((left.len(), right.len()), (2, 2));
                assert_eq!(left.is_skip(), node.is_skip());
                assert_eq!(right.is_gc(), node.is_gc());
            }
            let item = ItemBuilder::new()
                .id(Id::new(1, 5))
                .left_id(Some(Id::new(2, 3)))
                .right_id(Some(Id::new(3, 2)))
                .content(Content::String("abcd".into()))
                .build();
            item.flags.set_deleted();
            item.flags.set_keep();
            let (left, right) = Node::from(item).split_at(2).unwrap();
            for node in [&left, &right] {
                let item = node.as_item();
                let item = item.get().unwrap();
                assert!(item.deleted());
                assert!(item.keep());
                assert!(item.left.is_none() && item.right.is_none());
                assert_eq!(item.origin_right_id, Some(Id::new(3, 2)));
            }
            assert_eq!(left.as_item().get().unwrap().origin_left_id, Some(Id::new(2, 3)));
            assert_eq!(right.as_item().get().unwrap().origin_left_id, Some(Id::new(1, 6)));
        });
    }

    #[test]
    fn test_read_write_struct_info() {
        loom_model!({
            let has_not_parent_id_and_has_parent = Node::Item(Somr::new(
                ItemBuilder::new()
                    .id((0, 0).into())
                    .left_id(None)
                    .right_id(None)
                    .parent(Some(Parent::String(SmolStr::new_inline("parent"))))
                    .parent_sub(None)
                    .content(Content::String(String::from("content")))
                    .build(),
            ));

            let has_not_parent_id_and_has_parent_with_key = Node::Item(Somr::new(
                ItemBuilder::new()
                    .id((0, 0).into())
                    .left_id(None)
                    .right_id(None)
                    .parent(Some(Parent::String(SmolStr::new_inline("parent"))))
                    .parent_sub(Some(SmolStr::new_inline("parent_sub")))
                    .content(Content::String(String::from("content")))
                    .build(),
            ));

            let has_parent_id = Node::Item(Somr::new(
                ItemBuilder::new()
                    .id((0, 0).into())
                    .left_id(Some((1, 2).into()))
                    .right_id(Some((2, 5).into()))
                    .parent(None)
                    .parent_sub(None)
                    .content(Content::String(String::from("content")))
                    .build(),
            ));

            let struct_infos = vec![
                Node::new_gc((0, 0).into(), 42),
                Node::new_skip((0, 0).into(), 314),
                has_not_parent_id_and_has_parent,
                has_not_parent_id_and_has_parent_with_key,
                has_parent_id,
            ];

            for info in struct_infos {
                let mut update = Update::default();
                update.structs.insert(info.client(), [info.clone()].into());
                let decoded = Update::decode_v1(update.encode_v1().unwrap()).unwrap();
                let decoded = decoded.structs.get(&info.client()).unwrap().front().unwrap();

                assert_eq!(&info, decoded);
            }
        });
    }

    #[cfg(not(loom))]
    fn struct_info_round_trip(info: &mut Node) -> JwstCodecResult {
        if info.len() == 0 || info.clock().checked_add(info.len()).is_none() {
            return Ok(());
        }
        if let Node::Item(item) = info
            && let Some(item) = item.get_mut()
        {
            if !item.is_valid() {
                return Ok(());
            }

            if item.content.countable() {
                item.flags.set_countable();
            }
        }
        let mut update = Update::default();
        update.structs.insert(info.client(), [info.clone()].into());
        let decoded = Update::decode_v1(update.encode_v1()?)?;
        let decoded = decoded.structs.get(&info.client()).unwrap().front().unwrap();

        assert_eq!(info, decoded);

        Ok(())
    }

    #[cfg(not(loom))]
    proptest! {
        #[test]
        #[cfg_attr(miri, ignore)]
        fn test_random_struct_info(mut infos in vec(any::<Node>(), 0..10)) {
            for info in &mut infos {
                struct_info_round_trip(info).unwrap();
            }
        }
    }
}
