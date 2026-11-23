use super::*;

/// A transient view of a timeline block. Its span comes from the surrounding
/// client timeline; only the compact BlockRef is stored there.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) struct Node {
    pub id: Id,
    pub len: u64,
    pub kind: BlockKind,
}

impl Node {
    #[cfg(test)]
    pub fn store_item(types: &mut TypeArena, item: Item) -> Self {
        let (id, len, deleted) = (item.id, item.len, item.deleted());
        let idx = types.items.alloc(item).unwrap();
        Self {
            id,
            len,
            kind: if deleted {
                BlockKind::DeletedItem(idx)
            } else {
                BlockKind::Item(idx)
            },
        }
    }

    #[cfg(test)]
    pub fn item<'a>(&self, types: &'a TypeArena) -> &'a Item {
        types
            .items
            .get(self.as_item().expect("item node"))
            .expect("stored item")
    }

    pub fn new_gc(id: Id, len: u64) -> Self {
        Self {
            id,
            len,
            kind: BlockKind::Gc,
        }
    }
    pub fn new_skip(id: Id, len: u64) -> Self {
        Self {
            id,
            len,
            kind: BlockKind::Skip,
        }
    }
    #[cfg(test)]
    pub fn id(&self) -> Id {
        self.id
    }
    pub fn client(&self) -> Client {
        self.id.client
    }
    pub fn clock(&self) -> Clock {
        self.id.clock
    }
    pub fn len(&self) -> u64 {
        self.len
    }
    pub fn is_gc(&self) -> bool {
        self.kind == BlockKind::Gc
    }
    pub fn is_skip(&self) -> bool {
        self.kind == BlockKind::Skip
    }
    pub fn is_item(&self) -> bool {
        self.as_item().is_some()
    }
    pub fn deleted(&self) -> bool {
        self.kind.deleted()
    }
    pub fn as_item(&self) -> ItemRef {
        match self.kind {
            BlockKind::Item(i) | BlockKind::DeletedItem(i) => Some(i),
            BlockKind::Gc | BlockKind::Skip => None,
        }
    }
    pub fn write<W: CrdtWriter>(&self, types: &TypeArena, writer: &mut W) -> JwstCodecResult {
        match self.as_item() {
            Some(idx) => types.items.get(idx).expect("stored item").write(types, writer),
            None => {
                writer.write_info(if self.is_skip() { 10 } else { 0 })?;
                writer.write_var_u64(self.len)
            }
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
                    .parent(None)
                    .parent_sub(None)
                    .content(Content::String(String::from("content")))
                    .build();
                let mut types = TypeArena::default();
                let struct_info = Node::store_item(&mut types, item);

                assert_eq!(struct_info.len(), 7);
                assert_eq!(struct_info.client(), 3);
                assert_eq!(struct_info.clock(), 0);
                assert_eq!(struct_info.item(&types).left, None);
                assert_eq!(struct_info.item(&types).right, None);
            }
            for node in [Node::new_gc(Id::new(1, 5), 4), Node::new_skip(Id::new(1, 5), 4)] {
                let (left, right) = WireStruct::from_node(&TypeArena::default(), &node)
                    .unwrap()
                    .split_at(2)
                    .unwrap();
                assert_eq!(left.id(), Id::new(1, 5));
                assert_eq!(right.id(), Id::new(1, 7));
                assert_eq!((left.len(), right.len()), (2, 2));
                assert_eq!(left.is_skip(), node.is_skip());
                assert_eq!(matches!(right, WireStruct::Gc { .. }), node.is_gc());
            }
            let mut item = ItemBuilder::new()
                .id(Id::new(1, 5))
                .left_id(Some(Id::new(2, 3)))
                .right_id(Some(Id::new(3, 2)))
                .content(Content::String("abcd".into()))
                .build();
            item.flags.set_deleted();
            item.flags.set_keep();
            let (left, right) = item.split_at(2).unwrap();
            for item in [&left, &right] {
                assert!(item.deleted());
                assert!(item.keep());
                assert!(item.left.is_none() && item.right.is_none());
                assert_eq!(item.origin_right_id(), Some(Id::new(3, 2)));
            }
            assert_eq!(left.origin_left_id(), Some(Id::new(2, 3)));
            assert_eq!(right.origin_left_id(), Some(Id::new(1, 6)));
        });
    }

    #[test]
    fn test_read_write_struct_info() {
        loom_model!({
            let mut types = TypeArena::default();
            let root = types
                .alloc(YType::new_root(YTypeKind::Map, None, "parent".into()))
                .unwrap();
            let has_not_parent_id_and_has_parent = Node::store_item(
                &mut types,
                ItemBuilder::new()
                    .id((0, 0).into())
                    .left_id(None)
                    .right_id(None)
                    .parent(Some(root))
                    .parent_sub(None)
                    .content(Content::String(String::from("content")))
                    .build(),
            );

            let has_not_parent_id_and_has_parent_with_key = Node::store_item(
                &mut types,
                ItemBuilder::new()
                    .id((0, 0).into())
                    .left_id(None)
                    .right_id(None)
                    .parent(Some(root))
                    .parent_sub(Some(SmolStr::new_inline("parent_sub")))
                    .content(Content::String(String::from("content")))
                    .build(),
            );

            let has_parent_id = Node::store_item(
                &mut types,
                ItemBuilder::new()
                    .id((0, 0).into())
                    .left_id(Some((1, 2).into()))
                    .right_id(Some((2, 5).into()))
                    .parent(None)
                    .parent_sub(None)
                    .content(Content::String(String::from("content")))
                    .build(),
            );

            let struct_infos = vec![
                Node::new_gc((0, 0).into(), 42),
                Node::new_skip((0, 0).into(), 314),
                has_not_parent_id_and_has_parent,
                has_not_parent_id_and_has_parent_with_key,
                has_parent_id,
            ];

            for info in struct_infos {
                let mut update = Update::default();
                update
                    .structs
                    .insert(info.client(), [WireStruct::from_node(&types, &info).unwrap()].into());
                let decoded = Update::decode_v1(update.encode_v1().unwrap()).unwrap();
                let decoded = decoded.structs.get(&info.client()).unwrap().front().unwrap();

                assert_eq!(&WireStruct::from_node(&types, &info).unwrap(), decoded);
            }
        });
    }

    #[cfg(not(loom))]
    fn struct_info_round_trip(info: Node, types: &TypeArena) -> JwstCodecResult {
        if info.len() == 0 || info.clock().checked_add(info.len()).is_none() {
            return Ok(());
        }
        if info.is_item() && !info.item(types).is_valid() {
            return Ok(());
        }
        let mut update = Update::default();
        update
            .structs
            .insert(info.client(), [WireStruct::from_node(types, &info).unwrap()].into());
        let decoded = Update::decode_v1(update.encode_v1()?)?;
        let decoded = decoded.structs.get(&info.client()).unwrap().front().unwrap();

        assert_eq!(info.id(), decoded.id());
        assert_eq!(info.len(), decoded.len());

        Ok(())
    }

    #[cfg(not(loom))]
    proptest! {
        #[test]
        #[cfg_attr(miri, ignore)]
        fn test_random_struct_info(infos in vec((0u8..3, any::<Id>(), any::<u64>(), any::<Item>()), 0..10)) {
            let mut types = TypeArena::default();
            let root = types.alloc(YType::new_root(YTypeKind::Map,None,"root".into())).unwrap();
            for (kind,id,len,mut item) in infos {
                item.parent=Some(root);
                item.len = item.content.clock_len();
                if item.content.countable() { item.flags.set_countable(); }
                let node = match kind {0=> Node::new_gc(id,len), 1=> Node::new_skip(id,len), _=> Node::store_item(&mut types,item)};
                struct_info_round_trip(node,&types).unwrap();
            }
        }
    }
}
