use super::*;

pub(crate) struct ItemBuilder {
    item: Item,
}

#[allow(dead_code)]
impl ItemBuilder {
    pub fn new() -> ItemBuilder {
        Self { item: Item::default() }
    }

    pub fn id(mut self, id: Id) -> ItemBuilder {
        self.item.id = id;
        self
    }

    pub fn left_id(mut self, left_id: Option<Id>) -> ItemBuilder {
        self.item.set_origin_left_id(left_id);
        self
    }

    pub fn right_id(mut self, right_id: Option<Id>) -> ItemBuilder {
        self.item.set_origin_right_id(right_id);
        self
    }

    pub fn parent(mut self, parent: Option<TypeIdx>) -> ItemBuilder {
        self.item.parent = parent;
        self
    }

    #[allow(dead_code)]
    pub fn parent_sub(mut self, parent_sub: Option<SmolStr>) -> ItemBuilder {
        self.item.parent_sub = parent_sub;
        self
    }

    pub fn content(mut self, content: Content) -> ItemBuilder {
        self.item.replace_content(content);
        self
    }

    pub fn flags(mut self, flags: ItemFlag) -> ItemBuilder {
        self.item.flags = flags;
        self
    }

    pub fn build(mut self) -> Item {
        if self.item.content.countable() {
            self.item.flags.set(item_flags::ITEM_COUNTABLE);
        }

        self.item
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_item_builder() {
        loom_model!({
            let root = TypeArena::default()
                .alloc(YType::new_root(YTypeKind::Map, None, "test".into()))
                .unwrap();
            let item = ItemBuilder::new()
                .id(Id::new(0, 1))
                .left_id(Some(Id::new(2, 3)))
                .right_id(Some(Id::new(4, 5)))
                .parent(Some(root))
                .content(Content::Any(vec![Any::String("Hello".into())]))
                .build();

            assert_eq!(item.id, Id::new(0, 1));
            assert_eq!(item.origin_left_id(), Some(Id::new(2, 3)));
            assert_eq!(item.origin_right_id(), Some(Id::new(4, 5)));
            assert_eq!(item.parent, Some(root));
            assert_eq!(item.parent_sub, None);
            assert_eq!(item.content, Content::Any(vec![Any::String("Hello".into())]));
        });
    }
}
