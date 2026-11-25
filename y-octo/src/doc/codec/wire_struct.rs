use super::*;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum WireParent {
    Root(SmolStr),
    Item(Id),
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum WireContent {
    Deleted(u64),
    Json(Vec<Option<String>>),
    Binary(Vec<u8>),
    String(String),
    Embed(Box<Any>),
    Format { key: String, value: Box<Any> },
    Type { kind: YTypeKind, name: Option<String> },
    Any(Vec<Any>),
    Doc { guid: String, opts: Box<Any> },
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct WireItem {
    pub id: Id,
    pub len: u64,
    pub origin_left_id: Option<Id>,
    pub origin_right_id: Option<Id>,
    pub parent: Option<WireParent>,
    pub parent_sub: Option<SmolStr>,
    pub content: WireContent,
    pub flags: u8,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum WireStruct {
    Gc { id: Id, len: u64 },
    Skip { id: Id, len: u64 },
    Item(Box<WireItem>),
}

impl WireContent {
    pub(crate) fn wire_flags(&self) -> u8 {
        match self {
            Self::Deleted(_) => item_flags::ITEM_DELETED,
            Self::Format { .. } => 0,
            _ => item_flags::ITEM_COUNTABLE,
        }
    }

    pub fn split_in_place(&mut self, diff: u64) -> JwstCodecResult<Self> {
        match self {
            Self::String(str) => Ok(Self::String(utf16_split_in_place(str, diff))),
            Self::Json(vec) => {
                let right =
                    vec.split_off(usize::try_from(diff).map_err(|_| JwstCodecError::ContentSplitNotSupport(diff))?);
                vec.shrink_to_fit();
                Ok(Self::Json(right))
            }
            Self::Any(vec) => {
                let right =
                    vec.split_off(usize::try_from(diff).map_err(|_| JwstCodecError::ContentSplitNotSupport(diff))?);
                vec.shrink_to_fit();
                Ok(Self::Any(right))
            }
            Self::Deleted(len) => {
                let right = *len - diff;
                *len = diff;
                Ok(Self::Deleted(right))
            }
            _ => Err(JwstCodecError::ContentSplitNotSupport(diff)),
        }
    }

    pub(crate) fn split_in_place_with_len(&mut self, total_len: u64, diff: u64) -> JwstCodecResult<Self> {
        match self {
            Self::String(str) => Ok(Self::String(utf16_split_in_place_with_len(str, total_len, diff))),
            _ => self.split_in_place(diff),
        }
    }
    /// The stored content. A type is allocated in `types`, the arena of the
    /// store the content is integrated into.
    pub(crate) fn into_content(self, types: &mut TypeArena) -> JwstCodecResult<Content> {
        Ok(match self {
            Self::Deleted(v) => Content::Deleted(v),
            Self::Json(v) => Content::Json(v),
            Self::Binary(v) => Content::Binary(v),
            Self::String(v) => Content::String(v),
            Self::Embed(v) => Content::Embed(v),
            Self::Any(v) => Content::Any(v),
            Self::Format { key, value } => Content::format(key, *value),
            Self::Doc { guid, opts } => Content::doc(guid, *opts),
            Self::Type { kind, name } => Content::Type(types.alloc(YType::new(kind, name))?),
        })
    }
    pub(crate) fn view(&self) -> ContentView<'_> {
        match self {
            Self::Deleted(v) => ContentView::Deleted(*v),
            Self::Json(v) => ContentView::Json(v),
            Self::Binary(v) => ContentView::Binary(v),
            Self::String(v) => ContentView::String(v),
            Self::Embed(v) => ContentView::Embed(v),
            Self::Any(v) => ContentView::Any(v),
            Self::Format { key, value } => ContentView::Format { key, value },
            Self::Doc { guid, opts } => ContentView::Doc { guid, opts },
            Self::Type { kind, name } => ContentView::Type {
                kind: *kind,
                name: name.as_deref(),
            },
        }
    }
}
impl WireContent {
    /// A copy of `content` of the store whose type arena is `types`.
    pub(crate) fn from_content(types: &TypeArena, content: &Content) -> JwstCodecResult<Self> {
        Ok(match content {
            Content::Deleted(v) => Self::Deleted(*v),
            Content::Json(v) => Self::Json(v.clone()),
            Content::Binary(v) => Self::Binary(v.clone()),
            Content::String(v) => Self::String(v.clone()),
            Content::Embed(v) => Self::Embed(v.clone()),
            Content::Any(v) => Self::Any(v.clone()),
            Content::Format(format) => Self::Format {
                key: format.key.clone(),
                value: Box::new(format.value.clone()),
            },
            Content::Doc(doc) => Self::Doc {
                guid: doc.guid.clone(),
                opts: Box::new(doc.opts.clone()),
            },
            Content::Type(ty) => {
                let ty = types
                    .get(*ty)
                    .ok_or(JwstCodecError::InvalidStructType("released y type"))?;
                Self::Type {
                    kind: ty.kind(),
                    name: super::content::type_wire_name(ty.kind(), ty.name()).map(str::to_owned),
                }
            }
        })
    }
}

impl WireItem {
    /// A copy of `item` of the store whose type arena is `types`.
    pub(crate) fn from_item(types: &TypeArena, item: &Item) -> JwstCodecResult<Self> {
        let parent = if item.origin_left_id().is_none() && item.origin_right_id().is_none() {
            item.parent
                .as_ref()
                .map(|parent| parent.wire_parent(types))
                .transpose()?
                .map(|parent| match parent {
                    ParentInfo::Root(name) => WireParent::Root(name.into()),
                    ParentInfo::Item(id) => WireParent::Item(id),
                })
        } else {
            None
        };
        let content = WireContent::from_content(types, &item.content)?;
        Ok(Self {
            id: item.id,
            len: item.len,
            origin_left_id: item.origin_left_id(),
            origin_right_id: item.origin_right_id(),
            parent,
            // V1 retains the sub-key bit on stored overwrites even when the
            // origin makes the key itself implicit.
            parent_sub: item.parent_sub.clone(),
            flags: content.wire_flags(),
            content,
        })
    }
}

impl WireStruct {
    /// A copy of `node` of the store whose type arena is `types`.
    pub(crate) fn from_node(types: &TypeArena, node: &Node) -> JwstCodecResult<Self> {
        Ok(match node.as_item() {
            Some(idx) => Self::Item(Box::new(WireItem::from_item(
                types,
                types.items.get(idx).expect("stored item"),
            )?)),
            None if node.is_gc() => Self::Gc {
                id: node.id,
                len: node.len,
            },
            None => Self::Skip {
                id: node.id,
                len: node.len,
            },
        })
    }

    pub fn as_item(&self) -> Option<&WireItem> {
        match self {
            Self::Item(item) => Some(item),
            _ => None,
        }
    }
    pub fn id(&self) -> Id {
        match self {
            Self::Gc { id, .. } | Self::Skip { id, .. } => *id,
            Self::Item(item) => item.id,
        }
    }
    pub fn len(&self) -> u64 {
        match self {
            Self::Gc { len, .. } | Self::Skip { len, .. } => *len,
            Self::Item(item) => item.len,
        }
    }
    pub fn clock(&self) -> Clock {
        self.id().clock
    }
    pub fn client(&self) -> Client {
        self.id().client
    }
    pub fn is_skip(&self) -> bool {
        matches!(self, Self::Skip { .. })
    }
    pub fn split_at(self, offset: u64) -> JwstCodecResult<(Self, Self)> {
        debug_assert!(offset > 0 && offset < self.len());
        let right_id = self.id() + offset;
        let right_len = self.len() - offset;
        match self {
            Self::Gc { id, .. } => Ok((
                Self::Gc { id, len: offset },
                Self::Gc {
                    id: right_id,
                    len: right_len,
                },
            )),
            Self::Skip { id, .. } => Ok((
                Self::Skip { id, len: offset },
                Self::Skip {
                    id: right_id,
                    len: right_len,
                },
            )),
            Self::Item(mut left) => {
                let content = left.content.split_in_place_with_len(left.len, offset)?;
                let right = WireItem {
                    id: right_id,
                    len: right_len,
                    origin_left_id: Some(right_id - 1),
                    origin_right_id: left.origin_right_id,
                    parent: left.parent.clone(),
                    parent_sub: left.parent_sub.clone(),
                    content,
                    flags: left.flags,
                };
                left.len = offset;
                Ok((Self::Item(left), Self::Item(Box::new(right))))
            }
        }
    }
}

impl<W: CrdtWriter> CrdtWrite<W> for WireStruct {
    fn write(&self, encoder: &mut W) -> JwstCodecResult {
        match self {
            Self::Gc { len, .. } | Self::Skip { len, .. } => {
                encoder.write_info(if self.is_skip() { 10 } else { 0 })?;
                encoder.write_var_u64(*len)
            }
            Self::Item(item) => item.write(encoder),
        }
    }
}
impl<W: CrdtWriter> CrdtWrite<W> for WireItem {
    fn write(&self, encoder: &mut W) -> JwstCodecResult {
        self.content.view().write_item(
            encoder,
            self.origin_left_id,
            self.origin_right_id,
            self.parent_sub.as_ref(),
            || match self.parent.as_ref().ok_or(JwstCodecError::ParentNotFound)? {
                WireParent::Root(name) => Ok(ParentInfo::Root(name)),
                WireParent::Item(id) => Ok(ParentInfo::Item(*id)),
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn store_items_match_decoded_wire_metadata() {
        loom_model!(128 << 10, {
            let doc = DocOptions::new().with_client_id(7).auto_gc(false).build();
            let mut root = doc.get_or_create_map("root").unwrap();
            let mut inner = doc.create_map().unwrap();
            root.insert("inner".into(), inner.clone()).unwrap();
            inner
                .insert("xml".into(), doc.create_xml_element("section").unwrap())
                .unwrap();
            root.insert("key".into(), 1).unwrap();
            root.insert("key".into(), 2).unwrap();
            doc.get_or_create_array("list").unwrap().push(3).unwrap();
            let decoded = Update::decode_v1(doc.encode_update_v1().unwrap()).unwrap();
            let store = doc.store.read().unwrap();
            let nodes = &store.items[&7];
            assert_eq!(nodes.len(), 5);
            let wire = &decoded.structs[&7];
            assert_eq!(wire.len(), nodes.len());
            for (node, decoded) in nodes.nodes(7).zip(wire) {
                let stored = node.item(&store.type_arena);
                let mut direct = RawEncoder::default();
                stored.write(&store.type_arena, &mut direct).unwrap();
                let mut item = stored.clone();
                item.flags.set_keep();
                item.flags.set_deleted();
                if item.origin_left_id().is_some() {
                    // An inherited parent is never read by either writer or
                    // converter.
                    item.parent = None;
                }
                let mut converted = WireItem::from_item(&store.type_arena, &item).unwrap();
                let mut materialized = RawEncoder::default();
                converted.write(&mut materialized).unwrap();
                let bytes = materialized.into_inner();
                assert_eq!(bytes, direct.into_inner());
                assert_eq!(converted.flags, converted.content.wire_flags());

                let decoded = decoded.as_item().unwrap();
                if item.origin_left_id().is_some() || item.origin_right_id().is_some() {
                    assert_eq!(converted.parent_sub, item.parent_sub);
                    assert!(decoded.parent_sub.is_none());
                    // This fixture's inherited item overwrites the same map
                    // key.
                    assert_eq!(bytes[0], 0xA8);
                    let mut reencoded = RawEncoder::default();
                    decoded.write(&mut reencoded).unwrap();
                    let reencoded = reencoded.into_inner();
                    assert_eq!(reencoded[0], 0x88);
                    assert_eq!(bytes[1..], reencoded[1..]);
                    converted.parent_sub = None;
                }
                assert_eq!(&converted, decoded);
            }
            let nested = wire[1].as_item().unwrap();
            assert_eq!(nested.parent, Some(WireParent::Item(Id::new(7, 0))));
            assert_eq!(nested.parent_sub.as_deref(), Some("xml"));
            assert_eq!(
                nested.content,
                WireContent::Type {
                    kind: YTypeKind::XMLElement,
                    name: Some("section".into())
                }
            );
            let replacement = wire[3].as_item().unwrap();
            assert!(replacement.origin_left_id.is_some());
            assert_eq!(
                (replacement.parent.as_ref(), replacement.parent_sub.as_ref()),
                (None, None)
            );
            assert_eq!(wire[4].as_item().unwrap().parent, Some(WireParent::Root("list".into())));
            assert!(wire[4].as_item().unwrap().parent_sub.is_none());
        });
    }
}
