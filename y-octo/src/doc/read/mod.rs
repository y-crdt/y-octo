mod limits;
mod resolve;
mod scan;
mod value;

use std::{ops::Range, sync::Arc};

pub use limits::{ReadError, ReadLimits};
pub use value::{ReadAny, ReadArray, ReadMap, ReadText, ReadTextRun, ReadValue};

use super::{ClientMap, HashMap, Id, YTypeKind};

type NodeId = u32;
type TypeId = u32;
type KeyId = u32;
type AnyId = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Span {
    start: u32,
    end: u32,
}

impl Span {
    fn new(range: Range<usize>) -> Result<Self, ReadError> {
        Ok(Self {
            start: range
                .start
                .try_into()
                .map_err(|_| ReadError::ResourceLimit("input bytes"))?,
            end: range
                .end
                .try_into()
                .map_err(|_| ReadError::ResourceLimit("input bytes"))?,
        })
    }

    fn bytes(self, input: &[u8]) -> &[u8] {
        &input[self.start as usize..self.end as usize]
    }

    fn str(self, input: &[u8]) -> &str {
        std::str::from_utf8(self.bytes(input)).expect("read snapshot strings are validated during scan")
    }
}

#[derive(Debug, Clone)]
enum RawContent {
    None,
    Deleted,
    Json(Range<u32>),
    Binary(Span),
    String(Span),
    Embed(Span),
    Format { key: Span, value: Span },
    Type(TypeId),
    Any(Range<u32>),
    Doc { guid: Span, options: Span },
}

#[derive(Debug, Clone, Copy)]
enum RawParent {
    Root(KeyId),
    Item(Id),
    Inherit,
}

#[derive(Debug, Clone)]
struct RawNode {
    id: Id,
    len: u64,
    content_offset: u64,
    origin_left: Id,
    origin_right: Id,
    wire_parent_id: Id,
    content: RawContent,
    wire_parent_key: KeyId,
    parent_sub: KeyId,
    parent: TypeId,
    left: NodeId,
    right: NodeId,
    flags: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RawNodeKind {
    Item,
    Gc,
    Skip,
}

impl RawNode {
    const KIND_MASK: u32 = 0b11;
    const DELETED: u32 = 1 << 2;
    const COUNTABLE: u32 = 1 << 3;
    const INTEGRATED: u32 = 1 << 4;
    const ORIGIN_LEFT: u32 = 1 << 5;
    const ORIGIN_RIGHT: u32 = 1 << 6;
    const PARENT_ROOT: u32 = 1 << 7;
    const PARENT_ITEM: u32 = 1 << 8;
    const PARENT_SUB: u32 = 1 << 9;
    const PARENT: u32 = 1 << 10;
    const LEFT: u32 = 1 << 11;
    const RIGHT: u32 = 1 << 12;

    #[allow(clippy::too_many_arguments)]
    fn new(
        kind: RawNodeKind,
        id: Id,
        len: u64,
        origin_left: Option<Id>,
        origin_right: Option<Id>,
        wire_parent: RawParent,
        parent_sub: Option<KeyId>,
        content: Option<RawContent>,
        countable: bool,
        deleted: bool,
    ) -> Self {
        let mut node = Self {
            id,
            len,
            content_offset: 0,
            origin_left: origin_left.unwrap_or_default(),
            origin_right: origin_right.unwrap_or_default(),
            wire_parent_id: Id::default(),
            content: content.unwrap_or(RawContent::None),
            wire_parent_key: 0,
            parent_sub: parent_sub.unwrap_or(0),
            parent: 0,
            left: 0,
            right: 0,
            flags: kind as u32,
        };
        node.set_flag(Self::ORIGIN_LEFT, origin_left.is_some());
        node.set_flag(Self::ORIGIN_RIGHT, origin_right.is_some());
        node.set_flag(Self::PARENT_SUB, parent_sub.is_some());
        node.set_flag(Self::COUNTABLE, countable);
        node.set_flag(Self::DELETED, deleted);
        match wire_parent {
            RawParent::Root(key) => {
                node.wire_parent_key = key;
                node.flags |= Self::PARENT_ROOT;
            }
            RawParent::Item(id) => {
                node.wire_parent_id = id;
                node.flags |= Self::PARENT_ITEM;
            }
            RawParent::Inherit => {}
        }
        node
    }

    fn flag(&self, flag: u32) -> bool {
        self.flags & flag != 0
    }

    fn set_flag(&mut self, flag: u32, value: bool) {
        if value {
            self.flags |= flag;
        } else {
            self.flags &= !flag;
        }
    }

    fn kind(&self) -> RawNodeKind {
        match self.flags & Self::KIND_MASK {
            0 => RawNodeKind::Item,
            1 => RawNodeKind::Gc,
            2 => RawNodeKind::Skip,
            _ => unreachable!(),
        }
    }

    fn set_kind(&mut self, kind: RawNodeKind) {
        self.flags = (self.flags & !Self::KIND_MASK) | kind as u32;
    }

    fn origin_left(&self) -> Option<Id> {
        self.flag(Self::ORIGIN_LEFT).then_some(self.origin_left)
    }

    fn set_origin_left(&mut self, value: Option<Id>) {
        if let Some(value) = value {
            self.origin_left = value;
        }
        self.set_flag(Self::ORIGIN_LEFT, value.is_some());
    }

    fn origin_right(&self) -> Option<Id> {
        self.flag(Self::ORIGIN_RIGHT).then_some(self.origin_right)
    }

    fn set_origin_right(&mut self, value: Option<Id>) {
        if let Some(value) = value {
            self.origin_right = value;
        }
        self.set_flag(Self::ORIGIN_RIGHT, value.is_some());
    }

    fn wire_parent(&self) -> RawParent {
        if self.flag(Self::PARENT_ROOT) {
            RawParent::Root(self.wire_parent_key)
        } else if self.flag(Self::PARENT_ITEM) {
            RawParent::Item(self.wire_parent_id)
        } else {
            RawParent::Inherit
        }
    }

    fn parent_sub(&self) -> Option<KeyId> {
        self.flag(Self::PARENT_SUB).then_some(self.parent_sub)
    }

    fn set_parent_sub(&mut self, value: Option<KeyId>) {
        if let Some(value) = value {
            self.parent_sub = value;
        }
        self.set_flag(Self::PARENT_SUB, value.is_some());
    }

    fn parent(&self) -> Option<TypeId> {
        self.flag(Self::PARENT).then_some(self.parent)
    }

    fn set_parent(&mut self, value: Option<TypeId>) {
        if let Some(value) = value {
            self.parent = value;
        }
        self.set_flag(Self::PARENT, value.is_some());
    }

    fn left(&self) -> Option<NodeId> {
        self.flag(Self::LEFT).then_some(self.left)
    }

    fn set_left(&mut self, value: Option<NodeId>) {
        if let Some(value) = value {
            self.left = value;
        }
        self.set_flag(Self::LEFT, value.is_some());
    }

    fn right(&self) -> Option<NodeId> {
        self.flag(Self::RIGHT).then_some(self.right)
    }

    fn set_right(&mut self, value: Option<NodeId>) {
        if let Some(value) = value {
            self.right = value;
        }
        self.set_flag(Self::RIGHT, value.is_some());
    }

    fn integrated(&self) -> bool {
        self.flag(Self::INTEGRATED)
    }

    fn set_integrated(&mut self, value: bool) {
        self.set_flag(Self::INTEGRATED, value);
    }

    fn deleted(&self) -> bool {
        self.flag(Self::DELETED)
    }

    fn set_deleted(&mut self, value: bool) {
        self.set_flag(Self::DELETED, value);
    }

    fn countable(&self) -> bool {
        self.flag(Self::COUNTABLE)
    }

    fn set_countable(&mut self, value: bool) {
        self.set_flag(Self::COUNTABLE, value);
    }

    fn last_id(&self) -> Id {
        debug_assert!(self.len > 0);
        Id::new(self.id.client, self.id.clock + self.len - 1)
    }
}

#[derive(Debug)]
struct RawType {
    kind: YTypeKind,
    tag: Option<Span>,
    owner: Option<NodeId>,
    start: Option<NodeId>,
    map: HashMap<KeyId, NodeId>,
}

impl RawType {
    fn nested(kind: YTypeKind, tag: Option<Span>, owner: NodeId) -> Self {
        Self {
            kind,
            tag,
            owner: Some(owner),
            start: None,
            map: HashMap::default(),
        }
    }

    fn root() -> Self {
        Self {
            kind: YTypeKind::Unknown,
            tag: None,
            owner: None,
            start: None,
            map: HashMap::default(),
        }
    }
}

struct Builder {
    input: Arc<[u8]>,
    nodes: Vec<RawNode>,
    clients: ClientMap<Vec<NodeId>>,
    types: Vec<RawType>,
    roots: HashMap<KeyId, TypeId>,
    keys: KeyTable,
    parts: Vec<Span>,
    deletes: Vec<(u64, Range<u64>)>,
    limits: ReadLimits,
}

#[derive(Debug)]
enum FrozenContent {
    Any(Range<u32>),
    Binary(Span),
    String(Span),
    Format { key: Span, value: AnyId },
    Type(TypeId),
    Doc { guid: Span, options: AnyId },
}

#[derive(Debug)]
struct FrozenValue {
    content: FrozenContent,
    content_offset: u64,
    len: u64,
}

#[derive(Debug)]
struct FrozenType {
    kind: YTypeKind,
    tag: Option<Span>,
    map: Vec<(KeyId, FrozenValue)>,
    list: Vec<FrozenValue>,
    len: u64,
}

#[derive(Debug)]
pub struct ReadDoc {
    input: Arc<[u8]>,
    roots: HashMap<KeyId, TypeId>,
    keys: KeyTable,
    any: Vec<super::Any>,
    types: Vec<FrozenType>,
}

#[derive(Debug, Default)]
struct KeyTable {
    spans: Vec<Span>,
    buckets: HashMap<u64, Vec<KeyId>>,
}

impl KeyTable {
    fn intern(&mut self, input: &[u8], span: Span) -> Result<KeyId, ReadError> {
        let bytes = span.bytes(input);
        let hash = hash_key(bytes);
        if let Some(ids) = self.buckets.get(&hash) {
            for id in ids {
                if self.spans[*id as usize].bytes(input) == bytes {
                    return Ok(*id);
                }
            }
        }
        let id = self
            .spans
            .len()
            .try_into()
            .map_err(|_| ReadError::ResourceLimit("map keys"))?;
        self.spans.push(span);
        self.buckets.entry(hash).or_default().push(id);
        Ok(id)
    }

    fn find(&self, input: &[u8], key: &str) -> Option<KeyId> {
        self.buckets.get(&hash_key(key.as_bytes())).and_then(|ids| {
            ids.iter()
                .copied()
                .find(|id| self.spans[*id as usize].bytes(input) == key.as_bytes())
        })
    }

    fn str<'a>(&self, input: &'a [u8], id: KeyId) -> &'a str {
        self.spans[id as usize].str(input)
    }
}

fn hash_key(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100_0000_01b3)
    })
}

impl ReadDoc {
    /// Builds an immutable document from a complete Update V1 snapshot.
    ///
    /// `Vec<u8>` transfers its bytes and `Arc<[u8]>` shares them. Converting a
    /// borrowed slice to `Arc<[u8]>` copies the input. The update must resolve
    /// from an empty state; a valid incremental update can return
    /// [`ReadError::IncompleteSnapshot`].
    pub fn from_full_update_v1(input: impl Into<Arc<[u8]>>) -> Result<Self, ReadError> {
        Self::from_full_update_v1_with_limits(input, ReadLimits::default())
    }

    /// Builds an immutable document from a complete Update V1 snapshot under
    /// explicit resource limits.
    pub fn from_full_update_v1_with_limits(input: impl Into<Arc<[u8]>>, limits: ReadLimits) -> Result<Self, ReadError> {
        let builder = scan::scan(input.into(), limits)?;
        resolve::resolve(builder)
    }

    /// Returns all root names in unspecified order without allocating.
    pub fn root_names(&self) -> impl Iterator<Item = &str> {
        self.roots.keys().map(|key| self.keys.str(&self.input, *key))
    }

    /// Projects an existing root as a map according to caller-owned schema.
    ///
    /// Update V1 does not encode root kind; `None` only means the name does not
    /// exist.
    pub fn map(&self, name: &str) -> Option<ReadMap<'_>> {
        self.root(name).map(ReadMap::new)
    }

    /// Projects an existing root as an array according to caller-owned schema.
    pub fn array(&self, name: &str) -> Option<ReadArray<'_>> {
        self.root(name).map(ReadArray::new)
    }

    /// Projects an existing root as text according to caller-owned schema.
    pub fn text(&self, name: &str) -> Option<ReadText<'_>> {
        self.root(name).map(ReadText::new)
    }

    fn root(&self, name: &str) -> Option<(&Self, TypeId)> {
        let key = self.keys.find(&self.input, name)?;
        let id = self.roots.get(&key).copied()?;
        Some((self, id))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use rand::{RngExt, SeedableRng};
    use rand_chacha::ChaCha8Rng;
    use serde_json::{Map as JsonMap, Value as JsonValue};
    use smol_str::SmolStr;

    use super::*;
    use crate::{
        Any, Content, CrdtWrite, CrdtWriter, Doc, DocOptions, Id, Map, RawEncoder, StateVector, TextAttributes,
        TextDeltaOp, TextInsert, Update, Value,
        doc::{DeleteSet, HashMap, Item, Node, Parent, Somr, YType, YTypeRef},
    };

    type UpdateCase = (&'static str, fn() -> Vec<u8>);

    fn map_json(map: ReadMap<'_>) -> JsonValue {
        JsonValue::Object(
            map.iter()
                .map(|(key, value)| (key.to_string(), value_json(value)))
                .collect::<JsonMap<_, _>>(),
        )
    }

    fn value_json(value: ReadValue<'_>) -> JsonValue {
        match value {
            ReadValue::Any(value) => serde_json::to_value(value.to_owned()).unwrap(),
            ReadValue::Array(value) => JsonValue::Array(value.iter().map(value_json).collect()),
            ReadValue::Map(value) => map_json(value),
            ReadValue::Text(value) => JsonValue::String(format!("{:?}", value.to_delta())),
            ReadValue::Xml { kind, tag, map, array } => serde_json::json!({
                "kind": kind.as_str(),
                "tag": tag,
                "map": map_json(map),
                "list": array.iter().map(value_json).collect::<Vec<_>>(),
            }),
            ReadValue::Doc { guid, options } => serde_json::json!({
                "guid": guid,
                "options": options.to_owned(),
            }),
        }
    }

    fn mutable_value_json(value: Value) -> JsonValue {
        match value {
            Value::Any(value) => serde_json::to_value(value).unwrap(),
            Value::Array(value) => JsonValue::Array(value.iter().map(mutable_value_json).collect()),
            Value::Map(value) => mutable_map_json(value),
            Value::Text(value) => JsonValue::String(format!("{:?}", value.to_delta())),
            Value::Doc(value) => serde_json::json!({
                "guid": value.guid(),
                "options": Any::from(value.options().clone()),
            }),
            Value::XMLElement(value) => mutable_xml_json(&value.0),
            Value::XMLFragment(value) => mutable_xml_json(&value.0),
            Value::XMLHook(value) => mutable_xml_json(&value.0),
            Value::XMLText(value) => mutable_xml_json(&value.0),
        }
    }

    fn mutable_content_json(content: &Content) -> JsonValue {
        match content {
            Content::Doc { guid, opts } => serde_json::json!({
                "guid": guid,
                "options": opts,
            }),
            content => mutable_value_json(Value::from(content)),
        }
    }

    fn mutable_map_json(map: Map) -> JsonValue {
        mutable_type_map_json(&map.0.ty().unwrap())
    }

    fn mutable_type_map_json(ty: &YType) -> JsonValue {
        JsonValue::Object(
            ty.map
                .iter()
                .filter_map(|(key, item)| {
                    let item = item.get()?;
                    (!item.deleted()).then(|| (key.to_string(), mutable_content_json(&item.content)))
                })
                .collect(),
        )
    }

    fn mutable_xml_json(ty: &YTypeRef) -> JsonValue {
        let ty = ty.ty().unwrap();
        let mut list = Vec::new();
        let mut cursor = ty.start.clone();
        while let Some(item) = cursor.get() {
            let right = item.right.clone();
            if !(item.deleted() || matches!(item.content, Content::Format { .. })) {
                list.push(mutable_content_json(&item.content));
            }
            cursor = right;
        }
        serde_json::json!({
            "kind": ty.kind().as_str(),
            "tag": ty.name.as_deref(),
            "map": mutable_type_map_json(&ty),
            "list": list,
        })
    }

    fn assert_read_matches_mutable(update: &[u8], case: &str) {
        let readonly = ReadDoc::from_full_update_v1(update).unwrap();
        // each projection casts the root's kind inside the mutable doc, so
        // every projection kind needs its own pristine doc
        let mutables = [
            Doc::try_from_binary_v1(update).unwrap(),
            Doc::try_from_binary_v1(update).unwrap(),
            Doc::try_from_binary_v1(update).unwrap(),
        ];
        let read_roots = readonly.root_names().map(str::to_owned).collect::<BTreeSet<_>>();
        let mutable_roots = mutables[0].keys().into_iter().collect::<BTreeSet<_>>();
        assert_eq!(read_roots, mutable_roots, "{case} root names");

        for key in &read_roots {
            assert_eq!(
                map_json(readonly.map(key).unwrap()),
                mutable_map_json(mutables[0].get_map(key).unwrap()),
                "{case} map root {key}"
            );

            assert_eq!(
                JsonValue::Array(readonly.array(key).unwrap().iter().map(value_json).collect()),
                JsonValue::Array(
                    mutables[1]
                        .get_or_create_array(key)
                        .unwrap()
                        .iter()
                        .map(mutable_value_json)
                        .collect()
                ),
                "{case} array root {key}"
            );

            assert_eq!(
                readonly.text(key).unwrap().to_delta(),
                mutables[2].get_or_create_text(key).unwrap().to_delta(),
                "{case} text root {key}"
            );
        }
    }

    fn item(clock: u64, content: Content, parent: Option<Parent>, parent_sub: Option<&str>) -> Node {
        Node::from(Item::new(
            Id::new(1, clock),
            content,
            Somr::none(),
            Somr::none(),
            parent,
            parent_sub.map(SmolStr::from),
        ))
    }

    fn root_item(clock: u64, content: Content, root: &str, parent_sub: Option<&str>) -> Node {
        item(clock, content, Some(Parent::String(root.into())), parent_sub)
    }

    fn update_bytes(items: Vec<Node>, delete_set: DeleteSet) -> Vec<u8> {
        let mut update = Update::default();
        update.structs.insert(1, items.into());
        update.delete_set = delete_set;
        update.encode_v1().unwrap()
    }

    fn any_spectrum_update() -> Vec<u8> {
        let doc = Doc::new();
        let mut map = doc.get_or_create_map("map").unwrap();
        map.insert("null".into(), Any::Null).unwrap();
        map.insert("undefined".into(), Any::Undefined).unwrap();
        map.insert("false".into(), Any::False).unwrap();
        map.insert("true".into(), Any::True).unwrap();
        map.insert("int".into(), Any::Integer(-42)).unwrap();
        map.insert("bigint".into(), Any::BigInt64(i64::MAX)).unwrap();
        map.insert("f32".into(), Any::Float32(1.5.into())).unwrap();
        map.insert("f64".into(), Any::Float64((-0.25).into())).unwrap();
        map.insert("string".into(), Any::String("hello 😀".into())).unwrap();
        map.insert("binary".into(), Any::Binary(vec![0, 159, 146, 150]))
            .unwrap();
        map.insert(
            "array".into(),
            Any::Array(vec![Any::Integer(1), "two".into(), Any::True]),
        )
        .unwrap();
        map.insert(
            "object".into(),
            Any::Object(Box::new(HashMap::from_iter([
                ("nested".into(), Any::Array(vec![Any::Null, Any::Undefined])),
                (
                    "deep".into(),
                    Any::Object(Box::new(HashMap::from_iter([(
                        "leaf".into(),
                        Any::Float64(0.5.into()),
                    )]))),
                ),
            ]))),
        )
        .unwrap();
        let mut array = doc.get_or_create_array("array").unwrap();
        array.push(Any::Binary(vec![1, 2, 3])).unwrap();
        array.push(Any::Array(vec![Any::Null])).unwrap();
        doc.encode_update_v1().unwrap()
    }

    fn embed_text_update() -> Vec<u8> {
        let doc = Doc::new();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.apply_delta(&[
            TextDeltaOp::Insert {
                insert: TextInsert::Text("a=".into()),
                format: None,
            },
            TextDeltaOp::Insert {
                insert: TextInsert::Embed(vec![Any::Integer(42), Any::String("x".into())]),
                format: None,
            },
        ])
        .unwrap();
        doc.encode_update_v1().unwrap()
    }

    fn surrogate_pair_update() -> Vec<u8> {
        let doc = Doc::new();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "a😀b🎉c").unwrap();
        text.remove(3, 2).unwrap();
        doc.encode_update_v1().unwrap()
    }

    fn misc_content_update() -> Vec<u8> {
        update_bytes(
            vec![
                root_item(
                    0,
                    Content::Doc {
                        guid: "sub".into(),
                        opts: Box::new(Any::from(DocOptions::new().with_guid("sub".into()))),
                    },
                    "docs",
                    Some("sub"),
                ),
                root_item(1, Content::Binary(vec![0, 159, 146, 150]), "docs", Some("blob")),
                root_item(
                    2,
                    Content::Json(vec![Some("a".into()), None, Some("1".into())]),
                    "docs",
                    Some("json"),
                ),
            ],
            DeleteSet::default(),
        )
    }

    fn xml_update() -> Vec<u8> {
        update_bytes(
            vec![
                root_item(
                    0,
                    Content::Type(YTypeRef::new(YTypeKind::XMLElement, Some("div".into()))),
                    "xml",
                    Some("root"),
                ),
                item(
                    1,
                    Content::Any(vec![Any::String("container".into())]),
                    Some(Parent::Id(Id::new(1, 0))),
                    Some("class"),
                ),
                item(
                    2,
                    Content::Type(YTypeRef::new(YTypeKind::XMLText, None)),
                    Some(Parent::Id(Id::new(1, 0))),
                    None,
                ),
                item(
                    3,
                    Content::String("hello".into()),
                    Some(Parent::Id(Id::new(1, 2))),
                    None,
                ),
                item(
                    4,
                    Content::Type(YTypeRef::new(YTypeKind::XMLElement, Some("span".into()))),
                    Some(Parent::Id(Id::new(1, 0))),
                    None,
                ),
                item(
                    5,
                    Content::Type(YTypeRef::new(YTypeKind::XMLText, None)),
                    Some(Parent::Id(Id::new(1, 4))),
                    None,
                ),
                item(
                    6,
                    Content::String("inner".into()),
                    Some(Parent::Id(Id::new(1, 5))),
                    None,
                ),
                root_item(
                    7,
                    Content::Type(YTypeRef::new(YTypeKind::XMLFragment, None)),
                    "xml-fragment",
                    None,
                ),
                root_item(
                    8,
                    Content::Type(YTypeRef::new(YTypeKind::XMLHook, Some("hook".into()))),
                    "xml-hook",
                    None,
                ),
                root_item(
                    9,
                    Content::Type(YTypeRef::new(YTypeKind::XMLText, None)),
                    "xml-text",
                    None,
                ),
                item(
                    10,
                    Content::String("tail".into()),
                    Some(Parent::Id(Id::new(1, 9))),
                    None,
                ),
            ],
            DeleteSet::default(),
        )
    }

    fn gc_deleted_subtree() -> Vec<u8> {
        let doc = Doc::new();
        let mut map = doc.get_or_create_map("map").unwrap();
        map.insert("keep".into(), "alive").unwrap();
        let mut child = doc.create_map().unwrap();
        child.insert("a".into(), 1).unwrap();
        child.insert("b".into(), 2).unwrap();
        map.insert("drop".into(), child).unwrap();
        map.remove("drop");
        doc.gc().unwrap();
        let bytes = doc.encode_update_v1().unwrap();
        let update = Update::decode_v1(&bytes).unwrap();
        assert!(update.structs.values().flatten().any(Node::is_gc));
        bytes
    }

    fn deleted_text_content() -> Vec<u8> {
        let doc = Doc::new();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "hello world").unwrap();
        text.remove(5, 6).unwrap();
        let bytes = doc.encode_update_v1().unwrap();
        assert!(!Update::decode_v1(&bytes).unwrap().delete_set.is_empty());
        bytes
    }

    fn gc_deleted_text_content() -> Vec<u8> {
        let doc = Doc::new();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "hello world").unwrap();
        text.remove(5, 6).unwrap();
        doc.gc().unwrap();
        let bytes = doc.encode_update_v1().unwrap();
        let update = Update::decode_v1(&bytes).unwrap();
        assert!(update.structs.values().flatten().any(|node| {
            node.as_item()
                .get()
                .is_some_and(|item| matches!(item.content, Content::Deleted(_)))
        }));
        bytes
    }

    fn map_overwrite() -> Vec<u8> {
        let doc1 = Doc::with_client(1);
        doc1.get_or_create_map("map")
            .unwrap()
            .insert("key".into(), "from-1")
            .unwrap();
        let doc2 = Doc::with_client(2);
        doc2.get_or_create_map("map")
            .unwrap()
            .insert("key".into(), "from-2")
            .unwrap();
        Update::merge(
            [doc1.encode_update_v1().unwrap(), doc2.encode_update_v1().unwrap()]
                .map(|bytes| Update::decode_v1(bytes).unwrap()),
        )
        .encode_v1()
        .unwrap()
    }

    fn concurrent_array_insert() -> Vec<u8> {
        let base = Doc::with_client(9);
        base.get_or_create_array("array").unwrap().push("base").unwrap();
        let base_update = base.encode_update_v1().unwrap();
        let base_state = base.get_state_vector();

        let mut increments = vec![Update::decode_v1(&base_update).unwrap()];
        for (index, client) in [1, 2].into_iter().enumerate() {
            let mut replica = Doc::with_client(client);
            replica.apply_update_from_binary_v1(&base_update).unwrap();
            replica
                .get_or_create_array("array")
                .unwrap()
                .insert(1, format!("r{index}"))
                .unwrap();
            increments.push(Update::decode_v1(replica.encode_state_as_update_v1(&base_state).unwrap()).unwrap());
        }
        Update::merge(increments).encode_v1().unwrap()
    }

    fn mid_struct_split() -> Vec<u8> {
        let base = Doc::with_client(9);
        base.get_or_create_text("text").unwrap().insert(0, "abcdef").unwrap();
        let base_update = base.encode_update_v1().unwrap();

        let mut replica1 = Doc::with_client(1);
        replica1.apply_update_from_binary_v1(&base_update).unwrap();
        let base_state = replica1.get_state_vector();
        replica1.get_or_create_text("text").unwrap().insert(3, "XY").unwrap();
        let inc1 = replica1.encode_state_as_update_v1(&base_state).unwrap();

        let mut replica2 = Doc::with_client(2);
        replica2.apply_update_from_binary_v1(&base_update).unwrap();
        let base_state = replica2.get_state_vector();
        replica2.get_or_create_text("text").unwrap().insert(4, "Z").unwrap();
        let inc2 = replica2.encode_state_as_update_v1(&base_state).unwrap();

        // insert again after seeing the other replica, origins point into struct
        // middles
        replica1.apply_update_from_binary_v1(&inc2).unwrap();
        let state = replica1.get_state_vector();
        replica1.get_or_create_text("text").unwrap().insert(1, "!").unwrap();
        let inc3 = replica1.encode_state_as_update_v1(&state).unwrap();

        Update::merge([base_update, inc1, inc2, inc3].map(|bytes| Update::decode_v1(bytes).unwrap()))
            .encode_v1()
            .unwrap()
    }

    fn overlapping_delete_ranges() -> Vec<u8> {
        let mut encoder = RawEncoder::default();
        encoder.write_var_u64(1).unwrap();
        encoder.write_var_u64(1).unwrap();
        encoder.write_var_u64(1).unwrap();
        encoder.write_var_u64(0).unwrap();
        root_item(0, Content::String("hello world".into()), "text", None)
            .write(&mut encoder)
            .unwrap();
        // unsorted overlapping ranges: the read side must normalize before applying
        encoder.write_var_u64(1).unwrap();
        encoder.write_var_u64(1).unwrap();
        encoder.write_var_u64(3).unwrap();
        for range in [5..9, 3..8, 9..10] {
            encoder.write_var_u64(range.start).unwrap();
            encoder.write_var_u64(range.end - range.start).unwrap();
        }
        encoder.into_inner()
    }

    #[test]
    #[cfg_attr(loom, ignore)]
    fn updates_match_mutable_views() {
        let cases: [UpdateCase; 13] = [
            ("empty", || Doc::new().encode_update_v1().unwrap()),
            ("any scalars and containers", any_spectrum_update),
            ("text with embeds", embed_text_update),
            ("surrogate pairs", surrogate_pair_update),
            ("subdoc binary json", misc_content_update),
            ("xml all kinds", xml_update),
            ("gc of deleted subtree", gc_deleted_subtree),
            ("deleted text content", deleted_text_content),
            ("gc turns tombstones into Deleted content", gc_deleted_text_content),
            ("map overwrite by two clients", map_overwrite),
            ("concurrent array inserts", concurrent_array_insert),
            ("mid-struct split origins", mid_struct_split),
            ("overlapping delete ranges", overlapping_delete_ranges),
        ];
        for (name, build) in cases {
            assert_read_matches_mutable(&build(), name);
        }

        let empty = ReadDoc::from_full_update_v1(Doc::new().encode_update_v1().unwrap()).unwrap();
        assert_eq!(empty.root_names().count(), 0);
    }

    #[test]
    #[cfg_attr(loom, ignore)]
    fn skip_structs_mark_snapshot_incomplete() {
        // merge fills coverage holes of a client with Skip structs, so an update
        // carrying a Skip can never resolve from an empty state: the read side
        // rejects it while the mutable side parks the tail as pending.
        let doc1 = Doc::with_client(1);
        doc1.get_or_create_text("text").unwrap().insert(0, "ab").unwrap();
        let low = Update::decode_v1(doc1.encode_update_v1().unwrap()).unwrap();
        doc1.get_or_create_text("text").unwrap().insert(2, "cd").unwrap();
        let middle = Update::decode_v1(doc1.encode_state_as_update_v1(&StateVector::from([(1, 2)])).unwrap()).unwrap();
        doc1.get_or_create_text("text").unwrap().insert(4, "ef").unwrap();
        let high = Update::decode_v1(doc1.encode_state_as_update_v1(&StateVector::from([(1, 4)])).unwrap()).unwrap();

        let doc2 = Doc::with_client(2);
        doc2.get_or_create_map("map").unwrap().insert("key".into(), 1).unwrap();
        let other = Update::decode_v1(doc2.encode_update_v1().unwrap()).unwrap();

        let gapped = Update::merge([low, high, other]);
        assert!(gapped.structs.get(&1).unwrap().iter().any(Node::is_skip));

        let bytes = gapped.encode_v1().unwrap();
        assert!(Doc::try_from_binary_v1(&bytes).unwrap().has_pending_updates());
        assert_eq!(
            ReadDoc::from_full_update_v1(bytes).unwrap_err().to_string(),
            "incomplete snapshot: client clock gap"
        );

        // filling the hole replaces the Skip with real structs and the differential
        // holds
        let complete = Update::merge([gapped, middle]).encode_v1().unwrap();
        assert_read_matches_mutable(&complete, "skip gap filled");
    }

    #[test]
    #[cfg_attr(loom, ignore)]
    fn random_multi_client_histories_match() {
        let mut rng = ChaCha8Rng::seed_from_u64(0x5EED);

        let base = Doc::with_client(9);
        base.get_or_create_text("text").unwrap().insert(0, "base").unwrap();
        base.get_or_create_map("map").unwrap().insert("k0".into(), 0).unwrap();
        base.get_or_create_array("array").unwrap().push("base").unwrap();
        let base_update = base.encode_update_v1().unwrap();

        let mut replicas = [1, 2, 3].map(|client| {
            let mut doc = Doc::with_client(client);
            doc.apply_update_from_binary_v1(&base_update).unwrap();
            doc
        });

        for _ in 0..50 {
            let index = rng.random_range(0..replicas.len());
            let doc = &mut replicas[index];
            match rng.random_range(0..5) {
                0 => {
                    let mut text = doc.get_or_create_text("text").unwrap();
                    let position = rng.random_range(0..=text.len());
                    text.insert(position, format!("t{index}")).unwrap();
                }
                1 => {
                    let mut text = doc.get_or_create_text("text").unwrap();
                    if !text.is_empty() {
                        let start = rng.random_range(0..text.len());
                        text.remove(start, 1).unwrap();
                    }
                }
                2 => {
                    let mut map = doc.get_or_create_map("map").unwrap();
                    let key = format!("k{}", rng.random_range(0..5));
                    let value = match rng.random_range(0..3) {
                        0 => Any::Integer(rng.random_range(-100..100)),
                        1 => Any::String(format!("v{}", rng.random_range(0..10))),
                        _ => Any::True,
                    };
                    map.insert(key, value).unwrap();
                }
                3 => {
                    let mut array = doc.get_or_create_array("array").unwrap();
                    let position = rng.random_range(0..=array.len());
                    array.insert(position, Any::Integer(rng.random_range(0..100))).unwrap();
                }
                _ => {
                    let mut array = doc.get_or_create_array("array").unwrap();
                    if !array.is_empty() {
                        let start = rng.random_range(0..array.len());
                        array.remove(start, 1).unwrap();
                    }
                }
            }

            if rng.random_bool(0.5) {
                let source = rng.random_range(0..replicas.len());
                let target = rng.random_range(0..replicas.len());
                if source != target {
                    let update = replicas[source]
                        .encode_state_as_update_v1(&replicas[target].get_state_vector())
                        .unwrap();
                    replicas[target].apply_update_from_binary_v1(update).unwrap();
                }
            }
        }

        for _ in 0..3 {
            for source in 0..replicas.len() {
                for target in 0..replicas.len() {
                    if source != target {
                        let update = replicas[source]
                            .encode_state_as_update_v1(&replicas[target].get_state_vector())
                            .unwrap();
                        replicas[target].apply_update_from_binary_v1(update).unwrap();
                    }
                }
            }
        }

        let states = replicas.iter().map(Doc::get_state_vector).collect::<Vec<_>>();
        assert!(
            states.windows(2).all(|pair| pair[0] == pair[1]),
            "replicas diverged: {states:?}"
        );
        assert!(replicas.iter().all(|doc| !doc.has_pending_updates()));

        for doc in &replicas {
            assert_read_matches_mutable(&doc.encode_update_v1().unwrap(), "random replica");
        }
    }

    #[test]
    #[cfg_attr(loom, ignore)]
    fn invalid_or_incomplete_updates_are_classified() {
        let mut dependent = Item::new(
            Id::new(1, 0),
            Content::String("x".into()),
            Somr::none(),
            Somr::none(),
            Some(Parent::String("text".into())),
            None,
        );
        dependent.origin_left_id = Some(Id::new(99, 0));
        let missing_dependency = update_bytes(vec![Node::from(dependent)], DeleteSet::default());

        // wire-legal but the types nest in a cycle: the failure surfaces in
        // resolve's type_is_ancestor walk, not during decode
        let cyclic = update_bytes(
            vec![
                item(
                    0,
                    Content::Type(YTypeRef::new(YTypeKind::Map, None)),
                    Some(Parent::Id(Id::new(1, 1))),
                    None,
                ),
                item(
                    1,
                    Content::Type(YTypeRef::new(YTypeKind::Map, None)),
                    Some(Parent::Id(Id::new(1, 0))),
                    None,
                ),
            ],
            DeleteSet::default(),
        );

        let mut beyond_state = DeleteSet::default();
        beyond_state.add_range(1, 0..100);
        let deletes_beyond_state = update_bytes(
            vec![root_item(0, Content::String("hi".into()), "text", None)],
            beyond_state,
        );

        let mut unknown_client = DeleteSet::default();
        unknown_client.add_range(99, 0..1);
        let deletes_unknown_client = update_bytes(
            vec![root_item(0, Content::String("hi".into()), "text", None)],
            unknown_client,
        );

        // a valid incremental update is an incomplete snapshot from the empty state
        let incremental = {
            let doc = Doc::new();
            let mut text = doc.get_or_create_text("text").unwrap();
            text.insert(0, "base").unwrap();
            let state = doc.get_state_vector();
            text.insert(4, " increment").unwrap();
            doc.encode_state_as_update_v1(&state).unwrap()
        };

        let cases = [
            ("cyclic type parent", cyclic, "invalid update: Invalid parent"),
            (
                "missing struct dependency",
                missing_dependency,
                "incomplete snapshot: missing struct dependency",
            ),
            (
                "incremental update",
                incremental,
                "incomplete snapshot: client clock gap",
            ),
            (
                "delete range beyond state",
                deletes_beyond_state,
                "incomplete snapshot: delete-set range exceeds state",
            ),
            (
                "delete set unknown client",
                deletes_unknown_client,
                "incomplete snapshot: delete-set client not found",
            ),
        ];
        for (name, update, expected) in cases {
            let error = ReadDoc::from_full_update_v1(update).unwrap_err();
            assert_eq!(error.to_string(), expected, "{name}");
        }
    }

    #[test]
    #[cfg_attr(loom, ignore)]
    fn reads_map_array_text_and_nested_types() {
        let doc = Doc::new();
        let mut map = doc.get_or_create_map("map").unwrap();
        map.insert("title".into(), "hello").unwrap();
        map.insert("visible".into(), true).unwrap();

        let mut child = doc.create_map().unwrap();
        child.insert("value".into(), 42).unwrap();
        map.insert("child".into(), child).unwrap();

        let mut array = doc.get_or_create_array("array").unwrap();
        array.push("a").unwrap();
        array.push("b").unwrap();
        array.remove(0, 1).unwrap();

        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "hello world").unwrap();
        text.remove(5, 1).unwrap();

        let mut attributes = TextAttributes::new();
        attributes.insert("bold".to_string(), Any::True);
        let mut formatted = doc.get_or_create_text("formatted").unwrap();
        formatted
            .apply_delta(&[
                TextDeltaOp::Insert {
                    insert: TextInsert::Text("bold".to_string()),
                    format: Some(attributes),
                },
                TextDeltaOp::Insert {
                    insert: TextInsert::Text(" plain".to_string()),
                    format: None,
                },
            ])
            .unwrap();

        let update = doc.encode_update_v1().unwrap();
        let snapshot = ReadDoc::from_full_update_v1(update.clone()).unwrap();
        let map = snapshot.map("map").unwrap();
        assert_eq!(map.get("title").unwrap().as_any().unwrap().as_str(), Some("hello"));
        assert_eq!(map.get("visible").unwrap().as_any().unwrap().as_bool(), Some(true));
        assert_eq!(
            map.get("child")
                .unwrap()
                .as_map()
                .unwrap()
                .get("value")
                .unwrap()
                .as_any()
                .unwrap()
                .as_i64(),
            Some(42)
        );
        let array = snapshot.array("array").unwrap();
        assert_eq!(array.iter().next().unwrap().as_any().unwrap().as_str(), Some("b"));
        let text = snapshot.text("text").unwrap();
        let runs = text
            .runs()
            .filter_map(|run| match run {
                ReadTextRun::Text(value) => Some(value),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(runs, ["hello", "world"]);
        assert_eq!(text.to_string(), "helloworld");
        assert_eq!(snapshot.text("formatted").unwrap().to_delta(), formatted.to_delta());
        assert_eq!(
            snapshot.root_names().collect::<BTreeSet<_>>(),
            ["array", "formatted", "map", "text"].into_iter().collect()
        );

        assert!(map.get("missing").is_none());
    }

    #[test]
    #[cfg_attr(any(miri, loom), ignore)]
    fn fixtures_match_mutable_views() {
        let fixtures: [&[u8]; 5] = [
            include_bytes!("../../fixtures/basic.bin"),
            include_bytes!("../../fixtures/database.bin"),
            include_bytes!("../../fixtures/large.bin"),
            include_bytes!("../../fixtures/with-subdoc.bin"),
            include_bytes!("../../fixtures/edge-case-left-right-same-node.bin"),
        ];

        for (index, fixture) in fixtures.into_iter().enumerate() {
            assert_read_matches_mutable(fixture, &format!("fixture {index}"));
        }
    }

    #[test]
    fn compact_layout_sizes() {
        assert!(std::mem::size_of::<RawNode>() <= 128);
        assert!(std::mem::size_of::<RawContent>() <= 24);
        assert!(std::mem::size_of::<RawType>() <= 96);
        assert!(std::mem::size_of::<FrozenValue>() <= 32);
    }

    #[test]
    fn read_limits_are_enforced() {
        let fixture = include_bytes!("../../fixtures/basic.bin");
        let limits = ReadLimits {
            max_input_bytes: fixture.len() - 1,
            ..ReadLimits::default()
        };
        assert!(matches!(
            ReadDoc::from_full_update_v1_with_limits(fixture.as_slice(), limits),
            Err(ReadError::ResourceLimit("input bytes"))
        ));

        let limits = ReadLimits {
            max_structs: 0,
            ..ReadLimits::default()
        };
        assert!(matches!(
            ReadDoc::from_full_update_v1_with_limits(fixture.as_slice(), limits),
            Err(ReadError::ResourceLimit("structs"))
        ));
    }
}
