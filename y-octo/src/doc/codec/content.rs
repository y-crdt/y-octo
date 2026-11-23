#[cfg(feature = "debug")]
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

use super::*;

#[cfg(feature = "debug")]
static CLOCK_LEN_CALLS: AtomicU64 = AtomicU64::new(0);
#[cfg(feature = "debug")]
static STRING_CLOCK_LEN_CALLS: AtomicU64 = AtomicU64::new(0);
#[cfg(feature = "debug")]
static STRING_BYTES_SCANNED: AtomicU64 = AtomicU64::new(0);

#[cfg(feature = "debug")]
pub(crate) fn clock_len_counters() -> (u64, u64, u64) {
    (
        CLOCK_LEN_CALLS.load(AtomicOrdering::Relaxed),
        STRING_CLOCK_LEN_CALLS.load(AtomicOrdering::Relaxed),
        STRING_BYTES_SCANNED.load(AtomicOrdering::Relaxed),
    )
}

#[cfg(feature = "debug")]
pub(crate) fn reset_clock_len_counters() {
    CLOCK_LEN_CALLS.store(0, AtomicOrdering::Relaxed);
    STRING_CLOCK_LEN_CALLS.store(0, AtomicOrdering::Relaxed);
    STRING_BYTES_SCANNED.store(0, AtomicOrdering::Relaxed);
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct FormatContent {
    pub key: String,
    pub value: Any,
}

#[derive(Clone, Debug)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub(crate) struct DocContent {
    pub guid: String,
    pub opts: Any,
}

#[derive(Clone)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub(crate) enum Content {
    Deleted(u64),
    Json(Vec<Option<String>>),
    Binary(Vec<u8>),
    String(String),
    #[cfg_attr(test, proptest(skip))]
    Embed(Box<Any>),
    #[cfg_attr(test, proptest(skip))]
    Format(Box<FormatContent>),
    /// A type of the store holding the item, by its slot there.
    #[cfg_attr(test, proptest(skip))]
    Type(TypeIdx),
    Any(Vec<Any>),
    Doc(Box<DocContent>),
}

impl From<Any> for Content {
    fn from(value: Any) -> Self {
        match value {
            Any::Undefined
            | Any::Null
            | Any::Integer(_)
            | Any::Float32(_)
            | Any::Float64(_)
            | Any::BigInt64(_)
            | Any::False
            | Any::True
            | Any::String(_)
            | Any::Object(_) => Content::Any(vec![value; 1]),
            Any::Array(v) => Content::Any(v),
            Any::Binary(b) => Content::Binary(b),
        }
    }
}

impl PartialEq for Content {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Deleted(len1), Self::Deleted(len2)) => len1 == len2,
            (Self::Json(vec1), Self::Json(vec2)) => vec1 == vec2,
            (Self::Binary(vec1), Self::Binary(vec2)) => vec1 == vec2,
            (Self::String(str1), Self::String(str2)) => str1 == str2,
            (Self::Embed(json1), Self::Embed(json2)) => json1 == json2,
            (Self::Format(a), Self::Format(b)) => a == b,
            (Self::Any(any1), Self::Any(any2)) => any1 == any2,
            (Self::Doc(a), Self::Doc(b)) => a.guid == b.guid,
            (Self::Type(ty1), Self::Type(ty2)) => ty1 == ty2,
            _ => false,
        }
    }
}

impl std::fmt::Debug for Content {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Deleted(arg0) => f.debug_tuple("Deleted").field(arg0).finish(),
            Self::Json(arg0) => f
                .debug_tuple("JSON")
                .field(&format!("Vec [len: {}]", arg0.len()))
                .finish(),
            Self::Binary(arg0) => f
                .debug_tuple("Binary")
                .field(&format!("Binary [len: {}]", arg0.len()))
                .finish(),
            Self::String(arg0) => f.debug_tuple("String").field(arg0).finish(),
            Self::Embed(arg0) => f.debug_tuple("Embed").field(arg0).finish(),
            Self::Format(format) => format.fmt(f),
            Self::Type(arg0) => f.debug_tuple("Type").field(arg0).finish(),
            Self::Any(arg0) => f.debug_tuple("Any").field(arg0).finish(),
            Self::Doc(doc) => doc.fmt(f),
        }
    }
}

impl Content {
    pub fn format(key: String, value: Any) -> Self {
        Self::Format(Box::new(FormatContent { key, value }))
    }

    pub fn doc(guid: String, opts: Any) -> Self {
        Self::Doc(Box::new(DocContent { guid, opts }))
    }

    pub fn as_format(&self) -> Option<(&String, &Any)> {
        match self {
            Self::Format(format) => Some((&format.key, &format.value)),
            _ => None,
        }
    }

    /// The content as written to the wire. `types` is the arena of the store
    /// holding the item.
    pub(crate) fn view<'a>(&'a self, types: &'a TypeArena) -> JwstCodecResult<ContentView<'a>> {
        Ok(match self {
            Self::Deleted(v) => ContentView::Deleted(*v),
            Self::Json(v) => ContentView::Json(v),
            Self::Binary(v) => ContentView::Binary(v),
            Self::String(v) => ContentView::String(v),
            Self::Embed(v) => ContentView::Embed(v),
            Self::Any(v) => ContentView::Any(v),
            Self::Format(format) => ContentView::Format {
                key: &format.key,
                value: &format.value,
            },
            Self::Doc(doc) => ContentView::Doc {
                guid: &doc.guid,
                opts: &doc.opts,
            },
            Self::Type(ty) => {
                let ty = types
                    .get(*ty)
                    .ok_or(JwstCodecError::InvalidStructType("released y type"))?;
                ContentView::Type {
                    kind: ty.kind(),
                    name: ty.name(),
                }
            }
        })
    }
    pub fn clock_len(&self) -> u64 {
        #[cfg(feature = "debug")]
        {
            CLOCK_LEN_CALLS.fetch_add(1, AtomicOrdering::Relaxed);
            if let Self::String(string) = self {
                STRING_CLOCK_LEN_CALLS.fetch_add(1, AtomicOrdering::Relaxed);
                STRING_BYTES_SCANNED.fetch_add(string.len() as u64, AtomicOrdering::Relaxed);
            }
        }
        match self {
            Self::Deleted(len) => *len,
            Self::Json(strings) => strings.len() as u64,
            // TODO: need a custom wrapper with length cached, this cost too
            // much
            Self::String(string) => string.chars().map(|c| c.len_utf16()).sum::<usize>() as u64,
            Self::Any(any) => any.len() as u64,
            Self::Binary(_) | Self::Embed(_) | Self::Format(_) | Self::Type(_) | Self::Doc(_) => 1,
        }
    }

    pub fn countable(&self) -> bool {
        !matches!(self, Content::Format(_) | Content::Deleted(_))
    }

    #[allow(dead_code)]
    pub fn splittable(&self) -> bool {
        matches!(self, Self::String { .. } | Self::Any { .. } | Self::Json { .. })
    }

    pub fn split(&self, diff: u64) -> JwstCodecResult<(Self, Self)> {
        match self {
            Self::String(str) => Ok((
                Self::String(utf16_slice(str, 0, diff).into_owned()),
                Self::String(utf16_slice(str, diff, u64::MAX).into_owned()),
            )),
            Self::Json(vec) => {
                let (left, right) =
                    vec.split_at(usize::try_from(diff).map_err(|_| JwstCodecError::ContentSplitNotSupport(diff))?);
                Ok((Self::Json(left.to_owned()), Self::Json(right.to_owned())))
            }
            Self::Any(vec) => {
                let (left, right) =
                    vec.split_at(usize::try_from(diff).map_err(|_| JwstCodecError::ContentSplitNotSupport(diff))?);
                Ok((Self::Any(left.to_owned()), Self::Any(right.to_owned())))
            }
            Self::Deleted(len) => {
                let (left, right) = (diff, *len - diff);

                Ok((Self::Deleted(left), Self::Deleted(right)))
            }
            _ => Err(JwstCodecError::ContentSplitNotSupport(diff)),
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
}

pub(crate) enum ParentInfo<'a> {
    Root(&'a str),
    Item(Id),
}

pub(crate) enum ContentView<'a> {
    Deleted(u64),
    Json(&'a [Option<String>]),
    Binary(&'a [u8]),
    String(&'a str),
    Embed(&'a Any),
    Format { key: &'a str, value: &'a Any },
    Type { kind: YTypeKind, name: Option<&'a str> },
    Any(&'a [Any]),
    Doc { guid: &'a str, opts: &'a Any },
}

pub(super) fn type_wire_name(kind: YTypeKind, name: Option<&str>) -> Option<&str> {
    match kind {
        YTypeKind::XMLElement => Some(name.unwrap_or("UNDEFINED")),
        YTypeKind::XMLHook => Some(name.unwrap_or("")),
        _ => None,
    }
}

impl ContentView<'_> {
    pub(crate) fn write_item<'a, W: CrdtWriter>(
        &self,
        encoder: &mut W,
        left: Option<Id>,
        right: Option<Id>,
        sub: Option<&SmolStr>,
        parent: impl FnOnce() -> JwstCodecResult<ParentInfo<'a>>,
    ) -> JwstCodecResult {
        let mut info = self.get_info();
        if left.is_some() {
            info |= item_flags::ITEM_HAS_LEFT_ID;
        }
        if right.is_some() {
            info |= item_flags::ITEM_HAS_RIGHT_ID;
        }
        if sub.is_some() {
            info |= item_flags::ITEM_HAS_PARENT_SUB;
        }
        encoder.write_info(info)?;
        if let Some(id) = left {
            encoder.write_item_id(&id)?;
        }
        if let Some(id) = right {
            encoder.write_item_id(&id)?;
        }
        if info & item_flags::ITEM_HAS_SIBLING == 0 {
            match parent()? {
                ParentInfo::Root(name) => {
                    encoder.write_var_u64(1)?;
                    encoder.write_var_string(name)?;
                }
                ParentInfo::Item(id) => {
                    encoder.write_var_u64(0)?;
                    encoder.write_item_id(&id)?;
                }
            }
            if let Some(key) = sub {
                encoder.write_var_string(key)?;
            }
        }
        self.write(encoder)
    }

    pub(crate) fn get_info(&self) -> u8 {
        match self {
            Self::Deleted(_) => 1,
            Self::Json(_) => 2,
            Self::Binary(_) => 3,
            Self::String(_) => 4,
            Self::Embed(_) => 5,
            Self::Format { .. } => 6,
            Self::Type { .. } => 7,
            Self::Any(_) => 8,
            Self::Doc { .. } => 9,
        }
    }

    pub(crate) fn write<W: CrdtWriter>(&self, encoder: &mut W) -> JwstCodecResult {
        match self {
            Self::Deleted(len) => {
                encoder.write_var_u64(*len)?;
            }
            Self::Json(strings) => {
                encoder.write_var_u64(strings.len() as u64)?;
                for string in *strings {
                    match string {
                        Some(string) => encoder.write_var_string(string)?,
                        None => encoder.write_var_string("undefined")?,
                    }
                }
            }
            Self::Binary(buffer) => {
                encoder.write_var_buffer(buffer)?;
            }
            Self::String(string) => {
                encoder.write_var_string(string)?;
            }
            Self::Embed(val) => {
                encoder
                    .write_var_string(serde_json::to_string(val).map_err(|_| JwstCodecError::DamagedDocumentJson)?)?;
            }
            Self::Format { key, value } => {
                encoder.write_var_string(key)?;
                encoder
                    .write_var_string(serde_json::to_string(value).map_err(|_| JwstCodecError::DamagedDocumentJson)?)?;
            }
            Self::Type { kind, name } => {
                let type_ref = u64::from(*kind);
                encoder.write_var_u64(type_ref)?;

                if let Some(name) = type_wire_name(*kind, *name) {
                    encoder.write_var_string(name)?;
                }
            }
            Self::Any(any) => {
                Any::write_multiple(encoder, any)?;
            }
            Self::Doc { guid, opts } => {
                encoder.write_var_string(guid)?;
                opts.write(encoder)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use proptest::{collection::vec, prelude::*};

    use super::*;

    fn content_round_trip(types: &mut TypeArena, content: &Content) -> JwstCodecResult {
        if content.clock_len() == 0 {
            return Ok(());
        }
        let id = Id::new(1, 0);
        let item = Item::new(
            &ItemSpace::default(),
            id,
            content.clone(),
            None,
            None,
            Some(types.alloc(YType::new_root(YTypeKind::Map, None, "root".into()))?),
            None,
        );
        let mut update = Update::default();
        update.structs.insert(
            1,
            [WireStruct::Item(Box::new(WireItem::from_item(types, &item)?))].into(),
        );
        let decoded = Update::decode_v1(update.encode_v1()?)?;
        let decoded = decoded.structs[&1].front().unwrap().as_item().unwrap();
        assert_eq!(decoded.content, WireContent::from_content(types, content)?);

        Ok(())
    }

    #[test]
    fn test_content() {
        #[cfg(target_pointer_width = "64")]
        assert_eq!(std::mem::size_of::<Content>(), 32);

        loom_model!(64 << 10, {
            let mut types = TypeArena::default();
            let mut ty = |kind, name: Option<&str>| {
                Content::Type(types.alloc(YType::new(kind, name.map(str::to_string))).unwrap())
            };
            let contents = [
                Content::Deleted(42),
                Content::Json(vec![None, Some("test_1".to_string()), Some("test_2".to_string())]),
                Content::Binary(vec![1, 2, 3]),
                Content::String("hello".to_string()),
                Content::Embed(Box::new(Any::True)),
                Content::format("key".to_string(), Any::Integer(42)),
                ty(YTypeKind::Array, None),
                ty(YTypeKind::Map, None),
                ty(YTypeKind::Text, None),
                ty(YTypeKind::XMLElement, Some("test")),
                ty(YTypeKind::XMLFragment, None),
                ty(YTypeKind::XMLHook, Some("test")),
                ty(YTypeKind::XMLText, None),
                Content::Any(vec![Any::BigInt64(42), Any::String("Test Any".to_string())]),
                Content::doc("my_guid".to_string(), Any::BigInt64(42)),
            ];

            for content in &contents {
                content_round_trip(&mut types, content).unwrap();
            }
        });
    }

    #[test]
    fn test_content_split() {
        let contents = [
            Content::String("hello".to_string()),
            Content::Json(vec![None, Some("test_1".to_string()), Some("test_2".to_string())]),
            Content::Any(vec![Any::BigInt64(42), Any::String("Test Any".to_string())]),
            Content::Binary(vec![]),
        ];

        {
            let (left, right) = contents[0].split(1).unwrap();
            assert!(contents[0].splittable());
            assert_eq!(left, Content::String("h".to_string()));
            assert_eq!(right, Content::String("ello".to_string()));
        }

        let item = Item::new(
            &ItemSpace::default(),
            Id::new(1, 0),
            Content::String("a😀b".to_string()),
            None,
            None,
            None,
            None,
        );
        for (offset, left_text, right_text) in [(1, "a", "😀b"), (2, "a\u{fffd}", "\u{fffd}b"), (3, "a😀", "b")] {
            let (left, right) = item.split_at(offset).unwrap();
            assert_eq!((item.len(), left.len(), right.len()), (4, offset, 4 - offset));
            assert_eq!(left.content, Content::String(left_text.to_string()));
            assert_eq!(right.content, Content::String(right_text.to_string()));
        }

        {
            let (left, right) = contents[1].split(1).unwrap();
            assert!(contents[1].splittable());
            assert_eq!(left, Content::Json(vec![None]));
            assert_eq!(
                right,
                Content::Json(vec![Some("test_1".to_string()), Some("test_2".to_string())])
            );
        }

        {
            let (left, right) = contents[2].split(1).unwrap();
            assert!(contents[2].splittable());
            assert_eq!(left, Content::Any(vec![Any::BigInt64(42)]));
            assert_eq!(right, Content::Any(vec![Any::String("Test Any".to_string())]));
        }

        {
            assert!(!contents[3].splittable());
            assert_eq!(contents[3].split(2), Err(JwstCodecError::ContentSplitNotSupport(2)));
        }

        // split_in_place matches split across all splittable variants and error
        // cases
        for (content, diff) in [
            (Content::String("hello".to_string()), 1),
            (Content::String("a😀b".to_string()), 1),
            (Content::String("a😀b".to_string()), 2),
            (Content::String("a😀b".to_string()), 3),
            (
                Content::Json(vec![None, Some("test_1".to_string()), Some("test_2".to_string())]),
                1,
            ),
            (
                Content::Any(vec![Any::BigInt64(42), Any::String("Test Any".to_string())]),
                1,
            ),
            (Content::Deleted(5), 2),
        ] {
            let (expected_left, expected_right) = content.split(diff).unwrap();
            let mut left = content;
            let right = left.split_in_place(diff).unwrap();
            assert_eq!(left, expected_left);
            assert_eq!(right, expected_right);
        }
        let mut unsplittable = Content::Binary(vec![1, 2, 3]);
        assert_eq!(
            unsplittable.split_in_place(1),
            Err(JwstCodecError::ContentSplitNotSupport(1))
        );
        assert_eq!(unsplittable, Content::Binary(vec![1, 2, 3]));

        // Splitting large Json/Any vectors at a small offset shrinks the left
        // buffer.
        let mut big_any = Content::Any(vec![Any::Integer(1); 1 << 16]);
        let orig_any_cap = match &big_any {
            Content::Any(v) => v.capacity(),
            _ => unreachable!(),
        };
        let right_any = big_any.split_in_place(1).unwrap();
        assert_eq!(right_any.clock_len(), (1 << 16) - 1);
        match &big_any {
            Content::Any(v) => {
                assert_eq!(v.len(), 1);
                assert!(v.capacity() < orig_any_cap / 2);
            }
            _ => unreachable!(),
        }

        let mut big_json = Content::Json(vec![None; 1 << 16]);
        let orig_json_cap = match &big_json {
            Content::Json(v) => v.capacity(),
            _ => unreachable!(),
        };
        let right_json = big_json.split_in_place(1).unwrap();
        assert_eq!(right_json.clock_len(), (1 << 16) - 1);
        match &big_json {
            Content::Json(v) => {
                assert_eq!(v.len(), 1);
                assert!(v.capacity() < orig_json_cap / 2);
            }
            _ => unreachable!(),
        }
    }

    proptest! {
        #[test]
        #[cfg_attr(miri, ignore)]
        #[cfg_attr(loom, ignore)]
        fn test_random_content(contents in vec(any::<Content>(), 0..10)) {
            for content in &contents {
                content_round_trip(&mut TypeArena::default(), content).unwrap();
            }
        }
    }
}
