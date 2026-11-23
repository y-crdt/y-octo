use std::fmt::Display;

use super::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Any(Any),
    Doc(Doc),
    Array(Array),
    Map(Map),
    Text(Text),
    XMLElement(XMLElement),
    XMLFragment(XMLFragment),
    XMLHook(XMLHook),
    XMLText(XMLText),
}

impl Value {
    pub fn to_any(&self) -> Option<Any> {
        match self {
            Value::Any(any) => Some(any.clone()),
            _ => None,
        }
    }

    pub fn to_array(&self) -> Option<Array> {
        match self {
            Value::Array(array) => Some(array.clone()),
            _ => None,
        }
    }

    pub fn to_map(&self) -> Option<Map> {
        match self {
            Value::Map(map) => Some(map.clone()),
            _ => None,
        }
    }

    pub fn to_text(&self) -> Option<Text> {
        match self {
            Value::Text(text) => Some(text.clone()),
            _ => None,
        }
    }

    pub fn to_xml_element(&self) -> Option<XMLElement> {
        match self {
            Value::XMLElement(element) => Some(element.clone()),
            _ => None,
        }
    }

    pub fn to_xml_fragment(&self) -> Option<XMLFragment> {
        match self {
            Value::XMLFragment(fragment) => Some(fragment.clone()),
            _ => None,
        }
    }

    pub fn to_xml_text(&self) -> Option<XMLText> {
        match self {
            Value::XMLText(text) => Some(text.clone()),
            _ => None,
        }
    }

    pub fn to_xml_hook(&self) -> Option<XMLHook> {
        match self {
            Value::XMLHook(hook) => Some(hook.clone()),
            _ => None,
        }
    }

    pub fn from_vec<T: Into<Any>>(el: Vec<T>) -> Self {
        Value::Any(Any::Array(el.into_iter().map(|item| item.into()).collect::<Vec<_>>()))
    }
}

/// The plain value of content that is neither a type nor a subdocument.
/// Inlined so each caller dispatches on the content once.
#[inline(always)]
fn plain_any(content: &Content) -> Any {
    match content {
        Content::Any(any) => {
            if any.len() == 1 {
                any[0].clone()
            } else {
                Any::Array(any.clone())
            }
        }
        Content::String(s) => Any::String(s.clone()),
        Content::Json(json) => json_any(json),
        Content::Binary(buf) => Any::Binary(buf.clone()),
        Content::Embed(v) => v.as_ref().clone(),
        // Yjs `ContentFormat.getContent()` is empty, so a format item that
        // ended up as a map value reads as undefined.
        Content::Format(_) => Any::Undefined,
        // actually unreachable; the callers handle types and subdocuments
        Content::Deleted(_) | Content::Type(_) | Content::Doc(_) => Any::Undefined,
    }
}

#[cold]
#[inline(never)]
fn json_any(json: &[Option<String>]) -> Any {
    Any::Array(
        json.iter()
            .map(|item| item.clone().map_or(Any::Undefined, Any::String))
            .collect(),
    )
}

/// The plain value of content, `None` for a type or a subdocument.
#[cfg(feature = "session")]
pub(crate) fn content_any(content: &Content) -> Option<Any> {
    match content {
        Content::Type(_) | Content::Doc(_) => None,
        content => Some(plain_any(content)),
    }
}

/// The public handle of the type `ty` with the kind it has.
pub(crate) fn type_value(ty: YTypeRef, kind: YTypeKind) -> Option<Value> {
    Some(match kind {
        YTypeKind::Array => Value::Array(Array::from_unchecked(ty)),
        YTypeKind::Map => Value::Map(Map::from_unchecked(ty)),
        YTypeKind::Text => Value::Text(Text::from_unchecked(ty)),
        YTypeKind::XMLElement => Value::XMLElement(XMLElement::from_unchecked(ty)),
        YTypeKind::XMLFragment => Value::XMLFragment(XMLFragment::from_unchecked(ty)),
        YTypeKind::XMLHook => Value::XMLHook(XMLHook::from_unchecked(ty)),
        YTypeKind::XMLText => Value::XMLText(XMLText::from_unchecked(ty)),
        YTypeKind::Unknown => return None,
    })
}

impl Value {
    /// The value of `content` of the document read through `cx`. A type
    /// becomes a handle to it.
    #[inline]
    pub(crate) fn from_content(cx: TypeCx<'_>, content: &Content) -> Value {
        match content {
            Content::Type(_) | Content::Doc(_) => Self::nested_value(cx, content),
            content => Value::Any(plain_any(content)),
        }
    }

    #[cold]
    #[inline(never)]
    fn nested_value(cx: TypeCx<'_>, content: &Content) -> Value {
        match content {
            Content::Type(ty) => {
                let kind = cx.types[*ty].kind();
                // an unknown kind is actually unreachable
                type_value(cx.handle(*ty), kind).unwrap_or(Value::Any(Any::Undefined))
            }
            Content::Doc(doc) => Value::Doc(subdocument(&doc.guid, &doc.opts)),
            _ => unreachable!("expected a nested type or subdocument"),
        }
    }
}

/// A value on its way into a type: content the parent's document can hold, or
/// a type of another document, which it cannot (an item refers to a type by
/// its slot in the document's own arena).
pub(crate) enum NewContent {
    Local(Content),
    Foreign,
}

impl From<Content> for NewContent {
    fn from(content: Content) -> Self {
        Self::Local(content)
    }
}

impl NewContent {
    /// `value` as content for a type of the document `store`.
    pub(crate) fn from_value(value: Value, store: &WeakStoreRef) -> Self {
        let ty = match value {
            Value::Any(any) => return Self::Local(Content::from(any)),
            Value::Doc(doc) => {
                return Self::Local(Content::doc(doc.guid().to_owned(), Any::from(doc.options().clone())));
            }
            Value::Array(v) => v.0,
            Value::Map(v) => v.0,
            Value::Text(v) => v.0,
            Value::XMLElement(v) => v.0,
            Value::XMLFragment(v) => v.0,
            Value::XMLHook(v) => v.0,
            Value::XMLText(v) => v.0,
        };
        match ty.id {
            Some(id) if ty.store.ptr_eq(store) => Self::Local(Content::Type(id)),
            _ => Self::Foreign,
        }
    }
}

impl<T: Into<Any>> From<T> for Value {
    fn from(value: T) -> Self {
        Value::Any(value.into())
    }
}

impl From<Doc> for Value {
    fn from(value: Doc) -> Self {
        Value::Doc(value)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Any(any) => write!(f, "{any}"),
            Value::Text(text) => write!(f, "{text}"),
            Value::XMLElement(element) => write!(f, "{element}"),
            Value::XMLFragment(fragment) => write!(f, "{fragment}"),
            Value::XMLHook(_) => write!(f, "[object Object]"),
            Value::XMLText(text) => write!(f, "{text}"),
            _ => write!(f, ""),
        }
    }
}

impl serde::Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::Any(any) => any.serialize(serializer),
            Self::Array(array) => array.serialize(serializer),
            Self::Map(map) => map.serialize(serializer),
            Self::Text(text) => text.serialize(serializer),
            Self::XMLElement(xml_element) => xml_element.serialize(serializer),
            Self::XMLFragment(xml_fragment) => xml_fragment.serialize(serializer),
            Self::XMLHook(xml_hook) => xml_hook.serialize(serializer),
            Self::XMLText(xml_text) => xml_text.serialize(serializer),
            Self::Doc(_) => serializer.serialize_none(),
        }
    }
}
