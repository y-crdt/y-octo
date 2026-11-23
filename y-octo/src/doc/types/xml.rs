use std::fmt::{self, Display, Write as _};

use super::{
    array::{array_get, array_values},
    list::{ListIterator, ListType},
    map::{MapType, map_entries, map_remove},
    text::{TextAttributes, TextDelta, TextDeltaOp, TextIdentityRun, TextInsert, apply_text_delta, text_delta},
    *,
};
use crate::{Any, Content, JwstCodecResult, impl_type};

impl_type!(XMLElement);
impl ListType for XMLElement {}
impl MapType for XMLElement {}

impl_type!(XMLFragment);
impl ListType for XMLFragment {}

impl_type!(XMLText);
impl ListType for XMLText {}

impl_type!(XMLHook);
impl MapType for XMLHook {}

pub(crate) const DEFAULT_XML_ELEMENT_TAG: &str = "UNDEFINED";

/// The tag name of an XML element (`"UNDEFINED"` when unset, matching Yjs).
pub(crate) fn xml_tag_name(ty: &YType) -> &str {
    ty.name().unwrap_or(DEFAULT_XML_ELEMENT_TAG)
}

/// The hook name of an XML hook (`""` when unset).
pub(crate) fn xml_hook_name(ty: &YType) -> &str {
    ty.name().unwrap_or("")
}

/// First visible child of an XML fragment or element. Caller holds the store
/// lock.
pub(crate) fn xml_first_child(cx: TypeCx<'_>, ty: &YType) -> Option<Value> {
    ListIterator::new(&cx.types.items, ty)
        .find(|item| item.countable())
        .map(|item| match &item.content {
            Content::Any(any) if !any.is_empty() => Value::Any(any[0].clone()),
            content => Value::from_content(cx, content),
        })
}

/// Parent container of this XML node, if mounted inside another type. Caller
/// holds the store lock.
pub(crate) fn xml_parent(cx: TypeCx<'_>, ty: &YType) -> Option<Value> {
    let item = ty.live_carrier(&cx.types.items)?;
    let parent = item.parent?;
    type_value(cx.handle(parent), cx.get(parent)?.kind())
}

/// Next visible countable sibling of this XML node. Caller holds the store
/// lock.
pub(crate) fn xml_next_sibling(cx: TypeCx<'_>, ty: &YType) -> Option<Value> {
    let item = ty.live_carrier(&cx.types.items)?;
    let mut cur = item.right.and_then(|i| cx.types.items.get(i));
    while let Some(next) = cur {
        if next.indexable() {
            return Some(Value::from_content(cx, &next.content));
        }
        cur = next.right.and_then(|i| cx.types.items.get(i));
    }
    None
}

/// Previous visible countable sibling of this XML node. Caller holds the store
/// lock.
pub(crate) fn xml_prev_sibling(cx: TypeCx<'_>, ty: &YType) -> Option<Value> {
    let item = ty.live_carrier(&cx.types.items)?;
    let mut cur = item.left.and_then(|i| cx.types.items.get(i));
    while let Some(prev) = cur {
        if prev.indexable() {
            return Some(Value::from_content(cx, &prev.content));
        }
        cur = prev.left.and_then(|i| cx.types.items.get(i));
    }
    None
}

/// Compares strings by UTF-16 code unit order, matching JavaScript `<` / `>`.
fn cmp_utf16(a: &str, b: &str) -> std::cmp::Ordering {
    a.encode_utf16().cmp(b.encode_utf16())
}

/// Sorted snapshot of visible attributes of an XML element. Caller holds the
/// store lock.
pub(crate) fn xml_attributes(cx: TypeCx<'_>, ty: &YType) -> Vec<(String, Value)> {
    let mut attrs: Vec<(String, Value)> = map_entries(&cx.types.items, ty)
        .map(|(k, item)| (k.to_string(), Value::from_content(cx, &item.content)))
        .collect();
    attrs.sort_by(|a, b| cmp_utf16(&a.0, &b.0));
    attrs
}

/// Depth-first pre-order traversal of all active descendant XML nodes, matching
/// Yjs `YXmlTreeWalker`. Uses an explicit stack to avoid stack overflow on deep
/// trees. Caller holds the store lock.
pub(crate) fn xml_tree_walker(cx: TypeCx<'_>, ty: &YType) -> Vec<Value> {
    let mut out = Vec::new();
    let mut stack: Vec<&Item> = Vec::new();
    let mut direct: Vec<&Item> = ListIterator::new(&cx.types.items, ty)
        .filter(|item| item.countable())
        .collect();
    while let Some(item) = direct.pop() {
        stack.push(item);
    }
    while let Some(item) = stack.pop() {
        if let Content::Type(child) = &item.content
            && let Some(child_ty) = cx.get(*child)
        {
            let kind = child_ty.kind();
            if let Some(val) = type_value(cx.handle(*child), kind) {
                out.push(val);
            }
            if matches!(kind, YTypeKind::XMLElement | YTypeKind::XMLFragment) {
                let mut grandchildren: Vec<&Item> = ListIterator::new(&cx.types.items, child_ty)
                    .filter(|c| c.countable())
                    .collect();
                while let Some(gc) = grandchildren.pop() {
                    stack.push(gc);
                }
            }
        }
    }
    out
}

/// Formats an [Any] value with JavaScript `String(value)` coercion semantics as
/// used by Yjs `YXmlElement.prototype.toString()` and
/// `YXmlText.prototype.toString()`.
fn format_xml_any(out: &mut String, value: &Any) {
    match value {
        Any::Null => out.push_str("null"),
        Any::Undefined => out.push_str("undefined"),
        Any::True => out.push_str("true"),
        Any::False => out.push_str("false"),
        Any::Integer(n) => {
            let _ = write!(out, "{n}");
        }
        Any::BigInt64(n) => {
            let _ = write!(out, "{n}");
        }
        Any::Float32(f) => format_js_float(out, f64::from(f.0)),
        Any::Float64(f) => format_js_float(out, f.0),
        Any::String(s) => out.push_str(s),
        Any::Binary(buf) => {
            for (i, byte) in buf.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                let _ = write!(out, "{byte}");
            }
        }
        Any::Array(items) => {
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                // JS Array.prototype.toString turns null/undefined elements
                // into "".
                if !matches!(item, Any::Null | Any::Undefined) {
                    format_xml_any(out, item);
                }
            }
        }
        Any::Object(_) => out.push_str("[object Object]"),
    }
}

/// Formats a finite or special `f64` according to ECMA-262 6.1.6.1.20
/// `Number::toString`.
fn format_js_float(out: &mut String, v: f64) {
    let mut buf = ryu_js::Buffer::new();
    out.push_str(buf.format(v));
}

/// Formats a map-attribute item's content (matching Yjs `typeMapGet`, which
/// reads the last element of an item's content array).
fn format_xml_attr_content(out: &mut String, types: &TypeArena, content: &Content) {
    match content {
        Content::Any(any) => {
            if let Some(last) = any.last() {
                format_xml_any(out, last);
            } else {
                out.push_str("undefined");
            }
        }
        Content::Json(items) => {
            if let Some(last) = items.last() {
                match last {
                    Some(s) => out.push_str(s),
                    None => out.push_str("undefined"),
                }
            } else {
                out.push_str("undefined");
            }
        }
        other => format_xml_list_content(out, types, other),
    }
}

/// Formats a child-list item's content (matching Yjs `typeListForEach`, which
/// visits every element of multi-element `ContentAny` / `ContentJson` items).
fn format_xml_list_content(out: &mut String, types: &TypeArena, content: &Content) {
    match content {
        Content::Any(items) => {
            for item in items {
                format_xml_any(out, item);
            }
        }
        Content::String(s) => out.push_str(s),
        Content::Binary(buf) => {
            for (i, byte) in buf.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                let _ = write!(out, "{byte}");
            }
        }
        Content::Embed(v) => format_xml_any(out, v),
        Content::Json(items) => {
            for item in items {
                match item {
                    Some(s) => out.push_str(s),
                    None => out.push_str("undefined"),
                }
            }
        }
        Content::Type(ty) => {
            if let Some(ty) = types.get(*ty) {
                format_xml_type(out, types, ty);
            }
        }
        Content::Doc(_) => out.push_str("[object Object]"),
        Content::Format(_) | Content::Deleted(_) => out.push_str("undefined"),
    }
}

enum XmlFrame<'a> {
    Type(&'a YType),
    Content(&'a Content),
    Close(String),
}

fn push_xml_children<'a>(stack: &mut Vec<XmlFrame<'a>>, types: &'a TypeArena, ty: &'a YType) {
    let mut children: Vec<&Item> = ListIterator::new(&types.items, ty).filter(|i| i.countable()).collect();
    while let Some(child) = children.pop() {
        if let Content::Type(child_ty) = &child.content
            && let Some(child_ty) = types.get(*child_ty)
        {
            stack.push(XmlFrame::Type(child_ty));
        } else {
            stack.push(XmlFrame::Content(&child.content));
        }
    }
}

/// Serializes an XML type (or fragment/element/text) to its Yjs-compatible XML
/// string using an explicit stack to prevent stack overflow on deep trees.
/// Caller holds the store lock.
fn format_xml_type(out: &mut String, types: &TypeArena, root: &YType) {
    let mut stack = vec![XmlFrame::Type(root)];
    while let Some(frame) = stack.pop() {
        match frame {
            XmlFrame::Close(tag) => {
                out.push_str("</");
                out.push_str(&tag);
                out.push('>');
            }
            XmlFrame::Content(content) => {
                format_xml_list_content(out, types, content);
            }
            XmlFrame::Type(ty) => match ty.kind() {
                YTypeKind::XMLElement => {
                    let node_name = xml_tag_name(ty).to_lowercase();
                    out.push('<');
                    out.push_str(&node_name);
                    let mut attrs: Vec<(&str, &Item)> = map_entries(&types.items, ty).collect();
                    attrs.sort_unstable_by(|a, b| cmp_utf16(a.0, b.0));
                    for (key, item) in attrs {
                        out.push(' ');
                        out.push_str(key);
                        out.push_str("=\"");
                        format_xml_attr_content(out, types, &item.content);
                        out.push('"');
                    }
                    out.push('>');
                    stack.push(XmlFrame::Close(node_name));
                    push_xml_children(&mut stack, types, ty);
                }
                YTypeKind::XMLFragment | YTypeKind::Unknown => {
                    push_xml_children(&mut stack, types, ty);
                }
                YTypeKind::XMLText => {
                    format_xml_text(out, &types.items, ty);
                }
                YTypeKind::Text => {
                    out.push_str(&text::text_string(&types.items, ty));
                }
                YTypeKind::XMLHook | YTypeKind::Map | YTypeKind::Array => {
                    // Matches Yjs: YXmlHook/YMap/YArray inherit
                    // Object.prototype.toString().
                    out.push_str("[object Object]");
                }
            },
        }
    }
}

/// Serializes an `XMLFragment` or `XMLElement` to string, matching Yjs
/// `toString()`.
pub(crate) fn xml_to_string(types: &TypeArena, ty: &YType) -> String {
    let mut out = String::new();
    format_xml_type(&mut out, types, ty);
    out
}

/// Serializes an `XMLText` to string, matching Yjs
/// `YXmlText.prototype.toString()`.
pub(crate) fn xml_text_to_string(items: &ItemSpace, ty: &YType) -> String {
    let mut out = String::new();
    format_xml_text(&mut out, items, ty);
    out
}

fn format_xml_text(out: &mut String, items: &ItemSpace, ty: &YType) {
    let delta = text_delta(items, ty);
    for op in delta {
        let TextDeltaOp::Insert { insert, format } = op else {
            continue;
        };
        let mut opened: Vec<&str> = Vec::new();
        if let Some(ref attrs_map) = format {
            // Sort by UTF-16 code units, matching Yjs `nestedNodes.sort((a, b)
            // => a.nodeName < b.nodeName ? -1 : 1)`.
            let mut nodes: Vec<(&str, &Any)> = attrs_map.iter().map(|(k, v)| (k.as_str(), v)).collect();
            nodes.sort_unstable_by(|a, b| cmp_utf16(a.0, b.0));
            for (node_name, node_val) in nodes {
                out.push('<');
                out.push_str(node_name);
                match node_val {
                    Any::Object(obj) => {
                        let mut pairs: Vec<(&str, &Any)> = obj.iter().map(|(k, v)| (k.as_str(), v)).collect();
                        pairs.sort_unstable_by(|a, b| cmp_utf16(a.0, b.0));
                        for (k, v) in pairs {
                            out.push(' ');
                            out.push_str(k);
                            out.push_str("=\"");
                            format_xml_any(out, v);
                            out.push('"');
                        }
                    }
                    Any::Array(items) => {
                        let mut pairs: Vec<(String, &Any)> =
                            items.iter().enumerate().map(|(i, v)| (i.to_string(), v)).collect();
                        pairs.sort_unstable_by(|a, b| cmp_utf16(&a.0, &b.0));
                        for (k, v) in pairs {
                            out.push(' ');
                            out.push_str(&k);
                            out.push_str("=\"");
                            format_xml_any(out, v);
                            out.push('"');
                        }
                    }
                    Any::String(s) => {
                        let mut pairs: Vec<(String, String)> = s
                            .encode_utf16()
                            .enumerate()
                            .map(|(i, unit)| (i.to_string(), String::from_utf16_lossy(&[unit])))
                            .collect();
                        pairs.sort_unstable_by(|a, b| cmp_utf16(&a.0, &b.0));
                        for (k, v) in pairs {
                            out.push(' ');
                            out.push_str(&k);
                            out.push_str("=\"");
                            out.push_str(&v);
                            out.push('"');
                        }
                    }
                    Any::Binary(bytes) => {
                        let mut pairs: Vec<(String, u8)> = bytes
                            .iter()
                            .copied()
                            .enumerate()
                            .map(|(i, b)| (i.to_string(), b))
                            .collect();
                        pairs.sort_unstable_by(|a, b| cmp_utf16(&a.0, &b.0));
                        for (k, b) in pairs {
                            out.push(' ');
                            out.push_str(&k);
                            out.push_str("=\"");
                            let _ = write!(out, "{b}");
                            out.push('"');
                        }
                    }
                    _ => {}
                }
                out.push('>');
                opened.push(node_name);
            }
        }
        match &insert {
            TextInsert::Text(s) => out.push_str(s),
            TextInsert::Embed(values) => {
                for (i, value) in values.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    format_xml_any(out, value);
                }
            }
        }
        for node_name in opened.into_iter().rev() {
            out.push_str("</");
            out.push_str(node_name);
            out.push('>');
        }
    }
}

// ---------------------------------------------------------------------------
// XMLFragment

impl XMLFragment {
    #[inline(always)]
    pub fn id(&self) -> Option<Id> {
        self._id()
    }

    #[inline]
    pub fn len(&self) -> u64 {
        self.content_len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, index: u64) -> Option<Value> {
        or_released(self.as_inner().read_cx(|cx, ty| array_get(cx, ty, index)))
    }

    pub fn insert<V: Into<Value>>(&mut self, idx: u64, val: V) -> JwstCodecResult {
        self.insert_value_at(idx, val.into())
    }

    pub fn push<V: Into<Value>>(&mut self, val: V) -> JwstCodecResult {
        self.push_value(val.into())
    }

    pub fn remove(&mut self, idx: u64, len: u64) -> JwstCodecResult {
        self.remove_at(idx, len)
    }

    /// A snapshot of the visible children, taken under one store read lock.
    pub fn iter(&self) -> std::vec::IntoIter<Value> {
        or_released(
            self.as_inner()
                .read_cx(|cx, ty| array_values(cx, ty).collect::<Vec<_>>()),
        )
        .into_iter()
    }

    pub fn first_child(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_first_child))
    }

    pub fn parent(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_parent))
    }

    /// Depth-first pre-order snapshot of all active XML descendant nodes.
    pub fn tree_walker(&self) -> std::vec::IntoIter<Value> {
        or_released(self.as_inner().read_cx(xml_tree_walker)).into_iter()
    }

    /// Serializes all children to an XML string matching Yjs
    /// `YXmlFragment.prototype.toString()`.
    pub fn to_xml_string(&self) -> String {
        or_released(self.as_inner().read(|store, ty| xml_to_string(&store.type_arena, ty)))
    }
}

impl Display for XMLFragment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_xml_string())
    }
}

impl serde::Serialize for XMLFragment {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_xml_string())
    }
}

// ---------------------------------------------------------------------------
// XMLElement

impl XMLElement {
    #[inline(always)]
    pub fn id(&self) -> Option<Id> {
        ListType::_id(self)
    }

    #[inline]
    pub fn len(&self) -> u64 {
        self.content_len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The tag name of this XML element (`"UNDEFINED"` by default, matching
    /// Yjs).
    pub fn tag_name(&self) -> String {
        or_released(self.as_inner().read(|_, ty| xml_tag_name(ty).to_string()))
    }

    pub fn get(&self, index: u64) -> Option<Value> {
        or_released(self.as_inner().read_cx(|cx, ty| array_get(cx, ty, index)))
    }

    pub fn insert<V: Into<Value>>(&mut self, idx: u64, val: V) -> JwstCodecResult {
        self.insert_value_at(idx, val.into())
    }

    pub fn push<V: Into<Value>>(&mut self, val: V) -> JwstCodecResult {
        self.push_value(val.into())
    }

    pub fn remove(&mut self, idx: u64, len: u64) -> JwstCodecResult {
        self.remove_at(idx, len)
    }

    /// A snapshot of the visible children, taken under one store read lock.
    pub fn iter(&self) -> std::vec::IntoIter<Value> {
        or_released(
            self.as_inner()
                .read_cx(|cx, ty| array_values(cx, ty).collect::<Vec<_>>()),
        )
        .into_iter()
    }

    pub fn first_child(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_first_child))
    }

    pub fn parent(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_parent))
    }

    pub fn next_sibling(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_next_sibling))
    }

    pub fn prev_sibling(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_prev_sibling))
    }

    /// Depth-first pre-order snapshot of all active XML descendant nodes.
    pub fn tree_walker(&self) -> std::vec::IntoIter<Value> {
        or_released(self.as_inner().read_cx(xml_tree_walker)).into_iter()
    }

    pub fn set_attribute<K: Into<String>, V: Into<Value>>(&mut self, name: K, value: V) -> JwstCodecResult {
        self._insert(name.into(), value)
    }

    pub fn get_attribute(&self, name: &str) -> Option<Value> {
        self._get(name)
    }

    pub fn remove_attribute(&mut self, name: &str) -> JwstCodecResult {
        self.as_inner().write(|store, ty| {
            map_remove(store, ty, name);
            Ok(())
        })
    }

    pub fn contains_attribute(&self, name: &str) -> bool {
        self._contains_key(name)
    }

    /// Snapshot of visible attributes sorted by attribute name.
    pub fn attributes(&self) -> Vec<(String, Value)> {
        or_released(self.as_inner().read_cx(xml_attributes))
    }

    /// Serializes this element, its sorted attributes and children to an XML
    /// string matching Yjs `YXmlElement.prototype.toString()`.
    pub fn to_xml_string(&self) -> String {
        or_released(self.as_inner().read(|store, ty| xml_to_string(&store.type_arena, ty)))
    }
}

impl Display for XMLElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_xml_string())
    }
}

impl serde::Serialize for XMLElement {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_xml_string())
    }
}

// ---------------------------------------------------------------------------
// XMLText

impl XMLText {
    #[inline(always)]
    pub fn id(&self) -> Option<Id> {
        self._id()
    }

    #[inline]
    pub fn len(&self) -> u64 {
        self.content_len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn insert<T: ToString>(&mut self, char_index: u64, str: T) -> JwstCodecResult {
        self.insert_at(char_index, Content::String(str.to_string()))
    }

    pub fn insert_embed<V: Into<Any>>(&mut self, char_index: u64, embed: V) -> JwstCodecResult {
        let embed = embed.into();
        self.as_inner()
            .write(|store, ty| text::text_insert_embed(store, ty, char_index, embed))
    }

    pub fn format(&mut self, char_index: u64, len: u64, attrs: TextAttributes) -> JwstCodecResult {
        self.as_inner()
            .write(|store, ty| text::text_format(store, ty, char_index, len, attrs))
    }

    #[inline]
    pub fn remove(&mut self, char_index: u64, len: u64) -> JwstCodecResult {
        self.as_inner()
            .write(|store, ty| text::text_remove(store, ty, char_index, len))
    }

    pub fn to_delta(&self) -> TextDelta {
        or_released(
            self.as_inner()
                .read(|store, ty| text_delta(&store.type_arena.items, ty)),
        )
    }

    pub fn apply_delta(&mut self, delta: &[TextDeltaOp]) -> JwstCodecResult {
        self.as_inner().write(|store, ty| apply_text_delta(store, ty, delta))
    }

    pub fn identity_runs(&self) -> JwstCodecResult<Vec<TextIdentityRun>> {
        self.as_inner().read(|store, ty| {
            ty.identity(&store.type_arena.items)?;
            text::identity_runs(&store.type_arena.items, ty)
        })?
    }

    pub fn parent(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_parent))
    }

    pub fn next_sibling(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_next_sibling))
    }

    pub fn prev_sibling(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_prev_sibling))
    }

    /// Serializes this rich text with formatting tags matching Yjs
    /// `YXmlText.prototype.toString()`.
    pub fn to_xml_string(&self) -> String {
        or_released(
            self.as_inner()
                .read(|store, ty| xml_text_to_string(&store.type_arena.items, ty)),
        )
    }
}

impl Display for XMLText {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_xml_string())
    }
}

impl serde::Serialize for XMLText {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_xml_string())
    }
}

// ---------------------------------------------------------------------------
// XMLHook

impl XMLHook {
    #[inline(always)]
    pub fn id(&self) -> Option<Id> {
        self._id()
    }

    pub fn hook_name(&self) -> String {
        or_released(self.as_inner().read(|_, ty| xml_hook_name(ty).to_string()))
    }

    #[inline(always)]
    pub fn insert<V: Into<Value>>(&mut self, key: String, value: V) -> JwstCodecResult {
        self._insert(key, value)
    }

    #[inline(always)]
    pub fn get(&self, key: &str) -> Option<Value> {
        self._get(key)
    }

    #[inline(always)]
    pub fn contains_key(&self, key: &str) -> bool {
        self._contains_key(key)
    }

    pub fn remove(&mut self, key: &str) -> JwstCodecResult {
        self.as_inner().write(|store, ty| {
            map_remove(store, ty, key);
            Ok(())
        })
    }

    #[inline(always)]
    pub fn clear(&mut self) -> JwstCodecResult {
        self._clear()
    }

    #[inline(always)]
    pub fn len(&self) -> u64 {
        self._len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline(always)]
    pub fn iter(&self) -> std::vec::IntoIter<(String, Value)> {
        self._entries().into_iter()
    }

    #[inline(always)]
    pub fn entries(&self) -> std::vec::IntoIter<(String, Value)> {
        self._entries().into_iter()
    }

    #[inline(always)]
    pub fn keys(&self) -> std::vec::IntoIter<String> {
        self._keys().into_iter()
    }

    #[inline(always)]
    pub fn values(&self) -> std::vec::IntoIter<Value> {
        self._values().into_iter()
    }

    pub fn parent(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_parent))
    }

    pub fn next_sibling(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_next_sibling))
    }

    pub fn prev_sibling(&self) -> Option<Value> {
        or_released(self.as_inner().read_cx(xml_prev_sibling))
    }
}

impl serde::Serialize for XMLHook {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;

        let entries = self.iter();
        let mut map = serializer.serialize_map(Some(entries.len()))?;
        for (key, value) in entries {
            map.serialize_entry(&key, &value)?;
        }
        map.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Any, Doc, JwstCodecError, loom_model};
    #[cfg(not(loom))]
    use crate::{UndoManager, UndoOptions};

    #[test]
    fn test_xml_element_attributes_and_children() {
        loom_model!({
            let doc = Doc::with_client(1);
            let mut frag = doc.get_or_create_xml_fragment("xml").unwrap();
            let mut div = doc.create_xml_element("Div").unwrap();
            assert_eq!(div.tag_name(), "Div");

            frag.push(div.clone()).unwrap();
            div.set_attribute("z", "hello").unwrap();
            div.set_attribute("a", 42).unwrap();
            div.set_attribute("b", true).unwrap();
            div.set_attribute("d", Any::Null).unwrap();
            div.set_attribute("e", Any::Undefined).unwrap();

            assert!(div.contains_attribute("a"));
            assert!(div.contains_attribute("d"));
            assert!(div.contains_attribute("e"));
            assert_eq!(div.get_attribute("a"), Some(Value::Any(Any::Integer(42))));
            assert_eq!(div.get_attribute("d"), Some(Value::Any(Any::Null)));
            assert_eq!(div.get_attribute("e"), Some(Value::Any(Any::Undefined)));
            assert_eq!(
                div.attributes().into_iter().map(|(k, _)| k).collect::<Vec<_>>(),
                vec!["a", "b", "d", "e", "z"]
            );

            div.remove_attribute("e").unwrap();
            assert!(!div.contains_attribute("e"));

            let mut txt = doc.create_xml_text().unwrap();
            div.push(txt.clone()).unwrap();
            txt.insert(0, "hello world").unwrap();
            txt.format(0, 5, TextAttributes::from([("bold".into(), Any::True)]))
                .unwrap();

            let mut hook = doc.create_xml_hook("my-hook").unwrap();
            frag.push(hook.clone()).unwrap();
            hook.insert("k".into(), "v").unwrap();
            assert_eq!(hook.hook_name(), "my-hook");
            assert_eq!(hook.get("k"), Some(Value::Any(Any::String("v".into()))));

            assert_eq!(
                div.to_xml_string(),
                r#"<div a="42" b="true" d="null" z="hello"><bold>hello</bold> world</div>"#
            );
            assert_eq!(
                frag.to_xml_string(),
                r#"<div a="42" b="true" d="null" z="hello"><bold>hello</bold> world</div>[object Object]"#
            );
            assert_eq!(frag.first_child(), Some(Value::XMLElement(div.clone())));
            assert_eq!(div.parent(), Some(Value::XMLFragment(frag.clone())));
            assert_eq!(div.next_sibling(), Some(Value::XMLHook(hook.clone())));
            assert_eq!(hook.prev_sibling(), Some(Value::XMLElement(div.clone())));
            assert_eq!(txt.parent(), Some(Value::XMLElement(div.clone())));

            let walked = frag.tree_walker().collect::<Vec<_>>();
            assert_eq!(
                walked,
                vec![Value::XMLElement(div), Value::XMLText(txt), Value::XMLHook(hook),]
            );
        });
    }

    #[test]
    fn test_xml_root_element_default_tag_and_round_trip() {
        loom_model!({
            let doc = Doc::with_client(1);
            let mut root = doc.get_or_create_xml_element("root").unwrap();
            assert_eq!(root.tag_name(), "UNDEFINED");
            root.set_attribute("id", "r1").unwrap();
            assert_eq!(root.to_xml_string(), r#"<undefined id="r1"></undefined>"#);

            let update = doc.encode_update_v1().unwrap();
            let restored = Doc::try_from_binary_v1(update).unwrap();
            let restored_root = restored.get_or_create_xml_element("root").unwrap();
            assert_eq!(restored_root.tag_name(), "UNDEFINED");
            assert_eq!(restored_root.to_xml_string(), r#"<undefined id="r1"></undefined>"#);
        });
    }

    #[test]
    fn test_xml_preliminary_subtree_mount() {
        loom_model!(64 << 10, {
            let doc = Doc::with_client(10);
            let mut frag = doc.get_or_create_xml_fragment("xml").unwrap();

            let mut div = doc.create_xml_element("div").unwrap();
            div.set_attribute("class", "card").unwrap();
            div.set_attribute("removed", "x").unwrap();
            div.remove_attribute("removed").unwrap();

            let mut txt = doc.create_xml_text().unwrap();
            txt.insert(0, "hello world").unwrap();
            txt.format(0, 5, TextAttributes::from([("bold".into(), Any::True)]))
                .unwrap();
            div.push(txt.clone()).unwrap();

            // Still preliminary: no published state yet.
            assert!(doc.get_state_vector().is_empty());
            assert_eq!(div.id(), None);
            assert_eq!(txt.id(), None);

            frag.push(div.clone()).unwrap();
            assert!(div.id().is_some());
            assert!(txt.id().is_some());
            assert_eq!(
                frag.to_xml_string(),
                r#"<div class="card"><bold>hello</bold> world</div>"#
            );

            let peer = Doc::try_from_binary_v1(doc.encode_update_v1().unwrap()).unwrap();
            assert_eq!(
                peer.get_or_create_xml_fragment("xml").unwrap().to_xml_string(),
                r#"<div class="card"><bold>hello</bold> world</div>"#
            );
        });
    }

    #[test]
    fn test_xml_duplicate_insert_and_cycle_rejected() {
        loom_model!({
            let doc = Doc::with_client(1);
            let mut frag = doc.get_or_create_xml_fragment("xml").unwrap();
            let mut a = doc.create_xml_element("a").unwrap();
            let mut b = doc.create_xml_element("b").unwrap();

            a.push(b.clone()).unwrap();
            assert_eq!(frag.push(b.clone()), Err(JwstCodecError::TypeAlreadyInserted));
            assert_eq!(b.push(a.clone()), Err(JwstCodecError::InvalidParent));
            assert_eq!(a.push(a.clone()), Err(JwstCodecError::InvalidParent));
            assert_eq!(a.push(frag.clone()), Err(JwstCodecError::TypeAlreadyInserted));

            frag.push(a.clone()).unwrap();
            assert_eq!(frag.push(a.clone()), Err(JwstCodecError::TypeAlreadyInserted));
            frag.remove(0, 1).unwrap();
            assert_eq!(frag.push(a.clone()), Err(JwstCodecError::TypeAlreadyInserted));
        });
    }

    #[cfg(not(loom))]
    #[test]
    fn test_xml_undo_manager_attrs_children_and_rich_text() {
        let doc = Doc::with_client(1);
        let mut frag = doc.get_or_create_xml_fragment("xml").unwrap();
        let undo = UndoManager::<()>::new(
            &doc,
            [(&frag).into()],
            UndoOptions {
                capture_timeout: 0,
                ..UndoOptions::default()
            },
        )
        .unwrap();

        let mut div = doc.create_xml_element("div").unwrap();
        div.set_attribute("class", "box").unwrap();
        let mut txt = doc.create_xml_text().unwrap();
        txt.insert(0, "hello world").unwrap();
        div.push(txt.clone()).unwrap();
        frag.push(div.clone()).unwrap();
        let s1 = frag.to_xml_string();
        assert_eq!(s1, r#"<div class="box">hello world</div>"#);

        div.set_attribute("class", "box active").unwrap();
        let s2 = frag.to_xml_string();
        assert_eq!(s2, r#"<div class="box active">hello world</div>"#);

        txt.format(0, 5, TextAttributes::from([("bold".into(), Any::True)]))
            .unwrap();
        let s3 = frag.to_xml_string();
        assert_eq!(s3, r#"<div class="box active"><bold>hello</bold> world</div>"#);

        assert!(undo.undo().unwrap().is_some());
        assert_eq!(frag.to_xml_string(), s2);
        assert!(undo.undo().unwrap().is_some());
        assert_eq!(frag.to_xml_string(), s1);
        assert!(undo.undo().unwrap().is_some());
        assert_eq!(frag.to_xml_string(), "");

        assert!(undo.redo().unwrap().is_some());
        assert_eq!(frag.to_xml_string(), s1);
        assert!(undo.redo().unwrap().is_some());
        assert_eq!(frag.to_xml_string(), s2);
        assert!(undo.redo().unwrap().is_some());
        assert_eq!(frag.to_xml_string(), s3);
    }

    #[cfg(not(loom))]
    #[test]
    fn test_xml_transaction_views() {
        let doc = Doc::with_client(1);
        let frag = doc.get_or_create_xml_fragment("xml").unwrap();
        let el = doc.create_xml_element("p").unwrap();
        let txt = doc.create_xml_text().unwrap();
        let hook = doc.create_xml_hook("h").unwrap();

        doc.transact_mut(None, |tx| {
            tx.xml_text(&txt)?.insert(0, "abc")?;
            tx.xml_text(&txt)?
                .format(0, 2, TextAttributes::from([("em".into(), Any::True)]))?;
            tx.xml_element(&el)?.set_attribute("id", "p1")?;
            tx.xml_element(&el)?.push(txt.clone())?;
            tx.xml_hook(&hook)?.insert("k".into(), 9)?;
            tx.xml_fragment(&frag)?.push(el.clone())?;
            tx.xml_fragment(&frag)?.push(hook.clone())?;
            Ok(())
        })
        .unwrap();

        doc.transact(|tx| {
            let f = tx.xml_fragment(&frag)?;
            assert_eq!(f.len(), 2);
            assert_eq!(f.to_xml_string(), r#"<p id="p1"><em>ab</em>c</p>[object Object]"#);
            let e = tx.xml_element(&el)?;
            assert_eq!(e.tag_name(), "p");
            assert_eq!(e.get_attribute("id"), Some(Value::Any(Any::String("p1".into()))));
            let t = tx.xml_text(&txt)?;
            assert_eq!(t.to_xml_string(), "<em>ab</em>c");
            let h = tx.xml_hook(&hook)?;
            assert_eq!(h.hook_name(), "h");
            assert_eq!(h.get("k"), Some(Value::Any(Any::Integer(9))));
            Ok::<(), JwstCodecError>(())
        })
        .unwrap()
        .unwrap();
    }

    #[cfg(not(loom))]
    #[test]
    fn test_xml_siblings_skip_tombstone_with_undo_manager() {
        let doc = Doc::with_client(1);
        let mut frag = doc.get_or_create_xml_fragment("xml").unwrap();
        let _undo = UndoManager::<()>::new(&doc, [(&frag).into()], UndoOptions::default()).unwrap();

        let a = doc.create_xml_element("a").unwrap();
        let b = doc.create_xml_element("b").unwrap();
        let c = doc.create_xml_element("c").unwrap();
        frag.push(a.clone()).unwrap();
        frag.push(b).unwrap();
        frag.push(c.clone()).unwrap();

        frag.remove(1, 1).unwrap();
        assert_eq!(a.next_sibling(), Some(Value::XMLElement(c.clone())));
        assert_eq!(c.prev_sibling(), Some(Value::XMLElement(a)));
    }

    #[test]
    fn test_xml_siblings_skip_tombstone_without_gc() {
        loom_model!({
            let doc = DocOptions::from_identity(1, "no-gc".into()).auto_gc(false).build();
            let mut frag = doc.get_or_create_xml_fragment("xml").unwrap();

            let a = doc.create_xml_element("a").unwrap();
            let b = doc.create_xml_element("b").unwrap();
            let c = doc.create_xml_element("c").unwrap();
            frag.push(a.clone()).unwrap();
            frag.push(b).unwrap();
            frag.push(c.clone()).unwrap();

            frag.remove(1, 1).unwrap();
            assert_eq!(a.next_sibling(), Some(Value::XMLElement(c.clone())));
            assert_eq!(c.prev_sibling(), Some(Value::XMLElement(a)));
        });
    }

    #[test]
    fn test_format_js_float_ecma_262_golden() {
        let cases: &[(f64, &str)] = &[
            (f64::from_bits(0x430c6bf526340002), "1000000000000000.2"),
            (-f64::from_bits(0x430c6bf526340002), "-1000000000000000.2"),
            (1e-7, "1e-7"),
            (1e-6, "0.000001"),
            (1e20, "100000000000000000000"),
            (1e21, "1e+21"),
            (-0.0, "0"),
            (5e-324, "5e-324"),
            (1.5e300, "1.5e+300"),
            (f64::INFINITY, "Infinity"),
            (f64::NEG_INFINITY, "-Infinity"),
            (f64::NAN, "NaN"),
        ];
        for &(val, expected) in cases {
            let mut out = String::new();
            format_js_float(&mut out, val);
            assert_eq!(out, expected, "format_js_float({val:?})");
        }
    }

    #[test]
    fn test_xml_text_enumerable_format_values() {
        loom_model!({
            let doc = Doc::with_client(1);
            let mut txt = doc.get_or_create_xml_text("t").unwrap();
            let arr11 = Any::Array((0..11).map(Any::Integer).collect());
            txt.apply_delta(&[TextDeltaOp::Insert {
                insert: TextInsert::Text("X".into()),
                format: Some(TextAttributes::from([
                    ("link".into(), Any::String("ab".into())),
                    (
                        "arr".into(),
                        Any::Array(vec![Any::String("x".into()), Any::Integer(12)]),
                    ),
                    ("arr11".into(), arr11),
                    ("bin".into(), Any::Binary(vec![7, 8])),
                ])),
            }])
            .unwrap();
            assert_eq!(
                txt.to_xml_string(),
                r#"<arr 0="x" 1="12"><arr11 0="0" 1="1" 10="10" 2="2" 3="3" 4="4" 5="5" 6="6" 7="7" 8="8" 9="9"><bin 0="7" 1="8"><link 0="a" 1="b">X</link></bin></arr11></arr>"#
            );
        });
    }
}
