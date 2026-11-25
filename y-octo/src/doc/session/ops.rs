use super::{PathSegment, SessionReadValue, SessionValue, TypePath, TypeTarget};
use crate::{
    Any, Content, JwstCodecError, JwstCodecResult, TypeIdentity, YTypeKind,
    doc::{
        Carrier, DocStore, HashMap, TypeArena, TypeIdx, YType,
        types::{
            content_any, item_at, list_insert, list_push, map, text,
            xml::{xml_hook_name, xml_tag_name},
        },
    },
};

// ---------------------------------------------------------------------------
// Container kind validation & Unknown kind solidification

pub(crate) fn check_map_read_kind(ty: &YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::Map | YTypeKind::XMLHook | YTypeKind::Unknown => Ok(()),
        _ => Err(JwstCodecError::UnexpectedType("Map or XMLHook")),
    }
}

pub(crate) fn check_array_read_kind(ty: &YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::Array | YTypeKind::XMLFragment | YTypeKind::XMLElement | YTypeKind::Unknown => Ok(()),
        _ => Err(JwstCodecError::UnexpectedType("Array, XMLFragment or XMLElement")),
    }
}

pub(crate) fn check_text_read_kind(ty: &YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::Text | YTypeKind::XMLText | YTypeKind::Unknown => Ok(()),
        _ => Err(JwstCodecError::UnexpectedType("Text or XMLText")),
    }
}

pub(crate) fn solidify_map_kind(ty: &mut YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::Map | YTypeKind::XMLHook => Ok(()),
        YTypeKind::Unknown => ty.set_kind(YTypeKind::Map),
        _ => Err(JwstCodecError::UnexpectedType("Map or XMLHook")),
    }
}

pub(crate) fn solidify_array_kind(ty: &mut YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::Array | YTypeKind::XMLFragment | YTypeKind::XMLElement => Ok(()),
        YTypeKind::Unknown => {
            ty.set_kind(YTypeKind::Array)?;
            if ty.markers.is_none() {
                ty.markers = Some(Box::default());
            }
            Ok(())
        }
        _ => Err(JwstCodecError::UnexpectedType("Array, XMLFragment or XMLElement")),
    }
}

pub(crate) fn solidify_text_kind(ty: &mut YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::Text | YTypeKind::XMLText => Ok(()),
        YTypeKind::Unknown => {
            ty.set_kind(YTypeKind::Text)?;
            if ty.markers.is_none() {
                ty.markers = Some(Box::default());
            }
            Ok(())
        }
        _ => Err(JwstCodecError::UnexpectedType("Text or XMLText")),
    }
}

pub(crate) fn check_xml_element_kind(ty: &YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::XMLElement | YTypeKind::Unknown => Ok(()),
        _ => Err(JwstCodecError::UnexpectedType("XMLElement")),
    }
}

pub(crate) fn solidify_xml_element_kind(ty: &mut YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::XMLElement => Ok(()),
        YTypeKind::Unknown => {
            ty.set_kind(YTypeKind::XMLElement)?;
            if ty.markers.is_none() {
                ty.markers = Some(Box::default());
            }
            Ok(())
        }
        _ => Err(JwstCodecError::UnexpectedType("XMLElement")),
    }
}

pub(crate) fn check_xml_name_kind(ty: &YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::XMLElement | YTypeKind::XMLHook => Ok(()),
        _ => Err(JwstCodecError::UnexpectedType("XMLElement or XMLHook")),
    }
}

pub(crate) fn check_xml_string_kind(ty: &YType) -> JwstCodecResult {
    match ty.kind() {
        YTypeKind::XMLFragment | YTypeKind::XMLElement | YTypeKind::XMLText | YTypeKind::Unknown => Ok(()),
        _ => Err(JwstCodecError::UnexpectedType("XMLFragment, XMLElement or XMLText")),
    }
}

// ---------------------------------------------------------------------------
// Pre-validation before any store mutation

pub(crate) fn validate_session_value(value: &SessionValue, depth: usize) -> JwstCodecResult {
    if depth > Any::DEFAULT_MAX_DEPTH {
        return Err(JwstCodecError::IncompleteDocument(
            "SessionValue nesting exceeds limit".into(),
        ));
    }
    match value {
        SessionValue::Any(_) | SessionValue::Doc { .. } => Ok(()),
        SessionValue::Map(entries) => {
            for (_, v) in entries {
                validate_session_value(v, depth + 1)?;
            }
            Ok(())
        }
        SessionValue::Array(items) | SessionValue::XmlFragment(items) => {
            for v in items {
                validate_session_value(v, depth + 1)?;
            }
            Ok(())
        }
        SessionValue::Text(delta) | SessionValue::XmlText(delta) => text::validate_delta_against_len(0, delta),
        SessionValue::XmlElement { children, .. } => {
            for c in children {
                validate_session_value(c, depth + 1)?;
            }
            Ok(())
        }
        SessionValue::XmlHook { entries, .. } => {
            for (_, v) in entries {
                validate_session_value(v, depth + 1)?;
            }
            Ok(())
        }
    }
}

/// How many types inserting `value` adds to the document: itself and every
/// type nested in it. The value passed [validate_session_value], which bounds
/// its depth.
pub(crate) fn new_type_count(value: &SessionValue) -> usize {
    match value {
        SessionValue::Any(_) | SessionValue::Doc { .. } => 0,
        SessionValue::Text(_) | SessionValue::XmlText(_) => 1,
        SessionValue::Map(entries) | SessionValue::XmlHook { entries, .. } => {
            1 + entries.iter().map(|(_, value)| new_type_count(value)).sum::<usize>()
        }
        SessionValue::Array(items)
        | SessionValue::XmlFragment(items)
        | SessionValue::XmlElement { children: items, .. } => 1 + items.iter().map(new_type_count).sum::<usize>(),
    }
}

// ---------------------------------------------------------------------------
// Store-level resolution, zero-alloc liveness, and path computation

pub(crate) fn resolve_identity_raw(store: &DocStore, id: &TypeIdentity) -> JwstCodecResult<TypeIdx> {
    match id {
        TypeIdentity::Root(name) => store
            .types
            .get(name)
            .copied()
            .ok_or_else(|| JwstCodecError::RootStructNotFound(name.clone())),
        TypeIdentity::Item(item_id) => match store.get_node(*item_id).and_then(|n| n.as_item()) {
            Some(idx) => {
                let item = store.type_arena.items.get(idx).ok_or(JwstCodecError::InvalidParent)?;
                if item.id != *item_id {
                    return Err(JwstCodecError::InvalidParent);
                }
                match &item.content {
                    Content::Type(ty) => Ok(*ty),
                    _ => Err(JwstCodecError::InvalidParent),
                }
            }
            _ => Err(JwstCodecError::InvalidParent),
        },
    }
}

/// Zero-allocation liveness check: walks up the parent type chain verifying
/// no carrier item is deleted and the root is still registered in
/// `store.types`.
pub(crate) fn is_type_alive(store: &DocStore, ty: TypeIdx) -> bool {
    let mut cur = ty;
    loop {
        let Some(ty) = store.type_arena.get(cur) else {
            return false;
        };
        if let Some(root_name) = ty.root_name() {
            return store.types.get(root_name).is_some_and(|root| *root == cur);
        }
        let Some(item) = ty.live_carrier(&store.type_arena.items) else {
            return false;
        };
        if item.deleted() {
            return false;
        }
        match &item.parent {
            Some(parent) => cur = *parent,
            _ => return false,
        }
    }
}

pub(crate) fn compute_type_path(types: &TypeArena, ty: TypeIdx) -> Option<TypePath> {
    let mut segments = Vec::new();
    let mut cur = ty;
    loop {
        let ty = types.get(cur)?;
        if let Some(root_name) = ty.root_name() {
            segments.reverse();
            return Some(TypePath {
                root: root_name.to_owned(),
                segments,
            });
        }
        let item = ty.live_carrier(&types.items)?;
        if item.deleted() {
            return None;
        }
        let Some(parent) = &item.parent else {
            return None;
        };
        if let Some(key) = &item.parent_sub {
            segments.push(PathSegment::Key(key.to_string()));
        } else {
            let mut idx = 0u64;
            let mut left = item.left;
            while let Some(left_item) = left.and_then(|i| types.items.get(i)) {
                if left_item.indexable() {
                    idx += left_item.len();
                }
                left = left_item.left;
            }
            segments.push(PathSegment::Index(idx));
        }
        cur = *parent;
    }
}

pub(crate) fn resolve_path_in_store(store: &DocStore, path: &TypePath) -> JwstCodecResult<TypeIdx> {
    let mut cur = store
        .types
        .get(&path.root)
        .copied()
        .ok_or_else(|| JwstCodecError::RootStructNotFound(path.root.clone()))?;
    for segment in &path.segments {
        let next = {
            let ty = store.type_arena.get(cur).ok_or(JwstCodecError::DocReleased)?;
            match segment {
                PathSegment::Key(key) => {
                    let item =
                        map::map_value(&store.type_arena.items, ty, key).ok_or(JwstCodecError::ParentNotFound)?;
                    match &item.content {
                        Content::Type(child) => *child,
                        _ => return Err(JwstCodecError::InvalidParent),
                    }
                }
                PathSegment::Index(index) => {
                    let (item_ref, offset) =
                        item_at(&store.type_arena.items, ty, *index).ok_or(JwstCodecError::IndexOutOfBound(*index))?;
                    if offset != 0 {
                        return Err(JwstCodecError::InvalidParent);
                    }
                    let item = item_ref
                        .and_then(|i| store.type_arena.items.get(i))
                        .ok_or(JwstCodecError::ParentNotFound)?;
                    match &item.content {
                        Content::Type(child) => *child,
                        _ => return Err(JwstCodecError::InvalidParent),
                    }
                }
            }
        };
        cur = next;
    }
    Ok(cur)
}

pub(crate) fn resolve_target(store: &DocStore, target: &TypeTarget) -> JwstCodecResult<TypeIdx> {
    let ty = match target {
        TypeTarget::Identity(id) => resolve_identity_raw(store, id)?,
        TypeTarget::Path(path) => resolve_path_in_store(store, path)?,
    };
    if !is_type_alive(store, ty) {
        return Err(JwstCodecError::InvalidParent);
    }
    Ok(ty)
}

#[inline]
pub(crate) fn resolve_root(store: &DocStore, name: &str) -> JwstCodecResult<TypeIdx> {
    let ty = store
        .types
        .get(name)
        .copied()
        .ok_or_else(|| JwstCodecError::RootStructNotFound(name.to_owned()))?;
    if !is_type_alive(store, ty) {
        return Err(JwstCodecError::InvalidParent);
    }
    Ok(ty)
}

// ---------------------------------------------------------------------------
// Content read projection & unified atomic nested insertion

fn json_value_to_any(val: serde_json::Value) -> Any {
    match val {
        serde_json::Value::Null => Any::Null,
        serde_json::Value::Bool(b) => Any::from(b),
        serde_json::Value::Number(n) => n.as_f64().map_or(Any::Null, Any::from),
        serde_json::Value::String(s) => Any::String(s),
        serde_json::Value::Array(arr) => Any::Array(arr.into_iter().map(json_value_to_any).collect()),
        serde_json::Value::Object(map) => Any::Object(Box::new(
            map.into_iter().map(|(k, v)| (k, json_value_to_any(v))).collect(),
        )),
    }
}

pub(crate) fn parse_json_content_elem(elem: &Option<String>) -> Any {
    match elem {
        None => Any::Undefined,
        Some(s) => match serde_json::from_str::<serde_json::Value>(s) {
            Ok(val) => json_value_to_any(val),
            Err(_) => Any::String(s.clone()),
        },
    }
}

pub(crate) fn read_value_from_content(types: &TypeArena, content: &Content) -> SessionReadValue {
    match content {
        Content::Type(ty) => {
            let Some(ty) = types.get(*ty) else {
                return SessionReadValue::Any(Any::Undefined);
            };
            let Ok(identity) = ty.identity(&types.items) else {
                return SessionReadValue::Any(Any::Undefined);
            };
            match ty.kind() {
                YTypeKind::Map => SessionReadValue::Map(identity),
                YTypeKind::Array => SessionReadValue::Array(identity),
                YTypeKind::Text => SessionReadValue::Text(identity),
                YTypeKind::XMLElement => SessionReadValue::XmlElement {
                    tag: xml_tag_name(ty).to_string(),
                    identity,
                },
                YTypeKind::XMLFragment => SessionReadValue::XmlFragment(identity),
                YTypeKind::XMLText => SessionReadValue::XmlText(identity),
                YTypeKind::XMLHook => SessionReadValue::XmlHook {
                    name: xml_hook_name(ty).to_string(),
                    identity,
                },
                YTypeKind::Unknown => SessionReadValue::Any(Any::Undefined),
            }
        }
        Content::Doc(doc) => {
            let guid = &doc.guid;
            let gc = match &doc.opts {
                Any::Object(map) => !matches!(map.get("gc"), Some(Any::False)),
                _ => true,
            };
            SessionReadValue::Doc { guid: guid.clone(), gc }
        }
        Content::Json(items) => SessionReadValue::Any(items.last().map_or(Any::Undefined, parse_json_content_elem)),
        other => SessionReadValue::Any(content_any(other).unwrap_or(Any::Undefined)),
    }
}

fn new_child_type(store: &mut DocStore, kind: YTypeKind, name: Option<String>) -> JwstCodecResult<TypeIdx> {
    let mut ytype = YType::new(kind, name);
    ytype.markers = kind.uses_markers().then(Box::default);
    store.type_arena.alloc(ytype)
}

fn doc_content(guid: String, gc: bool) -> Content {
    let opts = Any::Object(Box::new(HashMap::from_iter([
        ("gc".into(), gc.into()),
        ("guid".into(), guid.clone().into()),
    ])));
    Content::doc(guid, opts)
}

fn populate_child_type(store: &mut DocStore, child: TypeIdx, value: SessionValue) -> JwstCodecResult {
    match value {
        SessionValue::Map(entries) => {
            for (k, v) in entries {
                insert_checked(store, child, InsertSlot::MapKey(k), v)?;
            }
            Ok(())
        }
        SessionValue::Array(items) | SessionValue::XmlFragment(items) => {
            for (i, v) in items.into_iter().enumerate() {
                insert_checked(store, child, InsertSlot::ListIndex(i as u64), v)?;
            }
            Ok(())
        }
        SessionValue::Text(delta) | SessionValue::XmlText(delta) => {
            if !delta.is_empty() {
                store.edit_type(child, |store, ty| text::apply_text_delta(store, ty, &delta))?;
            }
            Ok(())
        }
        SessionValue::XmlElement { attrs, children, .. } => {
            for (k, v) in attrs {
                store.edit_type(child, |store, ty| map::map_insert(store, ty, k, Content::from(v)))?;
            }
            for (i, c) in children.into_iter().enumerate() {
                insert_checked(store, child, InsertSlot::ListIndex(i as u64), c)?;
            }
            Ok(())
        }
        SessionValue::XmlHook { entries, .. } => {
            for (k, v) in entries {
                insert_checked(store, child, InsertSlot::MapKey(k), v)?;
            }
            Ok(())
        }
        SessionValue::Any(_) | SessionValue::Doc { .. } => unreachable!("handled by caller"),
    }
}

pub(crate) enum InsertSlot {
    MapKey(String),
    ListIndex(u64),
    ListPush,
}

fn mount_content(store: &mut DocStore, parent: TypeIdx, slot: InsertSlot, content: Content) -> JwstCodecResult {
    match slot {
        InsertSlot::MapKey(key) => store.edit_type(parent, |store, ty| {
            solidify_map_kind(&mut store.type_arena[ty])?;
            map::map_insert(store, ty, key, content)
        }),
        InsertSlot::ListIndex(index) => store.edit_type(parent, |store, ty| {
            solidify_array_kind(&mut store.type_arena[ty])?;
            list_insert(store, ty, index, content)
        }),
        InsertSlot::ListPush => store.edit_type(parent, |store, ty| {
            solidify_array_kind(&mut store.type_arena[ty])?;
            if store.type_arena[ty].kind() == YTypeKind::Array {
                list_push(store, ty, content)
            } else {
                let len = store.type_arena[ty].len;
                list_insert(store, ty, len, content)
            }
        }),
    }
}

/// Validates that `parent` takes a value at `slot`: container compatibility
/// and bounds.
fn check_slot(store: &DocStore, parent: TypeIdx, slot: &InsertSlot) -> JwstCodecResult {
    let ty = store.type_arena.get(parent).ok_or(JwstCodecError::DocReleased)?;
    match slot {
        InsertSlot::MapKey(_) => check_map_read_kind(ty),
        InsertSlot::ListIndex(idx) => {
            check_array_read_kind(ty)?;
            if *idx > ty.len {
                return Err(JwstCodecError::IndexOutOfBound(*idx));
            }
            Ok(())
        }
        InsertSlot::ListPush => check_array_read_kind(ty),
    }
}

/// Inserts a pre-validated [`SessionValue`] into the type `parent` of `store`
/// at `slot`. Nothing changes unless the slot takes a value and every type of
/// `value` fits the document.
pub(crate) fn insert_session_value(
    store: &mut DocStore,
    parent: TypeIdx,
    slot: InsertSlot,
    value: SessionValue,
) -> JwstCodecResult {
    check_slot(store, parent, &slot)?;
    store.type_arena.check_capacity(new_type_count(&value))?;
    insert_checked(store, parent, slot, value)
}

/// [insert_session_value] once the types of the whole value are known to fit.
fn insert_checked(store: &mut DocStore, parent: TypeIdx, slot: InsertSlot, value: SessionValue) -> JwstCodecResult {
    // Validate parent container compatibility and bounds BEFORE allocating any
    // child type in the store's arena or solidifying an `Unknown` root.
    check_slot(store, parent, &slot)?;
    match value {
        SessionValue::Any(any) => mount_content(store, parent, slot, Content::from(any)),
        SessionValue::Doc { guid, gc } => mount_content(store, parent, slot, doc_content(guid, gc)),
        value => {
            let (kind, name) = match &value {
                SessionValue::Map(_) => (YTypeKind::Map, None),
                SessionValue::Array(_) => (YTypeKind::Array, None),
                SessionValue::Text(_) => (YTypeKind::Text, None),
                SessionValue::XmlElement { tag, .. } => (YTypeKind::XMLElement, Some(tag.clone())),
                SessionValue::XmlFragment(_) => (YTypeKind::XMLFragment, None),
                SessionValue::XmlText(_) => (YTypeKind::XMLText, None),
                SessionValue::XmlHook { name, .. } => (YTypeKind::XMLHook, Some(name.clone())),
                SessionValue::Any(_) | SessionValue::Doc { .. } => unreachable!(),
            };
            // The child stays in the arena only once its carrier is mounted.
            let types_before = store.type_arena.len();
            let child = new_child_type(store, kind, name)?;
            if let Err(err) = mount_content(store, parent, slot, Content::Type(child)) {
                if !matches!(
                    store.type_arena[child].carrier(&store.type_arena.items),
                    Carrier::Live(_)
                ) {
                    store.type_arena.rollback(types_before);
                }
                return Err(err);
            }
            populate_child_type(store, child, value)
        }
    }
}
