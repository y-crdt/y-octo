use super::{PathSegment, SessionReadValue, SessionValue, TypePath, TypeTarget};
use crate::{
    Any, Content, JwstCodecError, JwstCodecResult, TypeIdentity, Value, YTypeKind,
    doc::{
        DocStore, HashMap, MarkerList, Node, Parent, Somr, YType, YTypeRef,
        store::StoreRef,
        types::{
            item_at, list_insert, map, text,
            xml::{xml_hook_name, xml_tag_name},
        },
    },
    sync::Arc,
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
                ty.markers = Some(MarkerList::new());
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
                ty.markers = Some(MarkerList::new());
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
                ty.markers = Some(MarkerList::new());
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

// ---------------------------------------------------------------------------
// Store-level resolution, zero-alloc liveness, and path computation

pub(crate) fn resolve_identity_raw(store: &DocStore, id: &TypeIdentity) -> JwstCodecResult<YTypeRef> {
    match id {
        TypeIdentity::Root(name) => store
            .types
            .get(name)
            .cloned()
            .ok_or_else(|| JwstCodecError::RootStructNotFound(name.clone())),
        TypeIdentity::Item(item_id) => match store.get_node(*item_id) {
            Some(Node::Item(item_ref)) => {
                let item = item_ref.get().ok_or(JwstCodecError::InvalidParent)?;
                if item.id != *item_id {
                    return Err(JwstCodecError::InvalidParent);
                }
                match &item.content {
                    Content::Type(ty_ref) => Ok(ty_ref.clone()),
                    _ => Err(JwstCodecError::InvalidParent),
                }
            }
            _ => Err(JwstCodecError::InvalidParent),
        },
    }
}

/// Zero-allocation liveness check: walks up the `Parent::Type` chain verifying
/// no carrier item is deleted and the root is still registered in
/// `store.types`.
pub(crate) fn is_type_alive(store: &DocStore, ty_ref: &YTypeRef) -> bool {
    let mut cur = ty_ref;
    loop {
        let Some(ty) = cur.ty() else {
            return false;
        };
        if let Some(root_name) = &ty.root_name {
            return store.types.get(root_name).is_some_and(|root| root == cur);
        }
        let Some(item) = ty.item.get() else {
            return false;
        };
        if item.deleted() {
            return false;
        }
        match &item.parent {
            Some(Parent::Type(parent_ref)) => cur = parent_ref,
            _ => return false,
        }
    }
}

pub(crate) fn compute_type_path(ty_ref: &YTypeRef) -> Option<TypePath> {
    let mut segments = Vec::new();
    let mut cur = ty_ref.clone();
    loop {
        let ty = cur.ty()?;
        if let Some(root_name) = &ty.root_name {
            segments.reverse();
            return Some(TypePath {
                root: root_name.clone(),
                segments,
            });
        }
        let item = ty.item.get()?;
        if item.deleted() {
            return None;
        }
        let Some(Parent::Type(parent_ref)) = &item.parent else {
            return None;
        };
        if let Some(key) = &item.parent_sub {
            segments.push(PathSegment::Key(key.to_string()));
        } else {
            let mut idx = 0u64;
            let mut left = item.left.clone();
            while let Some(left_item) = left.get() {
                if left_item.indexable() {
                    idx += left_item.len();
                }
                left = left_item.left.clone();
            }
            segments.push(PathSegment::Index(idx));
        }
        cur = parent_ref.clone();
    }
}

pub(crate) fn resolve_path_in_store(store: &DocStore, path: &TypePath) -> JwstCodecResult<YTypeRef> {
    let mut cur = store
        .types
        .get(&path.root)
        .cloned()
        .ok_or_else(|| JwstCodecError::RootStructNotFound(path.root.clone()))?;
    for segment in &path.segments {
        let next = {
            let ty = cur.ty().ok_or(JwstCodecError::DocReleased)?;
            match segment {
                PathSegment::Key(key) => {
                    let item = map::map_value(ty, key).ok_or(JwstCodecError::ParentNotFound)?;
                    match &item.content {
                        Content::Type(child) => child.clone(),
                        _ => return Err(JwstCodecError::InvalidParent),
                    }
                }
                PathSegment::Index(index) => {
                    let (item_ref, offset) =
                        item_at(&cur, ty, *index).ok_or(JwstCodecError::IndexOutOfBound(*index))?;
                    if offset != 0 {
                        return Err(JwstCodecError::InvalidParent);
                    }
                    let item = item_ref.get().ok_or(JwstCodecError::ParentNotFound)?;
                    match &item.content {
                        Content::Type(child) => child.clone(),
                        _ => return Err(JwstCodecError::InvalidParent),
                    }
                }
            }
        };
        cur = next;
    }
    Ok(cur)
}

pub(crate) fn resolve_target(store: &DocStore, target: &TypeTarget) -> JwstCodecResult<YTypeRef> {
    let ty_ref = match target {
        TypeTarget::Identity(id) => resolve_identity_raw(store, id)?,
        TypeTarget::Path(path) => resolve_path_in_store(store, path)?,
    };
    if !is_type_alive(store, &ty_ref) {
        return Err(JwstCodecError::InvalidParent);
    }
    Ok(ty_ref)
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

pub(crate) fn read_value_from_content(content: &Content) -> SessionReadValue {
    match content {
        Content::Type(ty_ref) => {
            let Some(ty) = ty_ref.ty() else {
                return SessionReadValue::Any(Any::Undefined);
            };
            let Ok(identity) = ty.identity() else {
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
        Content::Doc { guid, opts } => {
            let gc = match opts.as_ref() {
                Any::Object(map) => !matches!(map.get("gc"), Some(Any::False)),
                _ => true,
            };
            SessionReadValue::Doc { guid: guid.clone(), gc }
        }
        Content::Json(items) => SessionReadValue::Any(items.last().map_or(Any::Undefined, parse_json_content_elem)),
        other => match Value::from(other) {
            Value::Any(any) => SessionReadValue::Any(any),
            _ => SessionReadValue::Any(Any::Undefined),
        },
    }
}

fn new_child_type(store: &mut DocStore, store_ref: &StoreRef, kind: YTypeKind, name: Option<String>) -> YTypeRef {
    let mut ytype = YType::new(kind, name);
    ytype.markers = kind.uses_markers().then(MarkerList::new);
    let inner = Somr::new(ytype);
    let ty = YTypeRef {
        store: Arc::downgrade(store_ref),
        inner,
    };
    let ty_ref = ty.clone();
    store.dangling_types.insert(ty.inner.ptr().as_ptr() as usize, ty);
    ty_ref
}

fn doc_content(guid: String, gc: bool) -> Content {
    let opts = Any::Object(Box::new(HashMap::from_iter([
        ("gc".into(), gc.into()),
        ("guid".into(), guid.clone().into()),
    ])));
    Content::Doc {
        guid,
        opts: Box::new(opts),
    }
}

fn populate_child_type(
    store: &mut DocStore,
    store_ref: &StoreRef,
    child: &YTypeRef,
    value: SessionValue,
) -> JwstCodecResult {
    match value {
        SessionValue::Map(entries) => {
            for (k, v) in entries {
                insert_session_value(store, store_ref, child, InsertSlot::MapKey(k), v)?;
            }
            Ok(())
        }
        SessionValue::Array(items) | SessionValue::XmlFragment(items) => {
            for (i, v) in items.into_iter().enumerate() {
                insert_session_value(store, store_ref, child, InsertSlot::ListIndex(i as u64), v)?;
            }
            Ok(())
        }
        SessionValue::Text(delta) | SessionValue::XmlText(delta) => {
            if !delta.is_empty() {
                child.write_locked(store, |store, ty| text::apply_text_delta(child, store, ty, &delta))?;
            }
            Ok(())
        }
        SessionValue::XmlElement { attrs, children, .. } => {
            for (k, v) in attrs {
                child.write_locked(store, |store, ty| {
                    map::map_insert(child, store, ty, k, Content::from(v))
                })?;
            }
            for (i, c) in children.into_iter().enumerate() {
                insert_session_value(store, store_ref, child, InsertSlot::ListIndex(i as u64), c)?;
            }
            Ok(())
        }
        SessionValue::XmlHook { entries, .. } => {
            for (k, v) in entries {
                insert_session_value(store, store_ref, child, InsertSlot::MapKey(k), v)?;
            }
            Ok(())
        }
        SessionValue::Any(_) | SessionValue::Doc { .. } => unreachable!("handled by caller"),
    }
}

pub(crate) enum InsertSlot {
    MapKey(String),
    ListIndex(u64),
}

fn mount_content(store: &mut DocStore, parent: &YTypeRef, slot: InsertSlot, content: Content) -> JwstCodecResult {
    match slot {
        InsertSlot::MapKey(key) => parent.write_locked(store, |store, ty| {
            solidify_map_kind(ty)?;
            map::map_insert(parent, store, ty, key, content)
        }),
        InsertSlot::ListIndex(index) => parent.write_locked(store, |store, ty| {
            solidify_array_kind(ty)?;
            list_insert(parent, store, ty, index, content)
        }),
    }
}

/// Inserts a pre-validated [`SessionValue`] into `parent` at `slot`.
pub(crate) fn insert_session_value(
    store: &mut DocStore,
    store_ref: &StoreRef,
    parent: &YTypeRef,
    slot: InsertSlot,
    value: SessionValue,
) -> JwstCodecResult {
    // Validate parent container compatibility and bounds BEFORE allocating any
    // child type into `store.dangling_types` or solidifying an `Unknown` root.
    {
        let ty = parent.ty().ok_or(JwstCodecError::DocReleased)?;
        match &slot {
            InsertSlot::MapKey(_) => check_map_read_kind(ty)?,
            InsertSlot::ListIndex(idx) => {
                check_array_read_kind(ty)?;
                if *idx > ty.len {
                    return Err(JwstCodecError::IndexOutOfBound(*idx));
                }
            }
        }
    }
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
            let child = new_child_type(store, store_ref, kind, name);
            mount_content(store, parent, slot, Content::Type(child.clone()))?;
            populate_child_type(store, store_ref, &child, value)
        }
    }
}
