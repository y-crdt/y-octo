use super::*;

fn delta(text: &str, format: Option<TextAttributes>) -> TextDeltaOp {
    TextDeltaOp::Insert {
        insert: TextInsert::Text(text.into()),
        format,
    }
}

fn leave_slots(doc: &Doc, available: usize) {
    let mut store = doc.store.write().unwrap();
    let arena = &mut store.type_arena.items;
    arena.set_limit(arena.slots - arena.free.len() + available);
}

fn restore_slots(doc: &Doc) {
    doc.store.write().unwrap().type_arena.items.set_limit(u32::MAX as usize);
}

#[test]
fn empty_text_delta_allows_delete_and_insert() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "ab").unwrap();
    text.apply_delta(&[delta("", None)]).unwrap();
    text.remove(0, 1).unwrap();
    text.insert(0, "z").unwrap();
    assert_eq!(text.to_string(), "zb");
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn empty_text_delta_roundtrips_after_append_and_delete() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "ab").unwrap();
    text.apply_delta(&[delta("", None)]).unwrap();
    text.insert(2, "c").unwrap();
    text.remove(0, 1).unwrap();
    let mut peer = Doc::with_client(2);
    peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
        .unwrap();
    assert_eq!(text.to_string(), "bc");
    assert_eq!(peer.get_or_create_text("text").unwrap().to_string(), "bc");
    assert_eq!(peer.get_state_vector(), doc.get_state_vector());
    assert_eq!(peer.get_delete_sets(), doc.get_delete_sets());
}

#[test]
fn empty_text_delta_in_deleted_subtree_collects() {
    let doc = Doc::with_client(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    let mut text = doc.create_text().unwrap();
    map.insert("text".into(), text.clone()).unwrap();
    text.insert(0, "ab").unwrap();
    text.apply_delta(&[delta("", None)]).unwrap();
    map.remove("text");
    doc.gc().unwrap();
    assert!(!map.contains_key("text"));
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn empty_formatted_delta_preserves_clocks_and_formatting() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "ab").unwrap();
    let before = (text.to_delta(), doc.get_state_vector(), doc.encode_update_v1().unwrap());
    text.apply_delta(&[delta("", Some(TextAttributes::from([("bold".into(), Any::True)])))])
        .unwrap();
    assert_eq!(
        (text.to_delta(), doc.get_state_vector(), doc.encode_update_v1().unwrap()),
        before
    );
    let ty = text.as_inner().idx().unwrap();
    let mut store = doc.store.write().unwrap();
    let item = store.create_item(Content::String(String::new()), None, None, Some(ty), None);
    assert!(matches!(
        store.integrate_item(item, 0, Some(ty)),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    store.self_check().unwrap();
}

fn markers(ty: &YTypeRef) -> Vec<(ItemRef, u64)> {
    ty.read(|_, ty| {
        ty.markers
            .as_ref()
            .expect("marker cache")
            .iter()
            .map(|m| (m.ptr, m.index))
            .collect()
    })
    .unwrap()
}

#[test]
fn mounted_nested_markers_refill_after_remote_commit() {
    let doc = Doc::with_client(1);
    let mut root = doc.get_or_create_map("root").unwrap();
    let mut outer = doc.create_map().unwrap();
    let mut array = doc.create_array().unwrap();
    let mut text = doc.create_text().unwrap();
    array.push(0).unwrap();
    text.insert(0, "a").unwrap();
    outer.insert("array".into(), array.clone()).unwrap();
    outer.insert("text".into(), text.clone()).unwrap();
    root.insert("outer".into(), outer).unwrap();
    assert!(markers(array.as_inner()).is_empty());
    assert!(markers(text.as_inner()).is_empty());
    for n in 1..6 {
        array.insert(0, n).unwrap();
        text.insert(0, "x").unwrap();
    }
    array.insert(3, 8).unwrap();
    text.insert(3, "y").unwrap();
    assert!(!markers(array.as_inner()).is_empty());
    assert!(!markers(text.as_inner()).is_empty());

    let mut peer = Doc::with_client(2);
    peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
        .unwrap();
    let Value::Map(remote) = peer.get_map("root").unwrap().get("outer").unwrap() else {
        panic!("expected map")
    };
    let Value::Array(mut a) = remote.get("array").unwrap() else {
        panic!("expected array")
    };
    let Value::Text(mut t) = remote.get("text").unwrap() else {
        panic!("expected text")
    };
    a.insert(0, 7).unwrap();
    t.insert(0, "r").unwrap();
    doc.apply_update_with_origin(peer.encode_state_as_update(&doc.get_state_vector()).unwrap(), None)
        .unwrap();
    assert!(markers(array.as_inner()).is_empty());
    assert!(markers(text.as_inner()).is_empty());
    array.insert(3, 9).unwrap();
    text.insert(3, "z").unwrap();
    assert!(!markers(array.as_inner()).is_empty());
    assert!(!markers(text.as_inner()).is_empty());
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn preliminary_mount_reserves_carrier_and_contents_together() {
    let doc = Doc::with_client(1);
    let mut root = doc.get_or_create_map("root").unwrap();
    let mut child = doc.create_map().unwrap();
    child.insert("value".into(), 7).unwrap();
    let before = doc.encode_update_v1().unwrap();
    leave_slots(&doc, 1);
    assert!(matches!(
        root.insert("child".into(), child.clone()),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    assert!(!root.contains_key("child"));
    assert_eq!(child.id(), None);
    assert_eq!(serde_json::to_value(&child).unwrap(), serde_json::json!({"value":7}));
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    doc.store.read().unwrap().self_check().unwrap();
    restore_slots(&doc);
    root.insert("child".into(), child.clone()).unwrap();
    assert!(child.id().is_some());
    assert_eq!(
        serde_json::to_value(root).unwrap(),
        serde_json::json!({"child":{"value":7}})
    );
}

#[test]
fn remote_item_capacity_failure_leaves_no_named_root() {
    let source = Doc::with_client(1);
    source.get_or_create_map("new").unwrap().insert("x".into(), 7).unwrap();
    let bytes = source.encode_update_v1().unwrap();
    let mut peer = Doc::with_client(2);
    leave_slots(&peer, 0);
    assert!(matches!(
        peer.apply_update_from_binary_v1(&bytes),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    assert!(!peer.store.read().unwrap().types.contains_key("new"));
    assert_eq!(peer.get_state_vector().get(&1), 0);
    restore_slots(&peer);
    peer.apply_update_from_binary_v1(bytes).unwrap();
    assert_eq!(
        serde_json::to_value(peer.get_map("new").unwrap()).unwrap(),
        serde_json::json!({"x":7})
    );
}

#[test]
fn failed_cross_block_delete_keeps_event_and_wire_in_sync() {
    let doc = Doc::with_client(1);
    let mut a = doc.get_or_create_text("a").unwrap();
    let mut b = doc.get_or_create_text("b").unwrap();
    a.insert(0, "ab").unwrap();
    b.insert(0, "cd").unwrap();
    let (_sub, events) = {
        let events = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let sink = events.clone();
        (doc.subscribe(move |e| sink.lock().unwrap().push(e.clone())), events)
    };
    let mut peer = Doc::with_client(2);
    peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
        .unwrap();
    leave_slots(&doc, 0);
    assert!(matches!(
        doc.transact_mut(None, |tx| tx.store_mut().delete_range(1, 0..3)),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    assert!(events.lock().unwrap().is_empty());
    assert_eq!((a.to_string(), b.to_string()), ("ab".into(), "cd".into()));
    assert_eq!(doc.get_delete_sets(), peer.get_delete_sets());
    restore_slots(&doc);
    doc.transact_mut(None, |tx| tx.store_mut().delete_range(1, 0..3))
        .unwrap();
    let events = events.lock().unwrap();
    assert_eq!(events.len(), 1);
    assert_eq!(events[0].deleted, doc.get_delete_sets());
    peer.apply_update_from_binary_v1(&events[0].update).unwrap();
    assert_eq!(peer.get_delete_sets(), doc.get_delete_sets());
    assert_eq!(peer.get_or_create_text("b").unwrap().to_string(), "d");
}

#[test]
fn failed_list_and_rich_text_insert_preserve_marker_positions() {
    let doc = Doc::with_client(1);
    let mut array = doc.get_or_create_array("a").unwrap();
    let mut text = doc.get_or_create_text("t").unwrap();
    for n in 0..6 {
        array.insert(0, n).unwrap();
        text.insert(0, n.to_string()).unwrap();
    }
    text.format(0, 1, TextAttributes::from([("bold".into(), Any::True)]))
        .unwrap();
    array.insert(3, 7).unwrap();
    text.insert(3, "z").unwrap();
    let am = markers(array.as_inner());
    let tm = markers(text.as_inner());
    assert!(am.iter().any(|(_, i)| *i > 0) && tm.iter().any(|(_, i)| *i > 0));
    let before = (array.get(3), text.to_delta(), doc.encode_update_v1().unwrap());
    leave_slots(&doc, 0);
    assert!(array.insert(0, 9).is_err());
    assert!(text.insert(0, "a").is_err());
    assert!(text.apply_delta(&[delta("b", None)]).is_err());
    assert_eq!(markers(array.as_inner()), am);
    assert_eq!(markers(text.as_inner()), tm);
    assert_eq!((array.get(3), text.to_delta(), doc.encode_update_v1().unwrap()), before);
    restore_slots(&doc);
    text.insert(3, "q").unwrap();
    assert_eq!(text.to_string(), "543qz210");
}

fn failed_pop_keeps_history(doc: &Doc, undo: &UndoManager<u64>) -> UndoItem<u64> {
    let id = undo.peek(UndoStack::Undo).unwrap().id;
    undo.set_meta(UndoStack::Undo, id, 42).unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    let bytes = doc.encode_update_v1().unwrap();
    leave_slots(doc, 0);
    assert!(matches!(undo.undo(), Err(JwstCodecError::IncompleteDocument(_))));
    assert_eq!(doc.encode_update_v1().unwrap(), bytes);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    assert!(!undo.can_redo());
    doc.store.read().unwrap().self_check().unwrap();
    restore_slots(doc);
    top
}

#[test]
fn undo_prefix_split_capacity_preserves_suffix_and_history() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = UndoManager::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
    text.insert(0, "ab").unwrap();
    doc.transact_mut(Origin::new("untracked"), |tx| tx.text(&text)?.insert(2, "cd"))
        .unwrap();
    assert_eq!(doc.store.read().unwrap().get_node(Id::new(1, 0)).unwrap().len(), 4);
    let top = failed_pop_keeps_history(&doc, &undo);
    assert_eq!(text.to_string(), "abcd");
    assert_eq!(undo.undo().unwrap(), Some(top));
    assert_eq!(text.to_string(), "cd");
    assert!(undo.can_redo());
}

#[test]
fn undo_scalar_copy_capacity_preserves_value_and_history() {
    let doc = Doc::with_client(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("key".into(), 7).unwrap();
    let undo = UndoManager::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    map.remove("key");
    let top = failed_pop_keeps_history(&doc, &undo);
    assert!(!map.contains_key("key"));
    assert_eq!(undo.undo().unwrap(), Some(top));
    assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"key":7}));
    assert!(undo.can_redo());
}

#[test]
fn preliminary_clock_overflow_preserves_staging() {
    let mut doc = Doc::with_client(1);
    let mut root = doc.get_or_create_map("root").unwrap();
    let mut child = doc.create_text().unwrap();
    child.insert(0, "ab").unwrap();
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, 0), u64::MAX - 2))
        .unwrap();
    let before = doc.get_state_vector();
    assert!(matches!(
        root.insert("child".into(), child.clone()),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    assert_eq!(doc.get_state_vector(), before);
    assert!(!root.contains_key("child"));
    assert_eq!(child._id(), None);
    assert_eq!(child.to_string(), "ab");
    doc.store.read().unwrap().self_check().unwrap();
    doc.set_client(2);
    root.insert("child".into(), child.clone()).unwrap();
    assert_eq!(child._id(), Some(Id::new(2, 0)));
    assert_eq!(child.to_string(), "ab");
}

#[test]
fn cascade_delete_and_undo_preserve_utf16_child() {
    let doc = DocOptions::from_identity(1, "root".into()).auto_gc(false).build();
    let mut root = doc.get_or_create_map("root").unwrap();
    let mut child = doc.create_text().unwrap();
    root.insert("child".into(), child.clone()).unwrap();
    child.insert(0, "😀").unwrap();

    let undo = UndoManager::<()>::new(&doc, [(&root).into()], UndoOptions::default()).unwrap();
    let origin = Origin::new("remote edit");
    undo.add_tracked_origin(Some(origin.clone())).unwrap();
    // A deletion covering the carrier and the first UTF-16 unit of its child.
    let deletion = Update::decode_v1([0, 1, 1, 1, 0, 2]).unwrap();
    doc.apply_update_with_origin(deletion, origin).unwrap();
    assert!(!root.contains_key("child"));
    let encoded = doc.encode_update_v1().unwrap();
    assert!(encoded.windows("😀".len()).any(|s| s == "😀".as_bytes()));
    assert!(!encoded.windows("�".len()).any(|s| s == "�".as_bytes()));
    assert!(undo.undo().unwrap().is_some());
    let Some(Value::Text(restored)) = root.get("child") else {
        panic!("expected restored text")
    };
    assert_eq!(restored.to_string(), "😀");
}

#[test]
fn middle_insert_reserves_the_split_and_formatted_content() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "😀").unwrap();
    let before = doc.encode_update_v1().unwrap();
    let mut peer = Doc::with_client(2);
    peer.apply_update_from_binary_v1(&before).unwrap();
    leave_slots(&doc, 1);
    assert!(matches!(
        text.insert(1, "x"),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    assert_eq!(text.to_string(), "😀");
    leave_slots(&doc, 3); // Split, opening marker, content and closing marker require four.
    let ops = [
        TextDeltaOp::Retain {
            retain: 1,
            format: None,
        },
        delta("x", Some(TextAttributes::from([("bold".into(), Any::True)]))),
    ];
    assert!(matches!(
        text.apply_delta(&ops),
        Err(JwstCodecError::IncompleteDocument(_))
    ));
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    assert_eq!(text.to_string(), peer.get_or_create_text("t").unwrap().to_string());
    restore_slots(&doc);
    text.insert(1, "x").unwrap();
    assert_eq!(text.to_string(), "�x�");
}

#[test]
fn undo_clock_overflow_preserves_history_for_another_client() {
    let mut doc = Doc::with_client(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("key".into(), 7).unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    map.remove("key");
    let id = undo.peek(UndoStack::Undo).unwrap().id;
    undo.set_meta(UndoStack::Undo, id, 42).unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, 1), u64::MAX - 1))
        .unwrap();
    let before = doc.encode_update_v1().unwrap();
    assert!(matches!(undo.undo(), Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"));
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    assert!(!undo.can_redo());
    doc.set_client(2);
    assert_eq!(undo.undo().unwrap(), Some(top));
    assert_eq!(serde_json::to_value(map).unwrap(), serde_json::json!({"key":7}));
}

#[test]
fn zero_length_node_leaves_client_timelines_unchanged() {
    let doc = Doc::with_client(1);
    let mut store = doc.store.write().unwrap();
    let before = store.get_state_vector();
    let id = Id::new(7, 0);
    assert!(
        matches!(store.add_node(Node::new_gc(id, 0)), Err(JwstCodecError::IncompleteDocument(s)) if s == "zero-length struct")
    );
    for offset in [1, 2] {
        assert!(
            matches!(store.integrate_wire(WireStruct::Gc { id, len: 1 }, offset), Err(JwstCodecError::IncompleteDocument(s)) if s == "zero-length struct")
        );
    }
    assert!(!store.items.contains_key(&7));
    assert_eq!(store.get_state_vector(), before);
}
