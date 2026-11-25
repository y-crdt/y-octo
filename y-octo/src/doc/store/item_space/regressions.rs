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
    arena.set_limit(arena.occupied() + available);
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

#[test]
fn middle_insert_clock_overflow_preserves_utf16_and_wire() {
    let mut doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "😀").unwrap();
    // Exhaust local client clock to u64::MAX while item slots remain ample.
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, 2), u64::MAX - 2))
        .unwrap();
    let before = doc.encode_update_v1().unwrap();
    let mut peer = Doc::with_client(2);
    peer.apply_update_from_binary_v1(&before).unwrap();

    assert!(matches!(
        text.insert(1, "x"),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(text.to_string(), "😀");
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    assert_eq!(peer.get_or_create_text("t").unwrap().to_string(), "😀");
    assert_eq!(doc.get_state_vector(), peer.get_state_vector());
    doc.store.read().unwrap().self_check().unwrap();

    // Also cover list_insert with an embed and a preliminary subtree whose
    // carrier fits in the remaining clock (1 left) but whose visible child
    // overflows.
    assert!(matches!(
        text.insert_embed(1, Any::True),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(text.to_string(), "😀");
    assert_eq!(doc.encode_update_v1().unwrap(), before);

    doc.set_client(3);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(3, 0), u64::MAX - 1))
        .unwrap();
    let before_prelim = doc.encode_update_v1().unwrap();
    let mut prelim = doc.create_text().unwrap();
    prelim.insert(0, "ab").unwrap();
    let ty = text.as_inner().idx().unwrap();
    assert!(matches!(
        doc.store.write().unwrap().edit_type(ty, |store, ty| {
            crate::doc::list_insert(store, ty, 1, Content::Type(prelim.as_inner().idx().unwrap()))
        }),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(text.to_string(), "😀");
    assert_eq!(prelim._id(), None);
    assert_eq!(prelim.to_string(), "ab");
    assert_eq!(doc.encode_update_v1().unwrap(), before_prelim);
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn formatted_middle_insert_and_format_clock_overflow() {
    // Case 1: fast-path upper bound (content + 2 * attrs = 3) overflows when
    // only 1 clock remains, but exact clocks needed = 1 (same bold attr already
    // active).
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("t").unwrap();
    let bold = TextAttributes::from([("bold".into(), Any::True)]);
    text.apply_delta(&[delta("ab", Some(bold.clone()))]).unwrap();
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 1))
        .unwrap();
    let ops = [
        TextDeltaOp::Retain {
            retain: 1,
            format: None,
        },
        delta("x", Some(bold.clone())),
    ];
    text.apply_delta(&ops).unwrap();
    assert_eq!(text.to_string(), "axb");
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
    // 0-clock no-op format on already-bold span also succeeds at u64::MAX.
    text.format(0, 3, bold.clone()).unwrap();
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
    doc.store.read().unwrap().self_check().unwrap();

    // Case 2: plain "😀", formatted middle insert needs 3 clocks (opening +
    // content + closing) but only 2 clocks remain -> must fail before splitting
    // "😀" or writing opening format.
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "😀").unwrap();
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, 2), u64::MAX - 4))
        .unwrap();
    let before_delta = text.to_delta();
    let before_wire = doc.encode_update_v1().unwrap();
    let ops = [
        TextDeltaOp::Retain {
            retain: 1,
            format: None,
        },
        delta("x", Some(bold.clone())),
    ];
    assert!(matches!(
        text.apply_delta(&ops),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(text.to_string(), "😀");
    assert_eq!(text.to_delta(), before_delta);
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);
    doc.store.read().unwrap().self_check().unwrap();

    // Case 3: format_text on interior of "😀" needs 2 clocks (opening +
    // closing), fails cleanly when only 1 clock remains without splitting "😀".
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "😀").unwrap();
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, 2), u64::MAX - 3))
        .unwrap();
    let before_delta = text.to_delta();
    let before_format_wire = doc.encode_update_v1().unwrap();
    assert!(matches!(
        text.format(1, 1, bold),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(text.to_string(), "😀");
    assert_eq!(text.to_delta(), before_delta);
    assert_eq!(doc.encode_update_v1().unwrap(), before_format_wire);
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_zero_clock_succeeds_at_u64_max_and_real_overflow_still_rejected() {
    // Part 1: 0-clock undo succeeds even when local client clock is at
    // u64::MAX.
    let doc = Doc::with_client(1);
    let map = doc.get_or_create_map("map").unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    doc.transact_mut(None, |tx| {
        let mut m = tx.map(&map)?;
        m.insert("k".into(), 1)?;
        m.insert("k".into(), 2)?;
        Ok(())
    })
    .unwrap();
    assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"k": 2}));
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur))
        .unwrap();
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);

    assert!(undo.undo().unwrap().is_some());
    assert!(!map.contains_key("k"));
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
    doc.store.read().unwrap().self_check().unwrap();

    // Part 2: undo that genuinely needs 2 new clocks fails cleanly when only 1
    // clock remains, preserving stack, metadata, and document state; switching
    // to another client lets the undo succeed.
    let mut doc = Doc::with_client(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("a".into(), 1).unwrap();
    map.insert("b".into(), 2).unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    doc.transact_mut(None, |tx| {
        let mut m = tx.map(&map)?;
        m.remove("a");
        m.remove("b");
        Ok(())
    })
    .unwrap();
    let id = undo.peek(UndoStack::Undo).unwrap().id;
    undo.set_meta(UndoStack::Undo, id, 99).unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 1))
        .unwrap();
    let before = doc.encode_update_v1().unwrap();

    assert!(matches!(
        undo.undo(),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(doc.encode_update_v1().unwrap(), before);
    assert!(!map.contains_key("a") && !map.contains_key("b"));
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    assert!(!undo.can_redo());
    doc.store.read().unwrap().self_check().unwrap();

    doc.set_client(2);
    assert_eq!(undo.undo().unwrap(), Some(top));
    assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"a": 1, "b": 2}));
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_same_window_map_two_clients_overflow_is_atomic() {
    // Client 2 writes k=A, deleted in tracked window; remote client 1 writes
    // k=B, also deleted in the same capture window. With only 1 clock left,
    // undo needs 2 clocks (both B and A recreated in client-id order) and must
    // reject atomically without partially recreating B'.
    let mut doc = Doc::with_client(2);
    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("k".into(), "A").unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    undo.advance_time(100);
    let tracked = Origin::new("tracked");
    undo.add_tracked_origin(Some(tracked.clone())).unwrap();
    doc.transact_mut(Some(tracked.clone()), |tx| {
        tx.map(&map)?.remove("k");
        Ok(())
    })
    .unwrap();
    let mut peer = Doc::with_client(1);
    peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
        .unwrap();
    peer.get_or_create_map("map").unwrap().insert("k".into(), "B").unwrap();
    let remote_update = Update::decode_v1(peer.encode_update_v1().unwrap()).unwrap();
    doc.apply_update_with_origin(remote_update, Origin::new("remote"))
        .unwrap();
    doc.transact_mut(Some(tracked), |tx| {
        tx.map(&map)?.remove("k");
        Ok(())
    })
    .unwrap();

    let cur = doc.get_state_vector().get(&2);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(2, cur), u64::MAX - cur - 1))
        .unwrap();
    let before_wire = doc.encode_update_v1().unwrap();
    let before_sv = doc.get_state_vector();
    let top = undo.peek(UndoStack::Undo).unwrap();

    assert!(matches!(
        undo.undo(),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);
    assert_eq!(doc.get_state_vector(), before_sv);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    assert!(!map.contains_key("k"));
    doc.store.read().unwrap().self_check().unwrap();

    doc.set_client(3);
    assert_eq!(undo.undo().unwrap(), Some(top));
    assert!(map.contains_key("k"));
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_children_of_remote_overwritten_map_carrier_succeeds_at_u64_max() {
    let mut doc = Doc::with_client(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    let mut text = doc.create_text().unwrap();
    map.insert("k".into(), text.clone()).unwrap();
    text.insert(0, "abc").unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    map.remove("k");
    assert!(undo.can_undo());

    let mut peer = Doc::with_client(2);
    peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
        .unwrap();
    peer.get_or_create_map("map").unwrap().insert("k".into(), 5).unwrap();
    doc.apply_update_from_binary_v1(peer.encode_update_v1().unwrap())
        .unwrap();

    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur))
        .unwrap();
    assert_eq!(undo.undo().unwrap(), None);
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
    assert!(!undo.can_undo());
    assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"k": 5}));
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_merged_map_tombstones_overcount_and_undercount() {
    // Direction 1 (over-count): merged map tombstone where newer untracked
    // deletion blocks recreation -> 0-clock undo succeeds at u64::MAX.
    let doc = DocOptions::from_identity(1, "root".into()).auto_gc(false).build();
    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("k".into(), 1).unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    map.remove("k");
    doc.transact_mut(Origin::new("untracked"), |tx| {
        tx.map(&map)?.insert("k".into(), 2)?;
        Ok(())
    })
    .unwrap();
    doc.transact_mut(Origin::new("untracked"), |tx| {
        tx.map(&map)?.remove("k");
        Ok(())
    })
    .unwrap();
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur))
        .unwrap();
    assert_eq!(undo.undo().unwrap(), None);
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
    assert!(!undo.can_undo());
    doc.store.read().unwrap().self_check().unwrap();

    // Direction 2 (under-count): merged map tombstones where suffix is redone
    // -> undo2 needs 2 clocks (j + k) and must reject atomically with 1 left.
    let mut doc = DocOptions::from_identity(1, "root".into()).auto_gc(false).build();
    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("j".into(), 10).unwrap();
    map.insert("k".into(), 1).unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    doc.transact_mut(None, |tx| {
        let mut m = tx.map(&map)?;
        m.remove("j");
        m.remove("k");
        Ok(())
    })
    .unwrap();
    doc.transact_mut(Origin::new("untracked"), |tx| {
        tx.map(&map)?.insert("k".into(), 2)?;
        Ok(())
    })
    .unwrap();
    undo.stop_capturing().unwrap();
    map.remove("k");
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 2))
        .unwrap();

    assert!(undo.undo().unwrap().is_some());
    assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"k": 2}));
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX - 1);

    let before_wire = doc.encode_update_v1().unwrap();
    let before_sv = doc.get_state_vector();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert!(matches!(
        undo.undo(),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);
    assert_eq!(doc.get_state_vector(), before_sv);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"k": 2}));
    doc.store.read().unwrap().self_check().unwrap();

    doc.set_client(2);
    assert_eq!(undo.undo().unwrap(), Some(top));
    assert_eq!(
        serde_json::to_value(&map).unwrap(),
        serde_json::json!({"j": 10, "k": 1})
    );
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_merged_item_partial_redone_prefix_and_suffix() {
    // Prefix-only redone mapping on a merged deleted string "ab":
    // 1. When item slots are short by 1 for the redone-boundary split + copy,
    //    undo must fail atomically with wire and stack intact.
    // 2. When slots are restored, undo restores only the unmapped suffix "b"
    //    and reuses the mapped prefix without duplicating it.
    let mut doc = DocOptions::from_identity(1, "root".into()).auto_gc(false).build();
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "ab").unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
    text.remove(0, 2).unwrap();
    // Insert a separate live "a" at client 0 before syncing (so (0, 0) orders
    // before (1, 0..2)) and register (1, 0..1) -> (0, 0).
    let peer = Doc::with_client(0);
    peer.get_or_create_text("t").unwrap().insert(0, "a").unwrap();
    doc.apply_update_from_binary_v1(peer.encode_update_v1().unwrap())
        .unwrap();
    doc.store
        .write()
        .unwrap()
        .register_redone(Id::new(1, 0), 1, Id::new(0, 0));

    let before_wire = doc.encode_update_v1().unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    // Needs at least 2 slots (split at (1,1) + copy of (1,1..2)); leaving 1
    // must fail cleanly.
    leave_slots(&doc, 1);
    assert!(matches!(undo.undo(), Err(JwstCodecError::IncompleteDocument(_))));
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    doc.store.read().unwrap().self_check().unwrap();

    restore_slots(&doc);
    let state_before = doc.get_state_vector().get(&1);
    assert_eq!(undo.undo().unwrap(), Some(top));
    assert_eq!(doc.get_state_vector().get(&1) - state_before, 1);
    assert_eq!(text.to_string(), "ab");
    doc.store.read().unwrap().self_check().unwrap();

    // Suffix-only redone mapping on a merged deleted string "ab":
    // Must split at (1,1), recreate only "a", and never trigger
    // RedoMap::insert's "redo range registered twice" assertion.
    let mut doc = DocOptions::from_identity(1, "root".into()).auto_gc(false).build();
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "ab").unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
    text.remove(0, 2).unwrap();
    let mut peer = Doc::with_client(2);
    peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
        .unwrap();
    peer.get_or_create_text("t").unwrap().insert(0, "b").unwrap();
    doc.apply_update_from_binary_v1(peer.encode_update_v1().unwrap())
        .unwrap();
    doc.store
        .write()
        .unwrap()
        .register_redone(Id::new(1, 1), 1, Id::new(2, 0));

    let state_before = doc.get_state_vector().get(&1);
    assert!(undo.undo().unwrap().is_some());
    assert_eq!(doc.get_state_vector().get(&1) - state_before, 1);
    assert_eq!(text.to_string(), "ab");
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn multi_embed_insert_and_format_edge_cases_and_nested_preliminary() {
    // 1. Multi-value Embed([true, false]) at interior of "😀" with only 1 clock
    //    left must fail atomically before splitting "😀".
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "😀").unwrap();
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, 2), u64::MAX - 3))
        .unwrap();
    let before = (text.to_delta(), doc.encode_update_v1().unwrap(), doc.get_state_vector());
    let ops = [
        TextDeltaOp::Retain {
            retain: 1,
            format: None,
        },
        TextDeltaOp::Insert {
            insert: TextInsert::Embed(vec![Any::True, Any::False]),
            format: None,
        },
    ];
    assert!(matches!(
        text.apply_delta(&ops),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(text.to_string(), "😀");
    assert_eq!(
        (text.to_delta(), doc.encode_update_v1().unwrap(), doc.get_state_vector()),
        before
    );
    doc.store.read().unwrap().self_check().unwrap();

    // 2. Formatted multi-value Embed([true, false]) where fast-path upper bound
    //    overflows but exact clocks (2) fit exactly to u64::MAX -> succeeds.
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("t").unwrap();
    let bold = TextAttributes::from([("bold".into(), Any::True)]);
    text.apply_delta(&[delta("ab", Some(bold.clone()))]).unwrap();
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 2))
        .unwrap();
    let ops = [
        TextDeltaOp::Retain {
            retain: 1,
            format: None,
        },
        TextDeltaOp::Insert {
            insert: TextInsert::Embed(vec![Any::True, Any::False]),
            format: Some(bold.clone()),
        },
    ];
    text.apply_delta(&ops).unwrap();
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
    doc.store.read().unwrap().self_check().unwrap();

    // 3. Undo where upper bound overflows (2 deletions, 1 in insertions ->
    //    exact = 1) and local state is u64::MAX - 1 -> succeeds and reaches
    //    u64::MAX.
    let doc = Doc::with_client(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("a".into(), 1).unwrap();
    let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
    doc.transact_mut(None, |tx| {
        let mut m = tx.map(&map)?;
        m.remove("a");
        m.insert("b".into(), 10)?;
        m.insert("b".into(), 20)?;
        Ok(())
    })
    .unwrap();
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 1))
        .unwrap();
    assert!(undo.undo().unwrap().is_some());
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
    assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"a": 1}));
    doc.store.read().unwrap().self_check().unwrap();

    // 4. format_text end_split + conflicting format + multi-layer preliminary.
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "😀").unwrap();
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, 2), u64::MAX - 3))
        .unwrap();
    let before_wire = doc.encode_update_v1().unwrap();
    assert!(matches!(
        text.format(0, 1, bold.clone()),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(text.to_string(), "😀");
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);

    // Multi-layer preliminary (outer_array -> mid_map -> inner_text("ab"))
    // needs 1 (outer) + 1 (mid) + 1 (inner) + 2 ("ab") = 5 clocks; with 4 left
    // it must fail before splitting "😀".
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("t").unwrap();
    text.insert(0, "😀").unwrap();
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, 2), u64::MAX - 6))
        .unwrap();
    let before_wire = doc.encode_update_v1().unwrap();
    let mut outer = doc.create_array().unwrap();
    let mut mid = doc.create_map().unwrap();
    let mut inner = doc.create_text().unwrap();
    inner.insert(0, "ab").unwrap();
    mid.insert("inner".into(), inner).unwrap();
    outer.push(mid).unwrap();
    let ty = text.as_inner().idx().unwrap();
    assert!(matches!(
        doc.store.write().unwrap().edit_type(ty, |store, ty| {
            crate::doc::list_insert(store, ty, 1, Content::Type(outer.as_inner().idx().unwrap()))
        }),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(text.to_string(), "😀");
    assert_eq!(outer._id(), None);
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_to_redo_split_during_pop_restores_right_fragment_and_respects_clock_and_slots() {
    // Helper: creates a doc where client 0 has a deleted item (0, 0) in
    // `to_redo` whose `store.redone` target points into the middle of client
    // 1's merged deleted item "ab" at (1, 1) (also in `to_redo`).
    // During `undo()`, processing (0, 0) calls `clean_start(store, (1, 1))`,
    // splitting "ab" into "a" and "b" before client 1's span is visited.
    let setup = || {
        let mut doc = DocOptions::from_identity(1, "root".into()).auto_gc(false).build();
        let mut text = doc.get_or_create_text("t").unwrap();
        text.insert(0, "ab").unwrap();

        let peer = DocOptions::from_identity(0, "root".into()).auto_gc(false).build();
        peer.get_or_create_text("t").unwrap().insert(0, "z").unwrap();
        doc.apply_update_from_binary_v1(peer.encode_update_v1().unwrap())
            .unwrap();

        let undo = UndoManager::<u64>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
        // Delete both "z" (0, 0) and "ab" (1, 0..2) in one tracked transaction.
        text.remove(0, 3).unwrap();
        // Register (0, 0) -> (1, 1) so cleaning (0, 0)'s redone target splits
        // merged (1, 0..2) at (1, 1) mid-pop.
        doc.store
            .write()
            .unwrap()
            .register_redone(Id::new(0, 0), 1, Id::new(1, 1));
        (doc, text, undo)
    };

    // 1. With exactly 2 clocks left: both "a" and "b" are restored and state
    //    reaches u64::MAX.
    let (doc, text, undo) = setup();
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 2))
        .unwrap();
    assert!(undo.undo().unwrap().is_some());
    assert_eq!(text.to_string(), "ab");
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
    doc.store.read().unwrap().self_check().unwrap();

    // 2. With only 1 clock left: atomically rejected before mutating wire,
    //    history, or visible text.
    let (doc, text, undo) = setup();
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 1))
        .unwrap();
    let before_wire = doc.encode_update_v1().unwrap();
    let before_sv = doc.get_state_vector();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert!(matches!(
        undo.undo(),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(text.to_string(), "");
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);
    assert_eq!(doc.get_state_vector(), before_sv);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    doc.store.read().unwrap().self_check().unwrap();

    // 3. Tight item-slot pressure: splitting (1, 0..2) plus recreating both "a"
    //    and "b" needs at least 3 slots; leaving 2 must fail atomically and
    //    restoring slots succeeds.
    let (doc, text, undo) = setup();
    let before_wire = doc.encode_update_v1().unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    leave_slots(&doc, 2);
    assert!(matches!(undo.undo(), Err(JwstCodecError::IncompleteDocument(_))));
    assert_eq!(text.to_string(), "");
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    doc.store.read().unwrap().self_check().unwrap();

    restore_slots(&doc);
    assert_eq!(undo.undo().unwrap(), Some(top));
    assert_eq!(text.to_string(), "ab");
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_to_delete_split_during_pop_deletes_right_fragment() {
    let mut doc = DocOptions::from_identity(1, "root".into()).auto_gc(false).build();
    let text = doc.get_or_create_text("t").unwrap();
    let peer = DocOptions::from_identity(0, "root".into()).auto_gc(false).build();
    peer.get_or_create_text("t").unwrap().insert(0, "z").unwrap();
    doc.apply_update_from_binary_v1(peer.encode_update_v1().unwrap())
        .unwrap();

    let undo = UndoManager::<u64>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
    // Single tracked transaction deletes "z" (0, 0) and inserts merged "ab"
    // (1, 0..2).
    doc.transact_mut(None, |tx| {
        let mut t = tx.text(&text)?;
        t.remove(0, 1)?;
        t.insert(0, "ab")?;
        Ok(())
    })
    .unwrap();
    assert_eq!(text.to_string(), "ab");
    // Register (0, 0) -> (1, 1): during undo, `redo_item` on (0, 0) calls
    // `clean_start(store, (1, 1))`, splitting the live `to_delete` item "ab"
    // into "a" and "b" right before `to_delete` runs.
    doc.store
        .write()
        .unwrap()
        .register_redone(Id::new(0, 0), 1, Id::new(1, 1));

    assert!(undo.undo().unwrap().is_some());
    // Both "a" and "b" must be deleted; no right fragment may survive.
    assert_eq!(text.to_string(), "");
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_map_overwrite_kills_live_carrier_matches_exact_clocks() {
    for exhaust in [false, true] {
        let doc = Doc::with_client(1);
        let mut map = doc.get_or_create_map("map").unwrap();
        map.insert("k".into(), 1).unwrap();
        let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
        undo.advance_time(100);
        let mut arr = doc.create_array().unwrap();
        map.insert("k".into(), arr.clone()).unwrap();
        doc.transact_mut(Origin::new("untracked"), |tx| {
            tx.array(&arr)?.push(7)?;
            Ok(())
        })
        .unwrap();
        arr.remove(0, 1).unwrap();
        if exhaust {
            let cur = doc.get_state_vector().get(&1);
            doc.store
                .write()
                .unwrap()
                .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 1))
                .unwrap();
        }
        assert!(undo.undo().unwrap().is_some());
        assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"k": 1}));
        if exhaust {
            assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
        }
        doc.store.read().unwrap().self_check().unwrap();
    }
}

#[test]
fn undo_store_tail_right_blocks_later_same_key_item_in_recreated_parent() {
    // Old parent map `M` (client 1) was deleted and already has a `redone`
    // target `M'`. Inside `M`, client 1 deleted `k = "old"`. Inside `M'`,
    // client 2 wrote `k = "left"` then `k = "tail"` and deleted both in the
    // same window (`"tail"` is in `insertions` so without `store_tail_right`
    // `"left"` would appear skippable). During undo:
    //   1. Client 1's `"old"` recreates into `M'`, appending after `"tail"` and
    //      setting `store_tail_right[tail_idx]`.
    //   2. Client 2's `"left"` walks right to `"tail"`, sees the newly appended
    //      planned item at `tail_idx`, and is NOT recreated (0 clocks).
    // Total clocks = 1; must succeed with 1 clock left and pass
    // `debug_assert_eq!` with ample clocks.
    for exhaust in [false, true] {
        let mut doc = DocOptions::from_identity(1, "root".into()).auto_gc(false).build();
        let mut root = doc.get_or_create_map("root").unwrap();
        let mut m1 = doc.create_map().unwrap();
        root.insert("m1".into(), m1.clone()).unwrap();
        m1.insert("k".into(), "old").unwrap();
        let mut m2 = doc.create_map().unwrap();
        root.insert("m2".into(), m2.clone()).unwrap();
        let m1_id = m1.id().unwrap();
        let m2_id = m2.id().unwrap();

        doc.set_client(2);
        m2.insert("k".into(), "left").unwrap();
        let undo = UndoManager::<u64>::new(&doc, [(&root).into()], UndoOptions::default()).unwrap();
        undo.advance_time(100);
        // Tracked capture window:
        // - deletes m1 (and cascades to `"old"` at client 1)
        // - inserts `"tail"` on m2["k"] (deleting `"left"` at client 2)
        // - removes `"tail"` on m2["k"]
        doc.transact_mut(None, |tx| {
            tx.map(&root)?.remove("m1");
            let mut w2 = tx.map(&m2)?;
            w2.insert("k".into(), "tail")?;
            w2.remove("k");
            Ok(())
        })
        .unwrap();
        // Map m1 -> m2 so `"old"` recreates into m2 (after `"tail"`).
        doc.store.write().unwrap().register_redone(m1_id, 1, m2_id);

        if exhaust {
            let cur = doc.get_state_vector().get(&2);
            doc.store
                .write()
                .unwrap()
                .add_node(Node::new_gc(Id::new(2, cur), u64::MAX - cur - 1))
                .unwrap();
        }
        assert!(undo.undo().unwrap().is_some());
        assert_eq!(serde_json::to_value(&m2).unwrap(), serde_json::json!({"k": "old"}));
        if exhaust {
            assert_eq!(doc.get_state_vector().get(&2), u64::MAX);
        }
        doc.store.read().unwrap().self_check().unwrap();
    }
}

#[test]
fn undo_planned_redone_interior_offset_in_merged_map_tombstone() {
    // Astra R3-B1 (auto_gc(false)):
    // Same map key "k":
    //   - X (client 2, clock 0): old deleted value, right = Y
    //   - Y (client 2, clock 1): deleted value with store.redone[Y] = A+1
    //   - A (client 1, clock 0..2): merged length-2 deleted map tombstone tail
    //     on "k"
    // Both A (len 2) and X (len 1) are in `item.deletions` (total 3 clocks).
    // In client-id order, A is recreated first as P (len 2, new tail), then X
    // walks right -> Y -> store.redone[Y] = A+1 -> planned_redone[A+1] = P+1
    // (right == None), so X MUST also be recreated (3 clocks total).
    let setup = || {
        let doc = DocOptions::from_identity(2, "root".into()).auto_gc(false).build();
        let mut map = doc.get_or_create_map("map").unwrap();
        map.insert("k".into(), "X").unwrap();
        let undo = UndoManager::<u64>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
        undo.advance_time(100);
        // 1. Tracked delete of X (2, 0).
        doc.transact_mut(None, |tx| {
            tx.map(&map)?.remove("k");
            Ok(())
        })
        .unwrap();
        // 2. Untracked Y (2, 1) + untracked delete of Y.
        doc.transact_mut(Origin::new("untracked"), |tx| {
            let mut m = tx.map(&map)?;
            m.insert("k".into(), "Y")?;
            m.remove("k");
            Ok(())
        })
        .unwrap();
        // 3. Untracked A0 (1, 0) from peer 1, then tracked delete of A0.
        let mut peer = DocOptions::from_identity(1, "root".into()).auto_gc(false).build();
        peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
            .unwrap();
        peer.get_or_create_map("map").unwrap().insert("k".into(), "A0").unwrap();
        let u_a0 = Update::decode_v1(peer.encode_update_v1().unwrap()).unwrap();
        doc.apply_update_with_origin(u_a0, Origin::new("untracked")).unwrap();
        doc.transact_mut(None, |tx| {
            tx.map(&map)?.remove("k");
            Ok(())
        })
        .unwrap();
        // 4. Untracked A1 (1, 1) from peer 1, then tracked delete of A1. In
        //    doc, (1, 0) and (1, 1) are adjacent deleted map tombstones on "k"
        //    with auto_gc(false) -> merged into A = (1, 0..2) len 2!
        peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
            .unwrap();
        peer.get_or_create_map("map").unwrap().insert("k".into(), "A1").unwrap();
        let u_a1 = Update::decode_v1(peer.encode_update_v1().unwrap()).unwrap();
        doc.apply_update_with_origin(u_a1, Origin::new("untracked")).unwrap();
        doc.transact_mut(None, |tx| {
            tx.map(&map)?.remove("k");
            Ok(())
        })
        .unwrap();
        // Verify A = (1, 0..2) is merged to len 2 and register Y (2, 1) -> A+1
        // (1, 1).
        assert_eq!(doc.store.read().unwrap().get_node(Id::new(1, 0)).unwrap().len(), 2);
        doc.store
            .write()
            .unwrap()
            .register_redone(Id::new(2, 1), 1, Id::new(1, 1));
        (doc, map, undo)
    };

    // 1. With 3 clocks left: A (2) + X (1) = 3 clocks -> succeeds, restores
    //    "X", and state reaches u64::MAX.
    let (doc, map, undo) = setup();
    let cur = doc.get_state_vector().get(&2);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(2, cur), u64::MAX - cur - 3))
        .unwrap();
    assert!(undo.undo().unwrap().is_some());
    assert_eq!(serde_json::to_value(&map).unwrap(), serde_json::json!({"k": "X"}));
    assert_eq!(doc.get_state_vector().get(&2), u64::MAX);
    doc.store.read().unwrap().self_check().unwrap();

    // 2. With 2 clocks left: must reject atomically before recreating A; wire,
    //    state vector, visible map, and stack top stay unchanged.
    let (doc, map, undo) = setup();
    let cur = doc.get_state_vector().get(&2);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(2, cur), u64::MAX - cur - 2))
        .unwrap();
    let before_wire = doc.encode_update_v1().unwrap();
    let before_sv = doc.get_state_vector();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert!(matches!(
        undo.undo(),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);
    assert_eq!(doc.get_state_vector(), before_sv);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    assert!(!map.contains_key("k"));
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_self_split_stale_redone_len_public_api_and_clock_bounds() {
    // Fable R3-B4: pure public API reproduction (default config, single
    // client). Array holds nested Text "hi" -> prepend "xy" -> remove "hi" ->
    // undo1 (merges into "xyhi" with old "hi" redone pointing into the suffix
    // of "xyhi") -> remove Text from Array -> undo2 (right-neighbor trace
    // splits "xyhi" mid-`redo_item` into "xy" + "hi").
    let setup = || {
        let doc = Doc::with_client(1);
        let mut arr = doc.get_or_create_array("a").unwrap();
        let mut nested = doc.create_text().unwrap();
        nested.insert(0, "hi").unwrap();
        arr.push(nested.clone()).unwrap();
        nested.insert(0, "xy").unwrap();
        let undo = UndoManager::<u64>::new(&doc, [(&arr).into()], UndoOptions::default()).unwrap();
        nested.remove(2, 2).unwrap();
        assert!(undo.undo().unwrap().is_some());
        assert_eq!(nested.to_string(), "xyhi");
        arr.remove(0, 1).unwrap();
        (doc, arr, undo)
    };

    // 1. Default config (ample clocks): undo2 succeeds and restores "xyhi".
    let (doc, arr, undo) = setup();
    let before = doc.get_state_vector().get(&1);
    assert!(undo.undo().unwrap().is_some());
    let delta = doc.get_state_vector().get(&1) - before;
    assert_eq!(delta, 5); // 1 carrier + 2 ("xy") + 2 ("hi")
    let Some(Value::Text(restored)) = arr.get(0) else {
        panic!("expected restored text")
    };
    assert_eq!(restored.to_string(), "xyhi");
    doc.store.read().unwrap().self_check().unwrap();

    // 2. Exact remaining clocks (5 left): succeeds and reaches u64::MAX.
    let (doc, arr, undo) = setup();
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 5))
        .unwrap();
    assert!(undo.undo().unwrap().is_some());
    assert_eq!(doc.get_state_vector().get(&1), u64::MAX);
    let Some(Value::Text(restored)) = arr.get(0) else {
        panic!("expected restored text")
    };
    assert_eq!(restored.to_string(), "xyhi");
    doc.store.read().unwrap().self_check().unwrap();

    // 3. One clock short (4 left): atomically rejected; wire, SV, array, and
    //    stack top remain unchanged.
    let (doc, arr, undo) = setup();
    let cur = doc.get_state_vector().get(&1);
    doc.store
        .write()
        .unwrap()
        .add_node(Node::new_gc(Id::new(1, cur), u64::MAX - cur - 4))
        .unwrap();
    let before_wire = doc.encode_update_v1().unwrap();
    let before_sv = doc.get_state_vector();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert!(matches!(
        undo.undo(),
        Err(JwstCodecError::IncompleteDocument(s)) if s == "struct clock overflow"
    ));
    assert_eq!(doc.encode_update_v1().unwrap(), before_wire);
    assert_eq!(doc.get_state_vector(), before_sv);
    assert_eq!(undo.peek(UndoStack::Undo).as_ref(), Some(&top));
    assert!(arr.is_empty());
    doc.store.read().unwrap().self_check().unwrap();
}

#[derive(Clone)]
enum DiffContainer {
    Map(Map),
    Array(Array),
    Text(Text),
}

fn diff_pick(rng: &mut rand_chacha::ChaCha20Rng, roots: &[DiffContainer]) -> DiffContainer {
    use rand::RngExt;
    const KEYS: [&str; 3] = ["k0", "k1", "k2"];
    let mut cur = roots[rng.random_range(0..roots.len())].clone();
    for _ in 0..3 {
        if rng.random_bool(0.35) {
            break;
        }
        let next = match &cur {
            DiffContainer::Map(m) => m.get(KEYS[rng.random_range(0..KEYS.len())]),
            DiffContainer::Array(a) => {
                let len = a.len();
                if len == 0 {
                    None
                } else {
                    a.get(rng.random_range(0..len))
                }
            }
            DiffContainer::Text(_) => None,
        };
        match next {
            Some(Value::Map(m)) => cur = DiffContainer::Map(m),
            Some(Value::Array(a)) => cur = DiffContainer::Array(a),
            Some(Value::Text(t)) => cur = DiffContainer::Text(t),
            _ => break,
        }
    }
    cur
}

fn diff_new_child(rng: &mut rand_chacha::ChaCha20Rng, doc: &Doc) -> Value {
    use rand::RngExt;
    match rng.random_range(0u8..3) {
        0 => {
            let mut t = doc.create_text().unwrap();
            let _ = t.insert(0, "hi");
            Value::Text(t)
        }
        1 => {
            let mut m = doc.create_map().unwrap();
            let _ = m.insert("k0".into(), 7);
            if rng.random_bool(0.5) {
                let mut t = doc.create_text().unwrap();
                let _ = t.insert(0, "in");
                let _ = m.insert("k1".into(), t);
            }
            Value::Map(m)
        }
        _ => {
            let mut a = doc.create_array().unwrap();
            let _ = a.push(1);
            let _ = a.push(2);
            Value::Array(a)
        }
    }
}

fn diff_apply_op(
    rng: &mut rand_chacha::ChaCha20Rng,
    doc: &Doc,
    target: &DiffContainer,
    origin: Option<Origin>,
    step: usize,
) {
    use rand::RngExt;
    const KEYS: [&str; 3] = ["k0", "k1", "k2"];
    let mut child = rng.random_bool(0.3).then(|| diff_new_child(rng, doc));
    let n_ops = rng.random_range(1..=2);
    let _ = doc.transact_mut(origin, |tx| {
        for _ in 0..n_ops {
            match target {
                DiffContainer::Map(m) => {
                    let mut w = tx.map(m)?;
                    let key = KEYS[rng.random_range(0..KEYS.len())];
                    match rng.random_range(0u8..5) {
                        0 | 1 => {
                            let _ = w.insert(key.into(), step as i64);
                        }
                        2 | 3 => w.remove(key),
                        _ => {
                            if let Some(c) = child.take() {
                                let _ = w.insert(key.into(), c);
                            }
                        }
                    }
                }
                DiffContainer::Array(a) => {
                    let mut w = tx.array(a)?;
                    let len = w.len();
                    match rng.random_range(0u8..5) {
                        0 | 1 => {
                            let idx = rng.random_range(0..=len);
                            let _ = w.insert(idx, step as i64);
                        }
                        2 | 3 => {
                            if len > 0 {
                                let idx = rng.random_range(0..len);
                                let l = rng.random_range(1..=(len - idx).min(2));
                                let _ = w.remove(idx, l);
                            }
                        }
                        _ => {
                            if let Some(c) = child.take() {
                                let idx = rng.random_range(0..=len);
                                let _ = w.insert(idx, c);
                            }
                        }
                    }
                }
                DiffContainer::Text(t) => {
                    let mut w = tx.text(t)?;
                    let len = w.len();
                    match rng.random_range(0u8..6) {
                        0 | 1 => {
                            let idx = rng.random_range(0..=len);
                            let _ = w.insert(idx, if rng.random_bool(0.2) { "😀" } else { "ab" });
                        }
                        2 | 3 => {
                            if len > 0 {
                                let idx = rng.random_range(0..len);
                                let l = rng.random_range(1..=(len - idx).min(3));
                                let _ = w.remove(idx, l);
                            }
                        }
                        4 => {
                            if len > 0 {
                                let idx = rng.random_range(0..len);
                                let l = rng.random_range(1..=(len - idx).min(3));
                                let value = if rng.random_bool(0.5) { Any::True } else { Any::Null };
                                let _ = w.format(idx, l, TextAttributes::from([("bold".into(), value)]));
                            }
                        }
                        _ => {
                            let idx = rng.random_range(0..=len);
                            let _ = w.insert_embed(idx, Any::True);
                        }
                    }
                }
            }
        }
        Ok(())
    });
}

fn run_diff_round(round: u64, steps: usize, small_key_no_gc: bool) {
    use rand::{RngExt, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    let mut rng = ChaCha20Rng::seed_from_u64(0x5EED_0000 + round);
    let auto_gc = !small_key_no_gc && round.is_multiple_of(2);
    let mut doc = DocOptions::from_identity(1, "root".into()).auto_gc(auto_gc).build();
    let mut peer = DocOptions::from_identity(2, "root".into()).auto_gc(auto_gc).build();

    let doc_roots = if small_key_no_gc {
        vec![DiffContainer::Map(doc.get_or_create_map("m").unwrap())]
    } else {
        vec![
            DiffContainer::Map(doc.get_or_create_map("m").unwrap()),
            DiffContainer::Array(doc.get_or_create_array("a").unwrap()),
            DiffContainer::Text(doc.get_or_create_text("t").unwrap()),
            DiffContainer::Map(doc.get_or_create_map("x").unwrap()),
        ]
    };
    let peer_roots = if small_key_no_gc {
        vec![DiffContainer::Map(peer.get_or_create_map("m").unwrap())]
    } else {
        vec![
            DiffContainer::Map(peer.get_or_create_map("m").unwrap()),
            DiffContainer::Array(peer.get_or_create_array("a").unwrap()),
            DiffContainer::Text(peer.get_or_create_text("t").unwrap()),
            DiffContainer::Map(peer.get_or_create_map("x").unwrap()),
        ]
    };

    let undo = if small_key_no_gc || round.is_multiple_of(3) {
        UndoManager::<u64>::new(&doc, [(&doc).into()], UndoOptions::default()).unwrap()
    } else {
        let (DiffContainer::Map(m), DiffContainer::Array(a), DiffContainer::Text(t)) =
            (&doc_roots[0], &doc_roots[1], &doc_roots[2])
        else {
            unreachable!()
        };
        UndoManager::<u64>::new(&doc, [m.into(), a.into(), t.into()], UndoOptions::default()).unwrap()
    };
    let untracked = Origin::new("untracked");
    let remote_tracked = Origin::new("remote-tracked");
    undo.add_tracked_origin(Some(remote_tracked.clone())).unwrap();
    undo.advance_time(100);

    for step in 0..steps {
        match rng.random_range(0u8..20) {
            0..=6 => {
                let target = diff_pick(&mut rng, &doc_roots);
                diff_apply_op(&mut rng, &doc, &target, None, step);
            }
            7..=8 => {
                let target = diff_pick(&mut rng, &doc_roots);
                diff_apply_op(&mut rng, &doc, &target, Some(untracked.clone()), step);
            }
            9..=10 => {
                let _ = peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap());
                let target = diff_pick(&mut rng, &peer_roots);
                diff_apply_op(&mut rng, &peer, &target, None, step);
                let bytes = peer.encode_update_v1().unwrap();
                if rng.random_bool(0.25) {
                    let _ = doc.apply_update_with_origin(Update::decode_v1(bytes).unwrap(), remote_tracked.clone());
                } else {
                    let _ = doc.apply_update_from_binary_v1(bytes);
                }
            }
            11 => undo.stop_capturing().unwrap(),
            12 => undo.advance_time(100 + (step as u64) * rng.random_range(0..400u64)),
            13 => {
                let client = [1u64, 3, 5, 9][rng.random_range(0..4usize)];
                doc.set_client(client);
            }
            14..=17 => {
                let _ = undo.undo().unwrap();
            }
            _ => {
                let _ = undo.redo().unwrap();
            }
        }
    }
    while undo.can_undo() {
        let _ = undo.undo().unwrap();
    }
    while undo.can_redo() {
        let _ = undo.redo().unwrap();
    }
    doc.store.read().unwrap().self_check().unwrap();
}

#[test]
fn undo_exact_pop_clocks_differential_property() {
    let rounds: u64 = if cfg!(miri) { 4 } else { 1500 };
    let steps: usize = if cfg!(miri) { 16 } else { 80 };

    for round in 0..rounds {
        run_diff_round(round, steps, false);
    }

    // High-frequency small-key + untracked + stop_capturing + auto_gc(false)
    // bias targeting merged map tombstone chains and interior planned_redone.
    let small_key_rounds: u64 = if cfg!(miri) { 2 } else { 300 };
    for round in 0..small_key_rounds {
        run_diff_round(100_000 + round, steps, true);
    }

    // Explicitly replay historical seeds that caught R2/R3 divergences
    // (including 12223 which triggered self-split stale redone length).
    if !cfg!(miri) {
        for seed in [4433u64, 7658, 12223, 22173] {
            run_diff_round(seed, 80, false);
        }
        run_diff_round(3819, 250, false);
    }
}
