use super::*;

fn doc(client: Client) -> Doc {
    DocOptions::new().with_client_id(client).build()
}

/// Sends what `to` misses from `from`, as a remote transaction.
fn sync(from: &Doc, to: &Doc) {
    let update = from.encode_state_as_update(&to.get_state_vector()).unwrap();
    to.apply_update_with_origin(update, Origin::new("remote")).unwrap();
}

fn sync_both(a: &Doc, b: &Doc) {
    sync(a, b);
    sync(b, a);
}

fn manager(doc: &Doc, scope: impl Into<UndoScope>) -> UndoManager {
    UndoManager::new(doc, [scope.into()], UndoOptions::default()).unwrap()
}

fn content(doc: &Doc, id: (Client, Clock)) -> Option<Content> {
    let store = doc.store.read().unwrap();
    match store.get_node(id)? {
        Node::Item(item) => Some(item.get().unwrap().content.clone()),
        _ => None,
    }
}

fn format(attrs: &[(&str, Any)]) -> Option<TextAttributes> {
    Some(attrs.iter().map(|(k, v)| (k.to_string(), v.clone())).collect())
}

#[test]
fn undo_and_redo_text() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = manager(&doc, &text);

    text.insert(0, "abc").unwrap();
    undo.stop_capturing().unwrap();
    text.remove(1, 1).unwrap();
    assert_eq!(text.to_string(), "ac");

    assert!(undo.undo().unwrap().is_some());
    assert_eq!(text.to_string(), "abc");
    assert!(undo.undo().unwrap().is_some());
    assert_eq!(text.to_string(), "");
    assert!(undo.undo().unwrap().is_none());

    assert!(undo.redo().unwrap().is_some());
    assert_eq!(text.to_string(), "abc");
    assert!(undo.redo().unwrap().is_some());
    assert_eq!(text.to_string(), "ac");
    assert!(undo.redo().unwrap().is_none());
    assert!(undo.can_undo() && !undo.can_redo());
}

#[test]
fn undo_keeps_remote_insertions_and_deleted_flags() {
    let (a, b) = (doc(1), doc(2));
    let mut text_a = a.get_or_create_text("text").unwrap();
    let mut text_b = b.get_or_create_text("text").unwrap();
    let undo = manager(&a, &text_a);

    text_a.insert(0, "abcd").unwrap();
    sync(&a, &b);
    text_b.insert(2, "XY").unwrap();
    sync(&b, &a);
    assert_eq!(text_a.to_string(), "abXYcd");

    // only a's characters go, b's insertion in their middle stays
    undo.undo().unwrap();
    assert_eq!(text_a.to_string(), "XY");
    // redo recreates them under new ids next to b's characters
    undo.redo().unwrap();
    assert_eq!(text_a.to_string(), "abXYcd");
    let deleted = a.get_delete_sets();
    assert!(deleted.get(&1).unwrap().contains(0), "the original ids stay deleted");
    assert!(!deleted.get(&1).unwrap().contains(4), "the recreation is visible");

    sync_both(&a, &b);
    assert_eq!(text_b.to_string(), "abXYcd");
    // undo follows the recreated ids
    undo.undo().unwrap();
    sync_both(&a, &b);
    assert_eq!(text_b.to_string(), "XY");
}

#[test]
fn undo_of_a_deletion_recreates_it_after_remote_edits() {
    let (a, b) = (doc(1), doc(2));
    let mut text_a = a.get_or_create_text("text").unwrap();
    let mut text_b = b.get_or_create_text("text").unwrap();
    text_a.insert(0, "hello world").unwrap();
    sync(&a, &b);

    let undo = manager(&a, &text_a);
    text_a.remove(0, 6).unwrap();
    sync(&a, &b);
    text_b.insert(5, "!").unwrap();
    sync(&b, &a);
    assert_eq!(text_a.to_string(), "world!");

    undo.undo().unwrap();
    assert_eq!(text_a.to_string(), "hello world!");
    sync(&a, &b);
    assert_eq!(text_b.to_string(), "hello world!");
}

#[test]
fn same_window_insertions_are_not_recreated() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "ab").unwrap();
    let undo = manager(&doc, &text);
    doc.transact_mut(None, |tx| {
        let mut text = tx.text(&text)?;
        text.insert(1, "xyz")?;
        text.remove(2, 1)?;
        text.remove(0, 1)
    })
    .unwrap();
    assert_eq!(text.to_string(), "xzb");
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "ab");
}

#[test]
fn map_values_are_restored_unless_overwritten_remotely() {
    let (a, b) = (doc(1), doc(2));
    let mut map_a = a.get_or_create_map("map").unwrap();
    let mut map_b = b.get_or_create_map("map").unwrap();
    map_a.insert("k".into(), 1).unwrap();
    let undo = manager(&a, &map_a);
    map_a.insert("k".into(), 2).unwrap();
    undo.undo().unwrap();
    assert_eq!(map_a.get("k"), Some(Value::from(1)));
    undo.redo().unwrap();
    assert_eq!(map_a.get("k"), Some(Value::from(2)));

    // a remote value set after ours is not overwritten (Yjs
    // `ignoreRemoteMapChanges = false`)
    undo.stop_capturing().unwrap();
    map_a.insert("k".into(), 3).unwrap();
    sync(&a, &b);
    map_b.insert("k".into(), 4).unwrap();
    sync(&b, &a);
    // nothing left that does not overwrite the remote value
    assert!(undo.undo().unwrap().is_none());
    assert_eq!(map_a.get("k"), Some(Value::from(4)));
}

#[test]
fn undo_of_a_map_deletion() {
    let doc = doc(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("k".into(), "v").unwrap();
    let undo = manager(&doc, &map);
    map.remove("k");
    assert_eq!(map.get("k"), None);
    undo.undo().unwrap();
    assert_eq!(map.get("k"), Some(Value::from("v")));
}

#[test]
fn nested_types_are_recreated_with_new_identities() {
    let (a, b) = (doc(1), doc(2));
    let mut blocks = a.get_or_create_map("blocks").unwrap();
    blocks
        .insert("p".into(), Value::Text(a.create_text().unwrap()))
        .unwrap();
    let Some(Value::Text(mut text)) = blocks.get("p") else {
        unreachable!()
    };
    text.apply_delta(&[TextDeltaOp::Insert {
        insert: TextInsert::Text("bold".into()),
        format: format(&[("bold", Any::True)]),
    }])
    .unwrap();
    let old = text.identity().unwrap();

    let undo = manager(&a, &blocks);
    blocks.remove("p");
    assert_eq!(blocks.get("p"), None);
    sync(&a, &b);

    undo.undo().unwrap();
    let Some(Value::Text(restored)) = blocks.get("p") else {
        panic!("not restored")
    };
    assert_ne!(restored.identity().unwrap(), old, "a new type, not the old one revived");
    assert_eq!(restored.to_delta(), text_delta_of("bold", &[("bold", Any::True)]));
    // the old handle still points to the deleted type
    assert_eq!(text.to_string(), "");

    sync(&a, &b);
    let Some(Value::Text(remote)) = b.get_or_create_map("blocks").unwrap().get("p") else {
        panic!("not restored remotely")
    };
    assert_eq!(remote.to_delta(), restored.to_delta());
}

fn text_delta_of(text: &str, attrs: &[(&str, Any)]) -> TextDelta {
    vec![TextDeltaOp::Insert {
        insert: TextInsert::Text(text.into()),
        format: format(attrs),
    }]
}

#[test]
fn undo_of_formatting_keeps_remote_formatting() {
    let (a, b) = (doc(1), doc(2));
    let mut text_a = a.get_or_create_text("text").unwrap();
    let mut text_b = b.get_or_create_text("text").unwrap();
    text_a.insert(0, "abc").unwrap();
    sync(&a, &b);

    let undo = manager(&a, &text_a);
    text_a
        .apply_delta(&[TextDeltaOp::Retain {
            retain: 3,
            format: format(&[("bold", Any::True)]),
        }])
        .unwrap();
    text_b
        .apply_delta(&[TextDeltaOp::Retain {
            retain: 3,
            format: format(&[("italic", Any::True)]),
        }])
        .unwrap();
    sync_both(&a, &b);
    assert_eq!(
        text_a.to_delta(),
        text_delta_of("abc", &[("bold", Any::True), ("italic", Any::True)])
    );

    undo.undo().unwrap();
    assert_eq!(text_a.to_delta(), text_delta_of("abc", &[("italic", Any::True)]));
    undo.redo().unwrap();
    assert_eq!(
        text_a.to_delta(),
        text_delta_of("abc", &[("bold", Any::True), ("italic", Any::True)])
    );
}

#[test]
fn capture_window_and_stop_capturing() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = UndoManager::<()>::new(
        &doc,
        [(&text).into()],
        UndoOptions {
            capture_timeout: 100,
            ..Default::default()
        },
    )
    .unwrap();

    undo.advance_time(1);
    text.insert(0, "a").unwrap();
    undo.advance_time(50);
    text.insert(1, "b").unwrap(); // joins
    undo.advance_time(200);
    text.insert(2, "c").unwrap(); // too late
    undo.advance_time(150); // older than reported before: ignored
    undo.advance_time(210);
    undo.stop_capturing().unwrap();
    text.insert(3, "d").unwrap(); // stopped

    undo.undo().unwrap();
    assert_eq!(text.to_string(), "abc");
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "ab");
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "");

    // before the host reports a time every commit is an item of its own
    let doc = Doc::with_client(2);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = manager(&doc, &text);
    text.insert(0, "a").unwrap();
    text.insert(1, "b").unwrap();
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "a");
}

#[test]
fn local_edits_clear_redo_and_remote_edits_do_not() {
    let (a, b) = (doc(1), doc(2));
    let mut text_a = a.get_or_create_text("text").unwrap();
    let mut text_b = b.get_or_create_text("text").unwrap();
    let undo = manager(&a, &text_a);

    text_a.insert(0, "a").unwrap();
    undo.undo().unwrap();
    assert!(undo.can_redo());
    sync(&a, &b);
    text_b.insert(0, "remote").unwrap();
    sync(&b, &a);
    assert!(undo.can_redo(), "remote edits keep the redo stack");
    text_a.insert(0, "x").unwrap();
    assert!(!undo.can_redo(), "local edits clear it");
}

#[test]
fn scope_and_origins() {
    let doc = doc(1);
    let text = doc.get_or_create_text("text").unwrap();
    let mut other = doc.get_or_create_text("other").unwrap();
    let undo = manager(&doc, &text);

    other.insert(0, "out of scope").unwrap();
    assert!(!undo.can_undo());

    #[derive(Clone, PartialEq, Eq, Hash)]
    struct Editor(u32);
    doc.transact_mut(Origin::new(Editor(1)), |tx| tx.text(&text)?.insert(0, "untracked"))
        .unwrap();
    assert!(!undo.can_undo());

    // origins are tracked by identity: the instance and its clones
    let editor = Origin::new(Editor(1));
    undo.add_tracked_origin(Some(editor.clone())).unwrap();
    doc.transact_mut(Origin::new(Editor(1)), |tx| tx.text(&text)?.insert(0, "equal"))
        .unwrap();
    assert!(!undo.can_undo());
    doc.transact_mut(editor.clone(), |tx| tx.text(&text)?.insert(0, "a"))
        .unwrap();
    assert!(undo.can_undo());
    doc.transact_mut(Origin::new(Editor(2)), |tx| tx.text(&text)?.insert(0, "b"))
        .unwrap();
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "bequaluntracked");

    undo.track_origin_type::<Editor>().unwrap();
    doc.transact_mut(Origin::new(Editor(3)), |tx| tx.text(&text)?.insert(0, "c"))
        .unwrap();
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "bequaluntracked");

    undo.remove_tracked_origin(&Some(editor.clone())).unwrap();
    undo.clear(true, true).unwrap();
    // still tracked through its type
    doc.transact_mut(editor, |tx| tx.text(&text)?.insert(0, "d")).unwrap();
    assert!(undo.can_undo());

    undo.add_to_scope((&other).into()).unwrap();
    other.insert(0, "now ").unwrap();
    undo.undo().unwrap();
    assert_eq!(other.to_string(), "out of scope");

    // remote updates without origin are not captured
    let peer = Doc::with_client(2);
    let mut peer_text = peer.get_or_create_text("text").unwrap();
    peer_text.insert(0, "p").unwrap();
    let update = peer.encode_update().unwrap();
    let mut doc = doc;
    undo.clear(true, true).unwrap();
    doc.apply_update(update).unwrap();
    assert!(!undo.can_undo());
}

#[test]
fn document_scope() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let mut map = doc.get_or_create_map("map").unwrap();
    let undo = manager(&doc, &doc);
    doc.transact_mut(None, |tx| {
        tx.text(&text)?.insert(0, "a")?;
        tx.map(&map)?.insert("k".into(), 1)
    })
    .unwrap();
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "");
    assert_eq!(map.get("k"), None);
    text.insert(0, "b").unwrap();
    map.remove("k");
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "");
}

#[test]
fn deleted_content_is_retained_until_released() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "abc").unwrap();
    let undo = manager(&doc, &text);
    text.remove(0, 3).unwrap();
    assert_eq!(content(&doc, (1, 0)), Some(Content::String("abc".into())));

    undo.clear(true, true).unwrap();
    assert_eq!(content(&doc, (1, 0)), Some(Content::Deleted(3)));
    assert!(doc.store.read().unwrap().retained.is_empty());
}

#[test]
fn popped_items_release_what_nothing_needs() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "abc").unwrap();
    let undo = manager(&doc, &text);
    text.remove(0, 3).unwrap();
    undo.undo().unwrap();
    // "abc" is recreated as (1, 3); the popped item released the original
    assert_eq!(text.to_string(), "abc");
    assert_eq!(content(&doc, (1, 0)), Some(Content::Deleted(3)));
    undo.redo().unwrap();
    assert_eq!(text.to_string(), "");
    assert_eq!(content(&doc, (1, 3)), Some(Content::String("abc".into())));
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "abc");
    assert_eq!(content(&doc, (1, 3)), Some(Content::Deleted(3)));
}

#[test]
fn retained_nested_content_survives_remote_parent_deletion() {
    let (a, b) = (doc(1), doc(2));
    let mut blocks = a.get_or_create_map("blocks").unwrap();
    blocks
        .insert("p".into(), Value::Text(a.create_text().unwrap()))
        .unwrap();
    let Some(Value::Text(mut text)) = blocks.get("p") else {
        unreachable!()
    };
    text.insert(0, "hello").unwrap();
    sync(&a, &b);

    let undo = manager(&a, &blocks);
    text.remove(0, 5).unwrap();
    sync(&a, &b);
    // a remote peer deletes the block: GC would take the text with it
    b.get_or_create_map("blocks").unwrap().remove("p");
    sync(&b, &a);
    assert_eq!(content(&a, (1, 1)), Some(Content::String("hello".into())));

    // the parent was deleted remotely and is not recreated by this undo
    assert!(undo.undo().unwrap().is_none());
}

#[test]
fn dropping_the_manager_releases_retention() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "abc").unwrap();
    let undo = manager(&doc, &text);
    assert_eq!(
        UndoManager::<()>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap_err(),
        JwstCodecError::UndoManagerExists
    );
    text.remove(0, 3).unwrap();
    drop(undo);
    assert_eq!(content(&doc, (1, 0)), Some(Content::Deleted(3)));
    // a new manager can be created
    manager(&doc, &text);
}

#[test]
fn metadata() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = UndoManager::<Option<u64>>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
    text.insert(0, "a").unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert_eq!(top.meta, None);
    assert!(undo.set_meta(UndoStack::Undo, top.id, Some(7)).unwrap());
    assert!(!undo.set_meta(UndoStack::Redo, top.id, Some(8)).unwrap());
    assert_eq!(undo.peek(UndoStack::Undo).unwrap().meta, Some(Arc::new(Some(7))));

    let undone = undo.undo().unwrap().unwrap();
    assert_eq!(
        undone,
        UndoItem {
            id: top.id,
            meta: Some(Arc::new(Some(7)))
        }
    );
    // the undo's own changes are a new redo item
    assert_eq!(undo.peek(UndoStack::Redo).unwrap().meta, None);
}

/// The way an editor keeps its selection with a history entry: the relative
/// positions of the selection before the change go into the item's metadata.
/// Remote edits (also inside the selected range) neither add an item nor
/// touch the metadata, and after the undo the positions resolve to the
/// restored content, remote insertions included.
#[test]
fn selection_in_metadata_survives_remote_edits_and_resolves_after_undo() {
    type Selection = (RelativePosition, RelativePosition);
    let (a, b) = (doc(1), doc(2));
    let mut text_a = a.get_or_create_text("text").unwrap();
    let mut text_b = b.get_or_create_text("text").unwrap();
    text_a.insert(0, "hello wörld😀").unwrap();
    sync(&a, &b);
    let undo = UndoManager::<Selection>::new(&a, [(&text_a).into()], UndoOptions::default()).unwrap();
    let index = |rpos: &RelativePosition| {
        let position = a.resolve_relative_position(rpos, true).unwrap();
        assert_eq!(position.r#type, TypeIdentity::Root("text".into()));
        position.index
    };

    // select "wörld😀" (UTF-16 6..13) and delete it
    let selection = (
        text_a.relative_position(6, 0).unwrap(),
        text_a.relative_position(13, -1).unwrap(),
    );
    text_a.remove(6, 7).unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert!(undo.set_meta(UndoStack::Undo, top.id, selection.clone()).unwrap());

    // concurrently, the remote author edits before and inside the selection
    text_b.insert(0, "dear ").unwrap();
    text_b.insert(13, "XX").unwrap();
    sync_both(&a, &b);
    assert_eq!(text_a.to_string(), "dear hello XX");
    let peeked = undo.peek(UndoStack::Undo).unwrap();
    assert_eq!(peeked.id, top.id, "remote edits add no history item");
    assert_eq!(peeked.meta.as_deref(), Some(&selection));
    assert!(undo.peek(UndoStack::Redo).is_none());

    // the metadata comes back with the undo; the selection covers the
    // recreated text and the remote insertion that landed inside it
    let undone = undo.undo().unwrap().unwrap();
    assert_eq!(undone.meta.as_deref(), Some(&selection));
    assert_eq!(text_a.to_string(), "dear hello wöXXrld😀");
    assert_eq!((index(&selection.0), index(&selection.1)), (11, 20));
    // the same bytes, as stored by an editor, resolve the same way
    let decoded = RelativePosition::decode(selection.0.encode().unwrap()).unwrap();
    assert_eq!(index(&decoded), 11);
    // without following redone content, the anchors stay on the deleted
    // originals: only the end resolves to the same place
    let unfollowed = |rpos: &RelativePosition| a.resolve_relative_position(rpos, false).unwrap().index;
    assert_eq!((unfollowed(&selection.0), unfollowed(&selection.1)), (13, 20));

    // after the redo deletes it again, each anchor sits where its deleted
    // character was: the start before the remote "XX", the end after it
    undo.redo().unwrap();
    assert_eq!(text_a.to_string(), "dear hello XX");
    assert_eq!((index(&selection.0), index(&selection.1)), (11, 13));
    sync(&a, &b);
    assert_eq!(text_b.to_string(), "dear hello XX");
}

#[test]
fn undo_and_redo_commits_carry_their_origin() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = manager(&doc, &text);
    let seen = Arc::new(std::sync::Mutex::new(Vec::new()));
    let sink = seen.clone();
    let _subscription = doc.subscribe(move |event| {
        sink.lock().unwrap().push(
            event
                .origin
                .as_ref()
                .and_then(|origin| origin.downcast_ref::<UndoOrigin>())
                .map(|origin| origin.stack()),
        )
    });
    text.insert(0, "a").unwrap();
    undo.undo().unwrap();
    undo.redo().unwrap();
    assert_eq!(
        *seen.lock().unwrap(),
        [None, Some(UndoStack::Undo), Some(UndoStack::Redo)]
    );
}

#[test]
fn undo_in_arrays_keeps_positions() {
    let (a, b) = (doc(1), doc(2));
    let mut array_a = a.get_or_create_array("array").unwrap();
    let mut array_b = b.get_or_create_array("array").unwrap();
    array_a.push(1).unwrap();
    array_a.push(2).unwrap();
    array_a.push(3).unwrap();
    sync(&a, &b);
    let undo = manager(&a, &array_a);
    array_a.remove(1, 1).unwrap();
    sync(&a, &b);
    array_b.insert(1, 9).unwrap();
    sync(&b, &a);
    undo.undo().unwrap();
    let values = array_a.iter().map(|value| value.to_any().unwrap()).collect::<Vec<_>>();
    // the recreated 2 goes after the remote 9, which took its place (as Yjs)
    assert_eq!(values, [Any::from(1), Any::from(9), Any::from(2), Any::from(3)]);
}

/// Caller code (origin `PartialEq`/`Drop`, metadata `Clone`/`Drop`, the
/// time source) never runs under the document lock: here it uses the
/// document, which would fail with `Reentrant` there.
#[test]
fn caller_code_never_runs_under_the_document_lock() {
    #[derive(Clone)]
    struct Probe(Doc);
    impl Probe {
        fn touch(&self) {
            assert!(self.0.get_or_create_text("text").is_ok(), "called under the lock");
        }
    }
    impl PartialEq for Probe {
        fn eq(&self, _: &Self) -> bool {
            self.touch();
            true
        }
    }
    impl Eq for Probe {}
    impl std::hash::Hash for Probe {
        fn hash<H: std::hash::Hasher>(&self, _: &mut H) {
            self.touch();
        }
    }
    impl Drop for Probe {
        fn drop(&mut self) {
            if !std::thread::panicking() {
                self.touch();
            }
        }
    }
    struct Meta(Probe);
    impl Clone for Meta {
        fn clone(&self) -> Self {
            self.0.touch();
            Meta(self.0.clone())
        }
    }

    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let editor = Origin::new(Probe(doc.clone()));
    let undo = UndoManager::<Meta>::new(
        &doc,
        [(&text).into()],
        UndoOptions {
            capture_timeout: 1000,
            tracked_origins: vec![Some(editor.clone())],
        },
    )
    .unwrap();

    doc.transact_mut(editor.clone(), |tx| {
        // the host reports the time from inside a transaction
        undo.advance_time(5);
        tx.text(&text)?.insert(0, "a")
    })
    .unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert!(
        undo.set_meta(UndoStack::Undo, top.id, Meta(Probe(doc.clone())))
            .unwrap()
    );
    assert!(undo.peek(UndoStack::Undo).unwrap().meta.is_some());
    assert!(undo.undo().unwrap().unwrap().meta.is_some());
    assert_eq!(text.to_string(), "");
    undo.redo().unwrap();
    undo.add_tracked_origin(Some(Origin::new(Probe(doc.clone())))).unwrap();
    undo.remove_tracked_origin(&Some(editor.clone())).unwrap();
    text.insert(1, "b").unwrap();
    drop(undo);
    drop(editor);
}

/// A manager dropped inside a transaction of its document is released when
/// the transaction ends; a manager registered later is not touched by it.
#[test]
fn dropping_inside_a_transaction_releases_after_it() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "abc").unwrap();
    let undo = manager(&doc, &text);
    text.remove(0, 3).unwrap();
    assert_eq!(content(&doc, (1, 0)), Some(Content::String("abc".into())));

    doc.transact_mut(None, |tx| {
        drop(undo);
        // still registered while the lock is held
        assert!(tx.store_mut().history_hook.is_some());
        Ok(())
    })
    .unwrap();
    assert!(doc.store.read().unwrap().history_hook.is_none());
    assert!(doc.store.read().unwrap().retained.is_empty());
    assert_eq!(content(&doc, (1, 0)), Some(Content::Deleted(3)));

    // a new manager can be registered; a release meant for another manager
    // (the deferred one of a manager dropped earlier) leaves it alone
    let second = manager(&doc, &text);
    release_manager(&doc.store, 0).unwrap();
    text.insert(0, "x").unwrap();
    assert!(second.can_undo());
}

/// Metadata is handed out shared: reading it never runs `M`'s code, also
/// inside a transaction of another document (`M` here is not even `Clone`).
#[test]
fn reading_metadata_runs_no_caller_code() {
    struct NotClone(u64);
    let (a, b) = (doc(1), doc(2));
    let mut text = b.get_or_create_text("text").unwrap();
    let undo = UndoManager::<NotClone>::new(&b, [(&text).into()], UndoOptions::default()).unwrap();
    text.insert(0, "x").unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert!(undo.set_meta(UndoStack::Undo, top.id, NotClone(5)).unwrap());
    a.transact_mut(None, |_| {
        let meta = undo.peek(UndoStack::Undo).unwrap().meta.unwrap();
        assert_eq!(meta.0, 5);
        Ok(())
    })
    .unwrap();
    assert_eq!(undo.undo().unwrap().unwrap().meta.unwrap().0, 5);
}

/// Metadata passed to a `set_meta` that fails (inside a transaction of the
/// manager's own document) is released after that transaction, not inside
/// it.
#[test]
fn metadata_of_a_failed_set_meta_is_released_after_the_lock() {
    struct Touch(Doc, Arc<std::sync::atomic::AtomicBool>);
    impl Drop for Touch {
        fn drop(&mut self) {
            assert!(self.0.get_or_create_text("text").is_ok(), "dropped under the lock");
            self.1.store(true, std::sync::atomic::Ordering::SeqCst);
        }
    }

    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = UndoManager::<Touch>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
    text.insert(0, "x").unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    let released = Arc::new(std::sync::atomic::AtomicBool::new(false));
    doc.transact_mut(None, |_| {
        assert_eq!(
            undo.set_meta(UndoStack::Undo, top.id, Touch(doc.clone(), released.clone())),
            Err(JwstCodecError::Reentrant)
        );
        assert!(!released.load(std::sync::atomic::Ordering::SeqCst));
        Ok(())
    })
    .unwrap();
    assert!(released.load(std::sync::atomic::Ordering::SeqCst));
}

/// Metadata set for a new item while another thread collects the metadata
/// of dropped items is kept, and comes back with each undo.
#[test]
fn concurrent_metadata_is_kept() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = Arc::new(UndoManager::<u64>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap());
    let stop = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let reader = {
        let (undo, stop) = (undo.clone(), stop.clone());
        std::thread::spawn(move || {
            while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                undo.peek(UndoStack::Undo);
                undo.peek(UndoStack::Redo);
            }
        })
    };
    for i in 0..200 {
        text.insert(i, "x").unwrap();
        let top = undo.peek(UndoStack::Undo).unwrap();
        assert!(undo.set_meta(UndoStack::Undo, top.id, i).unwrap());
        if i % 10 == 9 {
            // redo items come and go
            undo.undo().unwrap();
            undo.redo().unwrap();
        }
    }
    stop.store(true, std::sync::atomic::Ordering::Relaxed);
    reader.join().unwrap();
    for i in (0..200).rev() {
        let undone = undo.undo().unwrap().unwrap();
        if i % 10 != 9 {
            assert_eq!(undone.meta.as_deref(), Some(&i), "item {i}");
        }
    }
}

/// An observer of the undo commit reads and sets redo metadata while the
/// undo returns: the popped item's metadata was taken before delivery, and
/// the metadata the observer set stays with the new redo item.
#[test]
fn observers_of_undo_commits_and_metadata() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = Arc::new(UndoManager::<u64>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap());
    text.insert(0, "a").unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert!(undo.set_meta(UndoStack::Undo, top.id, 7).unwrap());

    let observer = {
        let undo = undo.clone();
        doc.subscribe(move |event| {
            let popped = event
                .origin
                .as_ref()
                .and_then(|origin| origin.downcast_ref::<UndoOrigin>());
            if popped.is_some_and(|origin| origin.stack() == UndoStack::Undo) {
                let top = undo.peek(UndoStack::Redo).unwrap();
                assert_eq!(top.meta, None);
                assert!(undo.set_meta(UndoStack::Redo, top.id, 9).unwrap());
            }
        })
    };
    assert_eq!(undo.undo().unwrap().unwrap().meta.as_deref(), Some(&7));
    assert_eq!(undo.peek(UndoStack::Redo).unwrap().meta.as_deref(), Some(&9));
    assert_eq!(undo.redo().unwrap().unwrap().meta.as_deref(), Some(&9));
    drop(observer);
}

/// Metadata of items that leave the stacks is released right after the
/// commit that dropped them, not at a later call of the manager.
#[test]
fn metadata_of_cleared_items_is_released_with_the_commit() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = UndoManager::<Arc<Subscription>>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
    let seen = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    text.insert(0, "a").unwrap();
    undo.undo().unwrap();
    let top = undo.peek(UndoStack::Redo).unwrap();
    let subscription = {
        let seen = seen.clone();
        doc.subscribe(move |_| {
            seen.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        })
    };
    assert!(undo.set_meta(UndoStack::Redo, top.id, Arc::new(subscription)).unwrap());

    // a new local edit clears the redo stack; its own event was enqueued
    // with the subscription still alive
    text.insert(0, "b").unwrap();
    assert!(!undo.can_redo());
    let after_clear = seen.load(std::sync::atomic::Ordering::SeqCst);
    text.insert(0, "c").unwrap();
    assert_eq!(seen.load(std::sync::atomic::Ordering::SeqCst), after_clear, "released");
}

/// Metadata released inside a transaction of another document is dropped
/// after that document's lock is released too.
#[test]
fn metadata_is_released_after_every_document_lock() {
    #[derive(Clone)]
    struct Other(Doc, Arc<std::sync::atomic::AtomicBool>);
    impl Drop for Other {
        fn drop(&mut self) {
            if Arc::strong_count(&self.1) == 2 {
                // the last copy apart from the test's flag
                assert!(self.0.get_or_create_text("text").is_ok(), "dropped under a lock");
                self.1.store(true, std::sync::atomic::Ordering::SeqCst);
            }
        }
    }

    let (a, b) = (doc(1), doc(2));
    let mut text = a.get_or_create_text("text").unwrap();
    let undo = UndoManager::<Other>::new(&a, [(&text).into()], UndoOptions::default()).unwrap();
    let released = Arc::new(std::sync::atomic::AtomicBool::new(false));
    text.insert(0, "a").unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    assert!(
        undo.set_meta(UndoStack::Undo, top.id, Other(b.clone(), released.clone()))
            .unwrap()
    );

    b.transact_mut(None, |_| {
        undo.clear(true, true).unwrap();
        assert!(!released.load(std::sync::atomic::Ordering::SeqCst));
        Ok(())
    })
    .unwrap();
    assert!(released.load(std::sync::atomic::Ordering::SeqCst));

    // the state of a manager dropped inside the other document's transaction
    // is released after it as well
    text.insert(1, "b").unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap();
    let released = Arc::new(std::sync::atomic::AtomicBool::new(false));
    assert!(
        undo.set_meta(UndoStack::Undo, top.id, Other(b.clone(), released.clone()))
            .unwrap()
    );
    b.transact_mut(None, |_| {
        drop(undo);
        Ok(())
    })
    .unwrap();
    assert!(released.load(std::sync::atomic::Ordering::SeqCst));
}

/// Undo of an insertion that a redo recreated deletes exactly the recreated
/// ids of that insertion. Yjs deletes from the followed start to the end of
/// the recreated item; no public operation sequence was found where the two
/// differ (the right part of a merged insertion is always popped first and
/// splits the recreation), so the state is built directly: the recreation
/// (1, 6..12) of "abcdef" (1, 0..6) is one unsplit item, and a stack item
/// inserted only (1, 0..3).
#[test]
fn undo_deletes_exactly_the_recreated_ids_of_its_insertion() {
    let doc = doc(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let undo = manager(&doc, &text);
    text.insert(0, "abcdef").unwrap();
    undo.stop_capturing().unwrap();
    text.remove(0, 6).unwrap();
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "abcdef");
    {
        let store = doc.store.read().unwrap();
        assert_eq!(store.redone.follow(Id::new(1, 0)), Id::new(1, 6));
        let recreated = store.get_node((1, 6)).unwrap();
        assert_eq!(recreated.len(), 6, "one unsplit recreation");
    }

    // a stack item that inserted only "abc"
    {
        let mut store = doc.store.write().unwrap();
        let state = store
            .history_hook
            .as_deref_mut()
            .and_then(|hook| hook.as_any_mut().downcast_mut::<UndoState>())
            .unwrap();
        state.undo.clear();
        state.redo.clear();
        let mut insertions = DeleteSet::default();
        insertions.add(1, 0, 3);
        state.undo.push(StackItem {
            id: state.next_item,
            insertions,
            deletions: DeleteSet::default(),
            retained: DeleteSet::default(),
            meta: None,
        });
        state.next_item += 1;
    }

    assert!(undo.undo().unwrap().is_some());
    // the right half of the recreation stays (Yjs would delete all of it)
    assert_eq!(text.to_string(), "def");
}

/// A manager refused for a scope of another document, created inside a read
/// transaction, releases the origins it was given after that transaction.
#[test]
fn a_refused_manager_releases_its_origins_after_the_lock() {
    struct Flag(Doc, Arc<std::sync::atomic::AtomicBool>);
    impl Drop for Flag {
        fn drop(&mut self) {
            assert!(self.0.get_or_create_text("text").is_ok(), "dropped under the lock");
            self.1.store(true, std::sync::atomic::Ordering::SeqCst);
        }
    }
    impl PartialEq for Flag {
        fn eq(&self, _: &Self) -> bool {
            true
        }
    }
    impl Eq for Flag {}
    impl std::hash::Hash for Flag {
        fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
    }
    impl Clone for Flag {
        fn clone(&self) -> Self {
            unreachable!("never cloned")
        }
    }

    let (a, b) = (doc(1), doc(2));
    let foreign = b.get_or_create_text("text").unwrap();
    let released = Arc::new(std::sync::atomic::AtomicBool::new(false));
    // the options hold the last copy of the origin
    let options = UndoOptions {
        tracked_origins: vec![Some(Origin::new(Flag(a.clone(), released.clone())))],
        ..Default::default()
    };
    a.transact(|_| {
        assert_eq!(
            UndoManager::<()>::new(&a, [(&foreign).into()], options).unwrap_err(),
            JwstCodecError::ForeignType
        );
        assert!(!released.load(std::sync::atomic::Ordering::SeqCst));
    })
    .unwrap();
    assert!(released.load(std::sync::atomic::Ordering::SeqCst));
}

// Each peer independently formats the same character. The second delivery
// makes the receiver emit a local formatting maintenance commit.
fn apply_concurrent_formats(receiver: &Doc) {
    let base = receiver.encode_update_v1().unwrap();
    let peers = [202, 303].map(|client| {
        let mut peer = doc(client);
        let mut text = peer.get_or_create_text("text").unwrap();
        peer.apply_update_from_binary_v1(&base).unwrap();
        text.apply_delta(&[TextDeltaOp::Retain {
            retain: 1,
            format: format(&[("bold", Any::True)]),
        }])
        .unwrap();
        peer
    });
    for peer in &peers {
        sync(peer, receiver);
    }
    let deleted = receiver.get_delete_sets();
    assert!(deleted.get(&202).is_some() || deleted.get(&303).is_some());
}

#[test]
fn tracked_formatting_cleanup_preserves_redo() {
    use crate::doc::types::text::cleanup::FormattingCleanup;

    let doc = doc(101);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "ab").unwrap();
    let undo = manager(&doc, &text);
    undo.track_origin_type::<FormattingCleanup>().unwrap();
    undo.advance_time(100);
    text.insert(2, "x").unwrap();
    undo.undo().unwrap().unwrap();
    let redo = undo.peek(UndoStack::Redo).unwrap().id;

    apply_concurrent_formats(&doc);
    assert!(undo.can_redo(), "formatting cleanup cleared redo");
    assert!(!undo.can_undo());
    assert_eq!(undo.peek(UndoStack::Redo).unwrap().id, redo);
    undo.redo().unwrap().unwrap();
    assert_eq!(text.to_string(), "abx");
}

#[test]
fn tracked_formatting_cleanup_preserves_the_capture_window() {
    use crate::doc::types::text::cleanup::FormattingCleanup;

    let doc = doc(101);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "ab").unwrap();
    let undo = manager(&doc, &text);
    undo.track_origin_type::<FormattingCleanup>().unwrap();
    undo.advance_time(100);
    text.insert(2, "x").unwrap();
    let first = undo.peek(UndoStack::Undo).unwrap().id;

    undo.advance_time(550);
    apply_concurrent_formats(&doc);
    assert_eq!(undo.peek(UndoStack::Undo).unwrap().id, first);
    undo.advance_time(700);
    text.insert(3, "y").unwrap();
    assert_ne!(
        undo.peek(UndoStack::Undo).unwrap().id,
        first,
        "formatting cleanup advanced the capture window"
    );
    undo.undo().unwrap().unwrap();
    assert_eq!(text.to_string(), "abx");
    undo.undo().unwrap().unwrap();
    assert_eq!(text.to_string(), "ab");
}
