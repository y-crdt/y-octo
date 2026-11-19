//! [Doc::apply_local_update]: updates authored outside the document enter its
//! history exactly, remote updates waiting in it do not.

use std::sync::Arc;

use super::*;

fn doc(client: Client) -> Doc {
    DocOptions::new().with_client_id(client).build()
}

/// What `to` misses from `from`.
fn diff(from: &Doc, to: &Doc) -> Update {
    from.encode_state_as_update(&to.get_state_vector()).unwrap()
}

fn sync(from: &Doc, to: &Doc) {
    to.apply_update_with_origin(diff(from, to), Origin::new("remote"))
        .unwrap();
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Renderer;

/// The document with a manager tracking `renderer` and the renderer's own
/// document (another client), synchronized.
fn setup() -> (Doc, Doc, Origin, UndoManager) {
    let native = doc(1);
    native.get_or_create_text("text").unwrap();
    native.get_or_create_map("map").unwrap();
    let renderer = doc(50);
    sync(&native, &renderer);
    let origin = Origin::new(Renderer);
    let undo = UndoManager::new(
        &native,
        [(&native).into()],
        UndoOptions {
            tracked_origins: vec![None, Some(origin.clone())],
            ..Default::default()
        },
    )
    .unwrap();
    (native, renderer, origin, undo)
}

fn format(attrs: &[(&str, Any)]) -> Option<TextAttributes> {
    Some(attrs.iter().map(|(k, v)| (k.to_string(), v.clone())).collect())
}

#[test]
fn renderer_edits_enter_the_native_history() {
    let (native, renderer, origin, undo) = setup();
    let peer = doc(2);
    sync(&native, &peer);
    let mut text = native.get_or_create_text("text").unwrap();
    text.insert(0, "base").unwrap();
    undo.clear(true, true).unwrap();
    sync(&native, &renderer);
    sync(&native, &peer);

    // the renderer inserts, formats, deletes and nests in one transaction
    let mut rendered = renderer.get_or_create_text("text").unwrap();
    let map = renderer.get_or_create_map("map").unwrap();
    let block = renderer.create_text().unwrap();
    renderer
        .transact_mut(None, |tx| {
            let mut text = tx.text(&rendered)?;
            text.insert(4, " typed")?;
            text.apply_delta(&[TextDeltaOp::Retain {
                retain: 4,
                format: format(&[("bold", Any::True)]),
            }])?;
            text.remove(0, 1)?;
            tx.map(&map)?.insert("block".into(), Value::Text(block.clone()))
        })
        .unwrap();
    let Some(Value::Text(block)) = map.get("block") else {
        unreachable!()
    };
    renderer
        .transact_mut(None, |tx| tx.text(&block)?.insert(0, "nested"))
        .unwrap();
    rendered = renderer.get_or_create_text("text").unwrap();
    assert_eq!(rendered.to_string(), "ase typed");

    assert_eq!(
        native.apply_local_update(diff(&renderer, &native), origin).unwrap(),
        LocalUpdate::Applied
    );
    assert_eq!(text.to_string(), "ase typed");
    assert!(undo.can_undo());

    // a remote peer edits meanwhile
    let mut remote = peer.get_or_create_text("text").unwrap();
    sync(&native, &peer);
    remote.insert(9, "!").unwrap();
    sync(&peer, &native);

    // both renderer transactions arrived in one local update: one commit
    assert!(undo.undo().unwrap().is_some());
    assert!(!undo.can_undo());
    assert_eq!(text.to_string(), "base!");
    assert_eq!(text.to_delta().len(), 1, "formatting undone");
    assert!(native.get_or_create_map("map").unwrap().get("block").is_none());

    assert!(undo.redo().unwrap().is_some());
    assert_eq!(text.to_string(), "ase typed!");
    let Some(Value::Text(recreated)) = native.get_or_create_map("map").unwrap().get("block") else {
        panic!("block not recreated");
    };
    assert_eq!(recreated.to_string(), "nested");
}

#[test]
fn unblocked_remote_updates_stay_out_of_the_history() {
    let (native, renderer, origin, undo) = setup();
    let peer = doc(2);
    sync(&native, &peer);

    // the renderer types; the peer gets it first and edits inside it
    let mut rendered = renderer.get_or_create_text("text").unwrap();
    rendered.insert(0, "hello").unwrap();
    let local = diff(&renderer, &native);
    sync(&renderer, &peer);
    let mut remote = peer.get_or_create_text("text").unwrap();
    remote.insert(5, " world").unwrap();
    let remote_update = peer.encode_state_as_update(&renderer.get_state_vector()).unwrap();

    // the peer's update arrives first and waits for the renderer's structs
    native
        .apply_update_with_origin(remote_update, Origin::new("remote"))
        .unwrap();
    assert!(native.has_pending_updates());
    let text = native.get_or_create_text("text").unwrap();
    assert_eq!(text.to_string(), "");

    let events = Arc::new(std::sync::Mutex::new(Vec::new()));
    let _subscription = {
        let events = events.clone();
        native.subscribe(move |event| events.lock().unwrap().push((event.local, event.inserted.clone())))
    };
    assert_eq!(native.apply_local_update(local, origin).unwrap(), LocalUpdate::Applied);
    assert_eq!(text.to_string(), "hello world");
    assert!(!native.has_pending_updates());
    let events = events.lock().unwrap().clone();
    assert_eq!(events.len(), 2, "the local commit, then the unblocked remote one");
    assert!(events[0].0 && !events[1].0);
    assert!(
        events[0].1.get(&2).is_none(),
        "the local commit has only the renderer's structs"
    );

    // undo removes the renderer's text, not the peer's
    undo.undo().unwrap();
    assert_eq!(text.to_string(), " world");
    assert!(!undo.can_undo());
    undo.redo().unwrap();
    assert_eq!(text.to_string(), "hello world");
}

#[test]
fn updates_with_missing_dependencies_are_not_applied() {
    let (native, renderer, origin, undo) = setup();
    let mut rendered = renderer.get_or_create_text("text").unwrap();
    rendered.insert(0, "ab").unwrap();
    let first = diff(&renderer, &native);
    let state = renderer.get_state_vector();
    rendered.insert(2, "cd").unwrap();
    // only the second insertion: it needs (50, 0..2)
    let second = renderer.encode_state_as_update(&state).unwrap();

    let before = native.get_state_vector();
    let LocalUpdate::MissingDependencies(missing) = native.apply_local_update(second.clone(), origin.clone()).unwrap()
    else {
        panic!("applied without its dependencies");
    };
    assert_eq!(missing.get(&50), 0);
    assert_eq!(native.get_state_vector(), before, "nothing applied");
    assert!(!native.has_pending_updates());
    assert!(!undo.can_undo());

    // a deletion of structs the document lacks is missing too
    let mut deleting = doc(60);
    deleting
        .apply_update_from_binary_v1(renderer.encode_update_v1().unwrap())
        .unwrap();
    deleting.get_or_create_text("text").unwrap().remove(0, 1).unwrap();
    let deletion = deleting.encode_state_as_update(&renderer.get_state_vector()).unwrap();
    assert!(matches!(
        native.apply_local_update(deletion, origin.clone()).unwrap(),
        LocalUpdate::MissingDependencies(missing) if missing.get(&50) == 0
    ));

    // after resynchronizing, it applies
    assert_eq!(
        native.apply_local_update(first, origin.clone()).unwrap(),
        LocalUpdate::Applied
    );
    assert_eq!(native.apply_local_update(second, origin).unwrap(), LocalUpdate::Applied);
    assert_eq!(native.get_or_create_text("text").unwrap().to_string(), "abcd");
}

#[test]
fn duplicates_and_empty_updates_capture_nothing() {
    let (native, renderer, origin, undo) = setup();
    let mut rendered = renderer.get_or_create_text("text").unwrap();
    rendered.insert(0, "ab").unwrap();
    let update = diff(&renderer, &native);
    native.apply_local_update(update.clone(), origin.clone()).unwrap();
    let top = undo.peek(UndoStack::Undo).unwrap().id;

    let commits = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let _subscription = {
        let commits = commits.clone();
        native.subscribe(move |_| {
            commits.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        })
    };
    assert_eq!(
        native.apply_local_update(update, origin.clone()).unwrap(),
        LocalUpdate::Applied
    );
    assert_eq!(
        native.apply_local_update(Update::default(), origin).unwrap(),
        LocalUpdate::Applied
    );
    assert_eq!(commits.load(std::sync::atomic::Ordering::SeqCst), 0);
    assert_eq!(undo.peek(UndoStack::Undo).unwrap().id, top);
    undo.undo().unwrap();
    assert!(!undo.can_undo());
}

/// Native undo/redo reach the renderer as remote updates; its next edits come
/// back as local updates; both sides converge and nothing echoes.
#[test]
fn rounds_between_native_and_renderer_converge() {
    let (native, renderer, origin, undo) = setup();
    let text = native.get_or_create_text("text").unwrap();
    let mut rendered = renderer.get_or_create_text("text").unwrap();

    for round in 0..3 {
        rendered.insert(rendered.len(), format!("r{round} ")).unwrap();
        native
            .apply_local_update(diff(&renderer, &native), origin.clone())
            .unwrap();
        undo.stop_capturing().unwrap();
    }
    assert_eq!(text.to_string(), "r0 r1 r2 ");

    undo.undo().unwrap();
    sync(&native, &renderer);
    assert_eq!(rendered.to_string(), "r0 r1 ");
    // the renderer applied a remote update: nothing to send back
    assert!(
        diff(&renderer, &native)
            .structs
            .values()
            .all(|structs| structs.is_empty())
    );

    rendered.insert(0, "x").unwrap();
    native
        .apply_local_update(diff(&renderer, &native), origin.clone())
        .unwrap();
    assert!(!undo.can_redo(), "a new local edit clears redo");
    undo.undo().unwrap();
    undo.undo().unwrap();
    sync(&native, &renderer);
    assert_eq!(rendered.to_string(), "r0 ");
    undo.redo().unwrap();
    sync(&native, &renderer);
    assert_eq!(rendered.to_string(), text.to_string());
    assert_eq!(native.get_state_vector(), renderer.get_state_vector());
}

/// A remote update that only deletes structs of the renderer waits for them;
/// the local update that brings them unblocks it in a remote transaction.
#[test]
fn unblocked_remote_deletions_stay_out_of_the_history() {
    let (native, renderer, origin, undo) = setup();
    let mut rendered = renderer.get_or_create_text("text").unwrap();
    rendered.insert(0, "hello").unwrap();
    let local = diff(&renderer, &native);

    let mut deleter = doc(3);
    deleter
        .apply_update_from_binary_v1(renderer.encode_update_v1().unwrap())
        .unwrap();
    deleter.get_or_create_text("text").unwrap().remove(0, 1).unwrap();
    let deletion = deleter.encode_state_as_update(&renderer.get_state_vector()).unwrap();
    assert!(
        deletion.structs.values().all(|structs| structs.is_empty()),
        "deletion only"
    );

    native
        .apply_update_with_origin(deletion, Origin::new("remote"))
        .unwrap();
    assert!(native.has_pending_updates());

    assert_eq!(native.apply_local_update(local, origin).unwrap(), LocalUpdate::Applied);
    let text = native.get_or_create_text("text").unwrap();
    assert_eq!(text.to_string(), "ello");
    assert!(!native.has_pending_updates());

    // the remote deletion is not the user's: undo takes back only the rest
    // of the renderer's insertion, redo recreates only that
    undo.undo().unwrap();
    assert_eq!(text.to_string(), "");
    undo.redo().unwrap();
    assert_eq!(text.to_string(), "ello");
}

/// A waiting remote deletion that spans two renderer updates is applied in
/// parts: the part whose structs arrived is deleted in its own remote commit,
/// the right tail keeps waiting; repeated deliveries commit nothing.
#[test]
fn partly_unblocked_remote_deletions_keep_their_tail() {
    let (native, renderer, origin, undo) = setup();
    let mut rendered = renderer.get_or_create_text("text").unwrap();
    rendered.insert(0, "hello").unwrap();
    let first = diff(&renderer, &native);
    let state = renderer.get_state_vector();
    rendered.insert(5, "world").unwrap();
    let second = renderer.encode_state_as_update(&state).unwrap();

    // a peer's deletion of "lowo" (50, 3..7), across both renderer updates
    let mut deletion = Update::default();
    deletion.delete_set.add(50, 3, 4);

    let events = Arc::new(std::sync::Mutex::new(Vec::new()));
    let _subscription = {
        let events = events.clone();
        native.subscribe(move |event| {
            events
                .lock()
                .unwrap()
                .push((event.local, event.inserted.clone(), event.deleted.clone()))
        })
    };
    let take = || std::mem::take(&mut *events.lock().unwrap());

    native
        .apply_update_with_origin(deletion.clone(), Origin::new("remote"))
        .unwrap();
    assert!(take().is_empty(), "nothing to delete yet");
    assert!(native.has_pending_updates());

    let text = native.get_or_create_text("text").unwrap();
    assert_eq!(
        native.apply_local_update(first, origin.clone()).unwrap(),
        LocalUpdate::Applied
    );
    assert_eq!(text.to_string(), "hel");
    let commits = take();
    assert_eq!(commits.len(), 2);
    assert!(commits[0].0 && commits[0].2.is_empty(), "the local commit inserts only");
    assert!(!commits[1].0, "the deletion is a remote commit");
    assert_eq!(commits[1].2.get(&50).unwrap().canonical_ranges(), vec![3..5]);
    assert!(native.has_pending_updates(), "the right tail waits");

    // a repeated delivery commits nothing
    native
        .apply_update_with_origin(deletion.clone(), Origin::new("remote"))
        .unwrap();
    assert!(take().is_empty());

    assert_eq!(native.apply_local_update(second, origin).unwrap(), LocalUpdate::Applied);
    assert_eq!(text.to_string(), "helrld");
    let commits = take();
    assert_eq!(commits.len(), 2);
    assert_eq!(commits[1].2.get(&50).unwrap().canonical_ranges(), vec![5..7]);
    assert!(!native.has_pending_updates());

    native
        .apply_update_with_origin(deletion, Origin::new("remote"))
        .unwrap();
    assert!(take().is_empty(), "duplicate after completion");

    // undo takes back the renderer's insertions, not the remote deletion
    while undo.undo().unwrap().is_some() {}
    assert_eq!(text.to_string(), "");
    while undo.redo().unwrap().is_some() {}
    assert_eq!(text.to_string(), "helrld");
}

/// Resynchronizes `native` from `renderer` as `missing` says, then retries.
fn recover(native: &Doc, renderer: &Doc, origin: &Origin, missing: &StateVector, update: Update) {
    let mut from = native.get_state_vector();
    for (client, clock) in missing.iter() {
        assert_eq!(*clock, from.get(client), "the clock the document integrated");
        from.insert(*client, *clock);
    }
    let sync = renderer.encode_state_as_update(&from).unwrap();
    assert_eq!(
        native.apply_local_update(sync, origin.clone()).unwrap(),
        LocalUpdate::Applied
    );
    assert_eq!(
        native.apply_local_update(update, origin.clone()).unwrap(),
        LocalUpdate::Applied
    );
}

/// The clock of a refused update is the integrated state, whatever the
/// update itself reaches; one resynchronization from it makes the retry
/// succeed, and the refusal changed nothing.
#[test]
fn missing_dependencies_point_at_the_integrated_state() {
    let (native, renderer, origin, _undo) = setup();
    let mut rendered = renderer.get_or_create_text("text").unwrap();

    // nothing of the renderer integrated: clock zero
    rendered.insert(0, "ab").unwrap();
    let state = renderer.get_state_vector();
    rendered.insert(2, "cd").unwrap();
    let later = renderer.encode_state_as_update(&state).unwrap();
    let before = native.encode_update_v1().unwrap();
    let LocalUpdate::MissingDependencies(missing) = native.apply_local_update(later.clone(), origin.clone()).unwrap()
    else {
        panic!("applied")
    };
    assert_eq!(missing, StateVector::from([(50, 0)]));
    assert_eq!(native.encode_update_v1().unwrap(), before, "refusal changed nothing");
    recover(&native, &renderer, &origin, &missing, later);
    assert_eq!(native.get_or_create_text("text").unwrap().to_string(), "abcd");

    // part of the renderer integrated (4 clocks). The renderer types "efgh"
    // (4..8) and deletes its "f" (5); the package it sends holds "gh"
    // (6..8) and its whole delete set: the gap and the deletion target are
    // both missing here, and the clock points at the integrated 4
    rendered.insert(4, "efgh").unwrap();
    rendered.remove(5, 1).unwrap();
    let package = renderer.encode_state_as_update(&StateVector::from([(50, 6)])).unwrap();
    assert!(package.delete_set.get(&50).is_some_and(|ranges| ranges.contains(5)));
    let before = native.encode_update_v1().unwrap();
    let LocalUpdate::MissingDependencies(missing) = native.apply_local_update(package.clone(), origin.clone()).unwrap()
    else {
        panic!("applied")
    };
    assert_eq!(missing, StateVector::from([(50, 4)]));
    assert_eq!(native.encode_update_v1().unwrap(), before, "refusal changed nothing");

    // one diff from the author at the returned clock, then the same package
    recover(&native, &renderer, &origin, &missing, package);
    assert_eq!(native.get_or_create_text("text").unwrap().to_string(), "abcdegh");
    assert_eq!(native.get_state_vector().get(&50), renderer.get_state_vector().get(&50));
    assert_eq!(
        native.get_or_create_text("text").unwrap().to_delta(),
        rendered.to_delta()
    );

    // The renderer's own transaction updates: "ij" (8..10), "kl" (10..12),
    // then the deletion of its "k" (10). The package merges the first and the
    // last (the middle one was lost): "ij" arrives, the deletion target does
    // not. The clock is the integrated 8, not the 10 the package reaches.
    let sent = Arc::new(std::sync::Mutex::new(Vec::new()));
    let subscription = {
        let sent = sent.clone();
        renderer.subscribe(move |event| sent.lock().unwrap().push(event.update.clone()))
    };
    // (text indices: "abcdegh" has 7 characters)
    rendered.insert(7, "ij").unwrap();
    rendered.insert(9, "kl").unwrap();
    rendered.remove(9, 1).unwrap();
    drop(subscription);
    let sent = sent.lock().unwrap().clone();
    assert_eq!(sent.len(), 3);
    let package = Update::merge([
        Update::decode_v1(&sent[0]).unwrap(),
        Update::decode_v1(&sent[2]).unwrap(),
    ]);
    let before = native.encode_update_v1().unwrap();
    let LocalUpdate::MissingDependencies(missing) = native.apply_local_update(package.clone(), origin.clone()).unwrap()
    else {
        panic!("applied")
    };
    assert_eq!(missing, StateVector::from([(50, 8)]));
    assert_eq!(native.encode_update_v1().unwrap(), before, "refusal changed nothing");
    recover(&native, &renderer, &origin, &missing, package);
    assert_eq!(native.get_or_create_text("text").unwrap().to_string(), "abcdeghijl");
    assert_eq!(native.get_state_vector().get(&50), renderer.get_state_vector().get(&50));
    assert_eq!(
        native.get_or_create_text("text").unwrap().to_delta(),
        rendered.to_delta()
    );
}

/// Formatting cleanup (Yjs `cleanupYTextAfterTransaction`) follows the
/// remote commit of a deletion the local update unblocked, as its own
/// uncaptured commit; the local commit itself is not cleaned up, and the
/// history holds only the renderer's transaction.
#[test]
fn cleanup_after_an_unblocked_remote_deletion_stays_out_of_the_history() {
    let (native, renderer, origin, undo) = setup();
    let rendered = renderer.get_or_create_text("text").unwrap();
    renderer
        .transact_mut(None, |tx| {
            let mut text = tx.text(&rendered)?;
            text.insert(0, "abc")?;
            text.apply_delta(&[
                TextDeltaOp::Retain {
                    retain: 1,
                    format: None,
                },
                TextDeltaOp::Retain {
                    retain: 1,
                    format: format(&[("bold", Any::True)]),
                },
            ])
        })
        .unwrap();
    let local = diff(&renderer, &native);

    // a remote deletion of only the bold "b", without the gap cleanup a
    // deleting client normally does locally, arrives first and waits
    let mut deletion = Update::default();
    deletion.delete_set.add(50, 1, 1);
    native
        .apply_update_with_origin(deletion, Origin::new("remote"))
        .unwrap();
    assert!(native.has_pending_updates());

    let events = Arc::new(std::sync::Mutex::new(Vec::new()));
    let _subscription = {
        let events = events.clone();
        native.subscribe(move |event| {
            let cleanup = event.origin.as_ref().is_some_and(|origin| {
                origin
                    .downcast_ref::<types::text::cleanup::FormattingCleanup>()
                    .is_some()
            });
            events
                .lock()
                .unwrap()
                .push((event.local, cleanup, event.deleted.clone()));
        })
    };
    assert_eq!(native.apply_local_update(local, origin).unwrap(), LocalUpdate::Applied);
    let text = native.get_or_create_text("text").unwrap();
    assert_eq!(text.to_string(), "ac");
    let events = events.lock().unwrap().clone();
    assert!(events.len() >= 2, "{events:?}");
    assert!(events[0].0 && !events[0].1, "the local commit, no cleanup in it");
    assert!(!events[1].0 && !events[1].1, "the unblocked remote deletion");
    // the remote deletion leaves the bold markers around nothing: removed by
    // a cleanup commit of its own
    assert_eq!(events.len(), 3, "{events:?}");
    assert!(events[2].0 && events[2].1);
    assert_eq!(text.to_delta().len(), 1, "no formatting left");

    // one stack item: the renderer's; cleanup neither joined nor cleared it
    assert!(undo.undo().unwrap().is_some());
    assert!(!undo.can_undo());
    assert_eq!(text.to_string(), "");
    assert!(undo.redo().unwrap().is_some());
    assert_eq!(text.to_string(), "ac");
}
