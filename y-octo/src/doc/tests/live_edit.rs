//! A live document edited locally by index while remote updates arrive, and
//! incremental GC/merge against one full pass.

use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha20Rng;

use super::*;

fn sync(from: &Doc, to: &mut Doc) {
    let update = from.encode_state_as_update_v1(&to.get_state_vector()).unwrap();
    to.apply_update_from_binary_v1(update).unwrap();
}

#[test]
fn reordered_nested_update_can_be_saved_before_its_parent() {
    let mut source = Doc::with_client(101);
    let mut map = source.get_or_create_map("map").unwrap();
    let mut text = source.create_text().unwrap();
    map.insert("child".into(), text.clone()).unwrap();
    let parent_update = source.encode_update_v1().unwrap();
    let parent_state = source.get_state_vector();

    source.set_client(202);
    text.insert(0, "nested").unwrap();
    let child_update = source.encode_state_as_update_v1(&parent_state).unwrap();

    let mut relay = Doc::with_client(303);
    relay.apply_update_from_binary_v1(&child_update).unwrap();
    assert!(relay.has_pending_updates());
    assert_eq!(relay.get_state_vector(), StateVector::default());

    let mut restored = Doc::with_client(404);
    restored
        .apply_update_from_binary_v1(relay.encode_update_v1().unwrap())
        .unwrap();
    assert!(restored.has_pending_updates());
    restored.apply_update_from_binary_v1(parent_update).unwrap();
    assert!(!restored.has_pending_updates());
    assert_eq!(restored.get_state_vector(), source.get_state_vector());
    restored.apply_update_from_binary_v1(child_update).unwrap();
    assert!(!restored.has_pending_updates());
    assert_eq!(restored.get_state_vector(), source.get_state_vector());

    let reopened = Doc::try_from_binary_v1(restored.encode_update_v1().unwrap()).unwrap();
    let child = reopened.get_or_create_map("map").unwrap().get("child").unwrap();
    assert_eq!(child.to_text().unwrap().to_string(), "nested");
}

#[test]
fn indexed_array_read_skips_deleted_nested_value() {
    let source = Doc::with_client(1);
    let mut array = source.get_or_create_array("array").unwrap();
    array.push("before").unwrap();
    array.push(source.create_text().unwrap()).unwrap();
    array.push("after").unwrap();
    array.remove(1, 1).unwrap();

    let mut peer = DocOptions::new().with_client_id(2).auto_gc(false).build();
    sync(&source, &mut peer);
    let array = peer.get_or_create_array("array").unwrap();
    assert_eq!(array.get(1), Some(Value::Any(Any::String("after".into()))));
}

#[test]
fn collected_nested_handles_stay_retired() {
    let doc = Doc::with_client(1);
    let mut root = doc.get_or_create_array("root").unwrap();
    let mut map = doc.create_map().unwrap();
    let mut child = doc.create_array().unwrap();
    child.push(7).unwrap();
    map.insert("child".into(), child.clone()).unwrap();
    root.push(map.clone()).unwrap();
    let child_id = child.id().unwrap();

    root.remove(0, 1).unwrap();
    doc.gc().unwrap();
    assert!(doc.store.read().unwrap().get_node(child_id).unwrap().is_gc());
    let state = doc.get_state_vector();
    let update = doc.encode_update_v1().unwrap();

    assert_eq!(map.insert("late".into(), 1), Err(JwstCodecError::InvalidParent));
    assert_eq!(child.push(2), Err(JwstCodecError::InvalidParent));
    assert_eq!(root.push(child), Err(JwstCodecError::TypeAlreadyInserted));
    assert_eq!(doc.get_state_vector(), state);
    assert_eq!(doc.encode_update_v1().unwrap(), update);
}

#[test]
fn partial_remote_apply_preserves_changes_and_invalidates_only_touched_markers() {
    let mut doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let mut untouched = doc.get_or_create_text("untouched").unwrap();
    for text in [&mut text, &mut untouched] {
        text.insert(0, "bc").unwrap();
        text.insert(0, "a").unwrap();
        text.insert(2, "x").unwrap();
    }
    let marker_count = |text: &Text| text.0.read(|_, ty| ty.markers.as_ref().unwrap().len()).unwrap();
    assert!(marker_count(&text) > 0);
    let untouched_markers = marker_count(&untouched);
    assert!(untouched_markers > 0);

    let mut map = doc.get_or_create_map("map").unwrap();
    map.insert("local".into(), 1).unwrap();
    let commits = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let sink = commits.clone();
    let _subscription = doc.subscribe(move |event| sink.lock().unwrap().push(event.clone()));
    let state = doc.get_state_vector();
    let mut peer = Doc::with_client(2);
    sync(&doc, &mut peer);
    peer.get_or_create_text("text").unwrap().insert(0, "r").unwrap();
    peer.get_or_create_map("map")
        .unwrap()
        .insert("remote".into(), 2)
        .unwrap();
    let mut update = peer.encode_state_as_update(&state).unwrap();

    // The two valid items integrate before repair rejects a forward origin.
    let id = Id::new(2, peer.get_state_vector().get(&2));
    update
        .structs
        .get_mut(&2)
        .unwrap()
        .push_back(WireStruct::Item(Box::new(WireItem {
            id,
            len: 1,
            origin_left_id: Some(id),
            origin_right_id: None,
            parent: None,
            parent_sub: None,
            content: WireContent::String("x".into()),
            flags: item_flags::ITEM_COUNTABLE,
        })));

    assert_eq!(doc.apply_update(update), Err(JwstCodecError::InvalidParent));
    assert_eq!(text.to_string(), "rabxc");
    assert_eq!(marker_count(&text), 0);
    assert_eq!(marker_count(&untouched), untouched_markers);
    assert_eq!(map.get("local"), Some(Value::Any(Any::Integer(1))));
    assert_eq!(map.get("remote"), Some(Value::Any(Any::Integer(2))));

    let commits = commits.lock().unwrap();
    assert_eq!(commits.len(), 1);
    let event = &commits[0];
    assert!(!event.local);
    assert_eq!(event.changed.len(), 2);
    assert!(event.touches_subtree(&TypeIdentity::Root("text".into())));
    assert_eq!(
        event
            .changed
            .iter()
            .find(|entry| entry.identity == TypeIdentity::Root("map".into())),
        Some(&ChangedType {
            identity: TypeIdentity::Root("map".into()),
            keys: vec!["remote".into()],
        })
    );
}

/// Local index edits interleaved with remote inserts and deletes: the local
/// search markers must not keep positions from before the remote change
/// (each step is compared with a plain string).
#[test]
#[cfg_attr(miri, ignore)]
fn text_index_edits_after_remote_changes() {
    for seed in 0..100 {
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let mut local = Doc::with_client(1);
        let mut remote = Doc::with_client(2);
        let mut text = local.get_or_create_text("text").unwrap();
        let mut remote_text = remote.get_or_create_text("text").unwrap();
        let mut model = String::new();

        for step in 0..80 {
            sync(&local, &mut remote);
            let roll = rng.random_range(0..10);
            if roll < 3 {
                let sv = local.get_state_vector();
                if roll == 0 && !model.is_empty() {
                    let pos = rng.random_range(0..model.len());
                    let len = rng.random_range(1..=(model.len() - pos).min(4));
                    remote_text.remove(pos as u64, len as u64).unwrap();
                    model.replace_range(pos..pos + len, "");
                } else {
                    let pos = rng.random_range(0..=model.len());
                    let s = format!("<r{step}>");
                    remote_text.insert(pos as u64, &s).unwrap();
                    model.insert_str(pos, &s);
                }
                local
                    .apply_update_from_binary_v1(remote.encode_state_as_update_v1(&sv).unwrap())
                    .unwrap();
            } else if roll < 5 && !model.is_empty() {
                let pos = rng.random_range(0..model.len());
                let len = rng.random_range(1..=(model.len() - pos).min(4));
                text.remove(pos as u64, len as u64).unwrap();
                model.replace_range(pos..pos + len, "");
            } else {
                let pos = rng.random_range(0..=model.len());
                let s = format!("[l{step}]");
                text.insert(pos as u64, &s).unwrap();
                model.insert_str(pos, &s);
            }
            assert_eq!(text.to_string(), model, "seed {seed} step {step}");
        }
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn array_index_edits_after_remote_changes() {
    for seed in 0..100 {
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let mut local = Doc::with_client(1);
        let mut remote = Doc::with_client(2);
        let mut array = local.get_or_create_array("array").unwrap();
        let mut remote_array = remote.get_or_create_array("array").unwrap();
        let mut model: Vec<i64> = Vec::new();

        for step in 0..80i64 {
            sync(&local, &mut remote);
            let roll = rng.random_range(0..10);
            if roll < 3 {
                let sv = local.get_state_vector();
                if roll == 0 && !model.is_empty() {
                    let pos = rng.random_range(0..model.len());
                    let len = rng.random_range(1..=(model.len() - pos).min(3));
                    remote_array.remove(pos as u64, len as u64).unwrap();
                    model.drain(pos..pos + len);
                } else {
                    let pos = rng.random_range(0..=model.len());
                    remote_array.insert(pos as u64, Any::BigInt64(-step)).unwrap();
                    model.insert(pos, -step);
                }
                local
                    .apply_update_from_binary_v1(remote.encode_state_as_update_v1(&sv).unwrap())
                    .unwrap();
            } else if roll < 5 && !model.is_empty() {
                let pos = rng.random_range(0..model.len());
                let len = rng.random_range(1..=(model.len() - pos).min(3));
                array.remove(pos as u64, len as u64).unwrap();
                model.drain(pos..pos + len);
            } else {
                let pos = rng.random_range(0..=model.len());
                array.insert(pos as u64, Any::BigInt64(step)).unwrap();
                model.insert(pos, step);
            }
            let values = array
                .iter()
                .map(|v| match v {
                    Value::Any(Any::BigInt64(v)) => v,
                    v => panic!("unexpected {v:?}"),
                })
                .collect::<Vec<_>>();
            assert_eq!(values, model, "seed {seed} step {step}");
        }
    }
}

/// One random edit on `doc`: text, array and map edits on the roots and on
/// nested texts and maps, including deletes of whole nested types.
fn random_edit(doc: &Doc, rng: &mut ChaCha20Rng, step: usize) {
    let mut map = doc.get_or_create_map("map").unwrap();
    let mut text = doc.get_or_create_text("text").unwrap();
    let mut array = doc.get_or_create_array("array").unwrap();

    match rng.random_range(0..9) {
        0 => {
            let pos = rng.random_range(0..=text.len());
            text.insert(pos, format!("t{step}")).unwrap();
        }
        1 if !text.is_empty() => {
            let pos = rng.random_range(0..text.len());
            let len = rng.random_range(1..=(text.len() - pos).min(5));
            text.remove(pos, len).unwrap();
        }
        2 => {
            let pos = rng.random_range(0..=array.len());
            if rng.random_bool(0.5) {
                let nested = doc.create_text().unwrap();
                array.insert(pos, Value::from(nested.clone())).unwrap();
                let mut nested = nested;
                nested.insert(0, format!("n{step}")).unwrap();
            } else {
                array.insert(pos, Any::BigInt64(step as i64)).unwrap();
            }
        }
        3 if !array.is_empty() => {
            let pos = rng.random_range(0..array.len());
            let len = rng.random_range(1..=(array.len() - pos).min(3));
            array.remove(pos, len).unwrap();
        }
        4 => {
            let key = format!("k{}", rng.random_range(0..6));
            match rng.random_range(0..3) {
                0 => map.insert(key, Any::BigInt64(step as i64)).unwrap(),
                1 => {
                    let nested = doc.create_text().unwrap();
                    map.insert(key, Value::from(nested.clone())).unwrap();
                    let mut nested = nested;
                    nested.insert(0, format!("m{step}")).unwrap();
                }
                _ => {
                    let nested = doc.create_map().unwrap();
                    map.insert(key, Value::from(nested.clone())).unwrap();
                    let mut nested = nested;
                    nested.insert("x".into(), Any::BigInt64(step as i64)).unwrap();
                }
            }
        }
        5 => map.remove(&format!("k{}", rng.random_range(0..6))),
        6 | 7 => {
            // edit a nested text or map
            let key = format!("k{}", rng.random_range(0..6));
            match map.get(&key) {
                Some(Value::Text(mut nested)) => {
                    if nested.len() > 2 && rng.random_bool(0.4) {
                        nested.remove(1, 1).unwrap();
                    } else {
                        let pos = rng.random_range(0..=nested.len());
                        nested.insert(pos, format!("e{step}")).unwrap();
                    }
                }
                Some(Value::Map(mut nested)) => {
                    if rng.random_bool(0.4) {
                        nested.remove("x");
                    } else {
                        nested.insert("x".into(), Any::BigInt64(step as i64)).unwrap();
                    }
                }
                _ => {}
            }
        }
        _ => {
            if !array.is_empty() {
                let pos = rng.random_range(0..array.len());
                if let Some(Value::Text(mut nested)) = array.get(pos) {
                    let at = rng.random_range(0..=nested.len());
                    nested.insert(at, format!("a{step}")).unwrap();
                }
            }
        }
    }
}

fn snapshot(doc: &Doc) -> serde_json::Value {
    serde_json::json!({
        "map": serde_json::to_value(doc.get_or_create_map("map").unwrap()).unwrap(),
        "text": doc.get_or_create_text("text").unwrap().to_string(),
        "array": serde_json::to_value(doc.get_or_create_array("array").unwrap()).unwrap(),
    })
}

fn layout(doc: &Doc) -> Vec<String> {
    let store = doc.store.read().unwrap();
    let mut clients = store.items.keys().copied().collect::<Vec<_>>();
    clients.sort();
    let mut out = Vec::new();
    for client in clients {
        for node in store.items[&client].nodes(client) {
            let desc = match node.as_item() {
                Some(idx) => {
                    let item = store.type_arena.items.get(idx).unwrap();
                    format!(
                        "{} {}+{} item del={} keep={} {:?} left={:?} right={:?} ol={:?} or={:?}",
                        client,
                        item.id.clock,
                        item.len(),
                        item.deleted(),
                        item.keep(),
                        match &item.content {
                            Content::Type(_) => "Type".to_string(),
                            c => format!("{c:?}"),
                        },
                        item.left.and_then(|i| store.type_arena.items.get(i)).map(|l| l.id),
                        item.right.and_then(|i| store.type_arena.items.get(i)).map(|r| r.id),
                        item.origin_left_id(),
                        item.origin_right_id(),
                    )
                }
                None if node.is_gc() => format!("{} {}+{} GC", client, node.clock(), node.len()),
                None => format!("{} {}+{} Skip", client, node.clock(), node.len()),
            };
            out.push(desc);
        }
    }
    out
}

fn layout_diff(a: &Doc, b: &Doc) -> String {
    let (a, b) = (layout(a), layout(b));
    let mut out = String::new();
    for i in 0..a.len().max(b.len()) {
        let (x, y) = (a.get(i), b.get(i));
        if x != y {
            out.push_str(&format!("incremental: {x:?}\nfull:        {y:?}\n"));
        }
        if out.len() > 4000 {
            break;
        }
    }
    out
}

/// Three peers edit and exchange updates. One replica applies every update
/// with incremental GC; another applies the same updates without GC and runs
/// one full `Doc::gc()` at the end. Both must hold the same store, struct by
/// struct.
#[test]
#[cfg_attr(miri, ignore)]
fn incremental_gc_matches_full_gc() {
    for seed in 0..60 {
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let mut peers = (1..=3)
            .map(|client| DocOptions::new().with_client_id(client).auto_gc(false).build())
            .collect::<Vec<_>>();
        let mut incremental = DocOptions::new().with_client_id(100).build();
        let mut full = DocOptions::new().with_client_id(101).auto_gc(false).build();
        // String items only merge once their root is known to be a text
        for doc in [&incremental, &full] {
            snapshot(doc);
        }

        for step in 0..120 {
            let author = rng.random_range(0..peers.len());
            let sv = incremental.get_state_vector();
            // the author first catches up with what the others sent
            let catch_up = incremental
                .encode_state_as_update_v1(&peers[author].get_state_vector())
                .unwrap();
            peers[author].apply_update_from_binary_v1(catch_up).unwrap();
            random_edit(&peers[author], &mut rng, step);
            let update = peers[author].encode_state_as_update_v1(&sv).unwrap();

            incremental.apply_update_from_binary_v1(&update).unwrap();
            full.apply_update_from_binary_v1(&update).unwrap();
        }
        full.gc().unwrap();

        assert_eq!(snapshot(&incremental), snapshot(&full), "seed {seed}");
        assert_eq!(incremental.get_state_vector(), full.get_state_vector(), "seed {seed}");
        // the encoded delete set is derived from the structs (deleted items
        // and GC structs alike)
        assert_eq!(
            incremental.encode_update_v1().unwrap(),
            full.encode_update_v1().unwrap(),
            "seed {seed}"
        );
        assert!(
            incremental.store_compare(&full),
            "seed {seed}: store layout differs\n{}",
            layout_diff(&incremental, &full)
        );
        // and nothing was left for a later pass
        let before = incremental.encode_update_v1().unwrap();
        let before_layout = layout(&incremental);
        incremental.gc().unwrap();
        if incremental.encode_update_v1().unwrap() != before {
            let after = layout(&incremental);
            let mut diff = String::new();
            for i in 0..before_layout.len().max(after.len()) {
                if before_layout.get(i) != after.get(i) {
                    diff.push_str(&format!(
                        "before: {:?}\nafter:  {:?}\n",
                        before_layout.get(i),
                        after.get(i)
                    ));
                }
                if diff.len() > 3000 {
                    break;
                }
            }
            panic!("seed {seed}: a second full pass changed the store\n{diff}");
        }

        peers.clear();
    }
}
