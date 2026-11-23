//! Deleting a non-empty nested map records its children's clocks in the
//! (random) iteration order of the map's hash map. When that is the first
//! deletion of the client in the transaction, those ranges seed the
//! transaction's delete set, and later deletions in the same transaction are
//! merged into it with a binary search. The seed must therefore be sorted and
//! merged, or ranges get lost and undo forgets to restore them.

use std::sync::{Arc, Mutex};

use y_octo::{Any, DocOptions, Map, OrderRange, StateVector, UndoManager, UndoOptions, Update, Value};

const CLIENT: u64 = 1;

/// Key orders to insert in: forward, backward and a fixed shuffle.
fn key_orders(count: usize) -> Vec<Vec<usize>> {
    let forward = (0..count).collect::<Vec<_>>();
    let backward = forward.iter().rev().copied().collect::<Vec<_>>();
    let mut shuffled = forward.clone();
    let mut seed = 0x9e37_79b9_7f4a_7c15u64 ^ count as u64;
    for i in (1..shuffled.len()).rev() {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        shuffled.swap(i, (seed % (i as u64 + 1)) as usize);
    }
    vec![forward, backward, shuffled]
}

fn entries(map: &Map) -> Vec<(String, Value)> {
    let mut entries = map
        .iter()
        .map(|(key, value)| match value {
            Value::Map(nested) => (key, Value::Any(Any::String(format!("{:?}", entries(&nested))))),
            value => (key, value),
        })
        .collect::<Vec<_>>();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries
}

fn run(count: usize, order: &[usize]) {
    let doc = DocOptions {
        client_id: CLIENT,
        guid: "delete-set-order".into(),
        gc: true,
    }
    .build();
    let mut root = doc.get_or_create_map("root").unwrap();
    root.insert("inner".into(), doc.create_map().unwrap()).unwrap();
    let Some(Value::Map(mut inner)) = root.get("inner") else {
        panic!("inner map missing")
    };
    // interleave the nested keys with root keys, so the children's clocks
    // are not contiguous and cannot merge into one range
    for &key in order {
        inner.insert(format!("k{key}"), key as i64).unwrap();
        root.insert(format!("pad{key}"), key as i64).unwrap();
    }
    let before = entries(&root);
    assert_eq!(before.len(), count + 1);
    let clocks = doc.get_state_vector().get(&CLIENT);
    let snapshot = doc.encode_update_v1().unwrap();

    let updates = Arc::new(Mutex::new(Vec::new()));
    let sink = updates.clone();
    let _subscription = doc.subscribe(move |event| sink.lock().unwrap().push(event.update.clone()));
    let undo = UndoManager::<()>::new(&doc, [(&root).into()], UndoOptions::default()).unwrap();

    // one transaction: the nested map first (its children seed the delete
    // set of the client), then the root keys one by one
    doc.transact_mut(None, |tx| {
        let mut root = tx.map(&root)?;
        root.remove("inner");
        for &key in order.iter().rev() {
            root.remove(&format!("pad{key}"));
        }
        Ok(())
    })
    .unwrap();
    assert!(root.is_empty());

    // the commit deletes every item of the client exactly once
    let mut update = {
        let updates = updates.lock().unwrap();
        assert_eq!(updates.len(), 1);
        Update::decode_v1(&updates[0]).unwrap()
    };
    let mut known = StateVector::default();
    known.insert(CLIENT, u64::MAX);
    let deleted = update.delete_set_iter(known).collect::<Vec<_>>();
    assert!(deleted.iter().all(|(client, _)| *client == CLIENT), "{deleted:?}");
    let deleted = deleted.into_iter().map(|(_, range)| range).collect::<Vec<_>>();
    assert_eq!(deleted, vec![0..clocks], "{count} keys in order {order:?}");

    // a replica with the state before the commit applies it and ends up
    // with the same deletions
    let mut replica = DocOptions {
        client_id: CLIENT + 1,
        guid: "delete-set-order".into(),
        gc: true,
    }
    .build();
    replica.apply_update_from_binary_v1(&snapshot).unwrap();
    replica
        .apply_update_from_binary_v1(&updates.lock().unwrap()[0])
        .unwrap();
    assert!(replica.get_or_create_map("root").unwrap().is_empty());
    assert_eq!(
        replica.get_delete_sets().get(&CLIENT),
        Some(&OrderRange::from(0..clocks)),
        "{count} keys in order {order:?}"
    );

    // undo restores every field, redo removes them again
    for _ in 0..2 {
        undo.undo().unwrap().expect("deletion captured");
        assert_eq!(entries(&root), before, "{count} keys in order {order:?}");
        undo.redo().unwrap().expect("deletion redone");
        assert!(root.is_empty(), "{count} keys in order {order:?}");
    }
}

#[test]
fn nested_map_deletion_then_more_deletions_in_one_transaction() {
    // the hash map's order differs between maps, so repeat to cover many
    let repeats = if cfg!(miri) { 1 } else { 8 };
    for _ in 0..repeats {
        for count in [2, 3, 5, 8, 16, 33] {
            for order in key_orders(count) {
                run(count, &order);
            }
        }
    }
}
