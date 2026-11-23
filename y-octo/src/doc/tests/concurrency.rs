//! Readers and writers of one document on different threads. Under
//! `--cfg loom` every access to item and type data is checked for being
//! ordered by the store lock, so a reader that walks items while
//! a remote update splits, deletes, garbage-collects or merges them fails the
//! model.

use super::*;
use crate::sync::thread;
#[cfg(loom)]
use crate::sync::{Arc, Mutex};

const BEFORE: &str = "abcdef";
const AFTER: &str = "acXYdef";

/// A local document (client 1) and an update from client 2 that, when applied
/// to it, splits the local text item twice, deletes and garbage-collects a
/// character inside it, integrates two adjacent items that merge on optimize,
/// and overwrites a map key.
fn fixture() -> (Doc, Doc, Vec<u8>) {
    let local = Doc::with_client(1);
    local.get_or_create_text("text").unwrap().insert(0, BEFORE).unwrap();
    local.get_or_create_map("map").unwrap().insert("k".into(), 1).unwrap();

    let mut remote = Doc::with_client(2);
    remote
        .apply_update_from_binary_v1(local.encode_update_v1().unwrap())
        .unwrap();
    let sv = remote.get_state_vector();
    let mut text = remote.get_or_create_text("text").unwrap();
    text.insert(3, "X").unwrap();
    text.insert(4, "Y").unwrap();
    text.remove(1, 1).unwrap();
    remote.get_or_create_map("map").unwrap().insert("k".into(), 2).unwrap();
    assert_eq!(text.to_string(), AFTER);

    let update = remote.encode_state_as_update_v1(&sv).unwrap();
    (local, remote, update)
}

/// Runs `body` once, or under loom with every interleaving of up to two
/// preemptions.
fn model(body: fn()) {
    #[cfg(loom)]
    run_loom_model(body, None);
    #[cfg(not(loom))]
    body();
}

#[cfg(loom)]
fn run_loom_model(body: fn(), max_permutations: Option<usize>) {
    let mut builder = loom::model::Builder::new();
    builder.preemption_bound = Some(2);
    builder.max_permutations = max_permutations.or(builder.max_permutations);
    // Every refcount update of a shared item is a Loom atomic.
    builder.max_branches = 1 << 20;
    builder.check(move || {
        // The model body needs more than Loom's default 4 KiB stack.
        thread::Builder::new()
            .stack_size(256 << 10)
            .spawn(body)
            .unwrap()
            .join()
            .unwrap();
    });
}

#[test]
fn remote_apply_is_atomic_for_concurrent_readers() {
    model(|| {
        let (doc, remote, update) = fixture();
        let text = doc.get_or_create_text("text").unwrap();
        let map = doc.get_or_create_map("map").unwrap();

        let mut writer_doc = doc.clone();
        let writer = thread::spawn(move || writer_doc.apply_update_from_binary_v1(update).unwrap());

        let seen_text = text.to_string();
        let seen_len = text.len();
        let seen_k = map.get("k");
        writer.join().unwrap();

        // each read sees the document either before or after the whole update
        assert!(seen_text == BEFORE || seen_text == AFTER, "{seen_text}");
        assert!(seen_len == 6 || seen_len == 7, "{seen_len}");
        let k_after = seen_k == Some(Value::Any(Any::Integer(2)));
        assert!(k_after || seen_k == Some(Value::Any(Any::Integer(1))));
        // reads happen in this order: once one sees the update, the later
        // ones do too
        if seen_text == AFTER {
            assert_eq!(seen_len, 7);
        }
        if seen_len == 7 {
            assert!(k_after);
        }

        assert_eq!(text.to_string(), AFTER);
        assert_eq!(map.get("k"), Some(Value::Any(Any::Integer(2))));
        // the remote items were merged and the deleted one collected
        {
            let store = doc.store.read().unwrap();
            assert_eq!(store.items.get(&2).unwrap().len(), 2);
            assert!(matches!(
                &store.get_node((1, 1)).unwrap().item(&store.type_arena).content,
                Content::Deleted(1)
            ));
        }

        // A store drops its pointer-keyed maps in address order, which differs
        // between loom executions; skip the teardown so every execution
        // performs the same refcount updates. The handles too: with GC and
        // merge after the update, the type's refcount sees more updates than
        // loom 0.7 keeps history for, and dropping them trips its
        // `match_rmw_to_stores` assertion.
        #[cfg(loom)]
        std::mem::forget((doc, remote, text, map));
        #[cfg(not(loom))]
        drop((doc, remote, text, map));
    });
}

/// Local edits from several threads through cloned handles, interleaved with
/// remote applies and readers, converge with a peer that receives the same
/// updates.
///
/// One text is edited by index locally while remote applies change it, which
/// relies on remote applies resetting its search markers; a second text is
/// only edited locally.
#[test]
#[cfg(not(loom))]
#[cfg_attr(miri, ignore)]
fn threads_edit_apply_and_read_one_document() {
    use std::sync::Barrier;

    let doc = Doc::with_client(1);
    let text = doc.get_or_create_text("text").unwrap();
    let local_text = doc.get_or_create_text("local").unwrap();
    let map = doc.get_or_create_map("map").unwrap();
    let remote = Doc::with_client(2);
    let mut remote_text = remote.get_or_create_text("text").unwrap();
    let mut remote_updates = Vec::new();
    for i in 0..200u64 {
        let sv = remote.get_state_vector();
        remote_text.insert(0, format!("r{i}")).unwrap();
        if i % 3 == 0 {
            remote_text.remove(1, 1).unwrap();
        }
        remote_updates.push(remote.encode_state_as_update_v1(&sv).unwrap());
    }

    let barrier = std::sync::Arc::new(Barrier::new(5));
    let mut handles = Vec::new();
    for text in [text.clone(), local_text.clone()] {
        let mut text = text;
        let barrier = barrier.clone();
        handles.push(std::thread::spawn(move || {
            barrier.wait();
            for i in 0..200u64 {
                let len = text.len();
                text.insert(len / 2, format!("l{i}")).unwrap();
                if i % 4 == 0 && text.len() > 2 {
                    text.remove(1, 2).unwrap();
                }
            }
        }));
    }
    {
        let mut map = map.clone();
        let barrier = barrier.clone();
        handles.push(std::thread::spawn(move || {
            barrier.wait();
            for i in 0..200u64 {
                map.insert(format!("k{}", i % 7), i).unwrap();
                if i % 5 == 0 {
                    map.remove(&format!("k{}", i % 3));
                }
            }
        }));
    }
    {
        let mut doc = doc.clone();
        let barrier = barrier.clone();
        handles.push(std::thread::spawn(move || {
            barrier.wait();
            for update in remote_updates {
                doc.apply_update_from_binary_v1(update).unwrap();
            }
        }));
    }
    {
        let text = text.clone();
        let local_text = local_text.clone();
        let map = map.clone();
        let doc = doc.clone();
        handles.push(std::thread::spawn(move || {
            barrier.wait();
            for _ in 0..200 {
                let _ = text.to_string();
                let _ = text.to_delta();
                let _ = local_text.to_string();
                let _ = map.iter().count();
                let _ = doc.encode_update_v1().unwrap();
            }
        }));
    }
    for handle in handles {
        handle.join().unwrap();
    }

    let mut peer = Doc::with_client(3);
    peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
        .unwrap();
    assert_eq!(peer.get_or_create_text("text").unwrap().to_string(), text.to_string());
    assert_eq!(
        peer.get_or_create_text("local").unwrap().to_string(),
        local_text.to_string()
    );
    assert_eq!(peer.get_or_create_map("map").unwrap().len(), map.len());
    assert_eq!(peer.get_state_vector(), doc.get_state_vector());
}

/// `{:?}` of the public type handles prints their identity only, so it may run
/// while another thread writes the types.
#[test]
fn debug_of_type_handles_reads_no_type_data() {
    model(|| {
        let doc = Doc::with_client(1);
        let text = doc.get_or_create_text("text").unwrap();
        let array = doc.get_or_create_array("array").unwrap();
        let map = doc.get_or_create_map("map").unwrap();
        let (mut t, mut a, mut m) = (text.clone(), array.clone(), map.clone());
        let writer = thread::spawn(move || {
            t.insert(0, "x").unwrap();
            a.push(1).unwrap();
            m.insert("k".into(), 1).unwrap();
        });
        let _ = format!("{text:?} {array:?} {map:?} {:?}", Value::from(text.clone()));
        writer.join().unwrap();
    });
}

/// `{:?}` of a [StoreHistory] does not read its cached items, which another
/// thread may split or delete.
#[test]
fn debug_of_history_reads_no_items() {
    model(|| {
        let doc = Doc::with_client(1);
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abc").unwrap();
        let history = doc.history();
        let writer = thread::spawn(move || text.remove(1, 1).unwrap());
        let _ = format!("{history:?}");
        writer.join().unwrap();
    });
}

/// `push` appends at the end it sees under its own lock: a concurrent removal
/// cannot leave it inserting past the end.
#[test]
fn push_is_atomic_with_concurrent_remove() {
    model(|| {
        let doc = Doc::with_client(1);
        let mut array = doc.get_or_create_array("array").unwrap();
        array.push(1).unwrap();
        let mut other = array.clone();
        let writer = thread::spawn(move || other.remove(0, 1).unwrap());
        let pushed = array.push(2);
        writer.join().unwrap();
        assert_eq!(pushed, Ok(()));
        assert_eq!(array.iter().collect::<Vec<_>>(), vec![Value::from(2)]);
    });
}

#[test]
fn preliminary_mount_is_atomic_with_readers_and_child_edits() {
    model(|| {
        let doc = Doc::with_client(101);
        let mut root = doc.get_or_create_array("array").unwrap();
        let mut child = doc.create_array().unwrap();
        child.push(1).unwrap();
        let mut edit_child = child.clone();
        let mount = thread::spawn(move || root.push(child).unwrap());
        let edit = thread::spawn(move || edit_child.push(2).unwrap());
        // Encoding takes one document read lock. A reader sees no subtree or
        // a complete parent-before-child tree, never a partly rebuilt one.
        let update = doc.encode_update_v1().unwrap();
        mount.join().unwrap();
        edit.join().unwrap();
        let mut peer = Doc::with_client(202);
        peer.apply_update_from_binary_v1(update).unwrap();
        let seen = serde_json::to_value(peer.get_or_create_array("array").unwrap()).unwrap();
        assert!(
            seen == serde_json::json!([]) || seen == serde_json::json!([[1]]) || seen == serde_json::json!([[1, 2]])
        );
        assert!(!peer.has_pending_updates());
        peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
            .unwrap();
        assert_eq!(
            serde_json::to_value(peer.get_or_create_array("array").unwrap()).unwrap(),
            serde_json::json!([[1, 2]])
        );
        assert_eq!(peer.get_state_vector(), doc.get_state_vector());
    });
}

#[cfg(loom)]
#[test]
fn concurrent_and_reentrant_commits_deliver_in_sequence() {
    run_loom_model(
        || {
            let doc = Doc::with_client(1);
            let text = doc.get_or_create_text("text").unwrap();
            let seen = Arc::new(Mutex::new(Vec::new()));
            let sink = seen.clone();
            let callback_text = text.clone();
            let _subscription = doc.subscribe(move |event| {
                sink.lock().unwrap().push(event.seq);
                if event.seq == 1 {
                    callback_text.clone().insert(0, "r").unwrap();
                }
            });
            let writers = (0..2)
                .map(|_| {
                    let mut text = text.clone();
                    thread::spawn(move || text.insert(0, "a").unwrap())
                })
                .collect::<Vec<_>>();
            for writer in writers {
                writer.join().unwrap();
            }
            assert_eq!(*seen.lock().unwrap(), vec![1, 2, 3]);
            assert_eq!(text.len(), 3);
        },
        Some(3000),
    );
}

#[cfg(loom)]
#[test]
fn nested_commit_delivery_waits_for_outer_read_lock() {
    run_loom_model(
        || {
            let outer = Doc::with_client(1);
            let inner = Doc::with_client(2);
            let mut text = inner.get_or_create_text("text").unwrap();
            let seen = Arc::new(Mutex::new(Vec::new()));
            let sink = seen.clone();
            let callback_outer = outer.clone();
            let _subscription = inner.subscribe(move |event| {
                callback_outer.transact(|_| ()).unwrap();
                sink.lock().unwrap().push(event.seq);
            });
            outer
                .transact(|_| {
                    text.insert(0, "a").unwrap();
                    let mut other = text.clone();
                    thread::spawn(move || other.insert(0, "b").unwrap()).join().unwrap();
                    assert!(seen.lock().unwrap().is_empty());
                })
                .unwrap();
            assert_eq!(*seen.lock().unwrap(), vec![1, 2]);
        },
        Some(3000),
    );
}

#[cfg(loom)]
fn ordered_documents<const N: usize>() -> [Doc; N] {
    let mut docs = std::array::from_fn(|_| Doc::with_client(1));
    docs.sort_by_key(|doc| Arc::as_ptr(&doc.store).addr());
    docs
}

#[cfg(loom)]
#[test]
fn ordered_store_comparison_waits_for_concurrent_writer() {
    run_loom_model(
        || {
            let [low, high] = ordered_documents();
            let low_text = low.get_or_create_text("text").unwrap();
            low_text.clone().insert(0, "ready").unwrap();
            let high_text = high.get_or_create_text("text").unwrap();
            let (locked, wait_until_locked) = loom::sync::mpsc::channel();
            let writer_doc = high.clone();
            let writer = thread::spawn(move || {
                writer_doc
                    .transact_mut(None, |tx| {
                        locked.send(()).unwrap();
                        thread::yield_now();
                        tx.text(&high_text)?.insert(0, "ready")
                    })
                    .unwrap();
            });
            wait_until_locked.recv().unwrap();
            assert!(high.store_compare(&low));
            writer.join().unwrap();
        },
        Some(3000),
    );
}

#[cfg(loom)]
#[test]
fn mixed_order_nesting_checks_every_held_document() {
    run_loom_model(
        || {
            let [low, middle, high] = ordered_documents();
            let (locked, wait_until_locked) = loom::sync::mpsc::channel();
            let (checked, wait_until_checked) = loom::sync::mpsc::channel();
            let writer_doc = middle.clone();
            let writer = thread::spawn(move || {
                writer_doc
                    .transact_mut(None, |_| {
                        locked.send(()).unwrap();
                        wait_until_checked.recv().unwrap();
                        Ok(())
                    })
                    .unwrap();
            });
            wait_until_locked.recv().unwrap();
            high.transact(|_| {
                low.transact(|_| {
                    // The most recent lock is below middle, but high is
                    // still held. A request for middle must return promptly.
                    assert_eq!(middle.transact(|_| ()), Err(JwstCodecError::NestedDocumentBusy));
                    assert_eq!(
                        middle.transact_mut(None, |_| Ok(())),
                        Err(JwstCodecError::NestedDocumentBusy)
                    );
                    assert_eq!(high.transact(|_| ()), Err(JwstCodecError::Reentrant));
                })
                .unwrap();
            })
            .unwrap();
            checked.send(()).unwrap();
            writer.join().unwrap();
        },
        Some(3000),
    );
}

#[cfg(loom)]
#[test]
fn contended_nested_read_does_not_wait_across_a_thread_join() {
    run_loom_model(
        || {
            let [low, high] = ordered_documents();
            let (low_locked, wait_for_low) = loom::sync::mpsc::channel();
            let (high_locked, wait_for_high) = loom::sync::mpsc::channel();
            let first_low = low.clone();
            let first_high = high.clone();
            let first = thread::spawn(move || {
                first_low
                    .transact_mut(None, |_| {
                        low_locked.send(()).unwrap();
                        wait_for_high.recv().unwrap();
                        // Ascending document order cannot account for the
                        // other transaction's wait on its child thread.
                        assert_eq!(first_high.transact(|_| ()), Err(JwstCodecError::NestedDocumentBusy));
                        Ok(())
                    })
                    .unwrap();
            });
            high.transact_mut(None, |_| {
                high_locked.send(()).unwrap();
                wait_for_low.recv().unwrap();
                thread::spawn(move || low.transact(|_| ()).unwrap()).join().unwrap();
                Ok(())
            })
            .unwrap();
            first.join().unwrap();
        },
        Some(3000),
    );
}
