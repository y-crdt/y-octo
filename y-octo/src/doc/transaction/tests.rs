//! Transactions, the commit pipeline and commit events.

// ID ranges are compared as lists of ranges
#![allow(clippy::single_range_in_vec_init)]

use std::sync::{Arc, Mutex};

use super::*;

/// Records every delivered event.
fn record(doc: &Doc) -> (Subscription, Arc<Mutex<Vec<CommitEvent>>>) {
    let events = Arc::new(Mutex::new(Vec::new()));
    let sink = events.clone();
    let subscription = doc.subscribe(move |event| sink.lock().unwrap().push(event.clone()));
    (subscription, events)
}

fn take(events: &Mutex<Vec<CommitEvent>>) -> Vec<CommitEvent> {
    std::mem::take(&mut *events.lock().unwrap())
}

fn identities(event: &CommitEvent) -> Vec<TypeIdentity> {
    event.changed.iter().map(|changed| changed.identity.clone()).collect()
}

/// Delete sets compared by their ranges, not their representation.
fn ranges(ds: &DeleteSet) -> Vec<(u64, Vec<std::ops::Range<u64>>)> {
    let mut out = ds
        .iter()
        .map(|(client, ranges)| (*client, ranges.into_iter().collect::<Vec<_>>()))
        .collect::<Vec<_>>();
    out.sort_by_key(|(client, _)| *client);
    out
}

fn root(name: &str) -> TypeIdentity {
    TypeIdentity::Root(name.into())
}

/// Replays event updates into a fresh document.
fn replay(events: &[CommitEvent]) -> Doc {
    let mut doc = Doc::with_client(99);
    for event in events {
        doc.apply_update_from_binary_v1(&event.update).unwrap();
    }
    doc
}

#[test]
fn one_event_per_transaction_across_types() {
    let doc = Doc::with_client(1);
    let text = doc.get_or_create_text("text").unwrap();
    let map = doc.get_or_create_map("map").unwrap();
    let array = doc.get_or_create_array("array").unwrap();
    let (_sub, events) = record(&doc);

    doc.transact_mut(Origin::new("editor"), |tx| {
        tx.text(&text)?.insert(0, "hello")?;
        tx.map(&map)?.insert("title".into(), "doc")?;
        tx.map(&map)?.insert("count".into(), 1)?;
        tx.array(&array)?.push(true)?;
        // reads inside the transaction see its own writes
        assert_eq!(tx.text(&text)?.read().to_string(), "hello");
        assert_eq!(tx.map(&map)?.get("title"), Some(Value::Any(Any::String("doc".into()))));
        Ok(())
    })
    .unwrap();

    let events = take(&events);
    assert_eq!(events.len(), 1);
    let event = &events[0];
    assert_eq!(event.seq, 1);
    assert_eq!(event.origin, Some(Origin::new("editor")));
    assert!(event.local);
    let mut changed = identities(event);
    changed.sort_by_key(|identity| format!("{identity:?}"));
    assert_eq!(changed, vec![root("array"), root("map"), root("text")]);
    let map_change = event.changed.iter().find(|c| c.identity == root("map")).unwrap();
    assert_eq!(map_change.keys, vec!["count".to_string(), "title".to_string()]);
    assert_eq!(ranges(&event.inserted), vec![(1, vec![0..8])]);
    assert!(event.deleted.is_empty());

    assert_eq!(replay(&events).get_or_create_text("text").unwrap().to_string(), "hello");
}

#[test]
fn transactions_publish_preliminary_edits_only_at_mount() {
    let doc = Doc::with_client(1);
    let array = doc.get_or_create_array("array").unwrap();
    let map = doc.create_map().unwrap();
    let text = doc.create_text().unwrap();
    let (_subscription, events) = record(&doc);
    let before = doc.get_state_vector();
    let update = doc.encode_update_v1().unwrap();

    doc.transact_mut(None, |tx| {
        tx.text(&text)?.insert(0, "draft")?;
        tx.map(&map)?.insert("text".into(), text.clone())?;
        tx.text(&text)?.remove(0, 5)?;
        tx.text(&text)?.insert(0, "published")?;
        assert_eq!(tx.text(&text)?.read().to_string(), "published");
        assert_eq!(tx.state_vector(), before);
        Ok(())
    })
    .unwrap();
    assert_eq!(map.id(), None);
    assert_eq!(doc.encode_update_v1().unwrap(), update);
    assert!(take(&events).is_empty());

    doc.transact_mut(None, |tx| tx.array(&array)?.push(map.clone()))
        .unwrap();
    let mut published = take(&events);
    assert_eq!(published.len(), 1);
    assert_eq!(published[0].seq, 1);
    assert_eq!(published[0].before_state, before);
    assert!(published[0].deleted.is_empty());
    assert_eq!(identities(&published[0]), vec![root("array")]);
    let peer = replay(&published);
    let peer_array = peer.get_or_create_array("array").unwrap();
    let Some(Value::Map(peer_map)) = peer_array.get(0) else {
        panic!("mounted map missing on peer");
    };
    let Some(Value::Text(peer_text)) = peer_map.get("text") else {
        panic!("mounted text missing on peer");
    };
    assert_eq!(peer_text.to_string(), "published");
    assert_eq!(peer.get_state_vector(), doc.get_state_vector());

    doc.transact_mut(None, |tx| tx.array(&array)?.remove(0, 1)).unwrap();
    doc.gc().unwrap();
    published = take(&events);
    assert_eq!(published.len(), 1);
    let update = doc.encode_update_v1().unwrap();
    assert_eq!(
        doc.transact_mut(None, |tx| tx.text(&text)?.insert(0, "late")),
        Err(JwstCodecError::InvalidParent)
    );
    map.clone().remove("text");
    assert_eq!(
        doc.transact_mut(None, |tx| tx.array(&array)?.push(map)),
        Err(JwstCodecError::TypeAlreadyInserted)
    );
    assert!(take(&events).is_empty());
    assert_eq!(doc.encode_update_v1().unwrap(), update);
}

#[test]
fn delete_only_format_only_and_nested_changes_have_events() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let mut map = doc.get_or_create_map("map").unwrap();
    text.insert(0, "hello world").unwrap();
    let nested = doc.create_text().unwrap();
    map.insert("nested".into(), Value::from(nested.clone())).unwrap();
    let mut nested = nested;
    nested.insert(0, "inner").unwrap();
    let mut follower = Doc::with_client(2);
    follower
        .apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
        .unwrap();
    let (_sub, events) = record(&doc);

    // delete only
    text.remove(5, 6).unwrap();
    // format only
    text.apply_delta(&[TextDeltaOp::Retain {
        retain: 5,
        format: Some(TextAttributes::from([("bold".to_string(), Any::True)])),
    }])
    .unwrap();
    // nested
    nested.insert(5, "!").unwrap();

    let events = take(&events);
    assert_eq!(events.iter().map(|e| e.seq).collect::<Vec<_>>(), vec![4, 5, 6]);

    let delete = &events[0];
    assert!(delete.inserted.is_empty());
    assert_eq!(ranges(&delete.deleted), vec![(1, vec![5..11])]);
    assert_eq!(identities(delete), vec![root("text")]);

    let format = &events[1];
    assert!(!format.inserted.is_empty());
    assert_eq!(identities(format), vec![root("text")]);
    assert_eq!(
        doc.get_or_create_text("text").unwrap().to_delta(),
        vec![TextDeltaOp::Insert {
            insert: TextInsert::Text("hello".into()),
            format: Some(TextAttributes::from([("bold".to_string(), Any::True)])),
        }]
    );

    let nested_change = &events[2];
    assert_eq!(identities(nested_change), vec![nested.identity().unwrap()]);
    assert_eq!(nested_change.ancestors, vec![root("map")]);

    // the three updates replay onto a copy taken before them
    for event in &events {
        follower.apply_update_from_binary_v1(&event.update).unwrap();
    }
    assert_eq!(
        follower.get_or_create_text("text").unwrap().to_delta(),
        doc.get_or_create_text("text").unwrap().to_delta()
    );
    assert!(follower.store_compare(&doc) || follower.encode_update_v1() == doc.encode_update_v1());
}

#[test]
fn implicit_writes_cloned_handles_and_remote_applies_commit() {
    let doc = Doc::with_client(1);
    let (_sub, events) = record(&doc);

    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "a").unwrap();
    let mut clone = text.clone();
    clone.insert(1, "b").unwrap();

    let remote = Doc::with_client(2);
    remote.get_or_create_map("map").unwrap().insert("k".into(), 1).unwrap();
    let update = Update::decode_v1(remote.encode_update_v1().unwrap()).unwrap();
    doc.apply_update_with_origin(update, Origin::new("sync")).unwrap();

    let events = take(&events);
    assert_eq!(events.len(), 3);
    assert!(events[0].local && events[1].local);
    assert_eq!(identities(&events[1]), vec![root("text")]);
    let remote_event = &events[2];
    assert!(!remote_event.local);
    assert_eq!(remote_event.origin, Some(Origin::new("sync")));
    assert_eq!(identities(remote_event), vec![root("map")]);
    assert_eq!(
        remote_event
            .incoming
            .as_ref()
            .map(|incoming| (ranges(&incoming.structs), ranges(&incoming.delete_set))),
        Some(IncomingUpdate {
            structs: DeleteSet::from([(2, vec![0..1])]),
            delete_set: DeleteSet::default(),
        })
        .map(|incoming| (ranges(&incoming.structs), ranges(&incoming.delete_set)))
    );
}

#[test]
fn incoming_commit_ranges_leave_pending_clock_gaps() {
    let source = Doc::with_client(1);
    let mut text = source.get_or_create_text("text").unwrap();
    text.insert(0, "a").unwrap();
    let first = source.encode_update_v1().unwrap();
    text.insert(1, "b").unwrap();
    let prefix = source.get_state_vector();
    text.insert(2, "c").unwrap();
    let third = source.encode_state_as_update_v1(&prefix).unwrap();

    let receiver = Doc::with_client(2);
    let (_sub, events) = record(&receiver);
    receiver
        .apply_update_with_origin(merge_updates_v1([first, third]).unwrap(), None)
        .unwrap();

    let events = take(&events);
    assert_eq!(events.len(), 1);
    assert_eq!(
        ranges(&events[0].incoming.as_ref().unwrap().structs),
        vec![(1, vec![0..1, 2..3])]
    );
    assert_eq!(ranges(&events[0].inserted), vec![(1, vec![0..1])]);
    assert!(receiver.has_pending_updates());
}

#[test]
fn update_bytes_hold_only_the_transaction() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    // a long history with many deletions
    for i in 0..if cfg!(miri) { 40 } else { 200 } {
        text.insert(0, format!("{i},")).unwrap();
        if i % 2 == 0 {
            text.remove(1, 2).unwrap();
        }
    }
    let history = doc.encode_update_v1().unwrap();
    let mut follower = Doc::with_client(2);
    follower.apply_update_from_binary_v1(&history).unwrap();

    let (_sub, events) = record(&doc);
    text.remove(0, 1).unwrap();
    text.insert(3, "x").unwrap();

    let events = take(&events);
    assert_eq!(events.len(), 2);
    for event in &events {
        let update = Update::decode_v1(&event.update).unwrap();
        // the deletion of one char, not the whole history's delete set
        assert_eq!(ranges(&update.delete_set), ranges(&event.deleted));
        let structs = update.structs.values().map(|nodes| nodes.len()).sum::<usize>();
        assert!(structs <= 1, "{structs} structs");
        assert!(event.update.len() < 32);
    }
    assert!(events[0].deleted.get(&1).is_some());
    assert!(events[1].deleted.is_empty());

    // replaying the events onto the follower matches the source
    for event in &events {
        follower.apply_update_from_binary_v1(&event.update).unwrap();
    }
    assert_eq!(
        follower.get_or_create_text("text").unwrap().to_string(),
        text.to_string()
    );
}

#[test]
fn applying_an_update_twice_commits_once() {
    let source = Doc::with_client(2);
    source.get_or_create_text("text").unwrap().insert(0, "abc").unwrap();
    let update = source.encode_update_v1().unwrap();

    let mut doc = Doc::with_client(1);
    let (_sub, events) = record(&doc);
    doc.apply_update_from_binary_v1(&update).unwrap();
    doc.apply_update_from_binary_v1(&update).unwrap();
    assert_eq!(take(&events).len(), 1);
}

#[test]
fn commits_without_subscribers_still_count() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "a").unwrap();
    let (subscription, events) = record(&doc);
    text.insert(1, "b").unwrap();
    subscription.unsubscribe();
    text.insert(2, "c").unwrap();
    let (_subscription, later) = record(&doc);
    text.insert(3, "d").unwrap();
    assert_eq!(take(&events).iter().map(|e| e.seq).collect::<Vec<_>>(), vec![2]);
    assert_eq!(take(&later).iter().map(|e| e.seq).collect::<Vec<_>>(), vec![4]);
}

#[test]
fn callbacks_read_unsubscribe_and_edit() {
    let doc = Doc::with_client(1);
    let text = doc.get_or_create_text("text").unwrap();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let subscription = Arc::new(Mutex::new(None::<Subscription>));

    {
        let doc2 = doc.clone();
        let text2 = text.clone();
        let seen = seen.clone();
        let subscription_slot = subscription.clone();
        let sub = doc.subscribe(move |event| {
            // reading inside the callback
            seen.lock().unwrap().push((event.seq, text2.to_string()));
            if event.seq == 1 {
                // a commit from inside the callback is delivered after it
                doc2.get_or_create_text("text").unwrap().insert(0, ">").unwrap();
                assert_eq!(seen.lock().unwrap().len(), 1);
            } else {
                // unsubscribing from inside the callback
                subscription_slot.lock().unwrap().take();
            }
        });
        *subscription.lock().unwrap() = Some(sub);
    }

    let mut text = text;
    text.insert(0, "a").unwrap();
    assert_eq!(*seen.lock().unwrap(), vec![(1, "a".to_string()), (2, ">a".to_string())]);
    assert!(subscription.lock().unwrap().is_none());

    text.insert(0, "b").unwrap();
    assert_eq!(seen.lock().unwrap().len(), 2);
}

#[test]
fn callback_panic_drains_reentrant_commits_before_unwinding() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    let callback_text = text.clone();
    let _first = doc.subscribe(move |event| {
        if event.seq == 1 {
            callback_text.clone().insert(1, "b").unwrap();
            panic!("first callback panicked");
        }
    });
    let _second = doc.subscribe(|event| {
        if event.seq == 2 {
            panic!("second callback panicked");
        }
    });
    let (_recording, events) = record(&doc);

    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| text.insert(0, "a")))
        .expect_err("the first callback panic should propagate after delivery");
    assert_eq!(panic.downcast_ref::<&str>(), Some(&"first callback panicked"));
    let events = take(&events);
    assert_eq!(events.iter().map(|e| e.seq).collect::<Vec<_>>(), vec![1, 2]);
    assert_eq!(text.to_string(), "ab");
    assert_eq!(replay(&events).get_or_create_text("text").unwrap().to_string(), "ab");
}

#[test]
fn nested_commits_keep_subscriptions_from_enqueue_and_drop_callbacks_unlocked() {
    struct DropProbe(Doc, Doc, Arc<Mutex<Vec<u64>>>);

    impl Drop for DropProbe {
        fn drop(&mut self) {
            assert_eq!(self.0.client(), 1);
            let _temporary = self.1.subscribe(|_| {});
            self.2.lock().unwrap().push(3);
        }
    }

    let outer = Doc::with_client(1);
    let inner = Doc::with_client(2);
    let mut text = inner.get_or_create_text("text").unwrap();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let probe = DropProbe(outer.clone(), inner.clone(), seen.clone());
    let early = inner.subscribe(move |event| {
        assert_eq!(probe.0.client(), 1);
        probe.2.lock().unwrap().push(event.seq);
    });

    let _late = outer
        .transact(|_| {
            text.insert(0, "a").unwrap();
            early.unsubscribe();
            let seen_for_late = seen.clone();
            let late = inner.subscribe(move |event| seen_for_late.lock().unwrap().push(event.seq));
            // A different thread cannot deliver the commit at the head of
            // this queue before the first writer releases its outer lock.
            let mut other = text.clone();
            std::thread::spawn(move || other.insert(1, "b").unwrap())
                .join()
                .unwrap();
            assert!(seen.lock().unwrap().is_empty());
            late
        })
        .unwrap();
    assert_eq!(*seen.lock().unwrap(), vec![1, 2, 3]);
    assert_eq!(text.to_string(), "ab");
}

#[test]
fn nested_documents_report_contention_in_both_lock_orders() {
    let first = Doc::with_client(1);
    let second = Doc::with_client(2);
    let barrier = std::sync::Barrier::new(2);
    std::thread::scope(|scope| {
        for (held, other) in [(&first, &second), (&second, &first)] {
            let barrier = &barrier;
            scope.spawn(move || {
                held.transact_mut(None, |_| {
                    barrier.wait();
                    let read = other.transact(|_| ());
                    let write = other.transact_mut(None, |_| Ok(()));
                    barrier.wait();
                    assert_eq!(read, Err(JwstCodecError::NestedDocumentBusy));
                    assert_eq!(write, Err(JwstCodecError::NestedDocumentBusy));
                    Ok(())
                })
                .unwrap();
            });
        }
    });
    assert_eq!(first.client(), 1);
    assert_eq!(second.client(), 2);
}

#[test]
fn nested_commit_is_delivered_after_outer_transaction_panics() {
    let outer = Doc::with_client(1);
    let inner = Doc::with_client(2);
    let mut text = inner.get_or_create_text("text").unwrap();
    let (_subscription, events) = record(&inner);

    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        outer.transact_mut(None, |_| -> JwstCodecResult {
            text.insert(0, "committed")?;
            assert!(events.lock().unwrap().is_empty());
            panic!("outer transaction panicked");
        })
    }))
    .expect_err("the outer panic should propagate");
    assert_eq!(panic.downcast_ref::<&str>(), Some(&"outer transaction panicked"));
    assert_eq!(outer.transact(|_| ()), Err(JwstCodecError::DocPoisoned));
    let events = take(&events);
    assert_eq!(events.len(), 1);
    assert_eq!(
        replay(&events).get_or_create_text("text").unwrap().to_string(),
        "committed"
    );
}

#[test]
fn empty_text_inserts_validate_index_without_committing() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    text.insert(0, "abc").unwrap();
    let (_subscription, events) = record(&doc);
    let sv = doc.get_state_vector();
    let update = doc.encode_update_v1().unwrap();

    text.insert(1, "").unwrap();
    text.insert(3, "").unwrap();
    assert_eq!(text.insert(4, ""), Err(JwstCodecError::IndexOutOfBound(4)));
    doc.transact_mut(None, |tx| tx.text(&text)?.insert(2, "")).unwrap();
    assert_eq!(
        doc.transact_mut(None, |tx| tx.text(&text)?.insert(4, "")),
        Err(JwstCodecError::IndexOutOfBound(4))
    );
    assert_eq!(text.to_string(), "abc");
    assert_eq!(doc.get_state_vector(), sv);
    assert_eq!(doc.encode_update_v1().unwrap(), update);
    assert!(take(&events).is_empty());
}

#[test]
fn concurrent_commits_are_delivered_in_commit_order() {
    const COMMITS: usize = if cfg!(miri) { 10 } else { 100 };
    let doc = Doc::with_client(1);
    let (_sub, events) = record(&doc);

    let handles = (0..4)
        .map(|i| {
            let doc = doc.clone();
            std::thread::spawn(move || {
                let text = doc.get_or_create_text("text").unwrap();
                let map = doc.get_or_create_map("map").unwrap();
                for j in 0..COMMITS {
                    doc.transact_mut(None, |tx| {
                        tx.text(&text)?.insert(0, format!("{i}"))?;
                        tx.map(&map)?.insert(format!("{i}"), j as i64)
                    })
                    .unwrap();
                }
            })
        })
        .collect::<Vec<_>>();
    for handle in handles {
        handle.join().unwrap();
    }

    let events = take(&events);
    assert_eq!(events.len(), 4 * COMMITS);
    for (i, pair) in events.windows(2).enumerate() {
        assert_eq!(pair[0].seq + 1, pair[1].seq, "at {i}");
        // the store's commit order: each commit starts where the previous ended
        assert_eq!(pair[0].after_state, pair[1].before_state, "at {i}");
    }
    assert_eq!(
        replay(&events).get_or_create_text("text").unwrap().to_string(),
        doc.get_or_create_text("text").unwrap().to_string()
    );
}

#[test]
fn reentrant_calls_fail_instead_of_deadlocking() {
    let doc = Doc::with_client(1);
    let mut text = doc.get_or_create_text("text").unwrap();
    doc.get_or_create_map("map").unwrap();
    text.insert(0, "a").unwrap();
    let position = text.relative_position(0, 0).unwrap();

    let result = doc.transact_mut(None, |tx| {
        tx.text(&text)?.insert(1, "b")?;
        // a write through the handle instead of the transaction
        assert_eq!(text.clone().insert(0, "x"), Err(JwstCodecError::Reentrant));
        assert!(matches!(doc.transact(|_| ()), Err(JwstCodecError::Reentrant)));
        assert!(matches!(doc.encode_update_v1(), Err(JwstCodecError::Reentrant)));
        assert!(matches!(doc.get_map("map"), Err(JwstCodecError::Reentrant)));
        assert!(matches!(doc.get_or_create_text("text"), Err(JwstCodecError::Reentrant)));
        Ok(())
    });
    assert_eq!(result, Ok(()));

    let result = doc.transact(|tx| {
        assert!(matches!(
            doc.transact_mut(None, |_| Ok(())),
            Err(JwstCodecError::Reentrant)
        ));
        tx.text(&text).unwrap().to_string()
    });
    assert_eq!(result, Ok("ab".to_string()));

    // a read without an error in its signature stops with the reason
    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = doc.transact(|_| text.len());
    }));
    assert!(panicked.is_err());
    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = doc.transact(|_| doc.resolve_relative_position(&position, false));
    }));
    assert!(panicked.is_err());
    // and the document is still usable
    assert_eq!(text.to_string(), "ab");
}

#[test]
fn a_failed_transaction_keeps_and_commits_its_changes() {
    let doc = Doc::with_client(1);
    let text = doc.get_or_create_text("text").unwrap();
    let (_sub, events) = record(&doc);

    let result = doc.transact_mut(None, |tx| {
        tx.text(&text)?.insert(0, "kept")?;
        tx.text(&text)?.insert(100, "out of bounds")
    });
    assert_eq!(result, Err(JwstCodecError::IndexOutOfBound(100)));
    assert_eq!(text.to_string(), "kept");
    let events = take(&events);
    assert_eq!(events.len(), 1);
    assert_eq!(replay(&events).get_or_create_text("text").unwrap().to_string(), "kept");
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_panic_inside_a_transaction_poisons_the_document() {
    let doc = Doc::with_client(1);
    let text = doc.get_or_create_text("text").unwrap();
    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = doc.transact_mut(None, |tx| -> JwstCodecResult {
            tx.text(&text)?.insert(0, "half")?;
            panic!("caller bug");
        });
    }));
    assert!(panicked.is_err());
    assert_eq!(text.clone().insert(0, "x"), Err(JwstCodecError::DocPoisoned));
    assert!(matches!(doc.encode_update_v1(), Err(JwstCodecError::DocPoisoned)));
}

/// Without the `random` feature the document waits for the host instead
/// (`client_identity_tests`).
#[test]
#[cfg(feature = "random")]
fn remote_use_of_our_client_id_switches_it() {
    let mut doc = Doc::with_client(7);
    // another replica writing as client 7
    let other = Doc::with_client(7);
    other.get_or_create_text("text").unwrap().insert(0, "b").unwrap();
    doc.apply_update_from_binary_v1(other.encode_update_v1().unwrap())
        .unwrap();

    assert_ne!(doc.client(), 7);
    // our next edit no longer collides with theirs
    doc.get_or_create_text("text").unwrap().insert(0, "c").unwrap();
    assert_eq!(doc.get_state_vector().get(&7), 1);
}

#[test]
fn read_transaction_iterates_without_copies() {
    let doc = Doc::with_client(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    let mut array = doc.get_or_create_array("array").unwrap();
    map.insert("a".into(), 1).unwrap();
    map.insert("b".into(), 2).unwrap();
    array.push(1).unwrap();
    array.push("two").unwrap();

    doc.transact(|tx| {
        let map = tx.map(&map).unwrap();
        let mut keys = map.keys().collect::<Vec<_>>();
        keys.sort();
        assert_eq!(keys, vec!["a", "b"]);
        let array = tx.array(&array).unwrap();
        assert_eq!(
            array.iter().collect::<Vec<_>>(),
            vec![Value::Any(Any::Integer(1)), Value::Any(Any::String("two".into()))]
        );
    })
    .unwrap();
}

#[test]
fn foreign_handles_are_rejected() {
    let doc = Doc::with_client(1);
    let other = Doc::with_client(2);
    let text = other.get_or_create_text("text").unwrap();
    assert!(matches!(
        doc.transact(|tx| tx.text(&text).map(|_| ())),
        Ok(Err(JwstCodecError::ForeignType))
    ));
}

fn subdoc(guid: &str) -> Value {
    Value::from(DocOptions::new().with_guid(guid.into()).build())
}

fn guids(set: &std::collections::BTreeSet<String>) -> Vec<&str> {
    set.iter().map(String::as_str).collect()
}

/// (added, removed) of each event.
fn subdoc_changes(events: &[CommitEvent]) -> Vec<(Vec<&str>, Vec<&str>)> {
    events
        .iter()
        .map(|event| (guids(&event.subdocs_added), guids(&event.subdocs_removed)))
        .collect()
}

#[test]
fn subdocs_added_and_removed() {
    let doc = Doc::with_client(1);
    let mut map = doc.get_or_create_map("map").unwrap();
    let mut array = doc.get_or_create_array("array").unwrap();
    let (_sub, events) = record(&doc);

    // set, overwritten, deleted
    map.insert("sub".into(), subdoc("a")).unwrap();
    map.insert("sub".into(), subdoc("b")).unwrap();
    map.remove("sub");
    // removed from an array
    array.insert(0, subdoc("c")).unwrap();
    array.remove(0, 1).unwrap();
    // deleted with the type holding it
    let mut nested = doc.create_map().unwrap();
    map.insert("nested".into(), Value::from(nested.clone())).unwrap();
    nested.insert("sub".into(), subdoc("d")).unwrap();
    map.remove("nested");
    // added and deleted by one transaction: neither
    doc.transact_mut(None, |tx| {
        let mut map = tx.map(&map)?;
        map.insert("sub".into(), subdoc("e"))?;
        map.remove("sub");
        Ok(())
    })
    .unwrap();
    // a plain edit has no subdocument changes
    map.insert("plain".into(), 1).unwrap();

    let none = Vec::<&str>::new;
    let events = take(&events);
    assert_eq!(
        subdoc_changes(&events),
        vec![
            (vec!["a"], none()),
            (vec!["b"], vec!["a"]),
            (none(), vec!["b"]),
            (vec!["c"], none()),
            (none(), vec!["c"]),
            (none(), none()),
            (vec!["d"], none()),
            (none(), vec!["d"]),
            (none(), none()),
            (none(), none()),
        ]
    );
}

#[test]
fn remote_updates_carry_subdoc_changes() {
    let source = Doc::with_client(1);
    let mut map = source.get_or_create_map("map").unwrap();
    let (_source_sub, source_events) = record(&source);
    map.insert("sub".into(), subdoc("a")).unwrap();
    map.insert("sub".into(), subdoc("b")).unwrap();
    map.remove("sub");
    let updates = take(&source_events)
        .into_iter()
        .map(|event| event.update)
        .collect::<Vec<_>>();

    let mut follower = Doc::with_client(2);
    let (_sub, events) = record(&follower);
    for update in &updates {
        follower.apply_update_from_binary_v1(update).unwrap();
    }
    let none = Vec::<&str>::new;
    let remote = take(&events);
    assert!(remote.iter().all(|event| !event.local));
    assert_eq!(
        subdoc_changes(&remote),
        vec![(vec!["a"], none()), (vec!["b"], vec!["a"]), (none(), vec!["b"])]
    );

    // the whole history at once: added and deleted by one transaction
    let mut late = Doc::with_client(3);
    let (_late_sub, late_events) = record(&late);
    late.apply_update_from_binary_v1(source.encode_update_v1().unwrap())
        .unwrap();
    assert_eq!(subdoc_changes(&take(&late_events)), vec![(none(), none())]);
}

#[test]
fn subtree_subscriptions_follow_nested_changes() {
    let doc = Doc::with_client(1);
    let mut root_map = doc.get_or_create_map("root").unwrap();
    let mut other = doc.get_or_create_map("other").unwrap();
    let a = doc.create_map().unwrap();
    root_map.insert("a".into(), Value::from(a.clone())).unwrap();
    let b = doc.create_map().unwrap();
    root_map.insert("b".into(), Value::from(b.clone())).unwrap();
    let mut a = a;
    let deep = doc.create_map().unwrap();
    a.insert("deep".into(), Value::from(deep.clone())).unwrap();
    let mut deep = deep;
    let text = doc.create_text().unwrap();
    deep.insert("text".into(), Value::from(text.clone())).unwrap();
    let mut text = text;
    let mut b = b;

    let count = |identity: TypeIdentity| {
        let seen = Arc::new(Mutex::new(Vec::new()));
        let sink = seen.clone();
        let sub = doc.subscribe_subtree(identity, move |event| sink.lock().unwrap().push(event.seq));
        (sub, seen)
    };
    let (_a_sub, a_seen) = count(a.identity().unwrap());
    let (_root_sub, root_seen) = count(root("root"));
    let (_text_sub, text_seen) = count(text.identity().unwrap());

    text.insert(0, "deep").unwrap(); // in a, in root, the text itself
    b.insert("x".into(), 1).unwrap(); // sibling subtree of a
    root_map.insert("y".into(), 1).unwrap(); // root itself, not below a
    other.insert("z".into(), 1).unwrap(); // another root type
    a.insert("w".into(), 1).unwrap(); // a itself

    let seen = |seen: &Mutex<Vec<u64>>| seen.lock().unwrap().clone();
    let first = seen(&root_seen)[0];
    assert_eq!(seen(&a_seen), vec![first, first + 4]);
    assert_eq!(seen(&root_seen), vec![first, first + 1, first + 2, first + 4]);
    assert_eq!(seen(&text_seen), vec![first]);
}
