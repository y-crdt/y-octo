//! Ranges garbage collection must keep.
//!
//! Yjs marks each item an undo stack still needs with `Item.keep`, together
//! with the type items above it (`keepItem`), and clears the flag when a stack
//! is cleared. Here the history layer owns one set of id ranges,
//! [DocStore::retained]: GC skips every struct overlapping it, and replacing
//! the set collects what was released. The owner computes the set from
//! everything it still needs, so a range needed by two stack entries is only
//! released when neither needs it any more. It is local memory state and never
//! encoded.

use std::mem;

use super::*;

impl DocStore {
    /// Adds `item` and every type item above it to `retained`, like Yjs
    /// `keepItem`: collecting a type item collects all of its children, so a
    /// retained item is only safe while its ancestors are retained too.
    pub(crate) fn retain_with_ancestors(retained: &mut DeleteSet, item: &Item) {
        retained.add(item.id.client, item.id.clock, item.len());

        let mut parent = item.parent.clone();
        while let Some(Parent::Type(ty)) = parent {
            let Some(carrier) = ty.ty().and_then(|ty| ty.item.get()) else {
                break;
            };
            retained.add(carrier.id.client, carrier.id.clock, carrier.len());
            parent = carrier.parent.clone();
        }
    }

    /// Adds `ranges` to the retained ranges. Nothing is released, so nothing
    /// is collected: capturing a commit costs only its own ranges.
    pub(crate) fn add_retained(&mut self, ranges: &DeleteSet) {
        self.retained.merge(ranges);
    }

    /// Replaces the retained ranges with `retained`, then garbage-collects
    /// (when GC is enabled) and merges the deleted structs of the released
    /// ranges (retained before, not any more), so released content does not
    /// wait for a later deletion next to it. Only the released ranges are
    /// visited. Runs inside a transaction, whose commit merges the children
    /// replaced here.
    pub(crate) fn set_retained(&mut self, retained: DeleteSet) {
        let old = mem::replace(&mut self.retained, retained);
        let released = subtract(&old, &self.retained);
        if released.is_empty() {
            return;
        }
        if self.gc {
            // structs that still overlap a retained range are skipped
            self.gc_delete_set(&released);
        }
        self.merge_delete_set(&released);
    }
}

/// The ranges of `from` that are not in `ranges`.
fn subtract(from: &DeleteSet, ranges: &DeleteSet) -> DeleteSet {
    let mut result = DeleteSet::default();
    for (client, from) in from.iter() {
        let kept = ranges.get(client).map(|r| r.canonical_ranges()).unwrap_or_default();
        let mut next = 0;
        for range in from.canonical_ranges() {
            while next < kept.len() && kept[next].end <= range.start {
                next += 1;
            }
            let mut start = range.start;
            for kept in kept[next..].iter().take_while(|kept| kept.start < range.end) {
                if kept.start > start {
                    result.add_range(*client, start..kept.start);
                }
                start = start.max(kept.end);
            }
            if start < range.end {
                result.add_range(*client, start..range.end);
            }
        }
    }
    result
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    fn content(doc: &Doc, id: (Client, Clock)) -> Content {
        let store = doc.store.read().unwrap();
        match store.get_node(id).unwrap() {
            Node::Item(item) => item.get().unwrap().content.clone(),
            node => panic!("{id:?} is {node:?}"),
        }
    }

    fn range(client: Client, start: Clock, end: Clock) -> DeleteSet {
        let mut set = DeleteSet::default();
        set.add_range(client, start..end);
        set
    }

    fn set_retained(doc: &Doc, retained: DeleteSet) {
        doc.transact_mut(None, |tx| {
            tx.store_mut().set_retained(retained);
            Ok(())
        })
        .unwrap();
    }

    /// Retains the items at `ids` with their ancestors.
    fn retain(doc: &Doc, ids: &[(Client, Clock)]) {
        let mut retained = DeleteSet::default();
        {
            let store = doc.store.read().unwrap();
            for id in ids {
                let item = store.get_node(*id).unwrap().as_item();
                DocStore::retain_with_ancestors(&mut retained, item.get().unwrap());
            }
        }
        set_retained(doc, retained);
    }

    fn nested_text(doc: &Doc) -> (Map, Text) {
        let mut map = doc.get_or_create_map("map").unwrap();
        map.insert("text".into(), Value::Text(doc.create_text().unwrap()))
            .unwrap();
        let Some(Value::Text(text)) = map.get("text") else {
            unreachable!()
        };
        (map, text)
    }

    #[test]
    fn subtract_keeps_what_is_not_covered() {
        let mut from = range(1, 0, 10);
        from.add_range(1, 20..30);
        from.add_range(2, 0..5);
        let mut kept = range(1, 2, 4);
        kept.add_range(1, 6..25);
        kept.add_range(3, 0..5);
        let mut expected = range(1, 0, 2);
        expected.add_range(1, 4..6);
        expected.add_range(1, 25..30);
        expected.add_range(2, 0..5);
        let result = subtract(&from, &kept);
        for client in [1, 2] {
            assert_eq!(
                result.get(&client).unwrap().canonical_ranges(),
                expected.get(&client).unwrap().canonical_ranges()
            );
        }
        assert!(result.get(&3).is_none());
        assert!(subtract(&from, &from).is_empty());
    }

    #[test]
    fn adding_ranges_collects_nothing() {
        let doc = DocOptions::new().with_client_id(1).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abcdef").unwrap();
        retain(&doc, &[(1, 0)]);
        text.remove(0, 6).unwrap();
        doc.transact_mut(None, |tx| {
            tx.store_mut().add_retained(&range(1, 10, 20));
            Ok(())
        })
        .unwrap();
        assert_eq!(content(&doc, (1, 0)), Content::String("abcdef".into()));
    }

    #[test]
    fn shrinking_releases_only_the_difference() {
        let doc = DocOptions::new().with_client_id(1).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abcdef").unwrap();
        set_retained(&doc, range(1, 0, 6));
        text.remove(1, 1).unwrap(); // "b"
        text.remove(2, 1).unwrap(); // "d"
        text.remove(3, 1).unwrap(); // "f"
        // keep "b" and "f", release "d"
        let mut kept = range(1, 1, 2);
        kept.add_range(1, 5..6);
        set_retained(&doc, kept);
        assert_eq!(content(&doc, (1, 1)), Content::String("b".into()));
        assert_eq!(content(&doc, (1, 3)), Content::Deleted(1));
        assert_eq!(content(&doc, (1, 5)), Content::String("f".into()));
    }

    #[test]
    fn shrinking_to_part_of_an_item_keeps_it_whole() {
        let doc = DocOptions::new().with_client_id(1).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abc").unwrap();
        set_retained(&doc, range(1, 0, 3));
        text.remove(0, 3).unwrap();
        // "a" and "c" are released, but "abc" is one item overlapping "b"
        set_retained(&doc, range(1, 1, 2));
        assert_eq!(content(&doc, (1, 0)), Content::String("abc".into()));
    }

    #[test]
    fn retained_deep_ancestors_across_clients_survive_until_release() {
        let mut doc = Doc::with_client(1);
        let mut root = doc.get_or_create_map("root").unwrap();
        let mut parent = doc.create_map().unwrap();
        root.insert("parent".into(), parent.clone()).unwrap();
        doc.set_client(2);
        let mut middle = doc.create_map().unwrap();
        parent.insert("middle".into(), middle.clone()).unwrap();
        doc.set_client(3);
        let mut text = doc.create_text().unwrap();
        middle.insert("text".into(), text.clone()).unwrap();
        doc.set_client(4);
        text.insert(0, "abc").unwrap();

        let mut retained = DeleteSet::default();
        {
            let store = doc.store.read().unwrap();
            let item = store.get_node((4, 1)).unwrap().as_item();
            DocStore::retain_with_ancestors(&mut retained, item.get().unwrap());
        }
        for client in 1..=4 {
            assert!(retained.get(&client).unwrap().contains(0));
        }
        set_retained(&doc, retained);
        root.remove("parent");
        for client in 1..=3 {
            assert!(matches!(content(&doc, (client, 0)), Content::Type(_)));
        }
        assert_eq!(content(&doc, (4, 0)), Content::String("abc".into()));

        set_retained(&doc, DeleteSet::default());
        assert_eq!(content(&doc, (1, 0)), Content::Deleted(1));
        let store = doc.store.read().unwrap();
        for client in 2..=4 {
            assert!(store.get_node((client, 0)).unwrap().is_gc());
        }
    }

    /// Releasing from the history stage collects a type's children; the
    /// commit merges them with the merge points of the transaction.
    #[test]
    fn history_stage_release_merges_all_collected_children() {
        #[derive(Debug)]
        struct Release;
        impl CommitHook for Release {
            fn on_commit(&mut self, store: &mut DocStore, _: &CommitSummary) {
                store.set_retained(DeleteSet::default());
            }

            fn as_any(&self) -> &dyn std::any::Any {
                self
            }

            fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
                self
            }
        }

        let doc = Doc::with_client(1);
        let mut root = doc.get_or_create_map("root").unwrap();
        let mut parent = doc.create_map().unwrap();
        root.insert("parent".into(), parent.clone()).unwrap();
        for i in 0..4 {
            parent.insert(format!("k{i}"), i as i64).unwrap();
        }
        set_retained(&doc, range(1, 0, 1));
        root.remove("parent");
        doc.store.write().unwrap().history_hook = Some(Box::new(Release));
        root.insert("trigger".into(), 1).unwrap();

        let store = doc.store.read().unwrap();
        let child = store.get_node((1, 1)).unwrap();
        // `Node` equality only compares ids
        assert_eq!(child, Node::new_gc((1, 1).into(), 4));
        assert_eq!(child.len(), 4, "the collected children are merged");
        assert!(store.collector.is_empty());
    }

    /// Cost of retention changes with `n` retained fragments, in
    /// milliseconds: appending, setting the same set again and releasing a
    /// few ranges only visit what changed.
    #[test]
    #[ignore = "measurement, run with --ignored --nocapture"]
    fn retention_change_cost() {
        for n in [500u64, 3000] {
            let doc = Doc::with_client(1);
            let map = doc.get_or_create_map("root").unwrap();
            doc.transact_mut(None, |tx| {
                for i in 0..2 * n {
                    tx.map(&map)?.insert(format!("k{i}"), i as i64)?;
                }
                Ok(())
            })
            .unwrap();
            let mut retained = DeleteSet::default();
            for i in 0..n {
                retained.add(1, 2 * i, 1);
            }
            doc.transact_mut(None, |tx| {
                tx.store_mut().set_retained(retained.clone());
                for i in 0..n {
                    tx.map(&map)?.remove(&format!("k{}", 2 * i));
                }
                Ok(())
            })
            .unwrap();

            let time = |label: &str, f: &dyn Fn(&mut DocStore)| {
                for round in 0..3 {
                    let now = std::time::Instant::now();
                    doc.transact_mut(None, |tx| {
                        f(tx.store_mut());
                        Ok(())
                    })
                    .unwrap();
                    eprintln!(
                        "retained={n} {label} round={round} elapsed_us={}",
                        now.elapsed().as_micros()
                    );
                }
            };
            time("append-1", &|store| store.add_retained(&range(1, 10 * n, 10 * n + 1)));
            time("same", &|store| store.set_retained(store.retained.clone()));
            let fewer = retained.clone();
            let released = (0..5).map(|i| 2 * i).collect::<Vec<_>>();
            let fewer = subtract(&fewer, &{
                let mut set = DeleteSet::default();
                for clock in &released {
                    set.add(1, *clock, 1);
                }
                set
            });
            time("release-5", &|store| store.set_retained(fewer.clone()));
            let store = doc.store.read().unwrap();
            for clock in released {
                assert!(matches!(
                    store.get_node((1, clock)).unwrap().as_item().get().unwrap().content,
                    Content::Deleted(1)
                ));
            }
        }
    }

    #[test]
    fn commit_gc_skips_retained_ranges() {
        let doc = DocOptions::new().with_client_id(1).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abcdef").unwrap();
        retain(&doc, &[(1, 0)]);
        doc.transact_mut(None, |tx| {
            let mut text = tx.text(&text)?;
            text.remove(1, 2)?;
            text.remove(2, 1)
        })
        .unwrap();

        assert_eq!(text.to_string(), "adf");
        assert_eq!(content(&doc, (1, 1)), Content::String("bc".into()));
        assert_eq!(content(&doc, (1, 4)), Content::String("e".into()));
    }

    #[test]
    fn partially_retained_items_are_kept_whole() {
        let doc = DocOptions::new().with_client_id(1).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abc").unwrap();
        set_retained(&doc, range(1, 1, 2));
        text.remove(0, 3).unwrap();
        assert_eq!(content(&doc, (1, 0)), Content::String("abc".into()));
    }

    #[test]
    fn without_retention_deleted_parents_collect_children() {
        let doc = DocOptions::new().with_client_id(1).build();
        let (mut map, mut text) = nested_text(&doc);
        text.insert(0, "hello").unwrap();
        map.remove("text");
        let store = doc.store.read().unwrap();
        assert_eq!(store.get_node((1, 1)).unwrap(), Node::new_gc((1, 1).into(), 5));
    }

    #[test]
    fn retained_children_keep_their_deleted_parents() {
        let doc = DocOptions::new().with_client_id(1).build();
        let (mut map, mut text) = nested_text(&doc);
        text.insert(0, "hello").unwrap();
        // the text item (1, 0) is retained with its child
        retain(&doc, &[(1, 1)]);
        text.remove(0, 5).unwrap();
        map.remove("text");

        // collecting the text item would turn its children into GC structs
        assert!(matches!(content(&doc, (1, 0)), Content::Type(_)));
        assert_eq!(content(&doc, (1, 1)), Content::String("hello".into()));

        // released, the parent is collected with its children
        set_retained(&doc, DeleteSet::default());
        assert_eq!(content(&doc, (1, 0)), Content::Deleted(1));
        let store = doc.store.read().unwrap();
        assert_eq!(store.get_node((1, 1)).unwrap(), Node::new_gc((1, 1).into(), 5));
    }

    #[test]
    fn releasing_collects_and_merges() {
        let doc = DocOptions::new().with_client_id(1).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abcdef").unwrap();
        retain(&doc, &[(1, 0)]);
        text.remove(1, 2).unwrap();
        text.remove(2, 1).unwrap();

        set_retained(&doc, DeleteSet::default());
        assert_eq!(content(&doc, (1, 1)), Content::Deleted(2));
        assert_eq!(content(&doc, (1, 4)), Content::Deleted(1));
        assert_eq!(text.to_string(), "adf");

        // adjacent deleted ranges merge once released
        let doc = DocOptions::new().with_client_id(1).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abcdef").unwrap();
        retain(&doc, &[(1, 0)]);
        text.remove(1, 2).unwrap();
        text.remove(1, 2).unwrap();
        set_retained(&doc, DeleteSet::default());
        let store = doc.store.read().unwrap();
        let node = store.get_node((1, 1)).unwrap();
        assert_eq!((node.id(), node.len()), (Id::new(1, 1), 4));
        assert_eq!(&node.as_item().get().unwrap().content, &Content::Deleted(4));
    }

    #[test]
    fn overlapping_retention_is_released_with_its_last_owner() {
        let doc = DocOptions::new().with_client_id(1).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abcdef").unwrap();
        // two stack entries both need "cd"; the owner passes their union
        let first = range(1, 1, 3);
        let second = range(1, 2, 4);
        let mut union = first.clone();
        union.merge(&second);
        set_retained(&doc, union);
        text.remove(1, 1).unwrap(); // "b"
        text.remove(1, 2).unwrap(); // "cd"

        // the deleted "b" and "cd" merged into one item
        assert_eq!(content(&doc, (1, 1)), Content::String("bcd".into()));

        // the first entry goes away, the second one still needs "cd"
        set_retained(&doc, second);
        assert_eq!(content(&doc, (1, 1)), Content::String("bcd".into()));

        set_retained(&doc, DeleteSet::default());
        let store = doc.store.read().unwrap();
        let node = store.get_node((1, 1)).unwrap();
        assert_eq!((node.id(), node.len()), (Id::new(1, 1), 3));
        assert_eq!(&node.as_item().get().unwrap().content, &Content::Deleted(3));
    }

    #[test]
    fn releasing_without_gc_keeps_content() {
        let doc = DocOptions::new().with_client_id(1).auto_gc(false).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abc").unwrap();
        retain(&doc, &[(1, 0)]);
        text.remove(0, 3).unwrap();
        set_retained(&doc, DeleteSet::default());
        assert_eq!(content(&doc, (1, 0)), Content::String("abc".into()));
    }

    #[test]
    fn retained_content_is_encoded_and_decoded() {
        let doc = DocOptions::new().with_client_id(1).build();
        let mut text = doc.get_or_create_text("text").unwrap();
        text.insert(0, "abc").unwrap();
        retain(&doc, &[(1, 0)]);
        text.remove(1, 1).unwrap();

        let update = doc.encode_update_v1().unwrap();
        let mut peer = DocOptions::new().with_client_id(2).auto_gc(false).build();
        peer.apply_update_from_binary_v1(update.clone()).unwrap();
        assert_eq!(peer.get_or_create_text("text").unwrap().to_string(), "ac");
        assert_eq!(peer.encode_update_v1().unwrap(), update);
    }
}
