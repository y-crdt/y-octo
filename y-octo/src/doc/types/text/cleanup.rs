//! Formatting cleanup ported from Yjs v13.6.33 `types/YText.js` (MIT).

use super::*;
use crate::{
    YTypeKind,
    doc::{Carrier, DeleteSet},
};

/// Values plus their originating format item. JS object/array attributes use
/// reference equality in cleanupFormattingGap, not structural Any equality.
#[derive(Clone, Default)]
pub(super) struct FormatAttributes(BTreeMap<String, (Any, Id)>);
impl FormatAttributes {
    pub(super) fn get(&self, key: &str) -> Option<&Any> {
        self.0.get(key).map(|(value, _)| value)
    }
    pub(super) fn keys(&self) -> impl Iterator<Item = &String> {
        self.0.keys()
    }
    pub(super) fn remove(&mut self, key: &str) {
        self.0.remove(key);
    }
    pub(super) fn insert(&mut self, key: String, value: Any, id: Id) {
        self.0.insert(key, (value, id));
    }
    fn update(&mut self, key: &str, value: &Any, id: Id) {
        if is_nullish(value) {
            self.remove(key);
        } else {
            self.insert(key.to_string(), value.clone(), id);
        }
    }
    fn matches(&self, key: &str, value: &Any, source: Id) -> bool {
        let Some((previous, id)) = self.0.get(key) else {
            return matches!(value, Any::Null);
        };
        match (previous, value) {
            (Any::Object(_) | Any::Array(_) | Any::Binary(_), _) => *id == source,
            _ => equal_primitive(previous, value),
        }
    }
}
// Yjs equalAttrs uses lib0 equalFlat for objects. Only the outer
// container is compared by value. Nested objects have distinct identities
// in Any, which owns its children and does not share them across markers.
pub(super) fn equal_attrs(a: &Any, b: &Any) -> bool {
    match (a, b) {
        (Any::Object(a), Any::Object(b)) => {
            a.len() == b.len()
                && a.iter()
                    .all(|(key, value)| b.get(key).is_some_and(|other| equal_primitive(value, other)))
        }
        (Any::Array(a), Any::Array(b)) => a.len() == b.len() && a.iter().zip(b).all(|(a, b)| equal_primitive(a, b)),
        (Any::Object(map), Any::Array(array)) | (Any::Array(array), Any::Object(map)) => {
            map.len() == array.len()
                && array.iter().enumerate().all(|(index, value)| {
                    map.get(&index.to_string())
                        .is_some_and(|other| equal_primitive(value, other))
                })
        }
        (Any::Binary(a), Any::Binary(b)) => a == b,
        (Any::Binary(bytes), Any::Array(array)) | (Any::Array(array), Any::Binary(bytes)) => {
            bytes.len() == array.len()
                && bytes
                    .iter()
                    .zip(array)
                    .all(|(byte, value)| number(value) == Some(f64::from(*byte)))
        }
        (Any::Binary(bytes), Any::Object(map)) | (Any::Object(map), Any::Binary(bytes)) => {
            bytes.len() == map.len()
                && bytes
                    .iter()
                    .enumerate()
                    .all(|(index, byte)| map.get(&index.to_string()).and_then(number) == Some(f64::from(*byte)))
        }
        _ => equal_primitive(a, b),
    }
}

fn equal_primitive(a: &Any, b: &Any) -> bool {
    if matches!(a, Any::Object(_) | Any::Array(_) | Any::Binary(_))
        || matches!(b, Any::Object(_) | Any::Array(_) | Any::Binary(_))
    {
        return false;
    }
    number(a).zip(number(b)).map_or_else(|| a == b, |(a, b)| a == b)
}

fn number(value: &Any) -> Option<f64> {
    match value {
        Any::Integer(value) => Some(*value as f64),
        Any::Float32(value) => Some(value.into_inner() as f64),
        Any::Float64(value) => Some(value.into_inner()),
        _ => None,
    }
}

pub(super) fn cleanup_formatting_gap(
    store: &mut DocStore,
    ty: TypeIdx,
    mut start: ItemRef,
    curr: &ItemRef,
    start_attrs: &FormatAttributes,
    curr_attrs: &mut FormatAttributes,
) {
    let mut end = start;
    let mut end_formats = BTreeMap::new();
    while let Some(item) = end.and_then(|i| store.type_arena.items.get(i)) {
        if item.countable() && !item.deleted() {
            break;
        }
        if !item.deleted()
            && let Some((key, _)) = item.content.as_format()
        {
            end_formats.insert(key.clone(), item.id);
        }
        end = item.right;
    }
    let mut reached_curr = false;
    while !(start == end) {
        if *curr == start {
            reached_curr = true;
        }
        let item = start
            .and_then(|i| store.type_arena.items.get(i))
            .expect("gap end is reachable");
        let next = item.right;
        let mut remove = false;
        if !item.deleted()
            && let Some((key, value)) = item.content.as_format()
        {
            let same_start = start_attrs.matches(key, value, item.id);
            if end_formats.get(key) != Some(&item.id) || same_start {
                remove = true;
                if !reached_curr && curr_attrs.matches(key, value, item.id) && !same_start {
                    if let Some(entry) = start_attrs.0.get(key) {
                        curr_attrs.0.insert(key.clone(), entry.clone());
                    } else {
                        curr_attrs.remove(key);
                    }
                }
            }
            if !reached_curr && !remove {
                curr_attrs.update(key, value, item.id);
            }
        }
        if remove {
            store.delete_item(start.expect("current item"), Some(ty));
        }
        start = next;
    }
}

fn cleanup_contextless_gap(store: &mut DocStore, ty: TypeIdx, mut item_ref: ItemRef) {
    while let Some(item) = item_ref.and_then(|i| store.type_arena.items.get(i)) {
        if item
            .right
            .and_then(|i| store.type_arena.items.get(i))
            .is_none_or(|right| right.countable() && !right.deleted())
        {
            break;
        }
        item_ref = item.right;
    }
    let mut attrs = std::collections::BTreeSet::new();
    while let Some(item) = item_ref.and_then(|i| store.type_arena.items.get(i)) {
        let next = item.left;
        if item.countable() && !item.deleted() {
            break;
        }
        if !item.deleted()
            && let Some((key, _)) = item.content.as_format()
            && !attrs.insert(key.clone())
        {
            store.delete_item(item_ref.expect("current item"), Some(ty));
        }
        item_ref = next;
    }
}

fn cleanup_text(store: &mut DocStore, ty: TypeIdx) {
    let mut start = store.type_arena[ty].start;
    let mut end = start;
    let mut start_attrs = FormatAttributes::default();
    let mut current_attrs = FormatAttributes::default();
    while let Some(item) = end.and_then(|i| store.type_arena.items.get(i)) {
        let next = item.right;
        if !item.deleted() {
            match &item.content {
                Content::Format(format) => current_attrs.update(&format.key, &format.value, item.id),
                _ => {
                    cleanup_formatting_gap(store, ty, start, &end, &start_attrs, &mut current_attrs);
                    start_attrs = current_attrs.clone();
                    start = end;
                }
            }
        }
        end = next;
    }
}

/// A private origin identifies the event; history exclusion is independently
/// enforced by TransactionMut::capture_history, even if an origin is cloned.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(in crate::doc) struct FormattingCleanup;

#[derive(Default)]
pub(in crate::doc) struct CleanupPlan {
    full: std::collections::HashSet<TypeIdx>,
    gaps: Vec<(TypeIdx, Id)>,
}
impl CleanupPlan {
    pub(in crate::doc) fn after_remote(
        store: &DocStore,
        before: &crate::StateVector,
        after: &crate::StateVector,
        changed: &crate::doc::store::ChangedTypeRefs,
        deleted: &DeleteSet,
    ) -> Self {
        // Same gate as YText._callObserver: a pre-existing formatted text was
        // touched by a remote transaction. New nested types are not observers.
        let needed = changed.keys().any(|parent| {
            store.type_arena.get(*parent).is_some_and(|ty| {
                matches!(ty.kind(), YTypeKind::Text | YTypeKind::XMLText)
                    && ty.has_formatting
                    && match ty.carrier(&store.type_arena.items) {
                        Carrier::Live(item) => !item.deleted() && item.id.clock < before.get(&item.id.client),
                        // a root
                        Carrier::Unset => true,
                        // nothing is left in a retired type
                        Carrier::Retired => false,
                    }
            })
        });
        let mut plan = Self::default();
        if !needed {
            return plan;
        }
        for (client, clock) in after.iter() {
            let start = before.get(client);
            if *clock > start {
                visit_items(store, *client, start..*clock, |item| {
                    if !item.deleted()
                        && matches!(item.content, Content::Format(_))
                        && let Some(parent) = &item.parent
                    {
                        plan.full.insert(*parent);
                    }
                });
            }
        }
        for (client, ranges) in deleted.iter() {
            for range in ranges {
                visit_items(store, *client, range, |item| {
                    let Some(parent) = &item.parent else {
                        return;
                    };
                    if !store.type_arena.get(*parent).is_some_and(|ty| ty.has_formatting) {
                        return;
                    }
                    if matches!(item.content, Content::Format(_)) {
                        plan.full.insert(*parent);
                    } else {
                        plan.gaps.push((*parent, item.id));
                    }
                });
            }
        }
        plan
    }
    pub(in crate::doc) fn is_empty(&self) -> bool {
        self.full.is_empty() && self.gaps.is_empty()
    }
    pub(in crate::doc) fn run(self, store: &mut DocStore) {
        for (parent, id) in self.gaps {
            if self.full.contains(&parent) {
                continue;
            }
            // GC/merge may have replaced the old struct. Resolve by clock,
            // rather than keeping a temporary Item reference across commit.
            let Some(item) = store.get_node(id).and_then(|n| n.as_item()) else {
                continue;
            };
            cleanup_contextless_gap(store, parent, Some(item));
        }
        for parent in self.full {
            cleanup_text(store, parent);
        }
    }
}
fn visit_items(store: &DocStore, client: u64, range: std::ops::Range<u64>, mut visit: impl FnMut(&crate::Item)) {
    let Some(nodes) = store.items.get(&client) else {
        return;
    };
    let Some(start) = DocStore::get_node_index(nodes, range.start) else {
        return;
    };
    for node in nodes
        .nodes(client)
        .skip(start)
        .take_while(|node| node.clock() < range.end)
    {
        if let Some(item) = node.as_item() {
            visit(store.type_arena.items.get(item).expect("stored item"));
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Any, Doc, TextAttributes, TextDeltaOp, TextInsert, loom_model};

    #[test]
    fn deleting_formatted_text_removes_the_empty_formatting_gap() {
        loom_model!(64 << 10, {
            let doc = Doc::with_client(101);
            let mut text = doc.get_or_create_text("text").unwrap();
            text.apply_delta(&[TextDeltaOp::Insert {
                insert: TextInsert::Text("abc".into()),
                format: Some(TextAttributes::from([("bold".into(), Any::True)])),
            }])
            .unwrap();
            text.remove(0, 3).unwrap();
            assert_eq!(text.to_delta(), vec![]);
            assert_eq!(doc.get_delete_sets().get(&101).unwrap().canonical_ranges(), vec![0..5]);
        });
    }
}

#[cfg(test)]
mod remote_tests {
    use super::FormattingCleanup;
    use crate::{
        Any, Doc, Origin, TextAttributes, TextDeltaOp, loom_model,
        sync::{Arc, Mutex},
    };
    #[test]
    fn remote_cleanup_has_its_own_commit_and_no_empty_followup() {
        loom_model!(128 << 10, {
            let a = Doc::with_client(101);
            let mut ta = a.get_or_create_text("text").unwrap();
            ta.insert(0, "ab").unwrap();
            let mut b = Doc::with_client(202);
            let mut tb = b.get_or_create_text("text").unwrap();
            b.apply_update_from_binary_v1(a.encode_update_v1().unwrap()).unwrap();
            let bold = TextAttributes::from([("bold".into(), Any::True)]);
            ta.apply_delta(&[TextDeltaOp::Retain {
                retain: 1,
                format: Some(bold.clone()),
            }])
            .unwrap();
            tb.apply_delta(&[TextDeltaOp::Retain {
                retain: 1,
                format: Some(bold),
            }])
            .unwrap();
            let events = Arc::new(Mutex::new(Vec::new()));
            let sink = events.clone();
            let _sub = a.subscribe(move |event| sink.lock().unwrap().push(event.clone()));
            let hooks = Arc::new(Mutex::new(0));
            #[derive(Debug)]
            struct Hook(Arc<Mutex<usize>>);
            impl crate::doc::transaction::CommitHook for Hook {
                fn as_any(&self) -> &dyn std::any::Any {
                    self
                }
                fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
                    self
                }
                fn on_commit(&mut self, _: &mut crate::doc::DocStore, _: &crate::CommitSummary) {
                    *self.0.lock().unwrap() += 1;
                }
            }
            a.store.write().unwrap().history_hook = Some(Box::new(Hook(hooks.clone())));
            let incoming = b.encode_update_v1().unwrap();
            let mut receiver = a.clone();
            receiver
                .apply_update_with_origin(crate::Update::decode_v1(&incoming).unwrap(), Origin::new("remote"))
                .unwrap();
            let events = events.lock().unwrap();
            assert_eq!(events.len(), 2);
            assert_eq!(
                *hooks.lock().unwrap(),
                1,
                "maintenance bypasses the history hook entirely"
            );
            assert!(!events[0].local);
            assert!(events[1].local);
            assert!(
                events[1]
                    .origin
                    .as_ref()
                    .unwrap()
                    .downcast_ref::<FormattingCleanup>()
                    .is_some()
            );
            assert_eq!(events[1].before_state, events[0].after_state);
            assert_eq!(events[1].seq, events[0].seq + 1);
            assert_eq!(events[1].before_state, events[1].after_state);
            assert!(!events[1].deleted.is_empty());
            let count = receiver.store.read().unwrap().commit_seq;
            drop(events);
            receiver.apply_update_from_binary_v1(incoming).unwrap();
            assert_eq!(receiver.store.read().unwrap().commit_seq, count);
        });
    }
}

#[cfg(test)]
mod origin_drop_tests {
    use std::sync::{Arc, Mutex};

    use crate::{Any, Doc, Origin, Text, TextAttributes, TextDeltaOp, Update, loom_model};
    #[derive(Clone)]
    struct OriginProbe {
        doc: Doc,
        read_text: Option<Text>,
        unlocked: Arc<Mutex<Option<bool>>>,
    }
    impl PartialEq for OriginProbe {
        fn eq(&self, other: &Self) -> bool {
            std::ptr::eq(self, other)
        }
    }
    impl Eq for OriginProbe {}
    impl std::hash::Hash for OriginProbe {
        fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
            h.write_u8(1)
        }
    }
    impl Drop for OriginProbe {
        fn drop(&mut self) {
            let read = self.doc.transact(|tx| {
                if let Some(text) = &self.read_text {
                    assert_eq!(tx.text(text).unwrap().to_string(), "a committed");
                }
            });
            *self.unlocked.lock().unwrap() = Some(read.is_ok());
        }
    }
    #[test]
    fn remote_cleanup_drops_the_original_origin_after_unlocking() {
        loom_model!(128 << 10, {
            let doc = Doc::with_client(101);
            let mut text = doc.get_or_create_text("text").unwrap();
            text.insert(0, "ab").unwrap();
            let mut peer = Doc::with_client(202);
            let mut other = peer.get_or_create_text("text").unwrap();
            peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
                .unwrap();
            let delta = [TextDeltaOp::Retain {
                retain: 1,
                format: Some(TextAttributes::from([("bold".into(), Any::True)])),
            }];
            text.apply_delta(&delta).unwrap();
            other.apply_delta(&delta).unwrap();
            let unlocked = Arc::new(Mutex::new(None));
            let origin = Origin::new(OriginProbe {
                doc: doc.clone(),
                read_text: None,
                unlocked: unlocked.clone(),
            });
            // No subscriber or history hook keeps a copy of this origin.
            doc.apply_update_with_origin(Update::decode_v1(peer.encode_update_v1().unwrap()).unwrap(), origin)
                .unwrap();
            assert_eq!(*unlocked.lock().unwrap(), Some(true));
        });
    }
    #[test]
    fn nested_remote_origin_drops_after_the_outer_document_unlocks() {
        loom_model!(128 << 10, {
            let outer = Doc::with_client(101);
            let receiver = Doc::with_client(202);
            let sender = Doc::with_client(303);
            let mut outer_text = outer.get_or_create_text("outer").unwrap();
            outer_text.insert(0, "a").unwrap();
            sender.get_or_create_text("text").unwrap().insert(0, "b").unwrap();
            let update = Update::decode_v1(sender.encode_update_v1().unwrap()).unwrap();
            let unlocked = Arc::new(Mutex::new(None));
            outer
                .transact_mut(None, |tx| {
                    tx.text(&outer_text)?.insert(1, " committed")?;
                    receiver.apply_update_with_origin(
                        update,
                        Origin::new(OriginProbe {
                            doc: outer.clone(),
                            read_text: Some(outer_text.clone()),
                            unlocked: unlocked.clone(),
                        }),
                    )?;
                    assert_eq!(*unlocked.lock().unwrap(), None);
                    Ok(())
                })
                .unwrap();
            assert_eq!(*unlocked.lock().unwrap(), Some(true));
            assert_eq!(outer_text.to_string(), "a committed");
            assert_eq!(receiver.get_or_create_text("text").unwrap().to_string(), "b");
        });
    }
}
