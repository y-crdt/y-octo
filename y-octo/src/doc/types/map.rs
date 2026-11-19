use super::*;
use crate::{
    JwstCodecResult,
    doc::{AsInner, Node, Parent, YTypeRef},
    impl_type,
};

impl_type!(Map);

pub(crate) trait MapType: AsInner<Inner = YTypeRef> {
    fn _id(&self) -> Option<Id> {
        or_released(self.as_inner().read(|_, ty| ty.id()))
    }

    fn _insert<V: Into<Value>>(&mut self, key: String, value: V) -> JwstCodecResult {
        let parent = self.as_inner();
        let content: Content = value.into().into();
        parent.write(|store, ty| map_insert(parent, store, ty, key, content))
    }

    fn _get(&self, key: &str) -> Option<Value> {
        or_released(
            self.as_inner()
                .read(|_, ty| map_value(ty, key).map(|item| Value::from(&item.content))),
        )
    }

    fn _contains_key(&self, key: &str) -> bool {
        or_released(self.as_inner().read(|_, ty| map_value(ty, key).is_some()))
    }

    fn _remove(&mut self, key: &str) {
        let result = self.as_inner().write(|store, ty| {
            map_remove(store, ty, key);
            Ok(())
        });
        if result != Err(JwstCodecError::InvalidParent) {
            or_released(result);
        }
    }

    fn _clear(&mut self) -> JwstCodecResult {
        self.as_inner().write(|store, ty| {
            map_clear(store, ty);
            Ok(())
        })
    }

    fn _len(&self) -> u64 {
        or_released(self.as_inner().read(|_, ty| map_entries(ty).count() as u64))
    }

    /// A snapshot of the visible entries, taken under one store read lock.
    fn _entries(&self) -> Vec<(String, Value)> {
        or_released(self.as_inner().read(|_, ty| {
            map_entries(ty)
                .map(|(k, item)| (k.to_string(), Value::from(&item.content)))
                .collect()
        }))
    }

    fn _keys(&self) -> Vec<String> {
        or_released(
            self.as_inner()
                .read(|_, ty| map_entries(ty).map(|(k, _)| k.to_string()).collect()),
        )
    }

    fn _values(&self) -> Vec<Value> {
        or_released(
            self.as_inner()
                .read(|_, ty| map_entries(ty).map(|(_, item)| Value::from(&item.content)).collect()),
        )
    }
}

/// Sets `key` of the map type `parent` (data `ty`). The caller holds the
/// store write lock.
pub(crate) fn map_insert(
    parent: &YTypeRef,
    store: &mut DocStore,
    ty: &mut YType,
    key: String,
    content: Content,
) -> JwstCodecResult {
    check_insertable(parent, ty, &content)?;
    let key = SmolStr::new(key);
    let left = ty.map.get(&key).cloned();

    let item = store.create_item(
        content,
        left.unwrap_or(Somr::none()),
        Somr::none(),
        Some(Parent::Type(parent.clone())),
        Some(key),
    );
    store.integrate(Node::Item(item), 0, Some(ty))
}

/// Deletes `key` of a map type. The caller holds the store write lock.
pub(crate) fn map_remove(store: &mut DocStore, ty: &mut YType, key: &str) {
    if let Some(item) = ty.map.get(key).cloned()
        && let Some(item) = item.get()
    {
        store.delete_item(item, Some(ty));
    }
}

/// Deletes every key of a map type. The caller holds the store write lock.
pub(crate) fn map_clear(store: &mut DocStore, ty: &mut YType) {
    let items = ty
        .map
        .values()
        .filter(|item| item.get().is_some_and(|item| !item.deleted()))
        .cloned()
        .collect::<Vec<_>>();
    for item in items {
        if let Some(item) = item.get() {
            store.delete_item(item, Some(ty));
        }
    }
}

/// The current, not deleted value item of `key`. The caller holds the store
/// lock.
pub(crate) fn map_value<'a>(ty: &'a YType, key: &str) -> Option<&'a Item> {
    ty.map
        .get(key)
        .and_then(|item| item.get())
        .filter(|item| !item.deleted())
}

/// The visible entries of a map type. The caller holds the store lock.
pub(crate) fn map_entries(ty: &YType) -> impl Iterator<Item = (&str, &Item)> {
    ty.map
        .iter()
        .filter_map(|(k, v)| v.get().filter(|item| !item.deleted()).map(|item| (k.as_str(), item)))
}

impl MapType for Map {}

impl Map {
    #[inline(always)]
    pub fn id(&self) -> Option<Id> {
        self._id()
    }

    #[inline(always)]
    pub fn insert<V: Into<Value>>(&mut self, key: String, value: V) -> JwstCodecResult {
        self._insert(key, value)
    }

    #[inline(always)]
    pub fn get(&self, key: &str) -> Option<Value> {
        self._get(key)
    }

    #[inline(always)]
    pub fn contains_key(&self, key: &str) -> bool {
        self._contains_key(key)
    }

    /// Deletes `key`.
    ///
    /// # Panics
    ///
    /// On errors other than a released document, as it returns nothing (kept
    /// for compatibility): among them `ClientIdRequired` while the host has
    /// to assign a client ID ([Doc::client_required]). Remove inside
    /// [Doc::transact_mut] (`tx.map(&map)?.remove(key)`) to get that error
    /// back, with nothing changed, and retry after [Doc::set_client].
    #[inline(always)]
    pub fn remove(&mut self, key: &str) {
        self._remove(key)
    }

    /// Deletes every key in one transaction.
    #[inline(always)]
    pub fn clear(&mut self) -> JwstCodecResult {
        self._clear()
    }

    #[inline(always)]
    pub fn len(&self) -> u64 {
        self._len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// A snapshot of the visible entries, taken under one store read lock.
    #[inline(always)]
    pub fn iter(&self) -> std::vec::IntoIter<(String, Value)> {
        self._entries().into_iter()
    }

    /// Same as [Map::iter].
    #[inline(always)]
    pub fn entries(&self) -> std::vec::IntoIter<(String, Value)> {
        self._entries().into_iter()
    }

    /// A snapshot of the visible keys.
    #[inline(always)]
    pub fn keys(&self) -> std::vec::IntoIter<String> {
        self._keys().into_iter()
    }

    /// A snapshot of the visible values.
    #[inline(always)]
    pub fn values(&self) -> std::vec::IntoIter<Value> {
        self._values().into_iter()
    }
}

impl serde::Serialize for Map {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;

        let entries = self.iter();
        let mut map = serializer.serialize_map(Some(entries.len()))?;
        for (key, value) in entries {
            map.serialize_entry(&key, &value)?;
        }
        map.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Any, Doc, DocOptions, Update, loom_model};

    #[test]
    fn test_map_reinsert_after_gc_merge() {
        loom_model!({
            let doc = Doc::with_options(DocOptions::new().with_client_id(5));
            let mut map = doc.get_or_create_map("map").unwrap();
            map.insert("k".into(), 1).unwrap();
            map.insert("k".into(), 2).unwrap();
            map.remove("k");
            let before_gc = doc.encode_update_v1().unwrap();
            let sv = doc.get_state_vector();
            doc.gc().unwrap();
            map.insert("k".into(), 3).unwrap();
            let diff = doc.encode_state_as_update_v1(&sv).unwrap();
            let update = Update::decode_v1(&diff).unwrap();
            let item = update.structs.get(&5).unwrap().front().unwrap().as_item();
            // Yjs v13.6.33 tryToMergeWithLefts repairs the current map entry.
            assert_eq!(item.get().unwrap().origin_left_id, Some(Id::new(5, 1)));
            let mut peer = Doc::with_options(DocOptions::new().with_client_id(6).auto_gc(false));
            peer.apply_update_from_binary_v1(before_gc).unwrap();
            peer.apply_update_from_binary_v1(diff).unwrap();
            assert_eq!(
                peer.get_or_create_map("map").unwrap().get("k"),
                Some(Value::Any(Any::Integer(3)))
            );
        });
    }

    #[test]
    fn test_map_basic() {
        loom_model!({
            let doc = Doc::new();
            let mut map = doc.get_or_create_map("map").unwrap();
            map.insert("1".to_string(), "value").unwrap();
            assert_eq!(map.get("1").unwrap(), Value::Any(Any::String("value".to_string())));
            assert!(!map.contains_key("nonexistent_key"));
            assert_eq!(map.len(), 1);
            assert!(map.contains_key("1"));
            map.remove("1");
            assert!(!map.contains_key("1"));
            assert_eq!(map.len(), 0);
        });
    }

    #[test]
    fn test_map_equal() {
        loom_model!({
            let doc = Doc::new();
            let mut map = doc.get_or_create_map("map").unwrap();
            map.insert("1".to_string(), "value").unwrap();
            map.insert("2".to_string(), false).unwrap();

            let binary = doc.encode_update_v1().unwrap();
            let new_doc = Doc::try_from_binary_v1(binary).unwrap();
            let map = new_doc.get_or_create_map("map").unwrap();
            assert_eq!(map.get("1").unwrap(), Value::Any(Any::String("value".to_string())));
            assert_eq!(map.get("2").unwrap(), Value::Any(Any::False));
            assert_eq!(map.len(), 2);
        });
    }

    #[test]
    fn test_map_renew_value() {
        loom_model!({
            let doc = Doc::new();
            let mut map = doc.get_or_create_map("map").unwrap();
            map.insert("1".to_string(), "value").unwrap();
            map.insert("1".to_string(), "value2").unwrap();
            assert_eq!(map.get("1").unwrap(), Value::Any(Any::String("value2".to_string())));
            assert_eq!(map.len(), 1);
        });
    }

    #[test]
    fn test_map_re_encode() {
        loom_model!({
            let binary = {
                let doc = Doc::new();
                let mut map = doc.get_or_create_map("map").unwrap();
                map.insert("1".to_string(), "value1").unwrap();
                map.insert("2".to_string(), "value2").unwrap();
                doc.encode_update_v1().unwrap()
            };

            {
                let doc = Doc::try_from_binary_v1(binary).unwrap();
                let map = doc.get_or_create_map("map").unwrap();
                assert_eq!(map.get("1").unwrap(), Value::Any(Any::String("value1".to_string())));
                assert_eq!(map.get("2").unwrap(), Value::Any(Any::String("value2".to_string())));
            }
        });
    }

    #[test]
    fn test_map_iter() {
        loom_model!({
            let doc = Doc::new();
            let mut map = doc.get_or_create_map("map").unwrap();
            map.insert("1".to_string(), "value1").unwrap();
            map.insert("2".to_string(), "value2").unwrap();
            let mut vec = map.entries().collect::<Vec<_>>();

            // hashmap iteration is in random order instead of insert order
            vec.sort_by(|a, b| a.0.cmp(&b.0));

            assert_eq!(
                vec,
                vec![
                    ("1".to_string(), Value::Any(Any::String("value1".to_string()))),
                    ("2".to_string(), Value::Any(Any::String("value2".to_string())))
                ]
            )
        });
    }

    /// The map form of `array::tests::test_type_is_inserted_at_most_once`.
    #[test]
    fn test_type_is_inserted_at_most_once() {
        loom_model!({
            let doc = Doc::with_client(1);
            let mut a = doc.create_map().unwrap();
            let mut b = doc.create_map().unwrap();
            let mut c = doc.get_or_create_map("c").unwrap();

            a.insert("b".into(), b.clone()).unwrap();
            assert_eq!(
                c.insert("b".into(), b.clone()),
                Err(JwstCodecError::TypeAlreadyInserted)
            );
            // also under the key that holds it
            assert_eq!(
                a.insert("b".into(), b.clone()),
                Err(JwstCodecError::TypeAlreadyInserted)
            );
            assert_eq!(b.insert("a".into(), a.clone()), Err(JwstCodecError::InvalidParent));
            a.remove("b");

            assert_eq!(
                a.insert("b".into(), b.clone()),
                Err(JwstCodecError::TypeAlreadyInserted)
            );
            doc.gc().unwrap();
            assert_eq!(
                c.insert("b".into(), b.clone()),
                Err(JwstCodecError::TypeAlreadyInserted)
            );
            assert_eq!(
                a.insert("c".into(), c.clone()),
                Err(JwstCodecError::TypeAlreadyInserted)
            );

            assert!(a.is_empty());
            assert!(c.is_empty());
            assert!(b.is_empty());
        });
    }

    #[cfg(not(loom))]
    fn sorted_keys(map: &Map) -> Vec<String> {
        let mut keys = map.keys().collect::<Vec<_>>();
        keys.sort();
        keys
    }

    #[cfg(not(loom))]
    #[test]
    fn test_map_clear_commits_once_and_undoes_in_one_step() {
        use std::sync::{
            Arc,
            atomic::{AtomicUsize, Ordering},
        };

        use crate::{UndoManager, UndoOptions};

        let doc = Doc::with_client(1);
        let mut map = doc.get_or_create_map("map").unwrap();
        map.insert("a".into(), 1).unwrap();
        map.insert("b".into(), "two").unwrap();
        let mut list = doc.create_array().unwrap();
        map.insert("c".into(), list.clone()).unwrap();
        list.push(3).unwrap();

        let history = UndoManager::<()>::new(&doc, [(&map).into()], UndoOptions::default()).unwrap();
        let commits = Arc::new(AtomicUsize::new(0));
        let counter = commits.clone();
        let _subscription = doc.subscribe(move |_| {
            counter.fetch_add(1, Ordering::SeqCst);
        });

        map.clear().unwrap();
        assert_eq!(commits.load(Ordering::SeqCst), 1);
        assert!(map.is_empty());

        // clearing an empty map changes nothing and commits nothing
        map.clear().unwrap();
        assert_eq!(commits.load(Ordering::SeqCst), 1);

        let mut peer = Doc::with_client(2);
        peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
            .unwrap();
        let peer_map = peer.get_or_create_map("map").unwrap();
        assert!(peer_map.is_empty());
        assert_eq!(peer.get_state_vector(), doc.get_state_vector());
        // the undo manager keeps the deleted items from GC here, so compare
        // the peer by content instead of by store
        let sync = |peer: &mut Doc| {
            let diff = doc.encode_state_as_update_v1(&peer.get_state_vector()).unwrap();
            peer.apply_update_from_binary_v1(diff).unwrap();
            assert_eq!(peer.get_state_vector(), doc.get_state_vector());
        };

        assert!(history.undo().unwrap().is_some());
        assert_eq!(sorted_keys(&map), ["a", "b", "c"]);
        assert_eq!(map.get("a").unwrap(), Value::Any(Any::Integer(1)));
        assert_eq!(map.get("b").unwrap(), Value::Any(Any::String("two".into())));
        assert!(!history.can_undo());
        sync(&mut peer);
        assert_eq!(sorted_keys(&peer_map), ["a", "b", "c"]);
        assert_eq!(peer_map.get("b").unwrap(), Value::Any(Any::String("two".into())));

        assert!(history.redo().unwrap().is_some());
        assert!(map.is_empty());
        assert!(!history.can_redo());
        sync(&mut peer);
        assert!(peer_map.is_empty());
    }

    #[cfg(not(loom))]
    #[test]
    fn test_preliminary_map_clear_publishes_only_later_entries() {
        use crate::StateVector;

        let doc = Doc::with_client(1);
        let mut root = doc.get_or_create_map("root").unwrap();
        let mut draft = doc.create_map().unwrap();
        draft.insert("a".into(), 1).unwrap();
        draft.insert("b".into(), 2).unwrap();
        let mut list = doc.create_array().unwrap();
        list.push(1).unwrap();
        draft.insert("list".into(), list).unwrap();

        draft.clear().unwrap();
        assert!(draft.is_empty());
        draft.insert("c".into(), 3).unwrap();
        root.insert("draft".into(), draft.clone()).unwrap();

        // the root entry and "c" are all that is published
        assert_eq!(doc.get_state_vector(), StateVector::from([(1, 2)]));
        let Some(Value::Map(mounted)) = root.get("draft") else {
            panic!("draft is not mounted");
        };
        assert_eq!(sorted_keys(&mounted), ["c"]);

        let peer = Doc::try_from_binary_v1(doc.encode_update_v1().unwrap()).unwrap();
        let Some(Value::Map(copy)) = peer.get_or_create_map("root").unwrap().get("draft") else {
            panic!("draft is not synchronized");
        };
        assert_eq!(sorted_keys(&copy), ["c"]);
        assert_eq!(copy.get("c").unwrap(), Value::Any(Any::Integer(3)));
    }

    #[cfg(not(loom))]
    #[test]
    fn test_map_clear_in_transaction() {
        let doc = Doc::with_client(1);
        let mut map = doc.get_or_create_map("map").unwrap();
        map.insert("a".into(), 1).unwrap();
        map.insert("b".into(), 2).unwrap();

        doc.transact_mut(None, |tx| {
            let mut map = tx.map(&map)?;
            map.clear();
            assert!(map.is_empty());
            map.insert("c".into(), 3)
        })
        .unwrap();
        assert_eq!(sorted_keys(&map), ["c"]);

        let peer = Doc::try_from_binary_v1(doc.encode_update_v1().unwrap()).unwrap();
        assert_eq!(sorted_keys(&peer.get_or_create_map("map").unwrap()), ["c"]);
    }
}
