use super::{history::StoreHistory, store::StoreRef, *};
use crate::sync::{Arc, RwLock};

#[cfg(feature = "debug")]
#[derive(Debug, Clone, serde::Serialize)]
pub struct DocStoreStatus {
    pub clients: usize,
    pub nodes: usize,
    pub items: usize,
    pub gc_nodes: usize,
    pub skip_nodes: usize,
    pub deleted_items: usize,
    pub type_contents: usize,
    pub any_contents: usize,
    pub string_contents: usize,
    pub json_contents: usize,
    pub binary_contents: usize,
    pub deleted_contents: usize,
    pub other_contents: usize,
    pub delete_sets: usize,
    pub types: usize,
    pub dangling_types: usize,
    pub pending_nodes: usize,
    pub changed_types: usize,
    pub changed_keys: usize,
}

#[cfg(feature = "debug")]
#[derive(Debug, Clone, serde::Serialize)]
pub struct DocMemoryLayout {
    pub id: usize,
    pub option_id: usize,
    pub parent: usize,
    pub content: usize,
    pub any: usize,
    pub item: usize,
    pub item_ref: usize,
    pub item_allocation: usize,
    pub node: usize,
    pub node_len: usize,
    pub y_type: usize,
    pub y_type_ref: usize,
}

#[cfg(feature = "debug")]
pub fn memory_layout() -> DocMemoryLayout {
    use std::mem::size_of;

    DocMemoryLayout {
        id: size_of::<Id>(),
        option_id: size_of::<Option<Id>>(),
        parent: size_of::<Parent>(),
        content: size_of::<Content>(),
        any: size_of::<Any>(),
        item: size_of::<Item>(),
        item_ref: size_of::<ItemRef>(),
        item_allocation: size_of::<SomrInner<Item>>(),
        node: size_of::<Node>(),
        node_len: size_of::<NodeLen>(),
        y_type: size_of::<YType>(),
        y_type_ref: size_of::<YTypeRef>(),
    }
}

#[cfg(feature = "debug")]
pub fn reset_profiling_counters() {
    reset_clock_len_counters();
}

#[cfg(feature = "debug")]
pub fn profiling_counters() -> (u64, u64, u64) {
    clock_len_counters()
}

/// [DocOptions] used to create a new [Doc]
///
/// ```
/// use y_octo::DocOptions;
///
/// let doc = DocOptions::new()
///     .with_client_id(1)
///     .with_guid("guid".into())
///     .auto_gc(true)
///     .build();
///
/// assert_eq!(doc.guid(), "guid")
/// ```
#[derive(Clone, Debug)]
pub struct DocOptions {
    pub guid: String,
    pub client_id: u64,
    pub gc: bool,
}

impl Default for DocOptions {
    fn default() -> Self {
        if cfg!(any(test, feature = "bench")) {
            Self {
                client_id: 1,
                guid: "test".into(),
                gc: true,
            }
        } else {
            Self {
                client_id: random_client_id(),
                guid: nanoid::nanoid!(),
                gc: true,
            }
        }
    }
}

impl DocOptions {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_client_id(mut self, client_id: u64) -> Self {
        self.client_id = client_id;
        self
    }

    pub fn with_guid(mut self, guid: String) -> Self {
        self.guid = guid;
        self
    }

    pub fn auto_gc(mut self, gc: bool) -> Self {
        self.gc = gc;
        self
    }

    pub fn build(self) -> Doc {
        Doc::with_options(self)
    }
}

impl From<DocOptions> for Any {
    fn from(value: DocOptions) -> Self {
        Any::Object(Box::new(HashMap::from_iter([
            ("gc".into(), value.gc.into()),
            ("guid".into(), value.guid.into()),
        ])))
    }
}

impl TryFrom<Any> for DocOptions {
    type Error = JwstCodecError;

    fn try_from(value: Any) -> Result<Self, Self::Error> {
        match value {
            Any::Object(map) => {
                let mut options = DocOptions::default();
                for (key, value) in *map {
                    match key.as_str() {
                        "gc" => {
                            options.gc = bool::try_from(value)?;
                        }
                        "guid" => {
                            options.guid = String::try_from(value)?;
                        }
                        _ => {}
                    }
                }

                Ok(options)
            }
            _ => Err(JwstCodecError::UnexpectedType("Object")),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Doc {
    opts: DocOptions,

    pub(crate) store: StoreRef,
}

// Documents and type handles are shared across threads; every call takes the
// store lock itself.
const _: fn() = || {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<Doc>();
    send_sync::<Array>();
    send_sync::<Map>();
    send_sync::<Text>();
    send_sync::<Value>();
    send_sync::<Update>();
};

impl Default for Doc {
    fn default() -> Self {
        Doc::new()
    }
}

impl PartialEq for Doc {
    fn eq(&self, other: &Self) -> bool {
        self.client() == other.client()
    }
}

impl Doc {
    pub fn new() -> Self {
        Self::with_options(DocOptions::default())
    }

    pub fn with_options(options: DocOptions) -> Self {
        let store = Arc::new(RwLock::new(DocStore::with_client(options.client_id)));

        Self { opts: options, store }
    }

    pub fn with_client(client_id: u64) -> Self {
        DocOptions::new().with_client_id(client_id).build()
    }

    pub fn client(&self) -> Client {
        self.store.read().unwrap().client()
    }

    pub fn set_client(&mut self, client_id: u64) {
        self.store.write().unwrap().set_client(client_id);
    }

    pub fn renew_client(&mut self) {
        self.set_client(random_client_id());
    }

    pub fn clients(&self) -> Vec<u64> {
        self.store.read().unwrap().clients()
    }

    pub fn history(&self) -> StoreHistory {
        let history = StoreHistory::new(&self.store);
        history.resolve();
        history
    }

    #[cfg(feature = "debug")]
    pub fn store_status(&self) -> DocStoreStatus {
        let store = self.store.read().unwrap();

        let mut status = DocStoreStatus {
            clients: store.items.len(),
            nodes: store.total_nodes(),
            items: 0,
            gc_nodes: 0,
            skip_nodes: 0,
            deleted_items: 0,
            type_contents: 0,
            any_contents: 0,
            string_contents: 0,
            json_contents: 0,
            binary_contents: 0,
            deleted_contents: 0,
            other_contents: 0,
            delete_sets: store.total_delete_sets(),
            types: store.total_types(),
            dangling_types: store.total_dangling_types(),
            pending_nodes: store.total_pending_nodes(),
            changed_types: store.changed.len(),
            changed_keys: store.changed.values().map(Vec::len).sum(),
        };

        for node in store.items.values().flatten() {
            match node {
                Node::GC(_) => status.gc_nodes += 1,
                Node::Skip(_) => status.skip_nodes += 1,
                Node::Item(item) => {
                    status.items += 1;
                    let item = unsafe { item.get_unchecked() };
                    status.deleted_items += usize::from(item.deleted());
                    match &item.content {
                        Content::Type(_) => status.type_contents += 1,
                        Content::Any(_) => status.any_contents += 1,
                        Content::String(_) => status.string_contents += 1,
                        Content::Json(_) => status.json_contents += 1,
                        Content::Binary(_) => status.binary_contents += 1,
                        Content::Deleted(_) => status.deleted_contents += 1,
                        _ => status.other_contents += 1,
                    }
                }
            }
        }

        status
    }

    #[cfg(feature = "debug")]
    pub fn clear_change_tracking(&self) {
        self.store.write().unwrap().changed.clear();
    }

    pub fn store_compare(&self, other: &Doc) -> bool {
        if Arc::ptr_eq(&self.store, &other.store) {
            return true;
        }
        let store = self.store.read().unwrap();
        let other_store = other.store.read().unwrap();

        store.deep_compare(&other_store)
    }

    pub fn options(&self) -> &DocOptions {
        &self.opts
    }

    pub fn guid(&self) -> &str {
        self.opts.guid.as_str()
    }

    pub fn has_pending_updates(&self) -> bool {
        self.store.read().unwrap().pending.is_some()
    }

    /// Whether a root has visible sequence content, without assigning its type.
    pub fn root_has_sequence_content(&self, name: &str) -> bool {
        self.store
            .read()
            .unwrap()
            .types
            .get(name)
            .is_some_and(|root| root.ty().is_some_and(|ty| ty.len > 0))
    }

    // TODO:
    //   provide a better way instead of `_v1` methods
    //   when implementing `v2` binary format
    pub fn try_from_binary_v1<T: AsRef<[u8]>>(binary: T) -> JwstCodecResult<Self> {
        Self::try_from_binary_v1_with_options(binary, DocOptions::default())
    }

    pub fn try_from_binary_v1_with_options<T: AsRef<[u8]>>(binary: T, options: DocOptions) -> JwstCodecResult<Self> {
        let mut doc = Doc::with_options(options);
        doc.apply_update_from_binary_v1(binary)?;
        Ok(doc)
    }

    pub fn apply_update_from_binary_v1<T: AsRef<[u8]>>(&mut self, binary: T) -> JwstCodecResult {
        let mut decoder = RawDecoder::new(binary.as_ref());
        let update = Update::read(&mut decoder)?;
        self.apply_update(update)
    }

    pub fn apply_update(&mut self, update: Update) -> JwstCodecResult {
        let mut store = self.store.write().unwrap();
        // collect the types this update changes on their own
        let changed_before = std::mem::take(&mut store.changed);

        let result = Self::integrate_update(&mut store, &self.store, update);
        if result.is_ok() {
            store.optimize(self.opts.gc);
        }

        let changed = std::mem::replace(&mut store.changed, changed_before);
        // Remote changes move items under the search markers of the types
        // they touch, also when the update failed half way; Yjs drops those
        // markers after a remote transaction (`AbstractType._callObserver`).
        for (ty, keys) in changed {
            // SAFETY: store write lock held, no type borrowed.
            if let Some(mut ty) = unsafe { ty.ty_mut() }
                && let Some(markers) = &mut ty.markers
            {
                markers.clear();
            }
            store.changed.entry(ty).or_default().extend(keys);
        }

        result
    }

    fn integrate_update(store: &mut DocStore, store_ref: &StoreRef, mut update: Update) -> JwstCodecResult {
        let mut retry = false;

        loop {
            for (mut s, offset) in update.iter(store.get_state_vector()) {
                if let Node::Item(item) = &mut s {
                    debug_assert!(item.is_owned());
                    let mut item = unsafe { item.get_mut_unchecked() };
                    store.repair(&mut item, store_ref.clone())?;
                }
                store.integrate(s, offset, None)?;
            }

            for (client, range) in update.delete_set_iter(store.get_state_vector()) {
                store.delete_range(client, range)?;
            }

            if let Some(mut pending_update) = store.pending.take() {
                if pending_update
                    .missing_state
                    .iter()
                    .any(|(client, clock)| *clock < store.get_state(*client))
                {
                    // new update has been applied to the doc, need to
                    // re-integrate
                    retry = true;
                }

                for (client, range) in pending_update.delete_set_iter(store.get_state_vector()) {
                    store.delete_range(client, range)?;
                }
                // The iterator moves unavailable deletion tails into
                // pending_delete_set. Carry them into the next merge even if
                // this update was unrelated; their target structs may arrive in
                // a later batch.
                pending_update.delete_set = std::mem::take(&mut pending_update.pending_delete_set);

                if update.is_pending_empty() {
                    update = pending_update;
                } else {
                    // drain all pending state to pending update for later
                    // iteration
                    update.drain_pending_state();
                    Update::merge_into(&mut update, [pending_update]);
                }
            } else {
                // no pending update at store

                // no pending update in current iteration
                // thank god, all clean
                if update.is_pending_empty() {
                    break;
                } else {
                    // need to turn all pending state into update for later
                    // iteration
                    update.drain_pending_state();
                    retry = false;
                };
            }

            // can't integrate any more, save the pending update
            if !retry {
                if !update.is_empty() {
                    store.pending.replace(update);
                }
                break;
            }
        }

        Ok(())
    }

    pub fn keys(&self) -> Vec<String> {
        let store = self.store.read().unwrap();
        store.types.keys().cloned().collect()
    }

    pub fn get_or_create_text<S: AsRef<str>>(&self, name: S) -> JwstCodecResult<Text> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::Text)
            .set_name(name.as_ref().to_string())
            .build()
    }

    /// Creates an editable preliminary text. Its current contents enter the
    /// document atomically when inserted into a mounted type. Before then, its
    /// edits have no document identity and do not affect updates or state
    /// vectors.
    pub fn create_text(&self) -> JwstCodecResult<Text> {
        YTypeBuilder::new(self.store.clone()).with_kind(YTypeKind::Text).build()
    }

    pub fn get_or_create_array<S: AsRef<str>>(&self, str: S) -> JwstCodecResult<Array> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::Array)
            .set_name(str.as_ref().to_string())
            .build()
    }

    /// Creates an editable preliminary array. Its current contents enter the
    /// document atomically when inserted into a mounted type. Before then, its
    /// edits have no document identity and do not affect updates or state
    /// vectors.
    pub fn create_array(&self) -> JwstCodecResult<Array> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::Array)
            .build()
    }

    pub fn get_or_create_map<S: AsRef<str>>(&self, str: S) -> JwstCodecResult<Map> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::Map)
            .set_name(str.as_ref().to_string())
            .build()
    }

    /// Creates an editable preliminary map. Its current contents enter the
    /// document atomically when inserted into a mounted type. Before then, its
    /// edits have no document identity and do not affect updates or state
    /// vectors.
    pub fn create_map(&self) -> JwstCodecResult<Map> {
        YTypeBuilder::new(self.store.clone()).with_kind(YTypeKind::Map).build()
    }

    pub fn get_map(&self, str: &str) -> JwstCodecResult<Map> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::Map)
            .set_name(str.to_string())
            .build_exists()
    }

    pub fn encode_update_v1(&self) -> JwstCodecResult<Vec<u8>> {
        self.encode_state_as_update_v1(&StateVector::default())
    }

    pub fn encode_state_as_update_v1(&self, sv: &StateVector) -> JwstCodecResult<Vec<u8>> {
        // The diff shares items with the store, so it is encoded under the
        // same read lock.
        let store = self.store.read().unwrap();
        let update = store.diff_state_vector(sv, true)?;

        let mut encoder = RawEncoder::default();
        update.write(&mut encoder)?;
        Ok(encoder.into_inner())
    }

    pub fn encode_update(&self) -> JwstCodecResult<Update> {
        self.encode_state_as_update(&StateVector::default())
    }

    /// The returned [Update] is detached from this document.
    pub fn encode_state_as_update(&self, sv: &StateVector) -> JwstCodecResult<Update> {
        Update::decode_v1(self.encode_state_as_update_v1(sv)?)
    }

    pub fn get_state_vector(&self) -> StateVector {
        self.store.read().unwrap().get_state_vector()
    }

    pub fn get_delete_sets(&self) -> DeleteSet {
        self.store.read().unwrap().get_delete_sets()
    }

    /// Garbage-collects every deleted struct and merges the whole store.
    /// Updates already collect what they delete; this is the explicit full
    /// pass.
    pub fn gc(&self) -> JwstCodecResult<()> {
        self.store.write().unwrap().optimize_all();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fuzz_update_with_gced_parent_round_trips() {
        // The decode_doc_update fuzz case leaves descendants of a type whose
        // own parent is missing. Its descendants still consume their clocks.
        let update = [
            0x01, 0x07, 0x00, 0x00, 0x27, 0x07, 0x00, 0x27, 0x00, 0x00, 0x00, 0x83, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00,
            0x83, 0x00, 0x00, 0x00, 0x01, 0x73, 0x00, 0x00, 0x74, 0x80, 0x8f, 0x00, 0x00, 0x09, 0x00,
        ];

        loom_model!({
            for auto_gc in [false, true] {
                let options = DocOptions::default().auto_gc(auto_gc);
                let mut doc = Doc::with_options(options.clone());
                doc.apply_update_from_binary_v1(update).unwrap();

                let expected = StateVector::from([(0, 146)]);
                assert_eq!(doc.get_state_vector(), expected);
                assert!(!doc.has_pending_updates());

                let encoded = doc.encode_update_v1().unwrap();
                let mut reopened = Doc::with_options(options);
                reopened.apply_update_from_binary_v1(&encoded).unwrap();
                assert_eq!(reopened.get_state_vector(), expected);
                assert!(!reopened.has_pending_updates());
                assert_eq!(reopened.encode_update_v1().unwrap(), encoded);
            }
        });
    }

    #[test]
    fn test_duplicate_update_with_gced_parent() {
        loom_model!(64 << 10, {
            let mut doc = Doc::with_client(303);
            // Accepted by Yjs 13.6.21 and 13.6.33: the last update repeats
            // already-GCed type structs before introducing their descendants.
            for (index, hex) in [
                "0101ca01012700ca010001740200",
                "0101ca01002701036d617006706172656e740100",
                "010465002101036d617006706172656e740100030801056172726179017601066f70617175657d032101036d61700c61667465722d72656d6f74650102ca010200050702650200040501",
                "0109ca01002701036d617006706172656e74012700ca01000174022700ca01000161002700ca0100016d010500ca0101097b22726566223a367d2801036d61700179017d8f012801036d61700178017d102800ca0103016b017d0244ca010401610165010004",
            ]
            .iter()
            .enumerate()
            {
                let bytes = (0..hex.len())
                    .step_by(2)
                    .map(|offset| u8::from_str_radix(&hex[offset..offset + 2], 16).unwrap())
                    .collect::<Vec<_>>();
                let result = doc.apply_update_from_binary_v1(bytes);
                assert!(result.is_ok(), "update {}: {result:?}", index + 1);
            }
            assert!(!doc.has_pending_updates());
            let expected = StateVector::from([(101, 6), (202, 9)]);
            assert_eq!(doc.get_state_vector(), expected);
            let restored = Doc::try_from_binary_v1(doc.encode_update_v1().unwrap()).unwrap();
            assert_eq!(restored.get_state_vector(), expected);
            assert!(!restored.has_pending_updates());
        });
    }

    #[test]
    fn test_duplicate_types_with_new_grandchild_after_gc() {
        loom_model!({
            let source = Doc::with_client(202);
            let mut root = source.get_or_create_map("map").unwrap();
            let mut parent = source.create_map().unwrap();
            let mut child = source.create_text().unwrap();
            root.insert("parent".into(), parent.clone()).unwrap();
            parent.insert("child".into(), child.clone()).unwrap();

            let mut target = Doc::with_client(101);
            target
                .apply_update_from_binary_v1(source.encode_update_v1().unwrap())
                .unwrap();
            target.get_or_create_map("map").unwrap().remove("parent");
            target.gc().unwrap();
            assert!(target.store.read().unwrap().get_node(Id::new(202, 1)).unwrap().is_gc());

            child.insert(0, "x").unwrap();
            root.insert("tail".into(), 1).unwrap();
            // Full update repeats the parent and child types and adds a new
            // grandchild plus a following struct to verify contiguous clocks.
            target
                .apply_update_from_binary_v1(source.encode_update_v1().unwrap())
                .unwrap();
            assert!(target.store.read().unwrap().get_node(Id::new(202, 2)).unwrap().is_gc());
            assert_eq!(target.get_state_vector(), StateVector::from([(202, 4)]));
            assert!(!target.has_pending_updates());
            assert_eq!(
                target.get_or_create_map("map").unwrap().get("tail"),
                Some(Value::Any(Any::Integer(1)))
            );
            target.store.read().unwrap().self_check().unwrap();
        });
    }

    #[test]
    fn test_set_client_updates_item_author() {
        loom_model!({
            let mut doc = Doc::with_client(5);
            let mut map = doc.get_or_create_map("map").unwrap();
            map.insert("before".into(), 1).unwrap();
            doc.set_client(77);
            map.insert("after".into(), 2).unwrap();
            assert_eq!(doc.client(), 77);
            assert_eq!(doc.get_state_vector(), StateVector::from([(5, 1), (77, 1)]));
        });
    }

    #[test]
    fn test_renew_client_updates_item_author() {
        loom_model!({
            let mut doc = Doc::with_client(0);
            let mut map = doc.get_or_create_map("map").unwrap();
            doc.renew_client();
            let client = doc.client();
            assert!((1..=(1_u64 << 53) - 1).contains(&client));
            map.insert("k".into(), 1).unwrap();
            assert_eq!(doc.get_state_vector(), StateVector::from([(client, 1)]));
        });
    }

    #[test]
    fn test_clone_set_client_uses_shared_author() {
        loom_model!({
            let doc = Doc::with_client(5);
            let mut other = doc.clone();
            other.set_client(77);
            doc.get_or_create_text("text").unwrap().insert(0, "x").unwrap();
            assert_eq!(doc.get_state_vector(), StateVector::from([(77, 1)]));
            assert_eq!(doc.client(), 77);
            assert_eq!(doc, other);
            assert_eq!(doc, Doc::with_client(77));
        });
    }

    #[test]
    fn test_clone_renew_client_uses_shared_author() {
        loom_model!({
            let doc = Doc::with_client(0);
            let mut other = doc.clone();
            other.renew_client();
            let client = other.client();
            doc.get_or_create_text("text").unwrap().insert(0, "x").unwrap();
            assert_eq!(doc.get_state_vector(), StateVector::from([(client, 1)]));
            assert_eq!(doc.client(), client);
            assert_eq!(doc, other);
        });
    }

    #[test]
    fn test_default_test_client_is_fixed() {
        assert_eq!(DocOptions::default().client_id, 1);
        assert_eq!(DocOptions::default().guid, "test");
    }

    #[test]
    fn test_yjs_typed_embeds_with_declared_text_roots() {
        let bytes = yjs_fixture("text-type-embeds");
        loom_model!({
            let mut doc = DocOptions {
                client_id: 202,
                guid: "typed-embed-wire".into(),
                gc: true,
            }
            .build();
            let text = doc.get_or_create_text("typed_text").unwrap();
            let _: XMLText = YTypeBuilder::new(doc.store.clone())
                .with_kind(YTypeKind::XMLText)
                .set_name("typed_xml_text".into())
                .build()
                .unwrap();
            doc.apply_update_from_binary_v1(&bytes).unwrap();
            assert!(!doc.has_pending_updates());
            assert_eq!(text.to_string(), "leftright");
            assert_eq!(text.len(), 12);
            let store = doc.store.read().unwrap();
            for name in ["typed_text", "typed_xml_text"] {
                let root = store.types[name].ty().unwrap();
                assert_eq!(root.len, 12);
                let mut children = Vec::new();
                let mut item = root.start.clone();
                while let Some(node) = item.get() {
                    if let Content::Type(child) = &node.content {
                        children.push(child.ty().unwrap().kind());
                    }
                    item = node.right.clone();
                }
                assert_eq!(children, vec![YTypeKind::Map, YTypeKind::Array, YTypeKind::Text]);
            }
        });
    }

    #[test]
    fn test_encode_state_as_update() {
        loom_model!(64 << 10, {
            let binary = yjs_fixture("map");
            let binary_new = yjs_fixture("array-peer");
            let mut doc = Doc::try_from_binary_v1(&binary).unwrap();
            let mut doc_new = Doc::try_from_binary_v1(&binary_new).unwrap();

            let diff_update = doc_new.encode_state_as_update_v1(&doc.get_state_vector()).unwrap();

            let diff_update_reverse = doc.encode_state_as_update_v1(&doc_new.get_state_vector()).unwrap();

            doc.apply_update_from_binary_v1(diff_update).unwrap();
            doc_new.apply_update_from_binary_v1(diff_update_reverse).unwrap();

            assert_eq!(doc.encode_update_v1().unwrap(), doc_new.encode_update_v1().unwrap());
        });

        for (value, prefixes, tails) in [
            ("abcd", ["", "a", "ab", "abc", "abcd"], ["abcd", "bcd", "cd", "d", ""]),
            (
                "a😀b",
                ["", "a", "a\u{FFFD}", "a😀", "a😀b"],
                ["a😀b", "😀b", "\u{FFFD}b", "b", ""],
            ),
        ] {
            for clock in 0..=5 {
                loom_model!({
                    let source = Doc::with_client(1);
                    source.get_or_create_text("text").unwrap().insert(0, value).unwrap();
                    let original = source.encode_update_v1().unwrap();
                    let bytes = source
                        .encode_state_as_update_v1(&StateVector::from([(1, clock)]))
                        .unwrap();
                    assert_eq!(source.encode_update_v1().unwrap(), original);
                    let diff = Update::decode_v1(&bytes).unwrap();
                    if clock < 4 {
                        let node = &diff.structs[&1][0];
                        assert_eq!(node.clock(), clock);
                        assert_eq!(node.len(), 4 - clock);
                        let item = node.as_item();
                        let item = item.get().unwrap();
                        assert_eq!(item.origin_left_id, clock.checked_sub(1).map(|clock| Id::new(1, clock)));
                        assert_eq!(item.content, Content::String(tails[clock as usize].into()));
                    } else {
                        assert!(diff.structs.is_empty());
                    }
                    let mut target = Doc::with_client(1);
                    let prefix = prefixes[clock.min(4) as usize];
                    target.get_or_create_text("text").unwrap().insert(0, prefix).unwrap();
                    target.apply_update_from_binary_v1(&bytes).unwrap();
                    assert_eq!(
                        target.get_or_create_text("text").unwrap().to_string(),
                        format!("{prefix}{}", tails[clock.min(4) as usize])
                    );
                    assert_eq!(target.get_state_vector(), source.get_state_vector());
                });
            }
        }

        loom_model!({
            let source = Doc::with_client(1);
            source
                .get_or_create_text("text")
                .unwrap()
                .insert(0, "abcdefghij")
                .unwrap();
            let mut pending = Doc::with_client(2);
            pending
                .apply_update_from_binary_v1(source.encode_state_as_update_v1(&StateVector::from([(1, 6)])).unwrap())
                .unwrap();
            let mut deletion = Update::default();
            deletion.delete_set.add(1, 8, 2);
            pending.apply_update(deletion).unwrap();
            for clock in [0, 4, 6, 7, 10, 11] {
                let diff = Update::decode_v1(
                    pending
                        .encode_state_as_update_v1(&StateVector::from([(1, clock)]))
                        .unwrap(),
                )
                .unwrap();
                if clock < 10 {
                    let node = &diff.structs[&1][0];
                    assert_eq!(node.clock(), clock.max(6));
                    assert_eq!(node.len(), 10 - clock.max(6));
                } else {
                    assert!(diff.structs.is_empty());
                }
                assert_eq!(diff.delete_set.get(&1), Some(&OrderRange::from(8..10)));
            }

            let prefix = Doc::with_client(1);
            prefix.get_or_create_text("text").unwrap().insert(0, "abcd").unwrap();
            pending
                .apply_update_from_binary_v1(prefix.encode_state_as_update_v1(&StateVector::from([(1, 2)])).unwrap())
                .unwrap();
            let diff =
                Update::decode_v1(pending.encode_state_as_update_v1(&StateVector::from([(1, 5)])).unwrap()).unwrap();
            assert_eq!(diff.structs[&1][0].clock(), 6);
            assert_eq!(diff.structs[&1][0].len(), 4);
            assert_eq!(diff.delete_set.get(&1), Some(&OrderRange::from(8..10)));
        });

        loom_model!({
            let source = Doc::with_client(1);
            source
                .get_or_create_text("text")
                .unwrap()
                .insert(0, "abcdefgh")
                .unwrap();
            let mut delete_only = Doc::with_client(2);
            let mut deletion = Update::default();
            deletion.delete_set.add(1, 5, 3);
            delete_only.apply_update(deletion).unwrap();
            assert!(delete_only.has_pending_updates());
            let unrelated = Doc::with_client(3);
            unrelated
                .get_or_create_map("map")
                .unwrap()
                .insert("value".into(), 42)
                .unwrap();
            delete_only
                .apply_update_from_binary_v1(unrelated.encode_update_v1().unwrap())
                .unwrap();
            assert!(delete_only.has_pending_updates());
            let saved = delete_only
                .encode_state_as_update_v1(&StateVector::from([(3, 1)]))
                .unwrap();
            let mut restored = Doc::try_from_binary_v1(saved).unwrap();
            restored
                .apply_update_from_binary_v1(source.encode_update_v1().unwrap())
                .unwrap();
            assert!(!restored.has_pending_updates());
            assert_eq!(restored.get_or_create_text("text").unwrap().to_string(), "abcde");
        });

        loom_model!({
            let source = Doc::with_client(1);
            source
                .get_or_create_text("text")
                .unwrap()
                .insert(0, "abcdefgh")
                .unwrap();
            let mut partial = Doc::with_client(2);
            partial.get_or_create_text("local").unwrap().insert(0, "abcd").unwrap();
            partial
                .apply_update_from_binary_v1(source.encode_state_as_update_v1(&StateVector::from([(1, 6)])).unwrap())
                .unwrap();
            let mut deletion = Update::default();
            deletion.delete_set.add(1, 5, 3);
            partial.apply_update(deletion).unwrap();
            assert!(partial.has_pending_updates());

            let diff = partial.encode_state_as_update_v1(&StateVector::from([(2, 2)])).unwrap();
            let mut restored = Doc::with_client(2);
            restored.get_or_create_text("local").unwrap().insert(0, "ab").unwrap();
            restored.apply_update_from_binary_v1(diff).unwrap();
            assert!(restored.has_pending_updates());
            restored
                .apply_update_from_binary_v1(source.encode_update_v1().unwrap())
                .unwrap();
            assert!(!restored.has_pending_updates());
            assert_eq!(restored.get_or_create_text("local").unwrap().to_string(), "abcd");
            assert_eq!(restored.get_or_create_text("text").unwrap().to_string(), "abcde");
        });
    }

    #[test]
    #[cfg_attr(any(miri, loom), ignore)]
    fn test_array_create() {
        let json = serde_json::json!([42.0, -42.0, true, false, "hello", "world", [1.0]]);

        {
            let doc = Doc::try_from_binary_v1(yjs_fixture("mixed-array")).unwrap();
            let array = doc.get_or_create_array("abc").unwrap();
            let config = assert_json_diff::Config::new(assert_json_diff::CompareMode::Strict)
                .numeric_mode(assert_json_diff::NumericMode::AssumeFloat);
            assert_json_diff::assert_json_matches!(serde_json::to_value(&array).unwrap(), json, config);
        }

        {
            let binary = {
                let doc = Doc::new();
                let mut array = doc.get_or_create_array("abc").unwrap();
                array.insert(0, 42).unwrap();
                array.insert(1, -42).unwrap();
                array.insert(2, true).unwrap();
                array.insert(3, false).unwrap();
                array.insert(4, "hello").unwrap();
                array.insert(5, "world").unwrap();

                let mut sub_array = doc.create_array().unwrap();
                array.insert(6, sub_array.clone()).unwrap();
                sub_array.insert(0, 1).unwrap();

                doc.encode_update_v1().unwrap()
            };

            let mut doc = Doc::new();
            let array = doc.get_or_create_array("abc").unwrap();
            doc.apply_update_from_binary_v1(binary).unwrap();

            let list = array.iter().collect::<Vec<_>>();

            assert!(list.len() == 7);
            assert!(matches!(list[6], Value::Array(_)));
        }

        {
            let binary_detached = {
                let doc = Doc::new();
                let mut array = doc.get_or_create_array("abc").unwrap();
                array.insert(0, 42).unwrap();
                array.insert(1, -42).unwrap();
                array.insert(2, true).unwrap();
                array.insert(3, false).unwrap();
                array.insert(4, "hello").unwrap();
                array.insert(5, "world").unwrap();

                let mut sub_array = doc.create_array().unwrap();
                sub_array.insert(0, 1).unwrap();
                array.insert(6, sub_array.clone()).unwrap();

                doc.encode_update_v1().unwrap()
            };

            let detached_doc = Doc::try_from_binary_v1(binary_detached).unwrap();
            assert!(detached_doc.root_has_sequence_content("abc"));
            assert!(!detached_doc.root_has_sequence_content("missing"));
            let mut metadata = detached_doc.get_or_create_map("metadata").unwrap();
            metadata.insert("key".into(), "value").unwrap();
            assert!(!detached_doc.root_has_sequence_content("metadata"));
            let detached_array = detached_doc.get_or_create_array("abc").unwrap();
            let detached_sub_array = match detached_array.get(6).unwrap() {
                Value::Array(arr) => arr,
                _ => panic!("expected array at index 6"),
            };
            assert_eq!(detached_sub_array.get(0).unwrap(), Value::Any(1.0.into()));
        }
    }

    #[test]
    fn test_repeated_applied_pending_update() {
        // generate a pending update
        // update: [1, 1, 1, 0, 39, 1, 4, 116, 101, 115, 116, 3, 109, 97, 112,
        // 1, 0] update: [1, 1, 1, 1, 40, 0, 1, 0, 11, 115, 117, 98, 95,
        // 109, 97, 112, 95, 107, 101, 121, 1, 119, 13, 115, 117, 98,
        // 95, 109, 97, 112, 95, 118, 97, 108, 117, 101, 0]
        loom_model!({
            let mut doc = Doc::default();

            doc.apply_update_from_binary_v1(vec![
                1, 1, 1, 1, 40, 0, 1, 0, 11, 115, 117, 98, 95, 109, 97, 112, 95, 107, 101, 121, 1, 119, 13, 115, 117,
                98, 95, 109, 97, 112, 95, 118, 97, 108, 117, 101, 0,
            ])
            .unwrap();
            assert!(doc.has_pending_updates());

            let pending_size = doc
                .store
                .read()
                .unwrap()
                .pending
                .as_ref()
                .unwrap()
                .structs
                .iter()
                .map(|s| s.1.len())
                .sum::<usize>();
            doc.apply_update_from_binary_v1(vec![
                1, 1, 1, 1, 40, 0, 1, 0, 11, 115, 117, 98, 95, 109, 97, 112, 95, 107, 101, 121, 1, 119, 13, 115, 117,
                98, 95, 109, 97, 112, 95, 118, 97, 108, 117, 101, 0,
            ])
            .unwrap();

            // pending nodes should not grow up after apply same pending update
            assert_eq!(
                pending_size,
                doc.store
                    .read()
                    .unwrap()
                    .pending
                    .as_ref()
                    .unwrap()
                    .structs
                    .iter()
                    .map(|s| s.1.len())
                    .sum::<usize>()
            );
        });
    }

    #[test]
    fn test_update_from_vec_ref() {
        loom_model!(64 << 10, {
            let doc = Doc::new();

            let mut text = doc.get_or_create_text("text").unwrap();
            text.insert(0, "hello world").unwrap();

            let mut root = doc.get_or_create_map("root").unwrap();
            let mut child = doc.create_map().unwrap();
            child.insert("k".to_string(), "v").unwrap();
            root.insert("child".to_string(), child.clone()).unwrap();

            let update = doc.encode_update_v1().unwrap();

            let doc = Doc::try_from_binary_v1(update).unwrap();
            let text = doc.get_or_create_text("text").unwrap();

            assert_eq!(&text.to_string(), "hello world");

            let root = doc.get_or_create_map("root").unwrap();
            if let Some(Value::Map(child)) = root.get("child") {
                assert!(
                    matches!(child.get("k"), Some(Value::Any(Any::String(s))) if s == "v"),
                    "expected nested map value to survive apply_update"
                );
            } else {
                panic!("expected nested map to survive apply_update");
            }
        });
    }

    #[test]
    #[cfg_attr(any(miri, loom), ignore)]
    fn test_apply_update() {
        let updates = [
            include_bytes!("../fixtures/basic.bin").to_vec(),
            include_bytes!("../fixtures/database.bin").to_vec(),
            include_bytes!("../fixtures/large.bin").to_vec(),
            include_bytes!("../fixtures/with-subdoc.bin").to_vec(),
            include_bytes!("../fixtures/edge-case-left-right-same-node.bin").to_vec(),
        ];

        for update in updates {
            let mut doc = Doc::new();
            doc.apply_update_from_binary_v1(&update).unwrap();
        }
    }

    #[test]
    #[cfg_attr(loom, ignore)]
    fn test_reject_cyclic_type_nesting() {
        // found by fuzzing (decode_doc_update): this corrupt update nests a
        // type into its own descendant. The unified wire decoder rejects it
        // even earlier than the cyclic-parent check, on a zero-length
        // struct; wire-valid cyclic updates are covered by the read-only
        // differential tests.
        let update = [
            0x01, 0x07, 0x00, 0x00, 0x27, 0x07, 0x00, 0x00, 0x00, 0x00, 0x83, 0x00, 0x00, 0x00, 0x01, 0x73, 0x00, 0x00,
            0x74, 0x00, 0x00, 0x61, 0x00, 0x01, 0x20, 0x01, 0x00, 0x00, 0x80, 0x00, 0x07, 0x01, 0x80, 0x00, 0x00, 0x00,
            0x09, 0x00,
        ];

        assert!(matches!(
            Doc::try_from_binary_v1(update),
            Err(JwstCodecError::IncompleteDocument(message)) if message == "zero-length struct"
        ));
    }
}
