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
/// let doc = DocOptions::from_identity(1, "guid".into()).build();
///
/// assert_eq!(doc.guid(), "guid")
/// ```
#[derive(Clone, Debug)]
pub struct DocOptions {
    pub guid: String,
    pub client_id: u64,
    pub gc: bool,
}

/// A random client ID and GUID (fixed ones in tests and benches). Without the
/// `random` feature, use [DocOptions::from_identity].
#[cfg(any(test, feature = "bench", feature = "random"))]
impl Default for DocOptions {
    fn default() -> Self {
        #[cfg(any(test, feature = "bench"))]
        return Self::from_identity(1, "test".into());
        #[cfg(not(any(test, feature = "bench")))]
        Self::from_identity(random_client_id(), nanoid::nanoid!())
    }
}

impl DocOptions {
    #[cfg(any(test, feature = "bench", feature = "random"))]
    pub fn new() -> Self {
        Self::default()
    }

    /// Options with the client ID and GUID the host chose, the entry for
    /// builds without the `random` feature (such as wasm32-unknown-unknown,
    /// where the host draws them from `crypto.getRandomValues`). The host
    /// gives every replica its own client ID, below 2^53 to stay exact in
    /// JavaScript. 0 is an ordinary client ID.
    pub fn from_identity(client_id: u64, guid: String) -> Self {
        Self {
            client_id,
            guid,
            gc: true,
        }
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

impl DocOptions {
    /// Applies subdocument options as Yjs `createDocFromOpts` reads them from
    /// a `ContentDoc`: anything that is not an object, and any key of the
    /// wrong type, leaves the current value in place instead of failing.
    pub(crate) fn with_wire_options(mut self, opts: &Any) -> Self {
        if let Any::Object(map) = opts {
            match map.get("gc") {
                Some(Any::True) => self.gc = true,
                Some(Any::False) => self.gc = false,
                _ => {}
            }
            if let Some(Any::String(guid)) = map.get("guid") {
                self.guid = guid.clone();
            }
        }
        self
    }
}

/// Options read from their `Any` form, which carries no client ID: with the
/// `random` feature the document gets a random one. Without it there is no
/// such conversion, the host builds the options with
/// [DocOptions::from_identity].
#[cfg(feature = "random")]
impl TryFrom<Any> for DocOptions {
    type Error = JwstCodecError;

    fn try_from(value: Any) -> Result<Self, Self::Error> {
        DocOptions::default().read_any(value)
    }
}

#[cfg(feature = "random")]
impl DocOptions {
    /// Applies the fields of the `Any` form (`gc`, `guid`) to these options.
    fn read_any(mut self, value: Any) -> JwstCodecResult<Self> {
        match value {
            Any::Object(map) => {
                for (key, value) in *map {
                    match key.as_str() {
                        "gc" => {
                            self.gc = bool::try_from(value)?;
                        }
                        "guid" => {
                            self.guid = String::try_from(value)?;
                        }
                        _ => {}
                    }
                }
                Ok(self)
            }
            _ => Err(JwstCodecError::UnexpectedType("Object")),
        }
    }
}

/// The subdocument an item holds, from its GUID and options. They carry no
/// client ID: with the `random` feature it gets a random one; without it the
/// document waits for the host to set one ([Doc::client_required]).
pub(crate) fn subdocument(guid: &str, opts: &Any) -> Doc {
    #[cfg(feature = "random")]
    let options = DocOptions::default();
    #[cfg(not(feature = "random"))]
    let options = DocOptions::from_identity(0, String::new());
    let doc = options
        // opts come from the wire unchecked; Yjs spreads whatever it finds
        // into the subdocument options
        .with_wire_options(opts)
        // The GUID lives outside opts on the wire; projecting a subdoc must
        // preserve its identity instead of generating a new one.
        .with_guid(guid.into())
        .build();
    #[cfg(not(feature = "random"))]
    or_released(write_store(&doc.store).map(|mut store| store.client_required = true));
    doc
}

#[derive(Debug, Clone)]
pub struct Doc {
    opts: DocOptions,
    events: Arc<EventHub>,

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
    send_sync::<XMLElement>();
    send_sync::<XMLFragment>();
    send_sync::<XMLText>();
    send_sync::<XMLHook>();
    send_sync::<Value>();
    send_sync::<Update>();
};

#[cfg(any(test, feature = "bench", feature = "random"))]
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
    #[cfg(any(test, feature = "bench", feature = "random"))]
    pub fn new() -> Self {
        Self::with_options(DocOptions::default())
    }

    pub fn with_options(options: DocOptions) -> Self {
        let mut store = DocStore::with_client(options.client_id);
        store.gc = options.gc;
        let events = store.events.clone();
        let store = Arc::new(RwLock::new(store));

        Self {
            opts: options,
            events,
            store,
        }
    }

    /// A document with `client_id` and a random GUID.
    #[cfg(any(test, feature = "bench", feature = "random"))]
    pub fn with_client(client_id: u64) -> Self {
        DocOptions::new().with_client_id(client_id).build()
    }

    /// The client ID new structs are created with. It changes when a remote
    /// update shows another client using it.
    pub fn client(&self) -> Client {
        or_released(read_store(&self.store).map(|store| store.client()))
    }

    /// Whether the host has to set a client ID ([Doc::set_client]) before
    /// local transactions are accepted again; they fail with
    /// [JwstCodecError::ClientIdRequired] meanwhile. Only without the
    /// `random` feature, where the document cannot draw one itself, and only
    /// when no host assigned its current one: a subdocument read from a
    /// document (its options carry no client ID), or after a remote update
    /// showed another replica writing with this document's client ID (with
    /// `random` it switches to a random one, as Yjs does). A client ID the
    /// host passes, 0 included, is never questioned. Remote updates are still
    /// applied, and so is internal bookkeeping such as dropping an undo
    /// manager.
    pub fn client_required(&self) -> bool {
        or_released(read_store(&self.store).map(|store| store.client_required))
    }

    /// Sets the client ID new structs are created with (0 included); local
    /// transactions are accepted again ([Doc::client_required]).
    pub fn set_client(&mut self, client_id: u64) {
        or_released(write_store(&self.store).map(|mut store| store.set_client(client_id)));
    }

    #[cfg(feature = "random")]
    pub fn renew_client(&mut self) {
        self.set_client(random_client_id());
    }

    pub fn clients(&self) -> Vec<u64> {
        or_released(read_store(&self.store).map(|store| store.clients()))
    }

    pub fn history(&self) -> StoreHistory {
        let history = StoreHistory::new(&self.store);
        history.resolve();
        history
    }

    #[cfg(feature = "debug")]
    pub fn store_status(&self) -> DocStoreStatus {
        let store = read_store_or_panic(&self.store);

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
            changed_types: store.collector.changed.len(),
            changed_keys: store.collector.changed.values().map(Vec::len).sum(),
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
        or_released(write_store(&self.store).map(|mut store| store.collector.changed.clear()));
    }

    pub fn store_compare(&self, other: &Doc) -> bool {
        if Arc::ptr_eq(&self.store, &other.store) {
            return true;
        }
        let (store, other_store) =
            transaction::read_store_pair(&self.store, &other.store).unwrap_or_else(|err| panic!("{err}"));

        store.deep_compare(&other_store)
    }

    pub fn options(&self) -> &DocOptions {
        &self.opts
    }

    pub fn guid(&self) -> &str {
        self.opts.guid.as_str()
    }

    pub fn has_pending_updates(&self) -> bool {
        or_released(read_store(&self.store).map(|store| store.pending.is_some()))
    }

    /// Whether a root has visible sequence content, without assigning its type.
    pub fn root_has_sequence_content(&self, name: &str) -> bool {
        or_released(read_store(&self.store).map(|store| {
            store
                .types
                .get(name)
                .is_some_and(|root| root.ty().is_some_and(|ty| ty.len > 0))
        }))
    }

    // TODO:
    //   provide a better way instead of `_v1` methods
    //   when implementing `v2` binary format
    #[cfg(any(test, feature = "bench", feature = "random"))]
    pub fn try_from_binary_v1<T: AsRef<[u8]>>(binary: T) -> JwstCodecResult<Self> {
        Self::try_from_binary_v1_with_options(binary, DocOptions::default())
    }

    pub fn try_from_binary_v1_with_options<T: AsRef<[u8]>>(binary: T, options: DocOptions) -> JwstCodecResult<Self> {
        let mut doc = Doc::with_options(options);
        doc.apply_update_from_binary_v1(binary)?;
        Ok(doc)
    }

    /// Decodes and applies a remote Yjs Update V1, rejecting `Any` values
    /// nested deeper than [Any::DEFAULT_MAX_DEPTH] like [Update::decode_v1].
    /// For trusted updates nested deeper, decode them with
    /// [Update::decode_v1_with_max_any_depth] and call [Doc::apply_update].
    pub fn apply_update_from_binary_v1<T: AsRef<[u8]>>(&mut self, binary: T) -> JwstCodecResult {
        let mut decoder = RawDecoder::new(binary.as_ref());
        let update = Update::read(&mut decoder)?;
        self.apply_update(update)
    }

    /// Applies a remote update in a transaction of its own (not local, no
    /// origin).
    pub fn apply_update(&mut self, update: Update) -> JwstCodecResult {
        self.apply_update_with_origin(update, None)
    }

    /// Applies a remote update in a transaction of its own with `origin`.
    pub fn apply_update_with_origin(&self, update: Update, origin: impl Into<Option<Origin>>) -> JwstCodecResult {
        let store_ref = &self.store;
        transact_mut_with(store_ref, origin.into(), false, |tx| {
            // what the update itself declares, before pending structs join it
            tx.incoming = Some(IncomingUpdate::of(&update));
            Self::integrate_update(tx.store_mut(), store_ref, update)
        })
    }

    /// Applies an update authored locally outside this document (for
    /// example by a trusted renderer with a client ID of its own) as a local
    /// transaction with `origin`, so that history captures it like an edit
    /// made through this document; [Doc::apply_update] is for remote
    /// updates.
    ///
    /// The update is applied only when it can take effect completely: if it
    /// needs structs this document has not integrated (including ones still
    /// waiting in the document for their own dependencies), nothing is
    /// applied and [LocalUpdate::MissingDependencies] says from which clock
    /// of which client the caller has to resynchronize first. Otherwise the
    /// commit contains exactly what this update adds and deletes for the
    /// first time; remote updates waiting in the document that it unblocks
    /// are integrated after it, in a separate remote transaction. Applying an
    /// update again changes nothing and commits nothing.
    ///
    /// Use the renderer's commit update for the action being imported.
    /// A general synchronization diff can also contain earlier deletions,
    /// including changes from other peers.
    ///
    /// ```
    /// use std::sync::{Arc, Mutex};
    ///
    /// use y_octo::{DocOptions, LocalUpdate, Origin, UndoManager, UndoOptions, Update};
    ///
    /// let native = DocOptions::from_identity(101, "note".into()).build();
    /// let mut renderer = DocOptions::from_identity(202, "note".into()).build();
    /// let mut peer = DocOptions::from_identity(303, "note".into()).build();
    /// let mut text = native.get_or_create_text("body")?;
    /// text.insert(0, "Hello")?;
    /// let initial = native.encode_update_v1()?;
    /// renderer.apply_update_from_binary_v1(&initial)?;
    /// peer.apply_update_from_binary_v1(&initial)?;
    ///
    /// let origin = Origin::new("renderer");
    /// let history = UndoManager::<()>::new(
    ///     &native,
    ///     [(&text).into()],
    ///     UndoOptions {
    ///         tracked_origins: vec![None, Some(origin.clone())],
    ///         ..UndoOptions::default()
    ///     },
    /// )?;
    ///
    /// let edits = Arc::new(Mutex::new(Vec::new()));
    /// let sink = Arc::clone(&edits);
    /// let renderer_origin = origin.clone();
    /// let _subscription = renderer.subscribe(move |event| {
    ///     if event.local && event.origin.as_ref() == Some(&renderer_origin) {
    ///         sink.lock().unwrap().push(event.update.clone());
    ///     }
    /// });
    ///
    /// // The peer deletes 'e'. The renderer receives that change first.
    /// let mut peer_text = peer.get_or_create_text("body")?;
    /// peer_text.remove(1, 1)?;
    /// let remote = peer.encode_state_as_update_v1(&renderer.get_state_vector())?;
    /// renderer.apply_update_from_binary_v1(&remote)?;
    ///
    /// let rendered = renderer.get_or_create_text("body")?;
    /// assert_eq!(rendered.to_string(), "Hllo");
    /// renderer.transact_mut(origin.clone(), |tx| tx.text(&rendered)?.insert(4, "!"))?;
    /// let [bytes]: [Vec<u8>; 1] = std::mem::take(&mut *edits.lock().unwrap()).try_into().unwrap();
    /// match native.apply_local_update(Update::decode_v1(bytes)?, origin)? {
    ///     LocalUpdate::Applied => {}
    ///     LocalUpdate::MissingDependencies(clocks) => {
    ///         // In an editor, resynchronize the missing structs and retry.
    ///         panic!("renderer was not synchronized: {clocks:?}");
    ///     }
    /// }
    /// assert_eq!(text.to_string(), "Hello!");
    ///
    /// // The peer deletion arrives separately and does not enter local history.
    /// native.apply_update_with_origin(Update::decode_v1(remote)?, None)?;
    /// assert_eq!(text.to_string(), "Hllo!");
    /// assert!(history.undo()?.is_some());
    /// assert_eq!(text.to_string(), "Hllo");
    /// assert!(history.redo()?.is_some());
    /// assert_eq!(text.to_string(), "Hllo!");
    /// history.clear(true, true)?;
    /// assert!(!history.can_undo() && !history.can_redo());
    /// # Ok::<(), y_octo::JwstCodecError>(())
    /// ```
    pub fn apply_local_update(
        &self,
        update: Update,
        origin: impl Into<Option<Origin>>,
    ) -> JwstCodecResult<LocalUpdate> {
        let store_ref = &self.store;
        let applied = transact_mut_with(store_ref, origin.into(), true, |tx| {
            let missing = missing_dependencies(&update, tx.store_mut().get_state_vector());
            if !missing.is_empty() {
                return Ok(LocalUpdate::MissingDependencies(missing));
            }
            tx.incoming = Some(IncomingUpdate::of(&update));
            let store = tx.store_mut();
            // the remote updates waiting in the store stay out of this commit
            let pending = store.pending.take();
            let result = Self::integrate_update(store, store_ref, update);
            debug_assert!(store.pending.is_none(), "checked for missing dependencies");
            store.pending = pending;
            result.map(|()| LocalUpdate::Applied)
        })?;

        let unblocked = applied == LocalUpdate::Applied && {
            let store = read_store(store_ref)?;
            store.pending.as_ref().is_some_and(|pending| {
                // waiting structs whose dependencies arrived, or waiting
                // deletions (also of a deletion-only update) whose targets did
                pending
                    .missing_state
                    .iter()
                    .any(|(client, clock)| *clock < store.get_state(*client))
                    || pending.delete_set.iter().any(|(client, ranges)| {
                        let state = store.get_state(*client);
                        ranges.into_iter().any(|range| range.start < state)
                    })
            })
        };
        if unblocked {
            transact_mut_with(store_ref, None, false, |tx| {
                Self::integrate_update(tx.store_mut(), store_ref, Update::default())
            })?;
        }
        Ok(applied)
    }

    /// Runs `f` with a consistent read-only view of the document.
    ///
    /// The read lock is held until `f` returns. Calling other APIs of this
    /// document from `f` fails with [JwstCodecError::Reentrant] (or panics,
    /// for APIs without an error in their signature): read through `tx`.
    /// Access to a different document from `f` fails with
    /// [JwstCodecError::NestedDocumentBusy] if its lock is unavailable.
    pub fn transact<R>(&self, f: impl FnOnce(&Transaction<'_>) -> R) -> JwstCodecResult<R> {
        let tx = Transaction::begin(&self.store)?;
        Ok(f(&tx))
    }

    /// Runs `f` in a write transaction and commits it as one change: one
    /// commit event, one update, one step of history.
    ///
    /// The write lock is held until `f` returns; other threads block. Inside
    /// `f`, go through `tx` (see [Doc::transact]). If `f` fails, the changes
    /// it made stay and are committed like any other (there is no rollback)
    /// and its error is returned. A panic inside `f` leaves the document
    /// unusable ([JwstCodecError::DocPoisoned]).
    /// Other documents can be used from `f` when their locks are available
    /// immediately. Their commit events are deferred until this thread
    /// releases its outermost document lock.
    ///
    /// ```
    /// use std::sync::{Arc, Mutex};
    ///
    /// use y_octo::{Any, DocOptions, Origin, Value};
    ///
    /// let doc = DocOptions::from_identity(101, "greeting".into()).build();
    /// let text = doc.get_or_create_text("text").unwrap();
    /// let meta = doc.get_or_create_map("meta").unwrap();
    ///
    /// // keep every commit's update, in commit order
    /// let saved = Arc::new(Mutex::new(Vec::new()));
    /// let sink = saved.clone();
    /// let _subscription = doc.subscribe(move |event| {
    ///     sink.lock().unwrap().push(event.update.clone());
    /// });
    ///
    /// // several changes, one commit
    /// doc.transact_mut(Origin::new("editor"), |tx| {
    ///     tx.text(&text)?.insert(0, "Hello")?;
    ///     tx.map(&meta)?.insert("title".into(), "Greeting")?;
    ///     Ok(())
    /// })
    /// .unwrap();
    ///
    /// // single calls are transactions of their own
    /// text.clone().insert(5, " world").unwrap();
    ///
    /// // a consistent read of several types
    /// let (title, body) = doc
    ///     .transact(|tx| (tx.map(&meta).unwrap().get("title"), tx.text(&text).unwrap().to_string()))
    ///     .unwrap();
    /// assert_eq!(title, Some(Value::Any(Any::String("Greeting".into()))));
    /// assert_eq!(body, "Hello world");
    ///
    /// // the saved updates rebuild the document
    /// assert_eq!(saved.lock().unwrap().len(), 2);
    /// let mut copy = DocOptions::from_identity(202, "greeting".into()).build();
    /// for update in saved.lock().unwrap().iter() {
    ///     copy.apply_update_from_binary_v1(update).unwrap();
    /// }
    /// assert_eq!(copy.get_or_create_text("text").unwrap().to_string(), "Hello world");
    /// ```
    pub fn transact_mut<R>(
        &self,
        origin: impl Into<Option<Origin>>,
        f: impl FnOnce(&mut TransactionMut<'_>) -> JwstCodecResult<R>,
    ) -> JwstCodecResult<R> {
        transact_mut_with(&self.store, origin.into(), true, f)
    }

    /// Calls `callback` after every commit that changed the document, in
    /// commit order and outside of the document lock. Commits made from the
    /// callback are delivered after the current event. If a callback panics,
    /// delivery continues through the ready events before the first panic
    /// resumes on the delivering thread. An event uses the subscriptions in
    /// effect when it was enqueued. Dropping the returned [Subscription]
    /// excludes future events and leaves deliveries already enqueued intact.
    pub fn subscribe(&self, callback: impl Fn(&CommitEvent) + Send + Sync + 'static) -> Subscription {
        self.events.subscribe(Arc::new(callback))
    }

    /// Like [Doc::subscribe], for the commits that change the type `ty` or
    /// anything nested in it ([CommitSummary::touches_subtree]). Takes the
    /// place of Yjs `observeDeep`.
    pub fn subscribe_subtree(
        &self,
        ty: TypeIdentity,
        callback: impl Fn(&CommitEvent) + Send + Sync + 'static,
    ) -> Subscription {
        self.subscribe(move |event| {
            if event.touches_subtree(&ty) {
                callback(event)
            }
        })
    }

    pub(in crate::doc) fn integrate_update(
        store: &mut DocStore,
        store_ref: &StoreRef,
        mut update: Update,
    ) -> JwstCodecResult {
        let mut retry = false;

        loop {
            for (mut s, offset) in update.iter(store.get_state_vector()) {
                if let Node::Item(item) = &mut s {
                    debug_assert!(item.is_owned());
                    let mut item = unsafe { item.get_mut_unchecked() };
                    store.repair(&mut item, store_ref)?;
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
        or_released(read_store(&self.store).map(|store| store.types.keys().cloned().collect()))
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

    pub fn get_or_create_xml_fragment<S: AsRef<str>>(&self, name: S) -> JwstCodecResult<XMLFragment> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::XMLFragment)
            .set_name(name.as_ref().to_string())
            .build()
    }

    /// Creates an editable preliminary XML fragment.
    pub fn create_xml_fragment(&self) -> JwstCodecResult<XMLFragment> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::XMLFragment)
            .build()
    }

    /// Gets or creates a root XML element with default tag `"UNDEFINED"`,
    /// matching Yjs `doc.getXmlElement(name)`.
    pub fn get_or_create_xml_element<S: AsRef<str>>(&self, name: S) -> JwstCodecResult<XMLElement> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::XMLElement)
            .set_name(name.as_ref().to_string())
            .set_tag_name(xml::DEFAULT_XML_ELEMENT_TAG.to_string())
            .build()
    }

    /// Creates an editable preliminary XML element with the given `tag`.
    pub fn create_xml_element<S: Into<String>>(&self, tag: S) -> JwstCodecResult<XMLElement> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::XMLElement)
            .set_tag_name(tag.into())
            .build()
    }

    pub fn get_or_create_xml_text<S: AsRef<str>>(&self, name: S) -> JwstCodecResult<XMLText> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::XMLText)
            .set_name(name.as_ref().to_string())
            .build()
    }

    /// Creates an editable preliminary XML text.
    pub fn create_xml_text(&self) -> JwstCodecResult<XMLText> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::XMLText)
            .build()
    }

    pub fn get_or_create_xml_hook<S: AsRef<str>>(&self, name: S) -> JwstCodecResult<XMLHook> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::XMLHook)
            .set_name(name.as_ref().to_string())
            .build()
    }

    /// Creates an editable preliminary XML hook with the given `hook_name`.
    pub fn create_xml_hook<S: Into<String>>(&self, hook_name: S) -> JwstCodecResult<XMLHook> {
        YTypeBuilder::new(self.store.clone())
            .with_kind(YTypeKind::XMLHook)
            .set_tag_name(hook_name.into())
            .build()
    }

    pub fn encode_update_v1(&self) -> JwstCodecResult<Vec<u8>> {
        self.encode_state_as_update_v1(&StateVector::default())
    }

    pub fn encode_state_as_update_v1(&self, sv: &StateVector) -> JwstCodecResult<Vec<u8>> {
        let store = read_store(&self.store)?;
        let mut encoder = RawEncoder::default();
        store.write_state_as_update(sv, &mut encoder)?;
        Ok(encoder.into_inner())
    }

    pub fn encode_update(&self) -> JwstCodecResult<Update> {
        self.encode_state_as_update(&StateVector::default())
    }

    /// The returned [Update] is detached from this document. `Any` values the
    /// document holds may nest up to [Any::MAX_CONFIGURABLE_DEPTH] levels.
    pub fn encode_state_as_update(&self, sv: &StateVector) -> JwstCodecResult<Update> {
        Update::decode_v1_with_max_any_depth(self.encode_state_as_update_v1(sv)?, Any::MAX_CONFIGURABLE_DEPTH)
    }

    /// The `y-protocols/sync` step 1 message: this document's state vector.
    pub fn sync_step1(&self) -> JwstCodecResult<DocMessage> {
        Ok(DocMessage::Step1(self.get_state_vector().encode_v1()?))
    }

    /// The `y-protocols/sync` step 2 message answering a peer's state
    /// vector: everything this document has beyond `sv`, including all its
    /// deletions.
    pub fn sync_step2(&self, sv: &StateVector) -> JwstCodecResult<DocMessage> {
        Ok(DocMessage::Step2(self.encode_state_as_update_v1(sv)?))
    }

    /// Handles a `y-protocols/sync` message from a peer as a remote update
    /// without origin, see [Doc::handle_doc_message_with_origin].
    pub fn handle_doc_message(&mut self, msg: &DocMessage) -> JwstCodecResult<Option<DocMessage>> {
        self.handle_doc_message_with_origin(msg, None)
    }

    /// Handles a `y-protocols/sync` message from a peer: step 1 is answered
    /// with the step 2 message to send back, step 2 and updates are applied
    /// as a remote update with `origin` and answered with nothing.
    ///
    /// ```
    /// use y_octo::{DocMessage, DocOptions};
    ///
    /// let mut local = DocOptions::from_identity(1, "doc".into()).build();
    /// let mut remote = DocOptions::from_identity(2, "doc".into()).build();
    /// local.get_or_create_text("text")?.insert(0, "hello")?;
    ///
    /// // the remote peer asks for what it misses, the local one answers
    /// let reply = local.handle_doc_message(&remote.sync_step1()?)?;
    /// let Some(step2 @ DocMessage::Step2(_)) = reply else { unreachable!() };
    /// assert_eq!(remote.handle_doc_message(&step2)?, None);
    /// assert_eq!(remote.get_or_create_text("text")?.to_string(), "hello");
    /// # Ok::<(), y_octo::JwstCodecError>(())
    /// ```
    pub fn handle_doc_message_with_origin(
        &self,
        msg: &DocMessage,
        origin: impl Into<Option<Origin>>,
    ) -> JwstCodecResult<Option<DocMessage>> {
        let origin = origin.into();
        match msg {
            DocMessage::Step1(sv) => {
                let result = StateVector::decode_v1(sv).and_then(|sv| self.sync_step2(&sv)).map(Some);
                if let Some(origin) = origin {
                    after_unlock(move || drop(origin));
                }
                result
            }
            DocMessage::Step2(binary) | DocMessage::Update(binary) => match Update::decode_v1(binary) {
                Ok(update) => {
                    self.apply_update_with_origin(update, origin)?;
                    Ok(None)
                }
                Err(err) => {
                    if let Some(origin) = origin {
                        after_unlock(move || drop(origin));
                    }
                    Err(err)
                }
            },
        }
    }

    pub fn get_state_vector(&self) -> StateVector {
        or_released(read_store(&self.store).map(|store| store.get_state_vector()))
    }

    pub fn get_delete_sets(&self) -> DeleteSet {
        or_released(read_store(&self.store).map(|store| store.get_delete_sets()))
    }

    /// Garbage-collects every deleted struct and merges the whole store.
    /// Updates already collect what they delete; this is the explicit full
    /// pass.
    pub fn gc(&self) -> JwstCodecResult<()> {
        write_store(&self.store)?.optimize_all();
        Ok(())
    }
}

/// The result of [Doc::apply_local_update].
#[derive(Debug, Clone, PartialEq)]
pub enum LocalUpdate {
    /// The update took effect completely (or had nothing new).
    Applied,
    /// Nothing was applied: the update needs structs of these clients that
    /// the document has not integrated; each clock is what the document has
    /// integrated of that client, where resynchronization starts.
    MissingDependencies(StateVector),
}

impl IncomingUpdate {
    /// What `update` itself declares.
    pub(in crate::doc) fn of(update: &Update) -> Self {
        let mut structs = DeleteSet::default();
        for (&client, nodes) in &update.structs {
            let mut run: Option<std::ops::Range<Clock>> = None;
            for node in nodes.iter().filter(|node| !node.is_skip()) {
                let start = node.clock();
                let end = start + node.len();
                if let Some(range) = run.as_mut().filter(|range| range.end == start) {
                    range.end = end;
                } else if let Some(range) = run.replace(start..end) {
                    structs.add_range(client, range);
                }
            }
            if let Some(range) = run {
                structs.add_range(client, range);
            }
        }
        Self {
            structs,
            delete_set: update.delete_set.clone(),
        }
    }
}

/// What `update` needs beyond `state` (the document's integrated state) to
/// take effect completely: for each client the integration's dependency
/// check finds missing (run on a copy, without integrating), the clock the
/// document has integrated up to, from which the caller resynchronizes.
fn missing_dependencies(update: &Update, state: StateVector) -> StateVector {
    let mut probe = update.clone();
    let mut reached = state.clone();
    for (node, _) in probe.iter(state.clone()) {
        reached.set_max(node.client(), node.clock() + node.len());
    }
    for _ in probe.delete_set_iter(reached) {}
    let mut missing = StateVector::default();
    let clients = probe.missing_state.keys().chain(
        probe
            .pending_delete_set
            .iter()
            .filter(|(_, ranges)| !ranges.is_empty())
            .map(|(client, _)| client),
    );
    for client in clients {
        missing.insert(*client, state.get(client));
    }
    missing
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct RevertOrigin;

fn derive_revert_client(current: &[u8], target: &[u8], used: &HashSet<u64>) -> u64 {
    // Deterministic 53-bit FNV-1a mix so `revert_update_v1` needs no RNG and
    // stays exact in JS hosts.
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in current.iter().chain(target.iter()) {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    let mut candidate = (hash & ((1u64 << 53) - 1)).max(1);
    while used.contains(&candidate) {
        candidate = (candidate + 1) & ((1u64 << 53) - 1);
        if candidate == 0 {
            candidate = 1;
        }
    }
    candidate
}

fn delete_set_covers(outer: &DeleteSet, inner: &DeleteSet) -> bool {
    for (client, inner_ranges) in inner.iter() {
        let inner_vec = inner_ranges.canonical_ranges();
        if inner_vec.is_empty() {
            continue;
        }
        let Some(outer_ranges) = outer.get(client) else {
            return false;
        };
        let outer_vec = outer_ranges.canonical_ranges();
        let mut oi = 0;
        for r in inner_vec {
            while oi < outer_vec.len() && outer_vec[oi].end <= r.start {
                oi += 1;
            }
            if oi >= outer_vec.len() || outer_vec[oi].start > r.start || outer_vec[oi].end < r.end {
                return false;
            }
        }
    }
    true
}

/// Computes a V1 delta update that reverts `current_snapshot` back to the
/// content of its ancestor `target_snapshot`, including both undoing insertions
/// and recreating items deleted since `target_snapshot`.
///
/// Both snapshots must belong to the **same CRDT document lineage** (where a
/// given `(client, clock)` uniquely identifies the same operation). Rejects
/// snapshots with unresolved pending dependencies, inverted/diverged
/// histories (`target > current`), or delete sets in `target_snapshot` not
/// covered by `current_snapshot` with [`JwstCodecError::IncompleteDocument`].
pub fn revert_update_v1(current_snapshot: &[u8], target_snapshot: &[u8]) -> JwstCodecResult<Vec<u8>> {
    let target_update = Update::decode_v1(target_snapshot)?;
    let current_update = Update::decode_v1(current_snapshot)?;
    let target_ds = target_update.delete_set.clone();
    let current_ds = current_update.delete_set.clone();

    let current_sv_bytes = encode_state_vector_from_update_v1(current_snapshot)?;
    let current_sv = StateVector::decode_v1(&current_sv_bytes)?;

    let mut used_clients = HashSet::new();
    for client in current_sv
        .keys()
        .chain(current_update.structs.keys())
        .chain(current_update.delete_set.keys())
        .chain(target_update.structs.keys())
        .chain(target_update.delete_set.keys())
    {
        used_clients.insert(*client);
    }

    let shadow_client = derive_revert_client(current_snapshot, target_snapshot, &used_clients);
    let mut shadow = DocOptions::from_identity(shadow_client, "revert".into())
        .auto_gc(false)
        .build();
    shadow.apply_update(target_update)?;
    if shadow.has_pending_updates() {
        return Err(JwstCodecError::IncompleteDocument(
            "target snapshot has unresolved pending updates".into(),
        ));
    }

    let target_sv = shadow.get_state_vector();
    for (client, target_clock) in target_sv.iter() {
        if current_sv.get(client) < *target_clock {
            return Err(JwstCodecError::IncompleteDocument(
                "target snapshot is not an ancestor of current snapshot".into(),
            ));
        }
    }
    if !delete_set_covers(&current_ds, &target_ds) {
        return Err(JwstCodecError::IncompleteDocument(
            "target snapshot delete set is not covered by current snapshot".into(),
        ));
    }

    let target_sv_bytes = target_sv.encode_v1()?;
    let diff_bytes = diff_update_v1(current_snapshot, &target_sv_bytes)?;
    let diff_update = Update::decode_v1(&diff_bytes)?;

    let revert_origin = Origin::new(RevertOrigin);
    let undo = UndoManager::<()>::new(
        &shadow,
        [(&shadow).into()],
        UndoOptions {
            capture_timeout: u64::MAX,
            tracked_origins: vec![Some(revert_origin.clone())],
        },
    )?;

    shadow.apply_update_with_origin(diff_update, revert_origin)?;
    if shadow.has_pending_updates() || shadow.get_state_vector() != current_sv {
        return Err(JwstCodecError::IncompleteDocument(
            "current snapshot has unresolved pending updates or diverged state".into(),
        ));
    }

    match undo.pop_with_event(UndoStack::Undo)? {
        Some((_, Some(event))) => Ok(event.update),
        _ => Ok(vec![0, 0]),
    }
}

#[cfg(test)]
mod tests {
    #[cfg(all(not(loom), not(feature = "random")))]
    mod client_identity;
    #[cfg(not(loom))]
    mod local_update;

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
    #[cfg(feature = "random")]
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
    #[cfg(feature = "random")]
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

    /// Client ID 0 the host passes is an ordinary ID, with and without the
    /// `random` feature: built with it, or set to it, the document writes as
    /// client 0.
    #[test]
    fn test_explicit_client_zero_writes() {
        loom_model!({
            let mut doc = DocOptions::from_identity(0, "guid".into()).build();
            assert!(!doc.client_required());
            let mut text = doc.get_or_create_text("text").unwrap();
            text.insert(0, "a").unwrap();
            doc.set_client(5);
            text.insert(1, "b").unwrap();
            doc.set_client(0);
            assert!(!doc.client_required());
            text.insert(2, "c").unwrap();
            assert_eq!(doc.get_state_vector(), StateVector::from([(0, 2), (5, 1)]));
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
            let doc =
                Doc::try_from_binary_v1_with_options(yjs_fixture("mixed-array"), DocOptions::new().with_client_id(2))
                    .unwrap();
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

            let detached_doc =
                Doc::try_from_binary_v1_with_options(binary_detached, DocOptions::new().with_client_id(2)).unwrap();
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
            include_bytes!("../../fixtures/basic.bin").to_vec(),
            include_bytes!("../../fixtures/database.bin").to_vec(),
            include_bytes!("../../fixtures/large.bin").to_vec(),
            include_bytes!("../../fixtures/with-subdoc.bin").to_vec(),
            include_bytes!("../../fixtures/edge-case-left-right-same-node.bin").to_vec(),
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
