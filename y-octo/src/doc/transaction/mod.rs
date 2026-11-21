//! Transactions, the commit pipeline and ordered commit events.
//!
//! Every change of a document runs in a [TransactionMut] that owns the store
//! write lock: explicit ones from [Doc::transact_mut], implicit ones around
//! each single write method (`Text::insert`, `Map::insert`, …) and the one
//! around [Doc::apply_update]. Committing runs, still under the lock:
//!
//! 1. collect the changes (state vectors, new and first-time deleted ranges,
//!    changed types and keys and their ancestors, origin, locality),
//! 2. the internal history hook ([CommitHook]),
//! 3. GC of the ranges this transaction deleted,
//! 4. merge of the structs this transaction touched,
//! 5. for remote transactions, reset of the changed types' search markers,
//! 6. the commit event, with the update bytes when someone subscribed,
//!
//! and 7., after unlocking, delivers queued events in commit order.

#[cfg(all(test, not(loom)))]
mod tests;

use std::{
    any::{Any as StdAny, TypeId, type_name},
    cell::RefCell,
    collections::{BTreeSet, VecDeque},
    fmt,
    hash::{Hash, Hasher},
    mem,
    ops::{Deref, DerefMut},
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
    sync::TryLockError,
};

use super::{
    store::{ChangedTypeRefs, Collector, StoreRef},
    *,
};
use crate::sync::{Arc, AtomicBool, Mutex, Ordering, RwLockReadGuard, RwLockWriteGuard, Weak, thread_local};

trait OriginValue: Send + Sync {
    fn as_any(&self) -> &dyn StdAny;
    fn eq_value(&self, other: &dyn OriginValue) -> bool;
    fn hash_value(&self, state: &mut dyn Hasher);
    fn type_name(&self) -> &'static str;
}

impl<T: Clone + Eq + Hash + Send + Sync + 'static> OriginValue for T {
    fn as_any(&self) -> &dyn StdAny {
        self
    }

    fn eq_value(&self, other: &dyn OriginValue) -> bool {
        other.as_any().downcast_ref::<T>() == Some(self)
    }

    fn hash_value(&self, mut state: &mut dyn Hasher) {
        TypeId::of::<T>().hash(&mut state);
        self.hash(&mut state);
    }

    fn type_name(&self) -> &'static str {
        type_name::<T>()
    }
}

/// Who made a transaction, chosen by the caller. It is only local metadata:
/// it never enters the document or its updates.
///
/// Any `Clone + Eq + Hash + Send + Sync` value can be an origin; two origins
/// are equal when they hold equal values of the same type.
///
/// ```
/// use y_octo::Origin;
///
/// #[derive(Clone, PartialEq, Eq, Hash)]
/// enum Source {
///     Editor,
///     Sync,
/// }
///
/// assert_eq!(Origin::new(Source::Editor), Origin::new(Source::Editor));
/// assert_ne!(Origin::new(Source::Editor), Origin::new(Source::Sync));
/// assert_ne!(Origin::new(1u32), Origin::new(1u64));
/// assert_eq!(Origin::new("undo").downcast_ref::<&str>(), Some(&"undo"));
/// ```
#[derive(Clone)]
pub struct Origin(Arc<dyn OriginValue>);

impl Origin {
    pub fn new<T: Clone + Eq + Hash + Send + Sync + 'static>(value: T) -> Self {
        Self(Arc::new(value))
    }

    pub fn downcast_ref<T: 'static>(&self) -> Option<&T> {
        self.0.as_any().downcast_ref()
    }

    /// The same origin: `self` or a clone of it. Unlike `==` it never calls
    /// the value's `PartialEq`.
    pub(crate) fn same(&self, other: &Origin) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl PartialEq for Origin {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0.eq_value(&*other.0)
    }
}

impl Eq for Origin {}

impl Hash for Origin {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash_value(state)
    }
}

impl fmt::Debug for Origin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Origin({})", self.0.type_name())
    }
}

// ---------------------------------------------------------------------------
// Store locking with same-thread re-entrance detection.

thread_local! {
    static LOCKS: RefCell<StoreLocks> = RefCell::new(StoreLocks::default());
}

#[derive(Default)]
struct StoreLocks {
    held: Vec<usize>,
    deferred: Vec<AfterUnlock>,
}

fn store_key(store: &StoreRef) -> usize {
    Arc::as_ptr(store) as *const () as usize
}

struct HeldStoreLock(usize);

fn enter(key: usize) -> JwstCodecResult<(HeldStoreLock, bool)> {
    LOCKS.with(|locks| {
        let mut locks = locks.borrow_mut();
        if locks.held.contains(&key) {
            return Err(JwstCodecError::Reentrant);
        }
        let nested = !locks.held.is_empty();
        locks.held.push(key);
        Ok((HeldStoreLock(key), nested))
    })
}

impl Drop for HeldStoreLock {
    fn drop(&mut self) {
        let actions = LOCKS.with(|locks| {
            let mut locks = locks.borrow_mut();
            let pos = locks
                .held
                .iter()
                .position(|key| *key == self.0)
                .expect("registered lock");
            locks.held.swap_remove(pos);
            locks.held.is_empty().then(|| mem::take(&mut locks.deferred))
        });
        if let Some(actions) = actions {
            AfterUnlock::run(actions);
        }
    }
}

/// Drop the actual guard before releasing the thread's registration so any
/// deferred user code runs after the document lock is unlocked.
pub(crate) struct StoreReadGuard<'a> {
    guard: RwLockReadGuard<'a, DocStore>,
    _held: HeldStoreLock,
}

/// The store write lock, registered as held by this thread.
pub(crate) struct StoreWriteGuard<'a> {
    guard: RwLockWriteGuard<'a, DocStore>,
    _held: HeldStoreLock,
}

fn nested_lock_error<T>(error: TryLockError<T>) -> JwstCodecError {
    match error {
        TryLockError::WouldBlock => JwstCodecError::NestedDocumentBusy,
        TryLockError::Poisoned(_) => JwstCodecError::DocPoisoned,
    }
}

/// Takes the store read lock. Fails instead of deadlocking when this thread
/// already holds the lock (an API of the document called inside one of its
/// transactions), and when a panic left the store half changed.
pub(crate) fn read_store(store: &StoreRef) -> JwstCodecResult<StoreReadGuard<'_>> {
    read_store_with_order(store, false)
}

fn read_store_with_order(store: &StoreRef, ordered_pair: bool) -> JwstCodecResult<StoreReadGuard<'_>> {
    let (held, nested) = enter(store_key(store))?;
    let guard = if nested && !ordered_pair {
        store.try_read().map_err(nested_lock_error)?
    } else {
        store.read().map_err(|_| JwstCodecError::DocPoisoned)?
    };
    Ok(StoreReadGuard { guard, _held: held })
}

/// Takes the store write lock, see [read_store].
pub(crate) fn write_store(store: &StoreRef) -> JwstCodecResult<StoreWriteGuard<'_>> {
    let (held, nested) = enter(store_key(store))?;
    let guard = if nested {
        store.try_write().map_err(nested_lock_error)?
    } else {
        store.write().map_err(|_| JwstCodecError::DocPoisoned)?
    };
    Ok(StoreWriteGuard { guard, _held: held })
}

/// [read_store] for APIs that have no error in their signature.
pub(crate) fn read_store_or_panic(store: &StoreRef) -> StoreReadGuard<'_> {
    read_store(store).unwrap_or_else(|err| panic!("{err}"))
}

/// A top-level comparison may wait for both read locks because it always
/// acquires them in the same order. Inside a user transaction both use try.
pub(crate) fn read_store_pair<'a>(
    left: &'a StoreRef,
    right: &'a StoreRef,
) -> JwstCodecResult<(StoreReadGuard<'a>, StoreReadGuard<'a>)> {
    let top_level = LOCKS.with(|locks| locks.borrow().held.is_empty());
    if top_level && store_key(right) < store_key(left) {
        let right = read_store(right)?;
        Ok((read_store_with_order(left, true)?, right))
    } else {
        Ok((read_store(left)?, read_store_with_order(right, top_level)?))
    }
}

/// For read APIs that have no error in their signature: a released document
/// reads as empty, everything else is a misuse worth stopping at.
pub(crate) fn or_released<T: Default>(result: JwstCodecResult<T>) -> T {
    match result {
        Ok(value) => value,
        Err(JwstCodecError::DocReleased) => T::default(),
        Err(err) => panic!("{err}"),
    }
}

impl Deref for StoreReadGuard<'_> {
    type Target = DocStore;

    fn deref(&self) -> &DocStore {
        &self.guard
    }
}

impl Deref for StoreWriteGuard<'_> {
    type Target = DocStore;

    fn deref(&self) -> &DocStore {
        &self.guard
    }
}

impl DerefMut for StoreWriteGuard<'_> {
    fn deref_mut(&mut self) -> &mut DocStore {
        &mut self.guard
    }
}

// ---------------------------------------------------------------------------
// Commit events.

/// A type a transaction changed, and the map keys it changed.
#[derive(Debug, Clone, PartialEq)]
pub struct ChangedType {
    pub identity: TypeIdentity,
    /// Changed keys of the type's map part, sorted; empty when only its
    /// sequence part changed.
    pub keys: Vec<String>,
}

/// The ranges an applied update itself declared, before it was merged with
/// updates waiting in the document for missing dependencies.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct IncomingUpdate {
    pub structs: DeleteSet,
    pub delete_set: DeleteSet,
}

/// What one transaction changed.
#[derive(Debug, Clone)]
pub struct CommitSummary {
    pub origin: Option<Origin>,
    /// `false` for [Doc::apply_update].
    pub local: bool,
    pub before_state: StateVector,
    pub after_state: StateVector,
    /// ID ranges of the structs this transaction added.
    pub inserted: DeleteSet,
    /// ID ranges this transaction deleted for the first time.
    pub deleted: DeleteSet,
    /// Types that existed before the transaction and changed, with their
    /// changed keys. A type created by the transaction shows up as a change
    /// of its parent.
    pub changed: Vec<ChangedType>,
    /// Ancestors of the changed types, nearest first, each listed once.
    pub ancestors: Vec<TypeIdentity>,
    /// Set for [Doc::apply_update].
    pub incoming: Option<IncomingUpdate>,
    /// GUIDs of the subdocuments this transaction integrated and did not
    /// delete again (Yjs `subdocs` event, `added`).
    pub subdocs_added: BTreeSet<String>,
    /// GUIDs of the subdocuments integrated before this transaction that it
    /// deleted (Yjs `subdocs` event, `removed`). A GUID in both sets belongs to
    /// a subdocument item this transaction replaced with another one.
    pub subdocs_removed: BTreeSet<String>,
}

impl CommitSummary {
    /// Whether the type `ty` or anything below it changed: `ty` is one of
    /// the changed types or one of their ancestors.
    pub fn touches_subtree(&self, ty: &TypeIdentity) -> bool {
        self.changed.iter().any(|changed| &changed.identity == ty) || self.ancestors.contains(ty)
    }
}

/// A committed transaction, delivered to subscribers in `seq` order. Events
/// (and their update bytes) are only built while someone is subscribed.
#[derive(Debug, Clone)]
pub struct CommitEvent {
    /// Increases by one with every commit that changed the document.
    pub seq: u64,
    pub summary: CommitSummary,
    /// Update V1 bytes with exactly this transaction's new structs and
    /// deletions.
    pub update: Vec<u8>,
}

impl Deref for CommitEvent {
    type Target = CommitSummary;

    fn deref(&self) -> &CommitSummary {
        &self.summary
    }
}

/// The history stage of the commit pipeline: runs under the write lock after
/// the changes and before GC, and may retain or release ranges from GC
/// without advancing any struct clocks.
pub(crate) trait CommitHook: Send + Sync + fmt::Debug {
    fn on_commit(&mut self, store: &mut DocStore, summary: &CommitSummary);
    fn as_any(&self) -> &dyn StdAny;
    fn as_any_mut(&mut self) -> &mut dyn StdAny;
}

type Callback = Arc<dyn Fn(&CommitEvent) + Send + Sync>;
type PanicPayload = Box<dyn StdAny + Send>;

enum AfterUnlock {
    Deliver(Arc<EventHub>, Arc<AtomicBool>),
    DropCallbacks(Vec<Callback>),
    Run(Box<dyn FnOnce() + Send>),
}

/// Runs `f` once this thread holds no document lock: now, or when it
/// releases its last one.
pub(crate) fn after_unlock(f: impl FnOnce() + Send + 'static) {
    AfterUnlock::Run(Box::new(f)).schedule();
}

impl AfterUnlock {
    fn schedule(self) {
        let mut action = Some(self);
        // A document can also be dropped from another thread-local's
        // destructor. At thread exit there is no document lock to wait for.
        let _ = LOCKS.try_with(|locks| {
            let mut locks = locks.borrow_mut();
            if !locks.held.is_empty() {
                locks.deferred.push(action.take().unwrap());
            }
        });
        if let Some(action) = action {
            Self::run(vec![action]);
        }
    }

    fn run(actions: Vec<Self>) {
        // Publish readiness before invoking any callbacks. A callback may
        // write to any of these documents and queue another event.
        for action in &actions {
            if let Self::Deliver(_, ready) = action {
                ready.store(true, Ordering::Release);
            }
        }
        let mut panics = Vec::new();
        for action in actions {
            match action {
                Self::Deliver(hub, _) => hub.deliver(&mut panics),
                Self::Run(f) => {
                    if let Err(payload) = catch_unwind(AssertUnwindSafe(f)) {
                        panics.push(payload);
                    }
                }
                Self::DropCallbacks(callbacks) => {
                    for callback in callbacks {
                        if let Err(payload) = catch_unwind(AssertUnwindSafe(move || drop(callback))) {
                            panics.push(payload);
                        }
                    }
                }
            }
        }
        if !panics.is_empty() && !std::thread::panicking() {
            let first = panics.remove(0);
            drop(panics);
            resume_unwind(first);
        }
    }
}

struct QueuedEvent {
    event: CommitEvent,
    callbacks: Vec<Callback>,
    ready: Arc<AtomicBool>,
}

#[derive(Default)]
struct Delivery {
    queue: VecDeque<QueuedEvent>,
    delivering: bool,
}

/// Subscribers of a document and the queue of events waiting for them.
#[derive(Default)]
pub(crate) struct EventHub {
    subscribers: Mutex<(u64, Vec<(u64, Callback)>)>,
    delivery: Mutex<Delivery>,
}

impl fmt::Debug for EventHub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("EventHub")
    }
}

impl EventHub {
    pub(crate) fn subscribe(self: &Arc<Self>, callback: Callback) -> Subscription {
        let mut subscribers = self.subscribers.lock().unwrap();
        subscribers.0 += 1;
        let id = subscribers.0;
        subscribers.1.push((id, callback));
        Subscription {
            hub: Arc::downgrade(self),
            id,
        }
    }

    fn unsubscribe(&self, id: u64) {
        let callback = {
            let mut subscribers = self.subscribers.lock().unwrap();
            subscribers
                .1
                .iter()
                .position(|(other, _)| *other == id)
                .map(|index| subscribers.1.remove(index).1)
        };
        if let Some(callback) = callback {
            AfterUnlock::DropCallbacks(vec![callback]).schedule();
        }
    }

    /// Called with both the store write lock and the subscribers lock held.
    /// The queue is in commit order, with the subscription set at enqueue.
    fn enqueue(&self, event: CommitEvent, callbacks: Vec<Callback>) -> Arc<AtomicBool> {
        let ready = Arc::new(AtomicBool::new(false));
        self.delivery.lock().unwrap().queue.push_back(QueuedEvent {
            event,
            callbacks,
            ready: ready.clone(),
        });
        ready
    }

    /// Called without the store lock. One thread at a time drains the queue;
    /// commits made meanwhile, also from inside a callback, are queued behind
    /// the event being delivered and delivered by that thread.
    fn deliver(&self, panics: &mut Vec<PanicPayload>) {
        {
            let mut delivery = self.delivery.lock().unwrap();
            if delivery.delivering || delivery.queue.is_empty() {
                return;
            }
            delivery.delivering = true;
        }

        loop {
            let queued = {
                let mut delivery = self.delivery.lock().unwrap();
                if delivery
                    .queue
                    .front()
                    .is_none_or(|queued| !queued.ready.load(Ordering::Acquire))
                {
                    delivery.delivering = false;
                    return;
                }
                delivery.queue.pop_front().unwrap()
            };
            for callback in queued.callbacks {
                let event = &queued.event;
                if let Err(payload) = catch_unwind(AssertUnwindSafe(move || callback(event))) {
                    panics.push(payload);
                }
            }
        }
    }
}

impl Drop for EventHub {
    fn drop(&mut self) {
        let subscribers = self.subscribers.get_mut().unwrap();
        if !subscribers.1.is_empty() {
            let callbacks = subscribers.1.drain(..).map(|(_, callback)| callback).collect();
            AfterUnlock::DropCallbacks(callbacks).schedule();
        }
    }
}

/// Keeps a subscription alive; dropping it unsubscribes.
#[must_use = "dropping a Subscription unsubscribes"]
pub struct Subscription {
    hub: Weak<EventHub>,
    id: u64,
}

impl Subscription {
    pub fn unsubscribe(self) {}
}

impl Drop for Subscription {
    fn drop(&mut self) {
        if let Some(hub) = self.hub.upgrade() {
            hub.unsubscribe(self.id);
        }
    }
}

impl fmt::Debug for Subscription {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Subscription").field(&self.id).finish()
    }
}

// ---------------------------------------------------------------------------
// Transactions.

/// A read transaction: a consistent view of the document, holding its read
/// lock until the closure of [Doc::transact] returns.
pub struct Transaction<'doc> {
    store: StoreReadGuard<'doc>,
    store_ref: &'doc StoreRef,
}

/// A write transaction created by [Doc::transact_mut]. It holds the write
/// lock until the closure returns.
pub struct TransactionMut<'doc> {
    store: StoreWriteGuard<'doc>,
    store_ref: &'doc StoreRef,
    origin: Option<Origin>,
    local: bool,
    /// Internal formatting maintenance never captures history or clears redo.
    capture_history: bool,
    before_state: StateVector,
    pub(crate) incoming: Option<IncomingUpdate>,
}

impl<'doc> Transaction<'doc> {
    pub(crate) fn begin(store_ref: &'doc StoreRef) -> JwstCodecResult<Self> {
        Ok(Self {
            store: read_store(store_ref)?,
            store_ref,
        })
    }

    pub fn state_vector(&self) -> StateVector {
        self.store.get_state_vector()
    }

    pub fn text<'t>(&'t self, text: &'t Text) -> JwstCodecResult<TextRead<'t>> {
        let ty = own(self.store_ref, &text.0)?;
        Ok(TextRead::new(&self.store, &text.0, ty))
    }

    pub fn map<'t>(&'t self, map: &'t Map) -> JwstCodecResult<MapRead<'t>> {
        let ty = own(self.store_ref, &map.0)?;
        Ok(MapRead { ty })
    }

    pub fn array<'t>(&'t self, array: &'t Array) -> JwstCodecResult<ArrayRead<'t>> {
        let ty = own(self.store_ref, &array.0)?;
        Ok(ArrayRead { parent: &array.0, ty })
    }

    pub fn xml_fragment<'t>(&'t self, fragment: &'t XMLFragment) -> JwstCodecResult<XMLFragmentRead<'t>> {
        let ty = own(self.store_ref, &fragment.0)?;
        Ok(XMLFragmentRead {
            parent: &fragment.0,
            ty,
        })
    }

    pub fn xml_element<'t>(&'t self, element: &'t XMLElement) -> JwstCodecResult<XMLElementRead<'t>> {
        let ty = own(self.store_ref, &element.0)?;
        Ok(XMLElementRead { parent: &element.0, ty })
    }

    pub fn xml_text<'t>(&'t self, text: &'t XMLText) -> JwstCodecResult<XMLTextRead<'t>> {
        let ty = own(self.store_ref, &text.0)?;
        Ok(XMLTextRead { ty })
    }

    pub fn xml_hook<'t>(&'t self, hook: &'t XMLHook) -> JwstCodecResult<XMLHookRead<'t>> {
        let ty = own(self.store_ref, &hook.0)?;
        Ok(XMLHookRead { ty })
    }
}

/// The type behind `handle` if it belongs to the document of `store_ref`.
/// The caller holds that store's lock.
fn own<'t>(store_ref: &StoreRef, handle: &'t YTypeRef) -> JwstCodecResult<&'t YType> {
    if !std::ptr::eq(handle.store.as_ptr(), Arc::as_ptr(store_ref)) {
        return Err(JwstCodecError::ForeignType);
    }
    handle.ty().ok_or(JwstCodecError::DocReleased)
}

impl<'doc> TransactionMut<'doc> {
    pub(crate) fn begin(store_ref: &'doc StoreRef, origin: Option<Origin>, local: bool) -> JwstCodecResult<Self> {
        Self::begin_with(store_ref, origin, local, true)
    }

    /// `edits`: the transaction may create structs with the document's client
    /// ID, so it is refused while the host has to set one
    /// ([Doc::client_required]). Internal maintenance (history bookkeeping,
    /// releasing retained content) creates none and always runs.
    fn begin_with(
        store_ref: &'doc StoreRef,
        origin: Option<Origin>,
        local: bool,
        edits: bool,
    ) -> JwstCodecResult<Self> {
        let store = match write_store(store_ref) {
            Ok(store) => store,
            Err(error) => {
                if let Some(origin) = origin {
                    after_unlock(move || drop(origin));
                }
                return Err(error);
            }
        };
        if local && edits && store.client_required {
            drop(store);
            if let Some(origin) = origin {
                after_unlock(move || drop(origin));
            }
            return Err(JwstCodecError::ClientIdRequired);
        }
        if !store.collector.is_empty() {
            drop(store);
            if let Some(origin) = origin {
                after_unlock(move || drop(origin));
            }
            return Err(JwstCodecError::OpenTransactionFrame);
        }
        let before_state = store.get_state_vector();
        Ok(Self {
            store,
            store_ref,
            origin,
            local,
            capture_history: true,
            before_state,
            incoming: None,
        })
    }

    pub fn origin(&self) -> Option<&Origin> {
        self.origin.as_ref()
    }

    /// `false` for the transaction of [Doc::apply_update].
    pub fn is_local(&self) -> bool {
        self.local
    }

    pub fn before_state(&self) -> &StateVector {
        &self.before_state
    }

    pub fn state_vector(&self) -> StateVector {
        self.store.get_state_vector()
    }

    pub(crate) fn store_ref(&self) -> &'doc StoreRef {
        self.store_ref
    }

    pub(crate) fn store_mut(&mut self) -> &mut DocStore {
        &mut self.store
    }

    pub fn text<'t>(&'t mut self, text: &'t Text) -> JwstCodecResult<TextWrite<'t, 'doc>> {
        own(self.store_ref, &text.0)?;
        Ok(TextWrite {
            tx: self,
            parent: &text.0,
        })
    }

    pub fn map<'t>(&'t mut self, map: &'t Map) -> JwstCodecResult<MapWrite<'t, 'doc>> {
        own(self.store_ref, &map.0)?;
        Ok(MapWrite {
            tx: self,
            parent: &map.0,
        })
    }

    pub fn array<'t>(&'t mut self, array: &'t Array) -> JwstCodecResult<ArrayWrite<'t, 'doc>> {
        own(self.store_ref, &array.0)?;
        Ok(ArrayWrite {
            tx: self,
            parent: &array.0,
        })
    }

    pub fn xml_fragment<'t>(&'t mut self, fragment: &'t XMLFragment) -> JwstCodecResult<XMLFragmentWrite<'t, 'doc>> {
        own(self.store_ref, &fragment.0)?;
        Ok(XMLFragmentWrite {
            tx: self,
            parent: &fragment.0,
        })
    }

    pub fn xml_element<'t>(&'t mut self, element: &'t XMLElement) -> JwstCodecResult<XMLElementWrite<'t, 'doc>> {
        own(self.store_ref, &element.0)?;
        Ok(XMLElementWrite {
            tx: self,
            parent: &element.0,
        })
    }

    pub fn xml_text<'t>(&'t mut self, text: &'t XMLText) -> JwstCodecResult<XMLTextWrite<'t, 'doc>> {
        own(self.store_ref, &text.0)?;
        Ok(XMLTextWrite {
            tx: self,
            parent: &text.0,
        })
    }

    pub fn xml_hook<'t>(&'t mut self, hook: &'t XMLHook) -> JwstCodecResult<XMLHookWrite<'t, 'doc>> {
        own(self.store_ref, &hook.0)?;
        Ok(XMLHookWrite {
            tx: self,
            parent: &hook.0,
        })
    }

    /// Runs `f` on the type behind `parent` under the document write lock.
    fn with_type<R>(
        &mut self,
        parent: &YTypeRef,
        f: impl FnOnce(&mut DocStore, &mut YType) -> JwstCodecResult<R>,
    ) -> JwstCodecResult<R> {
        parent.write_locked(&mut self.store, f)
    }

    /// Shared view of the type behind `parent`.
    fn view<'t>(&'t self, parent: &'t YTypeRef) -> &'t YType {
        parent.ty().expect("checked when the view was created")
    }

    /// Steps 1 to 6 of the commit pipeline, under the write lock.
    fn commit(&mut self) {
        let _ = self.commit_with_origin(None, false);
    }

    fn commit_with_origin(
        &mut self,
        maintenance_origin: Option<Origin>,
        capture_event: bool,
    ) -> (Option<CommitEvent>, Option<CommitEvent>) {
        commit_store(
            &mut self.store,
            &mut self.before_state,
            &mut self.local,
            &mut self.capture_history,
            &self.origin,
            &mut self.incoming,
            maintenance_origin,
            capture_event,
        )
    }
}

/// Executes steps 1 to 6 of the commit pipeline directly on a locked
/// [`DocStore`]. Returns `(primary_event, cleanup_event)` when `capture_event`
/// is `true` and the respective step changed the document.
#[allow(clippy::too_many_arguments)]
pub(crate) fn commit_store(
    store: &mut DocStore,
    before_state: &mut StateVector,
    local: &mut bool,
    capture_history: &mut bool,
    origin: &Option<Origin>,
    incoming: &mut Option<IncomingUpdate>,
    maintenance_origin: Option<Origin>,
    capture_event: bool,
) -> (Option<CommitEvent>, Option<CommitEvent>) {
    let is_local = *local;
    let collector = mem::take(&mut store.collector);
    let after_state = store.get_state_vector();
    // Save format identities before GC/merge can erase their content.
    let cleanup = if !is_local {
        text::cleanup::CleanupPlan::after_remote(
            store,
            before_state,
            &after_state,
            &collector.changed,
            &collector.deleted,
        )
    } else {
        text::cleanup::CleanupPlan::default()
    };

    // 1. what changed
    let changes = !collector.deleted.is_empty()
        || !collector.changed.is_empty()
        || after_state
            .iter()
            .any(|(client, clock)| *clock > before_state.get(client));
    let hub = changes.then(|| store.events.clone());
    // Keep subscription changes serialized with enqueue, including when
    // there are no subscribers and we skip encoding.
    let subscribers = hub.as_ref().map(|hub| hub.subscribers.lock().unwrap());
    let deliver = subscribers.as_ref().is_some_and(|guard| !guard.1.is_empty());
    let need_event = changes && (deliver || capture_event);
    // only built for someone who reads it
    let summary = (need_event || (changes && *capture_history && store.history_hook.is_some())).then(|| {
        let mut inserted = DeleteSet::default();
        for (client, clock) in after_state.iter() {
            let before = before_state.get(client);
            if *clock > before {
                inserted.add(*client, before, clock - before);
            }
        }
        let (changed, ancestors) = changed_types(&collector.changed, before_state);
        CommitSummary {
            origin: maintenance_origin.clone().or_else(|| origin.clone()),
            local: is_local,
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            inserted,
            deleted: collector.deleted.clone(),
            changed,
            ancestors,
            incoming: incoming.take(),
            subdocs_added: collector.subdocs_added.iter().map(|(_, guid)| guid.clone()).collect(),
            subdocs_removed: collector.subdocs_removed.iter().cloned().collect(),
        }
    });

    // 2. history
    if *capture_history
        && let Some(summary) = &summary
        && let Some(mut hook) = store.history_hook.take()
    {
        hook.on_commit(store, summary);
        store.history_hook = Some(hook);
    }

    // 3., 4. GC and merge of what this transaction touched
    let Collector {
        changed,
        deleted,
        merges,
        ..
    } = collector;
    // The history stage only collects released ranges: it adds merge
    // points (children it replaced), never deletions.
    debug_assert!(store.collector.deleted.is_empty());
    store.collector.deleted = deleted;
    store.collector.merges.extend(merges);
    let client = store.client();
    let client_clock_advanced = !is_local && after_state.get(&client) != before_state.get(&client);
    store.optimize(store.gc, after_state);
    debug_assert!(store.collector.is_empty());

    // 5. remote changes move items under the search markers of the types
    // they touch (Yjs `AbstractType._callObserver`)
    if !is_local {
        for ty in changed.keys() {
            // SAFETY: store write lock held, no type borrowed.
            if let Some(mut ty) = unsafe { ty.ty_mut() }
                && let Some(markers) = &mut ty.markers
            {
                markers.clear();
            }
        }
    }

    // Another client advanced our clock: it uses our client ID. Yjs
    // `cleanupTransactions` switches to a new ID so our next edits cannot
    // collide with theirs.
    if client_clock_advanced {
        // Without randomness the host assigns identities: refuse local
        // writes until it sets a new one.
        #[cfg(feature = "random")]
        store.set_client(random_client_id());
        #[cfg(not(feature = "random"))]
        {
            store.client_required = true;
        }
    }

    // 6. the event
    if changes {
        store.commit_seq += 1;
    }
    // Release the subscription lock even when no event is encoded, before
    // the independent cleanup transaction takes its own subscription view.
    let subscribers = subscribers.filter(|_| deliver);
    let mut captured_primary = None;
    if need_event && let Some(summary) = summary {
        let update =
            encode_commit(store, &summary.before_state, &summary.deleted).expect("the store encodes its own structs");
        let event = CommitEvent {
            seq: store.commit_seq,
            summary,
            update,
        };
        if let Some(subscribers) = subscribers {
            if capture_event {
                captured_primary = Some(event.clone());
            }
            let ready = store.events.enqueue(
                event,
                subscribers.1.iter().map(|(_, callback)| callback.clone()).collect(),
            );
            drop(subscribers);
            AfterUnlock::Deliver(store.events.clone(), ready).schedule();
        } else if capture_event {
            captured_primary = Some(event);
        }
    } else {
        drop(subscribers);
    }

    let mut captured_cleanup = None;
    if !cleanup.is_empty() {
        // Separate collector, origin and event boundary, with no
        // intervening writer. Both commits are queued before unlocking and
        // callbacks.
        *before_state = store.get_state_vector();
        *local = true;
        *capture_history = false;
        *incoming = None;
        cleanup.run(store);
        // Keep the original origin owned by this transaction so its
        // destructor can defer release until the outermost unlock.
        let (cleanup_ev, _) = commit_store(
            store,
            before_state,
            local,
            capture_history,
            origin,
            incoming,
            Some(Origin::new(text::cleanup::FormattingCleanup)),
            capture_event,
        );
        captured_cleanup = cleanup_ev;
    }

    (captured_primary, captured_cleanup)
}

/// A local transaction that creates no structs of its own (history
/// bookkeeping, releasing retained content): it runs also while the document
/// waits for a client ID from the host.
pub(crate) fn transact_maintenance<R>(
    store_ref: &StoreRef,
    f: impl FnOnce(&mut TransactionMut<'_>) -> JwstCodecResult<R>,
) -> JwstCodecResult<R> {
    let mut tx = TransactionMut::begin_with(store_ref, None, true, false)?;
    let result = f(&mut tx);
    debug_assert!(
        !tx.store.client_required || tx.store.get_state(tx.store.client()) == tx.before_state.get(&tx.store.client()),
        "maintenance created structs while the document waits for a client ID"
    );
    tx.commit();
    result
}

/// Runs `f` in a write transaction and commits it, also when `f` fails: what
/// `f` changed stays in the document and is delivered like any other commit
/// (there is no rollback). A panic in `f` skips the
/// commit and poisons the document.
pub(crate) fn transact_mut_with<R>(
    store_ref: &StoreRef,
    origin: Option<Origin>,
    local: bool,
    f: impl FnOnce(&mut TransactionMut<'_>) -> JwstCodecResult<R>,
) -> JwstCodecResult<R> {
    let mut tx = TransactionMut::begin(store_ref, origin, local)?;
    let result = f(&mut tx);
    tx.commit();
    result
}

/// Runs `f` in a write transaction, commits it, and returns `(result, primary,
/// cleanup)` where `primary` and optional `cleanup` are the committed
/// [`CommitEvent`]s captured synchronously under the store lock.
pub(crate) fn transact_mut_with_events<R>(
    store_ref: &StoreRef,
    origin: Option<Origin>,
    local: bool,
    f: impl FnOnce(&mut TransactionMut<'_>) -> JwstCodecResult<R>,
) -> JwstCodecResult<(R, Option<CommitEvent>, Option<CommitEvent>)> {
    let mut tx = TransactionMut::begin(store_ref, origin, local)?;
    let result = f(&mut tx);
    let (primary, cleanup) = tx.commit_with_origin(None, true);
    result.map(|value| (value, primary, cleanup))
}

/// Changed types reported like Yjs `addChangedTypeToTransaction`: only types
/// that existed before the transaction and were not deleted by it.
fn changed_types(changed: &ChangedTypeRefs, before: &StateVector) -> (Vec<ChangedType>, Vec<TypeIdentity>) {
    let mut types = Vec::new();
    let mut ancestors = Vec::new();
    let mut seen = HashSet::new();

    for (ty_ref, keys) in changed {
        let Some(ty) = ty_ref.ty() else {
            continue;
        };
        if let Some(item) = ty.item.get()
            && (item.deleted() || item.id.clock >= before.get(&item.id.client))
        {
            continue;
        }
        let Ok(identity) = ty.identity() else {
            // a type never inserted into the document
            continue;
        };
        let mut keys = keys.iter().map(|key| key.to_string()).collect::<Vec<_>>();
        keys.sort();
        keys.dedup();
        types.push(ChangedType { identity, keys });

        let mut item = ty.item.clone();
        while let Some(Parent::Type(parent)) = item.get().and_then(|item| item.parent.clone()) {
            let Some(parent) = parent.ty() else {
                break;
            };
            let Ok(identity) = parent.identity() else {
                break;
            };
            if !seen.insert(identity.clone()) {
                break;
            }
            ancestors.push(identity);
            item = parent.item.clone();
        }
    }

    (types, ancestors)
}

/// Update V1 with the structs added since `before` and the `deleted` ranges
/// (Yjs `writeUpdateMessageFromTransaction`).
fn encode_commit(store: &DocStore, before: &StateVector, deleted: &DeleteSet) -> JwstCodecResult<Vec<u8>> {
    let update = Update {
        structs: DocStore::diff_structs(&store.items, before)?,
        delete_set: deleted.clone(),
        ..Update::default()
    };
    let mut encoder = RawEncoder::default();
    update.write(&mut encoder)?;
    Ok(encoder.into_inner())
}

impl Drop for TransactionMut<'_> {
    fn drop(&mut self) {
        // a panic inside the transaction: the changes are not committed and
        // the store lock gets poisoned with the guard
        debug_assert!(std::thread::panicking() || self.store.collector.is_empty());
        if let Some(origin) = self.origin.take() {
            after_unlock(move || drop(origin));
        }
    }
}

// ---------------------------------------------------------------------------
// Typed views inside transactions.

/// Reads of a [Text] inside a transaction.
pub struct TextRead<'t> {
    _store: &'t DocStore,
    _parent: &'t YTypeRef,
    ty: &'t YType,
}

impl<'t> TextRead<'t> {
    fn new(store: &'t DocStore, parent: &'t YTypeRef, ty: &'t YType) -> Self {
        Self {
            _store: store,
            _parent: parent,
            ty,
        }
    }

    pub fn len(&self) -> u64 {
        self.ty.len
    }

    pub fn is_empty(&self) -> bool {
        self.ty.len == 0
    }

    pub fn to_delta(&self) -> TextDelta {
        text::text_delta(self.ty)
    }

    pub fn identity_runs(&self) -> JwstCodecResult<Vec<TextIdentityRun>> {
        text::identity_runs(self.ty)
    }
}

impl fmt::Display for TextRead<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&text::text_string(self.ty))
    }
}

/// Reads and writes of a [Text] inside a write transaction.
pub struct TextWrite<'t, 'doc> {
    tx: &'t mut TransactionMut<'doc>,
    parent: &'t YTypeRef,
}

impl TextWrite<'_, '_> {
    pub fn read(&self) -> TextRead<'_> {
        TextRead::new(&self.tx.store, self.parent, self.tx.view(self.parent))
    }

    pub fn len(&self) -> u64 {
        self.read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    pub fn insert<T: ToString>(&mut self, index: u64, str: T) -> JwstCodecResult {
        let parent = self.parent;
        self.tx.with_type(parent, |store, ty| {
            list_insert(parent, store, ty, index, Content::String(str.to_string()))
        })
    }

    pub fn insert_embed<V: Into<Any>>(&mut self, index: u64, embed: V) -> JwstCodecResult {
        let parent = self.parent;
        let embed = embed.into();
        self.tx.with_type(parent, |store, ty| {
            text::text_insert_embed(parent, store, ty, index, embed)
        })
    }

    pub fn format(&mut self, index: u64, len: u64, attrs: TextAttributes) -> JwstCodecResult {
        let parent = self.parent;
        self.tx.with_type(parent, |store, ty| {
            text::text_format(parent, store, ty, index, len, attrs)
        })
    }

    pub fn remove(&mut self, index: u64, len: u64) -> JwstCodecResult {
        let parent = self.parent;
        self.tx
            .with_type(parent, |store, ty| text::text_remove(parent, store, ty, index, len))
    }

    pub fn apply_delta(&mut self, delta: &[TextDeltaOp]) -> JwstCodecResult {
        let parent = self.parent;
        self.tx
            .with_type(parent, |store, ty| text::apply_text_delta(parent, store, ty, delta))
    }
}

/// Reads of a [Map] inside a transaction.
pub struct MapRead<'t> {
    ty: &'t YType,
}

impl<'t> MapRead<'t> {
    pub fn get(&self, key: &str) -> Option<Value> {
        map::map_value(self.ty, key).map(|item| Value::from(&item.content))
    }

    pub fn contains_key(&self, key: &str) -> bool {
        map::map_value(self.ty, key).is_some()
    }

    pub fn len(&self) -> u64 {
        map::map_entries(self.ty).count() as u64
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The visible entries, borrowed from the transaction.
    pub fn iter(&self) -> impl Iterator<Item = (&'t str, Value)> + 't {
        map::map_entries(self.ty).map(|(key, item)| (key, Value::from(&item.content)))
    }

    pub fn keys(&self) -> impl Iterator<Item = &'t str> + 't {
        map::map_entries(self.ty).map(|(key, _)| key)
    }
}

/// Reads and writes of a [Map] inside a write transaction.
pub struct MapWrite<'t, 'doc> {
    tx: &'t mut TransactionMut<'doc>,
    parent: &'t YTypeRef,
}

impl MapWrite<'_, '_> {
    pub fn read(&self) -> MapRead<'_> {
        MapRead {
            ty: self.tx.view(self.parent),
        }
    }

    pub fn get(&self, key: &str) -> Option<Value> {
        self.read().get(key)
    }

    pub fn len(&self) -> u64 {
        self.read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    pub fn insert<V: Into<Value>>(&mut self, key: String, value: V) -> JwstCodecResult {
        let parent = self.parent;
        let content: Content = value.into().into();
        self.tx
            .with_type(parent, |store, ty| map::map_insert(parent, store, ty, key, content))
    }

    pub fn remove(&mut self, key: &str) {
        let parent = self.parent;
        let _ = self.tx.with_type(parent, |store, ty| {
            map::map_remove(store, ty, key);
            Ok(())
        });
    }

    /// Deletes every key.
    pub fn clear(&mut self) {
        let parent = self.parent;
        let _ = self.tx.with_type(parent, |store, ty| {
            map::map_clear(store, ty);
            Ok(())
        });
    }
}

/// Reads of an [Array] inside a transaction.
pub struct ArrayRead<'t> {
    parent: &'t YTypeRef,
    ty: &'t YType,
}

impl<'t> ArrayRead<'t> {
    pub fn len(&self) -> u64 {
        self.ty.len
    }

    pub fn is_empty(&self) -> bool {
        self.ty.len == 0
    }

    pub fn get(&self, index: u64) -> Option<Value> {
        array::array_get(self.parent, self.ty, index)
    }

    /// The values, borrowed from the transaction.
    pub fn iter(&self) -> impl Iterator<Item = Value> + 't {
        array::array_values(self.ty)
    }
}

/// Reads and writes of an [Array] inside a write transaction.
pub struct ArrayWrite<'t, 'doc> {
    tx: &'t mut TransactionMut<'doc>,
    parent: &'t YTypeRef,
}

impl ArrayWrite<'_, '_> {
    pub fn read(&self) -> ArrayRead<'_> {
        ArrayRead {
            parent: self.parent,
            ty: self.tx.view(self.parent),
        }
    }

    pub fn len(&self) -> u64 {
        self.read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    pub fn get(&self, index: u64) -> Option<Value> {
        self.read().get(index)
    }

    pub fn insert<V: Into<Value>>(&mut self, index: u64, value: V) -> JwstCodecResult {
        let parent = self.parent;
        let content: Content = value.into().into();
        self.tx
            .with_type(parent, |store, ty| list_insert(parent, store, ty, index, content))
    }

    pub fn push<V: Into<Value>>(&mut self, value: V) -> JwstCodecResult {
        let len = self.len();
        self.insert(len, value)
    }

    pub fn remove(&mut self, index: u64, len: u64) -> JwstCodecResult {
        let parent = self.parent;
        self.tx
            .with_type(parent, |store, ty| list_remove(parent, store, ty, index, len))
    }
}

/// Reads of an [XMLFragment] inside a transaction.
pub struct XMLFragmentRead<'t> {
    parent: &'t YTypeRef,
    ty: &'t YType,
}

impl<'t> XMLFragmentRead<'t> {
    pub fn len(&self) -> u64 {
        self.ty.len
    }

    pub fn is_empty(&self) -> bool {
        self.ty.len == 0
    }

    pub fn get(&self, index: u64) -> Option<Value> {
        array::array_get(self.parent, self.ty, index)
    }

    pub fn iter(&self) -> impl Iterator<Item = Value> + 't {
        array::array_values(self.ty)
    }

    pub fn first_child(&self) -> Option<Value> {
        xml::xml_first_child(self.ty)
    }

    pub fn parent(&self) -> Option<Value> {
        xml::xml_parent(self.ty)
    }

    pub fn tree_walker(&self) -> std::vec::IntoIter<Value> {
        xml::xml_tree_walker(self.ty).into_iter()
    }

    pub fn to_xml_string(&self) -> String {
        xml::xml_to_string(self.ty)
    }
}

impl fmt::Display for XMLFragmentRead<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_xml_string())
    }
}

/// Reads and writes of an [XMLFragment] inside a write transaction.
pub struct XMLFragmentWrite<'t, 'doc> {
    tx: &'t mut TransactionMut<'doc>,
    parent: &'t YTypeRef,
}

impl XMLFragmentWrite<'_, '_> {
    pub fn read(&self) -> XMLFragmentRead<'_> {
        XMLFragmentRead {
            parent: self.parent,
            ty: self.tx.view(self.parent),
        }
    }

    pub fn len(&self) -> u64 {
        self.read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    pub fn get(&self, index: u64) -> Option<Value> {
        self.read().get(index)
    }

    pub fn insert<V: Into<Value>>(&mut self, index: u64, value: V) -> JwstCodecResult {
        let parent = self.parent;
        let content: Content = value.into().into();
        self.tx
            .with_type(parent, |store, ty| list_insert(parent, store, ty, index, content))
    }

    pub fn push<V: Into<Value>>(&mut self, value: V) -> JwstCodecResult {
        let len = self.len();
        self.insert(len, value)
    }

    pub fn remove(&mut self, index: u64, len: u64) -> JwstCodecResult {
        let parent = self.parent;
        self.tx
            .with_type(parent, |store, ty| list_remove(parent, store, ty, index, len))
    }
}

/// Reads of an [XMLElement] inside a transaction.
pub struct XMLElementRead<'t> {
    parent: &'t YTypeRef,
    ty: &'t YType,
}

impl<'t> XMLElementRead<'t> {
    pub fn tag_name(&self) -> &'t str {
        xml::xml_tag_name(self.ty)
    }

    pub fn len(&self) -> u64 {
        self.ty.len
    }

    pub fn is_empty(&self) -> bool {
        self.ty.len == 0
    }

    pub fn get(&self, index: u64) -> Option<Value> {
        array::array_get(self.parent, self.ty, index)
    }

    pub fn iter(&self) -> impl Iterator<Item = Value> + 't {
        array::array_values(self.ty)
    }

    pub fn first_child(&self) -> Option<Value> {
        xml::xml_first_child(self.ty)
    }

    pub fn parent(&self) -> Option<Value> {
        xml::xml_parent(self.ty)
    }

    pub fn next_sibling(&self) -> Option<Value> {
        xml::xml_next_sibling(self.ty)
    }

    pub fn prev_sibling(&self) -> Option<Value> {
        xml::xml_prev_sibling(self.ty)
    }

    pub fn tree_walker(&self) -> std::vec::IntoIter<Value> {
        xml::xml_tree_walker(self.ty).into_iter()
    }

    pub fn get_attribute(&self, name: &str) -> Option<Value> {
        map::map_value(self.ty, name).map(|item| Value::from(&item.content))
    }

    pub fn contains_attribute(&self, name: &str) -> bool {
        map::map_value(self.ty, name).is_some()
    }

    pub fn attributes(&self) -> Vec<(String, Value)> {
        xml::xml_attributes(self.ty)
    }

    pub fn to_xml_string(&self) -> String {
        xml::xml_to_string(self.ty)
    }
}

impl fmt::Display for XMLElementRead<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_xml_string())
    }
}

/// Reads and writes of an [XMLElement] inside a write transaction.
pub struct XMLElementWrite<'t, 'doc> {
    tx: &'t mut TransactionMut<'doc>,
    parent: &'t YTypeRef,
}

impl XMLElementWrite<'_, '_> {
    pub fn read(&self) -> XMLElementRead<'_> {
        XMLElementRead {
            parent: self.parent,
            ty: self.tx.view(self.parent),
        }
    }

    pub fn tag_name(&self) -> &str {
        self.read().tag_name()
    }

    pub fn len(&self) -> u64 {
        self.read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    pub fn get(&self, index: u64) -> Option<Value> {
        self.read().get(index)
    }

    pub fn get_attribute(&self, name: &str) -> Option<Value> {
        self.read().get_attribute(name)
    }

    pub fn set_attribute<K: Into<String>, V: Into<Value>>(&mut self, name: K, value: V) -> JwstCodecResult {
        let parent = self.parent;
        let content: Content = value.into().into();
        self.tx.with_type(parent, |store, ty| {
            map::map_insert(parent, store, ty, name.into(), content)
        })
    }

    pub fn remove_attribute(&mut self, name: &str) -> JwstCodecResult {
        let parent = self.parent;
        self.tx.with_type(parent, |store, ty| {
            map::map_remove(store, ty, name);
            Ok(())
        })
    }

    pub fn insert<V: Into<Value>>(&mut self, index: u64, value: V) -> JwstCodecResult {
        let parent = self.parent;
        let content: Content = value.into().into();
        self.tx
            .with_type(parent, |store, ty| list_insert(parent, store, ty, index, content))
    }

    pub fn push<V: Into<Value>>(&mut self, value: V) -> JwstCodecResult {
        let len = self.len();
        self.insert(len, value)
    }

    pub fn remove(&mut self, index: u64, len: u64) -> JwstCodecResult {
        let parent = self.parent;
        self.tx
            .with_type(parent, |store, ty| list_remove(parent, store, ty, index, len))
    }
}

/// Reads of an [XMLText] inside a transaction.
pub struct XMLTextRead<'t> {
    ty: &'t YType,
}

impl<'t> XMLTextRead<'t> {
    pub fn len(&self) -> u64 {
        self.ty.len
    }

    pub fn is_empty(&self) -> bool {
        self.ty.len == 0
    }

    pub fn to_delta(&self) -> TextDelta {
        text::text_delta(self.ty)
    }

    pub fn identity_runs(&self) -> JwstCodecResult<Vec<TextIdentityRun>> {
        text::identity_runs(self.ty)
    }

    pub fn parent(&self) -> Option<Value> {
        xml::xml_parent(self.ty)
    }

    pub fn next_sibling(&self) -> Option<Value> {
        xml::xml_next_sibling(self.ty)
    }

    pub fn prev_sibling(&self) -> Option<Value> {
        xml::xml_prev_sibling(self.ty)
    }

    pub fn to_xml_string(&self) -> String {
        xml::xml_text_to_string(self.ty)
    }
}

impl fmt::Display for XMLTextRead<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_xml_string())
    }
}

/// Reads and writes of an [XMLText] inside a write transaction.
pub struct XMLTextWrite<'t, 'doc> {
    tx: &'t mut TransactionMut<'doc>,
    parent: &'t YTypeRef,
}

impl XMLTextWrite<'_, '_> {
    pub fn read(&self) -> XMLTextRead<'_> {
        XMLTextRead {
            ty: self.tx.view(self.parent),
        }
    }

    pub fn len(&self) -> u64 {
        self.read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    pub fn insert<T: ToString>(&mut self, index: u64, str: T) -> JwstCodecResult {
        let parent = self.parent;
        self.tx.with_type(parent, |store, ty| {
            list_insert(parent, store, ty, index, Content::String(str.to_string()))
        })
    }

    pub fn insert_embed<V: Into<Any>>(&mut self, index: u64, embed: V) -> JwstCodecResult {
        let parent = self.parent;
        let embed = embed.into();
        self.tx.with_type(parent, |store, ty| {
            text::text_insert_embed(parent, store, ty, index, embed)
        })
    }

    pub fn format(&mut self, index: u64, len: u64, attrs: TextAttributes) -> JwstCodecResult {
        let parent = self.parent;
        self.tx.with_type(parent, |store, ty| {
            text::text_format(parent, store, ty, index, len, attrs)
        })
    }

    pub fn remove(&mut self, index: u64, len: u64) -> JwstCodecResult {
        let parent = self.parent;
        self.tx
            .with_type(parent, |store, ty| text::text_remove(parent, store, ty, index, len))
    }

    pub fn apply_delta(&mut self, delta: &[TextDeltaOp]) -> JwstCodecResult {
        let parent = self.parent;
        self.tx
            .with_type(parent, |store, ty| text::apply_text_delta(parent, store, ty, delta))
    }
}

/// Reads of an [XMLHook] inside a transaction.
pub struct XMLHookRead<'t> {
    ty: &'t YType,
}

impl<'t> XMLHookRead<'t> {
    pub fn hook_name(&self) -> &'t str {
        xml::xml_hook_name(self.ty)
    }

    pub fn get(&self, key: &str) -> Option<Value> {
        map::map_value(self.ty, key).map(|item| Value::from(&item.content))
    }

    pub fn contains_key(&self, key: &str) -> bool {
        map::map_value(self.ty, key).is_some()
    }

    pub fn len(&self) -> u64 {
        map::map_entries(self.ty).count() as u64
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> impl Iterator<Item = (&'t str, Value)> + 't {
        map::map_entries(self.ty).map(|(key, item)| (key, Value::from(&item.content)))
    }

    pub fn keys(&self) -> impl Iterator<Item = &'t str> + 't {
        map::map_entries(self.ty).map(|(key, _)| key)
    }

    pub fn parent(&self) -> Option<Value> {
        xml::xml_parent(self.ty)
    }

    pub fn next_sibling(&self) -> Option<Value> {
        xml::xml_next_sibling(self.ty)
    }

    pub fn prev_sibling(&self) -> Option<Value> {
        xml::xml_prev_sibling(self.ty)
    }
}

/// Reads and writes of an [XMLHook] inside a write transaction.
pub struct XMLHookWrite<'t, 'doc> {
    tx: &'t mut TransactionMut<'doc>,
    parent: &'t YTypeRef,
}

impl XMLHookWrite<'_, '_> {
    pub fn read(&self) -> XMLHookRead<'_> {
        XMLHookRead {
            ty: self.tx.view(self.parent),
        }
    }

    pub fn hook_name(&self) -> &str {
        self.read().hook_name()
    }

    pub fn get(&self, key: &str) -> Option<Value> {
        self.read().get(key)
    }

    pub fn len(&self) -> u64 {
        self.read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    pub fn insert<V: Into<Value>>(&mut self, key: String, value: V) -> JwstCodecResult {
        let parent = self.parent;
        let content: Content = value.into().into();
        self.tx
            .with_type(parent, |store, ty| map::map_insert(parent, store, ty, key, content))
    }

    pub fn remove(&mut self, key: &str) -> JwstCodecResult {
        let parent = self.parent;
        self.tx.with_type(parent, |store, ty| {
            map::map_remove(store, ty, key);
            Ok(())
        })
    }

    pub fn clear(&mut self) -> JwstCodecResult {
        let parent = self.parent;
        self.tx.with_type(parent, |store, ty| {
            map::map_clear(store, ty);
            Ok(())
        })
    }
}
