//! Collaborative undo and redo, adapted from Yjs v13.6.33 (`UndoManager.js`
//! and `redoItem`, MIT, Copyright (c) 2023 Kevin Jahns).
//!
//! One [UndoManager] serves a document. Scope it to the shared types being
//! edited. By default it captures local transactions without an origin.
//! Register an origin explicitly to capture matching remote transactions.
//! Tracked origin instances match by identity. The host supplies the capture
//! clock through [UndoManager::advance_time].
//!
//! Before collection, the manager retains deleted content needed by a stack
//! item. Undo removes that item's insertions and recreates its deletions
//! under new IDs. The redo map follows those IDs across splits and merges.
//! Popping or clearing items releases content unused by the remaining stacks.

use std::{
    any::Any as StdAny,
    fmt, mem,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use super::{store::StoreRef, *};

/// Gives every manager its own undo origin.
static NEXT_MANAGER: AtomicU64 = AtomicU64::new(1);

/// What an [UndoManager] tracks: the whole document or a type and everything
/// below it.
#[derive(Debug, Clone)]
pub struct UndoScope(Scope);

#[derive(Debug, Clone, PartialEq)]
enum Scope {
    Doc,
    Type(YTypeRef),
}

impl From<&Doc> for UndoScope {
    fn from(_: &Doc) -> Self {
        Self(Scope::Doc)
    }
}

macro_rules! impl_scope {
    ($($name: ident),*) => {
        $(
            impl From<&$name> for UndoScope {
                fn from(value: &$name) -> Self {
                    Self(Scope::Type(value.0.clone()))
                }
            }
        )*
    };
}

impl_scope!(Text, Map, Array, XMLElement, XMLFragment, XMLText, XMLHook);

/// Which stack an operation pops or inspects.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UndoStack {
    Undo,
    Redo,
}

/// The origin of the transactions [UndoManager::undo] and
/// [UndoManager::redo] commit, visible in their [CommitEvent]s.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UndoOrigin {
    manager: u64,
    stack: UndoStack,
}

impl UndoOrigin {
    /// The stack the transaction popped: [UndoStack::Undo] for an undo.
    pub fn stack(&self) -> UndoStack {
        self.stack
    }

    #[cfg(feature = "session")]
    pub(crate) fn new_for_session(manager: u64, stack: UndoStack) -> Self {
        Self { manager, stack }
    }

    #[cfg(feature = "session")]
    pub(crate) fn manager(&self) -> u64 {
        self.manager
    }
}

#[cfg(feature = "session")]
pub(crate) fn next_manager_id() -> u64 {
    NEXT_MANAGER.fetch_add(1, Ordering::Relaxed)
}

/// Options of an [UndoManager], after Yjs `UndoManagerOptions`.
#[derive(Debug, Clone)]
pub struct UndoOptions {
    /// Captured commits less than this many milliseconds after the previous
    /// one join its stack item (Yjs `captureTimeout`), measured with the time
    /// the host reports through [UndoManager::advance_time].
    pub capture_timeout: u64,
    /// Origins of the commits that are captured (Yjs `trackedOrigins`).
    ///
    /// `None` matches local transactions without origin, including the single
    /// write methods, but never a remote update ([Doc::apply_update]): remote
    /// changes stay out of the local user's history unless their origin is
    /// tracked explicitly here (Yjs also captures remote updates applied with
    /// the `null` origin).
    ///
    /// An origin matches itself and its clones (Yjs compares origin objects
    /// by identity), so the document's own code never calls the origin
    /// value's `PartialEq` under the lock; see also
    /// [UndoManager::track_origin_type].
    pub tracked_origins: Vec<Option<Origin>>,
}

impl Default for UndoOptions {
    fn default() -> Self {
        Self {
            capture_timeout: 500,
            tracked_origins: vec![None],
        }
    }
}

/// A stack item as seen by the caller: its id, stable while it is on a
/// stack, and the metadata the caller attached to it (Yjs `StackItem.meta`,
/// for example the selection to restore).
#[derive(Debug, Clone, PartialEq)]
pub struct UndoItem<M> {
    pub id: u64,
    /// Shared with the stack item while it is on a stack: reading it never
    /// runs `M`'s code.
    pub meta: Option<Arc<M>>,
}

#[derive(Debug)]
pub(crate) struct StackItem {
    id: u64,
    insertions: DeleteSet,
    deletions: DeleteSet,
    /// Deleted items of the scope in `deletions` with their ancestors.
    retained: DeleteSet,
    /// The caller's metadata. Under the document lock it is only moved or
    /// its pointer cloned; values leaving a stack are released after the
    /// thread's last document lock ([after_unlock]).
    meta: Option<Meta>,
}

/// Type-erased caller metadata, see [UndoManager].
pub(crate) type Meta = Arc<dyn StdAny + Send + Sync>;

/// The metadata of an [UndoManager<M>] as `M`.
pub(crate) fn downcast<M: Send + Sync + 'static>(meta: Meta) -> Arc<M> {
    meta.downcast()
        .unwrap_or_else(|_| unreachable!("metadata of this manager's type"))
}

/// Releases caller metadata once this thread holds no document lock.
fn release_meta(meta: Vec<Meta>) {
    if !meta.is_empty() {
        release_later(meta);
    }
}

/// Drops `value` (caller metadata, origins, a manager's state) once this
/// thread holds no document lock, of any document: right away when it holds
/// none.
fn release_later<T: Send + 'static>(value: T) {
    after_unlock(move || drop(value));
}

type OriginMatcher = fn(&Origin) -> bool;

/// The manager's state. It lives in the store as its history hook, so it is
/// only touched under the document lock. No caller code runs there: no
/// clock, metadata only as shared pointers, origins compared by identity.
pub(in crate::doc) struct UndoState {
    manager: u64,
    scope: Vec<Scope>,
    tracked: Vec<Option<Origin>>,
    tracked_types: Vec<OriginMatcher>,
    capture_timeout: u64,
    /// The latest time the host reported, shared with the manager handle.
    now: Arc<AtomicU64>,
    undo: Vec<StackItem>,
    redo: Vec<StackItem>,
    last_change: u64,
    next_item: u64,
}

impl fmt::Debug for UndoState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("UndoState")
            .field("manager", &self.manager)
            .field("undo", &self.undo.len())
            .field("redo", &self.redo.len())
            .finish_non_exhaustive()
    }
}

/// Undo and redo of the local changes to a scope of one document, after Yjs
/// `UndoManager`. A document has at most one manager: it is the document's
/// history stage and owns the content kept from GC for it. Dropping the
/// manager releases that content.
///
/// `M` is the metadata the caller attaches to stack items. It lives with
/// its stack item, behind a shared pointer that [UndoManager::peek],
/// [UndoManager::undo] and [UndoManager::redo] hand out (`M` is never
/// cloned), and the manager drops its share once the thread holds no
/// document lock.
///
/// The capture window is measured with the time the host reports through
/// [UndoManager::advance_time]; until it reports one, every captured commit
/// is a stack item of its own.
///
/// ```
/// use y_octo::{DocOptions, UndoManager, UndoOptions};
///
/// let doc = DocOptions::from_identity(101, "note".into()).build();
/// let mut text = doc.get_or_create_text("text").unwrap();
/// let undo = UndoManager::<()>::new(&doc, [(&text).into()], UndoOptions::default()).unwrap();
///
/// text.insert(0, "hello").unwrap();
/// undo.undo().unwrap();
/// assert_eq!(text.to_string(), "");
/// undo.redo().unwrap();
/// assert_eq!(text.to_string(), "hello");
/// ```
pub struct UndoManager<M: Send + Sync + 'static = ()> {
    store: StoreRef,
    manager: u64,
    now: Arc<AtomicU64>,
    _meta: std::marker::PhantomData<fn() -> M>,
}

impl<M: Send + Sync + 'static> fmt::Debug for UndoManager<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("UndoManager").field("manager", &self.manager).finish()
    }
}

impl<M: Send + Sync + 'static> UndoManager<M> {
    /// Starts capturing the changes to `scope`. Fails with
    /// [JwstCodecError::UndoManagerExists] when the document has a manager.
    pub fn new(doc: &Doc, scope: impl IntoIterator<Item = UndoScope>, options: UndoOptions) -> JwstCodecResult<Self> {
        let manager = NEXT_MANAGER.fetch_add(1, Ordering::Relaxed);
        let now = Arc::new(AtomicU64::new(0));
        let mut state = UndoState {
            manager,
            scope: Vec::new(),
            tracked: Vec::new(),
            tracked_types: Vec::new(),
            capture_timeout: options.capture_timeout,
            now: now.clone(),
            undo: Vec::new(),
            redo: Vec::new(),
            last_change: 0,
            next_item: 0,
        };
        for origin in options.tracked_origins {
            state.track(origin);
        }
        let scope = scope.into_iter().collect::<Vec<_>>();
        // the store identity is read without the lock; type data only under it
        for scope in &scope {
            if let Err(error) = check_store(&scope.0, &doc.store) {
                release_later(state);
                return Err(error);
            }
        }

        let mut store = match write_store(&doc.store) {
            Ok(store) => store,
            Err(error) => {
                release_later(state);
                return Err(error);
            }
        };
        if store.history_hook.is_some() {
            drop(store);
            release_later(state);
            return Err(JwstCodecError::UndoManagerExists);
        }
        for scope in scope {
            if let Err(error) = state.add_to_scope(scope) {
                drop(store);
                release_later(state);
                return Err(error);
            }
        }
        store.history_hook = Some(Box::new(state));
        Ok(Self {
            store: doc.store.clone(),
            manager,
            now,
            _meta: Default::default(),
        })
    }

    /// Reports the host's monotonic time in milliseconds (greater than zero),
    /// read by the commits after it (on any thread) to decide whether they
    /// join the last stack item. A time older than one reported before is
    /// ignored. Takes no document lock.
    pub fn advance_time(&self, now_ms: u64) {
        self.now.fetch_max(now_ms, Ordering::AcqRel);
    }

    /// Undoes the last stack item that still changes the document, skipping
    /// (and dropping) items whose changes were all overwritten. Returns the
    /// item undone with its metadata; its changes are now the top of the redo
    /// stack.
    pub fn undo(&self) -> JwstCodecResult<Option<UndoItem<M>>> {
        self.pop(UndoStack::Undo)
    }

    /// Redoes the last undone stack item, see [UndoManager::undo].
    pub fn redo(&self) -> JwstCodecResult<Option<UndoItem<M>>> {
        self.pop(UndoStack::Redo)
    }

    pub fn can_undo(&self) -> bool {
        self.read(|state| !state.undo.is_empty())
    }

    pub fn can_redo(&self) -> bool {
        self.read(|state| !state.redo.is_empty())
    }

    /// The next commit starts a new stack item (Yjs `stopCapturing`).
    pub fn stop_capturing(&self) -> JwstCodecResult {
        self.write_maintenance(|state, _| state.last_change = 0)
    }

    /// Empties the given stacks and releases the content they retained.
    pub fn clear(&self, undo: bool, redo: bool) -> JwstCodecResult {
        self.write_maintenance(|state, store| {
            if undo {
                state.drop_items(UndoStack::Undo);
            }
            if redo {
                state.drop_items(UndoStack::Redo);
            }
            state.release(store);
        })
    }

    /// The top item of `stack`. Its metadata is shared, not cloned.
    pub fn peek(&self, stack: UndoStack) -> Option<UndoItem<M>> {
        let (id, meta) = self.read(|state| state.stack(stack).last().map(|item| (item.id, item.meta.clone())))?;
        Some(UndoItem {
            id,
            meta: meta.map(downcast),
        })
    }

    /// Replaces the metadata of the item `id` of `stack`. Returns whether the
    /// item is on that stack.
    pub fn set_meta(&self, stack: UndoStack, id: u64, meta: M) -> JwstCodecResult<bool> {
        // stays here if the transaction cannot start, to be released like
        // any other caller value
        let mut meta = Some(Arc::new(meta) as Meta);
        let result = self.write_maintenance(|state, _| {
            let stack = match stack {
                UndoStack::Undo => &mut state.undo,
                UndoStack::Redo => &mut state.redo,
            };
            // ids grow with every new item: each stack is sorted by id
            match stack.binary_search_by_key(&id, |item| item.id) {
                Ok(index) => (true, mem::replace(&mut stack[index].meta, meta.take())),
                Err(_) => (false, None),
            }
        });
        release_later(meta);
        let (found, previous) = result?;
        release_later(previous);
        Ok(found)
    }

    /// Extends the scope (Yjs `addToScope`).
    pub fn add_to_scope(&self, scope: UndoScope) -> JwstCodecResult {
        check_store(&scope.0, &self.store)?;
        self.write_maintenance(|state, _| state.add_to_scope(scope))?
    }

    /// Captures commits with `origin` (or a clone of it).
    pub fn add_tracked_origin(&self, origin: Option<Origin>) -> JwstCodecResult {
        // an origin already tracked comes back and is dropped here
        let mut origin = Some(origin);
        let result = self.write_maintenance(|state, _| state.track(origin.take().expect("taken once")));
        release_later(origin);
        release_later(result?);
        Ok(())
    }

    /// Stops capturing commits with `origin` (or a clone of it).
    pub fn remove_tracked_origin(&self, origin: &Option<Origin>) -> JwstCodecResult {
        // the removed origins are dropped after the lock is released
        let removed = self.write_maintenance(|state, _| {
            let (removed, kept) = std::mem::take(&mut state.tracked)
                .into_iter()
                .partition::<Vec<_>, _>(|tracked| same_origin(tracked, origin));
            state.tracked = kept;
            removed
        })?;
        release_later(removed);
        Ok(())
    }

    /// Captures commits whose origin holds a `T`, whatever its value (Yjs
    /// tracking an origin's constructor).
    pub fn track_origin_type<T: 'static>(&self) -> JwstCodecResult {
        self.write_maintenance(|state, _| {
            state.tracked_types.push(|origin| origin.downcast_ref::<T>().is_some());
        })
    }

    fn pop(&self, stack: UndoStack) -> JwstCodecResult<Option<UndoItem<M>>> {
        Ok(self.pop_with_event(stack)?.map(|(item, _)| item))
    }

    pub(crate) fn pop_with_event(
        &self,
        stack: UndoStack,
    ) -> JwstCodecResult<Option<(UndoItem<M>, Option<CommitEvent>)>> {
        let origin = Origin::new(UndoOrigin {
            manager: self.manager,
            stack,
        });
        // the popped item's metadata is moved out under the lock, before the
        // commit event is delivered
        let (performed, event, _) = transact_mut_with_events(&self.store, Some(origin), true, |tx| {
            let store_ref = tx.store_ref();
            let store = tx.store_mut();
            let mut hook = store.history_hook.take();
            let state = hook
                .as_deref_mut()
                .and_then(|hook| hook.as_any_mut().downcast_mut::<UndoState>())
                .expect("the manager owns the history hook");
            let result = state.pop(store, store_ref, stack);
            store.history_hook = hook;
            Ok(result)
        })?;
        Ok(performed.map(|(id, meta)| {
            (
                UndoItem {
                    id,
                    meta: meta.map(downcast),
                },
                event,
            )
        }))
    }

    fn read<R>(&self, f: impl FnOnce(&UndoState) -> R) -> R {
        let store = read_store_or_panic(&self.store);
        f(state(store.history_hook.as_deref()))
    }

    /// Runs bookkeeping `f` on the state inside a maintenance transaction,
    /// which runs also while the document waits for a client ID from the host.
    fn write_maintenance<R>(&self, f: impl FnOnce(&mut UndoState, &mut DocStore) -> R) -> JwstCodecResult<R> {
        transact_maintenance(&self.store, |tx| {
            let store = tx.store_mut();
            // the commit runs the hook, after it is back in place
            let mut hook = store.history_hook.take();
            let state = hook
                .as_deref_mut()
                .and_then(|hook| hook.as_any_mut().downcast_mut::<UndoState>())
                .expect("the manager owns the history hook");
            let result = f(state, store);
            store.history_hook = hook;
            Ok(result)
        })
    }
}

fn state(hook: Option<&dyn CommitHook>) -> &UndoState {
    hook.and_then(|hook| hook.as_any().downcast_ref())
        .expect("the manager owns the history hook")
}

impl<M: Send + Sync + 'static> Drop for UndoManager<M> {
    fn drop(&mut self) {
        let (store, manager) = (self.store.clone(), self.manager);
        // Dropped inside a transaction of this document (or while another
        // document lock is busy): release once this thread holds no document
        // lock any more. A poisoned or released document is not written.
        let released = release_manager(&store, manager);
        if let Err(JwstCodecError::Reentrant | JwstCodecError::NestedDocumentBusy) = released {
            after_unlock(move || {
                let _ = release_manager(&store, manager);
            });
        }
    }
}

/// Removes the hook of `manager` (not of a manager registered after it) and
/// releases its retained content. The state, with its tracked origins, is
/// dropped after the lock is released.
fn release_manager(store: &StoreRef, manager: u64) -> JwstCodecResult {
    let hook = transact_maintenance(store, |tx| {
        let store = tx.store_mut();
        let ours = store
            .history_hook
            .as_deref()
            .and_then(|hook| hook.as_any().downcast_ref::<UndoState>())
            .is_some_and(|state| state.manager == manager);
        if !ours {
            return Ok(None);
        }
        store.set_retained(DeleteSet::default());
        Ok(store.history_hook.take())
    })?;
    release_later(hook);
    Ok(())
}

impl CommitHook for UndoState {
    fn on_commit(&mut self, store: &mut DocStore, summary: &CommitSummary) {
        let (released, retained) = self.on_commit_raw(store, summary);
        if released {
            self.release(store);
        } else if !retained.is_empty() {
            store.add_retained(&retained);
        }
    }

    fn as_any(&self) -> &dyn StdAny {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn StdAny {
        self
    }
}

impl UndoState {
    #[cfg(feature = "session")]
    pub(crate) fn new_for_session(
        manager: u64,
        scopes: Vec<YTypeRef>,
        tracked: Vec<Option<Origin>>,
        capture_timeout: u64,
        now: Arc<AtomicU64>,
    ) -> JwstCodecResult<Self> {
        let mut state = Self {
            manager,
            scope: Vec::new(),
            tracked: Vec::new(),
            tracked_types: Vec::new(),
            capture_timeout,
            now,
            undo: Vec::new(),
            redo: Vec::new(),
            last_change: 0,
            next_item: 0,
        };
        for origin in tracked {
            state.track(origin);
        }
        if scopes.is_empty() {
            state.scope.push(Scope::Doc);
        } else {
            for ty in scopes {
                state.add_to_scope(UndoScope(Scope::Type(ty)))?;
            }
        }
        Ok(state)
    }

    #[cfg(feature = "session")]
    pub(crate) fn manager_id(&self) -> u64 {
        self.manager
    }

    #[cfg(feature = "session")]
    pub(crate) fn can_undo_redo(&self) -> (bool, bool) {
        (!self.undo.is_empty(), !self.redo.is_empty())
    }

    #[cfg(feature = "session")]
    pub(crate) fn stack_slices(&self) -> [&[StackItem]; 2] {
        [self.undo.as_slice(), self.redo.as_slice()]
    }

    #[cfg(feature = "session")]
    pub(crate) fn clear_stacks(&mut self, undo: bool, redo: bool) {
        if undo {
            self.drop_items(UndoStack::Undo);
        }
        if redo {
            self.drop_items(UndoStack::Redo);
        }
    }

    #[cfg(feature = "session")]
    pub(crate) fn stop_capturing(&mut self) {
        self.last_change = 0;
    }

    #[cfg(feature = "session")]
    pub(crate) fn set_top_meta(&mut self, stack: UndoStack, meta: Meta) -> (bool, Option<Meta>) {
        let stack = match stack {
            UndoStack::Undo => &mut self.undo,
            UndoStack::Redo => &mut self.redo,
        };
        match stack.last_mut() {
            Some(top) => (true, top.meta.replace(meta)),
            None => (false, Some(meta)),
        }
    }

    /// Processes a commit against this stack without updating `store.retained`.
    /// Returns `(released, newly_retained)`.
    pub(crate) fn on_commit_raw(&mut self, store: &DocStore, summary: &CommitSummary) -> (bool, DeleteSet) {
        let popped = summary
            .origin
            .as_ref()
            .and_then(|origin| origin.downcast_ref::<UndoOrigin>())
            .filter(|origin| origin.manager == self.manager)
            .map(|origin| origin.stack);
        if !self.scope_changed(summary) || popped.is_none() && !self.tracks(summary) {
            return (false, DeleteSet::default());
        }

        let undoing = popped == Some(UndoStack::Undo);
        let redoing = popped == Some(UndoStack::Redo);
        let mut released = false;
        if undoing {
            // the next undo does not join this item
            self.last_change = 0;
        } else if !redoing && !self.redo.is_empty() {
            // a new change: what was undone can no longer be redone
            self.drop_items(UndoStack::Redo);
            released = true;
        }

        let mut retained = DeleteSet::default();
        for_each_item(store, &summary.deleted, |item| {
            if self.in_scope(item) {
                DocStore::retain_with_ancestors(&mut retained, item);
            }
        });

        let now = self.now.load(Ordering::Acquire);
        let join =
            self.last_change > 0 && now.saturating_sub(self.last_change) < self.capture_timeout && !undoing && !redoing;
        let next_item = &mut self.next_item;
        let stack = if undoing { &mut self.redo } else { &mut self.undo };
        match stack.last_mut() {
            Some(last) if join => {
                last.deletions.merge(&summary.deleted);
                last.insertions.merge(&summary.inserted);
                last.retained.merge(&retained);
            }
            _ => {
                stack.push(StackItem {
                    id: *next_item,
                    insertions: summary.inserted.clone(),
                    deletions: summary.deleted.clone(),
                    retained: retained.clone(),
                    meta: None,
                });
                *next_item += 1;
            }
        }
        if !undoing && !redoing {
            self.last_change = now;
        }

        (released, retained)
    }

    /// Computes the union of retained ranges required by this stack without
    /// modifying `store.retained`.
    pub(crate) fn retained_set(&self) -> DeleteSet {
        let mut retained = DeleteSet::default();
        for item in self.undo.iter().chain(&self.redo) {
            retained.merge(&item.retained);
        }
        retained
    }
    fn stack(&self, stack: UndoStack) -> &[StackItem] {
        match stack {
            UndoStack::Undo => &self.undo,
            UndoStack::Redo => &self.redo,
        }
    }

    /// Tracks `origin` unless it is tracked already; returns it then.
    fn track(&mut self, origin: Option<Origin>) -> Option<Option<Origin>> {
        if self.tracked.iter().any(|tracked| same_origin(tracked, &origin)) {
            return Some(origin);
        }
        self.tracked.push(origin);
        None
    }

    /// Empties `stack`; the metadata of its items is released after the
    /// lock.
    fn drop_items(&mut self, stack: UndoStack) {
        let items = match stack {
            UndoStack::Undo => mem::take(&mut self.undo),
            UndoStack::Redo => mem::take(&mut self.redo),
        };
        release_meta(items.into_iter().filter_map(|item| item.meta).collect());
    }

    fn add_to_scope(&mut self, scope: UndoScope) -> JwstCodecResult {
        if let Scope::Type(ty) = &scope.0 {
            // a scope is a mounted type: commits report changes by identity
            if ty.ty().is_none_or(|ty| ty.is_preliminary()) {
                return Err(JwstCodecError::InvalidParent);
            }
        }
        if !self.scope.contains(&scope.0) {
            self.scope.push(scope.0);
        }
        Ok(())
    }

    /// Whether the commit changed something in the scope (Yjs:
    /// `changedParentTypes` has a scope type).
    fn scope_changed(&self, summary: &CommitSummary) -> bool {
        self.scope.iter().any(|scope| match scope {
            Scope::Doc => true,
            Scope::Type(ty) => ty
                .ty()
                .and_then(|ty| ty.identity().ok())
                .is_some_and(|identity| summary.touches_subtree(&identity)),
        })
    }

    fn tracks(&self, summary: &CommitSummary) -> bool {
        match &summary.origin {
            None => summary.local && self.tracked.contains(&None),
            origin @ Some(value) => {
                self.tracked.iter().any(|tracked| same_origin(tracked, origin))
                    || self.tracked_types.iter().any(|matches| matches(value))
            }
        }
    }

    /// Yjs `isParentOf` for any scope type, or a document scope.
    fn in_scope(&self, item: &Item) -> bool {
        self.scope.iter().any(|scope| match scope {
            Scope::Doc => true,
            Scope::Type(ty) => is_parent_of(ty, item),
        })
    }

    /// Retains exactly what the remaining stack items need and collects the
    /// rest.
    fn release(&self, store: &mut DocStore) {
        store.set_retained(self.retained_set());
    }

    /// Yjs `popStackItem`, in the transaction of an undo or redo.
    /// Returns the id and metadata of the item that changed the document.
    fn pop(&mut self, store: &mut DocStore, store_ref: &StoreRef, stack: UndoStack) -> Option<(u64, Option<Meta>)> {
        let performed = self.pop_with_extra_stacks(store, store_ref, stack, &[]);
        self.release(store);
        performed
    }

    /// Pops one stack item while consulting `other_stacks` in addition to this
    /// stack's own undo/redo stacks. Does **not** call `store.set_retained`;
    /// the caller is responsible for recomputing the combined retained set.
    pub(crate) fn pop_with_extra_stacks(
        &mut self,
        store: &mut DocStore,
        store_ref: &StoreRef,
        stack: UndoStack,
        other_stacks: &[&[StackItem]],
    ) -> Option<(u64, Option<Meta>)> {
        let mut performed = None;
        while performed.is_none() {
            let popped = match stack {
                UndoStack::Undo => self.undo.pop(),
                UndoStack::Redo => self.redo.pop(),
            };
            let Some(item) = popped else {
                break;
            };

            let mut to_delete = Vec::new();
            // Follow what a redo recreated, also from structs collected since:
            // the redo map outlives them (and a collected struct may cover
            // more than this item inserted).
            let mut clients = item.insertions.keys().copied().collect::<Vec<_>>();
            clients.sort_unstable();
            for client in clients {
                let state = store.get_state(client);
                for range in item.insertions[&client].canonical_ranges() {
                    let mut clock = range.start;
                    let end = range.end.min(state);
                    while clock < end {
                        let id = Id::new(client, clock);
                        let mut targets = Vec::new();
                        let len = match store.redone.range_at(id) {
                            Ok(len) => {
                                let len = len.min(end - clock);
                                for (redone, len) in store.redone.follow_range(id, len) {
                                    targets.extend(clean_items(store, redone, len));
                                }
                                len
                            }
                            Err(gap) => {
                                let len = gap.min(end - clock);
                                targets.extend(clean_items(store, id, len));
                                len
                            }
                        };
                        clock += len;
                        for target in targets {
                            if target.get().is_some_and(|item| !item.deleted() && self.in_scope(item)) {
                                to_delete.push(target);
                            }
                        }
                    }
                }
            }

            let mut to_redo = Vec::new();
            let mut redo_ids = HashSet::new();
            for node in clean_structs(store, &item.deletions) {
                let Node::Item(item_ref) = node else {
                    continue;
                };
                let struct_item = item_ref.get().expect("live structs");
                // never recreate what the same capture window inserted
                if self.in_scope(struct_item) && !contains(&item.insertions, struct_item.id) {
                    redo_ids.insert(struct_item.id);
                    to_redo.push(item_ref);
                }
            }

            let mut all_stacks: Vec<&[StackItem]> = Vec::with_capacity(2 + other_stacks.len());
            all_stacks.push(self.undo.as_slice());
            all_stacks.push(self.redo.as_slice());
            all_stacks.extend_from_slice(other_stacks);

            let mut changed = false;
            let ctx = RedoContext {
                store_ref,
                redo_ids: &redo_ids,
                insertions: &item.insertions,
                stacks: &all_stacks,
            };
            for item_ref in &to_redo {
                changed |= redo_item(store, &ctx, item_ref).is_some();
            }
            // children before their parents
            for item_ref in to_delete.iter().rev() {
                if let Some(target) = item_ref.get() {
                    store.delete_item(target, None);
                    changed = true;
                }
            }

            if changed {
                performed = Some((item.id, item.meta));
            } else {
                release_meta(item.meta.into_iter().collect());
            }
        }

        // Neither recreated items nor deletions moved the search markers.
        for ty in store.collector.changed.keys() {
            // SAFETY: store write lock held, no type borrowed.
            if let Some(mut ty) = unsafe { ty.ty_mut() }
                && let Some(markers) = &mut ty.markers
            {
                markers.clear();
            }
        }

        performed
    }
}

/// Origins are tracked by identity: an origin matches itself and its clones.
fn same_origin(a: &Option<Origin>, b: &Option<Origin>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => a.same(b),
        _ => false,
    }
}

/// A type scope belongs to the manager's document.
fn check_store(scope: &Scope, store: &StoreRef) -> JwstCodecResult {
    match scope {
        Scope::Type(ty) if !Arc::ptr_eq(&ty.store_ref()?, store) => Err(JwstCodecError::ForeignType),
        _ => Ok(()),
    }
}

/// `id` is in `set`.
fn contains(set: &DeleteSet, id: Id) -> bool {
    set.get(&id.client).is_some_and(|ranges| ranges.contains(id.clock))
}

/// The type item `item` belongs to, `None` below a root type.
fn carrier_of(item: &Item) -> Option<Id> {
    match &item.parent {
        Some(Parent::Type(ty)) => ty.ty().and_then(|ty| ty.item.get()).map(|carrier| carrier.id),
        _ => None,
    }
}

/// Yjs `isParentOf`: `item` is somewhere below `ty`.
fn is_parent_of(ty: &YTypeRef, item: &Item) -> bool {
    let mut parent = item.parent.as_ref();
    while let Some(Parent::Type(current)) = parent {
        if current == ty {
            return true;
        }
        let Some(carrier) = current.ty().and_then(|current| current.item.get()) else {
            return false;
        };
        parent = carrier.parent.as_ref();
    }
    false
}

/// Calls `f` on the items overlapping `set`, without splitting anything.
fn for_each_item(store: &DocStore, set: &DeleteSet, mut f: impl FnMut(&Item)) {
    for (client, ranges) in set.iter() {
        let Some(nodes) = store.items.get(client) else {
            continue;
        };
        for range in ranges {
            let Some(mut idx) = DocStore::get_node_index(nodes, range.start) else {
                continue;
            };
            while let Some(node) = nodes.get(idx) {
                if node.clock() >= range.end {
                    break;
                }
                if let Node::Item(item) = node
                    && let Some(item) = item.get()
                {
                    f(item);
                }
                idx += 1;
            }
        }
    }
}

/// Yjs `iterateDeletedStructs`: the structs of `set`, split at its range
/// boundaries, clients in ascending order. Ranges past the end of a client's
/// structs are skipped.
fn clean_structs(store: &mut DocStore, set: &DeleteSet) -> Vec<Node> {
    let mut clients = set.keys().copied().collect::<Vec<_>>();
    clients.sort_unstable();

    let mut structs = Vec::new();
    for client in clients {
        let state = store.get_state(client);
        for range in set[&client].canonical_ranges() {
            if range.start >= state {
                break;
            }
            let end = range.end.min(state);
            if store.split_at_and_get_right(Id::new(client, range.start)).is_err() {
                continue;
            }
            if end < state {
                let _ = store.split_at_and_get_right(Id::new(client, end));
            }
            let nodes = &store.items[&client];
            let mut idx = DocStore::get_node_index(nodes, range.start).expect("split above");
            while let Some(node) = nodes.get(idx) {
                if node.clock() >= end {
                    break;
                }
                structs.push(node.clone());
                idx += 1;
            }
        }
    }
    structs
}

/// Yjs `getItemCleanStart`: the item starting at `id`. `None` for a GC
/// struct.
fn clean_start(store: &mut DocStore, id: Id) -> Option<ItemRef> {
    match store.split_at_and_get_right(id).ok()? {
        Node::Item(item) => Some(item),
        _ => None,
    }
}

/// Yjs `getItemCleanEnd`: the item ending at `id`. `None` for a GC struct.
fn clean_end(store: &mut DocStore, id: Id) -> Option<ItemRef> {
    match store.split_at_and_get_left(id).ok()? {
        Node::Item(item) => Some(item),
        _ => None,
    }
}

/// The items covering exactly `id..id+len`, split at both ends. Collected
/// structs in the range are left out.
fn clean_items(store: &mut DocStore, id: Id, len: u64) -> Vec<ItemRef> {
    let end = id.clock + len;
    if store.split_at_and_get_right(id).is_err() {
        return Vec::new();
    }
    if end < store.get_state(id.client) {
        let _ = store.split_at_and_get_right(Id::new(id.client, end));
    }
    let nodes = &store.items[&id.client];
    let mut idx = DocStore::get_node_index(nodes, id.clock).expect("split above");
    let mut items = Vec::new();
    while let Some(node) = nodes.get(idx) {
        if node.clock() >= end {
            break;
        }
        if let Node::Item(item) = node {
            items.push(item.clone());
        }
        idx += 1;
    }
    items
}

struct RedoContext<'a> {
    store_ref: &'a StoreRef,
    /// The items this pop recreates.
    redo_ids: &'a HashSet<Id>,
    /// The insertions of the popped item, which this pop deletes.
    insertions: &'a DeleteSet,
    stacks: &'a [&'a [StackItem]],
}

impl RedoContext<'_> {
    /// Yjs `isDeletedByUndoStack` for both stacks.
    fn deleted_by_stacks(&self, id: Id) -> bool {
        self.stacks
            .iter()
            .any(|stack| stack.iter().any(|item| contains(&item.deletions, id)))
    }
}

/// Yjs `redoItem` with `ignoreRemoteMapChanges = false`: recreates the
/// deleted `item_ref` under a new id, or returns its existing recreation.
/// `None` when it cannot be recreated: its parent type is deleted and not
/// recreated with it, a remote change took its map key, or its content was
/// already collected.
fn redo_item(store: &mut DocStore, ctx: &RedoContext<'_>, item_ref: &ItemRef) -> Option<ItemRef> {
    let (id, len, item_parent, parent_sub, item_left, has_right) = {
        let item = item_ref.get()?;
        (
            item.id,
            item.len(),
            item.parent.clone(),
            item.parent_sub.clone(),
            item.left.clone(),
            item.right.is_some(),
        )
    };
    if let Some(redone) = store.redone.get(id) {
        return clean_start(store, redone);
    }
    // Yjs relies on keep; a retention gap must not insert a hole as content
    if matches!(item_ref.get()?.content, Content::Deleted(_)) {
        return None;
    }
    let Some(Parent::Type(item_parent)) = item_parent else {
        return None;
    };

    // make sure the parent is recreated
    let mut parent_item = item_parent.ty()?.item.clone();
    if let Some((parent_id, parent_deleted)) = parent_item.get().map(|parent| (parent.id, parent.deleted()))
        && parent_deleted
    {
        // recreate the parent if this pop recreates it anyway
        if store.redone.get(parent_id).is_none()
            && (!ctx.redo_ids.contains(&parent_id) || redo_item(store, ctx, &parent_item).is_none())
        {
            return None;
        }
        while let Some(redone) = parent_item.get().and_then(|parent| store.redone.get(parent.id)) {
            parent_item = clean_start(store, redone)?;
        }
    }
    let parent_item_id = parent_item.get().map(|parent| parent.id);
    let parent_type = match parent_item.get() {
        Some(parent) => match &parent.content {
            Content::Type(ty) => ty.clone(),
            _ => return None,
        },
        None => item_parent,
    };

    let (left, right) = if let Some(key) = &parent_sub {
        (
            recreated_map_left(store, ctx, item_ref, &parent_type, parent_item_id, key, has_right)?,
            Somr::none(),
        )
    } else {
        // a list item: insert at the old position, next to the neighbors (or
        // their recreations) in the recreated parent. A left neighbor is
        // traced by its last unit: deleted neighbors may have been merged
        // since they were recreated, and only the unit next to the item
        // tells where it goes.
        let mut left = item_left;
        while left.is_some() {
            let mut trace = left.clone();
            while let Some((trace_id, trace_parent)) = trace.get().map(|trace| (trace.last_id(), carrier_of(trace)))
                && trace_parent != parent_item_id
            {
                trace = match store.redone.get(trace_id) {
                    Some(redone) => clean_end(store, redone).unwrap_or_default(),
                    None => Somr::none(),
                };
            }
            if trace.get().is_some_and(|trace| carrier_of(trace) == parent_item_id) {
                left = trace;
                break;
            }
            left = left.get().map(|left| left.left.clone()).unwrap_or_default();
        }

        let mut right = item_ref.clone();
        while right.is_some() {
            let mut trace = right.clone();
            while let Some((trace_id, trace_parent)) = trace.get().map(|trace| (trace.id, carrier_of(trace)))
                && trace_parent != parent_item_id
            {
                trace = match store.redone.get(trace_id) {
                    Some(redone) => clean_start(store, redone).unwrap_or_default(),
                    None => Somr::none(),
                };
            }
            if trace.get().is_some_and(|trace| carrier_of(trace) == parent_item_id) {
                right = trace;
                break;
            }
            right = right.get().map(|right| right.right.clone()).unwrap_or_default();
        }
        (left, right)
    };

    let content = copy_content(store, ctx.store_ref, &item_ref.get()?.content);
    let new_id = Id::new(store.client(), store.get_state(store.client()));
    let owned = store.create_item(content, left, right, Some(Parent::Type(parent_type)), parent_sub);
    let redone = owned.clone();
    store.register_redone(id, len, new_id);
    store
        .integrate(Node::Item(owned), 0, None)
        .expect("a recreated item integrates locally");
    Some(redone)
}

/// The left neighbor of a recreated map value (`redoItem` for an item with
/// `parentSub`). `None` when a newer remote value of the key must not be
/// overwritten.
fn recreated_map_left(
    store: &mut DocStore,
    ctx: &RedoContext<'_>,
    item_ref: &ItemRef,
    parent_type: &YTypeRef,
    parent_item_id: Option<Id>,
    key: &SmolStr,
    has_right: bool,
) -> Option<ItemRef> {
    let mut left = if has_right {
        // Walk right while the newer values are being deleted by this pop
        // or by a stack: then this value replaces them.
        let mut left = item_ref.clone();
        while let Some(right_id) = left.get().and_then(|left| left.right.get()).map(|right| right.id)
            && (store.redone.get(right_id).is_some()
                || contains(ctx.insertions, right_id)
                || ctx.deleted_by_stacks(right_id))
        {
            left = left.get().map(|left| left.right.clone()).unwrap_or_default();
            while let Some(redone) = left.get().and_then(|left| store.redone.get(left.id)) {
                left = clean_start(store, redone)?;
            }
        }
        if left.get().is_some_and(|left| left.right.is_some()) {
            // a newer remote value: recreating this one would overwrite it
            return None;
        }
        left
    } else {
        parent_type.ty()?.map.get(key).cloned().unwrap_or_default()
    };
    // a left in another parent would mislead the origin on remote peers
    // (#757)
    if left.get().is_some_and(|left| carrier_of(left) != parent_item_id) {
        left = parent_type.ty()?.map.get(key).cloned().unwrap_or_default();
    }
    Some(left)
}

/// Yjs `AbstractContent.copy`: a type is recreated as a new empty type of the
/// same kind (its children are recreated into it); other content is copied.
fn copy_content(store: &mut DocStore, store_ref: &StoreRef, content: &Content) -> Content {
    match content {
        Content::Type(ty) => {
            let ty = ty.ty().expect("the item holds its type");
            let kind = ty.kind();
            let mut copy = YType::new(kind, ty.name.clone());
            if kind.uses_markers() {
                copy.markers = Some(MarkerList::new());
            }
            let owner = YTypeRef {
                store: Arc::downgrade(store_ref),
                inner: Somr::new(copy),
            };
            let copy = owner.clone();
            // the store owns types created in it
            store.dangling_types.insert(owner.inner.ptr().as_ptr() as usize, owner);
            Content::Type(copy)
        }
        content => content.clone(),
    }
}

#[cfg(all(test, not(loom)))]
mod tests;
