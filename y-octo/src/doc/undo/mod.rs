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
            if let Err(error) = state.add_to_scope(&store.type_arena, scope) {
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
        self.write_maintenance(|state, store| state.add_to_scope(&store.type_arena, scope))?
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
            let store = tx.store_mut();
            let mut hook = store.history_hook.take();
            let state = hook
                .as_deref_mut()
                .and_then(|hook| hook.as_any_mut().downcast_mut::<UndoState>())
                .expect("the manager owns the history hook");
            let result = state.pop(store, stack);
            store.history_hook = hook;
            result
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
        types: &TypeArena,
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
                state.add_to_scope(types, UndoScope(Scope::Type(ty)))?;
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
        if !self.scope_changed(&store.type_arena, summary) || popped.is_none() && !self.tracks(summary) {
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
        for_each_item(store, &summary.deleted, |item, _| {
            if self.in_scope(&store.type_arena, item) {
                DocStore::retain_with_ancestors(&store.type_arena, &mut retained, item);
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

    /// `types` is the arena of the manager's document.
    fn add_to_scope(&mut self, types: &TypeArena, scope: UndoScope) -> JwstCodecResult {
        if let Scope::Type(ty) = &scope.0 {
            // a scope is a mounted type: commits report changes by identity
            if ty.id.and_then(|id| types.get(id)).is_none_or(|ty| ty.is_preliminary()) {
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
    fn scope_changed(&self, types: &TypeArena, summary: &CommitSummary) -> bool {
        self.scope.iter().any(|scope| match scope {
            Scope::Doc => true,
            Scope::Type(ty) => ty
                .id
                .and_then(|id| types.get(id))
                .and_then(|ty| ty.identity(&types.items).ok())
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
    fn in_scope(&self, types: &TypeArena, item: &Item) -> bool {
        self.scope.iter().any(|scope| match scope {
            Scope::Doc => true,
            Scope::Type(ty) => ty.id.is_some_and(|ty| is_parent_of(types, ty, item)),
        })
    }

    /// Retains exactly what the remaining stack items need and collects the
    /// rest.
    fn release(&self, store: &mut DocStore) {
        store.set_retained(self.retained_set());
    }

    /// Yjs `popStackItem`, in the transaction of an undo or redo.
    /// Returns the id and metadata of the item that changed the document.
    fn pop(&mut self, store: &mut DocStore, stack: UndoStack) -> JwstCodecResult<Option<(u64, Option<Meta>)>> {
        let performed = self.pop_with_extra_stacks(store, stack, &[]);
        if performed.is_ok() {
            self.release(store);
        }
        performed
    }

    /// Pops one stack item while consulting `other_stacks` in addition to this
    /// stack's own undo/redo stacks. Does **not** call `store.set_retained`;
    /// the caller is responsible for recomputing the combined retained set.
    pub(crate) fn pop_with_extra_stacks(
        &mut self,
        store: &mut DocStore,
        stack: UndoStack,
        other_stacks: &[&[StackItem]],
    ) -> JwstCodecResult<Option<(u64, Option<Meta>)>> {
        let mut performed = None;
        let mut skipped = Vec::new();
        while performed.is_none() {
            // Recreating a deleted type item takes a new type. Ask for all of
            // them before the item leaves its stack and the document changes:
            // a full arena fails the pop with both as they were.
            let Some(next) = (match stack {
                UndoStack::Undo => self.undo.last(),
                UndoStack::Redo => self.redo.last(),
            }) else {
                break;
            };
            let insertions = insertion_targets(store, &next.insertions);
            if let Err(err) = check_pop_capacity(store, next, &insertions) {
                let history = match stack {
                    UndoStack::Undo => &mut self.undo,
                    UndoStack::Redo => &mut self.redo,
                };
                history.extend(skipped.into_iter().rev());
                return Err(err);
            }

            let popped = match stack {
                UndoStack::Undo => self.undo.pop(),
                UndoStack::Redo => self.redo.pop(),
            };
            let Some(item) = popped else {
                break;
            };

            let apply = || -> JwstCodecResult<bool> {
                let mut to_delete = Vec::new();
                for (id, len) in insertions {
                    for target in clean_items(store, id, len)? {
                        if store
                            .type_arena
                            .items
                            .get(target)
                            .is_some_and(|item| !item.deleted() && self.in_scope(&store.type_arena, item))
                        {
                            to_delete.push(target);
                        }
                    }
                }

                let mut to_redo = Vec::new();
                let mut redo_ids = HashSet::new();
                for node in clean_structs(store, &item.deletions)? {
                    let Some(idx) = node.as_item() else {
                        continue;
                    };
                    let struct_item = store.type_arena.items.get(idx).expect("live structs");
                    // never recreate what the same capture window inserted
                    if self.in_scope(&store.type_arena, struct_item) && !contains(&item.insertions, struct_item.id) {
                        redo_ids.insert(struct_item.id);
                        to_redo.push(idx);
                    }
                }

                let mut all_stacks: Vec<&[StackItem]> = Vec::with_capacity(2 + other_stacks.len());
                all_stacks.push(self.undo.as_slice());
                all_stacks.push(self.redo.as_slice());
                all_stacks.extend_from_slice(other_stacks);

                let mut changed = false;
                let ctx = RedoContext {
                    redo_ids: &redo_ids,
                    insertions: &item.insertions,
                    stacks: &all_stacks,
                };
                for item_ref in &to_redo {
                    changed |= redo_item(store, &ctx, *item_ref)?.is_some();
                }
                // children before their parents
                for item_ref in to_delete.iter().rev() {
                    store.delete_item(*item_ref, None);
                    changed = true;
                }
                Ok(changed)
            };
            let changed = match apply() {
                Ok(changed) => changed,
                Err(err) => {
                    let history = match stack {
                        UndoStack::Undo => &mut self.undo,
                        UndoStack::Redo => &mut self.redo,
                    };
                    history.push(item);
                    history.extend(skipped.into_iter().rev());
                    return Err(err);
                }
            };

            if changed {
                performed = Some((item.id, item.meta));
            } else {
                skipped.push(item);
            }
        }

        // Neither recreated items nor deletions moved the search markers.
        for ty in store.collector.changed.keys() {
            if let Some(ty) = store.type_arena.get_mut(*ty)
                && let Some(markers) = &mut ty.markers
            {
                markers.clear();
            }
        }

        release_meta(skipped.into_iter().filter_map(|item| item.meta).collect());
        Ok(performed)
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
fn carrier_of(types: &TypeArena, item: &Item) -> Option<Id> {
    match &item.parent {
        Some(ty) => types
            .get(*ty)
            .and_then(|ty| ty.live_carrier(&types.items))
            .map(|carrier| carrier.id),
        _ => None,
    }
}

/// Yjs `isParentOf`: `item` is somewhere below `ty`.
fn is_parent_of(types: &TypeArena, ty: TypeIdx, item: &Item) -> bool {
    let mut parent = item.parent.as_ref();
    while let Some(current) = parent {
        if *current == ty {
            return true;
        }
        let Some(carrier) = types
            .get(*current)
            .and_then(|current| current.live_carrier(&types.items))
        else {
            return false;
        };
        parent = carrier.parent.as_ref();
    }
    false
}

/// Calls `f` on the items overlapping `set`, without splitting anything.
fn for_each_item(store: &DocStore, set: &DeleteSet, mut f: impl FnMut(&Item, u64)) {
    for (client, ranges) in set.iter() {
        let Some(nodes) = store.items.get(client) else {
            continue;
        };
        for range in ranges {
            let Some(mut idx) = DocStore::get_node_index(nodes, range.start) else {
                continue;
            };
            while let Some(node) = nodes.node(*client, idx) {
                if node.clock() >= range.end {
                    break;
                }
                if let Some(item) = node.as_item().and_then(|i| store.type_arena.items.get(i)) {
                    f(
                        item,
                        range.end.min(node.clock() + node.len()) - range.start.max(node.clock()),
                    );
                }
                idx += 1;
            }
        }
    }
}

/// Resolve insertion ranges before splitting. Even collected sources may have
/// surviving targets, and different pieces can have different redo chains.
fn insertion_targets(store: &DocStore, set: &DeleteSet) -> Vec<(Id, u64)> {
    let mut clients: Vec<_> = set.keys().copied().collect();
    clients.sort_unstable();
    let mut targets = Vec::new();
    for client in clients {
        let state = store.get_state(client);
        for range in set[&client].canonical_ranges() {
            let end = state.min(range.end);
            if range.start < end {
                targets.extend(
                    store
                        .redone
                        .follow_range(Id::new(client, range.start), end - range.start),
                );
            }
        }
    }
    targets
}

fn check_pop_capacity(store: &DocStore, item: &StackItem, insertions: &[(Id, u64)]) -> JwstCodecResult {
    let mut types = 0;
    let mut copies = 0usize;
    let mut next_clock = Some(store.get_state(store.client()));
    for_each_item(store, &item.deletions, |item, len| {
        next_clock = next_clock.and_then(|clock| clock.checked_add(len));
        types += usize::from(matches!(item.content, Content::Type(_)));
        copies += 1;
    });
    next_clock.ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
    store.type_arena.check_capacity(types)?;

    // Count distinct interior cuts. An insertion boundary inside a deletion
    // can leave another fragment to recreate as well as the original.
    let mut cuts = HashSet::new();
    let mut boundary = |id: Id| {
        if store.get_node(id).is_some_and(|node| node.is_item() && node.id != id) {
            cuts.insert(id);
        }
    };
    for &(id, len) in insertions {
        boundary(id);
        boundary(id + len);
    }
    for (client, ranges) in item.deletions.iter() {
        for range in ranges {
            boundary(Id::new(*client, range.start));
            boundary(Id::new(*client, range.end));
        }
    }
    let extra_copies = cuts
        .iter()
        .filter(|id| {
            contains(&item.deletions, **id)
                && id.clock > 0
                && contains(&item.deletions, Id::new(id.client, id.clock - 1))
        })
        .count();
    let mut needed = copies.saturating_add(extra_copies).saturating_add(cuts.len());
    if copies > 0 && !store.redone.is_empty() {
        // Redo also cleans the neighbors and carriers reached through old
        // mappings. Each cut of an old target may propagate into its new copy.
        // Most documents have ample space even if every clock splits.
        // Only inspect individual mappings near the item limit.
        let clocks = store.items.values().fold(0usize, |sum, blocks| {
            sum.saturating_add(usize::try_from(blocks.end_clock).unwrap_or(usize::MAX))
        });
        if store
            .type_arena
            .items
            .check_capacity(needed.saturating_add(clocks.saturating_mul(2)))
            .is_ok()
        {
            return Ok(());
        }
        needed = needed.saturating_add(store.redone.target_split_bound(store).saturating_mul(2));
    }
    store.type_arena.items.check_capacity(needed)
}

fn clean_structs(store: &mut DocStore, set: &DeleteSet) -> JwstCodecResult<Vec<Node>> {
    let mut clients = set.keys().copied().collect::<Vec<_>>();
    clients.sort_unstable();
    let mut structs = Vec::new();
    for client in clients {
        let state = store.get_state(client);
        for range in set[&client].canonical_ranges() {
            if range.start >= state {
                break;
            }
            structs.extend(clean_range(store, Id::new(client, range.start), range.end.min(state))?);
        }
    }
    Ok(structs)
}

fn clean_start(store: &mut DocStore, id: Id) -> JwstCodecResult<ItemRef> {
    Ok(store.split_at_and_get_right(id)?.as_item())
}

fn clean_end(store: &mut DocStore, id: Id) -> JwstCodecResult<ItemRef> {
    Ok(store.split_at_and_get_left(id)?.as_item())
}

fn clean_range(store: &mut DocStore, id: Id, end: u64) -> JwstCodecResult<impl Iterator<Item = Node> + '_> {
    clean_start(store, id)?;
    if end < store.get_state(id.client) {
        clean_start(store, Id::new(id.client, end))?;
    }
    let blocks = &store.items[&id.client];
    let first = blocks.find(id.clock).expect("cleaned range");
    Ok((first..blocks.len())
        .map(move |i| blocks.node(id.client, i).expect("block index"))
        .take_while(move |node| node.clock() < end))
}

fn clean_items(store: &mut DocStore, id: Id, len: u64) -> JwstCodecResult<Vec<ItemIdx>> {
    Ok(clean_range(store, id, id.clock + len)?
        .filter_map(|node| node.as_item())
        .collect())
}

struct RedoContext<'a> {
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
fn redo_item(store: &mut DocStore, ctx: &RedoContext<'_>, idx: ItemIdx) -> JwstCodecResult<Option<ItemRef>> {
    let (id, len, item_parent, parent_sub, item_left, has_right) = {
        let item = store.type_arena.items.get(idx).expect("retained item");
        (
            item.id,
            item.len(),
            item.parent,
            item.parent_sub.clone(),
            item.left,
            item.right.is_some(),
        )
    };
    if let Some(redone) = store.redone.get(id) {
        return Ok(clean_start(store, redone)?.map(Some));
    }
    // Yjs relies on keep; a retention gap must not insert a hole as content
    if matches!(
        store.type_arena.items.get(idx).expect("retained item").content,
        Content::Deleted(_)
    ) {
        return Ok(None);
    }
    let Some(item_parent) = item_parent else {
        return Ok(None);
    };

    // make sure the parent is recreated
    let mut parent_item = store.type_arena[item_parent].carrier_ref();
    if let Some((parent_id, parent_deleted)) = parent_item
        .and_then(|i| store.type_arena.items.get(i))
        .map(|parent| (parent.id, parent.deleted()))
        && parent_deleted
    {
        // recreate the parent if this pop recreates it anyway
        if store.redone.get(parent_id).is_none()
            && (!ctx.redo_ids.contains(&parent_id)
                || redo_item(store, ctx, parent_item.expect("deleted carrier"))?.is_none())
        {
            return Ok(None);
        }
        while let Some(redone) = parent_item
            .and_then(|i| store.type_arena.items.get(i))
            .and_then(|parent| store.redone.get(parent.id))
        {
            let Some(carrier) = clean_start(store, redone)? else {
                return Ok(None);
            };
            parent_item = Some(carrier);
        }
    }
    let parent_item_id = parent_item
        .and_then(|i| store.type_arena.items.get(i))
        .map(|parent| parent.id);
    let parent_type = match parent_item.and_then(|i| store.type_arena.items.get(i)) {
        Some(parent) => match &parent.content {
            Content::Type(ty) => *ty,
            _ => return Ok(None),
        },
        None => item_parent,
    };

    let (left, right) = if let Some(key) = &parent_sub {
        let Some(left) = recreated_map_left(store, ctx, idx, parent_type, parent_item_id, key, has_right)? else {
            return Ok(None);
        };
        (left, None)
    } else {
        // a list item: insert at the old position, next to the neighbors (or
        // their recreations) in the recreated parent. A left neighbor is
        // traced by its last unit: deleted neighbors may have been merged
        // since they were recreated, and only the unit next to the item
        // tells where it goes.
        let mut left = item_left;
        while left.is_some() {
            let mut trace = left;
            while let Some((trace_id, trace_parent)) = trace
                .and_then(|i| store.type_arena.items.get(i))
                .map(|trace| (trace.last_id(), carrier_of(&store.type_arena, trace)))
                && trace_parent != parent_item_id
            {
                trace = match store.redone.get(trace_id) {
                    Some(redone) => clean_end(store, redone)?,
                    None => None,
                };
            }
            if trace
                .and_then(|i| store.type_arena.items.get(i))
                .is_some_and(|trace| carrier_of(&store.type_arena, trace) == parent_item_id)
            {
                left = trace;
                break;
            }
            left = left
                .and_then(|i| store.type_arena.items.get(i))
                .map(|left| left.left)
                .unwrap_or_default();
        }

        let mut right = Some(idx);
        while right.is_some() {
            let mut trace = right;
            while let Some((trace_id, trace_parent)) = trace
                .and_then(|i| store.type_arena.items.get(i))
                .map(|trace| (trace.id, carrier_of(&store.type_arena, trace)))
                && trace_parent != parent_item_id
            {
                trace = match store.redone.get(trace_id) {
                    Some(redone) => clean_start(store, redone)?,
                    None => None,
                };
            }
            if trace
                .and_then(|i| store.type_arena.items.get(i))
                .is_some_and(|trace| carrier_of(&store.type_arena, trace) == parent_item_id)
            {
                right = trace;
                break;
            }
            right = right
                .and_then(|i| store.type_arena.items.get(i))
                .map(|right| right.right)
                .unwrap_or_default();
        }
        (left, right)
    };

    let content = copy_content(store, idx)?;
    let new_id = Id::new(store.client(), store.get_state(store.client()));
    let owned = store.create_item(content, left, right, Some(parent_type), parent_sub);
    let Some(redone) = store.integrate_item(owned, 0, None)? else {
        return Ok(None);
    };
    store.register_redone(id, len, new_id);
    Ok(Some(Some(redone)))
}

/// The left neighbor of a recreated map value (`redoItem` for an item with
/// `parentSub`). `None` when a newer remote value of the key must not be
/// overwritten.
fn recreated_map_left(
    store: &mut DocStore,
    ctx: &RedoContext<'_>,
    idx: ItemIdx,
    parent_type: TypeIdx,
    parent_item_id: Option<Id>,
    key: &SmolStr,
    has_right: bool,
) -> JwstCodecResult<Option<ItemRef>> {
    let mut left = if has_right {
        // Walk right while the newer values are being deleted by this pop
        // or by a stack: then this value replaces them.
        let mut left = Some(idx);
        while let Some(right_id) = left
            .and_then(|i| store.type_arena.items.get(i))
            .and_then(|left| left.right.and_then(|i| store.type_arena.items.get(i)))
            .map(|right| right.id)
            && (store.redone.get(right_id).is_some()
                || contains(ctx.insertions, right_id)
                || ctx.deleted_by_stacks(right_id))
        {
            left = left
                .and_then(|i| store.type_arena.items.get(i))
                .map(|left| left.right)
                .unwrap_or_default();
            while let Some(redone) = left
                .and_then(|i| store.type_arena.items.get(i))
                .and_then(|left| store.redone.get(left.id))
            {
                let Some(target) = clean_start(store, redone)? else {
                    return Ok(None);
                };
                left = Some(target);
            }
        }
        if left
            .and_then(|i| store.type_arena.items.get(i))
            .is_some_and(|left| left.right.is_some())
        {
            // a newer remote value: recreating this one would overwrite it
            return Ok(None);
        }
        left
    } else {
        store.type_arena[parent_type].map_get(key).cloned().unwrap_or_default()
    };
    // a left in another parent would mislead the origin on remote peers
    // (#757)
    if left
        .and_then(|i| store.type_arena.items.get(i))
        .is_some_and(|left| carrier_of(&store.type_arena, left) != parent_item_id)
    {
        left = store.type_arena[parent_type].map_get(key).cloned().unwrap_or_default();
    }
    Ok(Some(left))
}

/// Yjs `AbstractContent.copy`: a type is recreated as a new empty type of the
/// same kind (its children are recreated into it); other content is copied.
fn copy_content(store: &mut DocStore, idx: ItemIdx) -> JwstCodecResult<Content> {
    Ok(match &store.type_arena.items.get(idx).expect("retained item").content {
        Content::Type(ty) => {
            let ty = &store.type_arena[*ty];
            let kind = ty.kind();
            let mut copy = YType::new(kind, ty.name().map(str::to_owned));
            if kind.uses_markers() {
                copy.markers = Some(Box::default());
            }
            // the store owns types created in it
            Content::Type(store.type_arena.alloc(copy)?)
        }
        content => content.clone(),
    })
}

#[cfg(all(test, not(loom)))]
mod tests;
