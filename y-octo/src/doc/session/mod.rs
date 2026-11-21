//! Single-owner synchronous document session core (`DocSession`).
//!
//! Designed for JS/Wasm (`@blocksuite/store` / ORM), GPUI and C-Wasm hosts
//! that need:
//! - Nested deferred-commit transaction frames (`begin_tx` / `commit_tx`) with
//!   synchronous read-your-writes and **zero** locks held across FFI callbacks,
//! - Atomic declarative nested writes ([`SessionValue`]),
//! - Path or [`TypeIdentity`]-addressed reads/writes and structured commit
//!   summaries ([`SessionCommit`]),
//! - Optional or multi-scope [`UndoStackId`] history stacks with shared GC
//!   retention and selection metadata,

mod history;
mod ops;
#[cfg(all(test, not(loom)))]
mod tests;

use std::sync::{
    Arc as StdArc,
    atomic::{AtomicU64, Ordering},
};

use history::SessionHistoryHub;
use ops::{
    InsertSlot, check_array_read_kind, check_map_read_kind, check_text_read_kind, check_xml_element_kind,
    check_xml_name_kind, check_xml_string_kind, compute_type_path, insert_session_value, is_type_alive,
    parse_json_content_elem, read_value_from_content, resolve_identity_raw, resolve_path_in_store, resolve_target,
    solidify_array_kind, solidify_map_kind, solidify_text_kind, solidify_xml_element_kind, validate_session_value,
};
use smol_str::SmolStr;

use super::{
    store::StoreRef,
    transaction::commit_store,
    types::{
        ListIterator, YTypeBuilder, item_at, list_insert, list_remove, map, text,
        xml::{xml_hook_name, xml_tag_name, xml_text_to_string, xml_to_string},
    },
    undo::{Meta, downcast},
    *,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct SessionTrackedOrigin;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct SessionUntrackedOrigin;

#[derive(Clone, PartialEq, Eq, Hash)]
struct SessionNamedOrigin(SmolStr);

/// Identifier of an undo stack managed by a [`DocSession`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UndoStackId(pub u32);

/// Undo history mode for a [`DocSession`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionUndoConfig {
    /// Disable undo tracking completely: no `history_hook` is installed on the
    /// underlying store, avoiding all history and GC retention overhead.
    Disabled,
    /// Install a single document-wide undo stack (`UndoStackId(0)`) tracking
    /// [`SessionTxOrigin::Tracked`] edits with the given capture timeout.
    Global { capture_timeout_ms: u64 },
    /// Start with zero undo stacks; callers register scoped or custom-origin
    /// stacks on demand via [`DocSession::create_undo_stack`].
    Custom,
}

/// Configuration for constructing a [`DocSession`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SessionConfig {
    pub undo: SessionUndoConfig,
}

impl Default for SessionConfig {
    fn default() -> Self {
        Self {
            undo: SessionUndoConfig::Global {
                capture_timeout_ms: 500,
            },
        }
    }
}

/// Origin category for a [`DocSession::begin_tx`] call or undo stack filter.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SessionTxOrigin {
    /// Local user edit tracked by the default undo stack.
    Tracked,
    /// Local write outside default undo history (e.g. raw proxy / migration).
    Untracked,
    /// Named local origin with stable identity within the session.
    Named(SmolStr),
}

/// Origin category reported on every [`SessionCommit`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SessionOriginKind {
    /// Local tracked transaction (`begin_tx(Tracked)` or standalone write).
    LocalTransact,
    /// Local untracked write (`begin_tx(Untracked)`).
    LocalUntracked,
    /// Local write with a custom [`SessionTxOrigin::Named`] origin.
    LocalNamed(String),
    /// Remote update applied via [`DocSession::apply_update_v1`].
    RemoteSync,
    /// Local formatting cleanup triggered immediately after integrating a
    /// remote rich-text update (must be broadcast as local).
    FormattingCleanup,
    /// Undo step on `stack_id`.
    Undo { stack_id: u32 },
    /// Redo step on `stack_id`.
    Redo { stack_id: u32 },
}

impl SessionOriginKind {
    pub fn is_undo(&self) -> bool {
        matches!(self, Self::Undo { .. })
    }

    pub fn is_redo(&self) -> bool {
        matches!(self, Self::Redo { .. })
    }
}

/// One step in a [`TypePath`] from a root type down to a nested CRDT type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PathSegment {
    Key(String),
    Index(u64),
}

/// Path from a named root type to a nested collaborative type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypePath {
    pub root: String,
    pub segments: Vec<PathSegment>,
}

impl TypePath {
    pub fn root(name: impl Into<String>) -> Self {
        Self {
            root: name.into(),
            segments: Vec::new(),
        }
    }

    pub fn key(mut self, key: impl Into<String>) -> Self {
        self.segments.push(PathSegment::Key(key.into()));
        self
    }

    pub fn index(mut self, index: u64) -> Self {
        self.segments.push(PathSegment::Index(index));
        self
    }
}

/// Address of a collaborative type in a [`DocSession`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeTarget {
    Identity(TypeIdentity),
    Path(TypePath),
}

impl From<TypeIdentity> for TypeTarget {
    fn from(id: TypeIdentity) -> Self {
        Self::Identity(id)
    }
}

impl From<TypePath> for TypeTarget {
    fn from(path: TypePath) -> Self {
        Self::Path(path)
    }
}

/// Liveness and parent-chain path of a [`TypeIdentity`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeStatus {
    pub alive: bool,
    pub kind: Option<YTypeKind>,
    pub path: Option<TypePath>,
}

/// Declarative nested value written atomically into a `Map` key, `Array`
/// index, `XMLFragment` or `XMLElement` under a single store write lock
/// (parent mounted before children).
#[derive(Debug, Clone, PartialEq)]
pub enum SessionValue {
    Any(Any),
    Map(Vec<(String, SessionValue)>),
    Array(Vec<SessionValue>),
    Text(Vec<TextDeltaOp>),
    Doc {
        guid: String,
        gc: bool,
    },
    XmlElement {
        tag: String,
        attrs: Vec<(String, Any)>,
        children: Vec<SessionValue>,
    },
    XmlFragment(Vec<SessionValue>),
    XmlText(Vec<TextDeltaOp>),
    XmlHook {
        name: String,
        entries: Vec<(String, SessionValue)>,
    },
}

/// Synchronous read projection of a `Map` entry, `Array` element or XML child.
#[derive(Debug, Clone, PartialEq)]
pub enum SessionReadValue {
    Any(Any),
    Map(TypeIdentity),
    Array(TypeIdentity),
    Text(TypeIdentity),
    Doc { guid: String, gc: bool },
    XmlElement { tag: String, identity: TypeIdentity },
    XmlFragment(TypeIdentity),
    XmlText(TypeIdentity),
    XmlHook { name: String, identity: TypeIdentity },
}

/// A type changed by a committed transaction, with its live path if still
/// reachable from a root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionChangedType {
    pub identity: TypeIdentity,
    pub path: Option<TypePath>,
    pub keys: Vec<String>,
}

/// Structured result of every committed [`DocSession`] transaction, remote
/// update application, undo or redo.
///
/// `can_undo` and `can_redo` reflect stack `UndoStackId(0)` (the default global
/// stack, or `false` when stack 0 is absent or undo is disabled).
#[derive(Debug, Clone, PartialEq)]
pub struct SessionCommit<M = Vec<u8>> {
    pub revision: u64,
    pub update: Vec<u8>,
    pub is_local: bool,
    pub origin_kind: SessionOriginKind,
    pub changed: Vec<SessionChangedType>,
    pub subdocs_added: Vec<String>,
    pub subdocs_removed: Vec<String>,
    pub can_undo: bool,
    pub can_redo: bool,
    pub selection_meta: Option<M>,
}

/// Active deferred transaction frame owned directly by [`DocSession`].
#[derive(Debug)]
struct DeferredTx {
    depth: usize,
    before_state: StateVector,
    origin: Option<Origin>,
    local: bool,
    capture_history: bool,
}

impl Drop for DeferredTx {
    fn drop(&mut self) {
        if let Some(origin) = self.origin.take() {
            after_unlock(move || drop(origin));
        }
    }
}

struct RootHandle;

impl types::FromTypeRef for RootHandle {
    fn from_type_ref(_: YTypeRef) -> Self {
        Self
    }
}

/// Single-owner synchronous document session exclusively owning a [`Doc`].
pub struct DocSession<M: Clone + Send + Sync + 'static = Vec<u8>> {
    doc: Option<Doc>,
    active_tx: Option<DeferredTx>,
    now: StdArc<AtomicU64>,
    has_history_hub: bool,
    manager_to_stack: HashMap<u64, u32>,
    tracked_origin: Origin,
    untracked_origin: Origin,
    named_origins: HashMap<SmolStr, Origin>,
    _meta: std::marker::PhantomData<fn() -> M>,
}

impl<M: Clone + Send + Sync + 'static> DocSession<M> {
    /// Creates a new session with the given [`DocOptions`] and
    /// [`SessionConfig`].
    pub fn with_config(options: DocOptions, config: SessionConfig) -> Self {
        let doc = Doc::with_options(options);
        Self::from_fresh_doc(doc, config)
    }

    /// Creates a new session with a single document-wide undo stack
    /// (`UndoStackId(0)`) and the given capture timeout in milliseconds.
    pub fn new(options: DocOptions, capture_timeout_ms: u64) -> Self {
        Self::with_config(
            options,
            SessionConfig {
                undo: SessionUndoConfig::Global { capture_timeout_ms },
            },
        )
    }

    /// Creates a new session populated from a V1 binary update without exposing
    /// any external [`Doc`] or type handles.
    pub fn from_update_v1(update: &[u8], options: DocOptions, config: SessionConfig) -> JwstCodecResult<Self> {
        let mut doc = Doc::with_options(options);
        doc.apply_update_from_binary_v1(update)?;
        Ok(Self::from_fresh_doc(doc, config))
    }

    fn from_fresh_doc(doc: Doc, config: SessionConfig) -> Self {
        let now = StdArc::new(AtomicU64::new(0));
        let tracked_origin = Origin::new(SessionTrackedOrigin);
        let untracked_origin = Origin::new(SessionUntrackedOrigin);
        let mut session = Self {
            doc: Some(doc),
            active_tx: None,
            now,
            has_history_hub: false,
            manager_to_stack: HashMap::new(),
            tracked_origin,
            untracked_origin,
            named_origins: HashMap::new(),
            _meta: std::marker::PhantomData,
        };
        if let SessionUndoConfig::Global { capture_timeout_ms } = config.undo {
            session
                .create_undo_stack(&[], capture_timeout_ms, &[SessionTxOrigin::Tracked])
                .expect("fresh document accepts history hook");
        }
        session
    }

    fn doc_ref(&self) -> &Doc {
        self.doc.as_ref().expect("active DocSession holds a Doc")
    }

    fn doc_mut(&mut self) -> &mut Doc {
        self.doc.as_mut().expect("active DocSession holds a Doc")
    }

    /// Detaches any session history hook, releases retained GC ranges via a
    /// maintenance transaction, and returns the underlying [`Doc`] without
    /// copying. Fails with [`JwstCodecError::OpenTransactionFrame`] if
    /// `tx_depth() > 0`.
    pub fn into_doc(mut self) -> JwstCodecResult<Doc> {
        if self.active_tx.is_some() {
            return Err(JwstCodecError::OpenTransactionFrame);
        }
        if self.has_history_hub {
            let store_ref = self.doc_ref().store.clone();
            let hook = transact_maintenance(&store_ref, |tx| {
                let store = tx.store_mut();
                store.set_retained(DeleteSet::default());
                Ok(store.history_hook.take())
            })?;
            if let Some(hook) = hook {
                after_unlock(move || drop(hook));
            }
            self.has_history_hub = false;
            self.manager_to_stack.clear();
        }
        Ok(self.doc.take().expect("active DocSession holds a Doc"))
    }

    pub fn client(&self) -> Client {
        self.doc_ref().client()
    }

    pub fn client_required(&self) -> bool {
        self.doc_ref().client_required()
    }

    pub fn set_client(&mut self, client_id: u64) {
        self.doc_mut().set_client(client_id);
    }

    pub fn guid(&self) -> &str {
        self.doc_ref().guid()
    }

    /// Current nesting depth of open [`DocSession::begin_tx`] frames (`0` when
    /// idle).
    pub fn tx_depth(&self) -> usize {
        self.active_tx.as_ref().map_or(0, |tx| tx.depth)
    }

    fn resolve_tx_origin(&mut self, origin: &SessionTxOrigin) -> Origin {
        match origin {
            SessionTxOrigin::Tracked => self.tracked_origin.clone(),
            SessionTxOrigin::Untracked => self.untracked_origin.clone(),
            SessionTxOrigin::Named(name) => self
                .named_origins
                .entry(name.clone())
                .or_insert_with(|| Origin::new(SessionNamedOrigin(name.clone())))
                .clone(),
        }
    }

    /// Opens (or nests) a deferred-commit local transaction frame.
    ///
    /// No lock is held after this call returns. Nested calls increment the
    /// frame depth and keep the outermost `origin` (matching Yjs
    /// `doc.transact`).
    pub fn begin_tx(&mut self, origin: SessionTxOrigin) -> JwstCodecResult<usize> {
        if let Some(active) = self.active_tx.as_mut() {
            active.depth += 1;
            return Ok(active.depth);
        }
        let resolved_origin = self.resolve_tx_origin(&origin);
        let store = write_store(&self.doc_ref().store)?;
        if store.client_required {
            drop(store);
            after_unlock(move || drop(resolved_origin));
            return Err(JwstCodecError::ClientIdRequired);
        }
        debug_assert!(store.collector.is_empty());
        let before_state = store.get_state_vector();
        drop(store);
        self.active_tx = Some(DeferredTx {
            depth: 1,
            before_state,
            origin: Some(resolved_origin),
            local: true,
            capture_history: true,
        });
        Ok(1)
    }

    /// Closes one transaction frame. Only the outermost `commit_tx` (when
    /// depth reaches `0`) executes the full commit pipeline and returns
    /// `Some(SessionCommit)` if the document changed.
    pub fn commit_tx(&mut self) -> JwstCodecResult<Option<SessionCommit<M>>> {
        let Some(active) = self.active_tx.as_mut() else {
            return Err(JwstCodecError::Unexpected);
        };
        if active.depth > 1 {
            active.depth -= 1;
            return Ok(None);
        }
        let mut deferred = self.active_tx.take().expect("checked above");
        let store_ref = self.doc_ref().store.clone();
        let mut store = write_store(&store_ref)?;
        let mut incoming = None;
        let (primary, _) = commit_store(
            &mut store,
            &mut deferred.before_state,
            &mut deferred.local,
            &mut deferred.capture_history,
            &deferred.origin,
            &mut incoming,
            None,
            true,
        );
        let commit = primary.as_ref().map(|ev| self.build_commit_locked(&store, ev, None));
        drop(deferred);
        Ok(commit)
    }

    /// Ensures a root type with `name` and `kind` exists and returns its
    /// [`TypeIdentity`].
    pub fn ensure_root(&mut self, name: &str, kind: YTypeKind) -> JwstCodecResult<TypeIdentity> {
        let mut builder = YTypeBuilder::new(self.doc_ref().store.clone())
            .with_kind(kind)
            .set_name(name.to_string());
        if kind == YTypeKind::XMLElement {
            builder = builder.set_tag_name(types::xml::DEFAULT_XML_ELEMENT_TAG.to_string());
        }
        let _: RootHandle = builder.build()?;
        Ok(TypeIdentity::Root(name.to_string()))
    }

    /// Resolves a [`TypePath`] to its current [`TypeIdentity`], or `None` if
    /// any segment does not exist or is not a collaborative type.
    pub fn resolve_path(&self, path: &TypePath) -> Option<TypeIdentity> {
        let store = read_store(&self.doc_ref().store).ok()?;
        let ty_ref = resolve_path_in_store(&store, path).ok()?;
        let ty = ty_ref.ty()?;
        if !is_type_alive(&store, &ty_ref) {
            return None;
        }
        ty.identity().ok()
    }

    /// Queries whether `id` is currently alive (not deleted or collected), its
    /// [`YTypeKind`], and its current parent-chain [`TypePath`].
    pub fn type_status(&self, id: &TypeIdentity) -> TypeStatus {
        let Ok(store) = read_store(&self.doc_ref().store) else {
            return TypeStatus {
                alive: false,
                kind: None,
                path: None,
            };
        };
        let Ok(ty_ref) = resolve_identity_raw(&store, id) else {
            return TypeStatus {
                alive: false,
                kind: None,
                path: None,
            };
        };
        let Some(ty) = ty_ref.ty() else {
            return TypeStatus {
                alive: false,
                kind: None,
                path: None,
            };
        };
        let path = compute_type_path(&ty_ref);
        let alive = path.is_some();
        TypeStatus {
            alive,
            kind: Some(ty.kind()),
            path,
        }
    }

    // -----------------------------------------------------------------------
    // Synchronous reads (safe during active deferred transactions)

    pub fn get_map_value(&self, target: &TypeTarget, key: &str) -> JwstCodecResult<Option<SessionReadValue>> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_map_read_kind(ty)?;
        Ok(map::map_value(ty, key).map(|item| read_value_from_content(&item.content)))
    }

    pub fn read_map(&self, target: &TypeTarget) -> JwstCodecResult<Vec<(String, SessionReadValue)>> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_map_read_kind(ty)?;
        let mut entries: Vec<_> = map::map_entries(ty)
            .map(|(k, item)| (k.to_string(), read_value_from_content(&item.content)))
            .collect();
        entries.sort_by(|(a, _), (b, _)| a.cmp(b));
        Ok(entries)
    }

    pub fn read_array(&self, target: &TypeTarget) -> JwstCodecResult<Vec<SessionReadValue>> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_array_read_kind(ty)?;
        let mut out = Vec::new();
        for item in ListIterator::new(ty).filter(|item| item.countable()) {
            match &item.content {
                Content::Any(any) if !any.is_empty() => {
                    for elem in any {
                        out.push(SessionReadValue::Any(elem.clone()));
                    }
                }
                Content::Json(items) if !items.is_empty() => {
                    for elem in items {
                        out.push(SessionReadValue::Any(parse_json_content_elem(elem)));
                    }
                }
                content => out.push(read_value_from_content(content)),
            }
        }
        Ok(out)
    }

    pub fn read_array_at(&self, target: &TypeTarget, index: u64) -> JwstCodecResult<Option<SessionReadValue>> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_array_read_kind(ty)?;
        let Some((item_ref, offset)) = item_at(&ty_ref, ty, index) else {
            return Ok(None);
        };
        Ok(item_ref.get().and_then(|item| match &item.content {
            Content::Any(any) => any.get(offset as usize).cloned().map(SessionReadValue::Any),
            Content::Json(items) => items
                .get(offset as usize)
                .map(|elem| SessionReadValue::Any(parse_json_content_elem(elem))),
            content => Some(read_value_from_content(content)),
        }))
    }

    pub fn read_text_len(&self, target: &TypeTarget) -> JwstCodecResult<u64> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_text_read_kind(ty)?;
        Ok(ty.len)
    }

    pub fn read_text_string(&self, target: &TypeTarget) -> JwstCodecResult<String> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_text_read_kind(ty)?;
        Ok(text::text_string(ty))
    }

    pub fn read_text_delta(&self, target: &TypeTarget) -> JwstCodecResult<TextDelta> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_text_read_kind(ty)?;
        Ok(text::text_delta(ty))
    }

    /// Returns the tag name of an `XMLElement` or the hook name of an
    /// `XMLHook`.
    pub fn xml_name(&self, target: &TypeTarget) -> JwstCodecResult<String> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_xml_name_kind(ty)?;
        Ok(match ty.kind() {
            YTypeKind::XMLElement => xml_tag_name(ty).to_string(),
            YTypeKind::XMLHook => xml_hook_name(ty).to_string(),
            _ => unreachable!("checked above"),
        })
    }

    pub fn xml_get_attr(&self, target: &TypeTarget, key: &str) -> JwstCodecResult<Option<Any>> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_xml_element_kind(ty)?;
        Ok(
            map::map_value(ty, key).and_then(|item| match Value::from(&item.content) {
                Value::Any(any) => Some(any),
                _ => None,
            }),
        )
    }

    pub fn xml_attrs(&self, target: &TypeTarget) -> JwstCodecResult<Vec<(String, Any)>> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_xml_element_kind(ty)?;
        let mut attrs: Vec<(String, Any)> = map::map_entries(ty)
            .filter_map(|(k, item)| match Value::from(&item.content) {
                Value::Any(any) => Some((k.to_string(), any)),
                _ => None,
            })
            .collect();
        attrs.sort_by(|(a, _), (b, _)| a.cmp(b));
        Ok(attrs)
    }

    pub fn xml_to_string(&self, target: &TypeTarget) -> JwstCodecResult<String> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        check_xml_string_kind(ty)?;
        Ok(match ty.kind() {
            YTypeKind::XMLFragment | YTypeKind::XMLElement | YTypeKind::Unknown => xml_to_string(ty),
            YTypeKind::XMLText => xml_text_to_string(ty),
            _ => unreachable!("checked above"),
        })
    }

    // -----------------------------------------------------------------------
    // Synchronous writes (pre-validated so errors never leave partial commits)

    pub fn map_set(
        &mut self,
        target: &TypeTarget,
        key: String,
        value: SessionValue,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        validate_session_value(&value, 0)?;
        self.mutate_in_tx(|store, store_ref| {
            let parent = resolve_target(store, target)?;
            insert_session_value(store, store_ref, &parent, InsertSlot::MapKey(key), value)
        })
    }

    pub fn map_remove(&mut self, target: &TypeTarget, key: &str) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                solidify_map_kind(ty)?;
                map::map_remove(store, ty, key);
                Ok(())
            })
        })
    }

    pub fn map_clear(&mut self, target: &TypeTarget) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                solidify_map_kind(ty)?;
                map::map_clear(store, ty);
                Ok(())
            })
        })
    }

    pub fn array_insert(
        &mut self,
        target: &TypeTarget,
        index: u64,
        values: Vec<SessionValue>,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        for v in &values {
            validate_session_value(v, 0)?;
        }
        self.mutate_in_tx(|store, store_ref| {
            let parent = resolve_target(store, target)?;
            {
                let ty = parent.ty().ok_or(JwstCodecError::DocReleased)?;
                check_array_read_kind(ty)?;
                if index > ty.len {
                    return Err(JwstCodecError::IndexOutOfBound(index));
                }
            }
            for (cursor, value) in (index..).zip(values) {
                insert_session_value(store, store_ref, &parent, InsertSlot::ListIndex(cursor), value)?;
            }
            Ok(())
        })
    }

    pub fn array_push(
        &mut self,
        target: &TypeTarget,
        values: Vec<SessionValue>,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        for v in &values {
            validate_session_value(v, 0)?;
        }
        self.mutate_in_tx(|store, store_ref| {
            let parent = resolve_target(store, target)?;
            let start = {
                let ty = parent.ty().ok_or(JwstCodecError::DocReleased)?;
                check_array_read_kind(ty)?;
                ty.len
            };
            for (cursor, value) in (start..).zip(values) {
                insert_session_value(store, store_ref, &parent, InsertSlot::ListIndex(cursor), value)?;
            }
            Ok(())
        })
    }

    pub fn array_remove(
        &mut self,
        target: &TypeTarget,
        index: u64,
        len: u64,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                check_array_read_kind(ty)?;
                if len > 0 && ty.len > 0 && index >= ty.len {
                    return Err(JwstCodecError::IndexOutOfBound(index));
                }
                solidify_array_kind(ty)?;
                list_remove(&parent, store, ty, index, len)
            })
        })
    }

    pub fn text_insert(
        &mut self,
        target: &TypeTarget,
        index: u64,
        text_str: &str,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                check_text_read_kind(ty)?;
                if index > ty.len {
                    return Err(JwstCodecError::IndexOutOfBound(index));
                }
                solidify_text_kind(ty)?;
                list_insert(&parent, store, ty, index, Content::String(text_str.to_string()))
            })
        })
    }

    pub fn text_remove(
        &mut self,
        target: &TypeTarget,
        index: u64,
        len: u64,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                check_text_read_kind(ty)?;
                if len > 0 && ty.len > 0 && index >= ty.len {
                    return Err(JwstCodecError::IndexOutOfBound(index));
                }
                solidify_text_kind(ty)?;
                text::text_remove(&parent, store, ty, index, len)
            })
        })
    }

    pub fn text_apply_delta(
        &mut self,
        target: &TypeTarget,
        delta: &[TextDeltaOp],
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                check_text_read_kind(ty)?;
                text::validate_delta_against_len(ty.len, delta)?;
                solidify_text_kind(ty)?;
                text::apply_text_delta(&parent, store, ty, delta)
            })
        })
    }

    pub fn text_format(
        &mut self,
        target: &TypeTarget,
        index: u64,
        len: u64,
        attrs: TextAttributes,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                check_text_read_kind(ty)?;
                if index > ty.len {
                    return Err(JwstCodecError::IndexOutOfBound(index));
                }
                if len > 0 && !attrs.is_empty() && index.checked_add(len).is_none_or(|end| end > ty.len) {
                    return Err(JwstCodecError::IndexOutOfBound(len));
                }
                solidify_text_kind(ty)?;
                text::text_format(&parent, store, ty, index, len, attrs)
            })
        })
    }

    pub fn text_insert_embed(
        &mut self,
        target: &TypeTarget,
        index: u64,
        embed: Any,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                check_text_read_kind(ty)?;
                if index > ty.len {
                    return Err(JwstCodecError::IndexOutOfBound(index));
                }
                solidify_text_kind(ty)?;
                text::text_insert_embed(&parent, store, ty, index, embed)
            })
        })
    }

    pub fn xml_set_attr(
        &mut self,
        target: &TypeTarget,
        key: String,
        value: Any,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                solidify_xml_element_kind(ty)?;
                map::map_insert(&parent, store, ty, key, Content::from(value))
            })
        })
    }

    pub fn xml_remove_attr(&mut self, target: &TypeTarget, key: &str) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.mutate_in_tx(|store, _| {
            let parent = resolve_target(store, target)?;
            parent.write_locked(store, |store, ty| {
                solidify_xml_element_kind(ty)?;
                map::map_remove(store, ty, key);
                Ok(())
            })
        })
    }

    // -----------------------------------------------------------------------
    // Sync and RelativePosition

    /// Applies a remote V1 update, returning all commits produced in order:
    /// - `[]` if the update made no change,
    /// - `[remote_commit]` (`is_local: false, origin_kind: RemoteSync`) in the
    ///   common case,
    /// - `[remote_commit, cleanup_commit]` when the remote update triggered a
    ///   local [`SessionOriginKind::FormattingCleanup`] commit (`is_local:
    ///   true`) that the host should broadcast to peers.
    pub fn apply_update_v1(&mut self, bytes: &[u8]) -> JwstCodecResult<Vec<SessionCommit<M>>> {
        if self.active_tx.is_some() {
            return Err(JwstCodecError::OpenTransactionFrame);
        }
        let mut decoder = RawDecoder::new(bytes);
        let update = Update::read(&mut decoder)?;
        let store_ref = &self.doc_ref().store;
        let (_, primary, cleanup) = transaction::transact_mut_with_events(store_ref, None, false, |tx| {
            tx.incoming = Some(IncomingUpdate::of(&update));
            Doc::integrate_update(tx.store_mut(), store_ref, update)
        })?;
        let mut commits = Vec::with_capacity(usize::from(primary.is_some()) + usize::from(cleanup.is_some()));
        if let Some(ev) = primary.as_ref() {
            commits.push(self.build_commit_unlocked(ev, None));
        }
        if let Some(cleanup_ev) = cleanup.as_ref() {
            commits.push(self.build_commit_unlocked(cleanup_ev, None));
        }
        Ok(commits)
    }

    pub fn encode_state_vector_v1(&self) -> JwstCodecResult<Vec<u8>> {
        self.doc_ref().get_state_vector().encode_v1()
    }

    pub fn encode_update_v1(&self) -> JwstCodecResult<Vec<u8>> {
        self.doc_ref().encode_update_v1()
    }

    pub fn encode_diff_v1(&self, remote_sv: &[u8]) -> JwstCodecResult<Vec<u8>> {
        let sv = StateVector::decode_v1(remote_sv)?;
        self.doc_ref().encode_state_as_update_v1(&sv)
    }

    pub fn create_relative_position(
        &self,
        target: &TypeTarget,
        index: u64,
        assoc: i64,
    ) -> JwstCodecResult<RelativePosition> {
        let store = read_store(&self.doc_ref().store)?;
        let ty_ref = resolve_target(&store, target)?;
        let ty = ty_ref.ty().ok_or(JwstCodecError::DocReleased)?;
        RelativePosition::from_type_index(ty, index, assoc)
    }

    pub fn resolve_relative_position(
        &self,
        rpos: &RelativePosition,
        follow_undone_deletions: bool,
    ) -> Option<AbsolutePosition> {
        let store = read_store(&self.doc_ref().store).ok()?;
        rpos.resolve(&store, follow_undone_deletions)
    }

    // -----------------------------------------------------------------------
    // Undo / Redo (single-stack defaults + multi-stack scoped API)

    pub fn advance_time(&self, now_ms: u64) {
        self.now.fetch_max(now_ms, Ordering::AcqRel);
    }

    /// Creates a new independent undo stack on this session.
    ///
    /// - Empty `scopes` means document-wide scope (`Scope::Doc`).
    /// - Non-empty `scopes` resolves each [`TypeTarget`] to a mounted subtree.
    /// - `tracked_origins` specifies which [`SessionTxOrigin`]s this stack
    ///   captures (defaults to `[Tracked]` if empty).
    pub fn create_undo_stack(
        &mut self,
        scopes: &[TypeTarget],
        capture_timeout_ms: u64,
        tracked_origins: &[SessionTxOrigin],
    ) -> JwstCodecResult<UndoStackId> {
        let resolved_origins: Vec<Option<Origin>> = if tracked_origins.is_empty() {
            vec![Some(self.tracked_origin.clone())]
        } else {
            tracked_origins
                .iter()
                .map(|o| Some(self.resolve_tx_origin(o)))
                .collect()
        };
        let store_ref = self.doc_ref().store.clone();
        let now = self.now.clone();
        let (stack_id, manager_id) = {
            let mut store = write_store(&store_ref)?;
            let mut resolved_scopes = Vec::with_capacity(scopes.len());
            for target in scopes {
                resolved_scopes.push(resolve_target(&store, target)?);
            }
            if store.history_hook.is_none() {
                store.history_hook = Some(Box::new(SessionHistoryHub::new(now)));
            }
            let hub = store
                .history_hook
                .as_deref_mut()
                .and_then(|hook| hook.as_any_mut().downcast_mut::<SessionHistoryHub>())
                .ok_or(JwstCodecError::UndoManagerExists)?;
            hub.create_stack(resolved_scopes, resolved_origins, capture_timeout_ms)?
        };
        self.has_history_hub = true;
        self.manager_to_stack.insert(manager_id, stack_id.0);
        Ok(stack_id)
    }

    /// Destroys an undo stack, never reuses its ID, and recomputes the
    /// store's retained GC set across all remaining stacks inside a maintenance
    /// transaction. Returns `Ok(true)` if the stack existed.
    pub fn destroy_undo_stack(&mut self, id: UndoStackId) -> JwstCodecResult<bool> {
        if self.active_tx.is_some() {
            return Err(JwstCodecError::OpenTransactionFrame);
        }
        if !self.has_history_hub {
            return Ok(false);
        }
        let store_ref = self.doc_ref().store.clone();
        let removed_manager = transact_maintenance(&store_ref, |tx| {
            let store = tx.store_mut();
            let mut hook = store.history_hook.take();
            let manager = hook
                .as_deref_mut()
                .and_then(|h| h.as_any_mut().downcast_mut::<SessionHistoryHub>())
                .and_then(|hub| hub.destroy_stack(id, store));
            store.history_hook = hook;
            Ok(manager)
        })?;
        if let Some(manager_id) = removed_manager {
            self.manager_to_stack.remove(&manager_id);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn pop_stack_impl(&mut self, id: UndoStackId, which: UndoStack) -> JwstCodecResult<Option<SessionCommit<M>>> {
        if self.active_tx.is_some() {
            return Err(JwstCodecError::OpenTransactionFrame);
        }
        if !self.has_history_hub {
            return Ok(None);
        }
        let store_ref = self.doc_ref().store.clone();
        let manager = {
            let store = read_store(&store_ref)?;
            store
                .history_hook
                .as_deref()
                .and_then(|h| h.as_any().downcast_ref::<SessionHistoryHub>())
                .and_then(|hub| hub.manager_id(id))
        };
        let Some(manager) = manager else {
            return Ok(None);
        };
        let origin = Origin::new(UndoOrigin::new_for_session(manager, which));
        let (performed, primary, _) = transaction::transact_mut_with_events(&store_ref, Some(origin), true, |tx| {
            let sref = tx.store_ref();
            let store = tx.store_mut();
            let mut hook = store.history_hook.take();
            let result = match hook
                .as_deref_mut()
                .and_then(|h| h.as_any_mut().downcast_mut::<SessionHistoryHub>())
            {
                Some(hub) => hub.pop_stack(id, store, sref, which),
                None => Ok(None),
            };
            store.history_hook = hook;
            result
        })?;
        match (performed, primary) {
            (Some((_, meta)), Some(ev)) => {
                let typed = meta.map(|m| (*downcast::<M>(m)).clone());
                Ok(Some(self.build_commit_unlocked(&ev, typed)))
            }
            _ => Ok(None),
        }
    }

    pub fn undo_stack(&mut self, id: UndoStackId) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.pop_stack_impl(id, UndoStack::Undo)
    }

    pub fn redo_stack(&mut self, id: UndoStackId) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.pop_stack_impl(id, UndoStack::Redo)
    }

    pub fn can_undo_stack(&self, id: UndoStackId) -> bool {
        if !self.has_history_hub {
            return false;
        }
        let Ok(store) = read_store(&self.doc_ref().store) else {
            return false;
        };
        store
            .history_hook
            .as_deref()
            .and_then(|h| h.as_any().downcast_ref::<SessionHistoryHub>())
            .is_some_and(|hub| hub.can_undo_redo(id).0)
    }

    pub fn can_redo_stack(&self, id: UndoStackId) -> bool {
        if !self.has_history_hub {
            return false;
        }
        let Ok(store) = read_store(&self.doc_ref().store) else {
            return false;
        };
        store
            .history_hook
            .as_deref()
            .and_then(|h| h.as_any().downcast_ref::<SessionHistoryHub>())
            .is_some_and(|hub| hub.can_undo_redo(id).1)
    }

    pub fn set_stack_selection_meta(&self, id: UndoStackId, stack: UndoStack, meta: M) -> JwstCodecResult<bool> {
        if !self.has_history_hub {
            return Ok(false);
        }
        let boxed: Meta = StdArc::new(meta);
        let mut store = write_store(&self.doc_ref().store)?;
        let Some(hub) = store
            .history_hook
            .as_deref_mut()
            .and_then(|h| h.as_any_mut().downcast_mut::<SessionHistoryHub>())
        else {
            after_unlock(move || drop(boxed));
            return Ok(false);
        };
        hub.set_top_meta(id, stack, boxed)
    }

    pub fn stop_capturing_stack(&mut self, id: UndoStackId) -> JwstCodecResult {
        if !self.has_history_hub {
            return Ok(());
        }
        let mut store = write_store(&self.doc_ref().store)?;
        if let Some(hub) = store
            .history_hook
            .as_deref_mut()
            .and_then(|h| h.as_any_mut().downcast_mut::<SessionHistoryHub>())
        {
            hub.stop_capturing_stack(id)?;
        }
        Ok(())
    }

    pub fn clear_stack_history(&mut self, id: UndoStackId, undo: bool, redo: bool) -> JwstCodecResult {
        if self.active_tx.is_some() {
            return Err(JwstCodecError::OpenTransactionFrame);
        }
        if !self.has_history_hub {
            return Ok(());
        }
        let store_ref = self.doc_ref().store.clone();
        transact_maintenance(&store_ref, |tx| {
            let store = tx.store_mut();
            let mut hook = store.history_hook.take();
            let res = match hook
                .as_deref_mut()
                .and_then(|h| h.as_any_mut().downcast_mut::<SessionHistoryHub>())
            {
                Some(hub) => hub.clear_stack(id, store, undo, redo),
                None => Ok(()),
            };
            store.history_hook = hook;
            res
        })
    }

    /// Attaches selection metadata to the top item of stack 0's undo stack.
    pub fn set_undo_selection_meta(&self, meta: M) -> JwstCodecResult<bool> {
        self.set_stack_selection_meta(UndoStackId(0), UndoStack::Undo, meta)
    }

    pub fn undo(&mut self) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.undo_stack(UndoStackId(0))
    }

    pub fn redo(&mut self) -> JwstCodecResult<Option<SessionCommit<M>>> {
        self.redo_stack(UndoStackId(0))
    }

    pub fn stop_capturing(&mut self) -> JwstCodecResult {
        if !self.has_history_hub {
            return Ok(());
        }
        self.stop_capturing_stack(UndoStackId(0))
    }

    pub fn clear_history(&mut self, undo: bool, redo: bool) -> JwstCodecResult {
        if !self.has_history_hub {
            return Ok(());
        }
        self.clear_stack_history(UndoStackId(0), undo, redo)
    }

    pub fn can_undo(&self) -> bool {
        self.can_undo_stack(UndoStackId(0))
    }

    pub fn can_redo(&self) -> bool {
        self.can_redo_stack(UndoStackId(0))
    }

    // -----------------------------------------------------------------------
    // Internal helpers

    fn mutate_in_tx(
        &mut self,
        f: impl FnOnce(&mut DocStore, &StoreRef) -> JwstCodecResult,
    ) -> JwstCodecResult<Option<SessionCommit<M>>> {
        let store_ref = self.doc_ref().store.clone();
        let mut store = write_store(&store_ref)?;
        if self.active_tx.is_some() {
            f(&mut store, &store_ref)?;
            return Ok(None);
        }
        if store.client_required {
            return Err(JwstCodecError::ClientIdRequired);
        }
        debug_assert!(store.collector.is_empty());
        let mut before_state = store.get_state_vector();
        let mut local = true;
        let mut capture_history = true;
        let origin = Some(self.tracked_origin.clone());
        let mut incoming = None;

        let res = f(&mut store, &store_ref);
        if let Err(err) = res {
            debug_assert!(
                store.collector.is_empty(),
                "failed standalone session write mutated store.collector"
            );
            if let Some(origin) = origin {
                after_unlock(move || drop(origin));
            }
            return Err(err);
        }
        let (primary, _) = commit_store(
            &mut store,
            &mut before_state,
            &mut local,
            &mut capture_history,
            &origin,
            &mut incoming,
            None,
            true,
        );
        let commit = primary.as_ref().map(|ev| self.build_commit_locked(&store, ev, None));
        if let Some(origin) = origin {
            after_unlock(move || drop(origin));
        }
        Ok(commit)
    }

    fn classify_origin(&self, summary: &CommitSummary) -> SessionOriginKind {
        if !summary.local {
            return SessionOriginKind::RemoteSync;
        }
        if let Some(origin) = &summary.origin {
            if origin.downcast_ref::<text::cleanup::FormattingCleanup>().is_some() {
                return SessionOriginKind::FormattingCleanup;
            }
            if let Some(undo_origin) = origin.downcast_ref::<UndoOrigin>() {
                let stack_id = self.manager_to_stack.get(&undo_origin.manager()).copied().unwrap_or(0);
                return match undo_origin.stack() {
                    UndoStack::Undo => SessionOriginKind::Undo { stack_id },
                    UndoStack::Redo => SessionOriginKind::Redo { stack_id },
                };
            }
            if origin.same(&self.untracked_origin) {
                return SessionOriginKind::LocalUntracked;
            }
            if let Some(named) = origin.downcast_ref::<SessionNamedOrigin>() {
                return SessionOriginKind::LocalNamed(named.0.to_string());
            }
        }
        SessionOriginKind::LocalTransact
    }

    fn build_commit_locked(
        &self,
        store: &DocStore,
        event: &CommitEvent,
        selection_meta: Option<M>,
    ) -> SessionCommit<M> {
        let changed = event
            .summary
            .changed
            .iter()
            .map(|c| {
                let mut keys: Vec<String> = c.keys.to_vec();
                keys.sort();
                keys.dedup();
                let path = resolve_identity_raw(store, &c.identity)
                    .ok()
                    .and_then(|ty_ref| compute_type_path(&ty_ref));
                SessionChangedType {
                    identity: c.identity.clone(),
                    path,
                    keys,
                }
            })
            .collect();

        let (can_undo, can_redo) = store
            .history_hook
            .as_deref()
            .and_then(|hook| hook.as_any().downcast_ref::<SessionHistoryHub>())
            .map(|hub| hub.can_undo_redo(UndoStackId(0)))
            .unwrap_or((false, false));

        SessionCommit {
            revision: event.seq,
            update: event.update.clone(),
            is_local: event.summary.local,
            origin_kind: self.classify_origin(&event.summary),
            changed,
            subdocs_added: event.summary.subdocs_added.iter().cloned().collect(),
            subdocs_removed: event.summary.subdocs_removed.iter().cloned().collect(),
            can_undo,
            can_redo,
            selection_meta,
        }
    }

    fn build_commit_unlocked(&self, event: &CommitEvent, selection_meta: Option<M>) -> SessionCommit<M> {
        let store = read_store_or_panic(&self.doc_ref().store);
        self.build_commit_locked(&store, event, selection_meta)
    }
}

impl<M: Clone + Send + Sync + 'static> Drop for DocSession<M> {
    fn drop(&mut self) {
        // Never silently commit an open deferred transaction frame on Drop, and
        // never call `set_retained` here (the exclusive store is being
        // dropped).
        let _ = self.active_tx.take();
        if self.has_history_hub
            && let Some(doc) = self.doc.as_ref()
            && let Ok(mut store) = write_store(&doc.store)
            && let Some(hook) = store.history_hook.take()
        {
            after_unlock(move || drop(hook));
        }
    }
}
