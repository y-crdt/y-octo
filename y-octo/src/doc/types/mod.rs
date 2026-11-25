mod arena;
pub(crate) mod array;
mod list;
pub(crate) mod map;
mod preliminary;
pub(crate) mod text;
mod value;
pub(crate) mod xml;

use std::{
    fmt,
    hash::{Hash, Hasher},
    sync::Weak,
};

use arena::Staging;
pub(crate) use arena::{TypeArena, TypeCx, TypeIdx};
pub use array::*;
pub(crate) use list::*;
pub use map::*;
pub use text::*;
pub use value::*;
pub use xml::*;

use super::{
    store::{StoreRef, WeakStoreRef},
    *,
};
use crate::{Item, JwstCodecError, JwstCodecResult, sync::Arc};

type TypeMap = HashMap<SmolStr, ItemRef>;

/// Where a type is in its life, see [YType::carrier].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum CarrierState {
    /// Never inserted: a named root, or a preliminary type.
    #[default]
    Unset,
    /// Inserted, `item` is its carrier.
    Live,
    /// The carrier was collected. Never leaves this state.
    Retired,
}

/// The item a type was inserted with, see [YType::carrier].
pub(crate) enum Carrier<'a> {
    /// Never inserted: a named root, or a preliminary type.
    Unset,
    /// The live carrier. It may be deleted, but its content is still this
    /// type.
    Live(&'a Item),
    /// The carrier was garbage-collected (its content dropped, or the whole
    /// item replaced by a GC struct). The type reads as empty, refuses writes
    /// and cannot be inserted again.
    Retired,
}

// The rarely set fields are boxed, names included: a thin pointer each keeps
// the type small for the many types that have neither name nor keys.
#[allow(clippy::box_collection)]
#[derive(Debug, Default)]
pub(crate) struct YType {
    pub start: ItemRef,
    /// The carrier, set exactly while [YType::carrier] is [Carrier::Live].
    item: ItemRef,
    /// The values by key, allocated with the first key.
    map: Option<Box<TypeMap>>,
    pub len: u64,
    /// The tag name of XMLElement and XMLHook type
    name: Option<Box<String>>,
    /// The name of the type that directly belongs the store.
    root_name: Option<Box<String>>,
    pub markers: Option<Box<MarkerList>>,
    /// Local-only editing state before this subtree is mounted. It is protected
    /// by the owning document lock, and never contributes to its SV or update.
    pub preliminary: Option<Box<DocStore>>,
    /// The type holding the carrier, set with it.
    parent_type: Option<TypeIdx>,
    kind: YTypeKind,
    carrier_state: CarrierState,
    /// Monotonic: this type has acquired a document identity. Retirement is
    /// still determined by its carrying item, never by resetting this bit.
    pub published: bool,
    /// Sticky, like Yjs _hasFormatting, even after the last Format is deleted.
    pub has_formatting: bool,
}

/// A handle to a type stored in a [DocStore].
///
/// Lock protocol: the owning store's `RwLock` is the only synchronization
/// point. The handle holds no type data, only the document and the slot of
/// the type in its [TypeArena]; the [YType] (and every [Item] reachable from
/// it) is only read through the store while its lock is held for reading and
/// only mutated through it while the lock is held for writing. Public APIs
/// take the lock through [YTypeRef::read] / [YTypeRef::write]; code that
/// already runs under the lock indexes the store's arena with [TypeIdx].
#[derive(Default, Clone)]
pub(crate) struct YTypeRef {
    pub store: WeakStoreRef,
    pub id: Option<TypeIdx>,
}

/// Only the handle's identity: the public type handles (`Text`, `Array`,
/// `Map`, `Value`, ...) derive `Debug` through it and may be formatted on any
/// thread without the store lock, or with it already held, so the type's data
/// is neither read nor locked here.
impl fmt::Debug for YTypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("YTypeRef")
            .field("store", &self.store.as_ptr())
            .field("id", &self.id)
            .finish()
    }
}

impl PartialEq for YTypeRef {
    fn eq(&self, other: &Self) -> bool {
        // identity only: the same slot of the same document
        Weak::ptr_eq(&self.store, &other.store) && self.id == other.id
    }
}

impl Eq for YTypeRef {}

impl Hash for YTypeRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.store.as_ptr() as usize).hash(state);
        self.id.hash(state);
    }
}

impl YType {
    pub fn new(kind: YTypeKind, tag_name: Option<String>) -> Self {
        YType {
            kind,
            name: tag_name.map(Box::new),
            ..YType::default()
        }
    }

    /// A type that directly belongs to the store under `root_name`.
    pub fn new_root(kind: YTypeKind, tag_name: Option<String>, root_name: String) -> Self {
        YType {
            kind,
            name: tag_name.map(Box::new),
            root_name: Some(Box::new(root_name)),
            published: true,
            ..YType::default()
        }
    }

    pub fn kind(&self) -> YTypeKind {
        self.kind
    }

    /// The tag name of XMLElement and XMLHook type
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref().map(String::as_str)
    }

    pub fn set_name(&mut self, name: Option<String>) {
        self.name = name.map(Box::new);
    }

    /// The name of the type that directly belongs the store.
    pub fn root_name(&self) -> Option<&str> {
        self.root_name.as_deref().map(String::as_str)
    }

    /// The carrier of this type and, with it, where the type is in its life:
    /// never inserted, inserted, or retired.
    pub fn carrier<'a>(&self, items: &'a ItemSpace) -> Carrier<'a> {
        match self.carrier_state {
            CarrierState::Unset => Carrier::Unset,
            // A carrier that never reached the store (its integration failed)
            // is gone like a collected one.
            CarrierState::Live => self.item.and_then(|i| items.get(i)).map_or(Carrier::Retired, |item| {
                debug_assert!(matches!(item.content, Content::Type(_)));
                debug_assert_eq!(self.parent_type, item.parent.as_ref().map(|parent| *parent));
                Carrier::Live(item)
            }),
            CarrierState::Retired => Carrier::Retired,
        }
    }

    /// The carrier while it is live.
    pub fn live_carrier<'a>(&self, items: &'a ItemSpace) -> Option<&'a Item> {
        match self.carrier(items) {
            Carrier::Live(item) => Some(item),
            Carrier::Unset | Carrier::Retired => None,
        }
    }

    /// The carrier while it is live, as a store reference.
    pub fn carrier_ref(&self) -> ItemRef {
        self.item
    }

    /// `item` now carries this type, as a child of `parent`.
    pub fn attach(&mut self, item: ItemRef, parent: Option<TypeIdx>) {
        debug_assert_ne!(self.carrier_state, CarrierState::Retired);
        self.item = item;
        self.parent_type = parent;
        self.carrier_state = CarrierState::Live;
    }

    /// The carrier was collected. Its children were taken before
    /// ([DocStore::take_type_children]).
    pub fn retire(&mut self) {
        self.item = None;
        self.parent_type = None;
        self.markers = None;
        self.carrier_state = CarrierState::Retired;
    }

    #[inline]
    pub fn map_get(&self, key: &str) -> Option<&ItemRef> {
        self.map.as_ref()?.get(key)
    }

    pub fn map_set(&mut self, key: SmolStr, item: ItemRef) {
        self.map.get_or_insert_default().insert(key, item);
    }

    pub fn map_iter(&self) -> impl Iterator<Item = (&SmolStr, &ItemRef)> {
        self.map.iter().flat_map(|map| map.iter())
    }

    pub fn map_values(&self) -> impl Iterator<Item = &ItemRef> {
        self.map.iter().flat_map(|map| map.values())
    }

    pub fn clear_map(&mut self) {
        self.map = None;
    }

    pub fn identity(&self, items: &ItemSpace) -> JwstCodecResult<TypeIdentity> {
        if self.is_preliminary() {
            return Err(JwstCodecError::InvalidParent);
        }
        if let Carrier::Live(item) = self.carrier(items) {
            Ok(TypeIdentity::Item(item.id))
        } else if let Some(name) = self.root_name() {
            Ok(TypeIdentity::Root(name.to_owned()))
        } else {
            Err(JwstCodecError::InvalidParent)
        }
    }

    pub fn set_kind(&mut self, kind: YTypeKind) -> JwstCodecResult {
        std::debug_assert!(kind != YTypeKind::Unknown);

        if self.kind() != kind {
            if self.kind == YTypeKind::Unknown {
                self.kind = kind;
            } else {
                return Err(JwstCodecError::TypeCastError(kind.as_str()));
            }
        }

        Ok(())
    }
}

impl YTypeRef {
    #[inline]
    pub fn store_ref(&self) -> JwstCodecResult<StoreRef> {
        self.store.upgrade().ok_or(JwstCodecError::DocReleased)
    }

    /// The slot of the type in its document.
    #[inline]
    pub fn idx(&self) -> JwstCodecResult<TypeIdx> {
        self.id.ok_or(JwstCodecError::DocReleased)
    }

    /// The reading context of this handle's document, for a caller holding
    /// its `store`.
    #[inline]
    pub fn cx<'a>(&'a self, store: &'a DocStore) -> TypeCx<'a> {
        TypeCx::new(&self.store, &store.type_arena)
    }

    /// Runs `f` under the owning store's read lock.
    pub fn read<R>(&self, f: impl FnOnce(&DocStore, &YType) -> R) -> JwstCodecResult<R> {
        let store_ref = self.store_ref()?;
        let store = read_store(&store_ref)?;
        let ty = store.type_arena.get(self.idx()?).ok_or(JwstCodecError::DocReleased)?;
        Ok(f(&store, ty))
    }

    /// [YTypeRef::read] for a reader that follows type indices or hands out
    /// handles.
    pub fn read_cx<R>(&self, f: impl FnOnce(TypeCx<'_>, &YType) -> R) -> JwstCodecResult<R> {
        self.read(|store, ty| f(self.cx(store), ty))
    }

    /// Runs `f` in an implicit write transaction of the owning document.
    pub fn write<R>(&self, f: impl FnOnce(&mut DocStore, TypeIdx) -> JwstCodecResult<R>) -> JwstCodecResult<R> {
        let store_ref = self.store_ref()?;
        transact_local_implicit(&store_ref, |store| self.write_locked(store, f))
    }

    /// Runs an edit of this type of `store` under the document's write lock,
    /// see [DocStore::edit_type].
    pub(in crate::doc) fn write_locked<R>(
        &self,
        store: &mut DocStore,
        f: impl FnOnce(&mut DocStore, TypeIdx) -> JwstCodecResult<R>,
    ) -> JwstCodecResult<R> {
        store.edit_type(self.idx()?, f)
    }
}

impl DocStore {
    /// Runs an edit of the type `id` of this store, under the document's
    /// write lock. `f` gets the store to edit and the type's slot in it:
    /// this store, or, before the type is mounted, the private store of its
    /// preliminary subtree with every type of the document in reach. Edits
    /// before mounting do not enter the document's collector.
    pub(in crate::doc) fn edit_type<R>(
        &mut self,
        id: TypeIdx,
        f: impl FnOnce(&mut DocStore, TypeIdx) -> JwstCodecResult<R>,
    ) -> JwstCodecResult<R> {
        match self.type_arena.preliminary_root(id)? {
            Some(root) => f(&mut Staging::enter(self, root), id),
            None => f(self, id),
        }
    }
}

/// A public type handle wrapping a [YTypeRef] whose kind is already checked.
pub(crate) trait FromTypeRef {
    fn from_type_ref(value: YTypeRef) -> Self;
}

pub(crate) struct YTypeBuilder {
    store: StoreRef,
    /// The tag name of XMLElement and XMLHook type
    name: Option<String>,
    /// The name of the type that directly belongs the store.
    root_name: Option<String>,
    kind: YTypeKind,
}

impl YTypeBuilder {
    pub fn new(store: StoreRef) -> Self {
        Self {
            store,
            name: None,
            root_name: None,
            kind: YTypeKind::Unknown,
        }
    }

    pub fn with_kind(mut self, kind: YTypeKind) -> Self {
        self.kind = kind;

        self
    }

    pub fn set_name(mut self, name: String) -> Self {
        self.root_name = Some(name);

        self
    }

    pub fn set_tag_name(mut self, tag_name: String) -> Self {
        self.name = Some(tag_name);

        self
    }

    fn handle(&self, id: TypeIdx) -> YTypeRef {
        YTypeRef {
            store: Arc::downgrade(&self.store),
            id: Some(id),
        }
    }

    pub fn build_exists<T: FromTypeRef>(self) -> JwstCodecResult<T> {
        let mut store = write_store(&self.store)?;
        let id = if let Some(root_name) = &self.root_name {
            match store.types.get(root_name) {
                Some(id) => *id,
                None => {
                    return Err(JwstCodecError::RootStructNotFound(root_name.clone()));
                }
            }
        } else {
            return Err(JwstCodecError::TypeCastError("root_name is not set"));
        };

        Self::assign_kind_and_name(self.kind, self.name.clone(), &mut store.type_arena, id)?;
        drop(store);

        Ok(T::from_type_ref(self.handle(id)))
    }

    /// Gives the type at `id` the builder's kind (and tag name if unset), or
    /// fails if it already has another kind. The caller holds the store write
    /// lock: finding or creating a type and assigning its kind is one step.
    fn assign_kind_and_name(
        kind: YTypeKind,
        tag_name: Option<String>,
        types: &mut TypeArena,
        id: TypeIdx,
    ) -> JwstCodecResult {
        if kind == YTypeKind::Unknown && tag_name.is_none() {
            return Ok(());
        }
        let ty = types.get_mut(id).ok_or(JwstCodecError::DocReleased)?;
        if kind != YTypeKind::Unknown {
            ty.set_kind(kind)?;
        }
        if ty.name.is_none() && tag_name.is_some() {
            ty.set_name(tag_name);
        }
        Ok(())
    }

    pub fn build<T: FromTypeRef>(self) -> JwstCodecResult<T> {
        let mut guard = write_store(&self.store)?;
        let store = &mut *guard;
        let id = if let Some(root_name) = &self.root_name {
            match store.types.get(root_name) {
                Some(id) => *id,
                None => {
                    let mut ty = YType::new_root(self.kind, self.name.clone(), root_name.clone());
                    ty.markers = Self::markers(self.kind);
                    let id = store.type_arena.alloc(ty)?;
                    store.types.insert(root_name.clone(), id);
                    id
                }
            }
        } else {
            // A preliminary type: the arena keeps it for the handle returned
            // here, whether or not it is ever inserted.
            let mut ty = YType::new(self.kind, self.name.clone());
            ty.markers = Self::markers(self.kind);
            store.type_arena.alloc(ty)?
        };

        Self::assign_kind_and_name(self.kind, self.name.clone(), &mut store.type_arena, id)?;
        drop(guard);

        Ok(T::from_type_ref(self.handle(id)))
    }

    fn markers(kind: YTypeKind) -> Option<Box<MarkerList>> {
        kind.uses_markers().then(Box::default)
    }
}

impl YTypeKind {
    pub(crate) fn uses_markers(self) -> bool {
        !matches!(self, Self::Map | Self::XMLHook)
    }
}

#[macro_export(local_inner_macros)]
macro_rules! impl_variants {
    ({$($name: ident: $codec_ref: literal),*}) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
        pub enum YTypeKind {
            $($name,)*
            #[default]
            Unknown,
        }

        impl YTypeKind {
            pub fn as_str(&self) -> &'static str {
                match self {
                    $(YTypeKind::$name => std::stringify!($name),)*
                    YTypeKind::Unknown => "Unknown",
                }
            }
        }

        impl From<u64> for YTypeKind {
            fn from(value: u64) -> Self {
                match value {
                    $($codec_ref => YTypeKind::$name,)*
                    _ => YTypeKind::Unknown,
                }
            }
        }


        impl From<YTypeKind> for u64 {
            fn from(value: YTypeKind) -> Self {
                std::debug_assert!(value != YTypeKind::Unknown);
                match value {
                    $(YTypeKind::$name => $codec_ref,)*
                    _ => std::unreachable!(),
                }
            }
        }
    };
}

pub(crate) trait AsInner {
    type Inner;
    fn as_inner(&self) -> &Self::Inner;
}

/// Stable within one document history, including across snapshot decoding.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeIdentity {
    Root(String),
    Item(Id),
}

#[macro_export(local_inner_macros)]
macro_rules! impl_type {
    ($name: ident) => {
        #[derive(Debug, Clone, PartialEq)]
        pub struct $name(pub(crate) super::YTypeRef);

        impl $name {
            pub(crate) fn new(inner: super::YTypeRef) -> Self {
                Self(inner)
            }

            /// The document identity, available after this type is mounted.
            /// Preliminary types and their nested children have no published identity.
            pub fn identity(&self) -> $crate::JwstCodecResult<super::TypeIdentity> {
                self.0.read(|store, ty| ty.identity(&store.type_arena.items))?
            }
        }

        impl super::AsInner for $name {
            type Inner = super::YTypeRef;

            #[inline(always)]
            fn as_inner(&self) -> &Self::Inner {
                &self.0
            }
        }

        impl TryFrom<super::YTypeRef> for $name {
            type Error = $crate::JwstCodecError;

            fn try_from(value: super::YTypeRef) -> Result<Self, Self::Error> {
                match value.write(|store, id| store.type_arena[id].set_kind(super::YTypeKind::$name)) {
                    Ok(()) => Ok($name::new(value)),
                    Err(err @ ($crate::JwstCodecError::Reentrant | $crate::JwstCodecError::DocPoisoned)) => Err(err),
                    Err(_) => Err($crate::JwstCodecError::TypeCastError(std::stringify!($name))),
                }
            }
        }

        impl $name {
            pub(crate) fn from_unchecked(value: super::YTypeRef) -> Self {
                $name::new(value.clone())
            }
        }

        impl super::FromTypeRef for $name {
            fn from_type_ref(value: super::YTypeRef) -> Self {
                $name::new(value)
            }
        }

        impl From<$name> for super::Value {
            fn from(value: $name) -> Self {
                Self::$name(value)
            }
        }
    };
}

impl_variants!({
    Array: 0,
    Map: 1,
    Text: 2,
    XMLElement: 3,
    XMLFragment: 4,
    XMLHook: 5,
    XMLText: 6
    // Doc: 9?
});
