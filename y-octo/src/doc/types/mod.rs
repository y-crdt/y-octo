pub(crate) mod array;
mod list;
pub(crate) mod map;
pub(crate) mod text;
mod value;
mod xml;

use std::{
    collections::hash_map::Entry,
    fmt,
    hash::{Hash, Hasher},
    sync::Weak,
};

pub use array::*;
use list::*;
pub use map::*;
pub use text::*;
pub use value::*;
pub use xml::*;

use super::{
    store::{StoreRef, WeakStoreRef},
    *,
};
use crate::{Item, JwstCodecError, JwstCodecResult, sync::Arc};

#[derive(Debug, Default)]
pub(crate) struct YType {
    pub start: Somr<Item>,
    pub item: Somr<Item>,
    pub map: HashMap<SmolStr, Somr<Item>>,
    pub len: u64,
    /// The tag name of XMLElement and XMLHook type
    pub name: Option<String>,
    /// The name of the type that directly belongs the store.
    pub root_name: Option<String>,
    kind: YTypeKind,
    pub markers: Option<MarkerList>,
}

/// A handle to a type stored in a [DocStore].
///
/// Lock protocol: the owning store's `RwLock` is the only synchronization
/// point. The [YType] behind `inner` (and every [Item] reachable from it) is
/// only read while that lock is held for reading and only mutated while it is
/// held for writing. Public APIs take the lock through [YTypeRef::read] /
/// [YTypeRef::write]; code that already runs under the lock uses
/// [YTypeRef::ty] / [YTypeRef::ty_mut]. A type that has no store yet (decoded
/// from an update and not integrated) has a single owner and needs no lock.
#[derive(Default, Clone)]
pub(crate) struct YTypeRef {
    pub store: WeakStoreRef,
    pub inner: Somr<YType>,
}

/// Only the handle's identity: the public type handles (`Text`, `Array`,
/// `Map`, `Value`, ...) derive `Debug` through it and may be formatted on any
/// thread without the store lock, or with it already held, so the type's data
/// is neither read nor locked here.
impl fmt::Debug for YTypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("YTypeRef")
            .field("ptr", &self.inner.ptr())
            .field("owned", &self.inner.is_owned())
            .finish()
    }
}

impl PartialEq for YType {
    fn eq(&self, other: &Self) -> bool {
        self.root_name == other.root_name
            || (self.start.is_some() && self.start == other.start)
            || self.map == other.map
    }
}

impl PartialEq for YTypeRef {
    fn eq(&self, other: &Self) -> bool {
        // only check pointer equality
        // currently no scenarios that involve cross document ytype comparisons
        self.inner.ptr_eq(&other.inner)
    }
}

impl Eq for YTypeRef {}

impl Hash for YTypeRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.ptr().hash(state);
    }
}

impl YType {
    pub fn new(kind: YTypeKind, tag_name: Option<String>) -> Self {
        YType {
            kind,
            name: tag_name,
            ..YType::default()
        }
    }

    pub fn kind(&self) -> YTypeKind {
        self.kind
    }

    pub fn identity(&self) -> JwstCodecResult<TypeIdentity> {
        if let Some(item) = self.item.get() {
            Ok(TypeIdentity::Item(item.id))
        } else if let Some(name) = &self.root_name {
            Ok(TypeIdentity::Root(name.clone()))
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
    pub fn new(kind: YTypeKind, tag_name: Option<String>) -> Self {
        Self {
            inner: Somr::new(YType::new(kind, tag_name)),
            store: Weak::new(),
        }
    }

    /// Shared view of the type. The caller holds the owning store's lock (or
    /// the type is detached), see [YTypeRef].
    #[inline]
    pub fn ty(&self) -> Option<&YType> {
        self.inner.get()
    }

    /// Exclusive view of the type.
    ///
    /// # Safety
    /// The caller holds the owning store's write lock (or the type is
    /// detached) and no other reference to this [YType] is alive.
    #[inline]
    pub unsafe fn ty_mut(&self) -> Option<InnerRefMut<'_, YType>> {
        if self.inner.is_some() {
            Some(unsafe { self.inner.get_mut_unchecked() })
        } else {
            None
        }
    }

    pub fn store_ref(&self) -> JwstCodecResult<StoreRef> {
        self.store.upgrade().ok_or(JwstCodecError::DocReleased)
    }

    /// Runs `f` under the owning store's read lock.
    pub fn read<R>(&self, f: impl FnOnce(&DocStore, &YType) -> R) -> JwstCodecResult<R> {
        let store_ref = self.store_ref()?;
        let store = store_ref.read().unwrap();
        let ty = self.ty().ok_or(JwstCodecError::DocReleased)?;
        Ok(f(&store, ty))
    }

    /// Runs `f` under the owning store's write lock.
    pub fn write<R>(&self, f: impl FnOnce(&mut DocStore, &mut YType) -> JwstCodecResult<R>) -> JwstCodecResult<R> {
        let store_ref = self.store_ref()?;
        let mut store = store_ref.write().unwrap();
        // SAFETY: we hold the store write lock and this is the only reference
        // to the type handed out under it.
        let mut ty = unsafe { self.ty_mut() }.ok_or(JwstCodecError::DocReleased)?;
        f(&mut store, &mut ty)
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

    #[allow(dead_code)]
    pub fn set_tag_name(mut self, tag_name: String) -> Self {
        self.name = Some(tag_name);

        self
    }

    pub fn build_exists<T: FromTypeRef>(self) -> JwstCodecResult<T> {
        let kind = self.kind;
        let store = self.store.write().unwrap();
        let ty = if let Some(root_name) = &self.root_name {
            match store.types.get(root_name) {
                Some(ty) => ty.clone(),
                None => {
                    return Err(JwstCodecError::RootStructNotFound(root_name.clone()));
                }
            }
        } else {
            return Err(JwstCodecError::TypeCastError("root_name is not set"));
        };

        Self::assign_kind(kind, &ty)?;
        drop(store);

        Ok(T::from_type_ref(ty))
    }

    /// Gives `ty` the builder's kind, or fails if it already has another one.
    /// The caller holds the store write lock: finding or creating a type and
    /// assigning its kind is one step.
    fn assign_kind(kind: YTypeKind, ty: &YTypeRef) -> JwstCodecResult {
        if kind == YTypeKind::Unknown {
            return Ok(());
        }
        // SAFETY: the caller holds the store write lock and no reference to
        // this type's data.
        match unsafe { ty.ty_mut() } {
            Some(mut inner) => inner.set_kind(kind),
            None => Err(JwstCodecError::DocReleased),
        }
    }

    pub fn build<T: FromTypeRef>(self) -> JwstCodecResult<T> {
        let kind = self.kind;
        let mut store = self.store.write().unwrap();
        let ty = if let Some(root_name) = self.root_name {
            match store.types.entry(root_name.clone()) {
                Entry::Occupied(e) => e.get().clone(),
                Entry::Vacant(e) => {
                    let inner = Somr::new(YType {
                        kind: self.kind,
                        name: self.name,
                        root_name: Some(root_name),
                        markers: Self::markers(self.kind),
                        ..Default::default()
                    });

                    let ty = YTypeRef {
                        store: Arc::downgrade(&self.store),
                        inner,
                    };

                    let ty_ref = ty.clone();
                    e.insert(ty);

                    ty_ref
                }
            }
        } else {
            let inner = Somr::new(YType {
                kind: self.kind,
                name: self.name,
                root_name: self.root_name.clone(),
                markers: Self::markers(self.kind),
                ..Default::default()
            });

            let ty = YTypeRef {
                store: Arc::downgrade(&self.store),
                inner,
            };

            let ty_ref = ty.clone();

            store.dangling_types.insert(ty.inner.ptr().as_ptr() as usize, ty);

            ty_ref
        };

        Self::assign_kind(kind, &ty)?;
        drop(store);

        Ok(T::from_type_ref(ty))
    }

    fn markers(kind: YTypeKind) -> Option<MarkerList> {
        match kind {
            YTypeKind::Map => None,
            _ => Some(MarkerList::new()),
        }
    }
}

#[macro_export(local_inner_macros)]
macro_rules! impl_variants {
    ({$($name: ident: $codec_ref: literal),*}) => {
        #[derive(Debug, Clone, Copy, PartialEq, Default)]
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

            pub fn identity(&self) -> $crate::JwstCodecResult<super::TypeIdentity> {
                self.0.read(|_, ty| ty.identity())?
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
                value
                    .write(|_, inner| inner.set_kind(super::YTypeKind::$name))
                    .map_err(|_| $crate::JwstCodecError::TypeCastError(std::stringify!($name)))?;
                Ok($name::new(value))
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
