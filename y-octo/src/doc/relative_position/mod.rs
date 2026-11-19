//! Yjs-compatible relative positions, ported from
//! `src/utils/RelativePosition.js` of Yjs v13.6.33.
//!
//! A relative position names a character (or array slot) by its id, so it keeps
//! pointing at the same content while other content is inserted or deleted
//! around it. The binary and JSON forms are the ones Yjs reads and writes.
//!
//! One intended difference from Yjs: when the type a position lives in has been
//! deleted, Yjs resolves to index 0 of that (deleted) type, while
//! [`Doc::resolve_relative_position`] returns `None` so that callers drop the
//! selection instead of moving it to a type that is gone. A root name the
//! document does not have also resolves to `None`; Yjs creates the root type.

#[cfg(all(test, not(loom)))]
mod tests;

use serde::{Deserialize, Serialize};

use super::*;

/// Yjs `RelativePosition`.
///
/// `item` names the character or array slot the position is associated with:
/// the one after the position when `assoc >= 0`, the one before it when
/// `assoc < 0`. Without `item` the position is at the start (`assoc < 0`) or
/// the end (`assoc >= 0`) of the type named by `tname` (a root type) or `type`
/// (the id of the item holding a nested type). Positions created from an index
/// carry both the type and the item, like in Yjs; the binary form keeps only
/// the item then.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(try_from = "RelativePositionJson", into = "RelativePositionJson")]
pub struct RelativePosition {
    pub r#type: Option<Id>,
    pub tname: Option<String>,
    pub item: Option<Id>,
    pub assoc: i64,
}

/// Yjs `AbsolutePosition`: an index in a type of the document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbsolutePosition {
    /// The type the index is in.
    pub r#type: TypeIdentity,
    /// Index in UTF-16 code units for text, in elements for arrays.
    pub index: u64,
    pub assoc: i64,
}

impl RelativePosition {
    /// Yjs `encodeRelativePosition`.
    pub fn encode(&self) -> JwstCodecResult<Vec<u8>> {
        let mut encoder = RawEncoder::default();
        self.write(&mut encoder)?;
        Ok(encoder.into_inner())
    }

    /// Yjs `decodeRelativePosition`. Unlike Yjs, an unknown kind or bytes left
    /// after the position are errors.
    pub fn decode<T: AsRef<[u8]>>(bytes: T) -> JwstCodecResult<Self> {
        let mut decoder = RawDecoder::new(bytes.as_ref());
        let rpos = Self::read(&mut decoder)?;
        if !decoder.is_empty() {
            return Err(JwstCodecError::UpdateNotFullyConsumed(decoder.len() as usize));
        }
        Ok(rpos)
    }

    /// Yjs `createRelativePositionFromTypeIndex` on the type data `ty`.
    fn from_type_index(ty: &YType, index: u64, assoc: i64) -> JwstCodecResult<Self> {
        check_assoc(assoc)?;
        if index > ty.len {
            return Err(JwstCodecError::IndexOutOfBound(index));
        }
        let (r#type, tname) = if let Some(item) = ty.item.get() {
            (Some(item.id), None)
        } else if let Some(name) = &ty.root_name {
            (None, Some(name.clone()))
        } else {
            // a type that is not in the document yet has no identity
            return Err(JwstCodecError::InvalidParent);
        };
        let position = |item| Self {
            r#type,
            tname,
            item,
            assoc,
        };

        let mut index = index;
        if assoc < 0 {
            // associated with the character before the position, or the start
            if index == 0 {
                return Ok(position(None));
            }
            index -= 1;
        }

        let mut cur = ty.start.clone();
        while let Some(item) = cur.get() {
            if item.indexable() {
                if item.len() > index {
                    return Ok(position(Some(Id::new(item.id.client, item.id.clock + index))));
                }
                index -= item.len();
            }
            cur = item.right.clone();
        }

        // `index == len` and `assoc >= 0`: the end of the type
        Ok(position(None))
    }

    /// Yjs `createAbsolutePositionFromRelativePosition`.
    fn resolve(&self, store: &DocStore, follow_undone_deletions: bool) -> Option<AbsolutePosition> {
        let lookup = |id: Id| {
            // structs the document has not received yet
            if store.get_state(id.client) <= id.clock {
                return None;
            }
            if follow_undone_deletions {
                store.follow_redone(id)
            } else {
                store.item_with_offset(id)
            }
        };

        if let Some(id) = self.item {
            let (item_ref, offset) = lookup(id)?;
            let item = item_ref.get()?;
            let Some(Parent::Type(parent)) = &item.parent else {
                unreachable!("items in the store have a type parent");
            };
            let parent = parent.ty()?;
            let identity = live_identity(&parent)?;

            let mut index = if item.indexable() {
                offset + if self.assoc >= 0 { 0 } else { 1 }
            } else {
                0
            };
            let mut cur = item.left.clone();
            while let Some(left) = cur.get() {
                if left.indexable() {
                    index += left.len();
                }
                cur = left.left.clone();
            }

            Some(AbsolutePosition {
                r#type: identity,
                index,
                assoc: self.assoc,
            })
        } else {
            let ty = if let Some(name) = &self.tname {
                store.types.get(name)?.clone()
            } else {
                let (item_ref, _) = lookup(self.r#type?)?;
                match &item_ref.get()?.content {
                    Content::Type(ty) => ty.clone(),
                    // the type item has been garbage collected
                    _ => return None,
                }
            };
            let ty = ty.ty()?;
            let identity = live_identity(&ty)?;

            Some(AbsolutePosition {
                r#type: identity,
                index: if self.assoc >= 0 { ty.len } else { 0 },
                assoc: self.assoc,
            })
        }
    }
}

/// The identity of a type that is still part of the document: `None` when its
/// item has been deleted (Yjs would still resolve into it) or when it has no
/// identity at all.
fn live_identity(ty: &YType) -> Option<TypeIdentity> {
    if let Some(item) = ty.item.get() {
        (!item.deleted()).then_some(TypeIdentity::Item(item.id))
    } else {
        ty.root_name.clone().map(TypeIdentity::Root)
    }
}

impl<W: CrdtWriter> CrdtWrite<W> for RelativePosition {
    /// Yjs `writeRelativePosition`.
    fn write(&self, writer: &mut W) -> JwstCodecResult {
        if let Some(item) = &self.item {
            writer.write_var_u64(0)?;
            writer.write_item_id(item)?;
        } else if let Some(tname) = &self.tname {
            writer.write_var_u64(1)?;
            writer.write_var_string(tname)?;
        } else if let Some(ty) = &self.r#type {
            writer.write_var_u64(2)?;
            writer.write_item_id(ty)?;
        } else {
            return Err(JwstCodecError::Unexpected);
        }
        writer.write_var_i64(self.assoc)
    }
}

impl<R: CrdtReader> CrdtRead<R> for RelativePosition {
    /// Yjs `readRelativePosition`; a missing `assoc` reads as 0.
    fn read(reader: &mut R) -> JwstCodecResult<Self> {
        let mut rpos = Self {
            r#type: None,
            tname: None,
            item: None,
            assoc: 0,
        };
        match reader.read_var_u64()? {
            0 => rpos.item = Some(reader.read_item_id()?),
            1 => rpos.tname = Some(reader.read_var_string()?),
            2 => rpos.r#type = Some(reader.read_item_id()?),
            _ => return Err(JwstCodecError::UnexpectedType("relative position kind 0, 1 or 2")),
        }
        if !reader.is_empty() {
            rpos.assoc = reader.read_var_i64()?;
        }
        Ok(rpos)
    }
}

/// `assoc` is a JS number in Yjs: positions outside the safe integer range
/// cannot be represented without changing their value. The varint codec
/// rejects them in the binary form; this checks the values y-octo is given
/// otherwise (creation arguments and the JSON form).
fn check_assoc(assoc: i64) -> JwstCodecResult<i64> {
    if assoc.unsigned_abs() > MAX_SAFE_INTEGER as u64 {
        return Err(JwstCodecError::UnexpectedType("assoc within the JS safe integer range"));
    }
    Ok(assoc)
}

/// The shape of Yjs `relativePositionToJSON` /
/// `createRelativePositionFromJSON`.
#[derive(Serialize, Deserialize)]
struct RelativePositionJson {
    #[serde(rename = "type", default, skip_serializing_if = "Option::is_none")]
    ty: Option<IdJson>,
    // Yjs leaves out an empty name too
    #[serde(default, skip_serializing_if = "is_none_or_empty")]
    tname: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    item: Option<IdJson>,
    #[serde(default)]
    assoc: Option<i64>,
}

#[derive(Serialize, Deserialize)]
struct IdJson {
    client: u64,
    clock: u64,
}

fn is_none_or_empty(s: &Option<String>) -> bool {
    s.as_deref().is_none_or(str::is_empty)
}

impl TryFrom<RelativePositionJson> for RelativePosition {
    type Error = JwstCodecError;

    fn try_from(json: RelativePositionJson) -> JwstCodecResult<Self> {
        Ok(Self {
            r#type: json.ty.map(|id| Id::new(id.client, id.clock)),
            tname: json.tname,
            item: json.item.map(|id| Id::new(id.client, id.clock)),
            assoc: check_assoc(json.assoc.unwrap_or(0))?,
        })
    }
}

impl From<RelativePosition> for RelativePositionJson {
    fn from(rpos: RelativePosition) -> Self {
        let id = |id: Id| IdJson {
            client: id.client,
            clock: id.clock,
        };
        Self {
            ty: rpos.r#type.map(id),
            tname: rpos.tname,
            item: rpos.item.map(id),
            assoc: Some(rpos.assoc),
        }
    }
}

macro_rules! impl_relative_position {
    ($ty: ident, $unit: literal) => {
        impl $ty {
            #[doc = concat!(
                "Yjs `createRelativePositionFromTypeIndex`: the position at `index` (in ",
                $unit,
                "), associated with the content after it when `assoc >= 0` and with the content before it ",
                "when `assoc < 0`. Fails when `index` is past the end, `assoc` is outside the JS safe integer range, or ",
                "the type is not part of the document yet."
            )]
            pub fn relative_position(&self, index: u64, assoc: i64) -> JwstCodecResult<RelativePosition> {
                let (_store, ty) = self.0.read().ok_or(JwstCodecError::DocReleased)?;
                RelativePosition::from_type_index(&ty, index, assoc)
            }
        }
    };
}

impl_relative_position!(Text, "UTF-16 code units");
impl_relative_position!(Array, "elements");

impl Doc {
    /// Yjs `createAbsolutePositionFromRelativePosition`.
    ///
    /// With `follow_undone_deletions`, a position on content that was deleted
    /// and recreated by a local redo resolves into the recreated content. Other
    /// peers do not know about local redos, so pass `false` when the result has
    /// to agree across peers.
    ///
    /// Returns `None` when the position points to content this document has
    /// not received, to a type that is gone (garbage collected, deleted, or a
    /// root name the document does not have), or names nothing.
    pub fn resolve_relative_position(
        &self,
        rpos: &RelativePosition,
        follow_undone_deletions: bool,
    ) -> Option<AbsolutePosition> {
        let store = self.store.read().unwrap();
        rpos.resolve(&store, follow_undone_deletions)
    }
}
