use super::*;

impl YType {
    /// A preliminary subtree has no document identities, even when its local
    /// staging engine has already linked nested types together.
    pub(crate) fn is_preliminary(&self) -> bool {
        !self.published
    }

    pub(super) fn id(&self) -> Option<Id> {
        if self.is_preliminary() {
            None
        } else {
            self.item.get().map(|item| item.id)
        }
    }
}

impl YTypeRef {
    /// The caller holds the document lock. A deleted or collected type is
    /// retired, not a fresh preliminary type.
    pub(crate) fn preliminary_root(&self) -> JwstCodecResult<Option<Self>> {
        let mut current = self;
        loop {
            let ty = current.ty().ok_or(JwstCodecError::DocReleased)?;
            if ty.published {
                if ty.root_name.is_none() && ty.item.get().is_none_or(|item| item.deleted()) {
                    return Err(JwstCodecError::InvalidParent);
                }
                return Ok(None);
            }
            if ty.item.is_unset() {
                return Ok(Some(current.clone()));
            }
            let item = ty.item.get().ok_or(JwstCodecError::InvalidParent)?;
            if item.deleted() {
                return Err(JwstCodecError::InvalidParent);
            }
            current = match &item.parent {
                Some(Parent::Type(parent)) => parent,
                _ => return Err(JwstCodecError::InvalidParent),
            };
        }
    }
}

// Only current contents cross the preliminary boundary. Staging item IDs,
// deleted items and their history are deliberately not published.
struct PreparedType {
    ty: YTypeRef,
    entries: Vec<(Option<SmolStr>, PreparedValue)>,
}
enum PreparedValue {
    Content(Content),
    Type(PreparedType),
}
impl PreparedValue {
    fn capture(content: &Content) -> Self {
        match content {
            Content::Type(ty) => Self::Type(PreparedType::capture(ty)),
            content => Self::Content(content.clone()),
        }
    }
    fn content(&self) -> Content {
        match self {
            Self::Content(content) => content.clone(),
            Self::Type(ty) => Content::Type(ty.ty.clone()),
        }
    }
}
impl PreparedType {
    fn capture(ty_ref: &YTypeRef) -> Self {
        let ty = ty_ref.ty().unwrap();
        let mut entries: Vec<_> = ListIterator::new(ty)
            .map(|item| (None, PreparedValue::capture(&item.content)))
            .collect();
        let mut map: Vec<_> = map_entries(ty).collect();
        map.sort_unstable_by_key(|(key, _)| *key);
        entries.extend(
            map.into_iter()
                .map(|(key, item)| (Some(SmolStr::new(key)), PreparedValue::capture(&item.content))),
        );
        Self {
            ty: ty_ref.clone(),
            entries,
        }
    }
    fn integrate(self, store: &mut DocStore) -> JwstCodecResult {
        // Public attachment checks admitted this acyclic tree before staging
        // was taken. Every call below uses offset 0 and an explicit parent, so
        // no split/remote ancestry error path is entered. create_item allocates
        // the store's current clock immediately before add_node under the same
        // document write lock: a clock mismatch is an internal invariant
        // failure. SAFETY: the document write lock protects every type in this
        // tree; the public insertion checks exclude aliases with the target
        // parent.
        let mut ty = unsafe { self.ty.ty_mut() }.unwrap();
        ty.start = Somr::none();
        ty.map.clear();
        ty.len = 0;
        if ty.markers.is_some() {
            ty.markers = Some(MarkerList::new());
        }
        let mut left = Somr::none();
        for (key, value) in self.entries {
            let item = store.create_item(
                value.content(),
                if key.is_some() { Somr::none() } else { left.clone() },
                Somr::none(),
                Some(Parent::Type(self.ty.clone())),
                key.clone(),
            );
            let item_ref = item.clone();
            store.integrate(Node::Item(item), 0, Some(&mut ty))?;
            if key.is_none() {
                left = item_ref;
            }
            if let PreparedValue::Type(child) = value {
                child.integrate(store)?;
            }
        }
        Ok(())
    }
}

impl DocStore {
    /// Called only after the type's parent item entered this store, under the
    /// document write lock. The private owners live until rebuilding finishes.
    pub(crate) fn integrate_preliminary(&mut self, ty: &YTypeRef) -> JwstCodecResult {
        // SAFETY: the document write lock is held; no reference to the newly
        // inserted type's data is borrowed by the insertion caller.
        let staging = unsafe { ty.ty_mut() }.unwrap().preliminary.take();
        if let Some(_staging) = staging {
            PreparedType::capture(ty).integrate(self)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{Any, Doc, Id, StateVector, TextAttributes, TextDeltaOp, TextInsert};

    // Refcount operations in a complete staging/mount/reopen scenario exceed
    // loom's default 1000 branches even without a competing thread.
    fn model(body: fn()) {
        #[cfg(loom)]
        {
            let mut builder = loom::model::Builder::new();
            builder.max_branches = 1 << 20;
            builder.check(move || {
                loom::thread::Builder::new()
                    .stack_size(128 << 10)
                    .spawn(body)
                    .unwrap()
                    .join()
                    .unwrap();
            });
        }
        #[cfg(not(loom))]
        body();
    }

    #[test]
    fn preliminary_edits_publish_only_after_mount() {
        model(|| {
            let doc = Doc::with_client(101);
            let mut root = doc.get_or_create_array("array").unwrap();
            let before = doc.encode_update_v1().unwrap();
            let mut child = doc.create_array().unwrap();
            child.push(1).unwrap();
            child.push(2).unwrap();
            child.remove(0, 1).unwrap();
            assert_eq!(child.len(), 1);
            assert_eq!(child.id(), None);
            assert!(child.relative_position(0, 0).is_err());
            assert_eq!(doc.get_state_vector().get(&101), 0);
            assert_eq!(doc.encode_update_v1().unwrap(), before);
            root.push(child.clone()).unwrap();
            assert_eq!(child.id(), Some(Id::new(101, 0)));
            assert_eq!(doc.get_state_vector().get(&101), 2);
            child.push(3).unwrap();
            let mut peer = Doc::with_client(202);
            peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
                .unwrap();
            assert_eq!(
                serde_json::to_value(peer.get_or_create_array("array").unwrap()).unwrap(),
                serde_json::json!([[2, 3]])
            );
            assert!(!peer.has_pending_updates());
            assert_eq!(peer.get_state_vector(), doc.get_state_vector());
        });
    }

    #[test]
    fn preliminary_nested_handles_and_formats_survive_mount() {
        model(|| {
            let doc = Doc::with_client(101);
            let mut outer = doc.create_map().unwrap();
            let mut array = doc.create_array().unwrap();
            let mut text = doc.create_text().unwrap();
            let attrs = TextAttributes::from([("bold".into(), Any::True)]);
            text.apply_delta(&[TextDeltaOp::Insert {
                insert: TextInsert::Text("A😀Z".into()),
                format: Some(attrs),
            }])
            .unwrap();
            text.remove(1, 2).unwrap();
            let delta = text.to_delta();
            array.push(text.clone()).unwrap();
            outer.insert("array".into(), array.clone()).unwrap();
            outer.insert("removed".into(), 99).unwrap();
            outer.remove("removed");
            assert_eq!(array.id(), None);
            assert!(text.identity_runs().is_err());
            // Further edits through a nested handle use the whole subtree's
            // staging engine.
            array.push(7).unwrap();
            assert!(doc.get_state_vector().is_empty());
            doc.get_or_create_map("map")
                .unwrap()
                .insert("child".into(), outer.clone())
                .unwrap();
            assert_eq!(outer.id(), Some(Id::new(101, 0)));
            assert_eq!(array.id(), Some(Id::new(101, 1)));
            assert_eq!(text.to_delta(), delta);
            assert!(text.identity_runs().is_ok());
            assert_eq!(
                serde_json::to_value(outer.clone()).unwrap(),
                serde_json::json!({"array":["AZ",7]})
            );
            text.insert(2, "!").unwrap();
            let mut peer = Doc::with_client(202);
            peer.apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
                .unwrap();
            assert_eq!(
                serde_json::to_value(peer.get_or_create_map("map").unwrap()).unwrap(),
                serde_json::json!({"child":{"array":["AZ!",7]}})
            );
            assert_eq!(peer.get_state_vector(), doc.get_state_vector());
        });
    }

    #[test]
    fn preliminary_failed_mount_preserves_contents_and_handles() {
        model(|| {
            let doc = Doc::with_client(101);
            let mut root = doc.get_or_create_array("array").unwrap();
            let mut child = doc.create_array().unwrap();
            child.push(1).unwrap();
            let before = doc.encode_update_v1().unwrap();
            assert!(root.insert(1, child.clone()).is_err());
            let foreign = Doc::with_client(202);
            assert!(
                foreign
                    .get_or_create_array("other")
                    .unwrap()
                    .push(child.clone())
                    .is_err()
            );
            assert!(child.push(child.clone()).is_err());
            assert_eq!(child.len(), 1);
            assert_eq!(child.id(), None);
            assert_eq!(doc.encode_update_v1().unwrap(), before);
            child.push(2).unwrap();
            root.push(child.clone()).unwrap();
            let attached = doc.encode_update_v1().unwrap();
            assert!(root.push(child.clone()).is_err());
            assert_eq!(doc.encode_update_v1().unwrap(), attached);
            assert_eq!(serde_json::to_value(child.clone()).unwrap(), serde_json::json!([1, 2]));
            root.remove(0, 1).unwrap();
            doc.gc().unwrap();
            assert!(root.push(child.clone()).is_err());
            assert!(child.push(3).is_err());
        });
    }

    #[test]
    fn preliminary_mount_uses_current_client_without_renumbering_published_items() {
        model(|| {
            let mut doc = Doc::with_client(101);
            let mut text = doc.get_or_create_text("text").unwrap();
            text.insert(0, "A").unwrap();
            let sv = doc.get_state_vector();
            let ids = text.identity_runs().unwrap();
            let rpos = text.relative_position(0, 0).unwrap();
            let mut child = doc.create_map().unwrap();
            child.insert("x".into(), 7).unwrap();
            assert_eq!(doc.get_state_vector(), sv);
            doc.set_client(303);
            doc.get_or_create_array("array").unwrap().push(child.clone()).unwrap();
            assert_eq!(child.id(), Some(Id::new(303, 0)));
            assert_eq!(text.identity_runs().unwrap(), ids);
            assert_eq!(text.relative_position(0, 0).unwrap(), rpos);
            assert_eq!(doc.get_state_vector(), StateVector::from([(101, 1), (303, 2)]));
        });
    }
}
