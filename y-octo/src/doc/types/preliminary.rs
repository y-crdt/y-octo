use super::*;

impl YType {
    /// A preliminary subtree has no document identities, even when its local
    /// staging engine has already linked nested types together.
    pub(crate) fn is_preliminary(&self) -> bool {
        !self.published
    }

    pub(super) fn id(&self, items: &ItemSpace) -> Option<Id> {
        if self.is_preliminary() {
            None
        } else if let Carrier::Live(item) = self.carrier(items) {
            Some(item.id)
        } else {
            None
        }
    }
}

impl TypeArena {
    /// The root of the preliminary subtree `id` is edited in, `None` for a
    /// type of the document itself. The caller holds the document lock. A
    /// deleted or collected type is retired, not a fresh preliminary type.
    pub(crate) fn preliminary_root(&self, id: TypeIdx) -> JwstCodecResult<Option<TypeIdx>> {
        let mut current = id;
        loop {
            let ty = self.get(current).ok_or(JwstCodecError::DocReleased)?;
            let carrier = ty.carrier(&self.items);
            if ty.published {
                if ty.root_name().is_none() && !matches!(carrier, Carrier::Live(item) if !item.deleted()) {
                    return Err(JwstCodecError::InvalidParent);
                }
                return Ok(None);
            }
            match carrier {
                Carrier::Unset => return Ok(Some(current)),
                Carrier::Live(item) if !item.deleted() => {
                    current = ty.parent_type.ok_or(JwstCodecError::InvalidParent)?;
                }
                Carrier::Live(_) | Carrier::Retired => return Err(JwstCodecError::InvalidParent),
            }
        }
    }
}

// Only current contents cross the preliminary boundary. Staging item IDs,
// deleted items and their history are deliberately not published.
// Stored as a flat indexed tree so capture, integration, and drop stay
// iterative and cannot overflow the stack on deeply nested preliminary types.
pub(in crate::doc) struct PreparedType {
    nodes: Vec<PreparedNode>,
}
struct PreparedNode {
    ty: TypeIdx,
    entries: Vec<(Option<SmolStr>, PreparedValue)>,
}
enum PreparedValue {
    Content(Content),
    Type(usize),
}
impl PreparedType {
    fn capture(types: &TypeArena, root: TypeIdx, mut clock: u64) -> JwstCodecResult<Self> {
        // The new carrier and every visible entry coexist with the quarantined
        // staging slots.
        let mut slots = 1usize;
        let mut nodes = vec![PreparedNode {
            ty: root,
            entries: Vec::new(),
        }];
        let mut stack = vec![0usize];
        while let Some(node_idx) = stack.pop() {
            let ty = &types[nodes[node_idx].ty];
            let mut entries = Vec::new();
            let mut prepare = |item: &Item| -> JwstCodecResult<PreparedValue> {
                clock = clock
                    .checked_add(item.len())
                    .ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
                Ok(match &item.content {
                    Content::Type(child_ty) => {
                        let child_idx = nodes.len();
                        nodes.push(PreparedNode {
                            ty: *child_ty,
                            entries: Vec::new(),
                        });
                        stack.push(child_idx);
                        PreparedValue::Type(child_idx)
                    }
                    content => PreparedValue::Content(content.clone()),
                })
            };
            for item in ListIterator::new(&types.items, ty) {
                entries.push((None, prepare(item)?));
            }
            let mut map: Vec<_> = map_entries(&types.items, ty).collect();
            map.sort_unstable_by_key(|(key, _)| *key);
            for (key, item) in map {
                entries.push((Some(SmolStr::new(key)), prepare(item)?));
            }
            slots = slots.saturating_add(entries.len());
            nodes[node_idx].entries = entries;
        }
        types.items.check_capacity(slots)?;
        Ok(Self { nodes })
    }
    fn integrate(mut self, store: &mut DocStore) -> JwstCodecResult {
        struct Frame {
            ty: TypeIdx,
            entries: std::vec::IntoIter<(Option<SmolStr>, PreparedValue)>,
            left: ItemRef,
        }

        // Public attachment checks admitted this acyclic tree before staging
        // was taken. Every call below uses offset 0 and an explicit parent, so
        // no split/remote ancestry error path is entered. create_item
        // allocates the store's current clock immediately before add_node
        // under the same document write lock: a clock mismatch is an internal
        // invariant failure.
        fn init_frame(types: &mut TypeArena, nodes: &mut [PreparedNode], idx: usize) -> Frame {
            let node = &mut nodes[idx];
            let ty = &mut types[node.ty];
            ty.start = None;
            ty.clear_map();
            ty.len = 0;
            if let Some(markers) = &mut ty.markers {
                markers.clear();
            }
            Frame {
                ty: node.ty,
                entries: std::mem::take(&mut node.entries).into_iter(),
                left: None,
            }
        }

        let mut stack = vec![init_frame(&mut store.type_arena, &mut self.nodes, 0)];
        while let Some(frame) = stack.last_mut() {
            let Some((key, value)) = frame.entries.next() else {
                stack.pop();
                continue;
            };
            let (content, child_idx) = match value {
                PreparedValue::Content(content) => (content, None),
                PreparedValue::Type(idx) => (Content::Type(self.nodes[idx].ty), Some(idx)),
            };
            let item = store.create_item(
                content,
                if key.is_some() { None } else { frame.left },
                None,
                Some(frame.ty),
                key.clone(),
            );
            let item_ref = store.integrate_item(item, 0, Some(frame.ty))?;
            if key.is_none() {
                frame.left = item_ref;
            }
            if let Some(child_idx) = child_idx {
                stack.push(init_frame(&mut store.type_arena, &mut self.nodes, child_idx));
            }
        }
        Ok(())
    }
}

impl DocStore {
    pub(in crate::doc) fn prepare_preliminary(
        &self,
        ty: TypeIdx,
        carrier: Id,
        len: u64,
    ) -> JwstCodecResult<PreparedType> {
        let start = if carrier.client == self.client() {
            carrier.clock.checked_add(len)
        } else {
            Some(self.get_state(self.client()))
        };
        let clock = start.ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
        PreparedType::capture(&self.type_arena, ty, clock)
    }
}

impl PreparedType {
    pub(in crate::doc) fn mount(self, store: &mut DocStore) -> JwstCodecResult {
        let root = self.nodes[0].ty;
        let staging = store.type_arena[root]
            .preliminary
            .take()
            .expect("prepared staging store");
        let visible: HashSet<_> = self.nodes.iter().map(|node| node.ty).collect();
        // Mounting rebuilds visible children only. Retire all old owners
        // and clear staging links, including those of removed children
        // whose public type handles can still exist.
        for (&client, blocks) in &staging.items {
            for node in blocks.nodes(client) {
                if let Some(idx) = node.as_item() {
                    if let Some(Item {
                        content: Content::Type(child),
                        ..
                    }) = store.type_arena.items.get(idx)
                    {
                        let child = *child;
                        if store.type_arena[child].carrier_ref() == Some(idx) {
                            let ty = &mut store.type_arena[child];
                            if visible.contains(&child) {
                                ty.item = None;
                                ty.parent_type = None;
                            } else {
                                ty.retire();
                            }
                            ty.start = None;
                            ty.clear_map();
                            ty.len = 0;
                        }
                    }
                    store.type_arena.items.retire(idx);
                }
            }
        }
        self.integrate(store)
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
