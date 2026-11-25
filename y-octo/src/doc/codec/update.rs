use std::{
    cmp::Reverse,
    collections::{BTreeMap, VecDeque},
    ops::Range,
};

use y_octo_core::{
    order_range::ClockRange,
    pending::{LocalStep, StructStep, check_local_readiness, classify_ready_step, split_delete_range},
    yata_store::IdCore,
};

use super::*;
use crate::doc::{OrderRange, StateVector, codec::decoder::v1 as decoder, find_missing_dependency};

#[derive(Debug, Default, Clone)]
pub struct Update {
    pub(crate) structs: ClientMap<VecDeque<WireStruct>>,
    pub(crate) delete_set: DeleteSet,

    /// all unapplicable items that we can't integrate into doc
    /// any item with inconsistent id clock or missing dependency will be put
    /// here
    pub(crate) pending_structs: ClientMap<VecDeque<WireStruct>>,
    /// missing state vector after applying updates
    pub(crate) missing_state: StateVector,
    /// all unapplicable delete set
    pub(crate) pending_delete_set: DeleteSet,
}

impl<'a> CrdtRead<RawDecoder<'a>> for Update {
    /// Reads the rest of `decoder` with `Any` values nested at most
    /// [Any::DEFAULT_MAX_DEPTH] levels.
    fn read(decoder: &mut RawDecoder<'a>) -> JwstCodecResult<Self> {
        Self::read_with_max_any_depth(decoder, Any::DEFAULT_MAX_DEPTH)
    }
}

impl Update {
    fn read_with_max_any_depth(decoder: &mut RawDecoder<'_>, max_any_depth: usize) -> JwstCodecResult<Self> {
        let limits = decoder::DecodeLimits {
            max_any_depth: max_any_depth.min(Any::MAX_CONFIGURABLE_DEPTH),
            ..decoder::DecodeLimits::UPDATE
        };
        let update =
            decoder::decode(decoder.rest_ref(), OwnedUpdateSink::default(), limits).map_err(|error| match error {
                decoder::Error::Codec(error) => error,
                decoder::Error::Resource(name) => JwstCodecError::IncompleteDocument(format!("{name} exceeds limit")),
            })?;
        decoder.consume_rest();
        Ok(update)
    }
}

#[derive(Default)]
struct OwnedUpdateSink {
    update: Update,
    deletes: Vec<(Client, Range<u64>)>,
    json: Vec<Option<String>>,
    content_any: Vec<Any>,
    any_stack: Vec<AnyFrame>,
    any_root: Option<Any>,
}

enum AnyFrame {
    Object(HashMap<String, Any>, Option<String>),
    Array(Vec<Any>),
}

impl OwnedUpdateSink {
    fn push_any(&mut self, value: Any) -> decoder::Result<()> {
        match self.any_stack.last_mut() {
            Some(AnyFrame::Array(values)) => values.push(value),
            Some(AnyFrame::Object(values, key)) => {
                let key = key.take().ok_or_else(|| {
                    decoder::Error::Codec(JwstCodecError::IncompleteDocument(
                        "Any object value without key".into(),
                    ))
                })?;
                values.insert(key, value);
            }
            None if self.any_root.is_none() => self.any_root = Some(value),
            None => {
                return Err(decoder::Error::Codec(JwstCodecError::IncompleteDocument(
                    "multiple Any roots".into(),
                )));
            }
        }
        Ok(())
    }
}

impl<'a> decoder::Sink<'a> for OwnedUpdateSink {
    type Output = Update;
    type Content = WireContent;
    type Any = Any;

    fn begin_client(&mut self, client: u64, count: usize) -> decoder::Result<()> {
        self.update
            .structs
            .insert(client, VecDeque::with_capacity(count.min(HASHMAP_SAFE_CAPACITY)));
        Ok(())
    }

    fn gc(&mut self, id: Id, len: u64) -> decoder::Result<()> {
        self.update
            .structs
            .get_mut(&id.client)
            .unwrap()
            .push_back(WireStruct::Gc { id, len });
        Ok(())
    }

    fn skip(&mut self, id: Id, len: u64) -> decoder::Result<()> {
        self.update
            .structs
            .get_mut(&id.client)
            .unwrap()
            .push_back(WireStruct::Skip { id, len });
        Ok(())
    }

    fn item(&mut self, id: Id, len: u64, meta: decoder::ItemMeta<'a>, content: WireContent) -> decoder::Result<()> {
        let parent = match meta.parent {
            decoder::WireParent::Root(name) => Some(WireParent::Root(SmolStr::new(name.value))),
            decoder::WireParent::Item(id) => Some(WireParent::Item(id)),
            decoder::WireParent::Inherit => None,
        };
        let item = Box::new(WireItem {
            id,
            len,
            origin_left_id: meta.origin_left,
            origin_right_id: meta.origin_right,
            parent,
            parent_sub: meta.parent_sub.map(|value| SmolStr::new(value.value)),
            flags: content.wire_flags(),
            content,
        });
        self.update
            .structs
            .get_mut(&id.client)
            .unwrap()
            .push_back(WireStruct::Item(item));
        Ok(())
    }

    fn content_atom(&mut self, atom: decoder::ContentAtom<'a>) -> decoder::Result<WireContent> {
        Ok(match atom {
            decoder::ContentAtom::Deleted(len) => WireContent::Deleted(len),
            decoder::ContentAtom::Binary(value) => WireContent::Binary(value.value.to_vec()),
            decoder::ContentAtom::String(value) => WireContent::String(value.value.to_string()),
            decoder::ContentAtom::Embed(value) => WireContent::Embed(Box::new(
                serde_json::from_str(value.value)
                    .map_err(|_| decoder::Error::Codec(JwstCodecError::DamagedDocumentJson))?,
            )),
            decoder::ContentAtom::Format { key, value } => WireContent::Format {
                key: key.value.to_string(),
                value: Box::new(
                    serde_json::from_str(value.value)
                        .map_err(|_| decoder::Error::Codec(JwstCodecError::DamagedDocumentJson))?,
                ),
            },
            decoder::ContentAtom::Type { kind, tag } => WireContent::Type {
                kind: kind.into(),
                name: tag.map(|value| value.value.to_string()),
            },
        })
    }

    fn json_start(&mut self, count: usize) -> decoder::Result<()> {
        self.json = Vec::with_capacity(count.min(HASHMAP_SAFE_CAPACITY));
        Ok(())
    }

    fn json_value(&mut self, value: decoder::WireStr<'a>) -> decoder::Result<()> {
        self.json
            .push((value.value != "undefined").then(|| value.value.to_string()));
        Ok(())
    }

    fn json_finish(&mut self) -> decoder::Result<WireContent> {
        Ok(WireContent::Json(std::mem::take(&mut self.json)))
    }

    fn any_content_start(&mut self, count: usize) -> decoder::Result<()> {
        self.content_any = Vec::with_capacity(count.min(HASHMAP_SAFE_CAPACITY));
        Ok(())
    }

    fn any_content_value(&mut self, value: Any) -> decoder::Result<()> {
        self.content_any.push(value);
        Ok(())
    }

    fn any_content_finish(&mut self) -> decoder::Result<WireContent> {
        Ok(WireContent::Any(std::mem::take(&mut self.content_any)))
    }

    fn doc_content(&mut self, guid: decoder::WireStr<'a>, options: Any) -> decoder::Result<WireContent> {
        Ok(WireContent::Doc {
            guid: guid.value.to_string(),
            opts: Box::new(options),
        })
    }

    fn any_start(&mut self) -> decoder::Result<()> {
        self.any_stack.clear();
        self.any_root = None;
        Ok(())
    }

    fn any_event(&mut self, event: decoder::AnyEvent<'a>) -> decoder::Result<()> {
        match event {
            decoder::AnyEvent::Undefined => self.push_any(Any::Undefined),
            decoder::AnyEvent::Null => self.push_any(Any::Null),
            decoder::AnyEvent::Integer(value) => self.push_any(Any::Integer(value)),
            decoder::AnyEvent::Float32(value) => self.push_any(Any::Float32(value.into())),
            decoder::AnyEvent::Float64(value) => self.push_any(Any::Float64(value.into())),
            decoder::AnyEvent::BigInt64(value) => self.push_any(Any::BigInt64(value)),
            decoder::AnyEvent::False => self.push_any(Any::False),
            decoder::AnyEvent::True => self.push_any(Any::True),
            decoder::AnyEvent::String(value) => self.push_any(Any::String(value.value.to_string())),
            decoder::AnyEvent::Binary(value) => self.push_any(Any::Binary(value.value.to_vec())),
            decoder::AnyEvent::BeginObject(count) => {
                self.any_stack.push(AnyFrame::Object(
                    HashMap::with_capacity(count.min(HASHMAP_SAFE_CAPACITY)),
                    None,
                ));
                Ok(())
            }
            decoder::AnyEvent::ObjectKey(value) => match self.any_stack.last_mut() {
                Some(AnyFrame::Object(_, key)) => {
                    *key = Some(value.value.to_string());
                    Ok(())
                }
                _ => Err(decoder::Error::Codec(JwstCodecError::IncompleteDocument(
                    "Any object key outside object".into(),
                ))),
            },
            decoder::AnyEvent::BeginArray(count) => {
                self.any_stack
                    .push(AnyFrame::Array(Vec::with_capacity(count.min(HASHMAP_SAFE_CAPACITY))));
                Ok(())
            }
            decoder::AnyEvent::EndContainer => {
                let frame = self.any_stack.pop().ok_or_else(|| {
                    decoder::Error::Codec(JwstCodecError::IncompleteDocument(
                        "Any container end without start".into(),
                    ))
                })?;
                let value = match frame {
                    AnyFrame::Object(values, None) => Any::Object(Box::new(values)),
                    AnyFrame::Object(_, Some(_)) => {
                        return Err(decoder::Error::Codec(JwstCodecError::IncompleteDocument(
                            "Any object key without value".into(),
                        )));
                    }
                    AnyFrame::Array(values) => Any::Array(values),
                };
                self.push_any(value)
            }
        }
    }

    fn any_finish(&mut self, _range: Range<usize>) -> decoder::Result<Any> {
        if !self.any_stack.is_empty() {
            return Err(decoder::Error::Codec(JwstCodecError::IncompleteDocument(
                "unterminated Any container".into(),
            )));
        }
        self.any_root
            .take()
            .ok_or_else(|| decoder::Error::Codec(JwstCodecError::IncompleteDocument("missing Any value".into())))
    }

    fn delete_range(&mut self, client: u64, range: Range<u64>) -> decoder::Result<()> {
        self.deletes.push((client, range));
        Ok(())
    }

    fn finish(mut self) -> decoder::Result<Update> {
        self.update.delete_set = DeleteSet::from_flat_ranges(std::mem::take(&mut self.deletes));
        for structs in self.update.structs.values_mut() {
            structs.shrink_to_fit();
        }
        self.update.structs.shrink_to_fit();
        Ok(self.update)
    }
}

impl<W: CrdtWriter> CrdtWrite<W> for Update {
    fn write(&self, encoder: &mut W) -> JwstCodecResult {
        let mut clients = self.structs.keys().copied().collect::<Vec<_>>();

        // Descending
        clients.sort_by(|a, b| b.cmp(a));

        // Skip zero-length structs and clients left empty by that: they carry
        // neither content nor deletions and apply() just drops them again, so
        // emitting them would produce non-canonical updates.
        let entries = clients
            .into_iter()
            .filter_map(|client| {
                let structs = self.structs.get(&client).unwrap();
                let structs = structs.iter().filter(|s| s.len() > 0).collect::<Vec<_>>();
                (!structs.is_empty()).then_some((client, structs))
            })
            .collect::<Vec<_>>();

        encoder.write_var_u64(entries.len() as u64)?;

        for (client, structs) in entries {
            encoder.write_var_u64(structs.len() as u64)?;
            encoder.write_var_u64(client)?;
            encoder.write_var_u64(structs.first().map(|s| s.clock()).unwrap_or(0))?;

            for struct_info in structs {
                struct_info.write(encoder)?;
            }
        }

        self.delete_set.write(encoder)?;

        Ok(())
    }
}

impl Update {
    /// Decodes a Yjs Update V1, rejecting `Any` values nested deeper than
    /// [Any::DEFAULT_MAX_DEPTH] with [JwstCodecError::IncompleteDocument].
    ///
    /// Yjs puts no limit on `Any` nesting; the default limit keeps untrusted
    /// input from building values whose recursive clone, comparison and drop
    /// use unbounded stack. Use [Update::decode_v1_with_max_any_depth] for
    /// trusted updates nested deeper.
    pub fn decode_v1<T: AsRef<[u8]>>(buffer: T) -> JwstCodecResult<Update> {
        Self::decode_v1_with_max_any_depth(buffer, Any::DEFAULT_MAX_DEPTH)
    }

    /// Decodes a Yjs Update V1 whose `Any` values nest at most
    /// `max_any_depth` levels, where a limit above
    /// [Any::MAX_CONFIGURABLE_DEPTH] acts as that limit and 0 accepts scalars
    /// and empty containers only. Deeper values fail with
    /// [JwstCodecError::IncompleteDocument].
    ///
    /// Apply the result with [crate::Doc::apply_update] or
    /// [crate::Doc::apply_update_with_origin] to accept trusted updates nested
    /// deeper than [crate::Doc::apply_update_from_binary_v1] allows.
    ///
    /// ```
    /// use y_octo::{Any, DocOptions, Update};
    ///
    /// let mut deep = Any::Null;
    /// for _ in 0..200 {
    ///     deep = Any::Array(vec![deep]);
    /// }
    /// let source = DocOptions::from_identity(1, "deep".into()).build();
    /// let mut map = source.get_or_create_map("root").unwrap();
    /// // the entry's `ContentAny` holds the single value `deep`
    /// map.insert("deep".into(), Any::Array(vec![deep.clone()])).unwrap();
    /// let bytes = source.encode_update_v1().unwrap();
    ///
    /// let mut doc = DocOptions::from_identity(2, "deep".into()).build();
    /// assert!(doc.apply_update_from_binary_v1(&bytes).is_err());
    /// doc.apply_update(Update::decode_v1_with_max_any_depth(&bytes, 256).unwrap()).unwrap();
    /// let root = doc.get_or_create_map("root").unwrap();
    /// assert_eq!(root.get("deep").unwrap().to_any(), Some(deep));
    /// ```
    pub fn decode_v1_with_max_any_depth<T: AsRef<[u8]>>(buffer: T, max_any_depth: usize) -> JwstCodecResult<Update> {
        Self::read_with_max_any_depth(&mut RawDecoder::new(buffer.as_ref()), max_any_depth)
    }

    pub fn encode_v1(&self) -> JwstCodecResult<Vec<u8>> {
        let mut encoder = RawEncoder::default();
        self.write(&mut encoder)?;
        Ok(encoder.into_inner())
    }

    pub(crate) fn iter(&mut self, state: StateVector) -> UpdateIterator<'_> {
        UpdateIterator::new(self, state)
    }

    pub fn delete_set_iter(&mut self, state: StateVector) -> DeleteSetIterator<'_> {
        DeleteSetIterator::new(self, state)
    }

    // take all pending structs and delete set to [self] update struct
    pub fn drain_pending_state(&mut self) {
        debug_assert!(self.is_empty());

        std::mem::swap(&mut self.pending_structs, &mut self.structs);
        std::mem::swap(&mut self.pending_delete_set, &mut self.delete_set);
    }

    pub fn merge<I: IntoIterator<Item = Update>>(updates: I) -> Update {
        let mut merged = Update::default();

        Self::merge_into(&mut merged, updates);

        merged
    }

    /// Union encoded material without integrating or garbage-collecting it.
    /// Overlapping snapshots/tails must cover each client clock only once.
    pub fn merge_into<I: IntoIterator<Item = Update>>(target: &mut Update, updates: I) {
        // Pending material still belongs on the wire even when its dependencies
        // have not arrived; retain deletion ranges and the earliest missing
        // clocks.
        target.delete_set.merge(&std::mem::take(&mut target.pending_delete_set));
        let target_structs = [
            std::mem::take(&mut target.structs),
            std::mem::take(&mut target.pending_structs),
        ];
        let mut sources: BTreeMap<_, VecDeque<_>> = BTreeMap::new();
        for source in target_structs
            .into_iter()
            .chain(updates.into_iter().flat_map(|update| {
                target.delete_set.merge(&update.delete_set);
                target.delete_set.merge(&update.pending_delete_set);
                target.missing_state.merge_with(&update.missing_state);
                [update.structs, update.pending_structs]
            }))
            .map(|structs| {
                let mut clients = structs.into_iter().collect::<Vec<_>>();
                clients.sort_by(|(left, _), (right, _)| right.cmp(left));
                clients
                    .into_iter()
                    .flat_map(|(_, structs)| structs)
                    // Skip denotes an unknown interval, not content that can hide
                    // another source. Rebuild only the gaps left by all real structs.
                    .filter(|node| !node.is_skip() && node.len() > 0)
                    .collect::<VecDeque<_>>()
            })
        {
            if let Some(head) = source.front() {
                sources
                    .entry((Reverse(head.client()), head.clock()))
                    .or_default()
                    .push_back(source);
            }
        }

        while let Some(mut entry) = sources.first_entry() {
            let mut source = entry.get_mut().pop_front().unwrap();
            if entry.get().is_empty() {
                entry.remove();
            }
            'source: {
                let mut node = source.pop_front().unwrap();
                let client = node.client();
                let merged = target.structs.entry(client).or_default();
                if let Some(last) = merged.back() {
                    let end = last.clock() + last.len();
                    let mut covered = false;
                    while node.clock() + node.len() <= end {
                        covered = true;
                        let Some(next) = source.pop_front() else {
                            break 'source;
                        };
                        node = next;
                        if node.client() != client {
                            source.push_front(node);
                            break 'source;
                        }
                    }
                    // After consuming covered nodes, another source may fill
                    // this gap. Compare source heads again before emitting a
                    // Skip.
                    if covered && node.clock() > end {
                        source.push_front(node);
                        break 'source;
                    }
                    if node.clock() > end {
                        merged.push_back(WireStruct::Skip {
                            id: Id::new(client, end),
                            len: node.clock() - end,
                        });
                    } else if node.clock() < end {
                        // V1 infers subsequent clocks from lengths: emit only
                        // the uncovered tail, or overlap would allocate extra
                        // clocks.
                        let offset = end - node.clock();
                        node = node.split_at(offset).unwrap().1;
                    }
                }
                merged.push_back(node);
                // Match Yjs's lazy reader: emit a source's contiguous run
                // before comparing its next head with the other sources again.
                while source.front().is_some_and(|next| {
                    let last = merged.back().unwrap();
                    next.client() == client && next.clock() == last.clock() + last.len()
                }) {
                    merged.push_back(source.pop_front().unwrap());
                }
            }
            // The selected source preceded every remaining source in the last
            // stable ordering, including sources matching its new head.
            if let Some(head) = source.front() {
                sources
                    .entry((Reverse(head.client()), head.clock()))
                    .or_default()
                    .push_front(source);
            }
        }
    }

    pub fn is_content_empty(&self) -> bool {
        self.structs.is_empty()
    }

    pub fn is_empty(&self) -> bool {
        self.structs.is_empty() && self.delete_set.is_empty()
    }

    pub fn is_pending_empty(&self) -> bool {
        self.pending_structs.is_empty() && self.pending_delete_set.is_empty()
    }
}

pub(crate) struct UpdateIterator<'a> {
    update: &'a mut Update,

    // --- local iterator state ---
    /// current state vector from store
    state: StateVector,
    /// all client ids sorted ascending
    client_ids: Vec<Client>,
    /// current id of client of the updates we're processing
    cur_client_id: Option<Client>,
    /// stack of previous iterating item with higher priority than updates in
    /// next iteration
    stack: Vec<WireStruct>,
}

impl<'a> UpdateIterator<'a> {
    pub fn new(update: &'a mut Update, state: StateVector) -> Self {
        let mut client_ids = update.structs.keys().cloned().collect::<Vec<_>>();
        client_ids.sort();
        let cur_client_id = client_ids.pop();

        UpdateIterator {
            update,
            state,
            client_ids,
            cur_client_id,
            stack: Vec::new(),
        }
    }

    /// iterate the client ids until we find the next client with left updates
    /// that can be consumed
    ///
    /// note:
    /// firstly we will check current client id as well to ensure current
    /// updates queue is not empty yet
    fn next_client(&mut self) -> Option<Client> {
        while let Some(client_id) = self.cur_client_id {
            match self.update.structs.get(&client_id) {
                Some(refs) if !refs.is_empty() => {
                    self.cur_client_id.replace(client_id);
                    return self.cur_client_id;
                }
                _ => {
                    self.update.structs.remove(&client_id);
                    self.cur_client_id = self.client_ids.pop();
                }
            }
        }

        None
    }

    /// update the missing state vector
    /// tell it the smallest clock that missed.
    fn update_missing_state(&mut self, client: Client, clock: Clock) {
        self.update.missing_state.set_min(client, clock);
    }

    /// any time we can't apply an update during the iteration,
    /// we should put all items in pending stack to rest structs
    fn add_stack_to_rest(&mut self) {
        for s in self.stack.drain(..) {
            let client = s.id().client;
            let unapplicable_items = self.update.structs.remove(&client);
            if let Some(mut items) = unapplicable_items {
                items.push_front(s);
                self.update.pending_structs.insert(client, items);
            } else {
                self.update.pending_structs.insert(client, [s].into());
            }
            self.client_ids.retain(|&c| c != client);
        }
    }

    /// tell if current update's dependencies(left, right, parent) has already
    /// been consumed and recorded and return the client of them if not.
    fn get_missing_dep(&self, struct_info: &WireStruct) -> Option<Client> {
        let item = struct_info.as_item()?;
        let parent = match &item.parent {
            Some(WireParent::Item(parent_id)) => Some(*parent_id),
            _ => None,
        };
        find_missing_dependency(item.id, item.origin_left_id, item.origin_right_id, parent, &self.state)
    }

    fn next_candidate(&mut self) -> Option<WireStruct> {
        let mut cur = None;

        if !self.stack.is_empty() {
            cur.replace(self.stack.pop().unwrap());
        } else if let Some(client) = self.next_client() {
            // Safety:
            // client index of updates and update length are both checked in
            // next_client safe to use unwrap
            cur.replace(self.update.structs.get_mut(&client).unwrap().pop_front().unwrap());
        }

        cur
    }

    /// Ends the walk at a struct the store refused: the structs the walk took
    /// off their queues to hand out after it, which wait for it, go back to
    /// the front of them. The update then holds every struct the walk has
    /// not handed out, the ones set aside in `pending_structs`.
    pub(crate) fn give_back(&mut self) {
        // the last one taken off a queue is the first to go back to it
        for wire in self.stack.drain(..).rev() {
            self.update.structs.entry(wire.client()).or_default().push_front(wire);
        }
    }
}

impl Iterator for UpdateIterator<'_> {
    type Item = (WireStruct, u64);

    /// What to do with a struct is decided by `y-octo-core`
    /// (`check_local_readiness`, then `classify_ready_step` for a struct
    /// whose earlier clocks are there; `Pending.classify_struct_step_spec`
    /// in `proofs/`). The dependencies of a skip, or of a struct that waits
    /// for clocks of its own client, are not looked up.
    fn next(&mut self) -> Option<Self::Item> {
        // fetch the first candidate from stack or updates
        let mut cur = self.next_candidate();

        while let Some(cur_update) = cur.take() {
            let id = cur_update.id();
            let core_id = IdCore {
                client: id.client,
                clock: id.clock,
            };
            // a skip is a skip whatever the document holds: no lookup for it
            let is_skip = cur_update.is_skip();
            let local_state = if is_skip { 0 } else { self.state.get(&id.client) };
            match check_local_readiness(core_id, is_skip, local_state) {
                LocalStep::Skip => {}
                LocalStep::MissingLocal { client, missing_clock } => {
                    // missing local state of same client
                    // can't apply the continuous updates from same client
                    // push into the stack and put tell all the items in stack
                    // are unapplicable
                    self.stack.push(cur_update);
                    self.update_missing_state(client, missing_clock);
                    self.add_stack_to_rest();
                }
                LocalStep::Ready => {
                    let missing = self.get_missing_dep(&cur_update);
                    match classify_ready_step(core_id, cur_update.len(), local_state, missing) {
                        // some dependency is missing, we need to turn to
                        // iterate the dependency first.
                        StructStep::MissingDep { client: dep } => {
                            self.stack.push(cur_update);

                            match self.update.structs.get_mut(&dep) {
                                Some(updates) if !updates.is_empty() => {
                                    // iterate the dependency client first
                                    cur.replace(updates.pop_front().unwrap());
                                    continue;
                                }
                                // but the dependency update is drained
                                // need to move all stack item to unapplicable
                                // store
                                _ => {
                                    self.update_missing_state(dep, self.state.get(&dep));
                                    self.add_stack_to_rest();
                                }
                            }
                        }
                        // we finally find the first applicable update
                        StructStep::Apply { offset, next_state } => {
                            self.state.set_max(id.client, next_state);
                            return Some((cur_update, offset));
                        }
                        // every clock of the struct is there already; the other
                        // answers are the ones of `check_local_readiness`
                        StructStep::AlreadyApplied | StructStep::Skip | StructStep::MissingLocal { .. } => {}
                    }
                }
            }

            cur = self.next_candidate();
        }

        // we all done
        None
    }
}

pub struct DeleteSetIterator<'a> {
    update: &'a mut Update,
    /// current state vector from store
    state: StateVector,
}

impl<'a> DeleteSetIterator<'a> {
    pub fn new(update: &'a mut Update, state: StateVector) -> Self {
        DeleteSetIterator { update, state }
    }
}

/// The ranges of a client from the first one with a part that waits:
/// `first` and the pending parts of the ranges after it, up to the first
/// range with a part to apply (`applicable` when that is the first one
/// itself), go to the client's entry of the pending set, looked up once. A
/// part that waits is not empty, so the entry is not left without a range.
/// Out of line, as the usual range waits for nothing.
#[inline(never)]
fn wait_from(
    deletes: &mut OrderRange,
    pending_set: &mut DeleteSet,
    client: Client,
    local_state: u64,
    first: ClockRange,
    mut applicable: Option<ClockRange>,
) -> Option<Range<u64>> {
    let waiting = pending_set.clients.entry(client).or_default();
    waiting.push(first.start..first.end);
    while applicable.is_none() {
        let Some(range) = deletes.pop() else { break };
        let split = split_delete_range(range.start, range.end, local_state);
        if let Some(pending) = split.pending {
            waiting.push(pending.start..pending.end);
        }
        applicable = split.applicable;
    }
    applicable.map(|range| range.start..range.end)
}

impl Iterator for DeleteSetIterator<'_> {
    type Item = (Client, Range<u64>);

    /// A range is cut at the clocks the document holds by
    /// `split_delete_range` of `y-octo-core` (`Pending.split_delete_range_spec`
    /// in `proofs/`): the part below them is applied, the rest waits.
    fn next(&mut self) -> Option<Self::Item> {
        // the first client and its ranges, in one step
        while let Some((&client, deletes)) = self.update.delete_set.clients.iter_mut().next() {
            let local_state = self.state.get(&client);

            let mut applicable = None;
            while let Some(range) = deletes.pop() {
                let split = split_delete_range(range.start, range.end, local_state);
                // all state missing, or partially state missing:
                // [start..end)
                //        ^ local_state in between
                // // split
                // [start..local_state) [local_state..end)
                //                      ^^^^^ unapplicable
                if let Some(pending) = split.pending {
                    applicable = wait_from(
                        deletes,
                        &mut self.update.pending_delete_set,
                        client,
                        local_state,
                        pending,
                        split.applicable,
                    );
                    break;
                }
                if let Some(range) = split.applicable {
                    applicable = Some(range.start..range.end);
                    break;
                }
            }

            // drop the client as soon as its ranges are used up, so an
            // iterator dropped early leaves no empty entry behind
            if deletes.is_empty() {
                self.update.delete_set.remove(&client);
            }
            if let Some(range) = applicable {
                return Some((client, range));
            }
        }

        None
    }
}

#[cfg(test)]
#[allow(clippy::single_range_in_vec_init, clippy::type_complexity)]
mod tests {
    use std::{num::ParseIntError, path::PathBuf};

    use serde::Deserialize;

    use super::*;
    use crate::doc::common::OrderRange;

    fn struct_item(id: (Client, Clock), len: usize) -> WireStruct {
        WireStruct::Item(Box::new(WireItem {
            id: id.into(),
            len: len as u64,
            origin_left_id: None,
            origin_right_id: None,
            parent: None,
            parent_sub: None,
            flags: item_flags::ITEM_COUNTABLE,
            content: WireContent::String("c".repeat(len)),
        }))
    }

    #[test]
    fn cloned_nested_updates_apply_independently() {
        loom_model!(128 << 10, {
            let source = Doc::with_client(1);
            let mut root = source.get_or_create_map("root").unwrap();
            let mut child = source.create_text().unwrap();
            root.insert("child".into(), child.clone()).unwrap();
            child.insert(0, "base").unwrap();

            let update = source.encode_update().unwrap();
            let original = update.encode_v1().unwrap();
            let mut copy = update.clone();
            let WireStruct::Item(carrier) = &mut copy.structs.get_mut(&1).unwrap()[0] else {
                unreachable!()
            };
            assert!(matches!(
                carrier.content,
                WireContent::Type {
                    kind: YTypeKind::Text,
                    ..
                }
            ));
            carrier.parent_sub = Some("copy".into());
            let mut first = Doc::with_client(2);
            first.apply_update(copy).unwrap();
            let mut first_child = first
                .get_or_create_map("root")
                .unwrap()
                .get("copy")
                .unwrap()
                .to_text()
                .unwrap();
            first_child.insert(4, "!").unwrap();
            assert_eq!(update.encode_v1().unwrap(), original);
            let mut second = Doc::with_client(3);
            second.apply_update(update).unwrap();
            assert_eq!(
                second
                    .get_or_create_map("root")
                    .unwrap()
                    .get("child")
                    .unwrap()
                    .to_text()
                    .unwrap()
                    .to_string(),
                "base"
            );
            assert_eq!(first_child.to_string(), "base!");
        });
    }

    #[test]
    fn merge_truncates_inside_utf16_pair() {
        loom_model!({
            let source = Doc::with_client(1);
            source.get_or_create_text("text").unwrap().insert(0, "a😀b").unwrap();
            let full = source.encode_update().unwrap();
            let mut prefix = full.clone();
            let nodes = prefix.structs.get_mut(&1).unwrap();
            let (left, right) = nodes.pop_front().unwrap().split_at(2).unwrap();
            assert_eq!(left.as_item().unwrap().content, WireContent::String("a�".into()));
            nodes.push_back(left);
            let merged = Update::merge([prefix, full]);
            assert_eq!(merged.structs[&1][1], right);
            assert_eq!(right.as_item().unwrap().content, WireContent::String("�b".into()));
            let replay = Doc::try_from_binary_v1(merged.encode_v1().unwrap()).unwrap();
            assert_eq!(replay.get_or_create_text("text").unwrap().to_string(), "a��b");
        });
    }

    fn parse_doc_update(input: Vec<u8>) -> JwstCodecResult<Update> {
        Update::decode_v1(input)
    }

    #[test]
    #[cfg_attr(any(miri, loom), ignore)]
    fn test_parse_doc() {
        let docs = [
            (include_bytes!("../../fixtures/basic.bin").to_vec(), 1, 188),
            (include_bytes!("../../fixtures/database.bin").to_vec(), 1, 149),
            (include_bytes!("../../fixtures/large.bin").to_vec(), 1, 9036),
            (include_bytes!("../../fixtures/with-subdoc.bin").to_vec(), 2, 30),
            (
                include_bytes!("../../fixtures/edge-case-left-right-same-node.bin").to_vec(),
                2,
                243,
            ),
        ];

        for (doc, clients, structs) in docs {
            let update = parse_doc_update(doc).unwrap();

            assert_eq!(update.structs.len(), clients);
            assert_eq!(update.structs.iter().map(|s| s.1.len()).sum::<usize>(), structs);
        }
    }

    fn decode_hex(s: &str) -> Result<Vec<u8>, ParseIntError> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
            .collect()
    }

    #[allow(dead_code)]
    #[derive(Deserialize, Debug)]
    struct Data {
        id: u64,
        workspace: String,
        timestamp: String,
        blob: String,
    }

    #[ignore = "just for local data test"]
    #[test]
    fn test_parse_local_doc() {
        let json = serde_json::from_slice::<Vec<Data>>(include_bytes!("../../fixtures/local_docs.json")).unwrap();

        for ws in json {
            let data = &ws.blob[5..=(ws.blob.len() - 2)];
            if let Ok(data) = decode_hex(data) {
                match parse_doc_update(data.clone()) {
                    Ok(update) => {
                        println!(
                            "workspace: {}, global structs: {}, total structs: {}",
                            ws.workspace,
                            update.structs.len(),
                            update.structs.iter().map(|s| s.1.len()).sum::<usize>()
                        );
                    }
                    Err(_e) => {
                        std::fs::write(
                            PathBuf::from("./src/fixtures/invalid").join(format!("{}.ydoc", ws.workspace)),
                            data,
                        )
                        .unwrap();
                        println!("doc error: {}", ws.workspace);
                    }
                }
            } else {
                println!("error origin data: {}", ws.workspace);
            }
        }
    }

    #[test]
    fn test_update_iterator() {
        loom_model!({
            let mut update = Update {
                structs: ClientMap::from_iter([
                    (
                        0,
                        VecDeque::from([
                            struct_item((0, 0), 1),
                            struct_item((0, 1), 1),
                            WireStruct::Skip {
                                id: (0, 2).into(),
                                len: 1,
                            },
                        ]),
                    ),
                    (
                        1,
                        VecDeque::from([struct_item((1, 0), 1), {
                            let WireStruct::Item(mut item) = struct_item((1, 1), 2) else {
                                unreachable!()
                            };
                            item.origin_left_id = Some((0, 1).into());
                            WireStruct::Item(item)
                        }]),
                    ),
                ]),
                ..Update::default()
            };

            let mut iter = update.iter(StateVector::default());
            assert_eq!(iter.next().unwrap().0.id(), (1, 0).into());
            assert_eq!(iter.next().unwrap().0.id(), (0, 0).into());
            assert_eq!(iter.next().unwrap().0.id(), (0, 1).into());
            assert_eq!(iter.next().unwrap().0.id(), (1, 1).into());
            assert_eq!(iter.next(), None);
        });
    }

    #[test]
    fn test_update_iterator_with_missing_state() {
        loom_model!({
            let mut update = Update {
                // an item with higher sequence id than local state
                structs: ClientMap::from_iter([(0, VecDeque::from([struct_item((0, 4), 1)]))]),
                ..Update::default()
            };

            let mut iter = update.iter(StateVector::from([(0, 3)]));
            assert_eq!(iter.next(), None);
            assert!(!update.pending_structs.is_empty());
            assert_eq!(
                update.pending_structs.get_mut(&0).unwrap().pop_front().unwrap().id(),
                (0, 4).into()
            );
            assert!(!update.missing_state.is_empty());
            assert_eq!(update.missing_state.get(&0), 3);
        });
    }

    #[test]
    fn test_delete_set_iterator() {
        let mut update = Update {
            delete_set: DeleteSet::from([(0, vec![(0..2), (3..5)])]),
            ..Update::default()
        };

        let mut iter = update.delete_set_iter(StateVector::from([(0, 10)]));
        assert_eq!(iter.next().unwrap(), (0, 0..2));
        assert_eq!(iter.next().unwrap(), (0, 3..5));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_delete_set_with_missing_state() {
        let mut update = Update {
            delete_set: DeleteSet::from([(0, vec![(3..5), (7..12), (13..15)])]),
            ..Update::default()
        };

        let mut iter = update.delete_set_iter(StateVector::from([(0, 10)]));
        assert_eq!(iter.next().unwrap(), (0, 3..5));
        assert_eq!(iter.next().unwrap(), (0, 7..10));
        assert_eq!(iter.next(), None);

        assert!(!update.pending_delete_set.is_empty());
        assert_eq!(
            update.pending_delete_set.get(&0).unwrap(),
            &OrderRange::from(vec![(10..12), (13..15)])
        );
    }

    #[test]
    fn test_merge_updates() {
        for case in 0..3 {
            loom_model!({
                let (sources, expected) = match case {
                    0 => (
                        [
                            vec![WireStruct::Gc {
                                id: (0, 5).into(),
                                len: 1,
                            }],
                            vec![struct_item((0, 0), 1), struct_item((0, 5), 1)],
                        ],
                        vec![
                            struct_item((0, 0), 1),
                            WireStruct::Skip {
                                id: (0, 1).into(),
                                len: 4,
                            },
                            struct_item((0, 5), 1),
                        ],
                    ),
                    1 => (
                        [
                            vec![
                                WireStruct::Gc {
                                    id: (0, 0).into(),
                                    len: 3,
                                },
                                WireStruct::Gc {
                                    id: (0, 5).into(),
                                    len: 1,
                                },
                            ],
                            vec![struct_item((0, 0), 1), struct_item((0, 5), 1)],
                        ],
                        vec![
                            WireStruct::Gc {
                                id: (0, 0).into(),
                                len: 3,
                            },
                            WireStruct::Skip {
                                id: (0, 3).into(),
                                len: 2,
                            },
                            struct_item((0, 5), 1),
                        ],
                    ),
                    _ => (
                        [
                            vec![WireStruct::Gc {
                                id: (0, 1).into(),
                                len: 1,
                            }],
                            vec![struct_item((0, 0), 1), struct_item((0, 1), 1)],
                        ],
                        vec![struct_item((0, 0), 1), struct_item((0, 1), 1)],
                    ),
                };
                let merged = Update::merge(sources.map(|nodes| Update {
                    structs: ClientMap::from_iter([(0, nodes.into())]),
                    ..Default::default()
                }));
                assert_eq!(merged.structs[&0], VecDeque::from(expected));
            });
        }

        loom_model!({
            let update = Update {
                structs: ClientMap::from_iter([(
                    0,
                    VecDeque::from([
                        struct_item((0, 0), 1),
                        struct_item((0, 1), 1),
                        struct_item((0, 10), 1),
                        WireStruct::Gc {
                            id: (0, 20).into(),
                            len: 10,
                        },
                    ]),
                )]),
                ..Default::default()
            };

            let merged = Update::merge([update]);

            assert_eq!(
                merged.structs.get(&0).unwrap(),
                &VecDeque::from([
                    struct_item((0, 0), 1),
                    struct_item((0, 1), 1),
                    WireStruct::Skip {
                        id: (0, 2).into(),
                        len: 8
                    },
                    struct_item((0, 10), 1),
                    WireStruct::Skip {
                        id: (0, 11).into(),
                        len: 9
                    },
                    WireStruct::Gc {
                        id: (0, 20).into(),
                        len: 10
                    },
                ])
            );
            let fill = Update {
                structs: ClientMap::from_iter([(
                    0,
                    VecDeque::from([
                        WireStruct::Skip {
                            id: (0, 0).into(),
                            len: 2,
                        },
                        struct_item((0, 2), 8),
                        WireStruct::Skip {
                            id: (0, 10).into(),
                            len: 15,
                        },
                        WireStruct::Gc {
                            id: (0, 25).into(),
                            len: 10,
                        },
                    ]),
                )]),
                ..Default::default()
            };
            let merged = Update::merge([merged, fill]);
            assert_eq!(
                merged.structs[&0]
                    .iter()
                    .map(|node| (node.clock(), node.len(), node.is_skip()))
                    .collect::<Vec<_>>(),
                [
                    (0, 1, false),
                    (1, 1, false),
                    (2, 8, false),
                    (10, 1, false),
                    (11, 9, true),
                    (20, 10, false),
                    (30, 5, false)
                ]
            );
            let pending = Update {
                pending_structs: ClientMap::from_iter([(0, VecDeque::from([struct_item((0, 11), 9)]))]),
                missing_state: StateVector::from([(0, 10), (1, 0)]),
                pending_delete_set: DeleteSet::from([(0, vec![12..15])]),
                ..Default::default()
            };
            let mut merged = Update::merge([merged, pending]);
            assert!(!merged.structs[&0].iter().any(WireStruct::is_skip));
            assert_eq!(merged.missing_state, StateVector::from([(0, 10), (1, 0)]));
            assert_eq!(merged.delete_set[&0].canonical_ranges(), vec![12..15]);
            assert!(merged.is_pending_empty());
            merged
                .pending_structs
                .insert(1, VecDeque::from([struct_item((1, 0), 1)]));
            merged.pending_delete_set.add_range(1, 0..1);
            Update::merge_into(
                &mut merged,
                [Update {
                    missing_state: StateVector::from([(0, 5), (1, 1)]),
                    ..Default::default()
                }],
            );
            assert_eq!(merged.missing_state, StateVector::from([(0, 5), (1, 0)]));
            assert_eq!(merged.structs[&1].len(), 1);
            assert_eq!(merged.delete_set[&1].canonical_ranges(), vec![0..1]);
            assert!(merged.is_pending_empty());
        });

        // Full snapshots and tails produced by Yjs 13.6.21, client 1.
        let cases: &[(&[u8], &[u8], &[u8], &str)] = &[
            (
                &[1, 1, 1, 0, 4, 1, 4, 116, 101, 120, 116, 4, 97, 98, 99, 100, 0],
                &[
                    1, 3, 1, 0, 4, 1, 4, 116, 101, 120, 116, 1, 97, 129, 1, 0, 1, 132, 1, 1, 2, 99, 100, 1, 1, 1, 1, 1,
                ],
                &[1, 1, 1, 2, 132, 1, 1, 2, 99, 100, 1, 1, 1, 1, 1],
                "acd",
            ),
            (
                &[
                    1, 1, 1, 0, 4, 1, 4, 116, 101, 120, 116, 6, 97, 240, 159, 152, 128, 98, 0,
                ],
                &[
                    1, 3, 1, 0, 4, 1, 4, 116, 101, 120, 116, 1, 97, 129, 1, 0, 1, 132, 1, 1, 4, 239, 191, 189, 98, 1,
                    1, 1, 1, 1,
                ],
                &[1, 1, 1, 2, 132, 1, 1, 4, 239, 191, 189, 98, 1, 1, 1, 1, 1],
                "a\u{fffd}b",
            ),
        ];
        for &(full, segmented, tail, text) in cases {
            for reverse in [false, true] {
                loom_model!(64 << 10, {
                    let inputs = if reverse { [segmented, full] } else { [full, segmented] };
                    let merged = Update::merge(inputs.map(|bytes| Update::decode_v1(bytes).unwrap()));
                    let structs = &merged.structs[&1];
                    assert_eq!(structs.front().unwrap().clock(), 0);
                    assert_eq!(structs.iter().map(WireStruct::len).sum::<u64>(), 4);
                    assert_eq!(merged.delete_set[&1].canonical_ranges(), vec![1..2]);
                    let bytes = merged.encode_v1().unwrap();
                    let expected = if reverse {
                        segmented.to_vec()
                    } else {
                        let mut bytes = full[..full.len() - 1].to_vec();
                        bytes.extend_from_slice(&[1, 1, 1, 1, 1]);
                        bytes
                    };
                    assert_eq!(bytes, expected);
                    let replay = Update::merge([
                        Update::decode_v1(&bytes).unwrap(),
                        Update::decode_v1(full).unwrap(),
                        Update::decode_v1(segmented).unwrap(),
                    ]);
                    assert_eq!(replay.encode_v1().unwrap(), bytes);
                    let doc = Doc::try_from_binary_v1(&bytes).unwrap();
                    assert_eq!(doc.get_or_create_text("text").unwrap().to_string(), text);
                    assert_eq!(doc.get_state_vector(), StateVector::from([(1, 4)]));

                    let partial = Update::merge([
                        Update::decode_v1(tail).unwrap(),
                        Update::decode_v1([0, 1, 1, 1, 0, 3]).unwrap(),
                    ]);
                    let bytes = partial.encode_v1().unwrap();
                    let partial = Update::decode_v1(&bytes).unwrap();
                    assert_eq!(partial.delete_set[&1].canonical_ranges(), vec![0..3]);
                    let mut doc = Doc::try_from_binary_v1(&bytes).unwrap();
                    assert!(doc.has_pending_updates());
                    doc.apply_update_from_binary_v1(full).unwrap();
                    assert!(!doc.has_pending_updates());
                    assert_eq!(
                        doc.get_or_create_text("text").unwrap().to_string(),
                        &text[text.len() - 1..]
                    );
                    let recovered = Update::merge([partial, Update::decode_v1(full).unwrap()]);
                    assert_eq!(recovered.structs[&1].iter().map(WireStruct::len).sum::<u64>(), 4);
                    assert_eq!(recovered.delete_set[&1].canonical_ranges(), vec![0..3]);
                });
            }
        }

        loom_model!({
            let prefix = [1, 1, 1, 0, 4, 1, 4, 116, 101, 120, 116, 2, 97, 98, 0];
            let full = [1, 1, 1, 0, 4, 1, 4, 116, 101, 120, 116, 4, 97, 98, 99, 100, 0];
            let expected = [
                1, 2, 1, 0, 4, 1, 4, 116, 101, 120, 116, 2, 97, 98, 132, 1, 1, 2, 99, 100, 0,
            ];
            let full_update = Update::decode_v1(full).unwrap();
            for _ in 0..2 {
                let merged = Update::merge([Update::decode_v1(prefix).unwrap(), full_update.clone()]);
                assert_eq!(merged.encode_v1().unwrap(), expected);
                assert_eq!(full_update.encode_v1().unwrap(), full);
            }
        });

        for reverse in [false, true] {
            loom_model!({
                let full = [
                    1, 1, 1, 0, 4, 1, 4, 116, 101, 120, 116, 6, 97, 240, 159, 152, 128, 98, 0,
                ];
                let higher_client = [
                    2, 1, 2, 0, 40, 1, 1, 109, 1, 120, 1, 125, 1, 3, 1, 0, 4, 1, 4, 116, 101, 120, 116, 1, 97, 129, 1,
                    0, 1, 132, 1, 1, 4, 239, 191, 189, 98, 1, 1, 1, 1, 1,
                ];
                let inputs = if reverse {
                    [higher_client.as_slice(), full.as_slice()]
                } else {
                    [full.as_slice(), higher_client.as_slice()]
                };
                let merged = Update::merge(inputs.map(|bytes| Update::decode_v1(bytes).unwrap()));
                assert_eq!(merged.encode_v1().unwrap(), higher_client);
            });
        }
        for count in 2..=4 {
            for reverse in [false, true] {
                loom_model!(64 << 10, {
                    let live = [
                        2, 1, 9, 0, 40, 0, 1, 0, 5, 118, 97, 108, 117, 101, 1, 119, 5, 99, 104, 105, 108, 100, 1, 1, 0,
                        39, 1, 4, 114, 111, 111, 116, 6, 110, 101, 115, 116, 101, 100, 1, 0,
                    ];
                    let collected = [
                        2, 1, 9, 0, 0, 1, 1, 1, 0, 33, 1, 4, 114, 111, 111, 116, 6, 110, 101, 115, 116, 101, 100, 1, 2,
                        9, 1, 0, 1, 1, 1, 0, 1,
                    ];
                    let future = [
                        1, 2, 15, 0, 40, 0, 1, 0, 6, 102, 117, 116, 117, 114, 101, 1, 125, 42, 40, 1, 4, 114, 111, 111,
                        116, 6, 109, 97, 114, 107, 101, 114, 1, 125, 163, 1, 0,
                    ];
                    let expected = [
                        3, 2, 15, 0, 0, 1, 40, 1, 4, 114, 111, 111, 116, 6, 109, 97, 114, 107, 101, 114, 1, 125, 163,
                        1, 1, 9, 0, 0, 1, 1, 1, 0, 33, 1, 4, 114, 111, 111, 116, 6, 110, 101, 115, 116, 101, 100, 1, 3,
                        15, 1, 0, 1, 9, 1, 0, 1, 1, 1, 0, 1,
                    ];
                    let merged = Update::merge((0..count).map(|index| {
                        let bytes = if (index % 2 == 0) == reverse {
                            live.as_slice()
                        } else {
                            collected.as_slice()
                        };
                        Update::decode_v1(bytes).unwrap()
                    }));
                    let mut doc = Doc::try_from_binary_v1(merged.encode_v1().unwrap()).unwrap();
                    doc.apply_update_from_binary_v1(future).unwrap();
                    assert!(!doc.has_pending_updates());
                    assert_eq!(doc.get_state_vector(), StateVector::from([(1, 1), (9, 1), (15, 2)]));
                    // Compare the official default-GC normal form, including
                    // all struct facts and delete ranges, after a future edit.
                    assert_eq!(doc.encode_update_v1().unwrap(), expected);
                });
            }
        }
    }

    #[test]
    fn merged_update_should_not_be_released_in_next_turn() {
        loom_model!({
            let update = Update {
                structs: ClientMap::from_iter([(
                    0,
                    VecDeque::from([
                        struct_item((0, 0), 1),
                        struct_item((0, 1), 1),
                        struct_item((0, 10), 1),
                        WireStruct::Gc {
                            id: (0, 20).into(),
                            len: 10,
                        },
                    ]),
                )]),
                ..Default::default()
            };

            let merged = Update::merge([update]);

            let update2 = Update {
                structs: ClientMap::from_iter([(
                    0,
                    VecDeque::from([
                        struct_item((0, 30), 1),
                        WireStruct::Gc {
                            id: (0, 32).into(),
                            len: 1,
                        },
                    ]),
                )]),
                ..Default::default()
            };

            let merged2 = Update::merge([update2, merged]);

            assert_eq!(merged2.structs.get(&0).unwrap().len(), 9);
        });
    }

    fn state(client: Client, clock: Clock) -> StateVector {
        let mut state = StateVector::default();
        state.insert(client, clock);
        state
    }

    #[test]
    fn delete_set_iter_dropped_after_fully_applicable_range_leaves_no_client() {
        let mut update = Update {
            delete_set: DeleteSet::from([(1, vec![0..2])]),
            ..Update::default()
        };
        assert_eq!(update.delete_set_iter(state(1, 5)).next(), Some((1, 0..2)));

        assert!(update.is_empty());
        assert!(update.is_pending_empty());
        assert!(update.delete_set.get(&1).is_none());
        let encoded = update.encode_v1().unwrap();
        assert_eq!(encoded, Update::default().encode_v1().unwrap());
        assert!(Update::decode_v1(encoded).unwrap().is_empty());
    }

    #[test]
    fn delete_set_iter_dropped_after_partially_applicable_range_leaves_no_client() {
        let mut update = Update {
            delete_set: DeleteSet::from([(1, vec![0..4])]),
            ..Update::default()
        };
        assert_eq!(update.delete_set_iter(state(1, 1)).next(), Some((1, 0..1)));

        assert!(update.is_empty());
        assert!(!update.is_pending_empty());
        assert!(update.delete_set.get(&1).is_none());
        assert_eq!(update.encode_v1().unwrap(), Update::default().encode_v1().unwrap());
        assert_eq!(update.pending_delete_set.get(&1), Some(&OrderRange::from(1..4)));
    }
}
