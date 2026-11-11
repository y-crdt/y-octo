use std::{collections::VecDeque, ops::Range};

use super::*;
use crate::doc::{StateVector, codec::decoder::v1 as decoder, find_missing_dependency};

#[derive(Debug, Default, Clone)]
pub struct Update {
    pub(crate) structs: ClientMap<VecDeque<Node>>,
    pub(crate) delete_set: DeleteSet,

    /// all unapplicable items that we can't integrate into doc
    /// any item with inconsistent id clock or missing dependency will be put
    /// here
    pub(crate) pending_structs: ClientMap<VecDeque<Node>>,
    /// missing state vector after applying updates
    pub(crate) missing_state: StateVector,
    /// all unapplicable delete set
    pub(crate) pending_delete_set: DeleteSet,
}

impl<'a> CrdtRead<RawDecoder<'a>> for Update {
    fn read(decoder: &mut RawDecoder<'a>) -> JwstCodecResult<Self> {
        let update = decoder::decode(
            decoder.rest_ref(),
            OwnedUpdateSink::default(),
            decoder::DecodeLimits::UNRESTRICTED,
        )
        .map_err(|error| match error {
            decoder::Error::Codec(error) => error,
            decoder::Error::Resource(name) => {
                JwstCodecError::IncompleteDocument(format!("{name} exceeds platform size"))
            }
        })?;
        decoder.consume_rest();
        Ok(update)
    }
}

#[derive(Default)]
struct OwnedUpdateSink {
    update: Update,
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
    type Content = Content;
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
            .push_back(Node::new_gc(id, len));
        Ok(())
    }

    fn skip(&mut self, id: Id, len: u64) -> decoder::Result<()> {
        self.update
            .structs
            .get_mut(&id.client)
            .unwrap()
            .push_back(Node::new_skip(id, len));
        Ok(())
    }

    fn item(&mut self, id: Id, len: u64, meta: decoder::ItemMeta<'a>, content: Content) -> decoder::Result<()> {
        let parent = match meta.parent {
            decoder::WireParent::Root(name) => Some(Parent::String(SmolStr::new(name.value))),
            decoder::WireParent::Item(id) => Some(Parent::Id(id)),
            decoder::WireParent::Inherit => None,
        };
        let item = Somr::new(Item {
            id,
            len,
            origin_left_id: meta.origin_left,
            origin_right_id: meta.origin_right,
            left: Somr::none(),
            right: Somr::none(),
            parent,
            parent_sub: meta.parent_sub.map(|value| SmolStr::new(value.value)),
            flags: ItemFlag::from(if content.countable() {
                item_flags::ITEM_COUNTABLE
            } else {
                0
            }),
            content,
        });
        if matches!(item.get().unwrap().content, Content::Deleted(_)) {
            item.get().unwrap().flags.set_deleted();
        }
        if let Content::Type(ty) = &item.get().unwrap().content
            && let Some(mut ty) = ty.ty_mut()
        {
            ty.item = item.clone();
        }
        self.update
            .structs
            .get_mut(&id.client)
            .unwrap()
            .push_back(Node::Item(item));
        Ok(())
    }

    fn content_atom(&mut self, atom: decoder::ContentAtom<'a>) -> decoder::Result<Content> {
        Ok(match atom {
            decoder::ContentAtom::Deleted(len) => Content::Deleted(len),
            decoder::ContentAtom::Binary(value) => Content::Binary(value.value.to_vec()),
            decoder::ContentAtom::String(value) => Content::String(value.value.to_string()),
            decoder::ContentAtom::Embed(value) => Content::Embed(Box::new(
                serde_json::from_str(value.value)
                    .map_err(|_| decoder::Error::Codec(JwstCodecError::DamagedDocumentJson))?,
            )),
            decoder::ContentAtom::Format { key, value } => Content::Format {
                key: key.value.to_string(),
                value: Box::new(
                    serde_json::from_str(value.value)
                        .map_err(|_| decoder::Error::Codec(JwstCodecError::DamagedDocumentJson))?,
                ),
            },
            decoder::ContentAtom::Type { kind, tag } => Content::Type(YTypeRef::new(
                YTypeKind::from(kind),
                tag.map(|value| value.value.to_string()),
            )),
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

    fn json_finish(&mut self) -> decoder::Result<Content> {
        Ok(Content::Json(std::mem::take(&mut self.json)))
    }

    fn any_content_start(&mut self, count: usize) -> decoder::Result<()> {
        self.content_any = Vec::with_capacity(count.min(HASHMAP_SAFE_CAPACITY));
        Ok(())
    }

    fn any_content_value(&mut self, value: Any) -> decoder::Result<()> {
        self.content_any.push(value);
        Ok(())
    }

    fn any_content_finish(&mut self) -> decoder::Result<Content> {
        Ok(Content::Any(std::mem::take(&mut self.content_any)))
    }

    fn doc_content(&mut self, guid: decoder::WireStr<'a>, options: Any) -> decoder::Result<Content> {
        Ok(Content::Doc {
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
        self.update.delete_set.add_range(client, range);
        Ok(())
    }

    fn finish(mut self) -> decoder::Result<Update> {
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
    // decode from ydoc v1
    pub fn decode_v1<T: AsRef<[u8]>>(buffer: T) -> JwstCodecResult<Update> {
        Update::read(&mut RawDecoder::new(buffer.as_ref()))
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
        let mut sources = target_structs
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
            .collect::<Vec<_>>();

        'merge: loop {
            sources.retain(|source| !source.is_empty());
            // Equal-clock snapshots can have different segmentation or GC
            // representations; neither length nor GC status is a version
            // priority. Keep source ties stable instead.
            sources.sort_by(|left, right| {
                let left = left.front().unwrap();
                let right = right.front().unwrap();
                right
                    .client()
                    .cmp(&left.client())
                    .then_with(|| left.clock().cmp(&right.clock()))
            });
            let Some(source) = sources.first_mut() else {
                break;
            };
            let mut node = source.pop_front().unwrap();
            let client = node.client();
            let merged = target.structs.entry(client).or_default();
            if let Some(last) = merged.back() {
                let end = last.clock() + last.len();
                let mut covered = false;
                while node.clock() + node.len() <= end {
                    covered = true;
                    let Some(next) = source.pop_front() else {
                        continue 'merge;
                    };
                    node = next;
                    if node.client() != client {
                        source.push_front(node);
                        continue 'merge;
                    }
                }
                // After consuming covered nodes, another source may fill this
                // gap. Compare source heads again before emitting a Skip.
                if covered && node.clock() > end {
                    source.push_front(node);
                    continue;
                }
                if node.clock() > end {
                    merged.push_back(Node::new_skip(Id::new(client, end), node.clock() - end));
                } else if node.clock() < end {
                    // V1 infers subsequent clocks from lengths: emit only the
                    // uncovered tail, or overlap would allocate extra clocks.
                    let offset = end - node.clock();
                    node = node.split_at(offset).unwrap().1;
                }
            }
            merged.push_back(node);
            // Match Yjs's lazy reader: emit a source's contiguous run before
            // comparing its next head with the other sources again.
            while source.front().is_some_and(|next| {
                let last = merged.back().unwrap();
                next.client() == client && next.clock() == last.clock() + last.len()
            }) {
                merged.push_back(source.pop_front().unwrap());
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
    stack: Vec<Node>,
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
    fn get_missing_dep(&self, struct_info: &Node) -> Option<Client> {
        let owner = struct_info.as_item();
        let item = owner.get()?;
        let parent = match &item.parent {
            Some(Parent::Id(parent_id)) => Some(*parent_id),
            _ => None,
        };
        find_missing_dependency(item.id, item.origin_left_id, item.origin_right_id, parent, &self.state)
    }

    fn next_candidate(&mut self) -> Option<Node> {
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
}

impl Iterator for UpdateIterator<'_> {
    type Item = (Node, u64);

    fn next(&mut self) -> Option<Self::Item> {
        // fetch the first candidate from stack or updates
        let mut cur = self.next_candidate();

        while let Some(cur_update) = cur.take() {
            let id = cur_update.id();
            if cur_update.is_skip() {
                cur = self.next_candidate();
                continue;
            } else if !self.state.contains(&id) {
                // missing local state of same client
                // can't apply the continuous updates from same client
                // push into the stack and put tell all the items in stack are
                // unapplicable
                self.stack.push(cur_update);
                self.update_missing_state(id.client, id.clock - 1);
                self.add_stack_to_rest();
            } else {
                let id = cur_update.id();
                let dep = self.get_missing_dep(&cur_update);
                // some dependency is missing, we need to turn to iterate the
                // dependency first.
                if let Some(dep) = dep {
                    self.stack.push(cur_update);

                    match self.update.structs.get_mut(&dep) {
                        Some(updates) if !updates.is_empty() => {
                            // iterate the dependency client first
                            cur.replace(updates.pop_front().unwrap());
                            continue;
                        }
                        // but the dependency update is drained
                        // need to move all stack item to unapplicable store
                        _ => {
                            self.update_missing_state(dep, self.state.get(&dep));
                            self.add_stack_to_rest();
                        }
                    }
                } else {
                    // we finally find the first applicable update
                    let local_state = self.state.get(&id.client);
                    // we've already check the local state is greater or equal
                    // to current update's clock so offset
                    // here will never be negative
                    let offset = local_state - id.clock;
                    if offset == 0 || offset < cur_update.len() {
                        self.state.set_max(id.client, id.clock + cur_update.len());
                        return Some((cur_update, offset));
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

impl Iterator for DeleteSetIterator<'_> {
    type Item = (Client, Range<u64>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(client) = self.update.delete_set.keys().next().cloned() {
            let deletes = self.update.delete_set.get_mut(&client).unwrap();
            let local_state = self.state.get(&client);

            while let Some(range) = deletes.pop() {
                let start = range.start;
                let end = range.end;

                if start < local_state {
                    if local_state < end {
                        // partially state missing
                        // [start..end)
                        //        ^ local_state in between
                        // // split
                        // [start..local_state) [local_state..end)
                        //                      ^^^^^ unapplicable
                        self.update
                            .pending_delete_set
                            .add(client, local_state, end - local_state);

                        return Some((client, start..local_state));
                    }

                    return Some((client, range));
                } else {
                    // all state missing
                    self.update.pending_delete_set.add(client, start, end - start);
                }
            }

            self.update.delete_set.remove(&client);
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use std::{num::ParseIntError, path::PathBuf};

    use serde::Deserialize;

    use super::*;
    use crate::doc::common::OrderRange;

    fn struct_item(id: (Client, Clock), len: usize) -> Node {
        Node::Item(Somr::new(
            ItemBuilder::new()
                .id(id.into())
                .content(Content::String("c".repeat(len)))
                .build(),
        ))
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
                            Node::new_skip((0, 2).into(), 1),
                        ]),
                    ),
                    (
                        1,
                        VecDeque::from([
                            struct_item((1, 0), 1),
                            Node::Item(Somr::new(
                                ItemBuilder::new()
                                    .id((1, 1).into())
                                    .left_id(Some((0, 1).into()))
                                    .content(Content::String("c".repeat(2)))
                                    .build(),
                            )),
                        ]),
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
        loom_model!({
            let update = Update {
                structs: ClientMap::from_iter([(
                    0,
                    VecDeque::from([
                        struct_item((0, 0), 1),
                        struct_item((0, 1), 1),
                        struct_item((0, 10), 1),
                        Node::new_gc((0, 20).into(), 10),
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
                    Node::new_skip((0, 2).into(), 8),
                    struct_item((0, 10), 1),
                    Node::new_skip((0, 11).into(), 9),
                    Node::new_gc((0, 20).into(), 10),
                ])
            );
            let fill = Update {
                structs: ClientMap::from_iter([(
                    0,
                    VecDeque::from([
                        Node::new_skip((0, 0).into(), 2),
                        struct_item((0, 2), 8),
                        Node::new_skip((0, 10).into(), 15),
                        Node::new_gc((0, 25).into(), 10),
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
            assert!(!merged.structs[&0].iter().any(Node::is_skip));
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
                    assert_eq!(structs.iter().map(Node::len).sum::<u64>(), 4);
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
                        Update::decode_v1(&[0, 1, 1, 1, 0, 3]).unwrap(),
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
                    assert_eq!(recovered.structs[&1].iter().map(Node::len).sum::<u64>(), 4);
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
                        Node::new_gc((0, 20).into(), 10),
                    ]),
                )]),
                ..Default::default()
            };

            let merged = Update::merge([update]);

            let update2 = Update {
                structs: ClientMap::from_iter([(
                    0,
                    VecDeque::from([struct_item((0, 30), 1), Node::new_gc((0, 32).into(), 1)]),
                )]),
                ..Default::default()
            };

            let merged2 = Update::merge([update2, merged]);

            assert_eq!(merged2.structs.get(&0).unwrap().len(), 9);
        });
    }
}
