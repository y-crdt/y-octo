use std::{ops::Range, sync::Arc};

use serde::{Deserialize, Serialize};

use super::{store::StoreRef, *};
use crate::sync::RwLock;

/// One edge in the resolved parent chain. Carrier IDs survive slot reuse and
/// the component records the key or list position at resolution time.
struct ParentSnapshot {
    parent: Option<WireParent>,
    component: SmolStr,
}

#[derive(Clone, Default)]
pub struct HistoryOptions {
    pub client: Option<u64>,
    /// Only available when client is set
    pub skip: Option<usize>,
    /// Only available when client is set
    pub limit: Option<usize>,
}

#[derive(Clone, Default)]
pub struct StoreHistory {
    store: StoreRef,
    parents: Arc<RwLock<HashMap<Id, ParentSnapshot>>>,
}

/// Formatting a history handle never needs to lock the document.
impl std::fmt::Debug for StoreHistory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StoreHistory").finish_non_exhaustive()
    }
}

/// [Value]'s `Display` without taking the store lock again: the caller holds
/// it.
fn content_string(arena: &TypeArena, content: &Content) -> String {
    match content {
        Content::Type(ty) => arena
            .get(*ty)
            .filter(|ty| ty.kind() == YTypeKind::Text)
            .map(|ty| types::text::text_string(&arena.items, ty))
            .unwrap_or_default(),
        content => scalar_history_string(content.view(arena).expect("scalar content is always available")),
    }
}

fn scalar_history_string(content: ContentView<'_>) -> String {
    match content {
        ContentView::String(s) => format!("\"{s}\""),
        ContentView::Binary(bytes) => format!("{bytes:?}"),
        ContentView::Embed(v) => v.to_string(),
        ContentView::Any([value]) => value.to_string(),
        ContentView::Any(values) => format!(
            "[{}]",
            values.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")
        ),
        ContentView::Json(values) => format!(
            "[{}]",
            values
                .iter()
                .map(|s| match s {
                    Some(s) => format!("\"{s}\""),
                    None => Any::Undefined.to_string(),
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ContentView::Deleted(_) | ContentView::Format { .. } => Any::Undefined.to_string(),
        ContentView::Doc { .. } | ContentView::Type { .. } => String::new(),
    }
}

/// Emit visible intervals in clock order. `deleted` begins at the first
/// deletion ending after this item's start.
fn visible_wire_content(item: &WireItem, deleted: &[Range<u64>], mut emit: impl FnMut(Clock, String)) {
    let start = item.id.clock;
    let end = start + item.len;
    let Some(first) = deleted.first().filter(|r| r.start < end) else {
        emit(start, scalar_history_string(item.content.view()));
        return;
    };
    if first.start <= start && first.end >= end {
        return;
    }
    let mut cursor = start;
    let survivors = deleted
        .iter()
        .take_while(|r| r.start < end)
        .cloned()
        .chain(std::iter::once(end..end))
        .filter_map(|r| {
            let gap = cursor..r.start;
            cursor = r.end;
            (!gap.is_empty()).then_some(gap)
        });
    match &item.content {
        WireContent::String(value) => {
            let mut slices = Utf16Slices::new(value);
            for gap in survivors {
                let slice = slices.slice(gap.start - start, gap.end - gap.start);
                emit(gap.start, scalar_history_string(ContentView::String(&slice)));
            }
        }
        WireContent::Any(_) | WireContent::Json(_) => {
            for gap in survivors {
                // Vector lengths are their clock lengths, including on wasm32.
                let a = usize::try_from(gap.start - start).expect("offset within vector");
                let b = usize::try_from(gap.end - start).expect("offset within vector");
                let view = match &item.content {
                    WireContent::Any(values) => ContentView::Any(&values[a..b]),
                    WireContent::Json(values) => ContentView::Json(&values[a..b]),
                    _ => unreachable!(),
                };
                emit(gap.start, scalar_history_string(view));
            }
        }
        _ => {}
    }
}

impl StoreHistory {
    pub(crate) fn new(store: &StoreRef) -> Self {
        Self {
            store: store.clone(),
            ..Default::default()
        }
    }

    /// Snapshots the ancestor path of each newly observed type. Its list
    /// indices are frozen on first resolution, including across later edits
    /// and subsequent calls to this method.
    pub fn resolve(&self) {
        let store = read_store_or_panic(&self.store);
        self.resolve_with_store(&store);
    }

    pub(crate) fn resolve_with_store(&self, store: &DocStore) {
        let mut parents = self.parents.write().unwrap();

        let mut scanned_lists = HashSet::new();
        for node in store.items.iter().flat_map(|(&client, blocks)| blocks.nodes(client)) {
            let Some(item) = node.as_item().and_then(|i| store.type_arena.items.get(i)) else {
                continue;
            };
            if !matches!(item.content, Content::Type(_)) || parents.contains_key(&item.id) {
                continue;
            }
            // Resolve a list of carriers in one pass, including tombstones in
            // the ordinal just as get_node_name does.
            if item.parent_sub.is_none()
                && let Some(parent) = item.parent
            {
                if scanned_lists.insert(parent) {
                    let mut current = store.type_arena[parent]
                        .start
                        .and_then(|i| store.type_arena.items.get(i));
                    let mut index = 0usize;
                    while let Some(sibling) = current {
                        if matches!(sibling.content, Content::Type(_)) {
                            parents.entry(sibling.id).or_insert_with(|| ParentSnapshot {
                                parent: Self::parent_id(&store.type_arena, sibling),
                                component: index.to_string().into(),
                            });
                        }
                        current = sibling.right.and_then(|i| store.type_arena.items.get(i));
                        index += 1;
                    }
                }
            } else {
                parents.insert(
                    item.id,
                    ParentSnapshot {
                        parent: Self::parent_id(&store.type_arena, item),
                        component: Self::get_node_name(&store.type_arena.items, item).into(),
                    },
                );
            }
        }
    }

    pub fn parse_update(&self, update: &Update) -> Vec<History> {
        let parents = self.parents.read().unwrap();
        let mut rows = Vec::new();
        for (client, nodes) in &update.structs {
            let Some(first) = nodes.front() else { continue };
            let ranges = update
                .delete_set
                .get(client)
                .map(OrderRange::canonical_ranges)
                .unwrap_or_default();
            let mut deleted = &ranges[ranges.partition_point(|r| r.end <= first.clock())..];
            for item in nodes.iter().filter_map(WireStruct::as_item) {
                if item.flags & item_flags::ITEM_DELETED != 0 {
                    continue;
                }
                while let Some((head, tail)) = deleted.split_first() {
                    if head.end > item.id.clock {
                        break;
                    }
                    deleted = tail;
                }
                let mut path = None;
                visible_wire_content(item, deleted, |start, content| {
                    let parent = path.get_or_insert_with(|| Self::wire_path(item, &parents)).clone();
                    let id = Id::new(*client, start);
                    rows.push((
                        (start, *client),
                        History {
                            id: id.to_string(),
                            parent,
                            content,
                            action: HistoryAction::Update,
                        },
                    ));
                });
            }
        }
        rows.sort_unstable_by_key(|(key, _)| *key);
        rows.into_iter().map(|(_, row)| row).collect()
    }

    fn wire_path(item: &WireItem, parents: &HashMap<Id, ParentSnapshot>) -> Vec<String> {
        let Some(parent) = &item.parent else { return Vec::new() };
        Self::resolved_path(
            Some(parent),
            item.parent_sub.as_deref().unwrap_or("0").to_owned(),
            parents,
        )
    }

    fn resolved_path<'a>(
        mut parent: Option<&'a WireParent>,
        component: String,
        parents: &'a HashMap<Id, ParentSnapshot>,
    ) -> Vec<String> {
        let mut path = vec![component];
        while let Some(next) = parent {
            match next {
                WireParent::Root(name) => {
                    path.push(name.to_string());
                    break;
                }
                WireParent::Item(id) => {
                    let Some(snapshot) = parents.get(id) else { break };
                    path.push(snapshot.component.to_string());
                    parent = snapshot.parent.as_ref();
                }
            }
        }
        path.reverse();
        path
    }

    pub fn parse_delete_sets(
        &self,
        old_sets: &ClientMap<OrderRange>,
        new_sets: &ClientMap<OrderRange>,
    ) -> Vec<History> {
        let store = read_store_or_panic(&self.store);
        let mut deleted_items = Vec::new();
        for (&client, new_ranges) in new_sets {
            let Some(blocks) = store.items.get(&client) else {
                continue;
            };
            let ranges = old_sets
                .get(&client)
                .map(|old| old.diff_range(new_ranges).into())
                .unwrap_or_else(|| new_ranges.clone());
            deleted_items.extend(
                blocks
                    .nodes(client)
                    .filter(|n| ranges.contains(n.clock()))
                    .filter_map(|n| n.as_item().and_then(|i| store.type_arena.items.get(i))),
            );
        }
        self.parse_deleted_items(&store, deleted_items)
    }

    pub fn parse_store(&self, options: HistoryOptions) -> Vec<History> {
        let store = read_store_or_panic(&self.store);
        let store_items = {
            let client = options
                .client
                .as_ref()
                .and_then(|client| client.ne(&0).then_some(client));
            let mut sort_iter: Box<dyn Iterator<Item = &Item> + '_> = Box::new(
                SortedNodes::new(if let Some(client) = client {
                    store.items.get(client).map(|i| vec![(client, i)]).unwrap_or_default()
                } else {
                    store.items.iter().collect::<Vec<_>>()
                })
                .filter_map(|n| n.as_item().and_then(|i| store.type_arena.items.get(i))),
            );
            if client.is_some() {
                // skip and limit only available when client is set
                if let Some(skip) = options.skip {
                    sort_iter = Box::new(sort_iter.skip(skip));
                }
                if let Some(limit) = options.limit {
                    sort_iter = Box::new(sort_iter.take(limit));
                }
            }

            sort_iter.collect::<Vec<_>>()
        };

        // make items as reference
        let mut store_items = store_items;
        store_items.sort_by_key(|item| item.id.clock);

        self.parse_items(&store, store_items)
    }

    /// `store` is the held read guard: items are only read under the lock.
    fn parse_items(&self, store: &DocStore, store_items: Vec<&Item>) -> Vec<History> {
        let parents = self.parents.read().unwrap();
        let mut histories = vec![];

        for item in store_items {
            if item.deleted() {
                continue;
            }

            histories.push(History {
                id: item.id.to_string(),
                parent: Self::parse_path(&store.type_arena, item, &parents),
                content: content_string(&store.type_arena, &item.content),
                action: HistoryAction::Update,
            })
        }

        histories
    }

    fn parse_deleted_items(&self, store: &DocStore, deleted_items: Vec<&Item>) -> Vec<History> {
        let parents = self.parents.read().unwrap();
        let mut histories = vec![];

        for item in deleted_items {
            histories.push(History {
                id: item.id.to_string(),
                parent: Self::parse_path(&store.type_arena, item, &parents),
                content: content_string(&store.type_arena, &item.content),
                action: HistoryAction::Delete,
            })
        }

        histories
    }

    fn parse_path(types: &TypeArena, item: &Item, parents: &HashMap<Id, ParentSnapshot>) -> Vec<String> {
        let Some(node) = item.find_node_with_parent_info(&types.items) else {
            return Vec::new();
        };
        Self::resolved_path(
            Self::parent_id(types, node).as_ref(),
            Self::get_node_name(&types.items, node),
            parents,
        )
    }

    fn parent_id(types: &TypeArena, item: &Item) -> Option<WireParent> {
        let ty = types.get(item.parent?)?;
        ty.live_carrier(&types.items)
            .map(|carrier| WireParent::Item(carrier.id))
            .or_else(|| ty.root_name().map(|name| WireParent::Root(name.into())))
    }

    fn get_node_name(items: &ItemSpace, item: &Item) -> String {
        if let Some(name) = item.parent_sub.clone() {
            name.to_string()
        } else {
            let mut curr = item;
            let mut idx = 0;

            while let Some(item) = curr.left.and_then(|i| items.get(i)) {
                curr = item;
                idx += 1;
            }

            idx.to_string()
        }
    }
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub enum HistoryAction {
    Insert,
    Update,
    Delete,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct History {
    pub id: String,
    pub parent: Vec<String>,
    pub content: String,
    pub action: HistoryAction,
}

pub(crate) struct SortedNodes<'a> {
    nodes: Vec<(&'a Client, &'a ClientBlocks)>,
    current: Option<(Client, &'a ClientBlocks, usize)>,
}

impl<'a> SortedNodes<'a> {
    pub fn new(mut nodes: Vec<(&'a Client, &'a ClientBlocks)>) -> Self {
        nodes.sort_by(|a, b| b.0.cmp(a.0));
        Self { nodes, current: None }
    }
}

impl Iterator for SortedNodes<'_> {
    type Item = Node;
    fn next(&mut self) -> Option<Node> {
        loop {
            if let Some((client, nodes, remaining)) = &mut self.current
                && *remaining > 0
            {
                *remaining -= 1;
                return nodes.node(*client, *remaining);
            }
            let (&client, nodes) = self.nodes.pop()?;
            self.current = Some((client, nodes, nodes.len()));
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_history_client_test() {
        loom_model!({
            let doc = Doc::default();
            let mut map = doc.get_or_create_map("map").unwrap();
            let mut sub_map = doc.create_map().unwrap();
            map.insert("sub_map".to_string(), sub_map.clone()).unwrap();
            sub_map.insert("key".to_string(), "value").unwrap();

            assert_eq!(doc.clients()[0], doc.client());
        });
    }

    #[test]
    fn parse_history_test() {
        loom_model!({
            let doc = Doc::default();
            let mut map = doc.get_or_create_map("map").unwrap();
            let mut sub_map = doc.create_map().unwrap();
            map.insert("sub_map".to_string(), sub_map.clone()).unwrap();
            sub_map.insert("key".to_string(), "value").unwrap();

            let history = StoreHistory::new(&doc.store);

            let update = doc.encode_update().unwrap();

            assert_eq!(history.parse_store(Default::default()), history.parse_update(&update,));

            // Resolving populates the parent cache. Nested
            // paths resolve to the root and stay identical between store and
            // update views.
            history.resolve();
            let resolved_store = history.parse_store(Default::default());
            let resolved_update = history.parse_update(&update);
            assert_eq!(resolved_store, resolved_update);
            assert!(
                resolved_store
                    .iter()
                    .any(|h| h.content == "\"value\"" && h.parent == vec!["map", "sub_map", "key"])
            );
        });
    }

    #[test]
    fn store_and_wire_history_agree_for_every_content_kind() {
        loom_model!(128 << 10, {
            let source = DocOptions::new().with_client_id(1).auto_gc(false).build();
            let mut map = source.get_or_create_map("root").unwrap();
            let mut nested = source.create_text().unwrap();
            map.insert("nested".into(), nested.clone()).unwrap();
            nested.insert(0, "text").unwrap();
            let mut update = source.encode_update().unwrap();
            let mut clock = source.get_state_vector().get(&1);
            let values = [
                WireContent::Json(vec![Some("s".into()), None]),
                WireContent::Binary(vec![1, 2]),
                WireContent::Embed(Box::new(Any::Integer(2))),
                WireContent::Format {
                    key: "bold".into(),
                    value: Box::new(Any::True),
                },
                WireContent::Any(vec![Any::Null, Any::True]),
                WireContent::Doc {
                    guid: "sub".into(),
                    opts: Box::new(Any::Null),
                },
                WireContent::Deleted(1),
            ];
            for (i, content) in values.into_iter().enumerate() {
                let len = match &content {
                    WireContent::Any(v) => v.len() as u64,
                    WireContent::Json(v) => v.len() as u64,
                    _ => 1,
                };
                update
                    .structs
                    .get_mut(&1)
                    .unwrap()
                    .push_back(WireStruct::Item(Box::new(WireItem {
                        id: Id::new(1, clock),
                        len,
                        origin_left_id: None,
                        origin_right_id: None,
                        parent: Some(WireParent::Root(format!("r{i}").into())),
                        parent_sub: None,
                        flags: content.wire_flags(),
                        content,
                    })));
                clock += len;
            }
            let mut doc = Doc::with_client(2);
            doc.apply_update(update.clone()).unwrap();
            let history = StoreHistory::new(&doc.store);
            for resolved in [false, true] {
                if resolved {
                    history.resolve();
                }
                let wire = history.parse_update(&update);
                let store = history.parse_store(Default::default());
                assert_eq!(wire[0].id, Id::new(1, 0).to_string());
                assert_eq!(wire[0].content, "");
                assert_eq!(store[0].content, "text");
                assert_eq!(wire[0].parent, ["root", "nested"]);
                assert_eq!(wire[0].parent, store[0].parent);
                assert_eq!(wire[1..], store[1..]);
                assert!(wire.iter().any(|h| h.content == "[1, 2]"));
                assert!(wire.iter().any(|h| h.content == "[null, true]"));
                assert!(!wire.iter().any(|h| h.parent.first().is_some_and(|name| name == "r6")));
            }
        });
    }

    #[test]
    fn merge_delete_set_slices_wire_history_at_utf16_clocks() {
        loom_model!({
            let doc = Doc::with_client(7);
            doc.get_or_create_text("body").unwrap().insert(0, "abc").unwrap();
            let history = StoreHistory::new(&doc.store);
            let saved = doc.encode_update().unwrap();
            for (start, expected) in [(0, vec![(1, "\"bc\"")]), (1, vec![(0, "\"a\""), (2, "\"c\"")])] {
                let mut deletion = Update::default();
                deletion.delete_set.add(7, start, 1);
                let merged = Update::merge([saved.clone(), deletion]);
                let rows = history.parse_update(&merged);
                let expected: Vec<_> = expected
                    .into_iter()
                    .map(|(clock, content)| (Id::new(7, clock).to_string(), content))
                    .collect();
                assert_eq!(
                    rows.iter()
                        .map(|row| (row.id.clone(), row.content.as_str()))
                        .collect::<Vec<_>>(),
                    expected
                );
            }

            let doc = Doc::with_client(8);
            doc.get_or_create_text("body").unwrap().insert(0, "a😀b😀c").unwrap();
            let mut update = doc.encode_update().unwrap();
            update.delete_set.add_range(8, 2..5);
            let rows = StoreHistory::new(&doc.store).parse_update(&update);
            assert_eq!(
                rows.iter().map(|r| r.content.as_str()).collect::<Vec<_>>(),
                ["\"a�\"", "\"�c\""]
            );
            assert_eq!(rows[1].id, Id::new(8, 5).to_string());
        });
    }

    #[test]
    fn saved_nested_text_history_keeps_wire_content_after_later_edits() {
        loom_model!({
            let doc = Doc::with_client(7);
            let mut root = doc.get_or_create_map("root").unwrap();
            let mut text = doc.create_text().unwrap();
            root.insert("child".into(), text.clone()).unwrap();
            text.insert(0, "A").unwrap();
            let saved = doc.encode_update().unwrap();
            let history = StoreHistory::new(&doc.store);
            history.resolve();
            let before = history.parse_update(&saved);
            text.insert(1, "B").unwrap();
            assert_eq!(text.to_string(), "AB");
            assert_eq!(history.parse_update(&saved), before);
            assert_eq!(
                before.iter().map(|r| r.content.as_str()).collect::<Vec<_>>(),
                ["", "\"A\""]
            );
        });
    }

    #[test]
    fn sorted_nodes_borrows_in_client_asc_clock_desc_order() {
        let blocks = || {
            let mut blocks = ClientBlocks::default();
            for clock in 0..2 {
                blocks
                    .append(
                        BlockRef {
                            clock,
                            kind: BlockKind::Gc,
                        },
                        1,
                    )
                    .unwrap();
            }
            blocks
        };
        let (c1, c3) = (blocks(), blocks());
        let empty = ClientBlocks::default();
        let client1 = 1;
        let client2 = 2;
        let client3 = 3;
        let ids: Vec<Id> = SortedNodes::new(vec![(&client3, &c3), (&client2, &empty), (&client1, &c1)])
            .map(|node| node.id())
            .collect();
        assert_eq!(ids, vec![Id::new(1, 1), Id::new(1, 0), Id::new(3, 1), Id::new(3, 0)]);
    }

    #[test]
    fn resolved_history_survives_gc_merge_and_resplit() {
        loom_model!({
            let doc = Doc::with_client(1);
            let mut arr = doc.get_or_create_array("arr").unwrap();
            let map1 = doc.create_map().unwrap();
            let mut map2 = doc.create_map().unwrap();
            arr.push(map1).unwrap();
            arr.push(map2.clone()).unwrap();
            map2.insert("key".to_string(), "value").unwrap();

            let old_update = doc.encode_update().unwrap();
            let history = StoreHistory::new(&doc.store);
            history.resolve();

            let before = history.parse_update(&old_update);
            assert!(
                before
                    .iter()
                    .any(|h| h.content == "\"value\"" && h.parent == vec!["arr", "1", "key"])
            );

            // Delete both maps and GC so their carriers are merged; do not call
            // resolve() again.
            arr.remove(0, 2).unwrap();
            doc.gc().unwrap();

            assert_eq!(history.parse_update(&old_update), before);
            assert!(history.parse_store(Default::default()).is_empty());

            // Splitting again at the second map's old ID must still not revive
            // or mis-attach the stale parent.
            {
                let mut store = doc.store.write().unwrap();
                let id = Id::new(1, 1);
                let merged = store.get_node(id).unwrap();
                assert!(merged.is_item());
                assert_eq!(merged.id(), Id::new(1, 0));
                assert!(id.clock < merged.clock() + merged.len());
                assert_eq!(store.split_at_and_get_right(id).unwrap().id(), id);
            }

            history.resolve();
            assert_eq!(history.parse_update(&old_update), before);
            assert!(history.parse_store(Default::default()).is_empty());
        });
    }
}
