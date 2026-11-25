use std::{cmp::max, collections::VecDeque, ops::Deref};

use super::*;

const MAX_SEARCH_MARKER: usize = 80;

#[derive(Clone, Debug)]
pub(crate) struct SearchMarker {
    pub ptr: ItemRef,
    pub index: u64,
}

impl SearchMarker {
    fn new(ptr: ItemRef, index: u64) -> Self {
        SearchMarker { ptr, index }
    }

    fn overwrite_marker(&mut self, ptr: ItemRef, index: u64) {
        self.ptr = ptr;
        self.index = index;
    }
}

/// in yjs, a timestamp field is used to sort markers and the oldest marker is
/// deleted once the limit is reached. this was designed for optimization
/// purposes for v8. In Rust, we can simply use a [VecDeque] and trust the
/// compiler to optimize. the [VecDeque] can naturally maintain the insertion
/// order, allowing us to know which marker is the oldest without using an extra
/// timestamp field.
///
/// A [MarkerList] belongs to a [YType] and is only changed under the store
/// write lock. Readers holding the read lock use [MarkerList::find_readonly].
#[derive(Debug, Default)]
pub(crate) struct MarkerList {
    list: VecDeque<SearchMarker>,
    may_have_unindexed: bool,
}

impl Deref for MarkerList {
    type Target = VecDeque<SearchMarker>;

    fn deref(&self) -> &Self::Target {
        &self.list
    }
}

impl MarkerList {
    pub fn clear(&mut self) {
        self.list.clear();
        self.may_have_unindexed = false;
    }

    #[inline]
    pub fn mark_unindexed(&mut self) {
        self.may_have_unindexed = true;
    }

    // mark pos and push to the end of the linked list
    fn mark_position(list: &mut VecDeque<SearchMarker>, ptr: ItemRef, index: u64) -> Option<SearchMarker> {
        if list.len() >= MAX_SEARCH_MARKER {
            let mut oldest_marker = list.pop_front().unwrap();
            oldest_marker.overwrite_marker(ptr, index);
            list.push_back(oldest_marker);
        } else {
            let marker = SearchMarker::new(ptr, index);
            list.push_back(marker);
        }
        list.back().cloned()
    }

    // update mark position if the index is within the range of the marker
    pub fn update_marker_changes(&mut self, items: &ItemSpace, index: u64, len: i64, inserted: ItemRef) {
        if len < 0 {
            self.may_have_unindexed = true;
        }
        let repair = len > 0 && self.may_have_unindexed;
        debug_assert!(
            len <= 0
                || self.may_have_unindexed
                || self
                    .list
                    .iter()
                    .all(|m| m.ptr.and_then(|i| items.get(i)).is_some_and(|item| item.indexable())),
            "may_have_unindexed was false while an unindexed marker existed"
        );
        let mut any_zero = false;

        for marker in self.list.iter_mut() {
            if repair {
                while let Some(ptr) = marker.ptr.and_then(|i| items.get(i)) {
                    if !ptr.indexable() {
                        // Marker indices still describe the list before this
                        // insertion. Walk the old predecessor edge when a
                        // format or tombstone now has the new item immediately
                        // to its left.
                        let left_ref = if ptr.left == inserted {
                            inserted.and_then(|id| items.get(id)).and_then(|item| item.left)
                        } else {
                            ptr.left
                        };
                        if let Some(left) = left_ref.and_then(|i| items.get(i)) {
                            if left.indexable() {
                                marker.index -= left.len();
                            }
                            marker.ptr = left_ref;
                        } else {
                            marker.ptr = None;
                            marker.index = 0;
                            break;
                        }
                    } else {
                        break;
                    }
                }
            }

            if marker.ptr.is_some() && (index < marker.index || (len > 0 && index == marker.index)) {
                marker.index = max(index as i64, marker.index as i64 + len) as u64;
            }

            if marker.index == 0 {
                any_zero = true;
            }
        }

        if any_zero {
            self.list.retain(|marker| marker.index > 0);
        }

        if repair {
            self.may_have_unindexed = false;
            debug_assert!(
                self.list
                    .iter()
                    .all(|m| m.ptr.and_then(|i| items.get(i)).is_some_and(|item| item.indexable())),
                "surviving markers must be indexable after repair"
            );
        }
    }

    /// Walks from the closest marker (or `start`) to an item boundary at or
    /// before `index`.
    fn walk(items: &ItemSpace, marker: Option<&SearchMarker>, start: &ItemRef, index: u64) -> (ItemRef, u64) {
        let mut marker_index = marker.map(|m| m.index).unwrap_or(0);
        let mut item_ptr = marker.map(|m| m.ptr).unwrap_or_else(|| *start);

        // iterate to the right if possible
        while let Some(item) = item_ptr.and_then(|i| items.get(i)) {
            if marker_index >= index {
                break;
            }

            let right_ref: ItemRef = item.right;
            if right_ref.is_some() {
                if item.indexable() {
                    if index < marker_index + item.len() {
                        break;
                    }

                    marker_index += item.len();
                }
                item_ptr = right_ref;
            } else {
                break;
            }
        }

        // iterate to the left if necessary (might be that marker_index >
        // index)
        while let Some(item) = item_ptr.and_then(|i| items.get(i)) {
            if marker_index <= index {
                break;
            }

            let left_ref: ItemRef = item.left;
            if let Some(left) = left_ref.and_then(|i| items.get(i)) {
                if left.indexable() {
                    marker_index -= left.len();
                }
                item_ptr = left_ref;
            } else {
                break;
            }
        }

        (item_ptr, marker_index)
    }

    fn closest(list: &VecDeque<SearchMarker>, index: u64) -> Option<usize> {
        list.iter()
            .enumerate()
            .min_by_key(|(_, m)| (index as i64 - m.index as i64).abs())
            .map(|(i, _)| i)
    }

    /// Finds the marker closest to `index` and moves or adds a marker there.
    /// Only called under the store write lock.
    pub fn find_marker(
        &mut self,
        items: &ItemSpace,
        start: &ItemRef,
        parent_len: u64,
        index: u64,
    ) -> Option<SearchMarker> {
        if start.is_none() || index == 0 {
            return None;
        }

        let closest = Self::closest(&self.list, index);
        let (item_ptr, marker_index) = Self::walk(items, closest.map(|i| &self.list[i]), start, index);
        if item_ptr.and_then(|i| items.get(i)).is_none_or(|item| !item.indexable()) {
            self.may_have_unindexed = true;
        }

        match closest {
            Some(i)
                if (self.list[i].index as f64 - marker_index as f64).abs()
                    < parent_len as f64 / MAX_SEARCH_MARKER as f64 =>
            {
                // adjust existing marker
                let marker = &mut self.list[i];
                marker.overwrite_marker(item_ptr, marker_index);
                Some(marker.clone())
            }
            _ => {
                // create new marker
                Self::mark_position(&mut self.list, item_ptr, marker_index)
            }
        }
    }

    /// Same search as [MarkerList::find_marker] without touching the list,
    /// for readers that only hold the store read lock.
    pub fn find_readonly(&self, items: &ItemSpace, start: &ItemRef, index: u64) -> Option<SearchMarker> {
        if start.is_none() || index == 0 {
            return None;
        }

        let closest = Self::closest(&self.list, index);
        let (ptr, index) = Self::walk(items, closest.map(|i| &self.list[i]), start, index);
        Some(SearchMarker { ptr, index })
    }

    #[allow(dead_code)]
    pub fn get_last_marker(&self) -> Option<SearchMarker> {
        self.list.back().cloned()
    }

    pub fn replace_marker(&mut self, raw: ItemRef, new: ItemRef, len_shift: i64, new_indexable: bool) {
        let mut has_zero = false;
        let mut replaced = false;
        for marker in self.list.iter_mut() {
            if marker.ptr == raw {
                replaced = true;
                marker.ptr = new;
                let updated = (marker.index as i64) + len_shift;
                debug_assert!(updated >= 0, "marker index underflow on merge");
                marker.index = updated.max(0) as u64;
                if marker.index == 0 {
                    has_zero = true;
                }
            }
        }
        if replaced && !new_indexable {
            self.may_have_unindexed = true;
        }
        if has_zero {
            self.list.retain(|m| m.index > 0);
        }
    }

    /// Retargets all markers pointing at any item in the contiguous merged
    /// clock range `(head_clock, end_clock)` of `client` onto `head`, in O(80).
    /// Must be called before retiring the merged tail items.
    pub fn replace_marker_range(
        &mut self,
        items: &ItemSpace,
        client: Client,
        head_clock: Clock,
        end_clock: Clock,
        head: ItemRef,
        head_indexable: bool,
    ) {
        let mut has_zero = false;
        let mut replaced = false;
        for marker in self.list.iter_mut() {
            if let Some(item) = marker.ptr.and_then(|i| items.get(i))
                && item.id.client == client
                && item.id.clock > head_clock
                && item.id.clock < end_clock
            {
                replaced = true;
                marker.ptr = head;
                if head_indexable {
                    let delta = item.id.clock - head_clock;
                    debug_assert!(marker.index >= delta, "marker index underflow on range merge");
                    marker.index = marker.index.saturating_sub(delta);
                }
                if marker.index == 0 {
                    has_zero = true;
                }
            }
        }
        if replaced && !head_indexable {
            self.may_have_unindexed = true;
        }
        if has_zero {
            self.list.retain(|m| m.index > 0);
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(not(loom))]
    use rand::{RngExt, SeedableRng};
    #[cfg(not(loom))]
    use rand_chacha::ChaCha20Rng;

    use super::*;

    #[test]
    fn test_marker_list() {
        let options = DocOptions::default();
        let buffer = crate::doc::yjs_fixture("marker-array");

        loom_model!({
            let client_id = 101;

            let mut decoder = RawDecoder::new(&buffer);
            let update = Update::read(&mut decoder).unwrap();

            let mut doc = Doc::with_options(options.clone());
            doc.apply_update(update).unwrap();
            let array = doc.get_or_create_array("abc").unwrap();

            let mut marker_list = MarkerList::default();

            let marker = array
                .0
                .read(|store, ty| marker_list.find_marker(&store.type_arena.items, &ty.start, ty.len, 8))
                .unwrap()
                .unwrap();

            assert_eq!(marker.index, 2);
            assert_eq!(
                marker.ptr,
                doc.store
                    .read()
                    .unwrap()
                    .get_node(Id::new(client_id, 2))
                    .unwrap()
                    .as_item()
            );
        });
    }

    #[test]
    fn test_search_marker_flaky() {
        let options = DocOptions::default();

        loom_model!({
            let doc = Doc::with_options(options.clone());
            let mut text = doc.get_or_create_text("test").unwrap();
            text.insert(0, "0").unwrap();
            text.insert(1, "1").unwrap();
            text.insert(0, "0").unwrap();
        });
    }

    #[cfg(not(loom))]
    fn search_with_seed(seed: u64) {
        let rand = ChaCha20Rng::seed_from_u64(seed);
        let iteration = 20;

        let doc = Doc::with_client(1);
        let mut text = doc.get_or_create_text("test").unwrap();
        text.insert(0, "This is a string with length 32.").unwrap();
        let mut len = text.len();

        for i in 0..iteration {
            let mut rand: ChaCha20Rng = rand.clone();
            let pos = rand.random_range(0..text.len());
            let str = format!("hello {i}");
            len += str.len() as u64;
            text.insert(pos, str).unwrap();
        }

        assert_eq!(text.len(), len);
        assert_eq!(text.to_string().len() as u64, len);
    }

    #[test]
    #[cfg(not(loom))]
    fn test_marker_list_with_seed() {
        search_with_seed(785590655803394607);
        search_with_seed(12958877733367615);
        search_with_seed(71776330571528794);
        search_with_seed(2207805473582911);
    }

    #[cfg(not(loom))]
    fn assert_markers_match_linear_scan(doc: &Doc, text: &Text) {
        let store = doc.store.read().unwrap();
        let ty = &store.type_arena[text.0.id.unwrap()];
        let items = &store.type_arena.items;
        let Some(markers) = ty.markers.as_ref() else {
            return;
        };
        for marker in markers.iter() {
            assert!(marker.index > 0, "marker invariant violated: index == 0 ({marker:?})");
            let target = marker.ptr.expect("marker ptr must be Some");
            assert!(items.get(target).is_some(), "marker ptr {target:?} is dangling");
            let mut cur = ty.start;
            let mut seen_index = 0u64;
            let mut found = false;
            while let Some(idx) = cur {
                if idx == target {
                    assert_eq!(
                        seen_index, marker.index,
                        "marker index mismatch: marker={marker:?} linear_scan={seen_index}"
                    );
                    found = true;
                    break;
                }
                let item = items.get(idx).expect("live list item");
                if item.indexable() {
                    seen_index += item.len();
                }
                cur = item.right;
            }
            assert!(found, "marker ptr {target:?} not reachable from ty.start");
        }
    }

    #[test]
    #[cfg(not(loom))]
    fn transact_mut_sequential_append_linear() {
        let n = if cfg!(miri) { 100 } else { 50_000 };
        let doc = Doc::with_client(1);
        let text = doc.get_or_create_text("t").unwrap();
        doc.transact_mut(None, |tx| {
            let mut w = tx.text(&text)?;
            for i in 0..n {
                w.insert(i, "a")?;
            }
            Ok(())
        })
        .unwrap();
        assert_eq!(text.len(), n);
        assert_eq!(text.to_string().len() as u64, n);
        assert_markers_match_linear_scan(&doc, &text);
    }

    #[test]
    #[cfg(not(loom))]
    fn randomized_marker_invariants() {
        let steps = if cfg!(miri) { 30 } else { 400 };
        for auto_gc in [false, true] {
            let mut rng = ChaCha20Rng::seed_from_u64(0x5EED_CAFE_u64 ^ u64::from(auto_gc));
            let mut doc = DocOptions::new().with_client_id(1).auto_gc(auto_gc).build();
            let mut peer = DocOptions::new().with_client_id(2).auto_gc(auto_gc).build();
            let mut text = doc.get_or_create_text("t").unwrap();
            let mut peer_text = peer.get_or_create_text("t").unwrap();

            for step in 0..steps {
                match rng.random_range(0..6u8) {
                    // Single-op insert (commits and merges)
                    0 => {
                        let pos = rng.random_range(0..=text.len());
                        let s = if rng.random_bool(0.2) { "😀" } else { "xy" };
                        text.insert(pos, s).unwrap();
                    }
                    // Batch transact_mut inserts + deletes (exercises unmerged
                    // nodes + splits)
                    1 | 2 => {
                        let ops = rng.random_range(1..=12);
                        doc.transact_mut(None, |tx| {
                            let mut w = tx.text(&text)?;
                            for _ in 0..ops {
                                let len = w.len();
                                if len == 0 || rng.random_bool(0.7) {
                                    let pos = rng.random_range(0..=len);
                                    let s = match rng.random_range(0..3u8) {
                                        0 => "a",
                                        1 => "bc",
                                        _ => "中",
                                    };
                                    w.insert(pos, s)?;
                                } else {
                                    let pos = rng.random_range(0..len);
                                    let del = rng.random_range(1..=(len - pos).min(4));
                                    w.remove(pos, del)?;
                                }
                            }
                            Ok(())
                        })
                        .unwrap();
                    }
                    // Single-op delete (splits + tombstones + merges)
                    3 => {
                        let len = text.len();
                        if len > 0 {
                            let pos = rng.random_range(0..len);
                            let del = rng.random_range(1..=(len - pos).min(5));
                            text.remove(pos, del).unwrap();
                        }
                    }
                    // Explicit GC
                    4 => {
                        doc.gc().unwrap();
                    }
                    // Remote peer edit + sync
                    _ => {
                        let sv = peer.get_state_vector();
                        let u = doc.encode_state_as_update_v1(&sv).unwrap();
                        peer.apply_update_from_binary_v1(u).unwrap();
                        let pos = rng.random_range(0..=peer_text.len());
                        peer_text.insert(pos, format!("{step}")).unwrap();
                        let sv_doc = doc.get_state_vector();
                        let u2 = peer.encode_state_as_update_v1(&sv_doc).unwrap();
                        doc.apply_update_from_binary_v1(u2).unwrap();
                    }
                }
                assert_markers_match_linear_scan(&doc, &text);
            }
        }
    }

    #[test]
    #[cfg(not(loom))]
    fn update_marker_changes_evicts_preexisting_zero_index_and_tracks_unindexed() {
        let doc = Doc::with_client(1);
        let mut text = doc.get_or_create_text("t").unwrap();
        text.insert(0, "abcdefghij").unwrap();

        // Manually inject a pre-existing index == 0 marker while
        // may_have_unindexed is false, then call update_marker_changes with an
        // index > 0 so that marker is untouched by the shift branch.
        {
            let mut store = doc.store.write().unwrap();
            let ty_id = text.0.id.unwrap();
            let start = store.type_arena[ty_id].start;
            let (ty, items) = store.type_arena.type_and_items(ty_id);
            let markers = ty.markers.as_mut().unwrap();
            markers.clear();
            markers.list.push_back(SearchMarker::new(start, 0));
            assert!(!markers.may_have_unindexed);
            markers.update_marker_changes(items, 5, 2, None);
            assert!(
                markers.is_empty(),
                "pre-existing index == 0 marker must be evicted even on fast path"
            );
        }

        // Verify delete sets may_have_unindexed and subsequent insert clears it
        // after repairing.
        text.insert(4, "X").unwrap();
        text.insert(8, "Y").unwrap();
        text.remove(4, 1).unwrap();
        {
            let store = doc.store.read().unwrap();
            let ty = &store.type_arena[text.0.id.unwrap()];
            assert!(ty.markers.as_ref().unwrap().may_have_unindexed);
        }
        text.insert(4, "Z").unwrap();
        {
            let store = doc.store.read().unwrap();
            let ty = &store.type_arena[text.0.id.unwrap()];
            assert!(!ty.markers.as_ref().unwrap().may_have_unindexed);
        }
        assert_markers_match_linear_scan(&doc, &text);
    }

    #[test]
    #[cfg(not(loom))]
    fn replace_marker_range_updates_head_mid_tail_and_evicts_zero() {
        let doc = Doc::with_client(1);
        let text = doc.get_or_create_text("t").unwrap();
        // Create 5 separate contiguous string items in one transaction before
        // commit: clocks 0..2, 2..4, 4..6, 6..8, 8..10
        doc.transact_mut(None, |tx| {
            let mut w = tx.text(&text)?;
            w.insert(0, "aa")?;
            w.insert(2, "bb")?;
            w.insert(4, "cc")?;
            w.insert(6, "dd")?;
            w.insert(8, "ee")?;
            // Place markers directly on clock 2 (idx 2), clock 4 (idx 4), clock
            // 8 (idx 8) When merged into clock 0 (head_clock = 0), all shift by
            // -clock -> idx 0 -> evicted!
            let store = tx.store_mut();
            let ty_id = text.0.id.unwrap();
            let i2 = store.get_node((1, 2)).unwrap().as_item();
            let i4 = store.get_node((1, 4)).unwrap().as_item();
            let i8 = store.get_node((1, 8)).unwrap().as_item();
            let markers = store.type_arena[ty_id].markers.as_mut().unwrap();
            markers.clear();
            markers.list.push_back(SearchMarker::new(i2, 2));
            markers.list.push_back(SearchMarker::new(i4, 4));
            markers.list.push_back(SearchMarker::new(i8, 8));
            Ok(())
        })
        .unwrap();
        assert_eq!(text.to_string(), "aabbccddee");
        assert_eq!(doc.store.read().unwrap().items[&1].len(), 1);
        assert!(
            doc.store.read().unwrap().type_arena[text.0.id.unwrap()]
                .markers
                .as_ref()
                .unwrap()
                .is_empty(),
            "markers shifted to index 0 must be evicted"
        );

        // Now test markers that stay > 0 after range merge (prefix from another
        // client)
        let doc2 = Doc::with_client(2);
        let mut t2 = doc2.get_or_create_text("t").unwrap();
        t2.insert(0, "PREFIX").unwrap();
        let seed = doc2.encode_update_v1().unwrap();

        let mut doc3 = Doc::with_client(3);
        let t3 = doc3.get_or_create_text("t").unwrap();
        doc3.apply_update_from_binary_v1(&seed).unwrap();
        doc3.transact_mut(None, |tx| {
            let mut w = tx.text(&t3)?;
            w.insert(6, "aa")?; // clock 0..2, list index 6
            w.insert(8, "bb")?; // clock 2..4, list index 8
            w.insert(10, "cc")?; // clock 4..6, list index 10
            w.insert(12, "dd")?; // clock 6..8, list index 12
            let store = tx.store_mut();
            let ty_id = t3.0.id.unwrap();
            let i0 = store.get_node((3, 0)).unwrap().as_item();
            let i2 = store.get_node((3, 2)).unwrap().as_item();
            let i6 = store.get_node((3, 6)).unwrap().as_item();
            let markers = store.type_arena[ty_id].markers.as_mut().unwrap();
            markers.clear();
            markers.list.push_back(SearchMarker::new(i0, 6));
            markers.list.push_back(SearchMarker::new(i2, 8));
            markers.list.push_back(SearchMarker::new(i6, 12));
            Ok(())
        })
        .unwrap();
        assert_eq!(t3.to_string(), "PREFIXaabbccdd");
        assert_markers_match_linear_scan(&doc3, &t3);
        let store = doc3.store.read().unwrap();
        let head = store.get_node((3, 0)).unwrap().as_item();
        let markers = store.type_arena[t3.0.id.unwrap()].markers.as_ref().unwrap();
        assert_eq!(markers.len(), 3);
        for m in markers.iter() {
            assert_eq!(m.ptr, head);
            assert_eq!(m.index, 6);
        }
    }
}
