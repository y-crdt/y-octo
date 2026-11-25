pub(in crate::doc) mod cleanup;
mod identity;
use std::{collections::BTreeMap, fmt::Display};

use cleanup::{FormatAttributes, cleanup_formatting_gap, equal_attrs};
pub use identity::TextIdentityRun;
pub(crate) use identity::identity_runs;

use super::{
    AsInner, Id,
    list::{ListIterator, ListType, check_remove, list_remove},
};
use crate::{
    Any, Content, JwstCodecError, JwstCodecResult,
    doc::{DocStore, ItemRef, ItemSpace, TypeIdx, YType},
    impl_type,
};

impl_type!(Text);

impl ListType for Text {}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
pub enum TextInsert {
    Text(String),
    Embed(Vec<Any>),
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
pub enum TextDeltaOp {
    Insert {
        insert: TextInsert,
        #[serde(skip_serializing_if = "Option::is_none")]
        format: Option<TextAttributes>,
    },
    Retain {
        retain: u64,
        #[serde(skip_serializing_if = "Option::is_none")]
        format: Option<TextAttributes>,
    },
    Delete {
        delete: u64,
    },
}

pub type TextDelta = Vec<TextDeltaOp>;
pub type TextAttributes = BTreeMap<String, Any>;

impl Text {
    #[inline]
    pub fn len(&self) -> u64 {
        self.content_len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn insert<T: ToString>(&mut self, char_index: u64, str: T) -> JwstCodecResult {
        self.insert_at(char_index, Content::String(str.to_string()))
    }

    pub fn insert_embed<V: Into<Any>>(&mut self, char_index: u64, embed: V) -> JwstCodecResult {
        let embed = embed.into();
        self.as_inner()
            .write(|store, ty| text_insert_embed(store, ty, char_index, embed))
    }

    pub fn format(&mut self, char_index: u64, len: u64, attrs: TextAttributes) -> JwstCodecResult {
        self.as_inner()
            .write(|store, ty| text_format(store, ty, char_index, len, attrs))
    }

    #[inline]
    pub fn remove(&mut self, char_index: u64, len: u64) -> JwstCodecResult {
        self.as_inner()
            .write(|store, ty| text_remove(store, ty, char_index, len))
    }

    pub fn to_delta(&self) -> TextDelta {
        crate::doc::or_released(
            self.as_inner()
                .read(|store, ty| text_delta(&store.type_arena.items, ty)),
        )
    }

    pub fn apply_delta(&mut self, delta: &[TextDeltaOp]) -> JwstCodecResult {
        self.as_inner().write(|store, ty| apply_text_delta(store, ty, delta))
    }
}

/// The caller holds the store lock.
pub(crate) fn text_delta(items: &ItemSpace, ty: &YType) -> TextDelta {
    let mut ops = Vec::new();
    let mut attrs = TextAttributes::new();

    for item in ListIterator::new(items, ty) {
        match &item.content {
            Content::Format(format) => {
                let (key, value) = (&format.key, &format.value);
                if is_nullish(value) {
                    attrs.remove(key.as_str());
                } else {
                    attrs.insert(key.to_string(), value.clone());
                }
            }
            Content::String(text) => {
                push_insert(&mut ops, TextInsert::Text(text.clone()), &attrs);
            }
            Content::Embed(embed) => {
                push_insert(&mut ops, TextInsert::Embed(vec![embed.as_ref().clone()]), &attrs);
            }
            Content::Any(any) => {
                push_insert(&mut ops, TextInsert::Embed(any.clone()), &attrs);
            }
            Content::Json(values) => {
                let converted = values
                    .iter()
                    .map(|value| value.as_ref().map(|s| Any::String(s.clone())).unwrap_or(Any::Undefined))
                    .collect::<Vec<_>>();
                push_insert(&mut ops, TextInsert::Embed(converted), &attrs);
            }
            Content::Binary(value) => {
                push_insert(&mut ops, TextInsert::Embed(vec![Any::Binary(value.clone())]), &attrs);
            }
            _ => {}
        }
    }

    ops
}

/// Validates that all `Retain` and `Delete` operations in `delta` stay within
/// a text sequence of `len` units before mutating the store.
pub(crate) fn validate_delta_against_len(len: u64, delta: &[TextDeltaOp]) -> JwstCodecResult {
    let mut remaining = len;
    for op in delta {
        match op {
            TextDeltaOp::Insert { .. } => {}
            TextDeltaOp::Retain { retain, .. } => {
                if *retain > remaining {
                    return Err(JwstCodecError::IndexOutOfBound(*retain));
                }
                remaining -= *retain;
            }
            TextDeltaOp::Delete { delete } => {
                if *delete > remaining {
                    return Err(JwstCodecError::IndexOutOfBound(*delete));
                }
                remaining -= *delete;
            }
        }
    }
    Ok(())
}

pub(crate) fn apply_text_delta(store: &mut DocStore, ty: TypeIdx, delta: &[TextDeltaOp]) -> JwstCodecResult {
    validate_delta_against_len(store.type_arena[ty].len, delta)?;
    {
        let mut pos = TextPosition::new(store.type_arena[ty].start);

        for op in delta {
            match op {
                TextDeltaOp::Insert { insert, format } => {
                    if matches!(insert, TextInsert::Text(text) if text.is_empty()) {
                        continue;
                    }
                    let attrs = format.clone().unwrap_or_default();
                    match insert {
                        TextInsert::Text(text) => {
                            insert_text_content(store, ty, &mut pos, Content::String(text.clone()), attrs)?;
                        }
                        TextInsert::Embed(values) => {
                            if values.is_empty() {
                                continue;
                            }
                            check_embed_insert_capacity(store, &pos, values.len(), &attrs)?;
                            for value in values {
                                insert_text_content(
                                    store,
                                    ty,
                                    &mut pos,
                                    Content::Embed(Box::new(value.clone())),
                                    attrs.clone(),
                                )?;
                            }
                        }
                    }
                }
                TextDeltaOp::Retain { retain, format } => {
                    let attrs = format.clone().unwrap_or_default();
                    if attrs.is_empty() {
                        advance_text_position(store, &mut pos, *retain)?;
                    } else {
                        format_text(store, ty, &mut pos, *retain, attrs)?;
                    }
                }
                TextDeltaOp::Delete { delete } => {
                    delete_text(store, ty, &mut pos, *delete)?;
                }
            }
        }

        Ok(())
    }
}

impl Display for Text {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&crate::doc::or_released(
            self.as_inner()
                .read(|store, ty| text_string(&store.type_arena.items, ty)),
        ))
    }
}

/// The plain string of a text type. The caller holds the store lock.
pub(crate) fn text_string(items: &ItemSpace, ty: &YType) -> String {
    let mut out = String::new();
    for item in ListIterator::new(items, ty) {
        if let Content::String(str) = &item.content {
            out.push_str(str);
        }
    }
    out
}

impl serde::Serialize for Text {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[derive(Clone)]
struct TextPosition {
    left: ItemRef,
    right: ItemRef,
    index: u64,
    attrs: FormatAttributes,
    // UTF-16 units retained inside right, until an edit needs a boundary.
    offset: u64,
}

impl TextPosition {
    fn new(right: ItemRef) -> Self {
        Self {
            left: None,
            right,
            index: 0,
            attrs: FormatAttributes::default(),
            offset: 0,
        }
    }

    /// Where `normalize` cuts the struct on the right of a position inside
    /// one: the first id of the right half.
    fn split(&self, items: &ItemSpace) -> Option<Id> {
        if self.offset == 0 {
            return None;
        }
        self.right
            .and_then(|right| items.get(right))
            .map(|right| right.id + self.offset)
    }

    fn normalize(&mut self, store: &mut DocStore) -> JwstCodecResult {
        if self.offset > 0 {
            let id = store
                .type_arena
                .items
                .get(self.right.expect("interior cursor"))
                .expect("live item")
                .id;
            let (left, right) = store.split_node(id, self.offset)?;
            self.left = left.as_item();
            self.right = right.as_item();
            self.index += std::mem::take(&mut self.offset);
        }
        Ok(())
    }

    fn forward(&mut self, items: &ItemSpace) {
        if let Some(right) = self.right.and_then(|i| items.get(i)) {
            if !right.deleted() {
                if let Some((key, value)) = right.content.as_format() {
                    if is_nullish(value) {
                        self.attrs.remove(key.as_str());
                    } else {
                        self.attrs.insert(key.to_string(), value.clone(), right.id);
                    }
                } else if right.countable() {
                    self.index += right.len();
                }
            }

            self.left = self.right;
            self.right = right.right;
        }
    }
}

fn is_nullish(value: &Any) -> bool {
    matches!(value, Any::Null | Any::Undefined)
}

fn push_insert(ops: &mut Vec<TextDeltaOp>, insert: TextInsert, attrs: &TextAttributes) {
    let format = if attrs.is_empty() { None } else { Some(attrs.clone()) };

    if let Some(TextDeltaOp::Insert {
        insert: TextInsert::Text(prev),
        format: prev_format,
    }) = ops.last_mut()
        && let TextInsert::Text(text) = insert
    {
        if prev_format.as_ref() == format.as_ref() {
            prev.push_str(&text);
            return;
        }
        ops.push(TextDeltaOp::Insert {
            insert: TextInsert::Text(text),
            format,
        });
        return;
    }

    ops.push(TextDeltaOp::Insert { insert, format });
}

fn advance_text_position(store: &DocStore, pos: &mut TextPosition, mut remaining: u64) -> JwstCodecResult {
    remaining += std::mem::take(&mut pos.offset);
    while remaining > 0 {
        let Some(item) = pos.right.and_then(|i| store.type_arena.items.get(i)) else {
            return Err(JwstCodecError::IndexOutOfBound(pos.index + remaining));
        };

        if item.deleted() {
            pos.forward(&store.type_arena.items);
            continue;
        }

        if matches!(item.content, Content::Format(_)) {
            pos.forward(&store.type_arena.items);
            continue;
        }

        let item_len = item.len();
        if remaining < item_len {
            pos.offset = remaining;
            break;
        }

        remaining -= item_len;
        pos.forward(&store.type_arena.items);
    }

    Ok(())
}

fn minimize_attribute_changes(store: &DocStore, pos: &mut TextPosition, attrs: &TextAttributes) {
    while let Some(item) = pos.right.and_then(|i| store.type_arena.items.get(i)) {
        if item.deleted() {
            pos.forward(&store.type_arena.items);
            continue;
        }

        if let Some((key, value)) = item.content.as_format() {
            let attr = attrs.get(key.as_str()).unwrap_or(&Any::Null);
            if equal_attrs(attr, value) {
                pos.forward(&store.type_arena.items);
                continue;
            }
        }

        break;
    }
}

fn insert_item(store: &mut DocStore, ty: TypeIdx, pos: &mut TextPosition, content: Content) -> JwstCodecResult {
    let item = store.create_item(content, pos.left, pos.right, Some(ty), None);
    let countable = item.countable();
    let clock_len = item.len();
    pos.right = store.integrate_item(item, 0, Some(ty))?;
    let (parent, items) = store.type_arena.type_and_items(ty);
    if let Some(markers) = &mut parent.markers
        && countable
    {
        markers.update_marker_changes(items, pos.index, clock_len as i64, pos.right);
    }
    pos.forward(&store.type_arena.items);

    Ok(())
}

fn insert_attributes(
    store: &mut DocStore,
    ty: TypeIdx,
    pos: &mut TextPosition,
    attrs: &TextAttributes,
) -> JwstCodecResult<TextAttributes> {
    let mut negated = TextAttributes::new();

    for (key, value) in attrs {
        let current = pos.attrs.get(key.as_str()).cloned().unwrap_or(Any::Null);
        if equal_attrs(&current, value) {
            continue;
        }

        negated.insert(key.to_string(), current);
        insert_item(store, ty, pos, Content::format(key.to_string(), value.clone()))?;
    }

    Ok(negated)
}

fn skip_negated_attributes(items: &ItemSpace, pos: &mut TextPosition, negated: &mut TextAttributes) {
    while let Some(item) = pos.right.and_then(|i| items.get(i)) {
        if item.deleted() {
            pos.forward(items);
            continue;
        }

        if let Some((key, value)) = item.content.as_format()
            && let Some(negated_value) = negated.get(key.as_str())
            && equal_attrs(negated_value, value)
        {
            negated.remove(key.as_str());
            pos.forward(items);
            continue;
        }

        break;
    }
}

fn insert_negated_attributes(
    store: &mut DocStore,
    ty: TypeIdx,
    pos: &mut TextPosition,
    mut negated: TextAttributes,
) -> JwstCodecResult {
    skip_negated_attributes(&store.type_arena.items, pos, &mut negated);
    for (key, value) in negated {
        insert_item(store, ty, pos, Content::format(key.to_string(), value))?;
    }

    Ok(())
}

fn check_embed_insert_capacity(
    store: &DocStore,
    pos: &TextPosition,
    count: usize,
    attrs: &TextAttributes,
) -> JwstCodecResult {
    if count <= 1 {
        return Ok(());
    }
    let items = &store.type_arena.items;
    let state = store.get_state(store.client());
    let max_attr_keys = attrs.len().saturating_add(pos.attrs.keys().count());
    let per_embed_slots = max_attr_keys.checked_mul(2).and_then(|n| n.checked_add(1));
    let fast_slots_ok = per_embed_slots
        .and_then(|per| per.checked_mul(count))
        .and_then(|total| total.checked_add(usize::from(pos.offset > 0)))
        .is_some_and(|total| items.check_capacity(total).is_ok() && store.blocks_fit(total));
    let fast_clocks_ok = (max_attr_keys as u64)
        .checked_mul(2)
        .and_then(|n| n.checked_add(1))
        .and_then(|per| per.checked_mul(count as u64))
        .and_then(|total| state.checked_add(total))
        .is_some();
    if fast_slots_ok && fast_clocks_ok {
        return Ok(());
    }

    let mut sim = pos.clone();
    let mut total_slots = usize::from(sim.offset > 0);
    let mut total_clocks = 0u64;
    for i in 0..count {
        let mut eff_attrs = attrs.clone();
        for key in sim.attrs.keys() {
            if !eff_attrs.contains_key(key.as_str()) {
                eff_attrs.insert(key.to_string(), Any::Null);
            }
        }
        if i == 0 && sim.offset > 0 {
            let opening = eff_attrs
                .iter()
                .filter(|(key, value)| {
                    let prev = sim.attrs.get(key.as_str()).unwrap_or(&Any::Null);
                    !equal_attrs(prev, value)
                })
                .count();
            let attr_items = opening.saturating_mul(2);
            total_slots = total_slots.saturating_add(1).saturating_add(attr_items);
            total_clocks = (attr_items as u64)
                .checked_add(1)
                .and_then(|step| total_clocks.checked_add(step))
                .ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
            sim.offset = 0;
        } else {
            minimize_attribute_changes(store, &mut sim, &eff_attrs);
            let mut closing: TextAttributes = eff_attrs
                .iter()
                .filter_map(|(key, value)| {
                    let prev = sim.attrs.get(key.as_str()).unwrap_or(&Any::Null);
                    (!equal_attrs(prev, value)).then(|| (key.clone(), prev.clone()))
                })
                .collect();
            let opening = closing.len();
            skip_negated_attributes(items, &mut sim, &mut closing);
            let attr_items = opening.saturating_add(closing.len());
            total_slots = total_slots.saturating_add(1).saturating_add(attr_items);
            total_clocks = (attr_items as u64)
                .checked_add(1)
                .and_then(|step| total_clocks.checked_add(step))
                .ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
        }
    }

    items.check_capacity(total_slots)?;
    store.check_blocks(
        store.client(),
        total_slots - usize::from(pos.offset > 0),
        &[pos.split(items)],
    )?;
    state
        .checked_add(total_clocks)
        .ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
    Ok(())
}

fn insert_text_content(
    store: &mut DocStore,
    ty: TypeIdx,
    pos: &mut TextPosition,
    content: Content,
    mut attrs: TextAttributes,
) -> JwstCodecResult {
    for key in pos.attrs.keys() {
        if !attrs.contains_key(key.as_str()) {
            attrs.insert(key.to_string(), Any::Null);
        }
    }

    minimize_attribute_changes(store, pos, &attrs);
    let items = &store.type_arena.items;
    let state = store.get_state(store.client());
    let content_clocks = content.clock_len();
    let slots = 1 + usize::from(pos.offset > 0);
    // With room for all opening and closing markers (both item slots and local
    // clocks) no further scan is needed.
    let fast_slots_ok = attrs
        .len()
        .checked_mul(2)
        .and_then(|n| slots.checked_add(n))
        .is_some_and(|n| items.check_capacity(n).is_ok() && store.blocks_fit(n));
    let fast_clocks_ok = (attrs.len() as u64)
        .checked_mul(2)
        .and_then(|c| content_clocks.checked_add(c))
        .and_then(|total| state.checked_add(total))
        .is_some();
    if !fast_slots_ok || !fast_clocks_ok {
        let mut closing: TextAttributes = attrs
            .iter()
            .filter_map(|(key, value)| {
                let prev = pos.attrs.get(key).unwrap_or(&Any::Null);
                (!equal_attrs(prev, value)).then(|| (key.clone(), prev.clone()))
            })
            .collect();
        let opening = closing.len();
        if pos.offset == 0 {
            skip_negated_attributes(items, &mut pos.clone(), &mut closing);
        }
        let attr_items = opening + closing.len();
        items.check_capacity(slots + attr_items)?;
        store.check_blocks(store.client(), 1 + attr_items, &[pos.split(items)])?;
        content_clocks
            .checked_add(attr_items as u64)
            .and_then(|total| state.checked_add(total))
            .ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
    }
    pos.normalize(store)?;
    let negated = insert_attributes(store, ty, pos, &attrs)?;
    insert_item(store, ty, pos, content)?;
    insert_negated_attributes(store, ty, pos, negated)?;

    Ok(())
}

fn check_format_capacity(
    store: &DocStore,
    pos: &TextPosition,
    remaining: u64,
    attrs: &TextAttributes,
) -> JwstCodecResult {
    let items = &store.type_arena.items;
    let state = store.get_state(store.client());
    let fast_slots_ok = attrs
        .len()
        .checked_mul(2)
        .and_then(|n| n.checked_add(2))
        .is_some_and(|n| items.check_capacity(n).is_ok() && store.blocks_fit(n));
    let fast_clocks_ok = (attrs.len() as u64)
        .checked_mul(2)
        .and_then(|total| state.checked_add(total))
        .is_some();
    if fast_slots_ok && fast_clocks_ok {
        return Ok(());
    }

    let mut sim = pos.clone();
    let start_split = usize::from(sim.offset > 0);
    let start_cut = sim.split(items);
    let mut end_cut = None;
    if sim.offset == 0 {
        minimize_attribute_changes(store, &mut sim, attrs);
    }
    let mut negated: TextAttributes = attrs
        .iter()
        .filter_map(|(key, value)| {
            let current = sim.attrs.get(key.as_str()).unwrap_or(&Any::Null);
            (!equal_attrs(current, value)).then(|| (key.clone(), current.clone()))
        })
        .collect();
    let opening = negated.len();

    let mut rem = remaining;
    let mut sim_offset = std::mem::take(&mut sim.offset);
    let mut end_split = 0usize;
    while let Some(item) = sim.right.and_then(|i| items.get(i)) {
        if rem == 0 && (negated.is_empty() || !item.deleted() && !matches!(item.content, Content::Format(_))) {
            break;
        }
        if item.deleted() {
            sim.forward(items);
            continue;
        }
        match &item.content {
            Content::Format(format) => {
                let (key, value) = (&format.key, &format.value);
                if let Some(attr) = attrs.get(key.as_str()) {
                    if equal_attrs(attr, value) {
                        negated.remove(key.as_str());
                    } else {
                        if rem == 0 {
                            break;
                        }
                        negated.insert(key.to_string(), value.clone());
                    }
                }
                sim.forward(items);
            }
            _ => {
                let skipped = std::mem::take(&mut sim_offset);
                let item_len = item.len() - skipped;
                if rem < item_len {
                    end_split = 1;
                    end_cut = Some(item.id + (skipped + rem));
                    break;
                }
                rem -= item_len;
                sim.forward(items);
            }
        }
    }
    if end_split == 0 {
        skip_negated_attributes(items, &mut sim, &mut negated);
    }

    let attr_items = opening + negated.len();
    items.check_capacity(start_split + end_split + attr_items)?;
    store.check_blocks(store.client(), attr_items, &[start_cut, end_cut])?;
    state
        .checked_add(attr_items as u64)
        .ok_or_else(|| JwstCodecError::IncompleteDocument("struct clock overflow".into()))?;
    Ok(())
}

fn format_text(
    store: &mut DocStore,
    ty: TypeIdx,
    pos: &mut TextPosition,
    mut remaining: u64,
    attrs: TextAttributes,
) -> JwstCodecResult {
    if remaining == 0 {
        return Ok(());
    }

    check_format_capacity(store, pos, remaining, &attrs)?;
    pos.normalize(store)?;
    minimize_attribute_changes(store, pos, &attrs);
    let mut negated = insert_attributes(store, ty, pos, &attrs)?;

    while let Some(item) = pos.right.and_then(|i| store.type_arena.items.get(i)) {
        // Yjs also scans trailing formats/tombstones while attributes still
        // need negating, but never crosses the next live content item.
        if remaining == 0 && (negated.is_empty() || !item.deleted() && !matches!(item.content, Content::Format(_))) {
            break;
        }
        if item.deleted() {
            pos.forward(&store.type_arena.items);
            continue;
        }

        match &item.content {
            Content::Format(format) => {
                let (key, value) = (&format.key, &format.value);
                if let Some(attr) = attrs.get(key.as_str()) {
                    if equal_attrs(attr, value) {
                        negated.remove(key.as_str());
                    } else {
                        if remaining == 0 {
                            break;
                        }
                        negated.insert(key.to_string(), value.clone());
                    }
                    store.delete_item(pos.right.expect("current format"), Some(ty));
                    pos.forward(&store.type_arena.items);
                } else {
                    pos.forward(&store.type_arena.items);
                }
            }
            _ => {
                let item_len = item.len();
                if remaining < item_len {
                    store.split_node(item.id, remaining)?;
                    remaining = 0;
                } else {
                    remaining -= item_len;
                }
                pos.forward(&store.type_arena.items);
            }
        }
    }

    insert_negated_attributes(store, ty, pos, negated)?;

    Ok(())
}

fn delete_text(store: &mut DocStore, ty: TypeIdx, pos: &mut TextPosition, mut remaining: u64) -> JwstCodecResult {
    if remaining == 0 {
        return Ok(());
    }

    check_remove(
        store,
        pos.right,
        pos.offset,
        remaining,
        pos.split(&store.type_arena.items),
    )?;
    pos.normalize(store)?;
    let start = remaining;
    let gap_start = pos.right;
    let start_attrs = pos.attrs.clone();

    while remaining > 0 {
        let item_ref = pos.right;
        let Some((indexable, item_len, item_id)) = item_ref
            .and_then(|i| store.type_arena.items.get(i))
            .map(|item| (item.indexable(), item.len(), item.id))
        else {
            break;
        };

        if indexable {
            if remaining < item_len {
                store.split_node(item_id, remaining)?;
                remaining = 0;
            } else {
                remaining -= item_len;
            }

            if let Some(item) = item_ref {
                store.delete_item(item, Some(ty));
            }
        }

        pos.forward(&store.type_arena.items);
    }

    if gap_start.is_some() {
        cleanup_formatting_gap(store, ty, gap_start, &pos.right, &start_attrs, &mut pos.attrs);
    }
    let (parent, items) = store.type_arena.type_and_items(ty);
    if let Some(markers) = &mut parent.markers {
        markers.update_marker_changes(items, pos.index, -((start - remaining) as i64), None);
    }

    Ok(())
}

/// The public text deletion path, shared by implicit and explicit transactions.
pub(crate) fn text_remove(store: &mut DocStore, ty: TypeIdx, index: u64, len: u64) -> JwstCodecResult {
    let text = &store.type_arena[ty];
    if !text.has_formatting {
        return list_remove(store, ty, index, len);
    }
    if len == 0 || text.len == 0 {
        return Ok(());
    }
    if index >= text.len {
        return Err(JwstCodecError::IndexOutOfBound(index));
    }
    let mut pos = TextPosition::new(text.start);
    advance_text_position(store, &mut pos, index)?;
    delete_text(store, ty, &mut pos, len)
}

/// Applies formatting attributes over `char_index..char_index + len`.
pub(crate) fn text_format(
    store: &mut DocStore,
    ty: TypeIdx,
    char_index: u64,
    len: u64,
    attrs: TextAttributes,
) -> JwstCodecResult {
    if char_index > store.type_arena[ty].len {
        return Err(JwstCodecError::IndexOutOfBound(char_index));
    }
    if len == 0 || attrs.is_empty() {
        return Ok(());
    }
    let mut ops = Vec::with_capacity(2);
    if char_index > 0 {
        ops.push(TextDeltaOp::Retain {
            retain: char_index,
            format: None,
        });
    }
    ops.push(TextDeltaOp::Retain {
        retain: len,
        format: Some(attrs),
    });
    apply_text_delta(store, ty, &ops)
}

/// Inserts an embed value at `char_index`.
pub(crate) fn text_insert_embed(store: &mut DocStore, ty: TypeIdx, char_index: u64, embed: Any) -> JwstCodecResult {
    super::list::list_insert(store, ty, char_index, Content::Embed(Box::new(embed)))
}

#[cfg(test)]
mod tests {
    use rand::{RngExt, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    use super::{TextAttributes, TextDeltaOp, TextInsert};
    #[cfg(not(loom))]
    use crate::sync::{Arc, AtomicUsize, Ordering};
    use crate::{Any, Doc, loom_model, sync::thread};

    #[test]
    fn test_manipulate_text() {
        loom_model!({
            let doc = Doc::new();
            let mut text = doc.create_text().unwrap();

            text.insert(0, "llo").unwrap();
            text.insert(0, "he").unwrap();
            text.insert(5, " world").unwrap();
            text.insert(6, "great ").unwrap();
            text.insert(17, '!').unwrap();

            assert_eq!(text.to_string(), "hello great world!");
            assert_eq!(text.len(), 18);

            text.remove(4, 4).unwrap();
            assert_eq!(text.to_string(), "helleat world!");
            assert_eq!(text.len(), 14);
        });
    }

    #[test]
    #[cfg(not(loom))]
    fn test_insert_before_leading_tombstone_converges() {
        fn sync(from: &Doc, to: &mut Doc) {
            let sv = to.get_state_vector();
            let update = from.encode_state_as_update_v1(&sv).unwrap();
            to.apply_update_from_binary_v1(update).unwrap();
        }

        // ascending client IDs (0 is unassigned without the random feature)
        let c0 = Doc::with_client(10);
        let mut t0 = c0.get_or_create_text("text").unwrap();
        let mut c1 = Doc::with_client(11);
        let mut t1 = c1.get_or_create_text("text").unwrap();
        let mut c2 = Doc::with_client(12);
        let mut t2 = c2.get_or_create_text("text").unwrap();

        t0.insert(0, "a").unwrap();
        sync(&c0, &mut c1);
        t1.insert(1, "b").unwrap();

        t0.insert(1, "c").unwrap();
        t0.remove(0, 1).unwrap();

        sync(&c0, &mut c2);
        t2.insert(0, "d").unwrap();

        sync(&c1, &mut c2);
        sync(&c2, &mut c1);

        let s1 = t1.to_string();
        let s2 = t2.to_string();
        assert_eq!(s1, s2, "c1 and c2 diverged: {s1:?} vs {s2:?}");
    }

    #[test]
    #[cfg(not(loom))]
    fn test_parallel_insert_text() {
        let seed = rand::rng().random();
        let rand = ChaCha20Rng::seed_from_u64(seed);
        let mut handles = Vec::new();

        let doc = Doc::with_client(1);
        let mut text = doc.get_or_create_text("test").unwrap();
        text.insert(0, "This is a string with length 32.").unwrap();

        let added_len = Arc::new(AtomicUsize::new(32));

        // parallel editing text
        {
            for i in 0..2 {
                let mut text = text.clone();
                let mut rand = rand.clone();
                let len = added_len.clone();

                handles.push(thread::spawn(move || {
                    for j in 0..10 {
                        let pos = rand.random_range(0..text.len());
                        let string = format!("hello {}", i * j);

                        text.insert(pos, &string).unwrap();

                        len.fetch_add(string.len(), Ordering::SeqCst);
                    }
                }));
            }
        }

        // parallel editing doc
        {
            for i in 0..2 {
                let doc = doc.clone();
                let mut rand = rand.clone();
                let len = added_len.clone();

                handles.push(thread::spawn(move || {
                    let mut text = doc.get_or_create_text("test").unwrap();
                    for j in 0..10 {
                        let pos = rand.random_range(0..text.len());
                        let string = format!("hello doc{}", i * j);

                        text.insert(pos, &string).unwrap();

                        len.fetch_add(string.len(), Ordering::SeqCst);
                    }
                }));
            }
        }

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(text.to_string().len(), added_len.load(Ordering::SeqCst));
        assert_eq!(text.len(), added_len.load(Ordering::SeqCst) as u64);
    }

    #[cfg(not(loom))]
    fn parallel_ins_del_text(seed: u64, thread: i32, iteration: i32) {
        let doc = Doc::with_client(1);
        let rand = ChaCha20Rng::seed_from_u64(seed);
        let mut text = doc.get_or_create_text("test").unwrap();
        text.insert(0, "This is a string with length 32.").unwrap();

        let mut handles = Vec::new();
        let len = Arc::new(AtomicUsize::new(32));

        for i in 0..thread {
            let len = len.clone();
            let mut rand = rand.clone();
            let text = text.clone();
            handles.push(thread::spawn(move || {
                for j in 0..iteration {
                    let len = len.clone();
                    let mut text = text.clone();
                    let ins = i % 2 == 0;
                    let pos = rand.random_range(0..16);

                    if ins {
                        let str = format!("hello {}", i * j);
                        text.insert(pos, &str).unwrap();

                        len.fetch_add(str.len(), Ordering::SeqCst);
                    } else {
                        text.remove(pos, 6).unwrap();

                        len.fetch_sub(6, Ordering::SeqCst);
                    }
                }
            }));
        }

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(text.to_string().len(), len.load(Ordering::SeqCst));
        assert_eq!(text.len(), len.load(Ordering::SeqCst) as u64);
    }

    #[test]
    #[cfg(not(loom))]
    fn test_parallel_ins_del_text() {
        // cases that ever broken
        // wrong left/right ref
        parallel_ins_del_text(973078538, 2, 2);
        parallel_ins_del_text(18414938500869652479, 2, 2);
    }

    #[test]
    fn loom_parallel_ins_del_text() {
        let seed = rand::rng().random();
        let mut rand = ChaCha20Rng::seed_from_u64(seed);
        let ranges = (0..20).map(|_| rand.random_range(0..16)).collect::<Vec<_>>();

        loom_model!({
            let doc = Doc::new();
            let mut text = doc.get_or_create_text("test").unwrap();
            text.insert(0, "This is a string with length 32.").unwrap();

            // enough for loom
            let handles = (0..2)
                .map(|i| {
                    let text = text.clone();
                    let ranges = ranges.clone();
                    thread::spawn(move || {
                        let mut text = text.clone();
                        let ins = i % 2 == 0;
                        let pos = ranges[i];

                        if ins {
                            let str = format!("hello {}", i);
                            text.insert(pos, &str).unwrap();
                        } else {
                            text.remove(pos, 6).unwrap();
                        }
                    })
                })
                .collect::<Vec<_>>();

            for handle in handles {
                handle.join().unwrap();
            }
        });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_recover_from_yjs_encoder() {
        let binary = crate::doc::yjs_fixture("text-recovery");
        loom_model!({
            let doc = Doc::try_from_binary_v1(&binary).unwrap();
            let mut text = doc.get_or_create_text("greating").unwrap();

            assert_eq!(text.to_string(), "hello world");

            text.insert(6, "great ").unwrap();
            text.insert(17, '!').unwrap();
            assert_eq!(text.to_string(), "hello great world!");
        });
    }

    #[test]
    fn test_recover_from_octobase_encoder() {
        loom_model!({
            let binary = {
                let doc = Doc::new();
                let mut text = doc.get_or_create_text("greating").unwrap();
                text.insert(0, "hello").unwrap();
                text.insert(5, " world!").unwrap();
                text.remove(11, 1).unwrap();

                doc.encode_update_v1().unwrap()
            };

            let doc = Doc::try_from_binary_v1_with_options(binary, crate::DocOptions::new().with_client_id(2)).unwrap();
            let mut text = doc.get_or_create_text("greating").unwrap();

            assert_eq!(text.to_string(), "hello world");

            text.insert(6, "great ").unwrap();
            text.insert(17, '!').unwrap();
            assert_eq!(text.to_string(), "hello great world!");
        });
    }

    #[test]
    fn test_text_delta_insert_format() {
        loom_model!({
            let doc = Doc::new();
            let mut text = doc.get_or_create_text("text").unwrap();

            let mut attrs = TextAttributes::new();
            attrs.insert("bold".to_string(), Any::True);

            text.apply_delta(&[TextDeltaOp::Insert {
                insert: TextInsert::Text("abc".to_string()),
                format: Some(attrs.clone()),
            }])
            .unwrap();

            assert_eq!(text.to_string(), "abc");
            assert_eq!(
                text.to_delta(),
                vec![TextDeltaOp::Insert {
                    insert: TextInsert::Text("abc".to_string()),
                    format: Some(attrs),
                }]
            );
        });
    }

    #[test]
    fn test_text_delta_retain_format() {
        loom_model!({
            let doc = Doc::new();
            let mut text = doc.get_or_create_text("text").unwrap();

            text.apply_delta(&[TextDeltaOp::Insert {
                insert: TextInsert::Text("abc".to_string()),
                format: None,
            }])
            .unwrap();

            let mut attrs = TextAttributes::new();
            attrs.insert("bold".to_string(), Any::True);

            text.apply_delta(&[TextDeltaOp::Retain {
                retain: 1,
                format: Some(attrs.clone()),
            }])
            .unwrap();

            assert_eq!(
                text.to_delta(),
                vec![
                    TextDeltaOp::Insert {
                        insert: TextInsert::Text("a".to_string()),
                        format: Some(attrs),
                    },
                    TextDeltaOp::Insert {
                        insert: TextInsert::Text("bc".to_string()),
                        format: None,
                    }
                ]
            );
        });
    }

    #[test]
    fn test_text_delta_utf16_retain() {
        loom_model!({
            let doc = Doc::new();
            let mut text = doc.get_or_create_text("text").unwrap();

            text.apply_delta(&[TextDeltaOp::Insert {
                insert: TextInsert::Text("😀".to_string()),
                format: None,
            }])
            .unwrap();

            let mut attrs = TextAttributes::new();
            attrs.insert("bold".to_string(), Any::True);

            text.apply_delta(&[TextDeltaOp::Retain {
                retain: 2,
                format: Some(attrs.clone()),
            }])
            .unwrap();

            assert_eq!(
                text.to_delta(),
                vec![TextDeltaOp::Insert {
                    insert: TextInsert::Text("😀".to_string()),
                    format: Some(attrs.clone()),
                }]
            );
            let runs = text.identity_runs().unwrap();
            assert_eq!(runs.len(), 1);
            assert_eq!(runs[0].attributes, attrs);
            assert_eq!(runs[0].insert, TextInsert::Text("😀".into()));
            assert_eq!(text.identity().unwrap(), crate::TypeIdentity::Root("text".into()));
            let mut decoded = Doc::with_client(77);
            decoded
                .apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
                .unwrap();
            let restored = decoded.get_or_create_text("text").unwrap();
            assert_eq!(restored.identity().unwrap(), text.identity().unwrap());
            assert_eq!(restored.identity_runs().unwrap(), runs);
            text.insert(2, "tail").unwrap();
            let tail = text.identity_runs().unwrap().last().unwrap().id;
            text.remove(2, 1).unwrap();
            doc.gc().unwrap();
            let surviving = text.identity_runs().unwrap();
            assert_eq!(surviving[0].id, runs[0].id);
            assert_eq!(surviving[1].id, tail + 1);
            assert!(
                doc.get_delete_sets()
                    .iter()
                    .any(|(client, ranges)| *client == tail.client && ranges.contains(tail.clock))
            );
        });
        loom_model!({
            let doc = Doc::new();
            let mut parent = doc.get_or_create_map("parent").unwrap();
            let nested = doc.create_text().unwrap();
            parent
                .insert("text".into(), crate::Value::Text(nested.clone()))
                .unwrap();
            let old_identity = nested.identity().unwrap();
            let replacement = doc.create_text().unwrap();
            parent
                .insert("text".into(), crate::Value::Text(replacement.clone()))
                .unwrap();
            assert_ne!(old_identity, replacement.identity().unwrap());
            let mut decoded = Doc::with_client(78);
            decoded
                .apply_update_from_binary_v1(doc.encode_update_v1().unwrap())
                .unwrap();
            let restored = decoded
                .get_map("parent")
                .unwrap()
                .get("text")
                .unwrap()
                .to_text()
                .unwrap();
            assert_eq!(restored.identity().unwrap(), replacement.identity().unwrap());
        });
    }
}
