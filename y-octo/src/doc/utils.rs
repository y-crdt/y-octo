use super::*;

pub fn encode_awareness_as_message(awareness: AwarenessStates) -> JwstCodecResult<Vec<u8>> {
    let mut buffer = Vec::new();
    write_sync_message(&mut buffer, &SyncMessage::Awareness(awareness))
        .map_err(|e| JwstCodecError::InvalidWriteBuffer(e.to_string()))?;

    Ok(buffer)
}

pub fn encode_update_as_message(update: Vec<u8>) -> JwstCodecResult<Vec<u8>> {
    let mut buffer = Vec::new();
    write_sync_message(&mut buffer, &SyncMessage::Doc(DocMessage::Update(update)))
        .map_err(|e| JwstCodecError::InvalidWriteBuffer(e.to_string()))?;

    Ok(buffer)
}

/// Merges multiple V1 binary updates into a single [`Update`].
///
/// If any frame in the batch strips a validated historical zero-length item,
/// colliding-origin, overlap-slicing, same-clock successor, and reference
/// invariants are also enforced across both the raw decoded frames and the
/// normalized merged output. Per-frame validation remains intentionally strict
/// (for example, a tag-4 `ContentString("")` still requires strict raw
/// DeleteSet coverage within its own frame).
pub fn merge_updates_v1<V: AsRef<[u8]>, I: IntoIterator<Item = V>>(updates: I) -> JwstCodecResult<Update> {
    let mut decoded = Vec::new();
    let mut skipped_zero_origins = Vec::new();
    for raw in updates {
        let (update, frame_skipped) = Update::decode_v1_with_skipped_zero_origins(raw)?;
        if !frame_skipped.is_empty() {
            skipped_zero_origins.extend(frame_skipped);
        }
        decoded.push(update);
    }

    if skipped_zero_origins.is_empty() {
        return Ok(Update::merge(decoded));
    }

    let mut combined_ds = DeleteSet::default();
    for update in &decoded {
        combined_ds.merge(&update.delete_set);
        combined_ds.merge(&update.pending_delete_set);
    }

    let skipped_set: HashSet<Id> = skipped_zero_origins.iter().copied().collect();
    let mut skipped_by_client: ClientMap<Vec<u64>> = ClientMap::default();
    for ol in &skipped_set {
        skipped_by_client.entry(ol.client).or_default().push(ol.clock);
    }
    for clocks in skipped_by_client.values_mut() {
        clocks.sort_unstable();
    }

    let mut colliding_ids: HashSet<Id> = HashSet::default();
    for update in &decoded {
        validate_update_against_skipped_zeros(
            update,
            &skipped_set,
            &skipped_by_client,
            &combined_ds,
            &mut colliding_ids,
        )?;
    }
    if !colliding_ids.is_empty() && decoded.iter().any(|u| update_references_any(u, &colliding_ids)) {
        return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()));
    }

    let merged = Update::merge(decoded);
    validate_update_against_skipped_zeros(
        &merged,
        &skipped_set,
        &skipped_by_client,
        &combined_ds,
        &mut colliding_ids,
    )?;

    if !colliding_ids.is_empty()
        && (!colliding_ids.is_disjoint(&skipped_set) || update_references_any(&merged, &colliding_ids))
    {
        return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()));
    }

    Ok(merged)
}

#[cold]
#[inline(never)]
fn validate_update_against_skipped_zeros(
    update: &Update,
    skipped_set: &HashSet<Id>,
    skipped_by_client: &ClientMap<Vec<u64>>,
    combined_ds: &DeleteSet,
    colliding_ids: &mut HashSet<Id>,
) -> JwstCodecResult<()> {
    for structs in update.structs.values().chain(update.pending_structs.values()) {
        for wire in structs {
            let (wire_id, wire_len) = match wire {
                WireStruct::Gc { id, len } | WireStruct::Skip { id, len } => (*id, *len),
                WireStruct::Item(item) => (item.id, item.len),
            };
            if let Some(ol_clocks) = skipped_by_client.get(&wire_id.client) {
                let end = wire_id.clock.saturating_add(wire_len);
                let idx = ol_clocks.partition_point(|&c| c < wire_id.clock);
                if let Some(&ol_clk) = ol_clocks.get(idx)
                    && ol_clk.checked_add(1).is_some_and(|z_clk| z_clk < end)
                {
                    return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()));
                }
            }
            if let WireStruct::Item(item) = wire
                && let Some(ol) = item.origin_left_id
                && skipped_set.contains(&ol)
            {
                if item.id.client == ol.client && ol.clock.checked_add(1) == Some(item.id.clock) {
                    return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()));
                }
                let is_deleted = matches!(item.content, WireContent::Deleted(_))
                    || combined_ds
                        .get(&item.id.client)
                        .is_some_and(|r| r.contains(item.id.clock));
                if item.len != 1 || !is_deleted {
                    return Err(JwstCodecError::IncompleteDocument("zero-length struct".into()));
                }
                colliding_ids.insert(item.id);
            }
        }
    }
    Ok(())
}

#[cold]
#[inline(never)]
fn update_references_any(update: &Update, target_ids: &HashSet<Id>) -> bool {
    for structs in update.structs.values().chain(update.pending_structs.values()) {
        for wire in structs {
            if let WireStruct::Item(item) = wire {
                let refs = item.origin_left_id.is_some_and(|id| target_ids.contains(&id))
                    || item.origin_right_id.is_some_and(|id| target_ids.contains(&id))
                    || matches!(item.parent, Some(WireParent::Item(pid)) if target_ids.contains(&pid));
                if refs {
                    return true;
                }
            }
        }
    }
    false
}

/// Generate a uniform, nonzero client ID representable exactly by JavaScript.
#[cfg(feature = "random")]
pub fn random_client_id() -> u64 {
    rand::random_range(1..=(1_u64 << 53) - 1)
}
