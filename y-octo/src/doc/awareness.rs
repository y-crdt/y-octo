use std::{cmp::max, collections::hash_map::Entry};

use super::*;
use crate::sync::Arc;

pub type AwarenessCallback = Arc<dyn Fn(&Awareness, AwarenessEvent) + Send + Sync + 'static>;

/// Presence states of the peers of one document, exchanged like the
/// `y-protocols` awareness protocol.
///
/// The local identity is authoritative, which deliberately differs from
/// `y-protocols`: its `Awareness` starts with a `{}` local state and its
/// `applyAwarenessUpdate` only refuses remote `null` removals of the local
/// client, so a remote update with a higher clock can still replace the local
/// state. Here the local state starts unset (`None`), and remote updates for
/// `local_id` never create or replace it, before or after the first
/// [Awareness::set_local_state]; they only raise the clock the local state is
/// broadcast with, so the local state wins on every peer. With distinct client
/// IDs per replica, as Yjs requires, both behave the same.
pub struct Awareness {
    awareness: AwarenessStates,
    callback: Option<AwarenessCallback>,
    local_id: u64,
    /// Highest clock remote peers claimed for `local_id` before a local state
    /// existed; the first local state starts above it so peers accept it.
    local_clock_floor: u64,
}

impl Awareness {
    /// Creates an awareness for `local_id` without a local state.
    pub fn new(local_id: u64) -> Self {
        Self {
            awareness: AwarenessStates::new(),
            callback: None,
            local_id,
            local_clock_floor: 0,
        }
    }

    pub fn local_id(&self) -> u64 {
        self.local_id
    }

    pub fn on_update(&mut self, f: impl Fn(&Awareness, AwarenessEvent) + Send + Sync + 'static) {
        self.callback = Some(Arc::new(f));
    }

    pub fn get_states(&self) -> &AwarenessStates {
        &self.awareness
    }

    pub fn get_local_state(&self) -> Option<String> {
        self.awareness.get(&self.local_id).map(|state| state.content.clone())
    }

    fn mut_local_state(&mut self) -> &mut AwarenessState {
        let floor = self.local_clock_floor;
        self.awareness
            .entry(self.local_id)
            .or_insert_with(|| AwarenessState::new(floor, "null".to_string()))
    }

    pub fn set_local_state(&mut self, content: String) {
        self.mut_local_state().set_content(content);
        if let Some(cb) = self.callback.as_ref() {
            cb(self, AwarenessEventBuilder::new().update(self.local_id).build());
        }
    }

    pub fn clear_local_state(&mut self) {
        self.mut_local_state().delete();
        if let Some(cb) = self.callback.as_ref() {
            cb(self, AwarenessEventBuilder::new().remove(self.local_id).build());
        }
    }

    /// Rotates the local client ID (for example after `Doc::client_required()`
    /// detects a client ID collision on a host without `random`).
    ///
    /// Marks the old local ID as offline (`"null"`) and, if the local client
    /// currently holds an active state, re-announces that state under
    /// `new_local_id` with a clock strictly greater than any known state for
    /// `new_local_id`. Returns the resulting [`AwarenessEvent`].
    pub fn set_local_id(&mut self, new_local_id: u64) -> AwarenessEvent {
        let mut event = AwarenessEventBuilder::new();
        if new_local_id == self.local_id {
            return event.build();
        }

        let old_id = self.local_id;
        let old_active_content = self
            .awareness
            .get(&old_id)
            .filter(|state| !state.is_deleted())
            .map(|state| state.content.clone());

        if let Some(old_state) = self.awareness.get_mut(&old_id)
            && !old_state.is_deleted()
        {
            old_state.delete();
            event.remove(old_id);
        }

        self.local_id = new_local_id;
        self.local_clock_floor = self.awareness.get(&new_local_id).map(|state| state.clock).unwrap_or(0);

        if let Some(content) = old_active_content {
            let existed = self.awareness.contains_key(&new_local_id);
            self.mut_local_state().set_content(content);
            if existed {
                event.update(new_local_id);
            } else {
                event.add(new_local_id);
            }
        }

        let built = event.build();
        if !built.is_empty()
            && let Some(cb) = self.callback.as_ref()
        {
            cb(self, built.clone());
        }
        built
    }

    /// Encodes the selected client states (or all known states when `clients`
    /// is `None`) in `y-protocols` awareness binary format (without the outer
    /// `DocMessage::Awareness` tag).
    pub fn encode_update(&self, clients: Option<&[u64]>) -> JwstCodecResult<Vec<u8>> {
        let subset: AwarenessStates = match clients {
            Some(ids) => ids
                .iter()
                .filter_map(|id| self.awareness.get(id).map(|s| (*id, s.clone())))
                .collect(),
            None => self.awareness.clone(),
        };
        let mut buf = Vec::new();
        crate::protocol::write_awareness(&mut buf, &subset)
            .map_err(|e| JwstCodecError::InvalidWriteBuffer(e.to_string()))?;
        Ok(buf)
    }

    /// Decodes a `y-protocols` awareness binary update (without the outer
    /// `DocMessage::Awareness` tag) and applies it, returning the event.
    pub fn apply_update_v1(&mut self, bytes: &[u8]) -> JwstCodecResult<AwarenessEvent> {
        let (tail, states) = crate::protocol::read_awareness(bytes)
            .map_err(|e| JwstCodecError::IncompleteDocument(format!("invalid awareness update: {e}")))?;
        if !tail.is_empty() {
            return Err(JwstCodecError::UpdateNotFullyConsumed(tail.len()));
        }
        Ok(self.apply_update_returning_event(states))
    }

    /// Applies remote states, keeping each one newer than the known state
    /// (and accepting equal-clock `null` offline broadcasts from
    /// `y-protocols@1.0.6`).
    ///
    /// States for `local_id` are never stored, unlike `y-protocols`
    /// `applyAwarenessUpdate`: they only raise the clock of the local state
    /// so its next broadcast supersedes them.
    pub fn apply_update(&mut self, update: AwarenessStates) {
        let _ = self.apply_update_returning_event(update);
    }

    fn apply_update_returning_event(&mut self, update: AwarenessStates) -> AwarenessEvent {
        let mut event = AwarenessEventBuilder::new();

        for (client_id, state) in update {
            match self.awareness.entry(client_id) {
                Entry::Occupied(mut entry) => {
                    let prev_state = entry.get_mut();
                    if client_id == self.local_id {
                        // ignore remote update about local client and
                        // add clock to overwrite remote data
                        prev_state.set_clock(max(prev_state.clock, state.clock).saturating_add(1));
                        event.update(client_id);
                        continue;
                    }

                    let equal_clock_offline =
                        prev_state.clock == state.clock && state.is_deleted() && !prev_state.is_deleted();
                    if prev_state.clock < state.clock || equal_clock_offline {
                        let was_deleted = prev_state.is_deleted();
                        let now_deleted = state.is_deleted();
                        *prev_state = state;
                        if now_deleted {
                            if !was_deleted {
                                event.remove(client_id);
                            }
                        } else {
                            event.update(client_id);
                        }
                    }
                }
                Entry::Vacant(_) if client_id == self.local_id => {
                    // Remote peers may not author the local state, even before
                    // it is set; only keep its clock so the first local state
                    // overrides theirs.
                    self.local_clock_floor = max(self.local_clock_floor, state.clock);
                }
                Entry::Vacant(entry) => {
                    let is_deleted = state.is_deleted();
                    entry.insert(state);
                    if !is_deleted {
                        event.add(client_id);
                    }
                }
            }
        }

        let built = event.build();
        if let Some(cb) = self.callback.as_ref() {
            cb(self, built.clone());
        }
        built
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AwarenessEvent {
    added: Vec<u64>,
    updated: Vec<u64>,
    removed: Vec<u64>,
}

impl AwarenessEvent {
    pub fn added(&self) -> &[u64] {
        &self.added
    }

    pub fn updated(&self) -> &[u64] {
        &self.updated
    }

    pub fn removed(&self) -> &[u64] {
        &self.removed
    }

    pub fn is_empty(&self) -> bool {
        self.added.is_empty() && self.updated.is_empty() && self.removed.is_empty()
    }

    pub fn get_updated(&self, states: &AwarenessStates) -> AwarenessStates {
        states
            .iter()
            .filter(|(id, _)| self.added.contains(id) || self.updated.contains(id) || self.removed.contains(id))
            .map(|(id, state)| (*id, state.clone()))
            .collect()
    }
}

struct AwarenessEventBuilder {
    added: Vec<u64>,
    updated: Vec<u64>,
    removed: Vec<u64>,
}

impl AwarenessEventBuilder {
    fn new() -> Self {
        Self {
            added: Vec::new(),
            updated: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn add(&mut self, client_id: u64) -> &mut Self {
        self.added.push(client_id);
        self
    }

    fn update(&mut self, client_id: u64) -> &mut Self {
        self.updated.push(client_id);
        self
    }

    fn remove(&mut self, client_id: u64) -> &mut Self {
        self.removed.push(client_id);
        self
    }

    fn build(&mut self) -> AwarenessEvent {
        AwarenessEvent {
            added: self.added.clone(),
            updated: self.updated.clone(),
            removed: self.removed.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sync::{Mutex, MutexGuard};

    #[test]
    fn test_awareness() {
        loom_model!({
            let mut awareness = Awareness::new(0);

            {
                // init state
                assert_eq!(awareness.local_id, 0);
                assert_eq!(awareness.awareness.len(), 0);
            }

            {
                // local state
                awareness.set_local_state("test".to_string());
                assert_eq!(awareness.get_local_state(), Some("test".to_string()));
                awareness.clear_local_state();
                assert_eq!(awareness.get_local_state(), Some("null".to_string()));
            }

            {
                // apply remote update
                let mut states = AwarenessStates::new();
                states.insert(0, AwarenessState::new(2, "test0".to_string()));
                states.insert(1, AwarenessState::new(2, "test1".to_string()));
                awareness.apply_update(states);
                assert!(awareness.get_states().contains_key(&1));

                // local state will not apply
                assert_eq!(awareness.get_states().get(&0).unwrap().content, "null".to_string());
                assert_eq!(awareness.get_states().get(&1).unwrap().content, "test1".to_string());
            }

            {
                // callback
                let values: Arc<Mutex<Vec<AwarenessEvent>>> = Arc::new(Mutex::new(Vec::new()));
                let callback_values = Arc::clone(&values);
                awareness.on_update(move |_, event| {
                    let mut values = callback_values.lock().unwrap();
                    values.push(event);
                });

                let mut new_states = AwarenessStates::new();
                // exists in local awareness: update
                new_states.insert(1, AwarenessState::new(3, "test update".to_string()));
                // not exists in local awareness: add
                new_states.insert(2, AwarenessState::new(1, "test update".to_string()));
                // not exists in local awareness and null: tombstone only, no
                // added event
                new_states.insert(3, AwarenessState::new(1, "null".to_string()));
                // not exists in local awareness: add
                new_states.insert(4, AwarenessState::new(1, "test update".to_string()));
                awareness.apply_update(new_states);

                let mut new_states = AwarenessStates::new();
                // exists in local awareness: delete
                new_states.insert(4, AwarenessState::new(2, "null".to_string()));
                awareness.apply_update(new_states);

                awareness.set_local_state("test".to_string());
                awareness.clear_local_state();

                let values: MutexGuard<Vec<AwarenessEvent>> = values.lock().unwrap();
                assert_eq!(values.len(), 4);
                let event = values.first().unwrap();

                let mut added = event.added.clone();
                added.sort();
                assert_eq!(added, [2, 4]);
                assert!(awareness.get_states().get(&3).unwrap().is_deleted());
                assert_eq!(event.updated, [1]);

                assert_eq!(
                    event.get_updated(awareness.get_states()).get(&1).unwrap(),
                    &AwarenessState::new(3, "test update".to_string())
                );

                let event = values.get(1).unwrap();
                assert_eq!(event.removed, [4]);

                let event = values.get(2).unwrap();
                assert_eq!(event.updated, [0]);

                let event = values.get(3).unwrap();
                assert_eq!(event.removed, [0]);
            }
        });
    }

    #[test]
    fn test_awareness_rejects_remote_local_state() {
        let mut awareness = Awareness::new(7);

        // a peer claims the local client before it set any state
        let mut states = AwarenessStates::new();
        states.insert(7, AwarenessState::new(u64::MAX - 1, "forged".to_string()));
        awareness.apply_update(states);
        assert_eq!(awareness.get_local_state(), None);

        // the first local state outranks the forged clock
        awareness.set_local_state("mine".to_string());
        assert_eq!(awareness.get_local_state(), Some("mine".to_string()));
        assert_eq!(awareness.get_states().get(&7).unwrap().clock(), u64::MAX);

        // clocks saturate instead of overflowing
        let mut states = AwarenessStates::new();
        states.insert(7, AwarenessState::new(u64::MAX, "forged".to_string()));
        awareness.apply_update(states);
        awareness.set_local_state("still mine".to_string());
        let local = awareness.get_states().get(&7).unwrap();
        assert_eq!(local.clock(), u64::MAX);
        assert_eq!(local.content(), "still mine");
    }

    #[test]
    fn test_awareness_equal_clock_null_offline_and_clock_preservation() {
        let mut awareness = Awareness::new(1);

        // Remote peer 2 comes online at clock 5.
        let mut online = AwarenessStates::new();
        online.insert(2, AwarenessState::new(5, r#"{"user":"alice"}"#.to_string()));
        let ev1 = awareness.apply_update_returning_event(online);
        assert_eq!(ev1.added(), &[2]);
        assert!(!awareness.get_states().get(&2).unwrap().is_deleted());

        // y-protocols@1.0.6 offline broadcast with EQUAL clock (5) and content
        // "null".
        let mut offline_same_clock = AwarenessStates::new();
        offline_same_clock.insert(2, AwarenessState::new(5, "null".to_string()));
        let ev2 = awareness.apply_update_returning_event(offline_same_clock);
        assert_eq!(ev2.removed(), &[2]);
        assert!(awareness.get_states().get(&2).unwrap().is_deleted());
        assert_eq!(awareness.get_states().get(&2).unwrap().clock(), 5);

        // Duplicate equal-clock null is ignored (no duplicate remove).
        let mut dup_offline = AwarenessStates::new();
        dup_offline.insert(2, AwarenessState::new(5, "null".to_string()));
        let ev3 = awareness.apply_update_returning_event(dup_offline);
        assert!(ev3.is_empty());

        // Remote higher-clock deletion preserves remote clock so stale online
        // packets cannot resurrect the peer.
        let mut peer3_online = AwarenessStates::new();
        peer3_online.insert(3, AwarenessState::new(2, r#"{"user":"bob"}"#.to_string()));
        awareness.apply_update(peer3_online);

        let mut peer3_offline = AwarenessStates::new();
        peer3_offline.insert(3, AwarenessState::new(10, "null".to_string()));
        let ev4 = awareness.apply_update_returning_event(peer3_offline);
        assert_eq!(ev4.removed(), &[3]);
        assert_eq!(awareness.get_states().get(&3).unwrap().clock(), 10);

        let mut stale_online = AwarenessStates::new();
        stale_online.insert(3, AwarenessState::new(6, r#"{"user":"bob-stale"}"#.to_string()));
        let ev5 = awareness.apply_update_returning_event(stale_online);
        assert!(ev5.is_empty());
        assert!(awareness.get_states().get(&3).unwrap().is_deleted());
    }

    #[test]
    fn test_awareness_rotate_local_id_reannounces_and_clears_old() {
        let mut awareness = Awareness::new(100);
        awareness.set_local_state(r#"{"cursor":42}"#.to_string());

        // Suppose another peer already had state under 200 at clock 7.
        let mut remote = AwarenessStates::new();
        remote.insert(200, AwarenessState::new(7, r#"{"cursor":1}"#.to_string()));
        awareness.apply_update(remote);

        let ev = awareness.set_local_id(200);
        assert_eq!(awareness.local_id(), 200);
        assert_eq!(ev.removed(), &[100]);
        assert_eq!(ev.updated(), &[200]);

        // Old ID is marked deleted, new ID has our state with clock > 7.
        assert!(awareness.get_states().get(&100).unwrap().is_deleted());
        let new_state = awareness.get_states().get(&200).unwrap();
        assert_eq!(new_state.content(), r#"{"cursor":42}"#);
        assert_eq!(new_state.clock(), 8);

        // Wire roundtrip of encoded update: peer sees 200 added; 100 is already
        // deleted ("null") so it records the clock floor without emitting
        // added.
        let bytes = awareness.encode_update(Some(&[100, 200])).unwrap();
        let mut peer = Awareness::new(999);
        let peer_ev = peer.apply_update_v1(&bytes).unwrap();
        assert_eq!(peer_ev.added(), &[200]);
        assert!(peer_ev.updated().is_empty());
        assert!(peer_ev.removed().is_empty());
        assert!(peer.get_states().get(&100).unwrap().is_deleted());
        assert_eq!(peer.get_states().get(&200).unwrap().content(), r#"{"cursor":42}"#);
    }

    #[test]
    fn first_packet_offline_null_does_not_emit_added_and_records_clock_floor() {
        let mut peer = Awareness::new(1);
        let mut offline = AwarenessStates::new();
        offline.insert(42, AwarenessState::new(5, "null".to_string()));
        let ev = peer.apply_update_returning_event(offline);
        assert!(ev.added().is_empty(), "first-seen offline null must not emit added");
        assert!(ev.updated().is_empty());
        assert!(ev.removed().is_empty());
        assert!(peer.get_states().get(&42).unwrap().is_deleted());
        assert_eq!(peer.get_states().get(&42).unwrap().clock(), 5);

        // Stale online packet with older clock must not resurrect client 42.
        let mut stale = AwarenessStates::new();
        stale.insert(42, AwarenessState::new(4, r#"{"user":"stale"}"#.to_string()));
        let ev_stale = peer.apply_update_returning_event(stale);
        assert!(ev_stale.is_empty());
        assert!(peer.get_states().get(&42).unwrap().is_deleted());
    }
}
