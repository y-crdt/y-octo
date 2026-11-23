use std::{
    any::Any as StdAny,
    sync::{Arc, atomic::AtomicU64},
};

use super::UndoStackId;
use crate::{
    DeleteSet, JwstCodecError, JwstCodecResult, Origin, UndoStack,
    doc::{
        CommitHook, CommitSummary, DocStore, TypeArena, YTypeRef, after_unlock,
        undo::{Meta, StackItem, UndoState, next_manager_id},
    },
};

/// Multi-stack history hub installed as `DocStore::history_hook` for a
/// [`DocSession`](super::DocSession).
///
/// Manages `0..N` independent [`UndoState`] stacks with monotonically
/// increasing [`UndoStackId`]s (destroyed IDs are never reused so stale handles
/// cannot accidentally affect newly created stacks) and always keeps
/// `store.retained` equal to the union of all live stacks' retained sets.
#[derive(Debug)]
pub(crate) struct SessionHistoryHub {
    now: Arc<AtomicU64>,
    next_id: u32,
    stacks: Vec<(UndoStackId, UndoState)>,
}

impl SessionHistoryHub {
    pub(crate) fn new(now: Arc<AtomicU64>) -> Self {
        Self {
            now,
            next_id: 0,
            stacks: Vec::new(),
        }
    }

    /// `types` is the arena of the document the `scopes` belong to.
    pub(crate) fn create_stack(
        &mut self,
        types: &TypeArena,
        scopes: Vec<YTypeRef>,
        tracked: Vec<Option<Origin>>,
        capture_timeout: u64,
    ) -> JwstCodecResult<(UndoStackId, u64)> {
        let id = UndoStackId(self.next_id);
        self.next_id = self.next_id.checked_add(1).ok_or(JwstCodecError::Unexpected)?;
        let manager = next_manager_id();
        let state = UndoState::new_for_session(types, manager, scopes, tracked, capture_timeout, self.now.clone())?;
        self.stacks.push((id, state));
        Ok((id, manager))
    }

    pub(crate) fn destroy_stack(&mut self, id: UndoStackId, store: &mut DocStore) -> Option<u64> {
        let pos = self.stacks.iter().position(|(sid, _)| *sid == id)?;
        let (_, removed) = self.stacks.remove(pos);
        let manager_id = removed.manager_id();
        after_unlock(move || drop(removed));
        self.sync_retained(store);
        Some(manager_id)
    }

    pub(crate) fn stack(&self, id: UndoStackId) -> Option<&UndoState> {
        self.stacks.iter().find(|(sid, _)| *sid == id).map(|(_, s)| s)
    }

    pub(crate) fn stack_mut(&mut self, id: UndoStackId) -> Option<&mut UndoState> {
        self.stacks.iter_mut().find(|(sid, _)| *sid == id).map(|(_, s)| s)
    }

    pub(crate) fn can_undo_redo(&self, id: UndoStackId) -> (bool, bool) {
        self.stack(id).map_or((false, false), UndoState::can_undo_redo)
    }

    pub(crate) fn manager_id(&self, id: UndoStackId) -> Option<u64> {
        self.stack(id).map(UndoState::manager_id)
    }

    pub(crate) fn sync_retained(&self, store: &mut DocStore) {
        let mut union = DeleteSet::default();
        for (_, state) in &self.stacks {
            let r = state.retained_set();
            union.merge(&r);
        }
        store.set_retained(union);
    }

    pub(crate) fn pop_stack(
        &mut self,
        id: UndoStackId,
        store: &mut DocStore,
        which: UndoStack,
    ) -> JwstCodecResult<Option<(u64, Option<Meta>)>> {
        let Some(pos) = self.stacks.iter().position(|(sid, _)| *sid == id) else {
            return Err(JwstCodecError::InvalidParent);
        };
        let (before, rest) = self.stacks.split_at_mut(pos);
        let ((_, target), after) = rest.split_first_mut().expect("pos < len");
        let mut other_slices: Vec<&[StackItem]> = Vec::with_capacity((before.len() + after.len()) * 2);
        for (_, s) in before.iter().chain(after.iter()) {
            let [u, r] = s.stack_slices();
            other_slices.push(u);
            other_slices.push(r);
        }
        let performed = target.pop_with_extra_stacks(store, which, &other_slices);
        self.sync_retained(store);
        performed
    }

    pub(crate) fn clear_stack(
        &mut self,
        id: UndoStackId,
        store: &mut DocStore,
        undo: bool,
        redo: bool,
    ) -> JwstCodecResult {
        let Some(state) = self.stack_mut(id) else {
            return Err(JwstCodecError::InvalidParent);
        };
        state.clear_stacks(undo, redo);
        self.sync_retained(store);
        Ok(())
    }

    pub(crate) fn stop_capturing_stack(&mut self, id: UndoStackId) -> JwstCodecResult {
        let Some(state) = self.stack_mut(id) else {
            return Err(JwstCodecError::InvalidParent);
        };
        state.stop_capturing();
        Ok(())
    }

    pub(crate) fn set_top_meta(&mut self, id: UndoStackId, which: UndoStack, meta: Meta) -> JwstCodecResult<bool> {
        let Some(state) = self.stack_mut(id) else {
            after_unlock(move || drop(meta));
            return Err(JwstCodecError::InvalidParent);
        };
        let (found, prev) = state.set_top_meta(which, meta);
        if let Some(p) = prev {
            after_unlock(move || drop(p));
        }
        Ok(found)
    }
}

impl CommitHook for SessionHistoryHub {
    fn on_commit(&mut self, store: &mut DocStore, summary: &CommitSummary) {
        let mut any_released = false;
        let mut newly_retained = DeleteSet::default();
        for (_, state) in &mut self.stacks {
            let (released, retained) = state.on_commit_raw(store, summary);
            any_released |= released;
            if !retained.is_empty() {
                newly_retained.merge(&retained);
            }
        }
        if any_released {
            self.sync_retained(store);
        } else if !newly_retained.is_empty() {
            store.add_retained(&newly_retained);
        }
    }

    fn as_any(&self) -> &dyn StdAny {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn StdAny {
        self
    }
}
