/-
`y_octo_core::item_space`: the item arena of a document, slots in chunks of
`CHUNK_SIZE`.

The theorems are about `cellAt s i`, what the slot `i` of the arena `s` holds
(`none`: no such slot; `some none`: an empty slot; `some (some x)`: the item
`x`), and `item s i`, its item. `cell`, `cell_mut`, `get`, `get_mut` and
`get_two_mut` are total on every arena and answer what `cellAt` says
(`cell_spec`, `cell_mut_spec`, `get_spec`, `get_mut_spec`,
`get_two_mut_spec`); a write through a borrow changes that slot only (`Upd`).

`WF` is the invariant of an arena: the chunks hold `slots` slots, all full
but the last one (`Geo`); there are at most `MAX_SLOTS` of them; and `free`
and `quarantine` together name every empty slot once. `new` makes such an
arena and `alloc`, `retire` and `finish` keep it (`new_spec`, `alloc_spec`,
`retire_spec`, `finish_spec`). `check_capacity` is exact and total
(`check_capacity_spec`).

`finish` either keeps every item where it is and lets `alloc` fill the slots
emptied since the last `finish`, or moves the items to the front, in their
order (`FinishMoved`): the table it answers has an entry for every old slot,
`0` for an empty one and one more than the new slot for an item, the new
slots are `0 .. live` in the order of the old ones, every item is read at its
new slot, and no slot of the arena is empty afterwards. A timeline whose item
blocks name slots that held an item is accepted by
`ClientBlocksCore::remap_slots` with this table (`finish_slots_moved`).
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.ListAux
import YoctoCore.Properties.IdSetModel
import YoctoCore.Properties.Ring
import YoctoCore.Properties.ClientBlocks

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties.ListAux YoctoCore.Properties.IdSetModel

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace YoctoCore.Properties.ItemSpace

variable {T : Type}

theorem get?_of_getElem {α : Type} {l : List α} {i : Nat} {x : α} (h : i < l.length)
    (hx : x = l[i]) : l[i]? = some x := by
  rw [hx]
  exact List.getElem?_eq_getElem h

theorem usize_zero_val : (0#usize : Std.Usize).val = 0 := rfl

theorem get?_set_self' {α : Type} {l : List α} {i : Nat} (v : α) (hi : i < l.length) :
    (l.set i v)[i]? = some v := by
  rw [set_eq_upd, get?_upd_self]
  obtain ⟨a, ha⟩ := get?_some hi
  rw [ha]
  rfl

theorem get?_set_ne' {α : Type} {l : List α} {i j : Nat} (v : α) (h : j ≠ i) :
    (l.set i v)[j]? = l[j]? := by
  rw [set_eq_upd, get?_upd_ne l _ h]

theorem chunk_size_val : (item_space.CHUNK_SIZE).val = 1024 := by simp [item_space.CHUNK_SIZE]

/-! ## The slots of an arena -/

/-- What the slot `i` holds: `none` when there is no such slot, `some none`
for an empty slot. The slot `i` is in the chunk `i / 1024` at `i % 1024`, and
the first chunk is a field of its own. -/
def cellAt (s : item_space.ItemSpaceCore T) (i : Nat) : Option (Option T) :=
  if i / 1024 = 0 then s.first.val[i % 1024]?
  else
    match s.rest.val[i / 1024 - 1]? with
    | none => none
    | some c => c.val[i % 1024]?

/-- The item of the slot `i`, if it holds one. -/
def item (s : item_space.ItemSpaceCore T) (i : Nat) : Option T :=
  match cellAt s i with
  | some (some x) => some x
  | _ => none

theorem cellAt_first {s : item_space.ItemSpaceCore T} {i : Nat} (h : i / 1024 = 0) :
    cellAt s i = s.first.val[i % 1024]? := by
  unfold cellAt
  exact ite_eq_left h

theorem cellAt_rest {s : item_space.ItemSpaceCore T} {i : Nat} (h : ¬ i / 1024 = 0)
    {c : alloc.vec.Vec (Option T)} (hc : s.rest.val[i / 1024 - 1]? = some c) :
    cellAt s i = c.val[i % 1024]? := by
  unfold cellAt
  rw [ite_eq_right h, hc]

theorem cellAt_rest_none {s : item_space.ItemSpaceCore T} {i : Nat} (h : ¬ i / 1024 = 0)
    (hc : s.rest.val[i / 1024 - 1]? = none) : cellAt s i = none := by
  unfold cellAt
  rw [ite_eq_right h, hc]

/-- A slot of the first chunk is read from `first` alone. -/
theorem cellAt_congr_first {s s' : item_space.ItemSpaceCore T} {j : Nat} (hj : j / 1024 = 0)
    (h : s'.first = s.first) : cellAt s' j = cellAt s j := by
  rw [cellAt_first hj, cellAt_first hj, h]

/-- A slot after the first chunk is read from `rest` alone. -/
theorem cellAt_congr_rest {s s' : item_space.ItemSpaceCore T} {j : Nat} (hj : ¬ j / 1024 = 0)
    (h : s'.rest = s.rest) : cellAt s' j = cellAt s j := by
  unfold cellAt
  rw [ite_eq_right hj, ite_eq_right hj, h]

theorem item_some {s : item_space.ItemSpaceCore T} {i : Nat} {x : T}
    (h : cellAt s i = some (some x)) : item s i = some x := by
  unfold item
  rw [h]

theorem item_empty {s : item_space.ItemSpaceCore T} {i : Nat} (h : cellAt s i = some none) :
    item s i = none := by
  unfold item
  rw [h]

theorem item_absent {s : item_space.ItemSpaceCore T} {i : Nat} (h : cellAt s i = none) :
    item s i = none := by
  unfold item
  rw [h]

/-- A slot with an item is a slot that holds it. -/
theorem cell_of_item {s : item_space.ItemSpaceCore T} {i : Nat} {x : T} (h : item s i = some x) :
    cellAt s i = some (some x) := by
  unfold item at h
  cases hc : cellAt s i with
  | none =>
    rw [hc] at h
    cases h
  | some c =>
    cases c with
    | none =>
      rw [hc] at h
      cases h
    | some y =>
      rw [hc] at h
      have e : y = x := Option.some.inj h
      rw [e]

theorem item_congr {s s' : item_space.ItemSpaceCore T} {i j : Nat}
    (h : cellAt s' j = cellAt s i) : item s' j = item s i := by
  unfold item
  rw [h]

/-- `cell` answers the slot. -/
@[step]
theorem cell_spec (s : item_space.ItemSpaceCore T) (slot : Std.Usize) :
    item_space.ItemSpaceCore.cell s slot ⦃ r => r = cellAt s slot.val ⦄ := by
  unfold item_space.ItemSpaceCore.cell
  simp only [item_space.CHUNK_SIZE]
  step as ⟨chunk, hchunk⟩
  step as ⟨offset, hoffset⟩
  have hc : chunk.val = slot.val / 1024 := by scalar_tac
  have ho : offset.val = slot.val % 1024 := by scalar_tac
  by_cases h0 : chunk = 0#usize
  · have h0' : (chunk = 0#usize) = True := eq_true h0
    simp only [h0', ↓reduceIte]
    have hcz : slot.val / 1024 = 0 := by
      rw [← hc, h0]
      rfl
    by_cases hlt : offset < alloc.vec.Vec.len s.first
    · simp only [hlt, ↓reduceIte]
      have hl : offset.val < s.first.val.length := by scalar_tac
      step as ⟨o, hov⟩
      have hg : s.first.val[offset.val]? = some o := get?_of_getElem hl hov
      rw [cellAt_first hcz, ← ho, hg]
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hl : s.first.val.length ≤ offset.val := by scalar_tac
      rw [cellAt_first hcz, ← ho, get?_none hl]
  · simp only [h0, ↓reduceIte]
    have hcnz : ¬ slot.val / 1024 = 0 := by
      intro e
      apply h0
      apply UScalar.eq_of_val_eq
      rw [hc, e]
      rfl
    step as ⟨ci, hci⟩
    have hciv : ci.val = slot.val / 1024 - 1 := by scalar_tac
    by_cases hlt : ci < alloc.vec.Vec.len s.rest
    · simp only [hlt, ↓reduceIte]
      have hl : ci.val < s.rest.val.length := by scalar_tac
      step as ⟨cells, hcells⟩
      have hg : s.rest.val[slot.val / 1024 - 1]? = some cells := by
        rw [← hciv]
        exact get?_of_getElem hl hcells
      by_cases hlt2 : offset < alloc.vec.Vec.len cells
      · simp only [hlt2, ↓reduceIte]
        have hl2 : offset.val < cells.val.length := by scalar_tac
        step as ⟨o, hov⟩
        have hg2 : cells.val[offset.val]? = some o := get?_of_getElem hl2 hov
        rw [cellAt_rest hcnz hg, ← ho, hg2]
      · simp only [hlt2, ↓reduceIte, spec_ok]
        have hl2 : cells.val.length ≤ offset.val := by scalar_tac
        rw [cellAt_rest hcnz hg, ← ho, get?_none hl2]
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hl : s.rest.val.length ≤ slot.val / 1024 - 1 := by scalar_tac
      rw [cellAt_rest_none hcnz (get?_none hl)]

/-- `s'` is `s` with `v` in the slot `i`, if there is such a slot: no other
slot is touched, no chunk changes its length, and the other fields are the
same. -/
structure Upd (s : item_space.ItemSpaceCore T) (i : Nat) (v : Option T)
    (s' : item_space.ItemSpaceCore T) : Prop where
  slots : s'.slots = s.slots
  free : s'.free = s.free
  quarantine : s'.quarantine = s.quarantine
  first : s'.first.val.length = s.first.val.length
  rest : s'.rest.val.map (fun c => c.val.length) = s.rest.val.map (fun c => c.val.length)
  cell : ∀ j, cellAt s' j = if j = i then (cellAt s i).map (fun _ => v) else cellAt s j

theorem map_length_set {α : Type} {l : List (alloc.vec.Vec α)} {i : Nat}
    {a b : alloc.vec.Vec α} (h : l[i]? = some a) (hb : b.val.length = a.val.length) :
    (l.set i b).map (fun c => c.val.length) = l.map (fun c => c.val.length) := by
  apply ext_get?
  intro j
  rw [get?_map, get?_map]
  by_cases e : j = i
  · rw [e, get?_set_self' b (get?_lt h), h]
    show some b.val.length = some a.val.length
    rw [hb]
  · rw [get?_set_ne' b e]

/-- What `cell_mut` answers: the slot, and a way to write it back. -/
structure CellMutPost (s : item_space.ItemSpaceCore T) (i : Nat) (o : Option (Option T))
    (back : Option (Option T) → item_space.ItemSpaceCore T) : Prop where
  cell : o = cellAt s i
  /-- nothing written: the arena as it was -/
  same : back none = s
  /-- what was there written again: the arena as it was -/
  again : ∀ v, cellAt s i = some v → back (some v) = s
  /-- a write changes this slot only -/
  write : ∀ v, Upd s i v (back (some v))

/-- `cell_mut` answers the slot, and what is written through it lands in that
slot only. -/
theorem cell_mut_spec (s : item_space.ItemSpaceCore T) (slot : Std.Usize) :
    item_space.ItemSpaceCore.cell_mut s slot ⦃ o back => CellMutPost s slot.val o back ⦄ := by
  unfold item_space.ItemSpaceCore.cell_mut
  simp only [item_space.CHUNK_SIZE]
  step as ⟨chunk, hchunk⟩
  step as ⟨offset, hoffset⟩
  have hc : chunk.val = slot.val / 1024 := by scalar_tac
  have ho : offset.val = slot.val % 1024 := by scalar_tac
  by_cases h0 : chunk = 0#usize
  · have h0' : (chunk = 0#usize) = True := eq_true h0
    simp only [h0', ↓reduceIte]
    have hcz : slot.val / 1024 = 0 := by
      rw [← hc, h0]
      rfl
    by_cases hlt : offset < alloc.vec.Vec.len s.first
    · simp only [hlt, ↓reduceIte]
      have hl : offset.val < s.first.val.length := by scalar_tac
      step as ⟨o, back, hov, hback⟩
      have hg : s.first.val[slot.val % 1024]? = some o := by
        rw [← ho]
        exact get?_of_getElem hl hov
      have hcell : cellAt s slot.val = some o := by rw [cellAt_first hcz, hg]
      have hset : ∀ v : Option T, (back v).val = s.first.val.set (slot.val % 1024) v := by
        intro v
        rw [hback, ← ho]
        simp
      have hagain : ∀ v : Option T, some o = some v →
          ({ s with first := back v } : item_space.ItemSpaceCore T) = s := by
        intro v hv
        have e : v = o := (Option.some.inj hv).symm
        have hb : back v = s.first := by
          apply alloc.vec.Vec.ext
          rw [hset v, e]
          exact set_eq_self hg
        rw [hb]
      refine ⟨hcell.symm, hagain o rfl, fun v hv => ?_, fun v => ?_⟩
      · rw [hcell] at hv
        exact hagain v hv
      · refine ⟨rfl, rfl, rfl, ?_, rfl, fun j => ?_⟩
        · show (back v).val.length = s.first.val.length
          rw [hset v, List.length_set]
        · by_cases hj : j / 1024 = 0
          · rw [cellAt_first hj]
            show (back v).val[j % 1024]? = _
            rw [hset v]
            by_cases e : j = slot.val
            · rw [ite_eq_left e, e, get?_set_self' v (get?_lt hg), hcell]
              rfl
            · rw [ite_eq_right e, get?_set_ne' v (by omega), cellAt_first hj]
          · have e : ¬ j = slot.val := by
              intro e
              rw [e] at hj
              exact hj hcz
            rw [ite_eq_right e]
            exact cellAt_congr_rest hj rfl
    · simp only [hlt, ↓reduceIte, spec_ok, uncurry'_pair]
      have hl : s.first.val.length ≤ slot.val % 1024 := by scalar_tac
      have hcell : cellAt s slot.val = none := by rw [cellAt_first hcz, get?_none hl]
      refine ⟨hcell.symm, rfl, fun v _ => rfl, fun v => ?_⟩
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun j => ?_⟩
      by_cases e : j = slot.val
      · rw [ite_eq_left e, e, hcell]
        rfl
      · rw [ite_eq_right e]
  · simp only [h0, ↓reduceIte]
    have hcnz : ¬ slot.val / 1024 = 0 := by
      intro e
      apply h0
      apply UScalar.eq_of_val_eq
      rw [hc, e]
      rfl
    step as ⟨ci, hci⟩
    have hciv : ci.val = slot.val / 1024 - 1 := by scalar_tac
    by_cases hlt : ci < alloc.vec.Vec.len s.rest
    · simp only [hlt, ↓reduceIte]
      have hl : ci.val < s.rest.val.length := by scalar_tac
      step as ⟨cells, back, hcells, hback⟩
      have hg : s.rest.val[slot.val / 1024 - 1]? = some cells := by
        rw [← hciv]
        exact get?_of_getElem hl hcells
      have hsetr : ∀ c : alloc.vec.Vec (Option T),
          (back c).val = s.rest.val.set (slot.val / 1024 - 1) c := by
        intro c
        rw [hback, ← hciv]
        simp
      have hsame : ({ s with rest := back cells } : item_space.ItemSpaceCore T) = s := by
        have hb : back cells = s.rest := by
          apply alloc.vec.Vec.ext
          rw [hsetr cells]
          exact set_eq_self hg
        rw [hb]
      by_cases hlt2 : offset < alloc.vec.Vec.len cells
      · simp only [hlt2, ↓reduceIte]
        have hl2 : offset.val < cells.val.length := by scalar_tac
        step as ⟨o, back1, hov, hback1⟩
        have hg2 : cells.val[slot.val % 1024]? = some o := by
          rw [← ho]
          exact get?_of_getElem hl2 hov
        have hcell : cellAt s slot.val = some o := by rw [cellAt_rest hcnz hg, hg2]
        have hsetc : ∀ v : Option T, (back1 v).val = cells.val.set (slot.val % 1024) v := by
          intro v
          rw [hback1, ← ho]
          simp
        have hagain : ∀ v : Option T, some o = some v →
            ({ s with rest := back (back1 v) } : item_space.ItemSpaceCore T) = s := by
          intro v hv
          have e : v = o := (Option.some.inj hv).symm
          have hb : back1 v = cells := by
            apply alloc.vec.Vec.ext
            rw [hsetc v, e]
            exact set_eq_self hg2
          rw [hb]
          exact hsame
        refine ⟨hcell.symm, hagain o rfl, fun v hv => ?_, fun v => ?_⟩
        · rw [hcell] at hv
          exact hagain v hv
        · refine ⟨rfl, rfl, rfl, rfl, ?_, fun j => ?_⟩
          · show (back (back1 v)).val.map (fun c => c.val.length) = _
            rw [hsetr]
            exact map_length_set hg (by rw [hsetc v, List.length_set])
          · by_cases hj : j / 1024 = 0
            · have e : ¬ j = slot.val := by
                intro e
                rw [e] at hj
                exact hcnz hj
              rw [ite_eq_right e]
              exact cellAt_congr_first hj rfl
            · by_cases hch : j / 1024 - 1 = slot.val / 1024 - 1
              · have hgj : (back (back1 v)).val[j / 1024 - 1]? = some (back1 v) := by
                  rw [hsetr, hch]
                  exact get?_set_self' _ (get?_lt hg)
                have hgj' : s.rest.val[j / 1024 - 1]? = some cells := by rw [hch, hg]
                rw [cellAt_rest (s := { s with rest := back (back1 v) }) hj hgj, hsetc v]
                by_cases e : j = slot.val
                · rw [ite_eq_left e, e, get?_set_self' v (get?_lt hg2), hcell]
                  rfl
                · rw [ite_eq_right e, get?_set_ne' v (by omega), cellAt_rest hj hgj']
              · have e : ¬ j = slot.val := by
                  intro e
                  rw [e] at hch
                  exact hch rfl
                rw [ite_eq_right e]
                unfold cellAt
                rw [ite_eq_right hj, ite_eq_right hj]
                show (match (back (back1 v)).val[j / 1024 - 1]? with
                  | none => none
                  | some c => c.val[j % 1024]?) = _
                rw [hsetr, get?_set_ne' _ hch]
      · simp only [hlt2, ↓reduceIte, spec_ok, uncurry'_pair]
        have hl2 : cells.val.length ≤ slot.val % 1024 := by scalar_tac
        have hcell : cellAt s slot.val = none := by rw [cellAt_rest hcnz hg, get?_none hl2]
        refine ⟨hcell.symm, hsame, fun v _ => hsame, fun v => ?_⟩
        show Upd s slot.val v ({ s with rest := back cells } : item_space.ItemSpaceCore T)
        rw [hsame]
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun j => ?_⟩
        by_cases e : j = slot.val
        · rw [ite_eq_left e, e, hcell]
          rfl
        · rw [ite_eq_right e]
    · simp only [hlt, ↓reduceIte, spec_ok, uncurry'_pair]
      have hl : s.rest.val.length ≤ slot.val / 1024 - 1 := by scalar_tac
      have hcell : cellAt s slot.val = none := cellAt_rest_none hcnz (get?_none hl)
      refine ⟨hcell.symm, rfl, fun v _ => rfl, fun v => ?_⟩
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun j => ?_⟩
      by_cases e : j = slot.val
      · rw [ite_eq_left e, e, hcell]
        rfl
      · rw [ite_eq_right e]

/-! ## Reading and writing one slot -/

/-- `holds` says whether the slot holds an item. -/
theorem holds_spec (s : item_space.ItemSpaceCore T) (slot : Std.Usize) :
    item_space.ItemSpaceCore.holds s slot ⦃ b => (b = true ↔ ∃ x, item s slot.val = some x) ⦄ := by
  unfold item_space.ItemSpaceCore.holds
  step with cell_spec s slot as ⟨o, ho⟩
  cases o with
  | none =>
    simp only [spec_ok]
    have hi : item s slot.val = none := item_absent ho.symm
    constructor
    · intro e
      cases e
    · rintro ⟨x, hx⟩
      rw [hi] at hx
      cases hx
  | some cell =>
    cases cell with
    | none =>
      simp only [spec_ok]
      have hi : item s slot.val = none := item_empty ho.symm
      constructor
      · intro e
        cases e
      · rintro ⟨x, hx⟩
        rw [hi] at hx
        cases hx
    | some x =>
      simp only [spec_ok]
      constructor
      · intro _
        exact ⟨x, item_some ho.symm⟩
      · intro _
        trivial

/-- What `take` does. -/
structure TakePost (s : item_space.ItemSpaceCore T) (i : Nat) (o : Option T)
    (s' : item_space.ItemSpaceCore T) : Prop where
  /-- it answers the item of the slot -/
  answer : o = item s i
  /-- no item: the arena as it was -/
  same : o = none → s' = s
  /-- an item: the slot is empty now, nothing else changes -/
  taken : ∀ x, o = some x → Upd s i none s'

/-- `take` answers the item of the slot and empties the slot; an arena whose
slot holds no item is left as it was. -/
theorem take_spec (s : item_space.ItemSpaceCore T) (slot : Std.Usize) :
    item_space.ItemSpaceCore.take s slot ⦃ o s' => TakePost s slot.val o s' ⦄ := by
  unfold item_space.ItemSpaceCore.take
  step with cell_mut_spec s slot as ⟨o, back, hpost⟩
  have hP : CellMutPost s slot.val o back := hpost
  cases o with
  | none =>
    simp only [spec_ok, uncurry'_pair]
    exact ⟨(item_absent hP.cell.symm).symm, fun _ => hP.same, fun x hx => (nomatch hx)⟩
  | some cell =>
    cases cell with
    | none =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨(item_empty hP.cell.symm).symm, fun _ => hP.again none hP.cell.symm,
        fun x hx => (nomatch hx)⟩
    | some x =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨(item_some hP.cell.symm).symm, fun h => (nomatch h), fun _ _ => hP.write none⟩

/-- What `put` does. -/
structure PutPost (s : item_space.ItemSpaceCore T) (i : Nat) (x : T) (o : Option T)
    (s' : item_space.ItemSpaceCore T) : Prop where
  /-- no such slot: the item comes back and the arena is as it was -/
  absent : cellAt s i = none → o = some x ∧ s' = s
  /-- a slot: it holds the item now, nothing else changes -/
  put : cellAt s i ≠ none → o = none ∧ Upd s i (some x) s'

/-- `put` writes the item into the slot, or hands it back when there is no
such slot and leaves the arena as it was. -/
theorem put_spec (s : item_space.ItemSpaceCore T) (slot : Std.Usize) (x : T) :
    item_space.ItemSpaceCore.put s slot x ⦃ o s' => PutPost s slot.val x o s' ⦄ := by
  unfold item_space.ItemSpaceCore.put
  step with cell_mut_spec s slot as ⟨o, back, hpost⟩
  have hP : CellMutPost s slot.val o back := hpost
  cases o with
  | none =>
    simp only [spec_ok, uncurry'_pair]
    exact ⟨fun _ => ⟨rfl, hP.same⟩, fun hne => absurd hP.cell.symm hne⟩
  | some c =>
    simp only [spec_ok, uncurry'_pair]
    refine ⟨fun hn => ?_, fun _ => ⟨rfl, hP.write (some x)⟩⟩
    rw [← hP.cell] at hn
    cases hn

/-- **`get` answers the item of the slot**, on every arena. -/
theorem get_spec (s : item_space.ItemSpaceCore T) (slot : Std.U32) :
    item_space.ItemSpaceCore.get s slot ⦃ r => r = item s slot.val ⦄ := by
  unfold item_space.ItemSpaceCore.get
  have hcast : slot.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.Usize slot hcast as ⟨i, hi⟩
  step with cell_spec s i as ⟨o, ho⟩
  rw [hi] at ho
  cases o with
  | none =>
    simp only [spec_ok]
    exact (item_absent ho.symm).symm
  | some cell =>
    cases cell with
    | none =>
      simp only [spec_ok]
      exact (item_empty ho.symm).symm
    | some x =>
      simp only [spec_ok]
      exact (item_some ho.symm).symm

/-- What `get_mut` answers: the item of the slot, and a way to write it. -/
structure GetMutPost (s : item_space.ItemSpaceCore T) (i : Nat) (o : Option T)
    (back : Option T → item_space.ItemSpaceCore T) : Prop where
  answer : o = item s i
  /-- nothing written: the arena as it was -/
  same : back none = s
  /-- no item to write to: the arena as it was -/
  absent : o = none → ∀ r, back r = s
  /-- a write changes the item of this slot only -/
  write : ∀ x, o = some x → ∀ y, Upd s i (some y) (back (some y))

/-- **`get_mut` answers the item of the slot**, and what is written through
it is the item of that slot afterwards; no other slot changes. -/
theorem get_mut_spec (s : item_space.ItemSpaceCore T) (slot : Std.U32) :
    item_space.ItemSpaceCore.get_mut s slot ⦃ o back => GetMutPost s slot.val o back ⦄ := by
  unfold item_space.ItemSpaceCore.get_mut
  have hcast : slot.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.Usize slot hcast as ⟨i, hi⟩
  step with cell_mut_spec s i as ⟨o, back, hpost⟩
  have hP : CellMutPost s slot.val o back := by
    rw [← hi]
    exact hpost
  cases o with
  | none =>
    simp only [spec_ok, uncurry'_pair]
    exact ⟨(item_absent hP.cell.symm).symm, hP.same, fun _ _ => hP.same,
      fun x hx => (nomatch hx)⟩
  | some cell =>
    cases cell with
    | none =>
      simp only [spec_ok, uncurry'_pair]
      have hs := hP.again none hP.cell.symm
      exact ⟨(item_empty hP.cell.symm).symm, hs, fun _ _ => hs, fun x hx => (nomatch hx)⟩
    | some x =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨(item_some hP.cell.symm).symm, hP.again (some x) hP.cell.symm,
        fun h => (nomatch h), fun _ _ y => hP.write (some y)⟩

/-- **`check_capacity` is exact and total**: it says whether the items the
arena holds, the slots emptied since the last `finish` counted, and
`additional` more are at most `limit` and at most `MAX_SLOTS` (`2 ^ 32 - 1`,
what `alloc` goes up to). No sum is formed that could exceed a `usize`. -/
theorem check_capacity_spec (s : item_space.ItemSpaceCore T) (additional limit : Std.Usize) :
    item_space.ItemSpaceCore.check_capacity s additional limit ⦃ b =>
      (b = true ↔ s.free.val.length ≤ s.slots.val ∧
        s.slots.val - s.free.val.length + additional.val ≤ min limit.val 4294967295) ⦄ := by
  unfold item_space.ItemSpaceCore.check_capacity
  simp only
  by_cases hgt : alloc.vec.Vec.len s.free > s.slots
  · simp only [hgt, ↓reduceIte, spec_ok]
    have hlt : s.slots.val < s.free.val.length := by scalar_tac
    constructor
    · intro e
      cases e
    · rintro ⟨h1, _⟩
      omega
  · simp only [hgt, ↓reduceIte]
    have hle : s.free.val.length ≤ s.slots.val := by scalar_tac
    have hmaxv : (item_space.MAX_SLOTS).val = 4294967295 := by simp [item_space.MAX_SLOTS]
    -- the limit that counts: the smaller one of `limit` and `MAX_SLOTS`
    have hlim : (if limit < item_space.MAX_SLOTS then ok limit else ok item_space.MAX_SLOTS :
        Result Std.Usize) ⦃ r =>
          (r.val = limit.val ∧ limit.val < 4294967295) ∨
            (r.val = 4294967295 ∧ 4294967295 ≤ limit.val) ⦄ := by
      by_cases hl : limit < item_space.MAX_SLOTS
      · have hlv : limit.val < 4294967295 := by scalar_tac
        simp only [hl, ↓reduceIte]
        exact (spec_ok _).mpr (Or.inl ⟨rfl, hlv⟩)
      · have hlv : 4294967295 ≤ limit.val := by scalar_tac
        simp only [hl, ↓reduceIte]
        exact (spec_ok _).mpr (Or.inr ⟨hmaxv, hlv⟩)
    step with hlim as ⟨limit1, hlimit1⟩
    rw [Nat.le_min]
    by_cases hadd : additional <= limit1
    · simp only [hadd, ↓reduceIte]
      have haddv : additional.val ≤ limit1.val := by scalar_tac
      step as ⟨occ, hocc⟩
      step as ⟨room, hroom⟩
      have hoccv : occ.val = s.slots.val - s.free.val.length := by scalar_tac
      have hroomv : room.val = limit1.val - additional.val := by scalar_tac
      constructor
      · intro hb
        have hor : occ.val ≤ room.val := by
          have := of_decide_eq_true hb
          scalar_tac
        refine ⟨hle, ?_, ?_⟩
        · rcases hlimit1 with ⟨e, h⟩ | ⟨e, h⟩ <;> omega
        · rcases hlimit1 with ⟨e, h⟩ | ⟨e, h⟩ <;> omega
      · rintro ⟨_, h2, h3⟩
        apply decide_eq_true
        have hor : occ.val ≤ room.val := by
          rcases hlimit1 with ⟨e, h⟩ | ⟨e, h⟩ <;> omega
        scalar_tac
    · simp only [hadd, ↓reduceIte, spec_ok]
      have haddv : limit1.val < additional.val := by scalar_tac
      constructor
      · intro e
        cases e
      · rintro ⟨_, h2, h3⟩
        rcases hlimit1 with ⟨e, h⟩ | ⟨e, h⟩ <;> omega

/-! ## The invariant -/

/-- The chunks hold the slots `0 .. n`: the first one the slots below `1024`,
the chunks after it `1024` slots each but the last one, which is not empty. -/
structure GeoN (n : Nat) (s : item_space.ItemSpaceCore T) : Prop where
  first : s.first.val.length = min n 1024
  rest : s.rest.val.length = (n - 1) / 1024
  chunk : ∀ (c : Nat) (v : alloc.vec.Vec (Option T)), s.rest.val[c]? = some v →
    v.val.length = min (n - 1024 * (c + 1)) 1024

/-- The chunks hold the slots of the arena. -/
def Geo (s : item_space.ItemSpaceCore T) : Prop := GeoN s.slots.val s

/-- Below `n` there is a slot. -/
theorem GeoN.cell_lt {n : Nat} {s : item_space.ItemSpaceCore T} (g : GeoN n s) {i : Nat}
    (h : i < n) : ∃ c, cellAt s i = some c := by
  by_cases hi : i / 1024 = 0
  · rw [cellAt_first hi]
    have hf := g.first
    exact get?_some (by omega)
  · have hr := g.rest
    obtain ⟨v, hv⟩ := get?_some (l := s.rest.val) (i := i / 1024 - 1) (by omega)
    have hlen := g.chunk _ v hv
    rw [cellAt_rest hi hv]
    exact get?_some (by omega)

/-- From `n` on there is no slot. -/
theorem GeoN.cell_ge {n : Nat} {s : item_space.ItemSpaceCore T} (g : GeoN n s) {i : Nat}
    (h : n ≤ i) : cellAt s i = none := by
  by_cases hi : i / 1024 = 0
  · rw [cellAt_first hi]
    have hf := g.first
    exact get?_none (by omega)
  · cases hv : s.rest.val[i / 1024 - 1]? with
    | none => exact cellAt_rest_none hi hv
    | some v =>
      have hlen := g.chunk _ v hv
      rw [cellAt_rest hi hv]
      exact get?_none (by omega)

/-- A slot is a number below `n`. -/
theorem GeoN.cell_iff {n : Nat} {s : item_space.ItemSpaceCore T} (g : GeoN n s) {i : Nat} :
    (∃ c, cellAt s i = some c) ↔ i < n := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra hge
    rw [g.cell_ge (by omega)] at hc
    cases hc
  · exact g.cell_lt

/-- The lengths of the chunks are all `GeoN` reads. -/
theorem GeoN.of_shape {n : Nat} {s s' : item_space.ItemSpaceCore T} (g : GeoN n s)
    (hf : s'.first.val.length = s.first.val.length)
    (hr : s'.rest.val.map (fun c => c.val.length) = s.rest.val.map (fun c => c.val.length)) :
    GeoN n s' := by
  have hlen : s'.rest.val.length = s.rest.val.length := by
    have := congrArg List.length hr
    rw [List.length_map, List.length_map] at this
    exact this
  refine ⟨by rw [hf]; exact g.first, by rw [hlen]; exact g.rest, fun c v hv => ?_⟩
  have h1 : (s'.rest.val.map (fun c => c.val.length))[c]? = some v.val.length := by
    rw [get?_map, hv]
    rfl
  rw [hr, get?_map] at h1
  cases hv0 : s.rest.val[c]? with
  | none =>
    rw [hv0] at h1
    cases h1
  | some v0 =>
    rw [hv0] at h1
    have e : v0.val.length = v.val.length := Option.some.inj h1
    rw [← e]
    exact g.chunk c v0 hv0

theorem Upd.geo {n : Nat} {s s' : item_space.ItemSpaceCore T} {i : Nat} {v : Option T}
    (u : Upd s i v s') (g : GeoN n s) : GeoN n s' :=
  g.of_shape u.first u.rest

/-- The item of every slot after a write. -/
theorem Upd.item {s s' : item_space.ItemSpaceCore T} {i : Nat} {v : Option T}
    (u : Upd s i v s') {c : Option T} (hc : cellAt s i = some c) (j : Nat) :
    item s' j = if j = i then v else item s j := by
  by_cases e : j = i
  · rw [ite_eq_left e]
    have h := u.cell j
    rw [ite_eq_left e, hc] at h
    have h' : cellAt s' j = some v := h
    cases v with
    | none => exact item_empty h'
    | some x => exact item_some h'
  · rw [ite_eq_right e]
    have h := u.cell j
    rw [ite_eq_right e] at h
    exact item_congr h

/-- The invariant of an arena. -/
structure WF (s : item_space.ItemSpaceCore T) : Prop where
  /-- the chunks hold `slots` slots -/
  geo : Geo s
  /-- a slot, and one more than a slot, fit a `u32` -/
  bound : s.slots.val ≤ 4294967295
  /-- no slot is named twice by `free` and `quarantine` -/
  nodup : (s.free.val ++ s.quarantine.val).Nodup
  /-- `free` and `quarantine` name the empty slots, all of them -/
  empty : ∀ i : Std.U32, i ∈ s.free.val ++ s.quarantine.val ↔ cellAt s i.val = some none

theorem nodup_snoc {α : Type} {l : List α} {a : α} (hn : l.Nodup) (ha : ¬ a ∈ l) :
    (l ++ [a]).Nodup := by
  rw [← insAt_length]
  exact nodup_insAt hn ha

/-- A list without one of its elements has no element twice either, and not
that one. -/
theorem nodup_remove {α : Type} {a : α} {r : List α} :
    ∀ {l : List α}, (l ++ ([a] ++ r)).Nodup → ¬ a ∈ l ++ r ∧ (l ++ r).Nodup
  | [], h => by
    have h' := List.nodup_cons.mp (show (a :: r).Nodup from h)
    exact ⟨h'.1, h'.2⟩
  | b :: t, h => by
    have h' := List.nodup_cons.mp (show (b :: (t ++ ([a] ++ r))).Nodup from h)
    obtain ⟨hn, hd⟩ := nodup_remove h'.2
    have hba : ¬ b = a := by
      intro e
      apply h'.1
      rw [e]
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))
    refine ⟨fun hm => ?_, ?_⟩
    · rcases List.mem_cons.mp (show a ∈ b :: (t ++ r) from hm) with e | hm'
      · exact hba e.symm
      · exact hn hm'
    · show (b :: (t ++ r)).Nodup
      refine List.nodup_cons.mpr ⟨fun hm => ?_, hd⟩
      apply h'.1
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left _ hm
      · exact List.mem_append_right _ (List.mem_append_right _ hm)

/-- A list made shorter. -/
theorem resize_take {α : Type} (l : List α) (n : Nat) (x : α) (h : n ≤ l.length) :
    l.resize n x = l.take n := by
  simp [List.resize, Nat.sub_eq_zero_of_le h]

theorem nodup_map_val : ∀ (l : List Std.U32), l.Nodup → (l.map (fun i => i.val)).Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    have h' := List.nodup_cons.mp h
    show (a.val :: t.map (fun i => i.val)).Nodup
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_val t h'.2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    have e' : b = a := UScalar.eq_of_val_eq e
    rw [e'] at hb
    exact h'.1 hb

/-- There are no more empty slots named than slots. -/
theorem WF.empties_le {s : item_space.ItemSpaceCore T} (h : WF s) :
    s.free.val.length + s.quarantine.val.length ≤ s.slots.val := by
  have hn := nodup_map_val _ h.nodup
  have hb : ∀ i, i ∈ (s.free.val ++ s.quarantine.val).map (fun i => i.val) → i < s.slots.val := by
    intro i hi
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hi
    have hc := (h.empty b).mp hb
    rw [← e]
    exact (GeoN.cell_iff h.geo).mp ⟨none, hc⟩
  have := nodup_length_le s.slots.val _ hn hb
  rw [List.length_map, List.length_append] at this
  exact this

/-- A slot that is not named leaves room for one more name. -/
theorem WF.empties_lt {s : item_space.ItemSpaceCore T} (h : WF s) {slot : Std.U32}
    (hlt : slot.val < s.slots.val) (hnot : ¬ slot ∈ s.free.val ++ s.quarantine.val) :
    s.free.val.length + s.quarantine.val.length < s.slots.val := by
  have hn := nodup_map_val (slot :: (s.free.val ++ s.quarantine.val))
    (List.nodup_cons.mpr ⟨hnot, h.nodup⟩)
  have hb : ∀ i, i ∈ (slot :: (s.free.val ++ s.quarantine.val)).map (fun i => i.val) →
      i < s.slots.val := by
    intro i hi
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hi
    rw [← e]
    rcases List.mem_cons.mp hb with e1 | hm
    · rw [e1]
      exact hlt
    · exact (GeoN.cell_iff h.geo).mp ⟨none, (h.empty b).mp hm⟩
  have := nodup_length_le s.slots.val _ hn hb
  rw [List.length_map, List.length_cons, List.length_append] at this
  omega

/-- A slot with an item is none of the empty slots. -/
theorem WF.item_lt {s : item_space.ItemSpaceCore T} (h : WF s) {i : Nat} {x : T}
    (hx : item s i = some x) : i < s.slots.val :=
  (GeoN.cell_iff h.geo).mp ⟨some x, cell_of_item hx⟩

theorem cellAt_no_chunk (s : item_space.ItemSpaceCore T) (h1 : s.first.val = [])
    (h2 : s.rest.val = []) (i : Nat) : cellAt s i = none := by
  unfold cellAt
  rw [h1, h2]
  by_cases hi : i / 1024 = 0
  · rw [ite_eq_left hi]
    rfl
  · rw [ite_eq_right hi]
    rfl

/-- **`new` makes the arena without a slot.** -/
theorem new_spec :
    item_space.ItemSpaceCore.new T ⦃ s =>
      WF s ∧ s.slots.val = 0 ∧ (∀ i, cellAt s i = none) ∧ s.free.val = [] ∧
        s.quarantine.val = [] ⦄ := by
  unfold item_space.ItemSpaceCore.new
  simp only [spec_ok]
  have hv : ∀ α : Type, (alloc.vec.Vec.new α).val = [] := by
    intro α
    simp
  have hcell := cellAt_no_chunk
    ({ first := alloc.vec.Vec.new (Option T), rest := alloc.vec.Vec.new (alloc.vec.Vec (Option T)),
       slots := 0#usize, free := alloc.vec.Vec.new Std.U32,
       quarantine := alloc.vec.Vec.new Std.U32 } : item_space.ItemSpaceCore T)
    (hv _) (hv _)
  refine ⟨⟨⟨?_, ?_, fun c v hc => ?_⟩, ?_, ?_, fun i => ?_⟩, usize_zero_val, hcell, hv _, hv _⟩
  · show (alloc.vec.Vec.new (Option T)).val.length = min (0#usize : Std.Usize).val 1024
    rw [hv, usize_zero_val]
    rfl
  · show (alloc.vec.Vec.new (alloc.vec.Vec (Option T))).val.length =
      ((0#usize : Std.Usize).val - 1) / 1024
    rw [hv, usize_zero_val]
    rfl
  · have hc' : (alloc.vec.Vec.new (alloc.vec.Vec (Option T))).val[c]? = some v := hc
    rw [hv] at hc'
    cases hc'
  · show (0#usize : Std.Usize).val ≤ 4294967295
    rw [usize_zero_val]
    omega
  · show ((alloc.vec.Vec.new Std.U32).val ++ (alloc.vec.Vec.new Std.U32).val).Nodup
    rw [hv]
    exact List.nodup_nil
  · rw [hcell]
    show i ∈ (alloc.vec.Vec.new Std.U32).val ++ (alloc.vec.Vec.new Std.U32).val ↔ _
    rw [hv]
    constructor
    · intro h
      cases h
    · intro h
      cases h

/-! ## `retire` -/

/-- What `retire` does. -/
structure RetirePost (s : item_space.ItemSpaceCore T) (slot : Std.U32) (r : Option T)
    (s' : item_space.ItemSpaceCore T) : Prop where
  /-- it answers the item of the slot -/
  answer : r = item s slot.val
  /-- no item: the arena as it was -/
  same : r = none → s' = s
  /-- an item: the slot is empty and in quarantine, nothing else changes -/
  taken : ∀ x, r = some x →
    WF s' ∧ s'.slots = s.slots ∧ s'.free = s.free ∧
      s'.quarantine.val = s.quarantine.val ++ [slot] ∧
      (∀ j, item s' j = if j = slot.val then none else item s j)

/-- **`retire` takes the item out of the slot** and keeps the invariant: the
slot is empty, named by `quarantine` and not by `free`, so `alloc` does not
fill it before `finish`. Without an item in the slot nothing changes. -/
theorem retire_spec (s : item_space.ItemSpaceCore T) (slot : Std.U32) (h : WF s) :
    item_space.ItemSpaceCore.retire s slot ⦃ r s' => RetirePost s slot r s' ⦄ := by
  unfold item_space.ItemSpaceCore.retire
  have hcast : slot.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.Usize slot hcast as ⟨i, hi⟩
  step with take_spec s i as ⟨o, s1, htake⟩
  have hT : TakePost s slot.val o s1 := by
    rw [← hi]
    exact htake
  have ho := hT.answer
  cases o with
  | none =>
    simp only [spec_ok, uncurry'_pair]
    exact ⟨ho, fun _ => hT.same rfl, fun x hx => (nomatch hx)⟩
  | some x =>
    simp only []
    have hu : Upd s slot.val none s1 := hT.taken x rfl
    have hcell : cellAt s slot.val = some (some x) := cell_of_item ho.symm
    have hlt : slot.val < s.slots.val := h.item_lt ho.symm
    have hle := h.empties_le
    -- the slot was not empty: it is in neither list
    have hnot : ¬ slot ∈ s.free.val ++ s.quarantine.val := by
      intro hm
      have := (h.empty slot).mp hm
      rw [hcell] at this
      cases this
    have hq : s1.quarantine.val.length < Std.Usize.max := by
      rw [hu.quarantine]
      have hu32 : 4294967295 ≤ Std.Usize.max := by scalar_tac
      have := h.bound
      have := h.empties_lt hlt hnot
      omega
    step as ⟨q, hq'⟩
    have hqv : q.val = s.quarantine.val ++ [slot] := by
      rw [hq', hu.quarantine]
    refine ⟨ho, fun hn => (nomatch hn), fun y _ => ⟨⟨?_, ?_, ?_, fun i => ?_⟩, hu.slots, hu.free,
      hqv, fun j => hu.item hcell j⟩⟩
    · show GeoN s1.slots.val _
      rw [hu.slots]
      exact GeoN.of_shape h.geo hu.first hu.rest
    · show s1.slots.val ≤ 4294967295
      rw [hu.slots]
      exact h.bound
    · show (s1.free.val ++ q.val).Nodup
      rw [hu.free, hqv, ← List.append_assoc]
      exact nodup_snoc h.nodup hnot
    · show i ∈ s1.free.val ++ q.val ↔ cellAt s1 i.val = some none
      rw [hu.free, hqv, ← List.append_assoc, hu.cell i.val, hcell]
      by_cases e : i = slot
      · rw [e, ite_eq_left rfl]
        constructor
        · intro _
          rfl
        · intro _
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · have e' : ¬ i.val = slot.val := fun hv => e (UScalar.eq_of_val_eq hv)
        rw [ite_eq_right e']
        constructor
        · intro hm
          rcases List.mem_append.mp hm with hm | hm
          · exact (h.empty i).mp hm
          · exact absurd (List.mem_singleton.mp hm) e
        · intro hc'
          exact List.mem_append_left _ ((h.empty i).mpr hc')

/-! ## `alloc` -/

theorem chunk_room {n c : Nat} (hn : 1024 * (c + 2) ≤ n) : 1024 ≤ n - 1024 * (c + 1) := by
  omega

/-- A chunk with a whole chunk after it is full, in every arena that has
that many slots. -/
theorem chunk_full_of {n m c len : Nat} (hn : 1024 * (c + 2) ≤ n) (hm : 1024 * (c + 2) ≤ m)
    (hlen : len = min (n - 1024 * (c + 1)) 1024) : len = min (m - 1024 * (c + 1)) 1024 := by
  rw [hlen, Nat.min_eq_right (chunk_room hn), Nat.min_eq_right (chunk_room hm)]

/-- What `alloc` does. -/
structure AllocPost (s : item_space.ItemSpaceCore T) (x : T) (limit : Nat)
    (r : core.result.Result Std.U32 T) (s' : item_space.ItemSpaceCore T) : Prop where
  /-- refused: the item comes back, the arena is as it was, and it holds
  `limit` items or would need a slot past `MAX_SLOTS` -/
  err : ∀ y, r = core.result.Result.Err y → y = x ∧ s' = s ∧
    ¬ (s.slots.val - s.free.val.length < limit ∧
      (s.free.val ≠ [] ∨ s.slots.val < 4294967295))
  /-- accepted: the slot was empty or new, is below `MAX_SLOTS` and holds the
  item; no other slot changes; the slot is the last one of `free`, or the
  one after the last slot when `free` names none -/
  ok : ∀ slot, r = core.result.Result.Ok slot →
    s.slots.val - s.free.val.length < limit ∧ slot.val < 4294967295 ∧ WF s' ∧
      item s slot.val = none ∧
      (∀ j, item s' j = if j = slot.val then some x else item s j) ∧
      s'.quarantine = s.quarantine ∧
      ((s.free.val = s'.free.val ++ [slot] ∧ s'.slots = s.slots) ∨
        (s.free.val = [] ∧ s'.free.val = [] ∧ slot.val = s.slots.val ∧
          s'.slots.val = s.slots.val + 1))

/-- An arena that got one more slot, with an item, after its last one. -/
theorem allocPost_grow {s s' : item_space.ItemSpaceCore T} (h : WF s) (x : T) {limit : Nat}
    {slot : Std.U32} (hroom : s.slots.val - s.free.val.length < limit) (hnil : s.free.val = [])
    (hlt : s.slots.val < 4294967295) (hslot : slot.val = s.slots.val)
    (hslots : s'.slots.val = s.slots.val + 1) (hf : s'.free = s.free)
    (hq : s'.quarantine = s.quarantine) (hgeo : GeoN (s.slots.val + 1) s')
    (hcell : ∀ j, cellAt s' j = if j = s.slots.val then some (some x) else cellAt s j) :
    AllocPost s x limit (core.result.Result.Ok slot) s' := by
  have hnew : cellAt s s.slots.val = none := GeoN.cell_ge h.geo (Nat.le_refl _)
  refine ⟨fun y hy => (nomatch hy), fun sl hs => ?_⟩
  cases hs
  refine ⟨hroom, by omega, ⟨?_, by omega, ?_, fun i => ?_⟩, ?_, fun j => ?_, hq,
    Or.inr ⟨hnil, by rw [hf]; exact hnil, hslot, hslots⟩⟩
  · show GeoN s'.slots.val s'
    rw [hslots]
    exact hgeo
  · rw [hf, hq]
    exact h.nodup
  · rw [hf, hq, hcell]
    by_cases e : i.val = s.slots.val
    · rw [ite_eq_left e]
      constructor
      · intro hm
        have hc := (h.empty i).mp hm
        rw [e, hnew] at hc
        cases hc
      · intro hc
        cases hc
    · rw [ite_eq_right e]
      exact h.empty i
  · rw [hslot]
    exact item_absent hnew
  · rw [hslot]
    by_cases e : j = s.slots.val
    · rw [ite_eq_left e]
      have hc := hcell j
      rw [ite_eq_left e] at hc
      exact item_some hc
    · rw [ite_eq_right e]
      have hc := hcell j
      rw [ite_eq_right e] at hc
      exact item_congr hc

/-- **`alloc` puts the item into an empty slot or a new one** and keeps the
invariant; the slot it answers is below `MAX_SLOTS`, so one more than it is
a `u32`. A refusal hands the item back and changes nothing: the arena holds
`limit` items, or it would need a slot past `MAX_SLOTS`. -/
theorem alloc_spec (s : item_space.ItemSpaceCore T) (x : T) (limit : Std.Usize) (h : WF s) :
    item_space.ItemSpaceCore.alloc s x limit ⦃ r s' => AllocPost s x limit.val r s' ⦄ := by
  unfold item_space.ItemSpaceCore.alloc
  simp only [item_space.CHUNK_SIZE, item_space.MAX_SLOTS]
  have hle := h.empties_le
  have hbound := h.bound
  have hg : GeoN s.slots.val s := h.geo
  have hu32 : 4294967295 ≤ Std.Usize.max := by scalar_tac
  have hngt : ¬ alloc.vec.Vec.len s.free > s.slots := by scalar_tac
  simp only [hngt, ↓reduceIte]
  step as ⟨occ, hocc⟩
  have hoccv : occ.val = s.slots.val - s.free.val.length := by scalar_tac
  by_cases hfull : occ >= limit
  · simp only [hfull, ↓reduceIte, spec_ok, uncurry'_pair]
    have hf : limit.val ≤ s.slots.val - s.free.val.length := by scalar_tac
    refine ⟨fun y hy => ?_, fun slot hs => (nomatch hs)⟩
    cases hy
    exact ⟨rfl, rfl, fun hc => by omega⟩
  · simp only [hfull, ↓reduceIte]
    have hroom : s.slots.val - s.free.val.length < limit.val := by scalar_tac
    by_cases hfree : alloc.vec.Vec.len s.free > 0#usize
    · simp only [hfree, ↓reduceIte]
      have hpos : 0 < s.free.val.length := by scalar_tac
      step as ⟨last, hlast⟩
      have hlastv : last.val = s.free.val.length - 1 := by scalar_tac
      step as ⟨slot, hslot⟩
      have hgs : s.free.val[last.val]? = some slot := get?_of_getElem (by omega) hslot
      -- `free` is the slots before its last one, and that one
      have hsplit : ∃ init, s.free.val = init ++ [slot] ∧ s.free.val.take last.val = init := by
        refine ⟨_, ?_, rfl⟩
        have ht := take_succ_get hgs
        rw [← ht]
        have e : last.val + 1 = s.free.val.length := by omega
        rw [e, List.take_length]
      obtain ⟨init, hinit, htake⟩ := hsplit
      have hmem : slot ∈ s.free.val ++ s.quarantine.val :=
        List.mem_append_left _ (get?_mem hgs)
      have hcell : cellAt s slot.val = some none := (h.empty slot).mp hmem
      have hslotlt : slot.val < s.slots.val := (GeoN.cell_iff hg).mp ⟨none, hcell⟩
      have hnd : (init ++ ([slot] ++ s.quarantine.val)).Nodup := by
        rw [← List.append_assoc, ← hinit]
        exact h.nodup
      obtain ⟨hnotin, hnd'⟩ := nodup_remove hnd
      have hcast : slot.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.Usize slot hcast as ⟨i, hi⟩
      step with put_spec s i x as ⟨o, s1, hput⟩
      have hP : PutPost s slot.val x o s1 := by
        rw [← hi]
        exact hput
      have hsome : cellAt s slot.val ≠ none := by
        rw [hcell]
        exact fun e => (nomatch e)
      obtain ⟨ho, hu⟩ := hP.put hsome
      rw [ho]
      simp only []
      step with alloc.vec.Vec.resize_spec core.clone.CloneU32 s1.free last 0#u32 rfl as ⟨v, hv⟩
      have hvv : v.val = init := by
        rw [hv, hu.free, ← htake]
        exact resize_take _ _ _ (by omega)
      refine ⟨fun y hy => (nomatch hy), fun sl hs => ?_⟩
      cases hs
      refine ⟨hroom, by omega, ⟨?_, ?_, ?_, fun j => ?_⟩, item_empty hcell,
        fun j => hu.item hcell j, hu.quarantine, Or.inl ⟨?_, hu.slots⟩⟩
      · show GeoN s1.slots.val _
        rw [hu.slots]
        exact GeoN.of_shape hg hu.first hu.rest
      · show s1.slots.val ≤ 4294967295
        rw [hu.slots]
        exact hbound
      · show (v.val ++ s1.quarantine.val).Nodup
        rw [hvv, hu.quarantine]
        exact hnd'
      · show j ∈ v.val ++ s1.quarantine.val ↔ cellAt _ j.val = some none
        have hc : cellAt ({ s1 with free := v } : item_space.ItemSpaceCore T) j.val =
            cellAt s1 j.val := rfl
        rw [hc, hvv, hu.quarantine, hu.cell j.val, hcell]
        by_cases e : j = slot
        · rw [e, ite_eq_left rfl]
          constructor
          · intro hm
            exact absurd hm hnotin
          · intro hc2
            have hc3 : some (some x) = some (none : Option T) := hc2
            cases hc3
        · have e' : ¬ j.val = slot.val := fun hval => e (UScalar.eq_of_val_eq hval)
          rw [ite_eq_right e']
          constructor
          · intro hm
            apply (h.empty j).mp
            rw [hinit]
            rcases List.mem_append.mp hm with hm | hm
            · exact List.mem_append_left _ (List.mem_append_left _ hm)
            · exact List.mem_append_right _ hm
          · intro hc2
            have hm := (h.empty j).mpr hc2
            rw [hinit] at hm
            rcases List.mem_append.mp hm with hm | hm
            · rcases List.mem_append.mp hm with hm | hm
              · exact List.mem_append_left _ hm
              · exact absurd (List.mem_singleton.mp hm) e
            · exact List.mem_append_right _ hm
      · show s.free.val = v.val ++ [slot]
        rw [hvv]
        exact hinit
    · simp only [hfree, ↓reduceIte]
      have hnil : s.free.val = [] := List.eq_nil_of_length_eq_zero (by scalar_tac)
      by_cases hmax : s.slots >= 4294967295#usize
      · simp only [hmax, ↓reduceIte, spec_ok, uncurry'_pair]
        have hge : 4294967295 ≤ s.slots.val := by scalar_tac
        refine ⟨fun y hy => ?_, fun slot hs => (nomatch hs)⟩
        cases hy
        refine ⟨rfl, rfl, fun hc => ?_⟩
        rcases hc.2 with hne | hlt
        · exact hne hnil
        · omega
      · simp only [hmax, ↓reduceIte]
        have hlt : s.slots.val < 4294967295 := by scalar_tac
        have hcastu : s.slots.val ≤ UScalar.max UScalarTy.U32 := by scalar_tac
        step as ⟨chunk, hchunk⟩
        have hchunkv : chunk.val = s.slots.val / 1024 := by scalar_tac
        by_cases hc0 : chunk = 0#usize
        · -- a slot of the first chunk
          have hc0' : (chunk = 0#usize) = True := eq_true hc0
          simp only [hc0', ↓reduceIte]
          have hz : s.slots.val / 1024 = 0 := by
            rw [← hchunkv, hc0]
            rfl
          have hfmax : s.first.val.length < Std.Usize.max := by
            have := hg.first
            omega
          step as ⟨v, hv⟩
          step as ⟨n1, hn1⟩
          have hn1v : n1.val = s.slots.val + 1 := by scalar_tac
          step with UScalar.cast_inBounds_spec UScalarTy.U32 s.slots hcastu as ⟨slot, hslot⟩
          have hfl : s.first.val.length = s.slots.val := by
            have := hg.first
            omega
          have hr0 : s.rest.val.length = 0 := by
            have := hg.rest
            omega
          refine allocPost_grow h x hroom hnil hlt hslot hn1v rfl rfl
            ⟨?_, ?_, fun c w hw => ?_⟩ (fun j => ?_)
          · show v.val.length = min (s.slots.val + 1) 1024
            rw [hv, List.length_append, List.length_singleton, hfl]
            omega
          · show s.rest.val.length = (s.slots.val + 1 - 1) / 1024
            rw [hr0]
            omega
          · have hw' : s.rest.val[c]? = some w := hw
            have := get?_lt hw'
            omega
          · by_cases hj : j / 1024 = 0
            · rw [cellAt_first hj]
              show v.val[j % 1024]? = _
              rw [hv]
              by_cases e : j = s.slots.val
              · rw [ite_eq_left e]
                have e2 : j % 1024 = s.first.val.length := by omega
                rw [e2]
                exact get?_snoc_last _ _
              · rw [ite_eq_right e, cellAt_first hj]
                by_cases hlt2 : j % 1024 < s.first.val.length
                · exact get?_append_left hlt2
                · rw [get?_none (l := s.first.val) (by omega)]
                  exact get?_none (by rw [List.length_append, List.length_singleton]; omega)
            · have e : ¬ j = s.slots.val := by omega
              rw [ite_eq_right e]
              exact cellAt_congr_rest hj rfl
        · simp only [hc0, ↓reduceIte]
          have hnz : ¬ s.slots.val / 1024 = 0 := by
            intro e
            apply hc0
            apply UScalar.eq_of_val_eq
            rw [hchunkv, e]
            rfl
          step as ⟨off, hoff⟩
          have hoffv : off.val = s.slots.val % 1024 := by scalar_tac
          by_cases ho0 : off = 0#usize
          · -- the first slot of a new chunk
            have ho0' : (off = 0#usize) = True := eq_true ho0
            simp only [ho0', ↓reduceIte]
            have hm : s.slots.val % 1024 = 0 := by
              rw [← hoffv, ho0]
              rfl
            have hrmax : s.rest.val.length < Std.Usize.max := by
              have := hg.rest
              omega
            have hemp : (alloc.vec.Vec.new (Option T)).val.length < Std.Usize.max := by
              simp
              omega
            step as ⟨cells, hcells⟩
            step as ⟨v, hv⟩
            step as ⟨n1, hn1⟩
            have hn1v : n1.val = s.slots.val + 1 := by scalar_tac
            step with UScalar.cast_inBounds_spec UScalarTy.U32 s.slots hcastu as ⟨slot, hslot⟩
            have hcv : cells.val = [some x] := by
              rw [hcells]
              simp
            have hfl : s.first.val.length = 1024 := by
              have := hg.first
              omega
            have hrl : s.rest.val.length = s.slots.val / 1024 - 1 := by
              have := hg.rest
              omega
            refine allocPost_grow h x hroom hnil hlt hslot hn1v rfl rfl
              ⟨?_, ?_, fun c w hw => ?_⟩ (fun j => ?_)
            · show s.first.val.length = min (s.slots.val + 1) 1024
              rw [hfl]
              omega
            · show v.val.length = (s.slots.val + 1 - 1) / 1024
              rw [hv, List.length_append, List.length_singleton, hrl]
              omega
            · have hw' : (s.rest.val ++ [cells])[c]? = some w := by
                rw [← hv]
                exact hw
              rcases get?_snoc_cases hw' with ⟨hcl, hold⟩ | ⟨hcl, hnew⟩
              · rw [hrl] at hcl
                have h1 : 1024 * (c + 2) ≤ s.slots.val := by omega
                exact chunk_full_of h1 (by omega) (hg.chunk c w hold)
              · rw [hnew, hcv]
                show 1 = min (s.slots.val + 1 - 1024 * (c + 1)) 1024
                omega
            · by_cases hj : j / 1024 = 0
              · have e : ¬ j = s.slots.val := by omega
                rw [ite_eq_right e]
                exact cellAt_congr_first hj rfl
              · by_cases hch : j / 1024 - 1 < s.rest.val.length
                · -- a chunk that was there
                  obtain ⟨w, hw⟩ := get?_some hch
                  have hw2 : v.val[j / 1024 - 1]? = some w := by
                    rw [hv, get?_append_left hch]
                    exact hw
                  have e : ¬ j = s.slots.val := by omega
                  rw [ite_eq_right e,
                    cellAt_rest (s := { s with rest := v, slots := n1 }) hj hw2,
                    cellAt_rest hj hw]
                · by_cases hch2 : j / 1024 - 1 = s.rest.val.length
                  · -- the new chunk
                    have hw2 : v.val[j / 1024 - 1]? = some cells := by
                      rw [hv, hch2]
                      exact get?_snoc_last _ _
                    rw [cellAt_rest (s := { s with rest := v, slots := n1 }) hj hw2, hcv]
                    by_cases e : j = s.slots.val
                    · rw [ite_eq_left e]
                      have e2 : j % 1024 = 0 := by omega
                      rw [e2]
                      rfl
                    · rw [ite_eq_right e, GeoN.cell_ge hg (by omega)]
                      exact get?_none (by show 1 ≤ j % 1024; omega)
                  · -- past the new chunk
                    have e : ¬ j = s.slots.val := by omega
                    rw [ite_eq_right e, GeoN.cell_ge hg (by omega)]
                    exact cellAt_rest_none hj
                      (get?_none (by
                        show v.val.length ≤ j / 1024 - 1
                        rw [hv, List.length_append, List.length_singleton]
                        omega))
          · -- one more slot of the last chunk
            simp only [ho0, ↓reduceIte]
            have hm : ¬ s.slots.val % 1024 = 0 := by
              intro e
              apply ho0
              apply UScalar.eq_of_val_eq
              rw [hoffv, e]
              rfl
            step as ⟨ci, hci⟩
            have hciv : ci.val = s.slots.val / 1024 - 1 := by scalar_tac
            have hcil : ci.val < s.rest.val.length := by
              have := hg.rest
              omega
            have hin : ci < alloc.vec.Vec.len s.rest := by scalar_tac
            simp only [hin, ↓reduceIte]
            step as ⟨w, back, hw, hback⟩
            have hgw : s.rest.val[s.slots.val / 1024 - 1]? = some w := by
              rw [← hciv]
              exact get?_of_getElem hcil hw
            have hwmax : w.val.length < Std.Usize.max := by
              have := hg.chunk _ w hgw
              omega
            step as ⟨w1, hw1⟩
            step as ⟨n1, hn1⟩
            have hn1v : n1.val = s.slots.val + 1 := by scalar_tac
            step with UScalar.cast_inBounds_spec UScalarTy.U32 s.slots hcastu as ⟨slot, hslot⟩
            have hwl : w.val.length = s.slots.val % 1024 := by
              have := hg.chunk _ w hgw
              omega
            have hfl : s.first.val.length = 1024 := by
              have := hg.first
              omega
            have hrl : s.rest.val.length = s.slots.val / 1024 := by
              have := hg.rest
              omega
            have hbv : (back w1).val = s.rest.val.set (s.slots.val / 1024 - 1) w1 := by
              rw [hback, ← hciv]
              simp
            refine allocPost_grow h x hroom hnil hlt hslot hn1v rfl rfl
              ⟨?_, ?_, fun c u hu => ?_⟩ (fun j => ?_)
            · show s.first.val.length = min (s.slots.val + 1) 1024
              rw [hfl]
              omega
            · show (back w1).val.length = (s.slots.val + 1 - 1) / 1024
              rw [hbv, List.length_set, hrl]
              omega
            · have hu' : (s.rest.val.set (s.slots.val / 1024 - 1) w1)[c]? = some u := by
                rw [← hbv]
                exact hu
              by_cases e : c = s.slots.val / 1024 - 1
              · rw [e, get?_set_self' w1 (get?_lt hgw)] at hu'
                have e2 : w1 = u := Option.some.inj hu'
                rw [← e2, hw1, List.length_append, List.length_singleton, hwl, e]
                omega
              · rw [get?_set_ne' w1 e] at hu'
                have hcl := get?_lt hu'
                rw [hrl] at hcl
                have h1 : 1024 * (c + 2) ≤ s.slots.val := by omega
                exact chunk_full_of h1 (by omega) (hg.chunk c u hu')
            · by_cases hj : j / 1024 = 0
              · have e : ¬ j = s.slots.val := by omega
                rw [ite_eq_right e]
                exact cellAt_congr_first hj rfl
              · by_cases hch : j / 1024 - 1 = s.slots.val / 1024 - 1
                · have hw2 : (back w1).val[j / 1024 - 1]? = some w1 := by
                    rw [hbv, hch]
                    exact get?_set_self' w1 (get?_lt hgw)
                  have hgw' : s.rest.val[j / 1024 - 1]? = some w := by rw [hch, hgw]
                  rw [cellAt_rest (s := { s with rest := back w1, slots := n1 }) hj hw2, hw1]
                  by_cases e : j = s.slots.val
                  · rw [ite_eq_left e]
                    have e2 : j % 1024 = w.val.length := by omega
                    rw [e2]
                    exact get?_snoc_last _ _
                  · rw [ite_eq_right e, cellAt_rest hj hgw']
                    by_cases hlt2 : j % 1024 < w.val.length
                    · exact get?_append_left hlt2
                    · rw [get?_none (l := w.val) (by omega)]
                      exact get?_none (by rw [List.length_append, List.length_singleton]; omega)
                · have e : ¬ j = s.slots.val := by
                    intro e
                    rw [e] at hch
                    exact hch rfl
                  rw [ite_eq_right e]
                  unfold cellAt
                  rw [ite_eq_right hj, ite_eq_right hj]
                  show (match (back w1).val[j / 1024 - 1]? with
                    | none => none
                    | some c => c.val[j % 1024]?) = _
                  rw [hbv, get?_set_ne' _ hch]

/-! ## `finish`: the slots in quarantine -/

theorem cellAt_congr {s s' : item_space.ItemSpaceCore T} (hf : s'.first = s.first)
    (hr : s'.rest = s.rest) (j : Nat) : cellAt s' j = cellAt s j := by
  unfold cellAt
  rw [hf, hr]

/-- `extend_from_slice` on slots: the slots, one list after the other. -/
theorem extend_u32_spec (v : alloc.vec.Vec Std.U32) (sl : Slice Std.U32)
    (h : v.val.length + sl.val.length ≤ Std.Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU32 v sl ⦃ r => r.val = v.val ++ sl.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  have h' : v.length + sl.length ≤ Std.Usize.max := h
  simp only [h', ↓reduceDIte]
  have hc := @List.clone_spec _ core.clone.CloneU32.clone sl.val (by intros; rfl)
  apply spec_bind hc
  intro l hl
  simp [hl.1]

/-- What `release` does. -/
structure ReleasePost (s s' : item_space.ItemSpaceCore T) : Prop where
  first : s'.first = s.first
  rest : s'.rest = s.rest
  slots : s'.slots = s.slots
  /-- the slots in quarantine go to the end of `free`, in their order -/
  free : s'.free.val = s.free.val ++ s.quarantine.val
  quarantine : s'.quarantine.val = []

/-- `release` lets `alloc` fill the slots in quarantine: they go to the end
of `free`, in their order, and nothing else changes. -/
theorem release_spec (s : item_space.ItemSpaceCore T) (h : WF s) :
    item_space.ItemSpaceCore.release s ⦃ s' => ReleasePost s s' ⦄ := by
  unfold item_space.ItemSpaceCore.release
  have hle := h.empties_le
  have hbound := h.bound
  have hu32 : 4294967295 ≤ Std.Usize.max := by scalar_tac
  step as ⟨b, hb⟩
  by_cases hq : s.quarantine.val.length = 0
  · have hbt : b = true := by
      rw [hb]
      exact hq
    simp only [hbt, ↓reduceIte, spec_ok]
    have hnil : s.quarantine.val = [] := List.eq_nil_of_length_eq_zero hq
    refine ⟨rfl, rfl, rfl, ?_, hnil⟩
    rw [hnil, List.append_nil]
  · have hbf : b = false := by
      cases b with
      | false => rfl
      | true => exact absurd (hb.mp rfl) hq
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    have hd : (alloc.vec.Vec.deref s.quarantine).val = s.quarantine.val := by
      simp [alloc.vec.Vec.deref]
    have hroom : s.free.val.length + (alloc.vec.Vec.deref s.quarantine).val.length ≤
        Std.Usize.max := by
      rw [hd]
      omega
    step with extend_u32_spec s.free (alloc.vec.Vec.deref s.quarantine) hroom as ⟨v, hv⟩
    step with alloc.vec.Vec.resize_spec core.clone.CloneU32 s.quarantine 0#usize 0#u32 rfl
      as ⟨q, hq'⟩
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · show v.val = s.free.val ++ s.quarantine.val
      rw [hv, hd]
    · show q.val = []
      rw [hq']
      exact resize_take _ 0 _ (Nat.zero_le _)

/-- The invariant after `release`. -/
theorem WF.released {s s' : item_space.ItemSpaceCore T} (h : WF s) (hR : ReleasePost s s') :
    WF s' := by
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · show GeoN s'.slots.val s'
    rw [hR.slots]
    have hg : GeoN s.slots.val s := h.geo
    exact hg.of_shape (by rw [hR.first]) (by rw [hR.rest])
  · rw [hR.slots]
    exact h.bound
  · rw [hR.free, hR.quarantine, List.append_nil]
    exact h.nodup
  · rw [hR.free, hR.quarantine, List.append_nil, cellAt_congr hR.first hR.rest]
    exact h.empty i

/-- When `finish` moves the items of an arena of `slots` slots, `free` of
them empty: some slot is empty, and all of them are, or more than two fifths
of at least `256`. -/
def Sparse (free slots : Nat) : Prop :=
  free ≠ 0 ∧ (free = slots ∨ (256 ≤ slots ∧ 2 * slots < 5 * free))

/-- `sparse` says whether `finish` moves the items. -/
theorem sparse_spec (s : item_space.ItemSpaceCore T) (hle : s.free.val.length ≤ s.slots.val)
    (hb : s.slots.val ≤ 4294967295) :
    item_space.ItemSpaceCore.sparse s ⦃ b =>
      (b = true ↔ Sparse s.free.val.length s.slots.val) ⦄ := by
  unfold item_space.ItemSpaceCore.sparse Sparse
  simp only [item_space.COMPACT_SLOTS]
  by_cases h0 : alloc.vec.Vec.len s.free = 0#usize
  · have h0' : (alloc.vec.Vec.len s.free = 0#usize) = True := eq_true h0
    simp only [h0', ↓reduceIte, spec_ok]
    have hz : s.free.val.length = 0 := by
      have := congrArg UScalar.val h0
      scalar_tac
    constructor
    · intro e
      cases e
    · rintro ⟨hne, _⟩
      exact absurd hz hne
  · simp only [h0, ↓reduceIte]
    have hnz : s.free.val.length ≠ 0 := by
      intro hz
      apply h0
      apply UScalar.eq_of_val_eq
      rw [usize_zero_val]
      scalar_tac
    by_cases hall : alloc.vec.Vec.len s.free = s.slots
    · have hall' : (alloc.vec.Vec.len s.free = s.slots) = True := eq_true hall
      simp only [hall', ↓reduceIte, spec_ok]
      have he : s.free.val.length = s.slots.val := by
        have := congrArg UScalar.val hall
        scalar_tac
      constructor
      · intro _
        exact ⟨hnz, Or.inl he⟩
      · intro _
        trivial
    · simp only [hall, ↓reduceIte]
      have hne : s.free.val.length ≠ s.slots.val := by
        intro he
        apply hall
        apply UScalar.eq_of_val_eq
        scalar_tac
      by_cases hbig : s.slots >= 256#usize
      · simp only [hbig, ↓reduceIte]
        have hbigv : 256 ≤ s.slots.val := by scalar_tac
        have hc1 : (alloc.vec.Vec.len s.free).val ≤ UScalar.max UScalarTy.U64 := by scalar_tac
        step with UScalar.cast_inBounds_spec UScalarTy.U64 (alloc.vec.Vec.len s.free) hc1
          as ⟨f, hf⟩
        have hfv : f.val = s.free.val.length := by scalar_tac
        step as ⟨f5, hf5⟩
        have hc2 : s.slots.val ≤ UScalar.max UScalarTy.U64 := by scalar_tac
        step with UScalar.cast_inBounds_spec UScalarTy.U64 s.slots hc2 as ⟨n, hn⟩
        step as ⟨n2, hn2⟩
        have hf5v : f5.val = 5 * s.free.val.length := by scalar_tac
        have hn2v : n2.val = 2 * s.slots.val := by scalar_tac
        constructor
        · intro hd
          have hgt : n2.val < f5.val := by
            have := of_decide_eq_true hd
            scalar_tac
          exact ⟨hnz, Or.inr ⟨hbigv, by omega⟩⟩
        · rintro ⟨_, he | ⟨_, hlt⟩⟩
          · exact absurd he hne
          · apply decide_eq_true
            scalar_tac
      · simp only [hbig, ↓reduceIte, spec_ok]
        have hsmall : s.slots.val < 256 := by scalar_tac
        constructor
        · intro e
          cases e
        · rintro ⟨_, he | ⟨hge, _⟩⟩
          · exact absurd he hne
          · omega

/-! ## `finish`: moving the items to the front -/

theorem cell_empty_of_item_none {s : item_space.ItemSpaceCore T} {i : Nat} {c : Option T}
    (hc : cellAt s i = some c) (hi : item s i = none) : cellAt s i = some none := by
  cases c with
  | none => exact hc
  | some x =>
    rw [item_some hc] at hi
    cases hi

/-- How many slots hold an item. -/
def liveCount (s : item_space.ItemSpaceCore T) : Nat :=
  countSome ((List.range s.slots.val).map (item s))

/-- The loop of `compact` when it is done with the slots below `old`: `s0`
is the arena it started with, of `n` slots; `live` items are in the slots
below `live`, in their order, and the table says where each one went. -/
structure Compacting (s0 : item_space.ItemSpaceCore T) (n : Nat)
    (s : item_space.ItemSpaceCore T) (moved : List Std.U32) (live old : Nat) : Prop where
  bounds : live ≤ old ∧ old ≤ n
  geo : GeoN n s
  slots : s.slots = s0.slots
  free : s.free = s0.free
  quarantine : s.quarantine = s0.quarantine
  length : moved.length = n
  /-- the slots not reached yet are as they were -/
  ahead : ∀ j, old ≤ j → cellAt s j = cellAt s0 j
  /-- the slots between the items and the scan are empty -/
  gap : ∀ j, live ≤ j → j < old → cellAt s j = some none
  /-- the table says nothing yet of the slots not reached -/
  zero : ∀ j, old ≤ j → j < n → ∃ m : Std.U32, moved[j]? = some m ∧ m.val = 0
  /-- a slot without an item has the entry `0` -/
  dead : ∀ j, j < old → item s0 j = none → ∃ m : Std.U32, moved[j]? = some m ∧ m.val = 0
  /-- an item is in the slot its entry names, one less -/
  kept : ∀ j x, j < old → item s0 j = some x →
    ∃ m : Std.U32, moved[j]? = some m ∧ 0 < m.val ∧ cellAt s (m.val - 1) = some (some x)
  /-- no entry names a slot past the items -/
  le : ∀ j (m : Std.U32), j < old → moved[j]? = some m → m.val ≤ live
  /-- every slot below `live` is named -/
  onto : ∀ r, r < live → ∃ j, ∃ m : Std.U32, j < old ∧ moved[j]? = some m ∧ m.val = r + 1
  /-- in the order of the slots -/
  mono : ∀ j1 j2 (m1 m2 : Std.U32), j1 < j2 → j2 < old → moved[j1]? = some m1 →
    moved[j2]? = some m2 → 0 < m1.val → 0 < m2.val → m1.val < m2.val
  /-- `live` counts the items met -/
  count : live = countSome ((List.range old).map (item s0))

theorem countSome_range_succ (f : Nat → Option T) (k : Nat) :
    countSome ((List.range (k + 1)).map f) = countSome ((List.range k).map f) + countSome [f k] := by
  rw [List.range_succ, List.map_append, countSome_append]
  rfl

/-- The scan passes a slot without an item. -/
theorem Compacting.skip {s0 s : item_space.ItemSpaceCore T} {n live old : Nat}
    {moved : List Std.U32} (hI : Compacting s0 n s moved live old) (hold : old < n)
    (hx : item s0 old = none) : Compacting s0 n s moved live (old + 1) := by
  obtain ⟨m0, hm0, hm0z⟩ := hI.zero old (Nat.le_refl _) hold
  have hb := hI.bounds
  refine ⟨⟨by omega, by omega⟩, hI.geo, hI.slots, hI.free, hI.quarantine, hI.length,
    fun j hj => hI.ahead j (by omega), fun j h1 h2 => ?_, fun j h1 h2 => hI.zero j (by omega) h2,
    fun j hj hd => ?_, fun j x hj hk => ?_, fun j m hj hm => ?_, fun r hr => ?_,
    fun j1 j2 m1 m2 h12 h2 e1 e2 p1 p2 => ?_, ?_⟩
  · by_cases e : j = old
    · rw [e]
      obtain ⟨c, hc⟩ := hI.geo.cell_lt hold
      have ha := hI.ahead old (Nat.le_refl _)
      have hi : item s old = none := by
        rw [item_congr ha]
        exact hx
      exact cell_empty_of_item_none hc hi
    · exact hI.gap j h1 (by omega)
  · by_cases e : j = old
    · rw [e]
      exact ⟨m0, hm0, hm0z⟩
    · exact hI.dead j (by omega) hd
  · by_cases e : j = old
    · rw [e, hx] at hk
      cases hk
    · exact hI.kept j x (by omega) hk
  · by_cases e : j = old
    · rw [e, hm0] at hm
      have e2 : m0 = m := Option.some.inj hm
      rw [← e2, hm0z]
      omega
    · exact hI.le j m (by omega) hm
  · obtain ⟨j, m, hj, hm, hv⟩ := hI.onto r hr
    exact ⟨j, m, by omega, hm, hv⟩
  · by_cases e : j2 = old
    · rw [e, hm0] at e2
      have e3 : m0 = m2 := Option.some.inj e2
      rw [← e3, hm0z] at p2
      omega
    · exact hI.mono j1 j2 m1 m2 h12 (by omega) e1 e2 p1 p2
  · rw [countSome_range_succ, hx]
    exact hI.count

/-- The scan meets an item and puts it after the ones it met before. -/
theorem Compacting.keep {s0 s s' : item_space.ItemSpaceCore T} {n live old : Nat}
    {moved : List Std.U32} (hI : Compacting s0 n s moved live old) (hold : old < n) {x : T}
    (hx : item s0 old = some x) {m : Std.U32} (hm : m.val = live + 1) (hgeo : GeoN n s')
    (hslots : s'.slots = s0.slots) (hfree : s'.free = s0.free)
    (hq : s'.quarantine = s0.quarantine) (hlive : cellAt s' live = some (some x))
    (hgone : live < old → cellAt s' old = some none)
    (hother : ∀ j, j ≠ live → j ≠ old → cellAt s' j = cellAt s j) :
    Compacting s0 n s' (moved.set old m) (live + 1) (old + 1) := by
  have hb := hI.bounds
  have holdl : old < moved.length := by
    rw [hI.length]
    exact hold
  have hself : (moved.set old m)[old]? = some m := get?_set_self' m holdl
  have hne : ∀ j, j ≠ old → (moved.set old m)[j]? = moved[j]? := fun j hj => get?_set_ne' m hj
  refine ⟨⟨by omega, by omega⟩, hgeo, hslots, hfree, hq, by rw [List.length_set]; exact hI.length,
    fun j hj => ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun j hj hd => ?_, fun j y hj hk => ?_,
    fun j m' hj hm' => ?_, fun r hr => ?_, fun j1 j2 m1 m2 h12 h2 e1 e2 p1 p2 => ?_, ?_⟩
  · rw [hother j (by omega) (by omega)]
    exact hI.ahead j (by omega)
  · by_cases e : j = old
    · rw [e]
      exact hgone (by omega)
    · rw [hother j (by omega) e]
      exact hI.gap j (by omega) (by omega)
  · rw [hne j (by omega)]
    exact hI.zero j (by omega) h2
  · have e : j ≠ old := by
      intro e
      rw [e, hx] at hd
      cases hd
    rw [hne j e]
    exact hI.dead j (by omega) hd
  · by_cases e : j = old
    · rw [e, hx] at hk
      have e2 : x = y := Option.some.inj hk
      rw [e]
      refine ⟨m, hself, by omega, ?_⟩
      have e3 : m.val - 1 = live := by omega
      rw [e3, ← e2]
      exact hlive
    · obtain ⟨m', hm', hpos, hc⟩ := hI.kept j y (by omega) hk
      have hle' := hI.le j m' (by omega) hm'
      refine ⟨m', by rw [hne j e]; exact hm', hpos, ?_⟩
      rw [hother _ (by omega) (by omega)]
      exact hc
  · by_cases e : j = old
    · rw [e, hself] at hm'
      have e2 : m = m' := Option.some.inj hm'
      rw [← e2]
      omega
    · rw [hne j e] at hm'
      have := hI.le j m' (by omega) hm'
      omega
  · by_cases e : r = live
    · exact ⟨old, m, by omega, hself, by omega⟩
    · obtain ⟨j, m', hj, hm', hv⟩ := hI.onto r (by omega)
      exact ⟨j, m', by omega, by rw [hne j (by omega)]; exact hm', hv⟩
  · have hj1 : j1 ≠ old := by omega
    rw [hne j1 hj1] at e1
    have hle1 := hI.le j1 m1 (by omega) e1
    by_cases e : j2 = old
    · rw [e, hself] at e2
      have e3 : m = m2 := Option.some.inj e2
      rw [← e3]
      omega
    · rw [hne j2 e] at e2
      exact hI.mono j1 j2 m1 m2 h12 (by omega) e1 e2 p1 p2
  · rw [countSome_range_succ, hx, ← hI.count]
    rfl

/-- One step of `compact`: the scan passes the slot `old`. -/
theorem compact_step_spec (s0 : item_space.ItemSpaceCore T) (n : Nat) (hn : n ≤ 4294967295)
    (s : item_space.ItemSpaceCore T) (moved : Slice Std.U32) (live old : Std.Usize)
    (hI : Compacting s0 n s moved.val live.val old.val) (hold : old.val < n) :
    item_space.ItemSpaceCore.compact_step s moved live old ⦃ live' s' moved' =>
      Compacting s0 n s' moved'.val live'.val (old.val + 1) ⦄ := by
  unfold item_space.ItemSpaceCore.compact_step
  have hb := hI.bounds
  have hu32 : 4294967295 ≤ Std.Usize.max := by scalar_tac
  have hml : old.val < moved.val.length := by
    rw [hI.length]
    exact hold
  have hahead : cellAt s old.val = cellAt s0 old.val := hI.ahead old.val (Nat.le_refl _)
  have hitem : item s old.val = item s0 old.val := item_congr hahead
  have hlmax : live.val < Std.Usize.max := by omega
  by_cases heq : old = live
  · -- no slot before this one is empty: its item stays
    have heq' : (old = live) = True := eq_true heq
    simp only [heq', ↓reduceIte]
    step with holds_spec s old as ⟨b, hb'⟩
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
      have hnone : item s0 old.val = none := by
        rw [← hitem]
        cases hi : item s old.val with
        | none => rfl
        | some y =>
          have := hb'.mpr ⟨y, hi⟩
          cases this
      exact hI.skip hold hnone
    | true =>
      simp only [↓reduceIte]
      obtain ⟨y, hy⟩ := hb'.mp rfl
      have hy0 : item s0 old.val = some y := by rw [← hitem, hy]
      step as ⟨next, hnext⟩
      have hnextv : next.val = live.val + 1 := by scalar_tac
      have hc : next.val ≤ UScalar.max UScalarTy.U32 := by scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.U32 next hc as ⟨m, hm⟩
      step as ⟨moved1, hmoved1⟩
      have hmv : moved1.val = moved.val.set old.val m := by
        rw [hmoved1]
        simp
      show Compacting s0 n s moved1.val next.val (old.val + 1)
      rw [hmv, hnextv]
      refine hI.keep hold hy0 (by rw [hm, hnextv]) hI.geo hI.slots hI.free hI.quarantine ?_
        (fun h => ?_) (fun j _ _ => rfl)
      · rw [← heq]
        exact cell_of_item hy
      · rw [heq] at h
        exact absurd h (Nat.lt_irrefl _)
  · simp only [heq, ↓reduceIte]
    have hlk : live.val < old.val := by
      have hne : live.val ≠ old.val := by
        intro e
        apply heq
        apply UScalar.eq_of_val_eq
        rw [e]
      omega
    step with take_spec s old as ⟨o, s2, htake⟩
    have hT : TakePost s old.val o s2 := htake
    cases o with
    | none =>
      simp only [spec_ok, uncurry'_pair]
      have hx : item s0 old.val = none := by
        rw [← hitem]
        exact hT.answer.symm
      rw [hT.same rfl]
      exact hI.skip hold hx
    | some y =>
      simp only []
      have hy : item s old.val = some y := hT.answer.symm
      have hy0 : item s0 old.val = some y := by rw [← hitem, hy]
      have hu : Upd s old.val none s2 := hT.taken y rfl
      have hck : cellAt s old.val = some (some y) := cell_of_item hy
      have hgap : cellAt s live.val = some none := hI.gap live.val (Nat.le_refl _) hlk
      have hc2 : cellAt s2 live.val = some none := by
        rw [hu.cell live.val, ite_eq_right (by omega), hgap]
      step with put_spec s2 live y as ⟨o2, s3, hput⟩
      have hP : PutPost s2 live.val y o2 s3 := hput
      have hsome2 : cellAt s2 live.val ≠ none := by
        rw [hc2]
        exact fun e => (nomatch e)
      obtain ⟨_, hu2⟩ := hP.put hsome2
      step as ⟨next, hnext⟩
      have hnextv : next.val = live.val + 1 := by scalar_tac
      have hc : next.val ≤ UScalar.max UScalarTy.U32 := by scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.U32 next hc as ⟨m, hm⟩
      step as ⟨moved1, hmoved1⟩
      have hmv : moved1.val = moved.val.set old.val m := by
        rw [hmoved1]
        simp
      show Compacting s0 n s3 moved1.val next.val (old.val + 1)
      rw [hmv, hnextv]
      refine hI.keep hold hy0 (by rw [hm, hnextv]) (hu2.geo (hu.geo hI.geo))
        (by rw [hu2.slots, hu.slots]; exact hI.slots)
        (by rw [hu2.free, hu.free]; exact hI.free)
        (by rw [hu2.quarantine, hu.quarantine]; exact hI.quarantine) ?_ (fun _ => ?_)
        (fun j h1 h2 => ?_)
      · rw [hu2.cell live.val, ite_eq_left rfl, hc2]
        rfl
      · rw [hu2.cell old.val, ite_eq_right (by omega), hu.cell old.val, ite_eq_left rfl, hck]
        rfl
      · rw [hu2.cell j, ite_eq_right h1, hu.cell j, ite_eq_right h2]

theorem compact_loop_spec (s0 : item_space.ItemSpaceCore T) (n : Std.Usize)
    (hn : n.val ≤ 4294967295) (s : item_space.ItemSpaceCore T) (moved : alloc.vec.Vec Std.U32)
    (live old : Std.Usize) (hinv : Compacting s0 n.val s moved.val live.val old.val) :
    item_space.ItemSpaceCore.compact_loop s n moved live old ⦃ r =>
      Compacting s0 n.val r.1 r.2.1.val r.2.2.val n.val ⦄ := by
  unfold item_space.ItemSpaceCore.compact_loop
  refine loop.spec_decr_nat
    (fun ((_, _, _, k) : item_space.ItemSpaceCore T × alloc.vec.Vec Std.U32 × Std.Usize ×
      Std.Usize) => n.val - k.val)
    (fun ((t, mv, l, k) : item_space.ItemSpaceCore T × alloc.vec.Vec Std.U32 × Std.Usize ×
      Std.Usize) => Compacting s0 n.val t mv.val l.val k.val)
    (fun (r : item_space.ItemSpaceCore T × alloc.vec.Vec Std.U32 × Std.Usize) =>
      Compacting s0 n.val r.1 r.2.1.val r.2.2.val n.val)
    _ (s, moved, live, old) ?_ hinv
  intro ⟨t, mv, l, k⟩ hinv0
  have hI : Compacting s0 n.val t mv.val l.val k.val := hinv0
  unfold item_space.ItemSpaceCore.compact_loop.body
  simp only
  by_cases hlt : k < n
  · simp only [hlt, ↓reduceIte, lift, alloc.vec.Vec.deref_mut]
    have hkn : k.val < n.val := by scalar_tac
    step with compact_step_spec s0 n.val hn t mv.slice l k hI hkn as ⟨l1, t1, sl1, hp⟩
    step as ⟨kn, hkn'⟩
    have hknv : kn.val = k.val + 1 := by scalar_tac
    refine ⟨?_, by scalar_tac⟩
    show Compacting s0 n.val t1 sl1.val l1.val kn.val
    rw [hknv]
    exact hp
  · simp only [hlt, ↓reduceIte, spec_ok]
    have e : k.val = n.val := by
      have := hI.bounds
      scalar_tac
    have hI' := hI
    rw [e] at hI'
    exact hI'

/-- `compact` moves every item to the first empty slot before it. -/
theorem compact_spec (s : item_space.ItemSpaceCore T) (hg : GeoN s.slots.val s)
    (hn : s.slots.val ≤ 4294967295) :
    item_space.ItemSpaceCore.compact s ⦃ r s' =>
      Compacting s s.slots.val s' r.1.val r.2.val s.slots.val ⦄ := by
  unfold item_space.ItemSpaceCore.compact
  step with alloc.vec.from_elem_spec core.clone.CloneU32 0#u32 s.slots rfl as ⟨moved, hmoved, _⟩
  have hinit : Compacting s s.slots.val s moved.val (0#usize : Std.Usize).val
      (0#usize : Std.Usize).val := by
    rw [usize_zero_val]
    refine ⟨⟨Nat.le_refl _, Nat.zero_le _⟩, hg, rfl, rfl, rfl, by rw [hmoved, List.length_replicate],
      fun j _ => rfl, fun j h1 h2 => by omega, fun j _ h2 => ?_, fun j hj _ => by omega,
      fun j x hj _ => by omega, fun j m hj _ => by omega, fun r hr => by omega,
      fun j1 j2 m1 m2 _ h2 _ _ _ _ => by omega, rfl⟩
    refine ⟨0#u32, ?_, rfl⟩
    rw [hmoved, Ring.get?_replicate, ite_eq_left h2]
  refine spec_bind (compact_loop_spec s s.slots hn s moved 0#usize 0#usize hinit) (fun p hp => ?_)
  obtain ⟨s1, moved1, live⟩ := p
  refine (spec_ok _).mpr ?_
  show Compacting s s.slots.val s1 moved1.val live.val s.slots.val
  exact hp

/-! ## `finish`: letting go of the chunks after the items -/

theorem get?_take_lt {α : Type} : ∀ (l : List α) {n j : Nat}, j < n → (l.take n)[j]? = l[j]?
  | [], n, j, _ => by simp
  | a :: t, 0, j, h => absurd h (Nat.not_lt_zero _)
  | a :: t, n + 1, 0, _ => rfl
  | a :: t, n + 1, j + 1, h => by
    have ih := get?_take_lt t (n := n) (j := j) (by omega)
    simpa using ih

/-- The loop of `head_of` after `i` slots. -/
structure Heading (c0 : List (Option T)) (c head : List (Option T)) (i keep : Nat) : Prop where
  bound : i ≤ keep
  length : c.length = c0.length
  head : head = c0.take i
  rest : ∀ j, i ≤ j → c[j]? = c0[j]?

theorem head_of_loop_spec (c0 : List (Option T)) (chunk : Slice (Option T)) (keep : Std.Usize)
    (head : alloc.vec.Vec (Option T)) (i : Std.Usize) (hk : keep.val ≤ c0.length)
    (hinv : Heading c0 chunk.val head.val i.val keep.val) :
    item_space.head_of_loop chunk keep head i ⦃ r => r.1.val = c0.take keep.val ⦄ := by
  unfold item_space.head_of_loop
  refine loop.spec_decr_nat
    (fun ((_, _, k) : Slice (Option T) × alloc.vec.Vec (Option T) × Std.Usize) =>
      keep.val - k.val)
    (fun ((c, hd, k) : Slice (Option T) × alloc.vec.Vec (Option T) × Std.Usize) =>
      Heading c0 c.val hd.val k.val keep.val)
    (fun (r : alloc.vec.Vec (Option T) × Slice (Option T)) => r.1.val = c0.take keep.val)
    _ (chunk, head, i) ?_ hinv
  intro ⟨c, hd, k⟩ hinv0
  have hI : Heading c0 c.val hd.val k.val keep.val := hinv0
  have hb := hI.bound
  have hlen := hI.length
  unfold item_space.head_of_loop.body
  simp only
  by_cases hlt : k < keep
  · simp only [hlt, ↓reduceIte]
    have hkk : k.val < keep.val := by scalar_tac
    have hkc : k.val < c.val.length := by omega
    step as ⟨o, back, ho, hback⟩
    have hgo : c0[k.val]? = some o := by
      rw [← hI.rest k.val (Nat.le_refl _)]
      exact get?_of_getElem hkc ho
    have hhl : hd.val.length < Std.Usize.max := by
      rw [hI.head, List.length_take]
      scalar_tac
    step as ⟨hd1, hhd1⟩
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = k.val + 1 := by scalar_tac
    have hbv : (back none).val = c.val.set k.val none := by
      rw [hback]
      simp
    refine ⟨?_, by scalar_tac⟩
    show Heading c0 (back none).val hd1.val k1.val keep.val
    rw [hbv, hk1v, hhd1]
    refine ⟨by omega, by rw [List.length_set]; exact hlen, ?_, fun j hj => ?_⟩
    · rw [take_succ_get hgo, hI.head]
    · rw [get?_set_ne' none (by omega)]
      exact hI.rest j (by omega)
  · simp only [hlt, ↓reduceIte, spec_ok]
    have e : k.val = keep.val := by scalar_tac
    show hd.val = c0.take keep.val
    rw [← e]
    exact hI.head

/-- `head_of` answers the first `keep` slots of a chunk. -/
theorem head_of_spec (chunk : Slice (Option T)) (keep : Std.Usize)
    (hk : keep.val ≤ chunk.val.length) :
    item_space.head_of chunk keep ⦃ head _rest => head.val = chunk.val.take keep.val ⦄ := by
  unfold item_space.head_of
  have hinit : Heading chunk.val chunk.val
      (alloc.vec.Vec.with_capacity (Option T) keep).val (0#usize : Std.Usize).val keep.val := by
    rw [usize_zero_val]
    refine ⟨Nat.zero_le _, rfl, ?_, fun j _ => rfl⟩
    simp [alloc.vec.Vec.with_capacity]
  refine spec_mono (head_of_loop_spec chunk.val chunk keep _ 0#usize hk hinit) ?_
  rintro ⟨a, b⟩ h
  exact h

/-- `cut` answers the first `keep` slots of a chunk that has as many, in a
vector of its own. -/
theorem cut_spec (chunk : Slice (Option T)) (keep : Std.Usize)
    (hk : keep.val ≤ chunk.val.length) :
    item_space.cut chunk keep ⦃ v _rest => v.val = chunk.val.take keep.val ⦄ := by
  unfold item_space.cut
  simp only
  by_cases hlt : keep < Slice.len chunk
  · simp only [hlt, ↓reduceIte]
    exact head_of_spec chunk keep hk
  · simp only [hlt, ↓reduceIte]
    have hlen : (Slice.len chunk).val = chunk.val.length := by scalar_tac
    have hge : chunk.val.length ≤ keep.val := by scalar_tac
    refine spec_mono (head_of_spec chunk (Slice.len chunk) (by omega)) ?_
    rintro ⟨v, r⟩ hv
    have hv' : v.val = chunk.val.take (Slice.len chunk).val := hv
    show v.val = chunk.val.take keep.val
    rw [hv', hlen, List.take_of_length_le (Nat.le_refl _), List.take_of_length_le hge]

/-- The loop of `let_go` at the chunk `i`: the chunks before `start` are as
they were. -/
structure Letting (c0 c : List (alloc.vec.Vec (Option T))) (start i : Nat) : Prop where
  length : c.length = c0.length
  before : ∀ j, j < start → c[j]? = c0[j]?
  bound : start ≤ i

theorem let_go_loop_spec (c0 : List (alloc.vec.Vec (Option T)))
    (chunks : Slice (alloc.vec.Vec (Option T))) (start : Nat) (i : Std.Usize)
    (hinv : Letting c0 chunks.val start i.val) :
    item_space.let_go_loop chunks i ⦃ r =>
      r.val.length = c0.length ∧ ∀ j, j < start → r.val[j]? = c0[j]? ⦄ := by
  unfold item_space.let_go_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : Slice (alloc.vec.Vec (Option T)) × Std.Usize) => c0.length - k.val)
    (fun ((c, k) : Slice (alloc.vec.Vec (Option T)) × Std.Usize) => Letting c0 c.val start k.val)
    (fun (r : Slice (alloc.vec.Vec (Option T))) =>
      r.val.length = c0.length ∧ ∀ j, j < start → r.val[j]? = c0[j]?)
    _ (chunks, i) ?_ hinv
  intro ⟨c, k⟩ hinv0
  have hI : Letting c0 c.val start k.val := hinv0
  have hlen := hI.length
  have hb := hI.bound
  unfold item_space.let_go_loop.body
  simp only
  by_cases hlt : k < Slice.len c
  · simp only [hlt, ↓reduceIte]
    have hkl : k.val < c.val.length := by scalar_tac
    have hk0 : k.val < c0.length := by omega
    step as ⟨v, back, hv, hback⟩
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = k.val + 1 := by scalar_tac
    have hbv : (back (alloc.vec.Vec.new (Option T))).val =
        c.val.set k.val (alloc.vec.Vec.new (Option T)) := by
      rw [hback]
      simp
    refine ⟨?_, by scalar_tac⟩
    show Letting c0 (back (alloc.vec.Vec.new (Option T))).val start k1.val
    rw [hbv, hk1v]
    refine ⟨by rw [List.length_set]; exact hlen, fun j hj => ?_, by omega⟩
    rw [get?_set_ne' _ (by omega)]
    exact hI.before j hj
  · simp only [hlt, ↓reduceIte, spec_ok]
    exact ⟨hlen, hI.before⟩

/-- `let_go` empties the chunks from `start` on and leaves the ones before
it. -/
theorem let_go_spec (chunks : Slice (alloc.vec.Vec (Option T))) (start : Std.Usize) :
    item_space.let_go chunks start ⦃ r =>
      r.val.length = chunks.val.length ∧ ∀ j, j < start.val → r.val[j]? = chunks.val[j]? ⦄ :=
  let_go_loop_spec chunks.val chunks start.val start ⟨rfl, fun _ _ => rfl, Nat.le_refl _⟩

/-- The loop of `shrink` after `i` chunks: every chunk it is done with is in
`rest`, in a vector of its own that holds the same slots. -/
structure Shrinking (v0 : List (alloc.vec.Vec (Option T))) (v rest : List (alloc.vec.Vec (Option T)))
    (i stop : Nat) : Prop where
  bound : i ≤ stop
  length : v.length = v0.length
  count : rest.length = i
  copied : ∀ j, j < i → ∃ c c', v0[j]? = some c ∧ rest[j]? = some c' ∧ c'.val = c.val
  ahead : ∀ j, i ≤ j → v[j]? = v0[j]?

theorem shrink_loop_spec (v0 : List (alloc.vec.Vec (Option T)))
    (v : alloc.vec.Vec (alloc.vec.Vec (Option T))) (chunk : Std.Usize)
    (rest : alloc.vec.Vec (alloc.vec.Vec (Option T))) (i : Std.Usize)
    (hc : chunk.val ≤ v0.length) (hpos : 0 < chunk.val)
    (hfull : ∀ j c, j < chunk.val - 1 → v0[j]? = some c → c.val.length = 1024)
    (hinv : Shrinking v0 v.val rest.val i.val (chunk.val - 1)) :
    item_space.ItemSpaceCore.shrink_loop v chunk rest i ⦃ r =>
      r.val.length = chunk.val - 1 ∧
        ∀ j, j < chunk.val - 1 → ∃ c c', v0[j]? = some c ∧ r.val[j]? = some c' ∧ c'.val = c.val ⦄ := by
  unfold item_space.ItemSpaceCore.shrink_loop
  refine loop.spec_decr_nat
    (fun ((_, _, k) : alloc.vec.Vec (alloc.vec.Vec (Option T)) ×
      alloc.vec.Vec (alloc.vec.Vec (Option T)) × Std.Usize) => chunk.val - 1 - k.val)
    (fun ((w, r, k) : alloc.vec.Vec (alloc.vec.Vec (Option T)) ×
      alloc.vec.Vec (alloc.vec.Vec (Option T)) × Std.Usize) =>
      Shrinking v0 w.val r.val k.val (chunk.val - 1))
    (fun (r : alloc.vec.Vec (alloc.vec.Vec (Option T))) =>
      r.val.length = chunk.val - 1 ∧
        ∀ j, j < chunk.val - 1 → ∃ c c', v0[j]? = some c ∧ r.val[j]? = some c' ∧ c'.val = c.val)
    _ (v, rest, i) ?_ hinv
  intro ⟨w, r, k⟩ hinv0
  have hI : Shrinking v0 w.val r.val k.val (chunk.val - 1) := hinv0
  have hb := hI.bound
  have hlen := hI.length
  have hcount := hI.count
  unfold item_space.ItemSpaceCore.shrink_loop.body
  simp only
  step as ⟨stop, hstop⟩
  have hstopv : stop.val = chunk.val - 1 := by scalar_tac
  by_cases hlt : k < stop
  · simp only [hlt, ↓reduceIte]
    have hks : k.val < chunk.val - 1 := by scalar_tac
    have hkw : k.val < w.val.length := by omega
    step as ⟨c, back, hcv, hback⟩
    have hgc : v0[k.val]? = some c := by
      rw [← hI.ahead k.val (Nat.le_refl _)]
      exact get?_of_getElem hkw hcv
    have hclen : c.val.length = 1024 := hfull k.val c hks hgc
    have hkeep : (item_space.CHUNK_SIZE).val ≤ c.slice.val.length := by
      rw [chunk_size_val]
      show 1024 ≤ c.val.length
      omega
    simp only [lift, alloc.vec.Vec.deref_mut]
    step with cut_spec c.slice item_space.CHUNK_SIZE hkeep as ⟨c1, _c, hc1⟩
    have hc1v : c1.val = c.val := by
      have h : c1.val = c.val.take (item_space.CHUNK_SIZE).val := hc1
      rw [h, chunk_size_val]
      exact List.take_of_length_le (by omega)
    have hrl : r.val.length < Std.Usize.max := by
      rw [hcount]
      scalar_tac
    step as ⟨r1, hr1⟩
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = k.val + 1 := by scalar_tac
    have hbv : (back (alloc.vec.Vec.new (Option T))).val =
        w.val.set k.val (alloc.vec.Vec.new (Option T)) := by
      rw [hback]
      simp
    refine ⟨?_, by scalar_tac⟩
    show Shrinking v0 (back (alloc.vec.Vec.new (Option T))).val r1.val k1.val (chunk.val - 1)
    rw [hbv, hk1v, hr1]
    refine ⟨by omega, by rw [List.length_set]; exact hlen, ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [List.length_append, List.length_singleton, hcount]
    · by_cases e : j = k.val
      · refine ⟨c, c1, by rw [e]; exact hgc, ?_, hc1v⟩
        rw [e, ← hcount]
        exact get?_snoc_last _ _
      · obtain ⟨o, o', ho, ho', hval⟩ := hI.copied j (by omega)
        refine ⟨o, o', ho, ?_, hval⟩
        rw [get?_append_left (by omega)]
        exact ho'
    · rw [get?_set_ne' _ (by omega)]
      exact hI.ahead j (by omega)
  · simp only [hlt, ↓reduceIte, spec_ok]
    have e : k.val = chunk.val - 1 := by scalar_tac
    refine ⟨by rw [hcount, e], ?_⟩
    rw [← e]
    exact hI.copied

/-- What `shrink` does: the arena keeps the slots below `live`. -/
structure ShrinkPost (s : item_space.ItemSpaceCore T) (live : Nat)
    (s' : item_space.ItemSpaceCore T) : Prop where
  geo : GeoN live s'
  cell : ∀ j, j < live → cellAt s' j = cellAt s j
  slots : s'.slots = s.slots
  free : s'.free = s.free
  quarantine : s'.quarantine = s.quarantine

/-- `shrink` keeps the slots below `live` and lets go of the others. -/
theorem shrink_spec (s : item_space.ItemSpaceCore T) (n : Nat) (live : Std.Usize)
    (hg : GeoN n s) (hle : live.val ≤ n) :
    item_space.ItemSpaceCore.shrink s live ⦃ s' => ShrinkPost s live.val s' ⦄ := by
  unfold item_space.ItemSpaceCore.shrink
  simp only [item_space.CHUNK_SIZE]
  have hv : ∀ α : Type, (alloc.vec.Vec.new α).val = [] := by
    intro α
    simp
  by_cases h0 : live = 0#usize
  · have h0' : (live = 0#usize) = True := eq_true h0
    simp only [h0', ↓reduceIte, spec_ok]
    have hz : live.val = 0 := by
      rw [h0]
      rfl
    refine ⟨⟨?_, ?_, fun c w hw => ?_⟩, fun j hj => by omega, rfl, rfl, rfl⟩
    · show (alloc.vec.Vec.new (Option T)).val.length = min live.val 1024
      rw [hv, hz]
      rfl
    · show (alloc.vec.Vec.new (alloc.vec.Vec (Option T))).val.length = (live.val - 1) / 1024
      rw [hv, hz]
      rfl
    · have hw' : (alloc.vec.Vec.new (alloc.vec.Vec (Option T))).val[c]? = some w := hw
      rw [hv] at hw'
      cases hw'
  · simp only [h0, ↓reduceIte]
    have hpos : 0 < live.val := by
      have hne : live.val ≠ 0 := by
        intro e
        apply h0
        apply UScalar.eq_of_val_eq
        rw [e]
        rfl
      omega
    step as ⟨last, hlast⟩
    have hlastv : last.val = live.val - 1 := by scalar_tac
    step as ⟨chunk, hchunk⟩
    have hchunkv : chunk.val = (live.val - 1) / 1024 := by scalar_tac
    step as ⟨at_, hat⟩
    have hatv : at_.val = (live.val - 1) % 1024 := by scalar_tac
    step as ⟨keep, hkeep⟩
    have hkeepv : keep.val = (live.val - 1) % 1024 + 1 := by scalar_tac
    by_cases hc0 : chunk = 0#usize
    · -- the items end in the first chunk
      have hc0' : (chunk = 0#usize) = True := eq_true hc0
      simp only [hc0', ↓reduceIte]
      have hcz : (live.val - 1) / 1024 = 0 := by
        rw [← hchunkv, hc0]
        rfl
      have hkle : keep.val ≤ s.first.val.length := by
        have := hg.first
        omega
      simp only [lift, alloc.vec.Vec.deref_mut]
      step with cut_spec s.first.slice keep hkle as ⟨v, _c, hvv⟩
      have hvv : v.val = s.first.val.take keep.val := hvv
      have hkl : keep.val = live.val := by omega
      have hvl : v.val = s.first.val.take live.val := by rw [hvv, hkl]
      have hfl := hg.first
      refine ⟨⟨?_, ?_, fun c w hw => ?_⟩, fun j hj => ?_, rfl, rfl, rfl⟩
      · show v.val.length = min live.val 1024
        rw [hvl, List.length_take]
        omega
      · show (alloc.vec.Vec.new (alloc.vec.Vec (Option T))).val.length = (live.val - 1) / 1024
        rw [hv, hcz]
        rfl
      · have hw' : (alloc.vec.Vec.new (alloc.vec.Vec (Option T))).val[c]? = some w := hw
        rw [hv] at hw'
        cases hw'
      · have hj0 : j / 1024 = 0 := by omega
        rw [cellAt_first hj0, cellAt_first hj0]
        show v.val[j % 1024]? = _
        rw [hvl]
        exact get?_take_lt _ (by omega)
    · -- the items end in a chunk after the first one
      simp only [hc0, ↓reduceIte]
      have hcnz : ¬ (live.val - 1) / 1024 = 0 := by
        intro e
        apply hc0
        apply UScalar.eq_of_val_eq
        rw [hchunkv, e]
        rfl
      step as ⟨ci, hci⟩
      have hciv : ci.val = (live.val - 1) / 1024 - 1 := by scalar_tac
      have hcic : ci.val = chunk.val - 1 := by omega
      have hgr := hg.rest
      have hfl := hg.first
      have hin : ci < alloc.vec.Vec.len s.rest := by scalar_tac
      simp only [hin, ↓reduceIte]
      -- the chunks after the last one are let go
      simp only [lift, alloc.vec.Vec.deref_mut]
      step with let_go_spec s.rest.slice chunk as ⟨s1, hs1len, hs1⟩
      have hs1len : s1.val.length = s.rest.val.length := hs1len
      have hs1 : ∀ j, j < chunk.val → s1.val[j]? = s.rest.val[j]? := hs1
      have hcil : ci.val < s1.val.length := by
        rw [hs1len]
        omega
      -- the last chunk is cut
      step as ⟨tail, back, htail, hback⟩
      · exact hcil
      have hgt : s.rest.val[chunk.val - 1]? = some tail := by
        rw [← hs1 (chunk.val - 1) (by omega), ← hcic]
        exact get?_of_getElem hcil htail
      have htl := hg.chunk _ tail hgt
      have hkle : keep.val ≤ tail.slice.val.length := by
        show keep.val ≤ tail.val.length
        omega
      step with cut_spec tail.slice keep hkle as ⟨t1, _c, ht1⟩
      have ht1 : t1.val = tail.val.take keep.val := ht1
      -- the first chunk gets a vector of its own
      have h1024 : (1024#usize : Std.Usize).val = 1024 := by scalar_tac
      have hfirst : (1024#usize : Std.Usize).val ≤ s.first.slice.val.length := by
        rw [h1024]
        show 1024 ≤ s.first.val.length
        omega
      step with cut_spec s.first.slice 1024#usize hfirst as ⟨f1, _c2, hf1⟩
      have hf1 : f1.val = s.first.val := by
        have h : f1.val = s.first.val.take (1024#usize : Std.Usize).val := hf1
        rw [h, h1024]
        exact List.take_of_length_le (by omega)
      -- and so does every chunk between the two
      have hbv : (back (alloc.vec.Vec.new (Option T))).val =
          s1.val.set ci.val (alloc.vec.Vec.new (Option T)) := by
        rw [hback]
        simp
        rfl
      have hv0len : (back (alloc.vec.Vec.new (Option T))).val.length = s.rest.val.length := by
        rw [hbv, List.length_set, hs1len]
      have hv0get : ∀ j, j < chunk.val - 1 →
          (back (alloc.vec.Vec.new (Option T))).val[j]? = s.rest.val[j]? := by
        intro j hj
        rw [hbv, get?_set_ne' _ (by omega)]
        exact hs1 j (by omega)
      have hfullc : ∀ j c, j < chunk.val - 1 →
          (back (alloc.vec.Vec.new (Option T))).val[j]? = some c → c.val.length = 1024 := by
        intro j c hj hc
        rw [hv0get j hj] at hc
        have := hg.chunk j c hc
        omega
      have hinit : Shrinking (back (alloc.vec.Vec.new (Option T))).val
          (back (alloc.vec.Vec.new (Option T))).val
          (alloc.vec.Vec.with_capacity (alloc.vec.Vec (Option T)) chunk).val
          (0#usize : Std.Usize).val (chunk.val - 1) := by
        rw [usize_zero_val]
        refine ⟨Nat.zero_le _, rfl, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ => rfl⟩
        simp [alloc.vec.Vec.with_capacity]
      step with shrink_loop_spec (back (alloc.vec.Vec.new (Option T))).val
        (back (alloc.vec.Vec.new (Option T))) chunk _ 0#usize (by omega) (by omega) hfullc hinit
        as ⟨rest1, hrl, hcopied⟩
      have hrmax : rest1.val.length < Std.Usize.max := by
        rw [hrl]
        scalar_tac
      step as ⟨rest2, hrest2⟩
      have ht1l : t1.val.length = keep.val := by
        rw [ht1, List.length_take]
        omega
      refine ⟨⟨?_, ?_, fun c u hu => ?_⟩, fun j hj => ?_, rfl, rfl, rfl⟩
      · show f1.val.length = min live.val 1024
        rw [hf1]
        omega
      · show rest2.val.length = (live.val - 1) / 1024
        rw [hrest2, List.length_append, List.length_singleton, hrl]
        omega
      · have hu' : (rest1.val ++ [t1])[c]? = some u := by
          rw [← hrest2]
          exact hu
        rcases get?_snoc_cases hu' with ⟨hcl, hold⟩ | ⟨hcl, hnew⟩
        · rw [hrl] at hcl
          obtain ⟨o, o', ho, ho', hval⟩ := hcopied c hcl
          have e : o' = u := Option.some.inj (ho'.symm.trans hold)
          rw [hv0get c hcl] at ho
          have hfull := hg.chunk c o ho
          have h1 : 1024 * (c + 2) ≤ live.val := by omega
          rw [← e, hval]
          exact chunk_full_of (by omega) h1 hfull
        · rw [hnew, ht1l, hcl, hrl]
          omega
      · by_cases hj0 : j / 1024 = 0
        · rw [cellAt_first hj0, cellAt_first hj0]
          show f1.val[j % 1024]? = s.first.val[j % 1024]?
          rw [hf1]
        · by_cases hjc : j / 1024 - 1 < chunk.val - 1
          · obtain ⟨o, o', ho, ho', hval⟩ := hcopied (j / 1024 - 1) hjc
            rw [hv0get _ hjc] at ho
            have hu2 : rest2.val[j / 1024 - 1]? = some o' := by
              rw [hrest2, get?_append_left (by omega)]
              exact ho'
            rw [cellAt_rest (s := { s with first := f1, rest := rest2 }) hj0 hu2,
              cellAt_rest hj0 ho, hval]
          · have hje : j / 1024 - 1 = chunk.val - 1 := by omega
            have hu2 : rest2.val[j / 1024 - 1]? = some t1 := by
              rw [hrest2, hje, ← hrl]
              exact get?_snoc_last _ _
            have hu : s.rest.val[j / 1024 - 1]? = some tail := by rw [hje, hgt]
            rw [cellAt_rest (s := { s with first := f1, rest := rest2 }) hj0 hu2,
              cellAt_rest hj0 hu, ht1]
            exact get?_take_lt _ (by omega)

/-! ## `finish` -/

/-- What `finish` does when it moves the items: `moved` is the table it
answers, read as `ClientBlocksCore::remap_slots` reads it (`movedTo`). -/
structure FinishMoved (s : item_space.ItemSpaceCore T) (moved : List Std.U32)
    (s' : item_space.ItemSpaceCore T) : Prop where
  wf : WF s'
  /-- an entry for every old slot -/
  length : moved.length = s.slots.val
  /-- no empty slot is left -/
  free : s'.free.val = [] ∧ s'.quarantine.val = []
  /-- as many slots as there were items -/
  slots : s'.slots.val = liveCount s
  /-- an empty slot went nowhere -/
  dead : ∀ j, j < s.slots.val → item s j = none → ClientBlocks.movedTo moved j = none
  /-- an item is read at the slot the table names for its old one -/
  kept : ∀ j x, item s j = some x →
    ∃ r, ClientBlocks.movedTo moved j = some r ∧ r < s'.slots.val ∧ item s' r = some x
  /-- every new slot is the slot of an item that was there -/
  onto : ∀ r, r < s'.slots.val → ∃ j, j < s.slots.val ∧ ClientBlocks.movedTo moved j = some r
  /-- the items keep their order -/
  mono : ∀ j1 j2 r1 r2, j1 < j2 → ClientBlocks.movedTo moved j1 = some r1 →
    ClientBlocks.movedTo moved j2 = some r2 → r1 < r2
  /-- every slot holds an item -/
  full : ∀ r, r < s'.slots.val → ∃ x, item s' r = some x

theorem movedTo_zero {moved : List Std.U32} {j : Nat} {m : Std.U32} (h : moved[j]? = some m)
    (hz : m.val = 0) : ClientBlocks.movedTo moved j = none := by
  simp [ClientBlocks.movedTo, h, hz]

theorem movedTo_pos {moved : List Std.U32} {j : Nat} {m : Std.U32} (h : moved[j]? = some m)
    (hp : 0 < m.val) : ClientBlocks.movedTo moved j = some (m.val - 1) := by
  have hne : ¬ m.val = 0 := by omega
  simp [ClientBlocks.movedTo, h, hne]

theorem movedTo_inv {moved : List Std.U32} {j r : Nat} (h : ClientBlocks.movedTo moved j = some r) :
    ∃ m : Std.U32, moved[j]? = some m ∧ m.val = r + 1 := by
  cases hm : moved[j]? with
  | none =>
    simp [ClientBlocks.movedTo, hm] at h
  | some m =>
    by_cases hz : m.val = 0
    · rw [movedTo_zero hm hz] at h
      cases h
    · rw [movedTo_pos hm (by omega)] at h
      have e : m.val - 1 = r := Option.some.inj h
      exact ⟨m, rfl, by omega⟩

/-- The arena after `compact`, `shrink` and the reset of its lists. -/
theorem finishMoved_of {s s1 s2 : item_space.ItemSpaceCore T} {moved : List Std.U32} {live : Nat}
    (hn : s.slots.val ≤ 4294967295) (hg : GeoN s.slots.val s)
    (hC : Compacting s s.slots.val s1 moved live s.slots.val)
    (hg2 : GeoN live s2) (hc2 : ∀ j, j < live → cellAt s2 j = cellAt s1 j) (s' : item_space.ItemSpaceCore T)
    (hf : s'.first = s2.first) (hr : s'.rest = s2.rest) (hs : s'.slots.val = live)
    (hfree : s'.free.val = []) (hq : s'.quarantine.val = []) : FinishMoved s moved s' := by
  have hb := hC.bounds
  have hcell : ∀ j, j < live → cellAt s' j = cellAt s1 j := by
    intro j hj
    rw [cellAt_congr hf hr, hc2 j hj]
  have hg' : GeoN live s' := hg2.of_shape (by rw [hf]) (by rw [hr])
  -- an item of the old arena, at its new slot
  have hkept : ∀ j x, item s j = some x →
      ∃ m : Std.U32, moved[j]? = some m ∧ 0 < m.val ∧ m.val ≤ live ∧
        cellAt s' (m.val - 1) = some (some x) := by
    intro j x hx
    have hjn : j < s.slots.val := (GeoN.cell_iff hg).mp ⟨some x, cell_of_item hx⟩
    obtain ⟨m, hm, hpos, hc⟩ := hC.kept j x hjn hx
    have hle := hC.le j m hjn hm
    exact ⟨m, hm, hpos, hle, by rw [hcell _ (by omega)]; exact hc⟩
  -- every new slot holds an item of the old arena
  have hfull : ∀ r, r < live → ∃ j x, j < s.slots.val ∧ item s j = some x ∧
      ∃ m : Std.U32, moved[j]? = some m ∧ m.val = r + 1 ∧ cellAt s' r = some (some x) := by
    intro r hr'
    obtain ⟨j, m, hj, hm, hv⟩ := hC.onto r hr'
    cases hi : item s j with
    | none =>
      obtain ⟨m0, hm0, hz⟩ := hC.dead j hj hi
      rw [hm] at hm0
      have e : m = m0 := Option.some.inj hm0
      rw [e] at hv
      omega
    | some x =>
      obtain ⟨m', hm', _, _, hc⟩ := hkept j x hi
      rw [hm] at hm'
      have e : m = m' := Option.some.inj hm'
      rw [← e] at hc
      have e2 : m.val - 1 = r := by omega
      rw [e2] at hc
      exact ⟨j, x, hj, hi, m, hm, hv, hc⟩
  refine ⟨⟨?_, ?_, ?_, fun i => ?_⟩, hC.length, ⟨hfree, hq⟩, ?_, fun j hj hd => ?_,
    fun j x hx => ?_, fun r hr' => ?_, fun j1 j2 r1 r2 h12 e1 e2 => ?_, fun r hr' => ?_⟩
  · show GeoN s'.slots.val s'
    rw [hs]
    exact hg'
  · rw [hs]
    omega
  · rw [hfree, hq]
    exact List.nodup_nil
  · rw [hfree, hq]
    constructor
    · intro hm
      cases hm
    · intro hc
      exfalso
      by_cases hlt : i.val < live
      · obtain ⟨_, x, _, _, _, _, _, hx⟩ := hfull i.val hlt
        rw [hx] at hc
        cases hc
      · rw [hg'.cell_ge (by omega)] at hc
        cases hc
  · rw [hs]
    exact hC.count
  · obtain ⟨m, hm, hz⟩ := hC.dead j hj hd
    exact movedTo_zero hm hz
  · obtain ⟨m, hm, hpos, hle, hc⟩ := hkept j x hx
    exact ⟨m.val - 1, movedTo_pos hm hpos, by rw [hs]; omega, item_some hc⟩
  · rw [hs] at hr'
    obtain ⟨j, _, hj, _, m, hm, hv, _⟩ := hfull r hr'
    refine ⟨j, hj, ?_⟩
    rw [movedTo_pos hm (by omega)]
    have e : m.val - 1 = r := by omega
    rw [e]
  · obtain ⟨m1, hm1, hv1⟩ := movedTo_inv e1
    obtain ⟨m2, hm2, hv2⟩ := movedTo_inv e2
    have hj2 : j2 < s.slots.val := by
      have := get?_lt hm2
      rw [hC.length] at this
      exact this
    have := hC.mono j1 j2 m1 m2 h12 hj2 hm1 hm2 (by omega) (by omega)
    omega
  · rw [hs] at hr'
    obtain ⟨_, x, _, _, _, _, _, hx⟩ := hfull r hr'
    exact ⟨x, item_some hx⟩

/-- A move of the arena after `release` is a move of the arena before it:
the two have the same slots. -/
theorem FinishMoved.of_released {s s1 s' : item_space.ItemSpaceCore T} {moved : List Std.U32}
    (hM : FinishMoved s1 moved s') (hR : ReleasePost s s1) : FinishMoved s moved s' := by
  have hi : ∀ j, item s1 j = item s j := fun j => item_congr (cellAt_congr hR.first hR.rest j)
  have hs1 := hR.slots
  have hlc : liveCount s1 = liveCount s := by
    unfold liveCount
    rw [hs1]
    have hfun : item s1 = item s := funext hi
    rw [hfun]
  refine ⟨hM.wf, by rw [hM.length, hs1], hM.free, by rw [hM.slots, hlc],
    fun j hj hd => hM.dead j (by rw [hs1]; exact hj) (by rw [hi]; exact hd),
    fun j x hx => hM.kept j x (by rw [hi]; exact hx), fun r hr => ?_, hM.mono, hM.full⟩
  obtain ⟨j, hj, hm⟩ := hM.onto r hr
  exact ⟨j, by rw [← hs1]; exact hj, hm⟩

/-- What `finish` does, by its answer. -/
structure FinishPost (s : item_space.ItemSpaceCore T) (r : Option (alloc.vec.Vec Std.U32))
    (s' : item_space.ItemSpaceCore T) : Prop where
  /-- it moves the items when some slot is empty and all of them are, or
  more than two fifths of at least `256` (`Sparse`), the slots emptied since
  the last `finish` counted -/
  decides : (∃ m, r = some m) ↔
    Sparse (s.free.val.length + s.quarantine.val.length) s.slots.val
  /-- no move: every slot is as it was, and the slots in quarantine may be
  filled again, after the ones that were free -/
  kept : r = none → WF s' ∧ ReleasePost s s'
  /-- a move: the table says where every item went -/
  moved : ∀ m, r = some m → FinishMoved s m.val s'

/-- **`finish` ends a transaction and keeps the invariant.** Without a move
every item stays in its slot and the slots emptied since the last `finish`
may be filled again. With a move the items are in the slots `0 .. live`, in
their order, no slot is empty, and the table answers the new slot of every
item (`FinishMoved`). -/
theorem finish_spec (s : item_space.ItemSpaceCore T) (h : WF s) :
    item_space.ItemSpaceCore.finish s ⦃ r s' => FinishPost s r s' ⦄ := by
  unfold item_space.ItemSpaceCore.finish
  step with release_spec s h as ⟨s1, hrel⟩
  have hR : ReleasePost s s1 := hrel
  have hw1 : WF s1 := h.released hR
  have hle1 := hw1.empties_le
  have hlen : s1.free.val.length = s.free.val.length + s.quarantine.val.length := by
    rw [hR.free, List.length_append]
  step with sparse_spec s1 (by omega) hw1.bound as ⟨b, hb⟩
  have hb' : b = true ↔ Sparse (s.free.val.length + s.quarantine.val.length) s.slots.val := by
    rw [← hlen, ← hR.slots]
    exact hb
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
    refine ⟨?_, fun _ => ⟨hw1, hR⟩, fun m hm => (nomatch hm)⟩
    constructor
    · rintro ⟨m, hm⟩
      cases hm
    · intro hd
      have := hb'.mpr hd
      cases this
  | true =>
    simp only [↓reduceIte]
    have hg1 : GeoN s1.slots.val s1 := hw1.geo
    step with compact_spec s1 hg1 hw1.bound as ⟨moved, live, s2, hC⟩
    have hC' : Compacting s1 s1.slots.val s2 moved.val live.val s1.slots.val := hC
    step with shrink_spec s2 s1.slots.val live hC'.geo hC'.bounds.1 as ⟨s3, hshr⟩
    have hS : ShrinkPost s2 live.val s3 := hshr
    have hv : (alloc.vec.Vec.new Std.U32).val = [] := by simp
    refine ⟨⟨fun _ => hb'.mp rfl, fun _ => ⟨moved, rfl⟩⟩, fun hn => (nomatch hn), fun m hm => ?_⟩
    cases hm
    refine FinishMoved.of_released (s1 := s1) ?_ hR
    exact finishMoved_of hw1.bound hg1 hC' hS.geo hS.cell _ rfl rfl rfl hv hv

/-- **The table of `finish` is one `remap_slots` accepts**: for a timeline
whose item blocks name slots that held an item, it names a new slot for every
item block (`ClientBlocks.SlotsMoved`, what `remap_slots_spec` asks for). -/
theorem finish_slots_moved {s s' : item_space.ItemSpaceCore T} {moved : List Std.U32}
    (hm : FinishMoved s moved s') (blocks : List client_blocks.BlockRefCore)
    (hlive : ∀ (p : Nat) (b : client_blocks.BlockRefCore) (sl : Std.U32), blocks[p]? = some b →
      ClientBlocks.kindSlot b.kind = some sl → ∃ x, item s sl.val = some x) :
    ClientBlocks.SlotsMoved blocks moved := by
  intro p b sl hp hk
  obtain ⟨x, hx⟩ := hlive p b sl hp hk
  obtain ⟨r, hr, _⟩ := hm.kept _ x hx
  exact ⟨r, hr⟩

/-! ## Two slots at once -/

theorem get?_drop' {α : Type} (l : List α) (n k : Nat) : (l.drop n)[k]? = l[n + k]? := by
  simp

/-- Two slots of a list, written through the two halves it was cut into. -/
theorem split_set2 {α : Type} (l : List α) {low high : Nat} (hlh : low < high)
    (hh : high < l.length) (x y : α) :
    (l.take high).set low x ++ (l.drop high).set 0 y = (l.set low x).set high y := by
  have hlen : ((l.take high).set low x).length = high := by
    rw [List.length_set, List.length_take]
    omega
  apply ext_get?
  intro j
  by_cases hj : j < high
  · rw [get?_append_left (by rw [hlen]; exact hj), get?_set_ne' y (by omega)]
    by_cases e : j = low
    · rw [e, get?_set_self' x (by rw [List.length_take]; omega), get?_set_self' x (by omega)]
    · rw [get?_set_ne' x e, get?_set_ne' x e, get?_take_lt l hj]
  · obtain ⟨k, rfl⟩ : ∃ k, j = high + k := ⟨j - high, by omega⟩
    have happ := get?_append_right ((l.take high).set low x) ((l.drop high).set 0 y) k
    rw [hlen] at happ
    rw [happ]
    by_cases ek : k = 0
    · rw [ek, get?_set_self' y (by rw [List.length_drop]; omega), Nat.add_zero,
        get?_set_self' y (by rw [List.length_set]; exact hh)]
    · rw [get?_set_ne' y ek, get?_set_ne' y (by omega), get?_set_ne' x (by omega), get?_drop']

/-- What `pair` answers. -/
structure PairPost (x y : Option T) (rev : Bool) (o : Option (T × T))
    (back : Option (T × T) → Option T × Option T) : Prop where
  /-- one of the two slots is empty: no borrow, and both stay as they are -/
  absent : (x = none ∨ y = none) → o = none ∧ ∀ r, back r = (x, y)
  /-- both hold an item: the two items in the order asked, and what is
  written through the two borrows goes back to the slot it came from -/
  both : ∀ a b, x = some a → y = some b →
    o = some (cond rev (b, a) (a, b)) ∧ back none = (x, y) ∧
      ∀ p q, back (some (p, q)) = cond rev (some q, some p) (some p, some q)

theorem pair_spec (x y : Option T) (rev : Bool) :
    item_space.pair x y rev ⦃ o back => PairPost x y rev o back ⦄ := by
  unfold item_space.pair
  cases x with
  | none =>
    simp only [spec_ok, uncurry'_pair]
    exact ⟨fun _ => ⟨rfl, fun _ => rfl⟩, fun a b ha _ => (nomatch ha)⟩
  | some a =>
    cases y with
    | none =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨fun _ => ⟨rfl, fun _ => rfl⟩, fun a' b' _ hb => (nomatch hb)⟩
    | some b =>
      cases rev with
      | true =>
        simp only [↓reduceIte, spec_ok, uncurry'_pair]
        refine ⟨fun h => ?_, fun a' b' ha hb => ?_⟩
        · rcases h with h | h <;> cases h
        · cases ha
          cases hb
          exact ⟨rfl, rfl, fun p q => rfl⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
        refine ⟨fun h => ?_, fun a' b' ha hb => ?_⟩
        · rcases h with h | h <;> cases h
        · cases ha
          cases hb
          exact ⟨rfl, rfl, fun p q => rfl⟩

/-- The items of two slots, the second one first when `rev`; `none` unless
both hold one. -/
def twoOf (x y : Option (Option T)) (rev : Bool) : Option (T × T) :=
  match x, y with
  | some (some a), some (some b) => some (cond rev (b, a) (a, b))
  | _, _ => none

theorem twoOf_some {x y : Option (Option T)} {rev : Bool} {r : T × T}
    (h : twoOf x y rev = some r) :
    ∃ a b, x = some (some a) ∧ y = some (some b) ∧ r = cond rev (b, a) (a, b) := by
  cases x with
  | none => cases h
  | some x' =>
    cases x' with
    | none => cases h
    | some a =>
      cases y with
      | none => cases h
      | some y' =>
        cases y' with
        | none => cases h
        | some b => exact ⟨a, b, rfl, rfl, (Option.some.inj h).symm⟩

/-- What `pair_of` answers on the slots `low` and `high` of a chunk. -/
structure PairOfPost (l : List (Option T)) (low high : Nat) (rev : Bool) (o : Option (T × T))
    (back : Option (T × T) → Slice (Option T)) : Prop where
  /-- the items of the two slots when `low` is the lower one -/
  answer : o = if low < high then twoOf l[low]? l[high]? rev else none
  /-- nothing written: the chunk as it was -/
  same : (back none).val = l
  /-- no two items: the chunk as it was -/
  absent : o = none → ∀ r, (back r).val = l
  /-- a write goes to the two slots, each item to the slot it was read from -/
  write : ∀ p q, o ≠ none → (back (some (p, q))).val =
    cond rev ((l.set low (some q)).set high (some p)) ((l.set low (some p)).set high (some q))

theorem twoOf_right_none (x : Option (Option T)) (rev : Bool) : twoOf x none rev = none := by
  cases x with
  | none => rfl
  | some c => cases c <;> rfl

theorem pair_of_spec (cells : Slice (Option T)) (low high : Std.Usize) (rev : Bool) :
    item_space.pair_of cells low high rev ⦃ o back =>
      PairOfPost cells.val low.val high.val rev o back ⦄ := by
  unfold item_space.pair_of
  by_cases hlt : low < high
  · simp only [hlt, ↓reduceIte]
    have hlh : low.val < high.val := by scalar_tac
    by_cases hin : high < Slice.len cells
    · simp only [hin, ↓reduceIte]
      have hhl : high.val < cells.val.length := by scalar_tac
      refine spec_bind (core.slice.Slice.split_at_mut.spec cells high (by scalar_tac))
        (fun p hp => ?_)
      obtain ⟨⟨before, after⟩, sback⟩ := p
      rw [uncurry'_pair] at hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := hp
      have h1' : before.val.length = high.val := h1
      have h2' : after.val.length = cells.val.length - high.val := h2
      have h3' : before.val = cells.val.take high.val := h3
      have h4' : after.val = cells.val.drop high.val := h4
      have hb1 : low.val < before.val.length := by omega
      have hb2 : (0#usize : Std.Usize).val < after.val.length := by
        rw [usize_zero_val]
        omega
      step as ⟨x, bx, hx, hbx⟩
      step as ⟨y, by_, hy, hby⟩
      step with pair_spec x y rev as ⟨o, pback, hpair⟩
      have hP : PairPost x y rev o pback := hpair
      have hgx : cells.val[low.val]? = some x := by
        have h := get?_of_getElem hb1 hx
        rw [h3', get?_take_lt _ hlh] at h
        exact h
      have hgy : cells.val[high.val]? = some y := by
        have h := get?_of_getElem hb2 hy
        rw [usize_zero_val, h4', get?_drop_zero] at h
        exact h
      have hsame : (cells.val.set low.val x).set high.val y = cells.val := by
        rw [set_eq_self hgx, set_eq_self hgy]
      have hback : ∀ u v : Option T,
          (sback (bx u, by_ v)).val = (cells.val.set low.val u).set high.val v := by
        intro u v
        have hbu : (bx u).val = before.val.set low.val u := by
          rw [hbx]
          simp
        have hbv : (by_ v).val = after.val.set 0 v := by
          rw [hby]
          simp
        have h := (h5 (bx u) (by_ v)
          (by show (bx u).val.length = high.val; rw [hbu, List.length_set]; exact h1')
          (by
            show (by_ v).val.length = cells.val.length - high.val
            rw [hbv, List.length_set]
            exact h2')).1
        rw [h, hbu, hbv, h3', h4']
        exact split_set2 cells.val hlh hhl u v
      show PairOfPost cells.val low.val high.val rev o
        (fun r => sback (bx (pback r).1, by_ (pback r).2))
      by_cases hboth : ∃ a b, x = some a ∧ y = some b
      · obtain ⟨a, b, ha, hb⟩ := hboth
        obtain ⟨ho, hbn, hbw⟩ := hP.both a b ha hb
        refine ⟨?_, ?_, fun hn => ?_, fun p q _ => ?_⟩
        · rw [ho, ite_eq_left hlh, hgx, hgy, ha, hb]
          rfl
        · show (sback (bx (pback none).1, by_ (pback none).2)).val = cells.val
          rw [hback, hbn]
          exact hsame
        · rw [ho] at hn
          cases hn
        · show (sback (bx (pback (some (p, q))).1, by_ (pback (some (p, q))).2)).val = _
          rw [hback, hbw p q]
          cases rev <;> rfl
      · have hxy : x = none ∨ y = none := by
          cases x with
          | none => exact Or.inl rfl
          | some a =>
            cases y with
            | none => exact Or.inr rfl
            | some b => exact absurd ⟨a, b, rfl, rfl⟩ hboth
        obtain ⟨ho, hb⟩ := hP.absent hxy
        have hbv : ∀ r, (sback (bx (pback r).1, by_ (pback r).2)).val = cells.val := by
          intro r
          rw [hback, hb r]
          exact hsame
        refine ⟨?_, hbv none, fun _ r => hbv r, fun p q hne => absurd ho hne⟩
        rw [ho, ite_eq_left hlh, hgx, hgy]
        rcases hxy with e | e
        · rw [e]
          rfl
        · rw [e]
          cases x <;> rfl
    · simp only [hin, ↓reduceIte, spec_ok, uncurry'_pair]
      have hl : cells.val.length ≤ high.val := by scalar_tac
      refine ⟨?_, rfl, fun _ _ => rfl, fun p q hne => absurd rfl hne⟩
      rw [ite_eq_left hlh, get?_none hl, twoOf_right_none]
  · simp only [hlt, ↓reduceIte, spec_ok, uncurry'_pair]
    have hnl : ¬ low.val < high.val := by scalar_tac
    refine ⟨?_, rfl, fun _ _ => rfl, fun p q hne => absurd rfl hne⟩
    rw [ite_eq_right hnl]

theorem twoOf_swap (x y : Option (Option T)) : twoOf x y true = twoOf y x false := by
  rcases x with _ | (_ | a) <;> rcases y with _ | (_ | b) <;> rfl

theorem get?_set2 {α : Type} (l : List α) {i1 i2 : Nat} (u v : α) (h1 : i1 < l.length)
    (h2 : i2 < l.length) (k : Nat) :
    ((l.set i1 u).set i2 v)[k]? = if k = i2 then some v else if k = i1 then some u else l[k]? := by
  by_cases e2 : k = i2
  · rw [ite_eq_left e2, e2]
    exact get?_set_self' v (by rw [List.length_set]; exact h2)
  · rw [ite_eq_right e2, get?_set_ne' v e2]
    by_cases e1 : k = i1
    · rw [ite_eq_left e1, e1]
      exact get?_set_self' u h1
    · rw [ite_eq_right e1, get?_set_ne' u e1]

/-- `s'` is `s` with `u` in the slot `n1` and `v` in the slot `n2`: no other
slot is touched, no chunk changes its length, and the other fields are the
same. -/
structure Upd2 (s : item_space.ItemSpaceCore T) (n1 n2 : Nat) (u v : Option T)
    (s' : item_space.ItemSpaceCore T) : Prop where
  slots : s'.slots = s.slots
  free : s'.free = s.free
  quarantine : s'.quarantine = s.quarantine
  first : s'.first.val.length = s.first.val.length
  rest : s'.rest.val.map (fun c => c.val.length) = s.rest.val.map (fun c => c.val.length)
  cell : ∀ j, cellAt s' j = if j = n2 then some v else if j = n1 then some u else cellAt s j

theorem Upd2.swap {s s' : item_space.ItemSpaceCore T} {n1 n2 : Nat} {u v : Option T}
    (h : Upd2 s n1 n2 u v s') (hne : n1 ≠ n2) : Upd2 s n2 n1 v u s' := by
  refine ⟨h.slots, h.free, h.quarantine, h.first, h.rest, fun j => ?_⟩
  rw [h.cell j]
  by_cases e1 : j = n1
  · rw [ite_eq_left e1, ite_eq_right (by omega : ¬ j = n2), ite_eq_left e1]
  · rw [ite_eq_right e1, ite_eq_right e1]

theorem Upd2.geo {n : Nat} {s s' : item_space.ItemSpaceCore T} {n1 n2 : Nat} {u v : Option T}
    (h : Upd2 s n1 n2 u v s') (g : GeoN n s) : GeoN n s' :=
  g.of_shape h.first h.rest

/-- Two slots of the first chunk. -/
theorem upd2_first {s s' : item_space.ItemSpaceCore T} {o1 o2 : Nat} {u v : Option T}
    (hs : s'.slots = s.slots) (hfr : s'.free = s.free) (hq : s'.quarantine = s.quarantine)
    (hr : s'.rest = s.rest) (hf : s'.first.val = (s.first.val.set o1 u).set o2 v)
    (h1 : o1 < s.first.val.length) (h2 : o2 < s.first.val.length) (hk1 : o1 < 1024)
    (hk2 : o2 < 1024) : Upd2 s o1 o2 u v s' := by
  refine ⟨hs, hfr, hq, by rw [hf, List.length_set, List.length_set], by rw [hr], fun j => ?_⟩
  by_cases hj : j / 1024 = 0
  · rw [cellAt_first hj, hf, get?_set2 _ u v h1 h2]
    by_cases e2 : j = o2
    · rw [ite_eq_left e2, ite_eq_left (by omega : j % 1024 = o2)]
    · rw [ite_eq_right e2, ite_eq_right (by omega : ¬ j % 1024 = o2)]
      by_cases e1 : j = o1
      · rw [ite_eq_left e1, ite_eq_left (by omega : j % 1024 = o1)]
      · rw [ite_eq_right e1, ite_eq_right (by omega : ¬ j % 1024 = o1), cellAt_first hj]
  · rw [ite_eq_right (by omega : ¬ j = o2), ite_eq_right (by omega : ¬ j = o1)]
    exact cellAt_congr_rest hj hr

/-- Two slots of one chunk after the first one. -/
theorem upd2_chunk {s s' : item_space.ItemSpaceCore T} {c o1 o2 : Nat}
    {w w' : alloc.vec.Vec (Option T)} {u v : Option T}
    (hs : s'.slots = s.slots) (hfr : s'.free = s.free) (hq : s'.quarantine = s.quarantine)
    (hf : s'.first = s.first) (hw : s.rest.val[c]? = some w)
    (hr : s'.rest.val = s.rest.val.set c w') (hw' : w'.val = (w.val.set o1 u).set o2 v)
    (h1 : o1 < w.val.length) (h2 : o2 < w.val.length) (hk1 : o1 < 1024) (hk2 : o2 < 1024) :
    Upd2 s (1024 * (c + 1) + o1) (1024 * (c + 1) + o2) u v s' := by
  refine ⟨hs, hfr, hq, by rw [hf], ?_, fun j => ?_⟩
  · rw [hr]
    exact map_length_set hw (by rw [hw', List.length_set, List.length_set])
  · by_cases hj : j / 1024 = 0
    · rw [ite_eq_right (by omega : ¬ j = 1024 * (c + 1) + o2),
        ite_eq_right (by omega : ¬ j = 1024 * (c + 1) + o1)]
      exact cellAt_congr_first hj hf
    · by_cases hc : j / 1024 - 1 = c
      · have hg' : s'.rest.val[j / 1024 - 1]? = some w' := by
          rw [hr, hc]
          exact get?_set_self' w' (get?_lt hw)
        have hg : s.rest.val[j / 1024 - 1]? = some w := by rw [hc, hw]
        rw [cellAt_rest hj hg', hw', get?_set2 _ u v h1 h2]
        by_cases e2 : j = 1024 * (c + 1) + o2
        · rw [ite_eq_left e2, ite_eq_left (by omega : j % 1024 = o2)]
        · rw [ite_eq_right e2, ite_eq_right (by omega : ¬ j % 1024 = o2)]
          by_cases e1 : j = 1024 * (c + 1) + o1
          · rw [ite_eq_left e1, ite_eq_left (by omega : j % 1024 = o1)]
          · rw [ite_eq_right e1, ite_eq_right (by omega : ¬ j % 1024 = o1), cellAt_rest hj hg]
      · rw [ite_eq_right (by omega : ¬ j = 1024 * (c + 1) + o2),
          ite_eq_right (by omega : ¬ j = 1024 * (c + 1) + o1)]
        unfold cellAt
        rw [ite_eq_right hj, ite_eq_right hj, hr, get?_set_ne' _ hc]

/-- A slot of the first chunk and a slot of a chunk after it. -/
theorem upd2_first_chunk {s s' : item_space.ItemSpaceCore T} {c o1 o2 : Nat}
    {w w' : alloc.vec.Vec (Option T)} {u v : Option T}
    (hs : s'.slots = s.slots) (hfr : s'.free = s.free) (hq : s'.quarantine = s.quarantine)
    (hf : s'.first.val = s.first.val.set o1 u) (hw : s.rest.val[c]? = some w)
    (hr : s'.rest.val = s.rest.val.set c w') (hw' : w'.val = w.val.set o2 v)
    (h1 : o1 < s.first.val.length) (h2 : o2 < w.val.length) (hk1 : o1 < 1024) (hk2 : o2 < 1024) :
    Upd2 s o1 (1024 * (c + 1) + o2) u v s' := by
  refine ⟨hs, hfr, hq, by rw [hf, List.length_set], ?_, fun j => ?_⟩
  · rw [hr]
    exact map_length_set hw (by rw [hw', List.length_set])
  · by_cases hj : j / 1024 = 0
    · rw [ite_eq_right (by omega : ¬ j = 1024 * (c + 1) + o2), cellAt_first hj, hf]
      by_cases e1 : j = o1
      · rw [ite_eq_left e1, e1]
        have e : o1 % 1024 = o1 := by omega
        rw [e]
        exact get?_set_self' u h1
      · rw [ite_eq_right e1, get?_set_ne' u (by omega : j % 1024 ≠ o1), cellAt_first hj]
    · rw [ite_eq_right (by omega : ¬ j = o1)]
      by_cases hc : j / 1024 - 1 = c
      · have hg' : s'.rest.val[j / 1024 - 1]? = some w' := by
          rw [hr, hc]
          exact get?_set_self' w' (get?_lt hw)
        have hg : s.rest.val[j / 1024 - 1]? = some w := by rw [hc, hw]
        rw [cellAt_rest hj hg', hw']
        by_cases e2 : j = 1024 * (c + 1) + o2
        · rw [ite_eq_left e2]
          have e : j % 1024 = o2 := by omega
          rw [e]
          exact get?_set_self' v h2
        · rw [ite_eq_right e2, get?_set_ne' v (by omega : j % 1024 ≠ o2), cellAt_rest hj hg]
      · rw [ite_eq_right (by omega : ¬ j = 1024 * (c + 1) + o2)]
        unfold cellAt
        rw [ite_eq_right hj, ite_eq_right hj, hr, get?_set_ne' _ hc]

/-- A slot of a chunk after the first one and a slot of a later chunk. -/
theorem upd2_chunks {s s' : item_space.ItemSpaceCore T} {c1 c2 o1 o2 : Nat}
    {w1 w2 w1' w2' : alloc.vec.Vec (Option T)} {u v : Option T}
    (hs : s'.slots = s.slots) (hfr : s'.free = s.free) (hq : s'.quarantine = s.quarantine)
    (hf : s'.first = s.first) (hc : c1 ≠ c2) (hw1 : s.rest.val[c1]? = some w1)
    (hw2 : s.rest.val[c2]? = some w2) (hr : s'.rest.val = (s.rest.val.set c1 w1').set c2 w2')
    (hw1' : w1'.val = w1.val.set o1 u) (hw2' : w2'.val = w2.val.set o2 v)
    (h1 : o1 < w1.val.length) (h2 : o2 < w2.val.length) (hk1 : o1 < 1024) (hk2 : o2 < 1024) :
    Upd2 s (1024 * (c1 + 1) + o1) (1024 * (c2 + 1) + o2) u v s' := by
  have hmid : (s.rest.val.set c1 w1')[c2]? = some w2 := by
    rw [get?_set_ne' w1' (Ne.symm hc)]
    exact hw2
  refine ⟨hs, hfr, hq, by rw [hf], ?_, fun j => ?_⟩
  · rw [hr, map_length_set hmid (by rw [hw2', List.length_set])]
    exact map_length_set hw1 (by rw [hw1', List.length_set])
  · by_cases hj : j / 1024 = 0
    · rw [ite_eq_right (by omega : ¬ j = 1024 * (c2 + 1) + o2),
        ite_eq_right (by omega : ¬ j = 1024 * (c1 + 1) + o1)]
      exact cellAt_congr_first hj hf
    · by_cases hc2 : j / 1024 - 1 = c2
      · have hg' : s'.rest.val[j / 1024 - 1]? = some w2' := by
          rw [hr, hc2]
          exact get?_set_self' w2' (get?_lt hmid)
        have hg : s.rest.val[j / 1024 - 1]? = some w2 := by rw [hc2, hw2]
        rw [cellAt_rest hj hg', hw2']
        by_cases e2 : j = 1024 * (c2 + 1) + o2
        · rw [ite_eq_left e2]
          have e : j % 1024 = o2 := by omega
          rw [e]
          exact get?_set_self' v h2
        · rw [ite_eq_right e2, ite_eq_right (by omega : ¬ j = 1024 * (c1 + 1) + o1),
            get?_set_ne' v (by omega : j % 1024 ≠ o2), cellAt_rest hj hg]
      · rw [ite_eq_right (by omega : ¬ j = 1024 * (c2 + 1) + o2)]
        by_cases hc1 : j / 1024 - 1 = c1
        · have hg' : s'.rest.val[j / 1024 - 1]? = some w1' := by
            rw [hr, get?_set_ne' w2' hc2, hc1]
            exact get?_set_self' w1' (get?_lt hw1)
          have hg : s.rest.val[j / 1024 - 1]? = some w1 := by rw [hc1, hw1]
          rw [cellAt_rest hj hg', hw1']
          by_cases e1 : j = 1024 * (c1 + 1) + o1
          · rw [ite_eq_left e1]
            have e : j % 1024 = o1 := by omega
            rw [e]
            exact get?_set_self' u h1
          · rw [ite_eq_right e1, get?_set_ne' u (by omega : j % 1024 ≠ o1), cellAt_rest hj hg]
        · rw [ite_eq_right (by omega : ¬ j = 1024 * (c1 + 1) + o1)]
          unfold cellAt
          rw [ite_eq_right hj, ite_eq_right hj, hr, get?_set_ne' _ hc2, get?_set_ne' _ hc1]

theorem first_eq {s : item_space.ItemSpaceCore T} {v : alloc.vec.Vec (Option T)}
    (h : v.val = s.first.val) : ({ s with first := v } : item_space.ItemSpaceCore T) = s := by
  have e : v = s.first := alloc.vec.Vec.ext _ _ h
  rw [e]

theorem rest_eq {s : item_space.ItemSpaceCore T} {v : alloc.vec.Vec (alloc.vec.Vec (Option T))}
    (h : v.val = s.rest.val) : ({ s with rest := v } : item_space.ItemSpaceCore T) = s := by
  have e : v = s.rest := alloc.vec.Vec.ext _ _ h
  rw [e]

theorem both_eq {s : item_space.ItemSpaceCore T} {v1 : alloc.vec.Vec (Option T)}
    {v2 : alloc.vec.Vec (alloc.vec.Vec (Option T))} (h1 : v1.val = s.first.val)
    (h2 : v2.val = s.rest.val) :
    ({ s with first := v1, rest := v2 } : item_space.ItemSpaceCore T) = s := by
  have e1 : v1 = s.first := alloc.vec.Vec.ext _ _ h1
  have e2 : v2 = s.rest := alloc.vec.Vec.ext _ _ h2
  rw [e1, e2]

/-- How `get_two_mut` orders the two slots. -/
structure LowHigh (a b : Std.U32) (low high : Std.Usize) : Prop where
  rev : a.val > b.val → low.val = b.val ∧ high.val = a.val
  fwd : ¬ a.val > b.val → low.val = a.val ∧ high.val = b.val

/-- What `get_two_mut` answers: the items of the two slots, and a way to
write both. -/
structure TwoMutPost (s : item_space.ItemSpaceCore T) (a b : Nat) (o : Option (T × T))
    (back : Option (T × T) → item_space.ItemSpaceCore T) : Prop where
  /-- the items of the slots `a` and `b`, in this order; none when the two
  are one slot, or when one of them holds no item -/
  answer : o = if a = b then none else twoOf (cellAt s a) (cellAt s b) false
  /-- nothing written: the arena as it was -/
  same : back none = s
  /-- no two items to write to: the arena as it was -/
  absent : o = none → ∀ r, back r = s
  /-- a write changes the items of these two slots only: `p` is the item of
  `a` afterwards and `q` the item of `b` -/
  write : ∀ p q, o ≠ none → Upd2 s a b (some p) (some q) (back (some (p, q)))

/-- From the two slots in their order to the two slots as they were asked
for. -/
theorem twoMutPost_of {s : item_space.ItemSpaceCore T} {a b : Std.U32} {low high : Std.Usize}
    {R : Bool} {o : Option (T × T)} {back : Option (T × T) → item_space.ItemSpaceCore T}
    (hL : LowHigh a b low high) (hRt : a.val > b.val → R = true)
    (hRf : ¬ a.val > b.val → R = false)
    (hans : o = if low.val < high.val then twoOf (cellAt s low.val) (cellAt s high.val) R
      else none)
    (hsame : back none = s) (habs : o = none → ∀ r, back r = s)
    (hwrite : ∀ p q, o ≠ none → Upd2 s low.val high.val (cond R (some q) (some p))
      (cond R (some p) (some q)) (back (some (p, q)))) :
    TwoMutPost s a.val b.val o back := by
  by_cases hgt : a.val > b.val
  · obtain ⟨el, eh⟩ := hL.rev hgt
    have eR := hRt hgt
    rw [el, eh, eR] at hans
    refine ⟨?_, hsame, habs, fun p q hne => ?_⟩
    · rw [hans, ite_eq_left (by omega : b.val < a.val), ite_eq_right (by omega : ¬ a.val = b.val)]
      exact twoOf_swap _ _
    · have h := hwrite p q hne
      rw [el, eh, eR] at h
      exact Upd2.swap h (by omega)
  · obtain ⟨el, eh⟩ := hL.fwd hgt
    have eR := hRf hgt
    rw [el, eh, eR] at hans
    refine ⟨?_, hsame, habs, fun p q hne => ?_⟩
    · by_cases e : a.val = b.val
      · rw [hans, ite_eq_left e, ite_eq_right (by omega : ¬ a.val < b.val)]
      · rw [hans, ite_eq_right e, ite_eq_left (by omega : a.val < b.val)]
    · have h := hwrite p q hne
      rw [el, eh, eR] at h
      exact h

theorem twoOf_ne_none {x y : Option (Option T)} {R : Bool} (h : twoOf x y R ≠ none) :
    ∃ a b, x = some (some a) ∧ y = some (some b) := by
  cases hr : twoOf x y R with
  | none => exact absurd hr h
  | some r =>
    obtain ⟨a, b, hx, hy, _⟩ := twoOf_some hr
    exact ⟨a, b, hx, hy⟩

theorem twoOf_left_none (y : Option (Option T)) (rev : Bool) : twoOf none y rev = none := rfl

theorem if_twoOf_none_left {c : Prop} [Decidable c] (y : Option (Option T)) (R : Bool) :
    (none : Option (T × T)) = if c then twoOf none y R else none := by
  by_cases h : c
  · rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h]

theorem if_twoOf_none_right {c : Prop} [Decidable c] (x : Option (Option T)) (R : Bool) :
    (none : Option (T × T)) = if c then twoOf x none R else none := by
  by_cases h : c
  · rw [ite_eq_left h, twoOf_right_none]
  · rw [ite_eq_right h]

/-- **`get_two_mut` answers the items of two slots, in the order asked**, on
every arena, and what is written through the two borrows is the item of its
slot afterwards; no other slot changes. The slots have to be two, and both
have to hold an item: otherwise it answers `none` and the arena stays as it
is. -/
theorem get_two_mut_spec (s : item_space.ItemSpaceCore T) (a b : Std.U32) :
    item_space.ItemSpaceCore.get_two_mut s a b ⦃ o back =>
      TwoMutPost s a.val b.val o back ⦄ := by
  unfold item_space.ItemSpaceCore.get_two_mut
  simp only [item_space.CHUNK_SIZE]
  have hca : a.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  have hcb : b.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  have hlh : (if a > b then (do
        let i ← lift (UScalar.cast .Usize b)
        let i1 ← lift (UScalar.cast .Usize a)
        ok (i, i1))
      else (do
        let i ← lift (UScalar.cast .Usize a)
        let i1 ← lift (UScalar.cast .Usize b)
        ok (i, i1)) : Result (Std.Usize × Std.Usize)) ⦃ low high => LowHigh a b low high ⦄ := by
    by_cases hab : a > b
    · simp only [hab, ↓reduceIte]
      have hgt : a.val > b.val := by scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.Usize b hcb as ⟨i, hi⟩
      step with UScalar.cast_inBounds_spec UScalarTy.Usize a hca as ⟨i1, hi1⟩
      exact ⟨fun _ => ⟨hi, hi1⟩, fun hn => absurd hgt hn⟩
    · simp only [hab, ↓reduceIte]
      have hgt : ¬ a.val > b.val := by scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.Usize a hca as ⟨i, hi⟩
      step with UScalar.cast_inBounds_spec UScalarTy.Usize b hcb as ⟨i1, hi1⟩
      exact ⟨fun h => absurd h hgt, fun _ => ⟨hi, hi1⟩⟩
  step with hlh as ⟨low, high, hLH⟩
  have hL : LowHigh a b low high := hLH
  have hRt : a.val > b.val → decide (a > b) = true := fun h => decide_eq_true (by scalar_tac)
  have hRf : ¬ a.val > b.val → decide (a > b) = false := fun h => decide_eq_false (by scalar_tac)
  generalize decide (a > b) = R at hRt hRf ⊢
  have hle : low.val ≤ high.val := by
    by_cases hgt : a.val > b.val
    · have := hL.rev hgt
      omega
    · have := hL.fwd hgt
      omega
  step as ⟨lc, hlc⟩
  step as ⟨li, hli⟩
  step as ⟨hc, hhc⟩
  step as ⟨hi, hhi⟩
  have hlcv : lc.val = low.val / 1024 := by scalar_tac
  have hliv : li.val = low.val % 1024 := by scalar_tac
  have hhcv : hc.val = high.val / 1024 := by scalar_tac
  have hhiv : hi.val = high.val % 1024 := by scalar_tac
  by_cases hsc : lc = hc
  · have hsc' : (lc = hc) = True := eq_true hsc
    simp only [hsc', ↓reduceIte]
    have hsame_chunk : low.val / 1024 = high.val / 1024 := by rw [← hlcv, ← hhcv, hsc]
    have hlt_iff : li.val < hi.val ↔ low.val < high.val := by
      constructor <;> intro h <;> omega
    by_cases h0 : lc = 0#usize
    · -- both slots in the first chunk
      have h0' : (lc = 0#usize) = True := eq_true h0
      simp only [h0', ↓reduceIte, lift, alloc.vec.Vec.deref_mut]
      have hlz : low.val / 1024 = 0 := by
        rw [← hlcv, h0]
        rfl
      have hhz : high.val / 1024 = 0 := by omega
      step with pair_of_spec s.first.slice li hi R as ⟨o, pback, hpo⟩
      have hP : PairOfPost s.first.val li.val hi.val R o pback := hpo
      refine twoMutPost_of hL hRt hRf ?_ (first_eq hP.same) (fun hn r => first_eq (hP.absent hn r))
        (fun p q hne => ?_)
      · rw [hP.answer, cellAt_first hlz, cellAt_first hhz, ← hliv, ← hhiv]
        by_cases hlt : low.val < high.val
        · rw [ite_eq_left hlt, ite_eq_left (hlt_iff.mpr hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (fun h => hlt (hlt_iff.mp h))]
      · have hlt : li.val < hi.val := by
          by_contra h
          apply hne
          rw [hP.answer, ite_eq_right h]
        have hsome : twoOf s.first.val[li.val]? s.first.val[hi.val]? R ≠ none := by
          have h := hP.answer
          rw [ite_eq_left hlt] at h
          rw [← h]
          exact hne
        obtain ⟨x, y, hx, hy⟩ := twoOf_ne_none hsome
        have hw' : (pback (some (p, q))).val =
            (s.first.val.set li.val (cond R (some q) (some p))).set hi.val
              (cond R (some p) (some q)) := by
          have hw := hP.write p q hne
          cases R <;> exact hw
        have el : low.val = li.val := by omega
        have eh : high.val = hi.val := by omega
        rw [el, eh]
        exact upd2_first rfl rfl rfl rfl hw' (get?_lt hx) (get?_lt hy) (by omega) (by omega)
    · -- both slots in one chunk after the first
      simp only [h0, ↓reduceIte]
      have hlnz : ¬ low.val / 1024 = 0 := by
        intro e
        apply h0
        apply UScalar.eq_of_val_eq
        rw [hlcv, e]
        rfl
      have hhnz : ¬ high.val / 1024 = 0 := by omega
      step as ⟨ci, hci⟩
      have hciv : ci.val = low.val / 1024 - 1 := by scalar_tac
      by_cases hin : ci < alloc.vec.Vec.len s.rest
      · simp only [hin, ↓reduceIte, lift, alloc.vec.Vec.deref_mut]
        have hcil : ci.val < s.rest.val.length := by scalar_tac
        step as ⟨w, iback, hw, hiback⟩
        have hgw : s.rest.val[low.val / 1024 - 1]? = some w := by
          rw [← hciv]
          exact get?_of_getElem hcil hw
        have hgw' : s.rest.val[high.val / 1024 - 1]? = some w := by rw [← hsame_chunk, hgw]
        have hbv : ∀ c : alloc.vec.Vec (Option T),
            (iback c).val = s.rest.val.set (low.val / 1024 - 1) c := by
          intro c
          rw [hiback, ← hciv]
          simp
        step with pair_of_spec w.slice li hi R as ⟨o, pback, hpo⟩
        have hP : PairOfPost w.val li.val hi.val R o pback := hpo
        have hkeep : ∀ r, (pback r).val = w.val →
            ({ s with rest := iback ⟨pback r⟩ } : item_space.ItemSpaceCore T) = s := by
          intro r hr
          apply rest_eq
          have e : (⟨pback r⟩ : alloc.vec.Vec (Option T)) = w := alloc.vec.Vec.ext _ _ hr
          rw [hbv, e]
          exact set_eq_self hgw
        refine twoMutPost_of hL hRt hRf ?_ (hkeep none hP.same)
          (fun hn r => hkeep r (hP.absent hn r)) (fun p q hne => ?_)
        · rw [hP.answer, cellAt_rest hlnz hgw, cellAt_rest hhnz hgw', ← hliv, ← hhiv]
          by_cases hlt : low.val < high.val
          · rw [ite_eq_left hlt, ite_eq_left (hlt_iff.mpr hlt)]
          · rw [ite_eq_right hlt, ite_eq_right (fun h => hlt (hlt_iff.mp h))]
        · have hlt : li.val < hi.val := by
            by_contra h
            apply hne
            rw [hP.answer, ite_eq_right h]
          have hsome : twoOf w.val[li.val]? w.val[hi.val]? R ≠ none := by
            have h := hP.answer
            rw [ite_eq_left hlt] at h
            rw [← h]
            exact hne
          obtain ⟨x, y, hx, hy⟩ := twoOf_ne_none hsome
          have hw' : (⟨pback (some (p, q))⟩ : alloc.vec.Vec (Option T)).val =
              (w.val.set li.val (cond R (some q) (some p))).set hi.val
                (cond R (some p) (some q)) := by
            have hwr := hP.write p q hne
            cases R <;> exact hwr
          have hU := upd2_chunk (s := s)
            (s' := { s with rest := iback ⟨pback (some (p, q))⟩ }) rfl rfl rfl rfl hgw (hbv _) hw'
            (get?_lt hx) (get?_lt hy) (by omega) (by omega)
          have el : 1024 * (low.val / 1024 - 1 + 1) + li.val = low.val := by omega
          have eh : 1024 * (low.val / 1024 - 1 + 1) + hi.val = high.val := by omega
          rw [el, eh] at hU
          exact hU
      · simp only [hin, ↓reduceIte, spec_ok, uncurry'_pair]
        have hl : s.rest.val.length ≤ low.val / 1024 - 1 := by scalar_tac
        have hcl : cellAt s low.val = none := cellAt_rest_none hlnz (get?_none hl)
        refine twoMutPost_of hL hRt hRf ?_ rfl (fun _ _ => rfl) (fun p q hne => absurd rfl hne)
        rw [hcl]
        exact if_twoOf_none_left _ _
  · simp only [hsc, ↓reduceIte]
    have hdc : ¬ low.val / 1024 = high.val / 1024 := by
      intro e
      apply hsc
      apply UScalar.eq_of_val_eq
      rw [hlcv, hhcv, e]
    have hlow_lt : low.val < high.val := by
      by_contra h
      have e : low.val = high.val := by omega
      rw [e] at hdc
      exact hdc rfl
    by_cases h0 : lc = 0#usize
    · -- a slot of the first chunk and a slot of a chunk after it
      have h0' : (lc = 0#usize) = True := eq_true h0
      simp only [h0', ↓reduceIte]
      have hlz : low.val / 1024 = 0 := by
        rw [← hlcv, h0]
        rfl
      have hhnz : ¬ high.val / 1024 = 0 := by omega
      by_cases hlf : li < alloc.vec.Vec.len s.first
      · simp only [hlf, ↓reduceIte]
        have hlfl : li.val < s.first.val.length := by scalar_tac
        step as ⟨ci, hci⟩
        have hciv : ci.val = high.val / 1024 - 1 := by scalar_tac
        by_cases hin : ci < alloc.vec.Vec.len s.rest
        · simp only [hin, ↓reduceIte]
          have hcil : ci.val < s.rest.val.length := by scalar_tac
          step as ⟨w, iback, hw, hiback⟩
          have hgw : s.rest.val[high.val / 1024 - 1]? = some w := by
            rw [← hciv]
            exact get?_of_getElem hcil hw
          have hbv : ∀ c : alloc.vec.Vec (Option T),
              (iback c).val = s.rest.val.set (high.val / 1024 - 1) c := by
            intro c
            rw [hiback, ← hciv]
            simp
          have hkeep : (iback w).val = s.rest.val := by
            rw [hbv]
            exact set_eq_self hgw
          by_cases hhw : hi < alloc.vec.Vec.len w
          · simp only [hhw, ↓reduceIte]
            have hhwl : hi.val < w.val.length := by scalar_tac
            step as ⟨x, fback, hx, hfback⟩
            step as ⟨y, cback, hy, hcback⟩
            have hgx : s.first.val[low.val % 1024]? = some x := by
              rw [← hliv]
              exact get?_of_getElem hlfl hx
            have hgy : w.val[high.val % 1024]? = some y := by
              rw [← hhiv]
              exact get?_of_getElem hhwl hy
            have hfv : ∀ u : Option T, (fback u).val = s.first.val.set (low.val % 1024) u := by
              intro u
              rw [hfback, ← hliv]
              simp
            have hcv : ∀ v : Option T, (cback v).val = w.val.set (high.val % 1024) v := by
              intro v
              rw [hcback, ← hhiv]
              simp
            step with pair_spec x y R as ⟨o, pback, hpair⟩
            have hP : PairPost x y R o pback := hpair
            -- the arena after a write of `(u, v)` through the two cells
            have hsame2 : ({ s with first := fback x, rest := iback (cback y) } :
                item_space.ItemSpaceCore T) = s := by
              apply both_eq
              · rw [hfv]
                exact set_eq_self hgx
              · have e : cback y = w := by
                  apply alloc.vec.Vec.ext
                  rw [hcv]
                  exact set_eq_self hgy
                rw [e]
                exact hkeep
            have hcl : cellAt s low.val = some x := by rw [cellAt_first hlz, hgx]
            have hch : cellAt s high.val = some y := by rw [cellAt_rest hhnz hgw, hgy]
            by_cases hboth : ∃ xa yb, x = some xa ∧ y = some yb
            · obtain ⟨xa, yb, hxa, hyb⟩ := hboth
              obtain ⟨ho, hbn, hbw⟩ := hP.both xa yb hxa hyb
              refine twoMutPost_of hL hRt hRf ?_ ?_ (fun hn r => ?_) (fun p q hne => ?_)
              · rw [ho, ite_eq_left hlow_lt, hcl, hch, hxa, hyb]
                rfl
              · rw [hbn]
                exact hsame2
              · rw [ho] at hn
                cases hn
              · rw [hbw p q]
                have hU := upd2_first_chunk (s := s)
                  (s' := { s with first := fback (cond R (some q) (some p)),
                                  rest := iback (cback (cond R (some p) (some q))) })
                  rfl rfl rfl (hfv _) hgw (hbv _) (hcv _) (get?_lt hgx) (get?_lt hgy)
                  (by omega) (by omega)
                have el : low.val % 1024 = low.val := by omega
                have eh : 1024 * (high.val / 1024 - 1 + 1) + high.val % 1024 = high.val := by
                  omega
                rw [el, eh] at hU
                cases R <;> exact hU
            · have hxy : x = none ∨ y = none := by
                cases x with
                | none => exact Or.inl rfl
                | some xa =>
                  cases y with
                  | none => exact Or.inr rfl
                  | some yb => exact absurd ⟨xa, yb, rfl, rfl⟩ hboth
              obtain ⟨ho, hb⟩ := hP.absent hxy
              have hbk : ∀ r, (match pback r with
                  | (o4, o5) => ({ s with first := fback o4, rest := iback (cback o5) } :
                    item_space.ItemSpaceCore T)) = s := by
                intro r
                rw [hb r]
                exact hsame2
              refine twoMutPost_of hL hRt hRf ?_ (hbk none) (fun _ r => hbk r)
                (fun p q hne => absurd ho hne)
              rw [ho, ite_eq_left hlow_lt, hcl, hch]
              rcases hxy with e | e
              · rw [e]
                rfl
              · rw [e]
                cases x <;> rfl
          · simp only [hhw, ↓reduceIte, spec_ok, uncurry'_pair]
            have hl : w.val.length ≤ high.val % 1024 := by scalar_tac
            have hch : cellAt s high.val = none := by rw [cellAt_rest hhnz hgw, get?_none hl]
            refine twoMutPost_of hL hRt hRf ?_ (rest_eq hkeep) (fun _ _ => rest_eq hkeep)
              (fun p q hne => absurd rfl hne)
            rw [hch]
            exact if_twoOf_none_right _ _
        · simp only [hin, ↓reduceIte, spec_ok, uncurry'_pair]
          have hl : s.rest.val.length ≤ high.val / 1024 - 1 := by scalar_tac
          have hch : cellAt s high.val = none := cellAt_rest_none hhnz (get?_none hl)
          refine twoMutPost_of hL hRt hRf ?_ rfl (fun _ _ => rfl) (fun p q hne => absurd rfl hne)
          rw [hch]
          exact if_twoOf_none_right _ _
      · simp only [hlf, ↓reduceIte, spec_ok, uncurry'_pair]
        have hl : s.first.val.length ≤ low.val % 1024 := by scalar_tac
        have hcl : cellAt s low.val = none := by rw [cellAt_first hlz, get?_none hl]
        refine twoMutPost_of hL hRt hRf ?_ rfl (fun _ _ => rfl) (fun p q hne => absurd rfl hne)
        rw [hcl]
        exact if_twoOf_none_left _ _
    · -- two chunks after the first one
      simp only [h0, ↓reduceIte]
      have hlnz : ¬ low.val / 1024 = 0 := by
        intro e
        apply h0
        apply UScalar.eq_of_val_eq
        rw [hlcv, e]
        rfl
      have hclt : low.val / 1024 < high.val / 1024 := by
        have := Nat.div_le_div_right (c := 1024) hle
        omega
      have hhnz : ¬ high.val / 1024 = 0 := by omega
      have hlch : lc < hc := by scalar_tac
      simp only [hlch, ↓reduceIte]
      step as ⟨ci, hci⟩
      have hciv : ci.val = high.val / 1024 - 1 := by scalar_tac
      by_cases hin : ci < alloc.vec.Vec.len s.rest
      · simp only [hin, ↓reduceIte, lift, alloc.vec.Vec.deref_mut]
        have hcil : ci.val < s.rest.val.length := by scalar_tac
        have hsl : (ci : Std.Usize).val ≤ s.rest.slice.val.length := by
          show ci.val ≤ s.rest.val.length
          omega
        step as ⟨before, after, sback, h1, h2, h3, h4, h5⟩
        have h1' : before.val.length = ci.val := h1
        have h2' : after.val.length = s.rest.val.length - ci.val := h2
        have h3' : before.val = s.rest.val.take ci.val := h3
        have h4' : after.val = s.rest.val.drop ci.val := h4
        step as ⟨c1, hc1⟩
        have hc1v : c1.val = low.val / 1024 - 1 := by scalar_tac
        have hc1lt : c1.val < ci.val := by omega
        have hb1 : c1.val < before.val.length := by omega
        have hb2 : (0#usize : Std.Usize).val < after.val.length := by
          rw [usize_zero_val]
          omega
        step as ⟨lw, lback, hlw, hlback⟩
        step as ⟨hw, hback, hhw, hhback⟩
        have hgl : s.rest.val[low.val / 1024 - 1]? = some lw := by
          have h := get?_of_getElem hb1 hlw
          rw [h3', get?_take_lt _ hc1lt, hc1v] at h
          exact h
        have hgh : s.rest.val[high.val / 1024 - 1]? = some hw := by
          have h := get?_of_getElem hb2 hhw
          rw [usize_zero_val, h4', get?_drop_zero, hciv] at h
          exact h
        have hne12 : low.val / 1024 - 1 ≠ high.val / 1024 - 1 := by omega
        -- the chunks after a write of the two chunks
        have hrest : ∀ lw' hw' : alloc.vec.Vec (Option T),
            (sback (lback lw', hback hw')).val =
              (s.rest.val.set (low.val / 1024 - 1) lw').set (high.val / 1024 - 1) hw' := by
          intro lw' hw'
          have hbu : (lback lw').val = before.val.set c1.val lw' := by
            rw [hlback]
            simp
          have hbv : (hback hw').val = after.val.set 0 hw' := by
            rw [hhback]
            simp
          have h := (h5 (lback lw') (hback hw')
            (by show (lback lw').val.length = ci.val; rw [hbu, List.length_set]; exact h1')
            (by
              show (hback hw').val.length = s.rest.val.length - ci.val
              rw [hbv, List.length_set]
              exact h2')).1
          rw [h, hbu, hbv, h3', h4', hc1v, ← hciv]
          exact split_set2 s.rest.val (by omega) hcil lw' hw'
        have hkeep : ∀ lw' hw' : alloc.vec.Vec (Option T), lw'.val = lw.val → hw'.val = hw.val →
            ({ s with rest := ⟨sback (lback lw', hback hw')⟩ } : item_space.ItemSpaceCore T) = s := by
          intro lw' hw' el eh
          have e1 : lw' = lw := alloc.vec.Vec.ext _ _ el
          have e2 : hw' = hw := alloc.vec.Vec.ext _ _ eh
          apply rest_eq
          show (sback (lback lw', hback hw')).val = s.rest.val
          rw [hrest, e1, e2, set_eq_self hgl, set_eq_self hgh]
        have hcl0 : cellAt s low.val = lw.val[low.val % 1024]? := cellAt_rest hlnz hgl
        have hch0 : cellAt s high.val = hw.val[high.val % 1024]? := cellAt_rest hhnz hgh
        by_cases hll : li < alloc.vec.Vec.len lw
        · simp only [hll, ↓reduceIte]
          have hlll : li.val < lw.val.length := by scalar_tac
          by_cases hhh : hi < alloc.vec.Vec.len hw
          · simp only [hhh, ↓reduceIte]
            have hhhl : hi.val < hw.val.length := by scalar_tac
            step as ⟨x, fback, hx, hfback⟩
            step as ⟨y, cback, hy, hcback⟩
            have hgx : lw.val[low.val % 1024]? = some x := by
              rw [← hliv]
              exact get?_of_getElem hlll hx
            have hgy : hw.val[high.val % 1024]? = some y := by
              rw [← hhiv]
              exact get?_of_getElem hhhl hy
            have hfv : ∀ u : Option T, (fback u).val = lw.val.set (low.val % 1024) u := by
              intro u
              rw [hfback, ← hliv]
              simp
            have hcv : ∀ v : Option T, (cback v).val = hw.val.set (high.val % 1024) v := by
              intro v
              rw [hcback, ← hhiv]
              simp
            step with pair_spec x y R as ⟨o, pback, hpair⟩
            have hP : PairPost x y R o pback := hpair
            have hsame2 : ({ s with rest := ⟨sback (lback (fback x), hback (cback y))⟩ } :
                item_space.ItemSpaceCore T) = s :=
              hkeep _ _ (by rw [hfv]; exact set_eq_self hgx) (by rw [hcv]; exact set_eq_self hgy)
            have hcl : cellAt s low.val = some x := by rw [hcl0, hgx]
            have hch : cellAt s high.val = some y := by rw [hch0, hgy]
            by_cases hboth : ∃ xa yb, x = some xa ∧ y = some yb
            · obtain ⟨xa, yb, hxa, hyb⟩ := hboth
              obtain ⟨ho, hbn, hbw⟩ := hP.both xa yb hxa hyb
              refine twoMutPost_of hL hRt hRf ?_ ?_ (fun hn r => ?_) (fun p q hne => ?_)
              · rw [ho, ite_eq_left hlow_lt, hcl, hch, hxa, hyb]
                rfl
              · rw [hbn]
                exact hsame2
              · rw [ho] at hn
                cases hn
              · rw [hbw p q]
                have hU := upd2_chunks (s := s)
                  (s' := { s with rest := ⟨sback (lback (fback (cond R (some q) (some p))),
                    hback (cback (cond R (some p) (some q))))⟩ })
                  rfl rfl rfl rfl hne12 hgl hgh (hrest _ _) (hfv _) (hcv _) (get?_lt hgx)
                  (get?_lt hgy) (by omega) (by omega)
                have el : 1024 * (low.val / 1024 - 1 + 1) + low.val % 1024 = low.val := by omega
                have eh : 1024 * (high.val / 1024 - 1 + 1) + high.val % 1024 = high.val := by
                  omega
                rw [el, eh] at hU
                cases R <;> exact hU
            · have hxy : x = none ∨ y = none := by
                cases x with
                | none => exact Or.inl rfl
                | some xa =>
                  cases y with
                  | none => exact Or.inr rfl
                  | some yb => exact absurd ⟨xa, yb, rfl, rfl⟩ hboth
              obtain ⟨ho, hb⟩ := hP.absent hxy
              have hbk : ∀ r, (match pback r with
                  | (o4, o5) => ({ s with rest := ⟨sback (lback (fback o4), hback (cback o5))⟩ } :
                    item_space.ItemSpaceCore T)) = s := by
                intro r
                rw [hb r]
                exact hsame2
              refine twoMutPost_of hL hRt hRf ?_ (hbk none) (fun _ r => hbk r)
                (fun p q hne => absurd ho hne)
              rw [ho, ite_eq_left hlow_lt, hcl, hch]
              rcases hxy with e | e
              · rw [e]
                rfl
              · rw [e]
                cases x <;> rfl
          · simp only [hhh, ↓reduceIte, spec_ok, uncurry'_pair]
            have hl : hw.val.length ≤ high.val % 1024 := by scalar_tac
            have hch : cellAt s high.val = none := by rw [hch0, get?_none hl]
            refine twoMutPost_of hL hRt hRf ?_ (hkeep lw hw rfl rfl) (fun _ _ => hkeep lw hw rfl rfl)
              (fun p q hne => absurd rfl hne)
            rw [hch]
            exact if_twoOf_none_right _ _
        · simp only [hll, ↓reduceIte, spec_ok, uncurry'_pair]
          have hl : lw.val.length ≤ low.val % 1024 := by scalar_tac
          have hcl : cellAt s low.val = none := by rw [hcl0, get?_none hl]
          refine twoMutPost_of hL hRt hRf ?_ (hkeep lw hw rfl rfl) (fun _ _ => hkeep lw hw rfl rfl)
            (fun p q hne => absurd rfl hne)
          rw [hcl]
          exact if_twoOf_none_left _ _
      · simp only [hin, ↓reduceIte, spec_ok, uncurry'_pair]
        have hl : s.rest.val.length ≤ high.val / 1024 - 1 := by scalar_tac
        have hch : cellAt s high.val = none := cellAt_rest_none hhnz (get?_none hl)
        refine twoMutPost_of hL hRt hRf ?_ rfl (fun _ _ => rfl) (fun p q hne => absurd rfl hne)
        rw [hch]
        exact if_twoOf_none_right _ _

end YoctoCore.Properties.ItemSpace
