/-
`y_octo_core::id_order`: the ids one conflict scan has walked, in their order,
with a table that says where an id is in that order.

A list is its ids (`s.ids`), a table of places and how many of the first ids
the table holds (`s.indexed`). `WF` is the invariant: the table names the
first `indexed` places and no other, it is at most half full, and every place
it holds is reached from the home slot of the id at that place without
meeting a free slot (`IdSetModel.TableOK`, on the places the slots hold).
Every function is total on every list that satisfies `WF` and keeps it.

`with_key` makes the empty list of a key (`with_key_spec`; `new` is the one of
the key `(0, 0)`). `push` puts an id at the end and refuses only at `2 ^ 30`
ids (`push_spec`).
`recent` looks at the place answered last and through the last sixteen ids:
the place it answers holds the id, `Absent` is a list without the id, and
`Far` says that the last sixteen ids are not the id and that there are more
(`recent_spec`). The place answered last is no part of the invariant (`Same`,
`WF.same`). `position` brings
the table up to the list and asks it: the place it answers holds the id, and
`none` is a list without the id (`position_spec`). Neither says which place
of an id that is in the list twice it answers.

The hash is the keyed one of `id_set`. As there, it only chooses the home
slot, and that this is a slot of the table is all the proofs use, for every
key: that ids are spread well, and that a peer cannot choose ids that are
not, is no theorem here. `key` changes the key only while the table holds no
id (`key_spec`).
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.ListAux
import YoctoCore.Properties.IdSetModel
import YoctoCore.Properties.IdSet

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties.ListAux YoctoCore.Properties.IdSetModel
open YoctoCore.Properties.IdSet (homeN homeN_lt homeN_zero home_spec id_eq_iff get?_of_getElem
  usize_zero_val)

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace YoctoCore.Properties.IdOrder

/-! ## The places a table holds -/

/-- What a slot of the table holds: nothing, or a place of the list. -/
def slotOf (e : Std.U32) : Option Nat := if e.val = 0 then none else some (e.val - 1)

theorem slotOf_zero : slotOf 0#u32 = none := by
  unfold slotOf
  have h : (0#u32 : Std.U32).val = 0 := rfl
  exact ite_eq_left h

theorem slotOf_pos {e : Std.U32} (h : ¬ e.val = 0) : slotOf e = some (e.val - 1) := by
  unfold slotOf
  exact ite_eq_right h

/-- The table as the places its slots hold. -/
def places (t : List Std.U32) : List (Option Nat) := t.map slotOf

theorem places_length (t : List Std.U32) : (places t).length = t.length := List.length_map _

theorem places_get? (t : List Std.U32) (i : Nat) : (places t)[i]? = (t[i]?).map slotOf :=
  get?_map slotOf t i

theorem map_set' {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat) (a : α), (l.set i a).map f = (l.map f).set i (f a)
  | [], i, _ => by cases i <;> rfl
  | _ :: _, 0, _ => rfl
  | x :: t, i + 1, a => by
    show f x :: (t.set i a).map f = f x :: (t.map f).set i (f a)
    rw [map_set' f t i a]

theorem places_set (t : List Std.U32) (i : Nat) (e : Std.U32) :
    places (t.set i e) = (places t).set i (slotOf e) := map_set' slotOf t i e

theorem places_replicate (n : Nat) :
    places (List.replicate n 0#u32) = List.replicate n (none : Option Nat) := by
  unfold places
  rw [List.map_replicate, slotOf_zero]

/-- The home slot of a place in a table of `cap` slots: the one of the id at
that place. -/
noncomputable def homeAt (k0 k1 : Std.U64) (ids : List yata_store.IdCore) (cap : Nat) (p : Nat) :
    Nat :=
  match ids[p]? with
  | some x => homeN k0 k1 x cap
  | none => 0

theorem homeAt_of {k0 k1 : Std.U64} {ids : List yata_store.IdCore} {cap p : Nat}
    {x : yata_store.IdCore} (h : ids[p]? = some x) :
    homeAt k0 k1 ids cap p = homeN k0 k1 x cap := by
  unfold homeAt
  rw [h]

/-- The table of a list: every place it holds is reached from the home slot
of the id at that place. -/
def Table (k0 k1 : Std.U64) (ids : List yata_store.IdCore) (t : List Std.U32) : Prop :=
  TableOK (homeAt k0 k1 ids t.length) (places t)

/-- `TableOK` only asks for the home slots of the elements of the table. -/
theorem tableOK_congr {α : Type} {home home' : α → Nat} {l : List (Option α)}
    (hok : TableOK home l) (h : ∀ x, Mem l x → home' x = home x) : TableOK home' l := by
  intro j x hj
  obtain ⟨t, ht, e, hb⟩ := hok j x hj
  have hx : home' x = home x := h x (get?_mem hj)
  rw [hx]
  exact ⟨t, ht, e, hb⟩

theorem table_replicate (k0 k1 : Std.U64) (ids : List yata_store.IdCore) (n : Nat) :
    Table k0 k1 ids (List.replicate n 0#u32) := by
  unfold Table
  rw [places_replicate]
  exact tableOK_replicate _ n

theorem not_mem_places_replicate (n p : Nat) : ¬ Mem (places (List.replicate n 0#u32)) p := by
  rw [places_replicate]
  exact not_mem_replicate n p

/-- The slot after `ix`, as the loops compute it. -/
theorem wrap_spec (idx1 slots : Std.Usize) (ix cap : Nat) (h1 : idx1.val = ix + 1)
    (hs : slots.val = cap) :
    (if idx1 = slots then ok 0#usize else ok idx1 : Result Std.Usize) ⦃ r =>
      r.val = nextSlot cap ix ⦄ := by
  unfold nextSlot
  by_cases e : idx1 = slots
  · have e' : (idx1 = slots) = True := eq_true e
    simp only [e', ↓reduceIte, spec_ok]
    have hc : ix + 1 = cap := by rw [← h1, e, hs]
    rw [ite_eq_left hc]
    exact usize_zero_val
  · simp only [e, ↓reduceIte, spec_ok]
    have hc : ¬ ix + 1 = cap := by
      intro hc
      apply e
      apply UScalar.eq_of_val_eq
      rw [h1, hc, hs]
    rw [ite_eq_right hc]
    exact h1

/-- Where a walk starts: the home slot of the id, and the slot `0` of a table
without slots. -/
theorem start_spec (k0 k1 : Std.U64) (id : yata_store.IdCore) (slots : Std.Usize) :
    (if slots = 0#usize then ok 0#usize else id_set.home k0 k1 id slots : Result Std.Usize) ⦃ r =>
      r.val = homeN k0 k1 id slots.val ⦄ := by
  by_cases e : slots = 0#usize
  · have e' : (slots = 0#usize) = True := eq_true e
    simp only [e', ↓reduceIte, spec_ok]
    have hs0 : slots.val = 0 := by
      rw [e]
      exact usize_zero_val
    have hh : homeN k0 k1 id slots.val = 0 := by
      rw [hs0]
      exact homeN_zero k0 k1 id
    rw [hh]
    rfl
  · simp only [e, ↓reduceIte]
    have hpos : 0 < slots.val := by
      have hne : slots.val ≠ 0 := by
        intro h0
        apply e
        apply UScalar.eq_of_val_eq
        rw [h0, usize_zero_val]
      omega
    exact home_spec k0 k1 id slots hpos

/-! ## How many slots -/

/-- The loop of `slots_for`: it stops at a table the ids fill no more than
half of, or at one of `2 ^ 31` slots. -/
theorem slots_for_loop_spec (count slots : Std.Usize) (hpos : 0 < slots.val) :
    id_order.slots_for_loop count slots ⦃ r =>
      0 < r.val ∧ (count.val ≤ r.val / 2 ∨ 1073741824 ≤ r.val / 2) ⦄ := by
  unfold id_order.slots_for_loop
  refine loop.spec_decr_nat
    (fun (s : Std.Usize) => 4294967296 - s.val)
    (fun (s : Std.Usize) => 0 < s.val)
    (fun (r : Std.Usize) => 0 < r.val ∧ (count.val ≤ r.val / 2 ∨ 1073741824 ≤ r.val / 2))
    _ slots ?_ hpos
  intro s hs0
  have hs : 0 < s.val := hs0
  have hmax : (id_order.MAX_IDS).val = 1073741824 := by simp [id_order.MAX_IDS]
  have hu32 : 4294967295 ≤ Std.Usize.max := by scalar_tac
  unfold id_order.slots_for_loop.body
  step as ⟨half, hhalf⟩
  have hhalfv : half.val = s.val / 2 := by scalar_tac
  by_cases hlt : half < count
  · simp only [hlt, ↓reduceIte]
    by_cases hroom : half < id_order.MAX_IDS
    · simp only [hroom, ↓reduceIte]
      have hsmall : s.val / 2 < 1073741824 := by scalar_tac
      have hmul : s.val * 2 ≤ Std.Usize.max := by omega
      step as ⟨s1, hs1⟩
      have hs1v : s1.val = s.val * 2 := by scalar_tac
      refine ⟨?_, ?_⟩
      · show 0 < s1.val
        omega
      · show 4294967296 - s1.val < 4294967296 - s.val
        omega
    · simp only [hroom, ↓reduceIte, spec_ok]
      have hbig : 1073741824 ≤ s.val / 2 := by scalar_tac
      exact ⟨hs, Or.inr hbig⟩
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : count.val ≤ s.val / 2 := by scalar_tac
    exact ⟨hs, Or.inl hge⟩

/-- `slots_for` answers a table the ids fill no more than half of. -/
theorem slots_for_spec (count : Std.Usize) (hc : count.val ≤ 1073741824) :
    id_order.slots_for count ⦃ r => 0 < r.val ∧ count.val * 2 ≤ r.val ⦄ := by
  have hfirst : 0 < (id_order.FIRST_SLOTS).val := by simp [id_order.FIRST_SLOTS]
  refine spec_mono (slots_for_loop_spec count id_order.FIRST_SLOTS hfirst) ?_
  intro r hr
  obtain ⟨h0, h1⟩ := hr
  refine ⟨h0, ?_⟩
  rcases h1 with h | h
  · omega
  · omega

/-! ## Putting a place into the table -/

/-- The loop of a walk after `st` steps, at the slot `ix`: the slots walked
are taken. -/
structure Walking (l : List (Option Nat)) (h ix st : Nat) : Prop where
  bound : st ≤ l.length
  slot : ix = slotAt l.length h st
  busy : Busy l h st

/-- What `put` does to a table with a free slot: the place goes into the
free slot the walk from `h` meets first. -/
structure PutPost (t : List Std.U32) (h p : Nat) (b : Bool) (t' : List Std.U32) : Prop where
  length : t'.length = t.length
  set : ∃ i st, st < (places t).length ∧ slotAt (places t).length h st = i ∧
    Busy (places t) h st ∧ (places t)[i]? = some none ∧ places t' = (places t).set i (some p)

theorem put_loop_spec (table : Slice Std.U32) («at» slots idx0 : Std.Usize)
    (hslots : slots.val = table.val.length) (hidx : idx0.val < table.val.length)
    (hroom : countSome (places table.val) < table.val.length)
    (hat : «at».val + 1 ≤ 4294967295) :
    id_order.put_loop table «at» slots idx0 0#usize ⦃ r =>
      PutPost table.val idx0.val «at».val r.1 r.2.val ⦄ := by
  unfold id_order.put_loop
  have hpl := places_length table.val
  have hinit : Walking (places table.val) idx0.val idx0.val (0#usize : Std.Usize).val := by
    rw [usize_zero_val]
    exact ⟨Nat.zero_le _, rfl, fun t' ht' => absurd ht' (Nat.not_lt_zero _)⟩
  refine loop.spec_decr_nat
    (fun ((_, st) : Std.Usize × Std.Usize) => slots.val - st.val)
    (fun ((ix, st) : Std.Usize × Std.Usize) =>
      Walking (places table.val) idx0.val ix.val st.val)
    (fun (r : Bool × Slice Std.U32) => PutPost table.val idx0.val «at».val r.1 r.2.val)
    _ (idx0, 0#usize) ?_ hinit
  intro ⟨ix, st⟩ hW0
  have hW : Walking (places table.val) idx0.val ix.val st.val := hW0
  have hst := hW.bound
  have hix := hW.slot
  have hbusy := hW.busy
  unfold id_order.put_loop.body
  simp only
  by_cases hlt : st < slots
  · simp only [hlt, ↓reduceIte]
    have hstlt : st.val < table.val.length := by scalar_tac
    have hixlt : ix.val < table.val.length := by
      rw [hix, hpl]
      exact slotAt_lt hidx _
    step as ⟨entry, hentry⟩
    have hget : table.val[ix.val]? = some entry := get?_of_getElem hixlt hentry
    by_cases hz : entry = 0#u32
    · have hz' : (entry = 0#u32) = True := eq_true hz
      simp only [hz', ↓reduceIte]
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = «at».val + 1 := by scalar_tac
      have hc : i1.val ≤ UScalar.max UScalarTy.U32 := by scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.U32 i1 hc as ⟨i2, hi2⟩
      step as ⟨table1, ht1⟩
      have hv : table1.val = table.val.set ix.val i2 := by
        rw [ht1]
        simp
      have hi2v : i2.val = «at».val + 1 := by rw [hi2, hi1v]
      have hslot : slotOf i2 = some «at».val := by
        rw [slotOf_pos (by omega), hi2v]
        rfl
      have hfree : (places table.val)[ix.val]? = some none := by
        rw [places_get?, hget, hz]
        show some (slotOf 0#u32) = some none
        rw [slotOf_zero]
      refine ⟨?_, ix.val, st.val, by omega, hix.symm, hbusy, hfree, ?_⟩
      · show table1.val.length = table.val.length
        rw [hv, List.length_set]
      · show places table1.val = (places table.val).set ix.val (some «at».val)
        rw [hv, places_set, hslot]
    · simp only [hz, ↓reduceIte]
      have hnz : ¬ entry.val = 0 := by
        intro h0
        apply hz
        apply UScalar.eq_of_val_eq
        rw [h0]
        rfl
      have htaken : (places table.val)[ix.val]? = some (some (entry.val - 1)) := by
        rw [places_get?, hget]
        show some (slotOf entry) = some (some (entry.val - 1))
        rw [slotOf_pos hnz]
      have hbnd := table.property
      step as ⟨idx1, hidx1⟩
      have hidx1v : idx1.val = ix.val + 1 := by scalar_tac
      step with wrap_spec idx1 slots ix.val (places table.val).length hidx1v (by omega)
        as ⟨idx2, hidx2⟩
      step as ⟨st1, hst1⟩
      have hst1v : st1.val = st.val + 1 := by scalar_tac
      refine ⟨?_, by scalar_tac⟩
      show Walking (places table.val) idx0.val idx2.val st1.val
      rw [hst1v]
      refine ⟨by omega, ?_, ?_⟩
      · rw [hidx2, hix]
        rfl
      · intro t' ht'
        by_cases e : t' = st.val
        · rw [e, ← hix]
          exact ⟨_, htaken⟩
        · exact hbusy t' (by omega)
  · simp only [hlt, ↓reduceIte, spec_ok]
    exfalso
    have e : st.val = (places table.val).length := by scalar_tac
    have hh : idx0.val < (places table.val).length := by omega
    have hc : countSome (places table.val) < (places table.val).length := by omega
    rw [e] at hbusy
    exact exists_free_step hh hc hbusy

/-- What `put` makes of the table of a list. -/
structure Put (k0 k1 : Std.U64) (ids : List yata_store.IdCore) (t : List Std.U32) (p : Nat)
    (t' : List Std.U32) : Prop where
  length : t'.length = t.length
  table : Table k0 k1 ids t'
  mem : ∀ z, Mem (places t') z ↔ z = p ∨ Mem (places t) z
  count : countSome (places t') = countSome (places t) + 1

/-- `put` adds the place of an id to a table with a free slot. -/
theorem put_spec (table : Slice Std.U32) (k0 k1 : Std.U64) (ids : List yata_store.IdCore)
    (id : yata_store.IdCore) («at» : Std.Usize) (hid : ids[«at».val]? = some id)
    (hok : Table k0 k1 ids table.val) (hroom : countSome (places table.val) < table.val.length)
    (hat : «at».val + 1 ≤ 4294967295) :
    id_order.put table k0 k1 id «at» ⦃ _b table1 =>
      Put k0 k1 ids table.val «at».val table1.val ⦄ := by
  unfold id_order.put
  simp only
  have hpos : 0 < table.val.length := by omega
  have hlen : (Slice.len table).val = table.val.length := by scalar_tac
  step with start_spec k0 k1 id (Slice.len table) as ⟨idx, hidx⟩
  rw [hlen] at hidx
  have hidxlt : idx.val < table.val.length := by
    rw [hidx]
    exact homeN_lt k0 k1 id hpos
  refine spec_mono (put_loop_spec table «at» (Slice.len table) idx hlen hidxlt hroom hat) ?_
  rintro ⟨b, t1⟩ hp
  have hP : PutPost table.val idx.val «at».val b t1.val := hp
  obtain ⟨i, st, hst, hslot, hbusy, hfree, hset⟩ := hP.set
  have hpl := places_length table.val
  have hhome : homeAt k0 k1 ids table.val.length «at».val = idx.val := by
    rw [homeAt_of hid, hidx]
  show Put k0 k1 ids table.val «at».val t1.val
  refine ⟨hP.length, ?_, ?_, ?_⟩
  · show TableOK (homeAt k0 k1 ids t1.val.length) (places t1.val)
    rw [hP.length, hset]
    refine TableOK.set hok hst ?_ ?_ hfree
    · rw [hhome]
      exact hslot
    · rw [hhome]
      exact hbusy
  · intro z
    rw [hset]
    exact mem_set hfree z
  · rw [hset]
    exact countSome_set «at».val hfree

/-! ## Looking a place up -/

/-- The first `st` slots the walk for `id` looks at hold places of other
ids. -/
def Passed (ids : List yata_store.IdCore) (l : List (Option Nat)) (h : Nat)
    (id : yata_store.IdCore) (st : Nat) : Prop :=
  ∀ t', t' < st → ∃ q, l[slotAt l.length h t']? = some (some q) ∧ ids[q]? ≠ some id

/-- What `seek` ends with: a place of the id, a free slot met after places of
other ids, or a walk around the table over places of other ids. -/
def SeekPost (ids : List yata_store.IdCore) (l : List (Option Nat)) (h : Nat)
    (id : yata_store.IdCore) : Option Std.Usize → Prop
  | some p => ids[p.val]? = some id
  | none => (∃ st, st < l.length ∧ l[slotAt l.length h st]? = some none ∧ Passed ids l h id st) ∨
      Passed ids l h id l.length

/-- The loop of `seek` after `st` steps, at the slot `ix`. -/
structure Seeking (ids : List yata_store.IdCore) (l : List (Option Nat)) (h : Nat)
    (id : yata_store.IdCore) (ix st : Nat) : Prop where
  bound : st ≤ l.length
  slot : ix = slotAt l.length h st
  passed : Passed ids l h id st

theorem seek_loop_spec (table : Slice Std.U32) (ids : Slice yata_store.IdCore)
    (id : yata_store.IdCore) (slots idx0 : Std.Usize) (hslots : slots.val = table.val.length)
    (hidx : table.val.length = 0 ∨ idx0.val < table.val.length) :
    id_order.seek_loop table ids id slots idx0 0#usize ⦃ r =>
      SeekPost ids.val (places table.val) idx0.val id r ⦄ := by
  unfold id_order.seek_loop
  have hpl := places_length table.val
  have hinit : Seeking ids.val (places table.val) idx0.val id idx0.val
      (0#usize : Std.Usize).val := by
    rw [usize_zero_val]
    exact ⟨Nat.zero_le _, rfl, fun t' ht' => absurd ht' (Nat.not_lt_zero _)⟩
  refine loop.spec_decr_nat
    (fun ((_, st) : Std.Usize × Std.Usize) => slots.val - st.val)
    (fun ((ix, st) : Std.Usize × Std.Usize) =>
      Seeking ids.val (places table.val) idx0.val id ix.val st.val)
    (fun (r : Option Std.Usize) => SeekPost ids.val (places table.val) idx0.val id r)
    _ (idx0, 0#usize) ?_ hinit
  intro ⟨ix, st⟩ hS0
  have hS : Seeking ids.val (places table.val) idx0.val id ix.val st.val := hS0
  have hst := hS.bound
  have hix := hS.slot
  have hpassed := hS.passed
  unfold id_order.seek_loop.body
  simp only
  by_cases hlt : st < slots
  · simp only [hlt, ↓reduceIte]
    have hstlt : st.val < table.val.length := by scalar_tac
    have h0 : idx0.val < table.val.length := by
      rcases hidx with h | h
      · omega
      · exact h
    have hixlt : ix.val < table.val.length := by
      rw [hix, hpl]
      exact slotAt_lt h0 _
    step as ⟨entry, hentry⟩
    have hget : table.val[ix.val]? = some entry := get?_of_getElem hixlt hentry
    by_cases hz : entry = 0#u32
    · have hz' : (entry = 0#u32) = True := eq_true hz
      simp only [hz', ↓reduceIte, spec_ok]
      have hfree : (places table.val)[ix.val]? = some none := by
        rw [places_get?, hget, hz]
        show some (slotOf 0#u32) = some none
        rw [slotOf_zero]
      left
      refine ⟨st.val, by omega, ?_, hpassed⟩
      rw [← hix]
      exact hfree
    · simp only [hz, ↓reduceIte]
      have hnz : ¬ entry.val = 0 := by
        intro h0
        apply hz
        apply UScalar.eq_of_val_eq
        rw [h0]
        rfl
      have htaken : (places table.val)[ix.val]? = some (some (entry.val - 1)) := by
        rw [places_get?, hget]
        show some (slotOf entry) = some (some (entry.val - 1))
        rw [slotOf_pos hnz]
      step as ⟨i, hi⟩
      have hiv : i.val = entry.val - 1 := by scalar_tac
      have hcast : i.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.Usize i hcast as ⟨«at», hat⟩
      have hatv : «at».val = entry.val - 1 := by rw [hat, hiv]
      have hbnd := table.property
      -- the walk goes on over a place that is not one of `id`
      have hnext : ∀ (idx2 st1 : Std.Usize), ids.val[«at».val]? ≠ some id →
          idx2.val = nextSlot (places table.val).length ix.val → st1.val = st.val + 1 →
          Seeking ids.val (places table.val) idx0.val id idx2.val st1.val := by
        intro idx2 st1 hne hidx2 hst1v
        rw [hst1v]
        refine ⟨by omega, ?_, ?_⟩
        · rw [hidx2, hix]
          rfl
        · intro t' ht'
          by_cases e : t' = st.val
          · rw [e, ← hix]
            exact ⟨entry.val - 1, htaken, by rw [← hatv]; exact hne⟩
          · exact hpassed t' (by omega)
      by_cases hin : «at» < Slice.len ids
      · simp only [hin, ↓reduceIte]
        have hinv : «at».val < ids.val.length := by scalar_tac
        step as ⟨ic, hic⟩
        have hgid : ids.val[«at».val]? = some ic := get?_of_getElem hinv hic
        step with id_eq_iff ic id as ⟨b, hb⟩
        by_cases hbt : b = true
        · simp only [hbt, ↓reduceIte, spec_ok]
          show ids.val[«at».val]? = some id
          rw [hgid, hb.mp hbt]
        · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
          have hne : ids.val[«at».val]? ≠ some id := by
            rw [hgid]
            intro e
            exact hbt (hb.mpr (Option.some.inj e))
          step as ⟨idx1, hidx1⟩
          have hidx1v : idx1.val = ix.val + 1 := by scalar_tac
          step with wrap_spec idx1 slots ix.val (places table.val).length hidx1v (by omega)
            as ⟨idx2, hidx2⟩
          step as ⟨st1, hst1⟩
          have hst1v : st1.val = st.val + 1 := by scalar_tac
          exact ⟨hnext idx2 st1 hne hidx2 hst1v, by scalar_tac⟩
      · simp only [hin, ↓reduceIte]
        have hout : ids.val.length ≤ «at».val := by scalar_tac
        have hne : ids.val[«at».val]? ≠ some id := by
          rw [get?_none hout]
          intro e
          cases e
        step as ⟨idx1, hidx1⟩
        have hidx1v : idx1.val = ix.val + 1 := by scalar_tac
        step with wrap_spec idx1 slots ix.val (places table.val).length hidx1v (by omega)
          as ⟨idx2, hidx2⟩
        step as ⟨st1, hst1⟩
        have hst1v : st1.val = st.val + 1 := by scalar_tac
        exact ⟨hnext idx2 st1 hne hidx2 hst1v, by scalar_tac⟩
  · simp only [hlt, ↓reduceIte, spec_ok]
    have e : st.val = (places table.val).length := by scalar_tac
    right
    show Passed ids.val (places table.val) idx0.val id (places table.val).length
    rw [← e]
    exact hpassed

/-- `seek` walks from the home slot of the id. -/
theorem seek_spec (table : Slice Std.U32) (ids : Slice yata_store.IdCore) (k0 k1 : Std.U64)
    (id : yata_store.IdCore) :
    id_order.seek table ids k0 k1 id ⦃ r =>
      SeekPost ids.val (places table.val) (homeN k0 k1 id table.val.length) id r ⦄ := by
  unfold id_order.seek
  simp only
  have hlen : (Slice.len table).val = table.val.length := by scalar_tac
  step with start_spec k0 k1 id (Slice.len table) as ⟨idx, hidx⟩
  rw [hlen] at hidx
  rw [← hidx]
  refine seek_loop_spec table ids id (Slice.len table) idx hlen ?_
  by_cases hz : table.val.length = 0
  · exact Or.inl hz
  · right
    rw [hidx]
    exact homeN_lt k0 k1 id (by omega)

/-- A walk that did not meet the id has shown that no place of the table is
one of the id. -/
theorem absent_of_seek {k0 k1 : Std.U64} {ids : List yata_store.IdCore} {t : List Std.U32}
    {id : yata_store.IdCore} (hok : Table k0 k1 ids t)
    (hpost : SeekPost ids (places t) (homeN k0 k1 id t.length) id none) :
    ∀ p, Mem (places t) p → ids[p]? ≠ some id := by
  intro p hm hp
  have hh : homeAt k0 k1 ids t.length p = homeN k0 k1 id t.length := homeAt_of hp
  rcases hpost with ⟨st, _, hfree, hpassed⟩ | hpassed
  · refine not_mem_of_free (home := homeAt k0 k1 ids t.length) (x := p) (t := st) hok ?_ ?_ hm
    · intro t' ht'
      rw [hh]
      obtain ⟨q, hq, hne⟩ := hpassed t' ht'
      refine ⟨q, hq, fun e => hne ?_⟩
      rw [e]
      exact hp
    · rw [hh]
      exact hfree
  · refine not_mem_of_full (home := homeAt k0 k1 ids t.length) (x := p) hok ?_ hm
    intro t' ht'
    rw [hh]
    obtain ⟨q, hq, hne⟩ := hpassed t' ht'
    refine ⟨q, hq, fun e => hne ?_⟩
    rw [e]
    exact hp

/-! ## Lists -/

/-- The invariant of a list. -/
structure WF (s : id_order.IdOrderCore) : Prop where
  /-- no more than `2 ^ 30` ids -/
  ids : s.ids.val.length ≤ 1073741824
  /-- the table holds places of the first ids -/
  indexed : s.indexed.val ≤ s.ids.val.length
  /-- at most half of the slots are taken -/
  load : s.indexed.val * 2 ≤ s.table.val.length
  /-- every place is reached from the home slot of its id under the key -/
  table : Table s.k0 s.k1 s.ids.val s.table.val
  /-- the table holds no place past the first `indexed` ones -/
  below : ∀ p, Mem (places s.table.val) p → p < s.indexed.val
  /-- and every one of these -/
  has : ∀ p, p < s.indexed.val → Mem (places s.table.val) p
  /-- one slot each -/
  count : countSome (places s.table.val) ≤ s.indexed.val

/-- The place `p` of the list holds `id`. -/
def At (s : id_order.IdOrderCore) (p : Nat) (id : yata_store.IdCore) : Prop :=
  s.ids.val[p]? = some id

/-- **`with_key` makes the empty list of a key**: no id, no table, and the
hash under the key it was given. -/
theorem with_key_spec (k0 k1 : Std.U64) :
    id_order.IdOrderCore.with_key k0 k1 ⦃ s =>
      WF s ∧ s.ids.val = [] ∧ s.indexed.val = 0 ∧ s.k0 = k0 ∧ s.k1 = k1 ⦄ := by
  unfold id_order.IdOrderCore.with_key
  have hv : ∀ α : Type, (alloc.vec.Vec.new α).val = [] := by
    intro α
    simp
  refine (spec_ok _).mpr ⟨⟨?_, ?_, ?_, ?_, fun p hm => ?_, fun p hp => ?_, ?_⟩, hv _, usize_zero_val,
    rfl, rfl⟩
  · show (alloc.vec.Vec.new yata_store.IdCore).val.length ≤ 1073741824
    rw [hv]
    exact Nat.zero_le _
  · show (0#usize : Std.Usize).val ≤ (alloc.vec.Vec.new yata_store.IdCore).val.length
    rw [usize_zero_val]
    exact Nat.zero_le _
  · show (0#usize : Std.Usize).val * 2 ≤ (alloc.vec.Vec.new Std.U32).val.length
    rw [usize_zero_val]
    exact Nat.zero_le _
  · show Table k0 k1 (alloc.vec.Vec.new yata_store.IdCore).val (alloc.vec.Vec.new Std.U32).val
    rw [hv Std.U32]
    exact table_replicate _ _ _ 0
  · have hm' : Mem (places (alloc.vec.Vec.new Std.U32).val) p := hm
    rw [hv] at hm'
    cases hm'
  · have hp' : p < (0#usize : Std.Usize).val := hp
    rw [usize_zero_val] at hp'
    exact absurd hp' (Nat.not_lt_zero _)
  · show countSome (places (alloc.vec.Vec.new Std.U32).val) ≤ (0#usize : Std.Usize).val
    rw [hv]
    exact Nat.le_refl _

/-- **`new` makes the empty list**: the one of the key `(0, 0)`. -/
theorem new_spec :
    id_order.IdOrderCore.new ⦃ s => WF s ∧ s.ids.val = [] ∧ s.indexed.val = 0 ⦄ := by
  unfold id_order.IdOrderCore.new
  exact spec_mono (with_key_spec 0#u64 0#u64) (fun s hs => ⟨hs.1, hs.2.1, hs.2.2.1⟩)

@[step]
theorem len_spec (s : id_order.IdOrderCore) :
    id_order.IdOrderCore.len s ⦃ n => n.val = s.ids.val.length ⦄ := by
  unfold id_order.IdOrderCore.len
  simp only [spec_ok]
  scalar_tac

@[step]
theorem is_empty_spec (s : id_order.IdOrderCore) :
    id_order.IdOrderCore.is_empty s ⦃ b => (b = true ↔ s.ids.val = []) ⦄ := by
  unfold id_order.IdOrderCore.is_empty
  simp only [spec_ok, decide_eq_true_eq]
  have hlen : (alloc.vec.Vec.len s.ids).val = s.ids.val.length := by scalar_tac
  constructor
  · intro e
    have h0 : s.ids.val.length = 0 := by
      rw [← hlen, e]
      rfl
    exact List.eq_nil_of_length_eq_zero h0
  · intro e
    apply UScalar.eq_of_val_eq
    rw [hlen, e]
    rfl

@[step]
theorem is_indexed_spec (s : id_order.IdOrderCore) :
    id_order.IdOrderCore.is_indexed s ⦃ b => (b = true ↔ 0 < s.indexed.val) ⦄ := by
  unfold id_order.IdOrderCore.is_indexed
  simp only [spec_ok, decide_eq_true_eq]
  constructor
  · intro h
    scalar_tac
  · intro h
    scalar_tac

/-- What `push` does, by its answer. -/
structure PushPost (s : id_order.IdOrderCore) (id : yata_store.IdCore) (b : Bool)
    (s' : id_order.IdOrderCore) : Prop where
  wf : WF s'
  /-- it accepted: the id is the last one, after the ones that were -/
  added : b = true → s'.ids.val = s.ids.val ++ [id]
  /-- it refused: the list is as it was -/
  refused : b = false → s' = s
  /-- it accepts while the list holds fewer than `2 ^ 30` ids -/
  accepts : s.ids.val.length < 1073741824 → b = true
  /-- the table and the key stay -/
  table : s'.table = s.table ∧ s'.indexed = s.indexed ∧ s'.k0 = s.k0 ∧ s'.k1 = s.k1

/-- **`push` puts the id at the end of the list**, or refuses and changes
nothing. -/
theorem push_spec (s : id_order.IdOrderCore) (id : yata_store.IdCore) (h : WF s) :
    id_order.IdOrderCore.push s id ⦃ b s' => PushPost s id b s' ⦄ := by
  unfold id_order.IdOrderCore.push
  simp only
  have hmax : (id_order.MAX_IDS).val = 1073741824 := by simp [id_order.MAX_IDS]
  by_cases hfull : alloc.vec.Vec.len s.ids >= id_order.MAX_IDS
  · simp only [hfull, ↓reduceIte, spec_ok, uncurry'_pair]
    have hge : 1073741824 ≤ s.ids.val.length := by scalar_tac
    exact ⟨h, (fun e => nomatch e), fun _ => rfl, fun hlt => by omega, ⟨rfl, rfl, rfl, rfl⟩⟩
  · simp only [hfull, ↓reduceIte]
    have hlt : s.ids.val.length < 1073741824 := by scalar_tac
    have hu32 : 4294967295 ≤ Std.Usize.max := by scalar_tac
    have hroom : s.ids.val.length < Std.Usize.max := by omega
    step as ⟨v, hv⟩
    have hvv : v.val = s.ids.val ++ [id] := hv
    have hsame : ∀ p, p < s.ids.val.length → v.val[p]? = s.ids.val[p]? := by
      intro p hp
      rw [hvv, get?_append_left hp]
    refine ⟨⟨?_, ?_, h.load, ?_, h.below, h.has, h.count⟩, fun _ => hvv, (fun e => nomatch e),
      fun _ => rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
    · show v.val.length ≤ 1073741824
      rw [hvv, List.length_append, List.length_singleton]
      omega
    · show s.indexed.val ≤ v.val.length
      rw [hvv, List.length_append, List.length_singleton]
      have := h.indexed
      omega
    · show TableOK (homeAt s.k0 s.k1 v.val s.table.val.length) (places s.table.val)
      refine tableOK_congr h.table (fun p hm => ?_)
      have hp : p < s.ids.val.length := by
        have h1 := h.below p hm
        have h2 := h.indexed
        omega
      unfold homeAt
      rw [hsame p hp]

/-- What `key` does. -/
structure KeyPost (s : id_order.IdOrderCore) (k0 k1 : Std.U64) (s' : id_order.IdOrderCore) :
    Prop where
  wf : WF s'
  /-- the ids, the table and what it holds stay -/
  same : s'.ids = s.ids ∧ s'.table = s.table ∧ s'.indexed = s.indexed
  /-- a table without an id takes the key -/
  taken : s.indexed.val = 0 → s'.k0 = k0 ∧ s'.k1 = k1
  /-- any other keeps its own -/
  kept : 0 < s.indexed.val → s' = s

/-- **`key` gives the hash a key while the table holds no id.** -/
theorem key_spec (s : id_order.IdOrderCore) (k0 k1 : Std.U64) (h : WF s) :
    id_order.IdOrderCore.key s k0 k1 ⦃ s' => KeyPost s k0 k1 s' ⦄ := by
  unfold id_order.IdOrderCore.key
  by_cases hz : s.indexed = 0#usize
  · have hz' : (s.indexed = 0#usize) = True := eq_true hz
    simp only [hz', ↓reduceIte, spec_ok]
    have h0 : s.indexed.val = 0 := by
      rw [hz]
      exact usize_zero_val
    refine ⟨⟨h.ids, h.indexed, h.load, ?_, h.below, h.has, h.count⟩, ⟨rfl, rfl, rfl⟩,
      fun _ => ⟨rfl, rfl⟩, fun hpos => by omega⟩
    -- no place is in the table: no home slot is asked for
    show TableOK (homeAt k0 k1 s.ids.val s.table.val.length) (places s.table.val)
    refine tableOK_congr h.table (fun p hm => ?_)
    have := h.below p hm
    omega
  · simp only [hz, ↓reduceIte, spec_ok]
    refine ⟨h, ⟨rfl, rfl, rfl⟩, fun h0 => ?_, fun _ => rfl⟩
    exfalso
    apply hz
    apply UScalar.eq_of_val_eq
    rw [h0, usize_zero_val]

/-! ## Looking through the last ids -/

/-- The loop of `window` at the place `a`, after `l` ids. -/
structure Looking (ids : List yata_store.IdCore) (id : yata_store.IdCore) (a l : Nat) :
    Prop where
  sum : a + l = ids.length
  looked : l ≤ 16
  other : ∀ j : Nat, a ≤ j → ids[j]? ≠ some id

/-- What `recent` answers. -/
def RecentPost (ids : List yata_store.IdCore) (id : yata_store.IdCore) : id_order.Recent → Prop
  | .At p => ids[p.val]? = some id
  | .Absent => ∀ j : Nat, ids[j]? ≠ some id
  | .Far => 16 < ids.length ∧ ∀ j : Nat, ids.length - 16 ≤ j → ids[j]? ≠ some id

theorem window_loop_spec (v : alloc.vec.Vec yata_store.IdCore) (id : yata_store.IdCore)
    (at0 looked0 : Std.Usize) (hinv : Looking v.val id at0.val looked0.val) :
    id_order.IdOrderCore.window_loop v id at0 looked0 ⦃ r => RecentPost v.val id r ⦄ := by
  unfold id_order.IdOrderCore.window_loop
  refine loop.spec_decr_nat
    (fun ((a, _) : Std.Usize × Std.Usize) => a.val)
    (fun ((a, l) : Std.Usize × Std.Usize) => Looking v.val id a.val l.val)
    (fun (r : id_order.Recent) => RecentPost v.val id r)
    _ (at0, looked0) ?_ hinv
  intro ⟨a, l⟩ hinv0
  have hI : Looking v.val id a.val l.val := hinv0
  have hsum := hI.sum
  have hlooked := hI.looked
  have hrecent : (id_order.RECENT).val = 16 := by simp [id_order.RECENT]
  unfold id_order.IdOrderCore.window_loop.body
  simp only
  by_cases hpos : a > 0#usize
  · simp only [hpos, ↓reduceIte]
    have hposv : 0 < a.val := by scalar_tac
    have hanz : ¬ a = 0#usize := by
      intro e
      rw [e, usize_zero_val] at hposv
      exact absurd hposv (Nat.lt_irrefl 0)
    by_cases hmore : l < id_order.RECENT
    · simp only [hmore, ↓reduceIte]
      have hlv : l.val < 16 := by scalar_tac
      step as ⟨a1, ha1⟩
      have ha1v : a1.val = a.val - 1 := by scalar_tac
      have ha1lt : a1.val < v.val.length := by omega
      step as ⟨ic, hic⟩
      have hgid : v.val[a1.val]? = some ic := get?_of_getElem ha1lt hic
      step with id_eq_iff ic id as ⟨b, hb⟩
      by_cases hbt : b = true
      · simp only [hbt, ↓reduceIte, spec_ok]
        show v.val[a1.val]? = some id
        rw [hgid, hb.mp hbt]
      · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
        have hne : v.val[a1.val]? ≠ some id := by
          rw [hgid]
          intro e
          exact hbt (hb.mpr (Option.some.inj e))
        step as ⟨l1, hl1⟩
        have hl1v : l1.val = l.val + 1 := by scalar_tac
        refine ⟨?_, by scalar_tac⟩
        show Looking v.val id a1.val l1.val
        refine ⟨by omega, by omega, fun j hj => ?_⟩
        by_cases e : j = a1.val
        · rw [e]
          exact hne
        · exact hI.other j (by omega)
    · simp only [hmore, hanz, ↓reduceIte, spec_ok]
      have hlv : 16 ≤ l.val := by scalar_tac
      show 16 < v.val.length ∧ ∀ j : Nat, v.val.length - 16 ≤ j → v.val[j]? ≠ some id
      exact ⟨by omega, fun j hj => hI.other j (by omega)⟩
  · have hzv : a.val = 0 := by scalar_tac
    have hz : a = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [hzv, usize_zero_val]
    have hz' : (a = 0#usize) = True := eq_true hz
    simp only [hpos, hz', ↓reduceIte, spec_ok]
    show ∀ j : Nat, v.val[j]? ≠ some id
    exact fun j => hI.other j (by omega)

/-- `window` looks through the last sixteen ids. -/
theorem window_spec (s : id_order.IdOrderCore) (id : yata_store.IdCore) :
    id_order.IdOrderCore.window s id ⦃ r => RecentPost s.ids.val id r ⦄ := by
  unfold id_order.IdOrderCore.window
  simp only
  refine window_loop_spec s.ids id (alloc.vec.Vec.len s.ids) 0#usize ?_
  have hlen : (alloc.vec.Vec.len s.ids).val = s.ids.val.length := by scalar_tac
  rw [usize_zero_val, hlen]
  refine ⟨Nat.add_zero _, Nat.zero_le _, fun j hj => ?_⟩
  rw [get?_none hj]
  intro e
  cases e

/-- `look` looks at the place answered last, if the list has it, and then
through the last sixteen ids. -/
theorem look_spec (s : id_order.IdOrderCore) (id : yata_store.IdCore) :
    id_order.IdOrderCore.look s id ⦃ r => RecentPost s.ids.val id r ⦄ := by
  unfold id_order.IdOrderCore.look
  simp only
  by_cases hlt : s.last < alloc.vec.Vec.len s.ids
  · simp only [hlt, ↓reduceIte]
    have hl : s.last.val < s.ids.val.length := by scalar_tac
    step as ⟨ic, hic⟩
    have hgid : s.ids.val[s.last.val]? = some ic := get?_of_getElem hl hic
    step with id_eq_iff ic id as ⟨b, hb⟩
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte, spec_ok]
      show s.ids.val[s.last.val]? = some id
      rw [hgid, hb.mp hbt]
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
      exact window_spec s id
  · simp only [hlt, ↓reduceIte]
    exact window_spec s id

/-- Two lists that differ in the place answered last at most. -/
structure Same (s s' : id_order.IdOrderCore) : Prop where
  ids : s'.ids = s.ids
  table : s'.table = s.table
  indexed : s'.indexed = s.indexed
  key : s'.k0 = s.k0 ∧ s'.k1 = s.k1

/-- The place answered last is no part of the invariant: whatever it is,
`look` reads it only when the list has such a place. -/
theorem WF.same {s s' : id_order.IdOrderCore} (h : WF s) (e : Same s s') : WF s' := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]
    exact h.ids
  · rw [e3, e1]
    exact h.indexed
  · rw [e3, e2]
    exact h.load
  · rw [e4, e5, e1, e2]
    exact h.table
  · rw [e2, e3]
    exact h.below
  · rw [e3, e2]
    exact h.has
  · rw [e2, e3]
    exact h.count

/-- **`recent` looks at the place answered last and through the last sixteen
ids**: the place it answers holds the id, `Absent` is a list without the id,
and `Far` says that none of the last sixteen ids is the id and that the list
holds more. It changes nothing of the list but the place it will look at
first the next time. -/
theorem recent_spec (s : id_order.IdOrderCore) (id : yata_store.IdCore) :
    id_order.IdOrderCore.recent s id ⦃ r s' => RecentPost s.ids.val id r ∧ Same s s' ⦄ := by
  unfold id_order.IdOrderCore.recent
  step with look_spec s id as ⟨found, hfound⟩
  cases found with
  | At a =>
    simp only [spec_ok, uncurry'_pair]
    exact ⟨hfound, ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩⟩⟩
  | Absent =>
    simp only [spec_ok, uncurry'_pair]
    exact ⟨hfound, ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩⟩⟩
  | Far =>
    simp only [spec_ok, uncurry'_pair]
    exact ⟨hfound, ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩⟩⟩

/-! ## Bringing the table up to the list -/

/-- What `fit` does: a table the ids fill no more than half of. -/
structure FitPost (s s' : id_order.IdOrderCore) : Prop where
  wf : WF s'
  same : s'.ids = s.ids ∧ s'.k0 = s.k0 ∧ s'.k1 = s.k1
  room : s.ids.val.length * 2 ≤ s'.table.val.length

theorem fit_spec (s : id_order.IdOrderCore) (h : WF s) :
    id_order.IdOrderCore.fit s ⦃ s' => FitPost s s' ⦄ := by
  unfold id_order.IdOrderCore.fit
  simp only
  have hlen : (alloc.vec.Vec.len s.ids).val = s.ids.val.length := by scalar_tac
  step as ⟨half, hhalf⟩
  have hhalfv : half.val = s.table.val.length / 2 := by scalar_tac
  by_cases hsmall : half < alloc.vec.Vec.len s.ids
  · simp only [hsmall, ↓reduceIte]
    have hcount : (alloc.vec.Vec.len s.ids).val ≤ 1073741824 := by
      rw [hlen]
      exact h.ids
    step with slots_for_spec (alloc.vec.Vec.len s.ids) hcount as ⟨n, hn0, hn⟩
    step with alloc.vec.from_elem_spec core.clone.CloneU32 0#u32 n rfl as ⟨fresh, hfresh, _⟩
    rw [hlen] at hn
    refine ⟨⟨h.ids, ?_, ?_, ?_, fun p hm => ?_, fun p hp => ?_, ?_⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
    · show (0#usize : Std.Usize).val ≤ s.ids.val.length
      rw [usize_zero_val]
      exact Nat.zero_le _
    · show (0#usize : Std.Usize).val * 2 ≤ fresh.val.length
      rw [usize_zero_val]
      exact Nat.zero_le _
    · show Table s.k0 s.k1 s.ids.val fresh.val
      rw [hfresh]
      exact table_replicate _ _ _ _
    · have hm' : Mem (places fresh.val) p := hm
      rw [hfresh] at hm'
      exact absurd hm' (not_mem_places_replicate _ p)
    · have hp' : p < (0#usize : Std.Usize).val := hp
      rw [usize_zero_val] at hp'
      exact absurd hp' (Nat.not_lt_zero _)
    · show countSome (places fresh.val) ≤ (0#usize : Std.Usize).val
      rw [hfresh, places_replicate, countSome_replicate]
      exact Nat.zero_le _
    · show s.ids.val.length * 2 ≤ fresh.val.length
      rw [hfresh, List.length_replicate]
      exact hn
  · simp only [hsmall, ↓reduceIte, spec_ok]
    have hge : s.ids.val.length ≤ s.table.val.length / 2 := by scalar_tac
    exact ⟨h, ⟨rfl, rfl, rfl⟩, by omega⟩

/-- The loop of `index`, when the table holds the first `a` places. -/
structure Indexing (k0 k1 : Std.U64) (ids : List yata_store.IdCore) (cap : Nat)
    (t : List Std.U32) (a : Nat) : Prop where
  length : t.length = cap
  table : Table k0 k1 ids t
  below : ∀ p, Mem (places t) p → p < a
  has : ∀ p, p < a → Mem (places t) p
  count : countSome (places t) ≤ a

/-- The invariant of the loop of `index`: it does not pass the end of the
list when it starts before it. -/
structure IndexingTo (k0 k1 : Std.U64) (ids : List yata_store.IdCore) (cap : Nat)
    (at0 count : Nat) (t : List Std.U32) (a : Nat) : Prop where
  inv : Indexing k0 k1 ids cap t a
  le : at0 ≤ count → a ≤ count

theorem index_loop_spec (v : alloc.vec.Vec yata_store.IdCore) (v1 : alloc.vec.Vec Std.U32)
    (k0 k1 : Std.U64) (count at0 : Std.Usize) (cap : Nat) (hcount : count.val = v.val.length)
    (hcap : count.val * 2 ≤ cap) (hmax : count.val ≤ 1073741824)
    (hinv : Indexing k0 k1 v.val cap v1.val at0.val) :
    id_order.IdOrderCore.index_loop v v1 k0 k1 count at0 ⦃ r =>
      ∃ a, Indexing k0 k1 v.val cap r.val a ∧ count.val ≤ a ∧ (at0.val ≤ count.val → a = count.val) ⦄ := by
  unfold id_order.IdOrderCore.index_loop
  refine loop.spec_decr_nat
    (fun ((_, a) : alloc.vec.Vec Std.U32 × Std.Usize) => count.val - a.val)
    (fun ((t, a) : alloc.vec.Vec Std.U32 × Std.Usize) =>
      IndexingTo k0 k1 v.val cap at0.val count.val t.val a.val)
    (fun (r : alloc.vec.Vec Std.U32) =>
      ∃ a, Indexing k0 k1 v.val cap r.val a ∧ count.val ≤ a ∧ (at0.val ≤ count.val → a = count.val))
    _ (v1, at0) ?_ ⟨hinv, fun h => h⟩
  intro ⟨t, a⟩ hinv0
  have hT : IndexingTo k0 k1 v.val cap at0.val count.val t.val a.val := hinv0
  have hI : Indexing k0 k1 v.val cap t.val a.val := hT.inv
  have hle : at0.val ≤ count.val → a.val ≤ count.val := hT.le
  unfold id_order.IdOrderCore.index_loop.body
  simp only
  by_cases hlt : a < count
  · simp only [hlt, ↓reduceIte]
    have hav : a.val < count.val := by scalar_tac
    have hal : a.val < v.val.length := by omega
    simp only [lift, alloc.vec.Vec.deref_mut]
    step as ⟨ic, hic⟩
    have hgid : v.val[a.val]? = some ic := get?_of_getElem hal hic
    have hroom : countSome (places t.slice.val) < t.slice.val.length := by
      show countSome (places t.val) < t.val.length
      have h1 := hI.count
      have h2 := hI.length
      omega
    have hat : a.val + 1 ≤ 4294967295 := by omega
    step with put_spec t.slice k0 k1 v.val ic a hgid hI.table hroom hat as ⟨_b, s1, hp⟩
    have hP : Put k0 k1 v.val t.val a.val s1.val := hp
    step as ⟨a1, ha1⟩
    have ha1v : a1.val = a.val + 1 := by scalar_tac
    refine ⟨?_, by scalar_tac⟩
    show IndexingTo k0 k1 v.val cap at0.val count.val s1.val a1.val
    refine ⟨?_, fun _ => by omega⟩
    show Indexing k0 k1 v.val cap s1.val a1.val
    rw [ha1v]
    refine ⟨by rw [hP.length]; exact hI.length, hP.table, fun p hm => ?_, fun p hp => ?_, ?_⟩
    · rcases (hP.mem p).mp hm with e | hm'
      · omega
      · have := hI.below p hm'
        omega
    · by_cases e : p = a.val
      · exact (hP.mem p).mpr (Or.inl e)
      · exact (hP.mem p).mpr (Or.inr (hI.has p (by omega)))
    · rw [hP.count]
      have := hI.count
      omega
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : count.val ≤ a.val := by scalar_tac
    exact ⟨a.val, hI, hge, fun h0 => by have := hle h0; omega⟩

/-- What `index` does: the table holds every place of the list. -/
structure IndexPost (s s' : id_order.IdOrderCore) : Prop where
  wf : WF s'
  same : s'.ids = s.ids ∧ s'.k0 = s.k0 ∧ s'.k1 = s.k1
  all : s'.indexed.val = s.ids.val.length

theorem index_spec (s : id_order.IdOrderCore) (h : WF s) :
    id_order.IdOrderCore.index s ⦃ s' => IndexPost s s' ⦄ := by
  unfold id_order.IdOrderCore.index
  step with fit_spec s h as ⟨s1, hfit⟩
  have hF : FitPost s s1 := hfit
  have hw := hF.wf
  obtain ⟨hids, hk0, hk1⟩ := hF.same
  have hlen : (alloc.vec.Vec.len s1.ids).val = s1.ids.val.length := by scalar_tac
  have hroom : (alloc.vec.Vec.len s1.ids).val * 2 ≤ s1.table.val.length := by
    rw [hlen, hids]
    exact hF.room
  have hmax : (alloc.vec.Vec.len s1.ids).val ≤ 1073741824 := by
    rw [hlen]
    exact hw.ids
  have hinit : Indexing s1.k0 s1.k1 s1.ids.val s1.table.val.length s1.table.val s1.indexed.val :=
    ⟨rfl, hw.table, hw.below, hw.has, hw.count⟩
  step with index_loop_spec s1.ids s1.table s1.k0 s1.k1 (alloc.vec.Vec.len s1.ids) s1.indexed
    s1.table.val.length hlen hroom hmax hinit as ⟨v1, a, hI, _, ha⟩
  have hae : a = s1.ids.val.length := by
    rw [← hlen]
    apply ha
    rw [hlen]
    exact hw.indexed
  rw [hae] at hI
  refine ⟨⟨hw.ids, ?_, ?_, hI.table, ?_, ?_, ?_⟩, ⟨hids, hk0, hk1⟩, ?_⟩
  · show (alloc.vec.Vec.len s1.ids).val ≤ s1.ids.val.length
    exact Nat.le_of_eq hlen
  · show (alloc.vec.Vec.len s1.ids).val * 2 ≤ v1.val.length
    rw [hI.length]
    exact hroom
  · show ∀ p, Mem (places v1.val) p → p < (alloc.vec.Vec.len s1.ids).val
    rw [hlen]
    exact hI.below
  · show ∀ p, p < (alloc.vec.Vec.len s1.ids).val → Mem (places v1.val) p
    rw [hlen]
    exact hI.has
  · show countSome (places v1.val) ≤ (alloc.vec.Vec.len s1.ids).val
    rw [hlen]
    exact hI.count
  · show (alloc.vec.Vec.len s1.ids).val = s.ids.val.length
    rw [hlen, hids]

/-- What `position` answers, and what it leaves. -/
structure PositionPost (s : id_order.IdOrderCore) (id : yata_store.IdCore)
    (r : Option Std.Usize) (s' : id_order.IdOrderCore) : Prop where
  wf : WF s'
  /-- the ids and the key stay -/
  same : s'.ids = s.ids ∧ s'.k0 = s.k0 ∧ s'.k1 = s.k1
  /-- the table holds every place -/
  all : s'.indexed.val = s.ids.val.length
  /-- a place it answers holds the id -/
  found : ∀ p, r = some p → At s p.val id
  /-- and without an answer no place does -/
  absent : r = none → ∀ p, ¬ At s p id

/-- **`position` answers a place of the id**, and `none` only for an id the
list does not hold. -/
theorem position_spec (s : id_order.IdOrderCore) (id : yata_store.IdCore) (h : WF s) :
    id_order.IdOrderCore.position s id ⦃ r s' => PositionPost s id r s' ⦄ := by
  unfold id_order.IdOrderCore.position
  step with index_spec s h as ⟨s1, hindex⟩
  have hX : IndexPost s s1 := hindex
  have hw := hX.wf
  obtain ⟨hids, hk0, hk1⟩ := hX.same
  have hdt : (alloc.vec.Vec.deref s1.table).val = s1.table.val := by
    simp [alloc.vec.Vec.deref]
  have hdi : (alloc.vec.Vec.deref s1.ids).val = s1.ids.val := by
    simp [alloc.vec.Vec.deref]
  step with seek_spec (alloc.vec.Vec.deref s1.table) (alloc.vec.Vec.deref s1.ids) s1.k0 s1.k1 id
    as ⟨o, ho⟩
  rw [hdt, hdi] at ho
  cases o with
  | none =>
    simp only [spec_ok, uncurry'_pair]
    refine ⟨hw, ⟨hids, hk0, hk1⟩, hX.all, (fun p e => nomatch e), fun _ p hp => ?_⟩
    have hat : s1.ids.val[p]? = some id := by
      rw [hids]
      exact hp
    have hplt : p < s1.indexed.val := by
      rw [hX.all, ← hids]
      exact get?_lt hat
    exact absent_of_seek hw.table ho p (hw.has p hplt) hat
  | some a =>
    simp only [spec_ok, uncurry'_pair]
    refine ⟨hw.same ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩⟩, ⟨hids, hk0, hk1⟩, hX.all, fun p e => ?_,
      (fun e => nomatch e)⟩
    have ho' : s1.ids.val[a.val]? = some id := ho
    have ep : a = p := Option.some.inj e
    unfold At
    rw [← ep, ← hids]
    exact ho'

end YoctoCore.Properties.IdOrder
