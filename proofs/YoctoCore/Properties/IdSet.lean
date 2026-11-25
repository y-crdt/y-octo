/-
`y_octo_core::id_set`: the set of ids of the conflict scan, an open addressing
table with linear probing (`IdSetModel`).

`WF` is the invariant of a set: its table is empty or a power of two of
slots, at most half of them taken, `len` counts the taken ones, and every id
is reached from its home slot without meeting a free slot. Every function is
total on every set that satisfies `WF` and keeps it; `contains` answers
whether the id is in the table (`contains_spec`), and `insert` either adds
the id (`Mem s' z ↔ z = id ∨ Mem s z`) or, when the table cannot grow, leaves
the set as it was (`insert_spec`). It accepts while the set holds fewer than
`2 ^ 30` ids. `clear` empties the set and keeps its key (`clear_spec`).

The hash is keyed: a set is made with two words (`with_key_spec`; `new` is
the set of the key `(0, 0)`), and they are part of where an id is at home.
The hash only chooses the home slot: that it is a slot of the table is all
the proofs use (`homeN_lt`), for every key. That ids are spread well, and
that a peer cannot choose ids that are not, is no theorem here.
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.ListAux
import YoctoCore.Properties.IdSetModel

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties.ListAux YoctoCore.Properties.IdSetModel

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace YoctoCore.Properties.IdSet

/-- A call that meets a specification returned. -/
theorem exists_ok {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : ∃ x, m = ok x ∧ P x := by
  cases m with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact ((spec_vis i k).mp h).elim
  | div => exact (spec_div.mp h).elim

theorem get?_of_getElem {α : Type} {l : List α} {i : Nat} {x : α} (h : i < l.length)
    (hx : x = l[i]) : l[i]? = some x := by
  rw [hx]
  exact List.getElem?_eq_getElem h

theorem usize_zero_val : (0#usize : Std.Usize).val = 0 := rfl

/-! ## The hash and the home slot -/

/-- `fold` never fails. -/
@[step]
theorem fold_total (a b : Std.U64) : id_set.fold a b ⦃ _ => True ⦄ := by
  unfold id_set.fold
  step*

/-- `hash_id` never fails, whatever the key. -/
theorem hash_id_total (k0 k1 : Std.U64) (id : yata_store.IdCore) :
    id_set.hash_id k0 k1 id ⦃ _ => True ⦄ := by
  unfold id_set.hash_id
  step*

/-- The hash of an id under the key `(k0, k1)`: what `hash_id` answers. -/
noncomputable def hashU (k0 k1 : Std.U64) (id : yata_store.IdCore) : Std.U64 :=
  Classical.choose (exists_ok (hash_id_total k0 k1 id))

theorem hash_id_eq (k0 k1 : Std.U64) (id : yata_store.IdCore) :
    id_set.hash_id k0 k1 id = ok (hashU k0 k1 id) :=
  (Classical.choose_spec (exists_ok (hash_id_total k0 k1 id))).1

theorem hash_id_spec (k0 k1 : Std.U64) (id : yata_store.IdCore) :
    id_set.hash_id k0 k1 id ⦃ h => h = hashU k0 k1 id ⦄ := by
  rw [hash_id_eq k0 k1 id]
  exact (spec_ok _).mpr rfl

/-- The home slot of an id in a table of `cap` slots: its hash under the key,
masked. -/
noncomputable def homeN (k0 k1 : Std.U64) (id : yata_store.IdCore) (cap : Nat) : Nat :=
  (UScalar.cast .Usize (hashU k0 k1 id)).val &&& (cap - 1)

theorem homeN_lt (k0 k1 : Std.U64) (id : yata_store.IdCore) {cap : Nat} (h : 0 < cap) :
    homeN k0 k1 id cap < cap := by
  unfold homeN
  have := @Nat.and_le_right (UScalar.cast .Usize (hashU k0 k1 id)).val (cap - 1)
  omega

theorem homeN_zero (k0 k1 : Std.U64) (id : yata_store.IdCore) : homeN k0 k1 id 0 = 0 := by
  unfold homeN
  simp

theorem home_spec (k0 k1 : Std.U64) (id : yata_store.IdCore) (slots : Std.Usize)
    (hs : 0 < slots.val) :
    id_set.home k0 k1 id slots ⦃ i => i.val = homeN k0 k1 id slots.val ⦄ := by
  unfold id_set.home
  step with hash_id_spec k0 k1 id as ⟨hsh, hh⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = slots.val - 1 := by scalar_tac
  have hv : (i1 &&& i2).val = i1.val &&& i2.val := BitVec.toNat_and i1.bv i2.bv
  unfold homeN
  rw [hv, hi2v, hi1, hh]

/-! ## A table of free slots -/

/-- The loop of `free_table` after `k` slots. -/
structure Filling (slots : Nat) (t : List (Option yata_store.IdCore)) (k : Nat) : Prop where
  bound : k ≤ slots
  free : t = List.replicate k none

theorem free_table_loop_spec (slots : Std.Usize)
    (table : alloc.vec.Vec (Option yata_store.IdCore)) (i : Std.Usize)
    (hinv : Filling slots.val table.val i.val) :
    id_set.free_table_loop slots table i ⦃ r => r.val = List.replicate slots.val none ⦄ := by
  unfold id_set.free_table_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : alloc.vec.Vec (Option yata_store.IdCore) × Std.Usize) => slots.val - k.val)
    (fun ((t, k) : alloc.vec.Vec (Option yata_store.IdCore) × Std.Usize) =>
      Filling slots.val t.val k.val)
    (fun (r : alloc.vec.Vec (Option yata_store.IdCore)) =>
      r.val = List.replicate slots.val none)
    _ (table, i) ?_ hinv
  intro ⟨t, k⟩ hF0
  have hF : Filling slots.val t.val k.val := hF0
  have hk := hF.bound
  have ht := hF.free
  unfold id_set.free_table_loop.body
  simp only
  by_cases hlt : k < slots
  · simp only [hlt, ↓reduceIte]
    have htl : t.val.length < Std.Usize.max := by
      have := congrArg List.length ht
      rw [List.length_replicate] at this
      scalar_tac
    step as ⟨t1, ht1⟩
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = k.val + 1 := by scalar_tac
    refine ⟨?_, by scalar_tac⟩
    show Filling slots.val t1.val k1.val
    refine ⟨by scalar_tac, ?_⟩
    rw [ht1, ht, hk1v, List.replicate_succ']
  · simp only [hlt, ↓reduceIte, spec_ok]
    have e : k.val = slots.val := by scalar_tac
    rw [ht, e]

theorem free_table_spec (slots : Std.Usize) :
    id_set.free_table slots ⦃ r => r.val = List.replicate slots.val none ⦄ := by
  unfold id_set.free_table
  refine free_table_loop_spec slots _ 0#usize ?_
  rw [usize_zero_val]
  exact ⟨Nat.zero_le _, by simp [alloc.vec.Vec.with_capacity]⟩

theorem free_slot_spec : id_set.free_slot ⦃ o => o = none ⦄ := by
  unfold id_set.free_slot
  simp only [spec_ok]

/-- The loop of `free_all` after `k` slots. -/
structure Freeing (n : Nat) (t : List (Option yata_store.IdCore)) (k : Nat) : Prop where
  bound : k ≤ n
  length : t.length = n
  free : ∀ j, j < k → t[j]? = some none

theorem free_all_loop_spec (table : Slice (Option yata_store.IdCore)) (i : Std.Usize)
    (n : Nat) (hinv : Freeing n table.val i.val) :
    id_set.free_all_loop table i ⦃ r => r.val = List.replicate n none ⦄ := by
  unfold id_set.free_all_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : Slice (Option yata_store.IdCore) × Std.Usize) => n - k.val)
    (fun ((t, k) : Slice (Option yata_store.IdCore) × Std.Usize) => Freeing n t.val k.val)
    (fun (r : Slice (Option yata_store.IdCore)) => r.val = List.replicate n none)
    _ (table, i) ?_ hinv
  intro ⟨t, k⟩ hF0
  have hF : Freeing n t.val k.val := hF0
  have hk := hF.bound
  have hlen := hF.length
  unfold id_set.free_all_loop.body
  simp only
  by_cases hlt : k < Slice.len t
  · simp only [hlt, ↓reduceIte]
    have hkl : k.val < t.val.length := by scalar_tac
    step with free_slot_spec as ⟨o, ho⟩
    step as ⟨t1, ht1⟩
    have hv : t1.val = t.val.set k.val none := by
      rw [ht1, ho]
      simp
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = k.val + 1 := by scalar_tac
    refine ⟨?_, by scalar_tac⟩
    show Freeing n t1.val k1.val
    rw [hk1v, hv]
    refine ⟨by omega, by rw [List.length_set]; exact hlen, fun j hj => ?_⟩
    by_cases e : j = k.val
    · rw [e]
      exact get?_set_self none hkl
    · rw [get?_set_ne none e]
      exact hF.free j (by omega)
  · simp only [hlt, ↓reduceIte, spec_ok]
    have e : k.val = n := by scalar_tac
    apply ext_get?
    intro j
    by_cases hj : j < n
    · rw [hF.free j (by omega)]
      simp [hj]
    · rw [get?_none (by omega), get?_none (by simp; omega)]

/-- `free_all` frees every slot of a table, in place. -/
theorem free_all_spec (table : Slice (Option yata_store.IdCore)) :
    id_set.free_all table ⦃ r => r.val = List.replicate table.val.length none ⦄ := by
  unfold id_set.free_all
  refine free_all_loop_spec table 0#usize table.val.length ?_
  rw [usize_zero_val]
  exact ⟨Nat.zero_le _, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

/-! ## Probing -/

theorem id_eq_iff (a b : yata_store.IdCore) :
    yata_store.id_eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold yata_store.id_eq
  by_cases h : a.client = b.client
  · have h' : (a.client = b.client) = True := eq_true h
    simp only [h', ↓reduceIte, spec_ok, decide_eq_true_eq]
    constructor
    · intro h2
      cases a with
      | mk c1 k1 =>
        cases b with
        | mk c2 k2 =>
          have e1 : c1 = c2 := h
          have e2 : k1 = k2 := h2
          rw [e1, e2]
    · intro e
      rw [e]
  · simp only [h, ↓reduceIte, spec_ok]
    constructor
    · intro e
      cases e
    · intro e
      exact absurd (by rw [e]) h

/-- The first `t` slots the probe of `id` looks at hold other ids. -/
def Seen (l : List (Option yata_store.IdCore)) (h : Nat) (id : yata_store.IdCore) (t : Nat) :
    Prop :=
  ∀ t', t' < t → ∃ y, l[slotAt l.length h t']? = some (some y) ∧ y ≠ id

theorem Seen.busy {l : List (Option yata_store.IdCore)} {h : Nat} {id : yata_store.IdCore}
    {t : Nat} (hs : Seen l h id t) : Busy l h t := by
  intro t' ht'
  obtain ⟨y, hy, _⟩ := hs t' ht'
  exact ⟨y, hy⟩

/-- What a probe from the slot `h` ends with: the id, the free slot the walk
met first, or a walk around the table that met neither. -/
def ProbePost (l : List (Option yata_store.IdCore)) (h : Nat) (id : yata_store.IdCore) :
    id_set.Probe → Prop
  | .Found => Mem l id
  | .Free i => ∃ t, t < l.length ∧ slotAt l.length h t = i.val ∧ l[i.val]? = some none ∧
      Seen l h id t
  | .Full => Seen l h id l.length

/-- The loop of `probe` after `st` steps, at the slot `ix`. -/
structure Probing (l : List (Option yata_store.IdCore)) (h : Nat) (id : yata_store.IdCore)
    (ix st : Nat) : Prop where
  bound : st ≤ l.length
  slot : ix = slotAt l.length h st
  seen : Seen l h id st

theorem probe_loop_spec (table : Slice (Option yata_store.IdCore)) (id : yata_store.IdCore)
    (slots idx0 : Std.Usize) (hslots : slots.val = table.val.length)
    (hidx : table.val.length = 0 ∨ idx0.val < table.val.length) :
    id_set.probe_loop table id slots idx0 0#usize ⦃ r =>
      ProbePost table.val idx0.val id r ⦄ := by
  unfold id_set.probe_loop
  have hinit : Probing table.val idx0.val id idx0.val (0#usize : Std.Usize).val := by
    rw [usize_zero_val]
    exact ⟨Nat.zero_le _, rfl, fun t' ht' => absurd ht' (Nat.not_lt_zero _)⟩
  refine loop.spec_decr_nat
    (fun ((_, st) : Std.Usize × Std.Usize) => slots.val - st.val)
    (fun ((ix, st) : Std.Usize × Std.Usize) => Probing table.val idx0.val id ix.val st.val)
    (fun (r : id_set.Probe) => ProbePost table.val idx0.val id r)
    _ (idx0, 0#usize) ?_ hinit
  intro ⟨ix, st⟩ hP0
  have hP : Probing table.val idx0.val id ix.val st.val := hP0
  have hst := hP.bound
  have hix := hP.slot
  have hseen := hP.seen
  unfold id_set.probe_loop.body
  simp only
  by_cases hlt : st < slots
  · simp only [hlt, ↓reduceIte]
    have hstlt : st.val < table.val.length := by scalar_tac
    have h0 : idx0.val < table.val.length := by
      rcases hidx with h | h
      · omega
      · exact h
    have hixlt : ix.val < table.val.length := by
      rw [hix]
      exact slotAt_lt h0 _
    step as ⟨slot, hslot⟩
    have hget : table.val[ix.val]? = some slot := get?_of_getElem hixlt hslot
    cases slot with
    | none =>
      simp only [spec_ok]
      exact ⟨st.val, hstlt, hix.symm, hget, hseen⟩
    | some found =>
      simp only []
      step with id_eq_iff found id as ⟨b, hb⟩
      by_cases hbt : b = true
      · simp only [hbt, ↓reduceIte, spec_ok]
        have e : found = id := hb.mp hbt
        show Mem table.val id
        rw [← e]
        exact get?_mem hget
      · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
        have hne : found ≠ id := fun e => hbt (hb.mpr e)
        have hbnd := table.property
        step as ⟨idx1, hidx1⟩
        have hidx1v : idx1.val = ix.val + 1 := by scalar_tac
        have hwrap : (if idx1 = slots then ok 0#usize else ok idx1 : Result Std.Usize) ⦃ r =>
            r.val = nextSlot table.val.length ix.val ⦄ := by
          unfold nextSlot
          by_cases e : idx1 = slots
          · have e' : (idx1 = slots) = True := eq_true e
            simp only [e', ↓reduceIte, spec_ok]
            have hc : ix.val + 1 = table.val.length := by
              rw [← hidx1v, e, hslots]
            rw [ite_eq_left hc]
            exact usize_zero_val
          · simp only [e, ↓reduceIte, spec_ok]
            have hc : ¬ ix.val + 1 = table.val.length := by
              intro hc
              apply e
              apply UScalar.eq_of_val_eq
              rw [hidx1v, hc, hslots]
            rw [ite_eq_right hc]
            exact hidx1v
        step with hwrap as ⟨idx2, hidx2⟩
        step as ⟨st1, hst1⟩
        have hst1v : st1.val = st.val + 1 := by scalar_tac
        refine ⟨?_, by scalar_tac⟩
        show Probing table.val idx0.val id idx2.val st1.val
        rw [hst1v]
        refine ⟨by omega, ?_, ?_⟩
        · rw [hidx2, hix]
          rfl
        · intro t' ht'
          by_cases e : t' = st.val
          · rw [e, ← hix, hget]
            exact ⟨found, rfl, hne⟩
          · exact hseen t' (by omega)
  · simp only [hlt, ↓reduceIte, spec_ok]
    have e : st.val = table.val.length := by scalar_tac
    show Seen table.val idx0.val id table.val.length
    rw [← e]
    exact hseen

/-- `probe` walks from the home slot of the id. -/
theorem probe_spec (table : Slice (Option yata_store.IdCore)) (k0 k1 : Std.U64)
    (id : yata_store.IdCore) :
    id_set.probe table k0 k1 id ⦃ r =>
      ProbePost table.val (homeN k0 k1 id table.val.length) id r ⦄ := by
  unfold id_set.probe
  simp only
  have hstart : (if Slice.len table = 0#usize then ok 0#usize
      else id_set.home k0 k1 id (Slice.len table) : Result Std.Usize) ⦃ r =>
        r.val = homeN k0 k1 id table.val.length ⦄ := by
    by_cases e : Slice.len table = 0#usize
    · have e' : (Slice.len table = 0#usize) = True := eq_true e
      simp only [e', ↓reduceIte, spec_ok]
      have hl : table.val.length = 0 := by
        have := congrArg UScalar.val e
        scalar_tac
      rw [hl, homeN_zero]
      exact usize_zero_val
    · simp only [e, ↓reduceIte]
      have hpos : 0 < (Slice.len table).val := by
        have hne : (Slice.len table).val ≠ 0 := by
          intro h0
          apply e
          apply UScalar.eq_of_val_eq
          rw [h0, usize_zero_val]
        omega
      have hlen : (Slice.len table).val = table.val.length := by scalar_tac
      refine spec_mono (home_spec k0 k1 id (Slice.len table) hpos) ?_
      intro r hr
      rw [hr, hlen]
  step with hstart as ⟨idx, hidx⟩
  rw [← hidx]
  refine probe_loop_spec table id (Slice.len table) idx (by scalar_tac) ?_
  by_cases hz : table.val.length = 0
  · exact Or.inl hz
  · right
    rw [hidx]
    exact homeN_lt k0 k1 id (by omega)

/-! ## Tables -/

/-- The table of a set: every id is reached from its home slot. -/
def Table (k0 k1 : Std.U64) (l : List (Option yata_store.IdCore)) : Prop :=
  TableOK (fun x => homeN k0 k1 x l.length) l

theorem table_replicate (k0 k1 : Std.U64) (n : Nat) :
    Table k0 k1 (List.replicate n (none : Option yata_store.IdCore)) :=
  tableOK_replicate _ n

/-- What `put` does to a table with a free slot: the id is in it afterwards,
and one more slot is taken when it was not there. -/
structure PutPost (k0 k1 : Std.U64) (l : List (Option yata_store.IdCore))
    (id : yata_store.IdCore) (b : Bool) (l' : List (Option yata_store.IdCore)) : Prop where
  length : l'.length = l.length
  table : Table k0 k1 l'
  mem : ∀ z, Mem l' z ↔ z = id ∨ Mem l z
  count : countSome l' = countSome l + (if b = true then 1 else 0)

theorem put_spec (table : Slice (Option yata_store.IdCore)) (k0 k1 : Std.U64)
    (id : yata_store.IdCore) (hok : Table k0 k1 table.val)
    (hroom : countSome table.val < table.val.length) :
    id_set.put table k0 k1 id ⦃ b table1 => PutPost k0 k1 table.val id b table1.val ⦄ := by
  unfold id_set.put
  have hpos : 0 < table.val.length := by omega
  have hhome := homeN_lt k0 k1 id hpos
  step with probe_spec table k0 k1 id as ⟨p, hp⟩
  cases p with
  | Found =>
    simp only [spec_ok, uncurry'_pair]
    have hm : Mem table.val id := hp
    refine ⟨rfl, hok, fun z => ?_, by simp⟩
    constructor
    · intro h
      exact Or.inr h
    · rintro (e | h)
      · rw [e]
        exact hm
      · exact h
  | Free idx =>
    obtain ⟨t, ht, hslot, hfree, hseen⟩ := hp
    have hlt : idx.val < table.val.length := get?_lt hfree
    simp only []
    step as ⟨table1, ht1⟩
    have hv : table1.val = table.val.set idx.val (some id) := by
      rw [ht1]
      simp
    rw [hv]
    refine ⟨List.length_set, ?_, mem_set hfree, ?_⟩
    · show TableOK (fun x => homeN k0 k1 x (table.val.set idx.val (some id)).length) _
      rw [List.length_set]
      exact TableOK.set hok ht hslot hseen.busy hfree
    · rw [countSome_set id hfree]
      simp
  | Full =>
    exfalso
    have hs : Seen table.val (homeN k0 k1 id table.val.length) id table.val.length := hp
    exact exists_free_step hhome hroom hs.busy

/-! ## Growing -/

theorem countSome_take_le (l : List (Option yata_store.IdCore)) (i : Nat) :
    countSome (l.take i) ≤ countSome l := by
  have e : countSome l = countSome (l.take i) + countSome (l.drop i) := by
    rw [← countSome_append, List.take_append_drop]
  omega

theorem countSome_snoc (l : List (Option yata_store.IdCore)) (a : Option yata_store.IdCore) :
    countSome (l ++ [a]) = countSome l + countSome [a] :=
  countSome_append l [a]

/-- The loop of `rehash`, when it is done with the first `i` slots of the
old table. -/
structure Rehashing (k0 k1 : Std.U64) (old : List (Option yata_store.IdCore)) (cap : Nat)
    (t : List (Option yata_store.IdCore)) (count i : Nat) : Prop where
  bound : i ≤ old.length
  length : t.length = cap
  table : Table k0 k1 t
  counted : countSome t = count
  le : count ≤ countSome (old.take i)
  mem : ∀ z, Mem t z ↔ Mem (old.take i) z

theorem rehash_loop_spec (old : Slice (Option yata_store.IdCore)) (k0 k1 : Std.U64) (cap : Nat)
    (table : alloc.vec.Vec (Option yata_store.IdCore)) (count i : Std.Usize)
    (hroom : countSome old.val < cap)
    (hinv : Rehashing k0 k1 old.val cap table.val count.val i.val) :
    id_set.rehash_loop old k0 k1 table count i ⦃ r =>
      Rehashing k0 k1 old.val cap r.1.val r.2.val old.val.length ⦄ := by
  unfold id_set.rehash_loop
  refine loop.spec_decr_nat
    (fun ((_, _, k) : alloc.vec.Vec (Option yata_store.IdCore) × Std.Usize × Std.Usize) =>
      old.val.length - k.val)
    (fun ((t, c, k) : alloc.vec.Vec (Option yata_store.IdCore) × Std.Usize × Std.Usize) =>
      Rehashing k0 k1 old.val cap t.val c.val k.val)
    (fun (r : alloc.vec.Vec (Option yata_store.IdCore) × Std.Usize) =>
      Rehashing k0 k1 old.val cap r.1.val r.2.val old.val.length)
    _ (table, count, i) ?_ hinv
  intro ⟨t, c, k⟩ hinv0
  have hI : Rehashing k0 k1 old.val cap t.val c.val k.val := hinv0
  unfold id_set.rehash_loop.body
  simp only
  by_cases hlt : k < Slice.len old
  · simp only [hlt, ↓reduceIte]
    have hkl : k.val < old.val.length := by scalar_tac
    have hbnd := old.property
    step as ⟨slot, hslot⟩
    have hget : old.val[k.val]? = some slot := get?_of_getElem hkl hslot
    have htake : old.val.take (k.val + 1) = old.val.take k.val ++ [slot] := take_succ_get hget
    have hcle := countSome_take_le old.val (k.val + 1)
    cases slot with
    | none =>
      simp only
      step as ⟨kn, hkn⟩
      have hknv : kn.val = k.val + 1 := by scalar_tac
      refine ⟨?_, by scalar_tac⟩
      show Rehashing k0 k1 old.val cap t.val c.val kn.val
      rw [hknv]
      refine ⟨by omega, hI.length, hI.table, hI.counted, ?_, fun z => ?_⟩
      · rw [htake, countSome_snoc]
        have := hI.le
        show c.val ≤ countSome (old.val.take k.val) + 0
        omega
      · rw [hI.mem z, htake]
        unfold Mem
        simp
    | some id =>
      have hcount : countSome t.val < t.val.length := by
        have h1 := hI.le
        have h2 := hI.counted
        have h3 := hI.length
        rw [htake, countSome_snoc] at hcle
        have h4 : countSome [some id] = 1 := rfl
        omega
      have hput := put_spec t.slice k0 k1 id hI.table hcount
      simp only []
      refine spec_bind (?_ : spec _ (fun (p : alloc.vec.Vec (Option yata_store.IdCore) ×
          Std.Usize) => Rehashing k0 k1 old.val cap p.1.val p.2.val (k.val + 1))) (fun p hp => ?_)
      · simp only [lift, alloc.vec.Vec.deref_mut]
        step with hput as ⟨b, s1, hp⟩
        have hp' : PutPost k0 k1 t.val id b s1.val := hp
        have hmem : ∀ z, Mem s1.val z ↔ Mem (old.val.take (k.val + 1)) z := by
          intro z
          rw [hp'.mem z, hI.mem z, htake]
          unfold Mem
          simp only [List.mem_append, List.mem_singleton, Option.some.injEq]
          exact Or.comm
        by_cases hbt : b = true
        · simp only [hbt, ↓reduceIte]
          have hcb : c.val < Std.Usize.max := by
            have h1 := hI.counted
            have h2 := t.property
            omega
          step as ⟨c2, hc2⟩
          have hc2v : c2.val = c.val + 1 := by scalar_tac
          show Rehashing k0 k1 old.val cap s1.val c2.val (k.val + 1)
          rw [hc2v]
          refine ⟨by omega, by rw [hp'.length]; exact hI.length, hp'.table, ?_, ?_, hmem⟩
          · rw [hp'.count, hI.counted, hbt]
            rfl
          · rw [htake, countSome_snoc]
            have := hI.le
            show c.val + 1 ≤ countSome (old.val.take k.val) + 1
            omega
        · simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
          show Rehashing k0 k1 old.val cap s1.val c.val (k.val + 1)
          refine ⟨by omega, by rw [hp'.length]; exact hI.length, hp'.table, ?_, ?_, hmem⟩
          · rw [hp'.count, hI.counted]
            simp [hbt]
          · rw [htake, countSome_snoc]
            have := hI.le
            show c.val ≤ countSome (old.val.take k.val) + 1
            omega
      · obtain ⟨t1, c1⟩ := p
        have hp1 : Rehashing k0 k1 old.val cap t1.val c1.val (k.val + 1) := hp
        step as ⟨kn, hkn⟩
        have hknv : kn.val = k.val + 1 := by scalar_tac
        refine ⟨?_, by scalar_tac⟩
        show Rehashing k0 k1 old.val cap t1.val c1.val kn.val
        rw [hknv]
        exact hp1
  · simp only [hlt, ↓reduceIte, spec_ok]
    have e : k.val = old.val.length := by
      have := hI.bound
      scalar_tac
    show Rehashing k0 k1 old.val cap t.val c.val old.val.length
    rw [← e]
    exact hI

/-- `rehash` moves the ids of a table into a larger one. -/
theorem rehash_spec (old : Slice (Option yata_store.IdCore)) (k0 k1 : Std.U64)
    (slots : Std.Usize) (hroom : countSome old.val < slots.val) :
    id_set.rehash old k0 k1 slots ⦃ table count =>
      table.val.length = slots.val ∧ Table k0 k1 table.val ∧ countSome table.val = count.val ∧
        count.val ≤ countSome old.val ∧ ∀ z, Mem table.val z ↔ Mem old.val z ⦄ := by
  unfold id_set.rehash
  step with free_table_spec slots as ⟨table, htable⟩
  have hinit : Rehashing k0 k1 old.val slots.val table.val (0#usize : Std.Usize).val
      (0#usize : Std.Usize).val := by
    rw [htable, usize_zero_val]
    refine ⟨Nat.zero_le _, List.length_replicate, table_replicate k0 k1 _, countSome_replicate _,
      Nat.zero_le _, fun z => ?_⟩
    · constructor
      · intro h
        exact absurd h (not_mem_replicate _ z)
      · intro h
        have h' : some z ∈ ([] : List (Option yata_store.IdCore)) := h
        cases h'
  refine spec_mono (rehash_loop_spec old k0 k1 slots.val table 0#usize 0#usize hroom hinit) ?_
  rintro ⟨t, c⟩ hr
  have hR : Rehashing k0 k1 old.val slots.val t.val c.val old.val.length := hr
  have hfull : old.val.take old.val.length = old.val := List.take_length
  have h1 := hR.le
  have h2 := hR.mem
  rw [hfull] at h1 h2
  show t.val.length = slots.val ∧ Table k0 k1 t.val ∧ countSome t.val = c.val ∧
    c.val ≤ countSome old.val ∧ ∀ z, Mem t.val z ↔ Mem old.val z
  exact ⟨hR.length, hR.table, hR.counted, h1, h2⟩

/-! ## Sets -/

/-- The invariant of a set. -/
structure WF (s : id_set.IdSetCore) : Prop where
  /-- no table, or a power of two of slots -/
  pow : s.buckets.val = [] ∨ ∃ n, s.buckets.val.length = 2 ^ n
  /-- `len` counts the ids -/
  count : s.len.val = countSome s.buckets.val
  /-- at most half of the slots are taken -/
  load : 2 * s.len.val ≤ s.buckets.val.length
  /-- every id is reached from its home slot under the key of the set -/
  table : Table s.k0 s.k1 s.buckets.val

/-- `id` is in the set. -/
def Has (s : id_set.IdSetCore) (id : yata_store.IdCore) : Prop := Mem s.buckets.val id

/-- **`with_key` makes the empty set of a key.** -/
@[step]
theorem with_key_spec (k0 k1 : Std.U64) :
    id_set.IdSetCore.with_key k0 k1 ⦃ s =>
      WF s ∧ (∀ id, ¬ Has s id) ∧ s.len.val = 0 ∧ s.k0 = k0 ∧ s.k1 = k1 ⦄ := by
  unfold id_set.IdSetCore.with_key
  have hb : (alloc.vec.Vec.new (Option yata_store.IdCore)).val = [] := by simp
  refine (spec_ok _).mpr ⟨⟨Or.inl hb, ?_, ?_, ?_⟩, fun id h => ?_, usize_zero_val, rfl, rfl⟩
  · show (0#usize : Std.Usize).val = countSome (alloc.vec.Vec.new (Option yata_store.IdCore)).val
    rw [hb, usize_zero_val]
    rfl
  · show 2 * (0#usize : Std.Usize).val ≤
      (alloc.vec.Vec.new (Option yata_store.IdCore)).val.length
    rw [hb, usize_zero_val]
    exact Nat.le_refl _
  · show Table k0 k1 (alloc.vec.Vec.new (Option yata_store.IdCore)).val
    rw [hb]
    exact tableOK_nil _
  · have h' : some id ∈ (alloc.vec.Vec.new (Option yata_store.IdCore)).val := h
    rw [hb] at h'
    cases h'

/-- **`new` makes the empty set of the key `(0, 0)`.** -/
@[step]
theorem new_spec :
    id_set.IdSetCore.new ⦃ s => WF s ∧ (∀ id, ¬ Has s id) ∧ s.len.val = 0 ⦄ := by
  unfold id_set.IdSetCore.new
  refine spec_mono (with_key_spec 0#u64 0#u64) ?_
  intro s hs
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

/-- What `clear` makes of a set. -/
structure ClearPost (s s' : id_set.IdSetCore) : Prop where
  wf : WF s'
  /-- no id is in the set -/
  empty : ∀ z, ¬ Has s' z
  len : s'.len.val = 0
  /-- the key stays -/
  key : s'.k0 = s.k0 ∧ s'.k1 = s.k1
  /-- an empty set is left as it is -/
  same : s.len.val = 0 → s' = s
  /-- the table does not grow -/
  slots : s'.buckets.val.length ≤ s.buckets.val.length

/-- A set whose table was emptied, or replaced by an empty one whose size is
the size of a table, and which is not larger. -/
theorem clearPost_of_free (s : id_set.IdSetCore) (v : alloc.vec.Vec (Option yata_store.IdCore))
    (n : Nat) (hv : v.val = List.replicate n none) (hn : n = 0 ∨ ∃ m, n = 2 ^ m)
    (hle : n ≤ s.buckets.val.length) (hne : s.len.val ≠ 0) :
    ClearPost s { s with buckets := v, len := 0#usize } := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun z hz => ?_, usize_zero_val, ⟨rfl, rfl⟩,
    fun h0 => absurd h0 hne, ?_⟩
  · show v.val = [] ∨ ∃ m, v.val.length = 2 ^ m
    rw [hv, List.length_replicate]
    rcases hn with h0 | ⟨m, hm⟩
    · left
      rw [h0]
      rfl
    · exact Or.inr ⟨m, hm⟩
  · show (0#usize : Std.Usize).val = countSome v.val
    rw [hv, usize_zero_val, countSome_replicate]
  · show 2 * (0#usize : Std.Usize).val ≤ v.val.length
    rw [usize_zero_val]
    omega
  · show Table s.k0 s.k1 v.val
    rw [hv]
    exact table_replicate _ _ _
  · have hz' : Mem v.val z := hz
    rw [hv] at hz'
    exact not_mem_replicate _ z hz'
  · show v.val.length ≤ s.buckets.val.length
    rw [hv, List.length_replicate]
    exact hle

/-- **`clear` empties the set**: no id is in it, it keeps its key, and it is a
set again (`WF`). A table of at most `FIRST_SLOTS` slots, or one that is at
least an eighth full, is emptied in place; a larger one is let go for a table
of `FIRST_SLOTS` slots. -/
theorem clear_spec (s : id_set.IdSetCore) (h : WF s) :
    id_set.IdSetCore.clear s ⦃ s' => ClearPost s s' ⦄ := by
  unfold id_set.IdSetCore.clear
  have hfirst : (id_set.FIRST_SLOTS).val = 16 := by simp [id_set.FIRST_SLOTS]
  have hsize : s.buckets.val.length = 0 ∨ ∃ m, s.buckets.val.length = 2 ^ m := by
    rcases h.pow with hnil | hp
    · left
      rw [hnil]
      rfl
    · exact Or.inr hp
  by_cases hz : s.len = 0#usize
  · have hz' : (s.len = 0#usize) = True := eq_true hz
    simp only [hz', ↓reduceIte, spec_ok]
    have h0 : s.len.val = 0 := by
      rw [hz]
      exact usize_zero_val
    refine ⟨h, fun z hm => ?_, h0, ⟨rfl, rfl⟩, fun _ => rfl, Nat.le_refl _⟩
    -- an empty set holds no id: its table has no taken slot
    have hc : countSome s.buckets.val = 0 := by
      rw [← h.count]
      exact h0
    obtain ⟨j, hj⟩ := mem_get? (show some z ∈ s.buckets.val from hm)
    have := countSome_pos_of_get hj
    omega
  · simp only [hz, ↓reduceIte]
    have hne : s.len.val ≠ 0 := by
      intro h0
      apply hz
      apply UScalar.eq_of_val_eq
      rw [h0, usize_zero_val]
    by_cases hsmall : alloc.vec.Vec.len s.buckets <= id_set.FIRST_SLOTS
    · simp only [hsmall, ↓reduceIte]
      simp only [lift, alloc.vec.Vec.deref_mut]
      step with free_all_spec s.buckets.slice as ⟨t1, ht1⟩
      have ht1' : t1.val = List.replicate s.buckets.val.length none := ht1
      exact clearPost_of_free s _ s.buckets.val.length ht1' hsize (Nat.le_refl _) hne
    · simp only [hsmall, ↓reduceIte]
      have hbig : 16 < s.buckets.val.length := by scalar_tac
      step as ⟨eighth, heighth⟩
      by_cases hfull : eighth <= s.len
      · simp only [hfull, ↓reduceIte]
        simp only [lift, alloc.vec.Vec.deref_mut]
        step with free_all_spec s.buckets.slice as ⟨t1, ht1⟩
        have ht1' : t1.val = List.replicate s.buckets.val.length none := ht1
        exact clearPost_of_free s _ s.buckets.val.length ht1' hsize (Nat.le_refl _) hne
      · simp only [hfull, ↓reduceIte]
        step with free_table_spec id_set.FIRST_SLOTS as ⟨table, htable⟩
        rw [hfirst] at htable
        exact clearPost_of_free s table 16 htable (Or.inr ⟨4, rfl⟩) (by omega) hne

@[step]
theorem len_spec (s : id_set.IdSetCore) : id_set.IdSetCore.impl.len s ⦃ n => n = s.len ⦄ := by
  unfold id_set.IdSetCore.impl.len
  simp [spec_ok]

@[step]
theorem is_empty_spec (s : id_set.IdSetCore) :
    id_set.IdSetCore.is_empty s ⦃ b => (b = true ↔ s.len.val = 0) ⦄ := by
  unfold id_set.IdSetCore.is_empty
  simp only [spec_ok, decide_eq_true_eq]
  constructor
  · intro e
    rw [e]
    exact usize_zero_val
  · intro e
    apply UScalar.eq_of_val_eq
    rw [e, usize_zero_val]

/-- **`contains` answers whether the id is in the set.** -/
@[step]
theorem contains_spec (s : id_set.IdSetCore) (id : yata_store.IdCore) (h : WF s) :
    id_set.IdSetCore.contains s id ⦃ b => (b = true ↔ Has s id) ⦄ := by
  unfold id_set.IdSetCore.contains
  simp only
  have hd : (alloc.vec.Vec.deref s.buckets).val = s.buckets.val := by
    simp [alloc.vec.Vec.deref]
  step with probe_spec (alloc.vec.Vec.deref s.buckets) s.k0 s.k1 id as ⟨p, hp⟩
  rw [hd] at hp
  cases p with
  | Found =>
    simp only [spec_ok]
    have hm : Mem s.buckets.val id := hp
    constructor
    · intro _
      exact hm
    · intro _
      trivial
  | Free idx =>
    simp only [spec_ok]
    obtain ⟨t, _, hslot, hfree, hseen⟩ := hp
    have hfree' : s.buckets.val[slotAt s.buckets.val.length
        (homeN s.k0 s.k1 id s.buckets.val.length) t]? = some none := by
      rw [hslot]
      exact hfree
    have hno : ¬ Mem s.buckets.val id :=
      not_mem_of_free (home := fun x => homeN s.k0 s.k1 x s.buckets.val.length) h.table hseen hfree'
    constructor
    · intro e
      cases e
    · intro hm
      exact absurd hm hno
  | Full =>
    simp only [spec_ok]
    have hs : Seen s.buckets.val (homeN s.k0 s.k1 id s.buckets.val.length) id
        s.buckets.val.length := hp
    have hno : ¬ Mem s.buckets.val id :=
      not_mem_of_full (home := fun x => homeN s.k0 s.k1 x s.buckets.val.length) h.table hs
    constructor
    · intro e
      cases e
    · intro hm
      exact absurd hm hno

/-- What `reserve` does: it keeps the ids, and when it accepts the table has
a free slot left after one more id. -/
structure ReservePost (s : id_set.IdSetCore) (b : Bool) (s' : id_set.IdSetCore) : Prop where
  wf : WF s'
  mem : ∀ z, Has s' z ↔ Has s z
  refused : b = false → s' = s
  room : b = true → 2 * (s'.len.val + 1) ≤ s'.buckets.val.length
  len : s'.len.val ≤ s.len.val
  /-- it accepts while the set holds fewer than `2 ^ 30` ids -/
  accepts : s.len.val < 1073741824 → b = true
  /-- the key stays -/
  key : s'.k0 = s.k0 ∧ s'.k1 = s.k1

theorem reserve_spec (s : id_set.IdSetCore) (h : WF s) :
    id_set.IdSetCore.reserve s ⦃ b s' => ReservePost s b s' ⦄ := by
  unfold id_set.IdSetCore.reserve
  simp only
  by_cases hz : alloc.vec.Vec.len s.buckets = 0#usize
  · have hz' : (alloc.vec.Vec.len s.buckets = 0#usize) = True := eq_true hz
    simp only [hz', ↓reduceIte]
    have hl : s.buckets.val.length = 0 := by
      have := congrArg UScalar.val hz
      scalar_tac
    have hnil : s.buckets.val = [] := List.eq_nil_of_length_eq_zero hl
    have hlen0 : s.len.val = 0 := by
      have := h.load
      omega
    step with free_table_spec id_set.FIRST_SLOTS as ⟨table, htable⟩
    have hfirst : (id_set.FIRST_SLOTS).val = 16 := by simp [id_set.FIRST_SLOTS]
    rw [hfirst] at htable
    refine ⟨⟨Or.inr ⟨4, ?_⟩, ?_, ?_, ?_⟩, fun z => ?_, (fun e => nomatch e), fun _ => ?_,
      Nat.le_refl _, fun _ => rfl, ⟨rfl, rfl⟩⟩
    · show table.val.length = 2 ^ 4
      rw [htable]
      simp
    · show s.len.val = countSome table.val
      rw [htable, hlen0, countSome_replicate]
    · show 2 * s.len.val ≤ table.val.length
      rw [htable, hlen0]
      simp
    · show Table s.k0 s.k1 table.val
      rw [htable]
      exact table_replicate _ _ _
    · show Mem table.val z ↔ Mem s.buckets.val z
      rw [htable, hnil]
      constructor
      · intro hm
        exact absurd hm (not_mem_replicate _ z)
      · intro hm
        cases hm
    · show 2 * (s.len.val + 1) ≤ table.val.length
      rw [htable, hlen0]
      simp
  · simp only [hz, ↓reduceIte]
    have hpos : 0 < s.buckets.val.length := by
      have hne : (alloc.vec.Vec.len s.buckets).val ≠ 0 := by
        intro h0
        apply hz
        apply UScalar.eq_of_val_eq
        rw [h0]
        rfl
      scalar_tac
    step as ⟨half, hhalf⟩
    have hhalfv : half.val = s.buckets.val.length / 2 := by scalar_tac
    by_cases hlow : s.len < half
    · simp only [hlow, ↓reduceIte, spec_ok, uncurry'_pair]
      have hlt : s.len.val < s.buckets.val.length / 2 := by scalar_tac
      exact ⟨h, fun _ => Iff.rfl, (fun e => nomatch e), fun _ => by omega, Nat.le_refl _,
        fun _ => rfl, ⟨rfl, rfl⟩⟩
    · simp only [hlow, ↓reduceIte]
      have hge : s.buckets.val.length / 2 ≤ s.len.val := by scalar_tac
      step as ⟨top, htop⟩
      have hMax : (core.num.Usize.MAX : Std.Usize).val = Std.Usize.max := rfl
      have htopv : top.val = Std.Usize.max / 2 := by
        rw [← hMax]
        scalar_tac
      by_cases hbig : alloc.vec.Vec.len s.buckets > top
      · simp only [hbig, ↓reduceIte, spec_ok, uncurry'_pair]
        refine ⟨h, fun _ => Iff.rfl, fun _ => rfl, (fun e => nomatch e), Nat.le_refl _,
          fun hsmall => ?_, ⟨rfl, rfl⟩⟩
        exfalso
        have hb : Std.Usize.max / 2 < s.buckets.val.length := by scalar_tac
        have hu : 4294967295 ≤ Std.Usize.max := by scalar_tac
        omega
      · simp only [hbig, ↓reduceIte]
        have hsmall : s.buckets.val.length ≤ Std.Usize.max / 2 := by scalar_tac
        have hd : (alloc.vec.Vec.deref s.buckets).val = s.buckets.val := by
          simp [alloc.vec.Vec.deref]
        step as ⟨twice, htwice⟩
        have htwicev : twice.val = s.buckets.val.length * 2 := by scalar_tac
        have hroom : countSome (alloc.vec.Vec.deref s.buckets).val < twice.val := by
          rw [hd, htwicev]
          have := countSome_le s.buckets.val
          omega
        step with rehash_spec (alloc.vec.Vec.deref s.buckets) s.k0 s.k1 twice hroom
          as ⟨table, count, hlen, htab, hcount, hle, hmem⟩
        rw [hd] at hle hmem
        have hcl : count.val ≤ s.len.val := by
          rw [h.count]
          exact hle
        have hload := h.load
        refine ⟨⟨?_, ?_, ?_, htab⟩, hmem, (fun e => nomatch e), fun _ => ?_, hcl, fun _ => rfl,
          ⟨rfl, rfl⟩⟩
        · right
          rcases h.pow with hnil | ⟨n, hn⟩
          · rw [hnil] at hpos
            exact absurd hpos (by decide)
          · refine ⟨n + 1, ?_⟩
            show table.val.length = 2 ^ (n + 1)
            rw [hlen, htwicev, hn, Nat.pow_succ]
        · show count.val = countSome table.val
          exact hcount.symm
        · show 2 * count.val ≤ table.val.length
          rw [hlen, htwicev]
          omega
        · show 2 * (count.val + 1) ≤ table.val.length
          rw [hlen, htwicev]
          omega

/-- What `insert` does, by its answer. -/
structure InsertPost (s : id_set.IdSetCore) (id : yata_store.IdCore) (b : Bool)
    (s' : id_set.IdSetCore) : Prop where
  wf : WF s'
  /-- it accepted: the id is in the set, next to the ones that were -/
  added : b = true → ∀ z, Has s' z ↔ z = id ∨ Has s z
  /-- it refused: the set is as it was -/
  refused : b = false → s' = s
  /-- one more id at most -/
  len : s'.len.val ≤ s.len.val + 1
  /-- it accepts while the set holds fewer than `2 ^ 30` ids -/
  accepts : s.len.val < 1073741824 → b = true
  /-- the key stays -/
  key : s'.k0 = s.k0 ∧ s'.k1 = s.k1

/-- **`insert` adds the id to the set**, or refuses and changes nothing. -/
theorem insert_spec (s : id_set.IdSetCore) (id : yata_store.IdCore) (h : WF s) :
    id_set.IdSetCore.insert s id ⦃ b s' => InsertPost s id b s' ⦄ := by
  unfold id_set.IdSetCore.insert
  step with reserve_spec s h as ⟨b, s1, hres⟩
  have hR : ReservePost s b s1 := hres
  by_cases hbt : b = true
  · simp only [hbt, ↓reduceIte]
    have hroom := hR.room hbt
    have hwf := hR.wf
    have hs1len := hR.len
    have hcount : countSome s1.buckets.slice.val < s1.buckets.slice.val.length := by
      show countSome s1.buckets.val < s1.buckets.val.length
      rw [← hwf.count]
      omega
    have hput := put_spec s1.buckets.slice s1.k0 s1.k1 id hwf.table hcount
    simp only [lift, alloc.vec.Vec.deref_mut]
    step with hput as ⟨b1, t1, hp⟩
    have hp' : PutPost s1.k0 s1.k1 s1.buckets.val id b1 t1.val := hp
    have hpow : ∀ l : List (Option yata_store.IdCore), l.length = s1.buckets.val.length →
        l = [] ∨ ∃ n, l.length = 2 ^ n := by
      intro l hl
      rcases hwf.pow with hnil | ⟨n, hn⟩
      · rw [hnil] at hroom
        exact absurd hroom (by simp)
      · exact Or.inr ⟨n, by rw [hl, hn]⟩
    have hadd : ∀ z, Mem t1.val z ↔ z = id ∨ Has s z := by
      intro z
      rw [hp'.mem z]
      have := hR.mem z
      unfold Has at this
      rw [this]
      rfl
    by_cases hb1 : b1 = true
    · simp only [hb1, ↓reduceIte]
      have hlen1 : s1.len.val < Std.Usize.max := by
        have := s1.buckets.property
        omega
      step as ⟨n1, hn1⟩
      have hn1v : n1.val = s1.len.val + 1 := by scalar_tac
      refine ⟨⟨hpow _ hp'.length, ?_, ?_, hp'.table⟩, fun _ => hadd, (fun e => nomatch e), ?_,
        fun _ => rfl, hR.key⟩
      · show n1.val = countSome t1.val
        rw [hn1v, hp'.count, hwf.count, hb1]
        rfl
      · show 2 * n1.val ≤ t1.val.length
        rw [hn1v, hp'.length]
        exact hroom
      · show n1.val ≤ s.len.val + 1
        omega
    · simp only [hb1, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
      refine ⟨⟨hpow _ hp'.length, ?_, ?_, hp'.table⟩, fun _ => hadd, (fun e => nomatch e), ?_,
        fun _ => rfl, hR.key⟩
      · show s1.len.val = countSome t1.val
        rw [hp'.count, hwf.count]
        simp [hb1]
      · show 2 * s1.len.val ≤ t1.val.length
        rw [hp'.length]
        exact hwf.load
      · show s1.len.val ≤ s.len.val + 1
        omega
  · have hbf : b = false := by
      cases hb : b with
      | false => rfl
      | true => exact absurd hb hbt
    simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
    have e := hR.refused hbf
    rw [e]
    refine ⟨h, fun hb => ?_, fun _ => rfl, Nat.le_succ _, fun hsmall => ?_, ⟨rfl, rfl⟩⟩
    · cases hb
    · exact absurd (hR.accepts hsmall) hbt

end YoctoCore.Properties.IdSet
