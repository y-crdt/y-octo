/-
`y_octo_core::doc_kernel`: the decisions `DocStore` takes about the structure
of a document, apart from the conflict scan.

Every function is total on every input (no panic, no overflow) and answers
what its specification says, exactly:

* `parent_precedes_item`, `check_origin`: a struct of the same client created
  at or after an item (`Late`) is neither its origin nor its parent.
* `same_container`: the same parent and, as the caller says, the same key; an
  item without a parent matches anything.
* `check_direct_cycle`, `parent_walk_step`: one step of the walk up the type
  tree. `walk` is the loop `TypeArena::is_above` of `y-octo` runs with it, and
  `walk_iff_reach` says what that loop answers when it is given as many steps
  as there are types that have a parent: whether the type is above the other
  one at all (`Reach`), however the types above loop. No set of the types it
  met is needed for that (`reach_bounded`, a pigeonhole).
* `needs_conflict_scan`: `needsScanK`.
* `decide_integrate_link`: `linkPlan`. Under a map key the plan keeps every
  value but the last one deleted (`Lww`): `lww_integrate`, for a value linked
  at any place of the list of its key; `lww_unique` and `lww_determined` say
  what that invariant is worth: at most the last value is not deleted, and two
  lists of the same values in the same order differ at most in whether the
  last one is deleted. `KeyRun` is every list of a key a replica can reach
  that way; `keyRun_lww` and `keyRun_sec` are the two for such lists.
* `follows_in_list`, `can_merge_items`: `CanMerge`, and the list the two are
  in; the answer is the one for one list and the list
  (`can_merge_items_and`), and nothing merges that does not follow in its
  list.
* `cuts_live_item`, `plan_delete_range_splits`, `plan_split_node`: where a
  range and an item are cut.

What is not here: that `DocStore` calls these functions where it takes these
decisions, and that the lists it keeps are the lists these theorems speak of
(`proofs/TRUSTED.md`).
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.ListAux
import YoctoCore.Properties.IdSet

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties.ListAux
open YoctoCore.Properties.IdSet (id_eq_iff usize_zero_val)

set_option maxHeartbeats 400000
set_option autoImplicit false

namespace YoctoCore.Properties.DocKernel

/-- A call that meets a specification returned. -/
theorem ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    ∃ x, m = ok x ∧ P x := by
  cases m with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact ((spec_vis i k).mp h).elim
  | div => exact (spec_div.mp h).elim

theorem bne_true_ne {a b : Std.U64} (h : (a != b) = true) : ¬ a = b := by
  intro e
  rw [e] at h
  simp at h

theorem bne_false_eq {a b : Std.U64} (h : (a != b) = false) : a = b := by
  by_contra hne
  have ht : (a != b) = true := bne_iff_ne.mpr hne
  rw [h] at ht
  cases ht

theorem bool_false_of_not {b : Bool} (h : ¬ b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

/-! ## The comparisons of `yata_store`, on what they compare -/

theorem opt_slot_eq_raw (a b : Option Std.U32) :
    yata_store.opt_slot_eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold yata_store.opt_slot_eq
  cases a <;> cases b <;> simp [spec_ok]

theorem slot_is_raw (a : Option Std.U32) (b : Std.U32) :
    yata_store.slot_is a b ⦃ r => (r = true ↔ a = some b) ⦄ := by
  unfold yata_store.slot_is
  cases a <;> simp [spec_ok]

theorem opt_id_eq_raw (a b : Option yata_store.IdCore) :
    yata_store.opt_id_eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold yata_store.opt_id_eq
  cases a with
  | none => cases b <;> simp [spec_ok]
  | some x =>
    cases b with
    | none => simp [spec_ok]
    | some y =>
      refine spec_mono (id_eq_iff x y) ?_
      intro r hr
      rw [hr]
      exact ⟨fun e => by rw [e], fun e => Option.some.inj e⟩

/-! ## Origins and parents -/

/-- `other` is a struct of the client of `item` created at or after it: no
struct `item` can name. -/
def Late (item other : yata_store.IdCore) : Prop :=
  other.client = item.client ∧ item.clock.val ≤ other.clock.val

/-- **`parent_precedes_item` refuses exactly the structs of the same client
at or after the item.** -/
@[step]
theorem parent_precedes_item_spec (item parent : yata_store.IdCore) :
    doc_kernel.parent_precedes_item item parent ⦃ b => (b = true ↔ ¬ Late item parent) ⦄ := by
  unfold doc_kernel.parent_precedes_item Late
  by_cases h : parent.client = item.client
  · by_cases hge : parent.clock >= item.clock
    · have hle : item.clock.val ≤ parent.clock.val := by scalar_tac
      simp [h, hge, hle, spec_ok]
    · have hle : ¬ item.clock.val ≤ parent.clock.val := by scalar_tac
      simp [h, hge, hle, spec_ok]
  · simp [h, spec_ok]

/-- **`check_origin` refuses exactly an origin of the same client at or after
the item**, with `InvalidOrigin`. -/
@[step]
theorem check_origin_spec (id : yata_store.IdCore) (origin : Option yata_store.IdCore) :
    doc_kernel.check_origin id origin ⦃ r =>
      ((∀ o, origin = some o → ¬ Late id o) ∧ r = core.result.Result.Ok ()) ∨
      ((∃ o, origin = some o ∧ Late id o) ∧
        r = core.result.Result.Err client_blocks.StoreError.InvalidOrigin) ⦄ := by
  unfold doc_kernel.check_origin
  cases origin with
  | none =>
    simp only [spec_ok]
    exact Or.inl ⟨(fun o e => nomatch e), trivial⟩
  | some o =>
    simp only []
    step as ⟨b, hb⟩
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte, spec_ok]
      refine Or.inl ⟨fun o' e => ?_, trivial⟩
      cases e
      exact hb.mp hbt
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact Or.inr ⟨⟨o, rfl, Classical.not_not.mp (fun hn => hbt (hb.mpr hn))⟩, trivial⟩

/-- An item without an origin is never refused. -/
theorem check_origin_none (id : yata_store.IdCore) :
    doc_kernel.check_origin id none = ok (core.result.Result.Ok ()) := by
  unfold doc_kernel.check_origin
  rfl

/-! ## Lists -/

/-- **`same_container`**: an item without a parent matches anything; any
other one matches an item of the same parent, when the caller says that the
two have the same key. -/
theorem same_container_spec (other this : Option Std.U32) (same_sub : Bool) :
    doc_kernel.same_container other this same_sub ⦃ b =>
      (b = true ↔ this = none ∨ ∃ t, this = some t ∧ other = some t ∧ same_sub = true) ⦄ := by
  unfold doc_kernel.same_container
  cases this with
  | none => simp [spec_ok]
  | some t =>
    cases other with
    | none => simp [spec_ok]
    | some o =>
      by_cases e : o = t
      · have e' : (o = t) = True := eq_true e
        simp only [e', ↓reduceIte, spec_ok]
        constructor
        · intro hs
          exact Or.inr ⟨t, rfl, by rw [e], hs⟩
        · rintro (hn | ⟨t', _, _, hs⟩)
          · cases hn
          · exact hs
      · simp only [e, ↓reduceIte, spec_ok]
        constructor
        · intro hf
          cases hf
        · rintro (hn | ⟨t', ht, ho, _⟩)
          · cases hn
          · exact absurd ((Option.some.inj ho).trans (Option.some.inj ht).symm) e

/-! ## The walk up the type tree -/

/-- **`check_direct_cycle`**: the type is its own parent. -/
theorem check_direct_cycle_spec (inner parent : Std.U32) :
    doc_kernel.check_direct_cycle inner parent ⦃ b => (b = true ↔ inner = parent) ⦄ := by
  unfold doc_kernel.check_direct_cycle
  simp only [spec_ok, decide_eq_true_eq]

/-- What a step of the walk says. -/
inductive Walk where
  | cycle
  | exhausted
  | next (rest : Nat)

def toWalk : doc_kernel.ParentWalkStep → Walk
  | .Cycle => Walk.cycle
  | .Exhausted => Walk.exhausted
  | .Continue rest => Walk.next rest.val

section Walking

variable {α : Type} [DecidableEq α]

/-- A step of the walk at the type `current`, with `remaining` steps left. -/
def stepN (inner current : α) : Nat → Walk
  | 0 => if current = inner then Walk.cycle else Walk.exhausted
  | rest + 1 => if current = inner then Walk.cycle else Walk.next rest

theorem stepN_cycle {inner current : α} (h : current = inner) (n : Nat) :
    stepN inner current n = Walk.cycle := by
  cases n <;> simp [stepN, h]

theorem stepN_zero {inner current : α} (h : ¬ current = inner) :
    stepN inner current 0 = Walk.exhausted := by
  simp [stepN, h]

theorem stepN_succ {inner current : α} (h : ¬ current = inner) (rest : Nat) :
    stepN inner current (rest + 1) = Walk.next rest := by
  simp [stepN, h]

/-- The walk from `ancestor` up, with `remaining` steps left: whether it
meets `inner`. This is the loop of `TypeArena::is_above`. -/
def walkN (parent : α → Option α) (inner : α) : Nat → Option α → Bool
  | _, none => false
  | 0, some current => decide (current = inner)
  | rest + 1, some current =>
    if current = inner then true else walkN parent inner rest (parent current)

/-- The walk is its step, again and again. -/
theorem walkN_step (parent : α → Option α) (inner current : α) (remaining : Nat) :
    walkN parent inner remaining (some current) =
      match stepN inner current remaining with
      | Walk.cycle => true
      | Walk.exhausted => false
      | Walk.next rest => walkN parent inner rest (parent current) := by
  by_cases h : current = inner
  · rw [stepN_cycle h]
    cases remaining <;> simp [walkN, h]
  · cases remaining with
    | zero =>
      rw [stepN_zero h]
      simp [walkN, h]
    | succ rest =>
      rw [stepN_succ h]
      simp [walkN, h]

/-- The type `k` steps above `a`: its parent, `k` times. -/
def above (parent : α → Option α) : Nat → Option α → Option α
  | 0, a => a
  | k + 1, a => above parent k (a.bind parent)

/-- `inner` is `start` or a type above it. -/
def Reach (parent : α → Option α) (inner : α) (start : Option α) : Prop :=
  ∃ k, above parent k start = some inner

omit [DecidableEq α] in
theorem above_none (parent : α → Option α) (k : Nat) : above parent k none = none := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

omit [DecidableEq α] in
theorem above_add (parent : α → Option α) (a b : Nat) (s : Option α) :
    above parent (a + b) s = above parent b (above parent a s) := by
  induction a generalizing s with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ a ih =>
    rw [Nat.succ_add]
    exact ih (s.bind parent)

/-- A type the walk reaches within the steps it is given is found. -/
theorem walkN_of_above (parent : α → Option α) (inner : α) :
    ∀ (k remaining : Nat) (start : Option α), above parent k start = some inner →
      k ≤ remaining → walkN parent inner remaining start = true := by
  intro k
  induction k with
  | zero =>
    intro remaining start h _
    have e : start = some inner := h
    rw [e]
    cases remaining <;> simp [walkN]
  | succ k ih =>
    intro remaining start h hle
    cases start with
    | none =>
      rw [above_none] at h
      cases h
    | some current =>
      obtain ⟨rest, e⟩ : ∃ rest, remaining = rest + 1 := ⟨remaining - 1, by omega⟩
      rw [e]
      by_cases hc : current = inner
      · simp [walkN, hc]
      · have h' : above parent k (parent current) = some inner := h
        have := ih rest (parent current) h' (by omega)
        simp [walkN, hc, this]

/-- A type the walk finds is `start` or above it, within the steps the walk
was given. -/
theorem above_of_walkN (parent : α → Option α) (inner : α) :
    ∀ (remaining : Nat) (start : Option α), walkN parent inner remaining start = true →
      ∃ k, k ≤ remaining ∧ above parent k start = some inner := by
  intro remaining
  induction remaining with
  | zero =>
    intro start h
    cases start with
    | none => simp [walkN] at h
    | some current =>
      have e : current = inner := by simpa [walkN] using h
      exact ⟨0, Nat.le_refl _, by rw [e]; rfl⟩
  | succ rest ih =>
    intro start h
    cases start with
    | none => simp [walkN] at h
    | some current =>
      by_cases hc : current = inner
      · exact ⟨0, Nat.zero_le _, by rw [hc]; rfl⟩
      · have h' : walkN parent inner rest (parent current) = true := by
          simpa [walkN, hc] using h
        obtain ⟨k, hk, hab⟩ := ih (parent current) h'
        exact ⟨k + 1, by omega, hab⟩

/-- The pigeonhole: more places than there are values to put there hold a
value twice. -/
theorem exists_repeat {β : Type} [DecidableEq β] :
    ∀ (k : Nat) (S : List β) (f : Nat → β), S.length < k → (∀ i, i < k → f i ∈ S) →
      ∃ i j, i < j ∧ j < k ∧ f i = f j := by
  intro k
  induction k with
  | zero =>
    intro S f h _
    exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro S f hlen hmem
    by_cases hrep : ∃ i, i < k ∧ f i = f k
    · obtain ⟨i, hi, e⟩ := hrep
      exact ⟨i, k, hi, Nat.lt_succ_self k, e⟩
    · have hk : f k ∈ S := hmem k (Nat.lt_succ_self k)
      have hpos : 0 < S.length := List.length_pos_of_mem hk
      have hlen' : (S.erase (f k)).length < k := by
        rw [List.length_erase_of_mem hk]
        omega
      have hmem' : ∀ i, i < k → f i ∈ S.erase (f k) := by
        intro i hi
        have hne : f i ≠ f k := fun e => hrep ⟨i, hi, e⟩
        exact (List.mem_erase_of_ne hne).mpr (hmem i (by omega))
      obtain ⟨i, j, hij, hj, e⟩ := ih (S.erase (f k)) f hlen' hmem'
      exact ⟨i, j, hij, by omega, e⟩

omit [DecidableEq α] in
/-- A type `k` steps above `start`, when the walk does not end before: the
types on the way have a parent, so they are types of `S`. -/
theorem above_mem (parent : α → Option α) (S : List α)
    (hS : ∀ v p, parent v = some p → v ∈ S) {k : Nat} {start : Option α} {inner : α}
    (h : above parent k start = some inner) (i : Nat) (hi : i < k) :
    above parent i start ∈ S.map some := by
  obtain ⟨d, hd⟩ : ∃ d, k = i + (d + 1) := ⟨k - i - 1, by omega⟩
  rw [hd, above_add] at h
  cases hv : above parent i start with
  | none =>
    rw [hv, above_none] at h
    cases h
  | some v =>
    rw [hv] at h
    have h' : above parent d (parent v) = some inner := h
    cases hp : parent v with
    | none =>
      rw [hp, above_none] at h'
      cases h'
    | some p => exact List.mem_map.mpr ⟨v, hS v p hp, rfl⟩

/-- **A type above another one is within as many steps as there are types
that have a parent.** A longer way up goes through a type twice, and the part
between the two visits can be left out. -/
theorem reach_bounded (parent : α → Option α) (S : List α)
    (hS : ∀ v p, parent v = some p → v ∈ S) (inner : α) (start : Option α) :
    ∀ k, above parent k start = some inner →
      ∃ k', k' ≤ S.length ∧ above parent k' start = some inner := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro h
    by_cases hle : k ≤ S.length
    · exact ⟨k, hle, h⟩
    · have hlen : (S.map some).length < k := by
        rw [List.length_map]
        omega
      obtain ⟨i, j, hij, hj, e⟩ :=
        exists_repeat k (S.map some) (fun i => above parent i start) hlen
          (fun i hi => above_mem parent S hS h i hi)
      have e' : above parent i start = above parent j start := e
      obtain ⟨d, hd⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
      have hshort : above parent (i + d) start = some inner := by
        rw [above_add, e', ← above_add, ← hd]
        exact h
      exact ih (i + d) (by omega) hshort

/-- **The walk that is given as many steps as there are types with a parent
answers whether the type is above the other one.** `S` lists the types that
have a parent (the types of the arena: `TypeArena::parent_of` answers for a
stored type only) and the walk has at least `S.length` steps. However the
types above `start` loop, it ends, and it finds `inner` exactly when `inner`
is `start` or above it. -/
theorem walk_iff_reach (parent : α → Option α) (S : List α)
    (hS : ∀ v p, parent v = some p → v ∈ S) (inner : α) (start : Option α) (n : Nat)
    (hn : S.length ≤ n) :
    walkN parent inner n start = true ↔ Reach parent inner start := by
  constructor
  · intro h
    obtain ⟨k, _, hk⟩ := above_of_walkN parent inner n start h
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    obtain ⟨k', hk', hab⟩ := reach_bounded parent S hS inner start k hk
    exact walkN_of_above parent inner k' n start hab (by omega)

/-- More steps than there are types change nothing. -/
theorem walkN_steps (parent : α → Option α) (S : List α)
    (hS : ∀ v p, parent v = some p → v ∈ S) (inner : α) (start : Option α) (n m : Nat)
    (hn : S.length ≤ n) (hm : S.length ≤ m) :
    walkN parent inner n start = walkN parent inner m start := by
  have h1 := walk_iff_reach parent S hS inner start n hn
  have h2 := walk_iff_reach parent S hS inner start m hm
  cases e1 : walkN parent inner n start with
  | true =>
    exact (h2.mpr (h1.mp e1)).symm
  | false =>
    cases e2 : walkN parent inner m start with
    | false => rfl
    | true =>
      have := h1.mpr (h2.mp e2)
      rw [e1] at this
      cases this

end Walking

/-- **`parent_walk_step` is the step of the walk.** -/
@[step]
theorem parent_walk_step_spec (inner current : Std.U32) (remaining : Std.Usize) :
    doc_kernel.parent_walk_step inner current remaining ⦃ r =>
      toWalk r = stepN inner current remaining.val ⦄ := by
  unfold doc_kernel.parent_walk_step
  by_cases hc : current = inner
  · have hc' : (current = inner) = True := eq_true hc
    simp only [hc', ↓reduceIte, spec_ok]
    rw [stepN_cycle hc]
    rfl
  · simp only [hc, ↓reduceIte]
    by_cases hz : remaining = 0#usize
    · have hz' : (remaining = 0#usize) = True := eq_true hz
      simp only [hz', ↓reduceIte, spec_ok]
      have hv : remaining.val = 0 := by
        rw [hz]
        exact usize_zero_val
      rw [hv, stepN_zero hc]
      rfl
    · simp only [hz, ↓reduceIte]
      have hpos : 0 < remaining.val := by
        apply Nat.pos_of_ne_zero
        intro h0
        apply hz
        apply UScalar.eq_of_val_eq
        rw [h0, usize_zero_val]
      step as ⟨i, hi⟩
      have hv : remaining.val = i.val + 1 := by scalar_tac
      rw [hv, stepN_succ hc]
      rfl

/-- The loop of `TypeArena::is_above`, with the extracted step: `fuel` only
says that the loop ends, which the steps left do. -/
def walk (parent : Std.U32 → Option Std.U32) (inner : Std.U32) :
    Nat → Option Std.U32 → Std.Usize → Result Bool
  | _, none, _ => ok false
  | 0, some _, _ => ok false
  | fuel + 1, some current, remaining => do
    let step ← doc_kernel.parent_walk_step inner current remaining
    match step with
    | .Cycle => ok true
    | .Exhausted => ok false
    | .Continue rest => walk parent inner fuel (parent current) rest

/-- **The loop with the extracted step is the walk**, for any fuel that
covers the steps it is given. -/
theorem walk_spec (parent : Std.U32 → Option Std.U32) (inner : Std.U32) :
    ∀ (fuel : Nat) (ancestor : Option Std.U32) (remaining : Std.Usize),
      remaining.val < fuel →
      walk parent inner fuel ancestor remaining ⦃ b =>
        b = walkN parent inner remaining.val ancestor ⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro ancestor remaining h
    exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro ancestor remaining hfuel
    cases ancestor with
    | none =>
      unfold walk
      simp only [spec_ok]
      cases remaining.val <;> rfl
    | some current =>
      unfold walk
      step with parent_walk_step_spec inner current remaining as ⟨st, hst⟩
      rw [walkN_step]
      rw [← hst]
      cases st with
      | Cycle =>
        simp only [spec_ok]
        rfl
      | Exhausted =>
        simp only [spec_ok]
        rfl
      | Continue rest =>
        simp only []
        have hrest : rest.val < remaining.val := by
          by_cases hc : current = inner
          · rw [stepN_cycle hc] at hst
            cases hst
          · cases hr : remaining.val with
            | zero =>
              rw [hr, stepN_zero hc] at hst
              cases hst
            | succ m =>
              rw [hr, stepN_succ hc] at hst
              have e : rest.val = m := by
                have := hst
                simp only [toWalk] at this
                exact Walk.next.inj this
              omega
        exact ih (parent current) rest (by omega)

/-! ## The conflict scan is needed -/

/-- Whether other items may sit between the two neighbours of a new item. -/
def needsScanK (has_left : Bool) (left_right right right_left : Option Std.U32) : Bool :=
  if has_left then decide (left_right ≠ right)
  else
    match right with
    | none => true
    | some _ => right_left.isSome

/-- **`needs_conflict_scan`**: with a left neighbour, unless the right one
follows it; without one, unless the right one is the first item. -/
@[step]
theorem needs_conflict_scan_spec (has_left : Bool) (left_right right right_left : Option Std.U32) :
    doc_kernel.needs_conflict_scan has_left left_right right right_left ⦃ b =>
      b = needsScanK has_left left_right right right_left ⦄ := by
  unfold doc_kernel.needs_conflict_scan
  cases has_left with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases right <;> cases right_left <;> simp [spec_ok, needsScanK]
  | true =>
    simp only [↓reduceIte]
    step with opt_slot_eq_raw left_right right as ⟨b, hb⟩
    by_cases e : left_right = right
    · have hbt : b = true := hb.mpr e
      simp [needsScanK, hbt, e]
    · have hbf : b = false := bool_false_of_not (fun hbt => e (hb.mp hbt))
      simp [needsScanK, hbf, e]

/-! ## Linking an item -/

/-- What linking an item does besides making it the neighbour of its
neighbours. -/
def linkPlan (has_left has_right is_map_entry parent_deleted countable : Bool) :
    doc_kernel.IntegrateLinkPlan :=
  { set_list_start := !has_left && !is_map_entry
    set_map_winner := is_map_entry && !has_right
    delete_prev_map_winner := is_map_entry && !has_right && has_left
    delete_self := parent_deleted || (is_map_entry && has_right)
    add_list_len := !(parent_deleted || (is_map_entry && has_right)) && !is_map_entry && countable }

/-- **`decide_integrate_link` is `linkPlan`**, on every input. -/
@[step]
theorem decide_integrate_link_spec (has_left has_right is_map_entry parent_deleted countable : Bool) :
    doc_kernel.decide_integrate_link has_left has_right is_map_entry parent_deleted countable ⦃ p =>
      p = linkPlan has_left has_right is_map_entry parent_deleted countable ⦄ := by
  unfold doc_kernel.decide_integrate_link
  cases has_left <;> cases has_right <;> cases is_map_entry <;> cases parent_deleted <;>
    cases countable <;> simp [spec_ok, linkPlan]

theorem decide_integrate_link_eq (has_left has_right is_map_entry parent_deleted countable : Bool) :
    doc_kernel.decide_integrate_link has_left has_right is_map_entry parent_deleted countable =
      ok (linkPlan has_left has_right is_map_entry parent_deleted countable) := by
  obtain ⟨p, e, hp⟩ := ok_of_spec
    (decide_integrate_link_spec has_left has_right is_map_entry parent_deleted countable)
  rw [e, hp]

/-! ### Last writer wins

The values under a map key are a list (the YATA list of the key) and the value
of the key is its last item, when that is not deleted. Here a list of a key is
its values in order, each with whether it is deleted. -/

section Lww

variable {α : Type}

/-- Every value of the key but the last one is deleted. -/
def Lww (chain : List (α × Bool)) : Prop :=
  ∀ (i : Nat) (e : α × Bool), chain[i]? = some e → i + 1 < chain.length → e.2 = true

/-- The value of the key: its last value, unless that is deleted. -/
def winner (chain : List (α × Bool)) : Option α :=
  match chain.getLast? with
  | some (x, false) => some x
  | _ => none

def markDeleted (e : α × Bool) : α × Bool := (e.1, true)

/-- The list of a key after the value `x` was linked at the place `k`, as
`plan` says: the value before it is deleted when the plan says so, and the
value itself is there deleted or not as the plan says. -/
def linkAt (chain : List (α × Bool)) (k : Nat) (x : α) (plan : doc_kernel.IntegrateLinkPlan) :
    List (α × Bool) :=
  insAt (if plan.delete_prev_map_winner = true then upd chain (k - 1) markDeleted else chain) k
    (x, plan.delete_self)

theorem lww_nil : Lww ([] : List (α × Bool)) := by
  intro i e h
  simp at h

/-- Deleting a value keeps the invariant. -/
theorem lww_delete {chain : List (α × Bool)} (h : Lww chain) (i : Nat) :
    Lww (upd chain i markDeleted) := by
  intro j e hj hlt
  rw [length_upd] at hlt
  rcases get?_upd_cases hj with ⟨_, a, _, rfl⟩ | ⟨_, hj'⟩
  · rfl
  · exact h j e hj' hlt

/-- **A value linked as `decide_integrate_link` says keeps every value of its
key but the last one deleted**, wherever in the list of the key the conflict
scan puts it: at the end it takes the key and the value before it is deleted,
anywhere else it is deleted itself. -/
theorem lww_integrate {chain : List (α × Bool)} (h : Lww chain) (k : Nat) (x : α)
    (hk : k ≤ chain.length) (parent_deleted countable : Bool) :
    Lww (linkAt chain k x
      (linkPlan (decide (0 < k)) (decide (k < chain.length)) true parent_deleted countable)) := by
  intro i e hi hlt
  unfold linkAt at hi hlt
  rw [length_insAt] at hlt
  have hbl : (if (linkPlan (decide (0 < k)) (decide (k < chain.length)) true parent_deleted
      countable).delete_prev_map_winner = true then upd chain (k - 1) markDeleted
      else chain).length = chain.length := by
    by_cases hc : (linkPlan (decide (0 < k)) (decide (k < chain.length)) true parent_deleted
        countable).delete_prev_map_winner = true
    · simp only [hc, ↓reduceIte, length_upd]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
  rw [hbl] at hlt
  by_cases hend : k < chain.length
  · -- not at the end: the value is deleted, the others are as they were
    have hprev : (linkPlan (decide (0 < k)) (decide (k < chain.length)) true parent_deleted
        countable).delete_prev_map_winner = false := by
      simp [linkPlan, hend]
    have hself : (linkPlan (decide (0 < k)) (decide (k < chain.length)) true parent_deleted
        countable).delete_self = true := by
      simp [linkPlan, hend]
    rw [hprev, hself] at hi
    simp only [Bool.false_eq_true, ↓reduceIte] at hi
    rcases get?_insAt_cases hk hi with ⟨hq, hq'⟩ | ⟨_, rfl⟩ | ⟨q', rfl, hq, hq'⟩
    · exact h i e hq' (by omega)
    · rfl
    · exact h q' e hq' (by omega)
  · -- at the end: the value before it is deleted
    have hke : k = chain.length := by omega
    by_cases hpos : 0 < k
    · have hplan : (linkPlan (decide (0 < k)) (decide (k < chain.length)) true parent_deleted
          countable).delete_prev_map_winner = true := by
        simp [linkPlan, hend, hpos]
      rw [hplan] at hi
      simp only [↓reduceIte] at hi
      have hk' : k ≤ (upd chain (k - 1) markDeleted).length := by
        rw [length_upd]
        exact hk
      rcases get?_insAt_cases hk' hi with ⟨hq, hq'⟩ | ⟨hq, _⟩ | ⟨q', rfl, hq, _⟩
      · rcases get?_upd_cases hq' with ⟨_, a, _, rfl⟩ | ⟨hne, hq''⟩
        · rfl
        · exact h i e hq'' (by omega)
      · omega
      · omega
    · omega

/-- **At most the last value of a key is not deleted.** -/
theorem lww_unique {chain : List (α × Bool)} (h : Lww chain) {i : Nat} {e : α × Bool}
    (hi : chain[i]? = some e) (hlive : e.2 = false) : i + 1 = chain.length := by
  have hlt := get?_lt hi
  by_cases hlast : i + 1 < chain.length
  · have := h i e hi hlast
    rw [hlive] at this
    cases this
  · omega

/-- Two values of a key that are not deleted are the same value. -/
theorem lww_one {chain : List (α × Bool)} (h : Lww chain) {i j : Nat} {a b : α × Bool}
    (hi : chain[i]? = some a) (hj : chain[j]? = some b) (ha : a.2 = false) (hb : b.2 = false) :
    i = j := by
  have h1 := lww_unique h hi ha
  have h2 := lww_unique h hj hb
  omega

/-- **The deletions last writer wins makes are read off the list.** Two lists
of a key that hold the same values in the same order, and agree on whether the
last one is deleted, are the same list: which values were deleted for coming
before another one does not depend on the order they were linked in. -/
theorem lww_determined {c₁ c₂ : List (α × Bool)} (h₁ : Lww c₁) (h₂ : Lww c₂)
    (hvals : c₁.map Prod.fst = c₂.map Prod.fst)
    (hlast : ∀ e₁ e₂, c₁.getLast? = some e₁ → c₂.getLast? = some e₂ → e₁.2 = e₂.2) :
    c₁ = c₂ := by
  have hlen : c₁.length = c₂.length := by
    have := congrArg List.length hvals
    simpa using this
  apply ext_get?
  intro i
  cases hi₁ : c₁[i]? with
  | none =>
    have : c₂.length ≤ i := by
      have := get?_none_le hi₁
      omega
    rw [get?_none this]
  | some a =>
    have hlt₁ := get?_lt hi₁
    obtain ⟨b, hi₂⟩ := get?_some (l := c₂) (i := i) (by omega)
    rw [hi₂]
    have hfst : a.1 = b.1 := by
      have e₁ : (c₁.map Prod.fst)[i]? = some a.1 := by rw [get?_map, hi₁]; rfl
      have e₂ : (c₂.map Prod.fst)[i]? = some b.1 := by rw [get?_map, hi₂]; rfl
      rw [hvals, e₂] at e₁
      exact (Option.some.inj e₁).symm
    have hsnd : a.2 = b.2 := by
      by_cases hl : i + 1 < c₁.length
      · rw [h₁ i a hi₁ hl, h₂ i b hi₂ (by omega)]
      · have hlast₁ : c₁.getLast? = some a := by
          rw [List.getLast?_eq_getElem?]
          have : c₁.length - 1 = i := by omega
          rw [this]
          exact hi₁
        have hlast₂ : c₂.getLast? = some b := by
          rw [List.getLast?_eq_getElem?]
          have : c₂.length - 1 = i := by omega
          rw [this]
          exact hi₂
        exact hlast a b hlast₁ hlast₂
    cases a with
    | mk a1 a2 =>
      cases b with
      | mk b1 b2 =>
        have e1 : a1 = b1 := hfst
        have e2 : a2 = b2 := hsnd
        rw [e1, e2]

/-- A value linked at the end of the list of its key, in a parent that is
not deleted, is the value of the key. -/
theorem winner_link_end (chain : List (α × Bool)) (x : α) (countable : Bool) :
    winner (linkAt chain chain.length x
      (linkPlan (decide (0 < chain.length)) (decide (chain.length < chain.length)) true false
        countable)) = some x := by
  have hself : (linkPlan (decide (0 < chain.length)) (decide (chain.length < chain.length)) true
      false countable).delete_self = false := by
    simp [linkPlan]
  have hbl : (if (linkPlan (decide (0 < chain.length)) (decide (chain.length < chain.length))
      true false countable).delete_prev_map_winner = true
      then upd chain (chain.length - 1) markDeleted else chain).length = chain.length := by
    by_cases hc : (linkPlan (decide (0 < chain.length)) (decide (chain.length < chain.length))
        true false countable).delete_prev_map_winner = true
    · simp only [hc, ↓reduceIte, length_upd]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
  have hlast : (linkAt chain chain.length x
      (linkPlan (decide (0 < chain.length)) (decide (chain.length < chain.length)) true false
        countable)).getLast? = some (x, false) := by
    rw [List.getLast?_eq_getElem?]
    unfold linkAt
    rw [length_insAt, hbl, hself, Nat.add_sub_cancel]
    exact get?_insAt_self _ _ (by omega)
  unfold winner
  rw [hlast]

/-- The lists of a key a replica can reach: values linked as
`decide_integrate_link` says, each at whatever place of the list the conflict
scan puts it, in a parent that is deleted or not, and values deleted. -/
inductive KeyRun : List (α × Bool) → Prop
  | empty : KeyRun []
  | link (chain : List (α × Bool)) (k : Nat) (x : α) (parent_deleted countable : Bool) :
      KeyRun chain → k ≤ chain.length →
      KeyRun (linkAt chain k x
        (linkPlan (decide (0 < k)) (decide (k < chain.length)) true parent_deleted countable))
  | delete (chain : List (α × Bool)) (i : Nat) : KeyRun chain → KeyRun (upd chain i markDeleted)

/-- **Every list of a key a replica can reach has all its values deleted but
the last one.** -/
theorem keyRun_lww {chain : List (α × Bool)} (h : KeyRun chain) : Lww chain := by
  induction h with
  | empty => exact lww_nil
  | link chain k x parent_deleted countable _ hk ih =>
    exact lww_integrate ih k x hk parent_deleted countable
  | delete chain i _ ih => exact lww_delete ih i

/-- **Last writer wins converges.** Two replicas whose lists of a key hold
the same values in the same order (what the conflict scan gives replicas
that hold the same structs, `Refinement.core_sec_ids`), and agree on whether
the last one was deleted, hold the same list, deletions included, and read
the same value: whatever order the values came in at each. -/
theorem keyRun_sec {c₁ c₂ : List (α × Bool)} (h₁ : KeyRun c₁) (h₂ : KeyRun c₂)
    (hvals : c₁.map Prod.fst = c₂.map Prod.fst)
    (hlast : ∀ e₁ e₂, c₁.getLast? = some e₁ → c₂.getLast? = some e₂ → e₁.2 = e₂.2) :
    c₁ = c₂ ∧ winner c₁ = winner c₂ := by
  have e := lww_determined (keyRun_lww h₁) (keyRun_lww h₂) hvals hlast
  exact ⟨e, by rw [e]⟩

end Lww

/-! ## Two items are one -/

/-- **`follows_in_list`**: each of the two items names the other as its
neighbour. -/
@[step]
theorem follows_in_list_spec (left_right : Option Std.U32) (l : Std.U32)
    (right_left : Option Std.U32) (r : Std.U32) :
    doc_kernel.follows_in_list left_right l right_left r ⦃ b =>
      (b = true ↔ left_right = some r ∧ right_left = some l) ⦄ := by
  unfold doc_kernel.follows_in_list
  step with slot_is_raw left_right r as ⟨b, hb⟩
  by_cases hbt : b = true
  · simp only [hbt, ↓reduceIte]
    refine spec_mono (slot_is_raw right_left l) ?_
    intro b1 hb1
    exact ⟨fun e => ⟨hb.mp hbt, hb1.mp e⟩, fun hh => hb1.mpr hh.2⟩
  · simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
    constructor
    · intro e
      cases e
    · rintro ⟨h1, _⟩
      exact absurd (hb.mpr h1) hbt

/-- `right` (slot `r`) follows `left` (slot `l`) in the list and continues
it. -/
structure CanMerge (left : doc_kernel.MergeSide) (l : Std.U32) (right : doc_kernel.MergeSide)
    (r : Std.U32) : Prop where
  /-- they are neighbours -/
  right_of : left.right = some r
  left_of : right.left = some l
  /-- of the same client -/
  client : left.id.client = right.id.client
  /-- the left one has clocks, and they fit a `u64` -/
  pos : 0 < left.len.val
  fits : left.id.clock.val + left.len.val ≤ Std.U64.max
  /-- the first clock of the right one is the next clock -/
  next : left.id.clock.val + left.len.val = right.id.clock.val
  /-- it was typed right after the last clock of the left one -/
  typed : ∃ o, right.origin_left = some o ∧ o.client = left.id.client ∧
    o.clock.val = left.id.clock.val + left.len.val - 1
  /-- with the same right origin -/
  origin : left.origin_right = right.origin_right

/-- **`can_merge_items` answers whether the right item continues the left one
in one list.** It is total: the clocks of an item that has none, or whose
clocks do not fit, are not computed. -/
@[step]
theorem can_merge_items_spec (left : doc_kernel.MergeSide) (l : Std.U32)
    (right : doc_kernel.MergeSide) (r : Std.U32) (same_container : Bool) :
    doc_kernel.can_merge_items left l right r same_container ⦃ b =>
      (b = true ↔ CanMerge left l right r ∧ same_container = true) ⦄ := by
  unfold doc_kernel.can_merge_items
  have no : ∀ (P : Prop), ¬ P → (CanMerge left l right r → P) →
      ((false = true) ↔ CanMerge left l right r ∧ same_container = true) := by
    intro P hnp hp
    constructor
    · intro e
      cases e
    · rintro ⟨hc, _⟩
      exact absurd (hp hc) hnp
  have no' : ∀ (P : Prop), ¬ P → (CanMerge left l right r → P) →
      (False ↔ CanMerge left l right r ∧ same_container = true) := by
    intro P hnp hp
    constructor
    · intro e
      exact e.elim
    · rintro ⟨hc, _⟩
      exact absurd (hp hc) hnp
  step with follows_in_list_spec left.right l right.left r as ⟨b, hb⟩
  by_cases hbt : b = true
  · simp only [hbt, ↓reduceIte]
    have h1 := (hb.mp hbt).1
    have h2 := (hb.mp hbt).2
    cases hne : (left.id.client != right.id.client) with
    | true =>
      simp only [↓reduceIte, spec_ok]
      exact no _ (bne_true_ne hne) (fun hc => hc.client)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h3 : left.id.client = right.id.client := bne_false_eq hne
      by_cases hz : left.len = 0#u64
      · have hz' : (left.len = 0#u64) = True := eq_true hz
        simp only [hz', ↓reduceIte, spec_ok]
        have hzv : ¬ 0 < left.len.val := by
          rw [hz]
          exact Nat.lt_irrefl 0
        exact no _ hzv (fun hc => hc.pos)
      · simp only [hz, ↓reduceIte]
        have h4 : 0 < left.len.val := by scalar_tac
        have hMax : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
        have hle : left.len.val ≤ (core.num.U64.MAX : Std.U64).val := by
          rw [hMax]
          scalar_tac
        step as ⟨i, hi⟩
        have hiv : i.val = 2 ^ 64 - 1 - left.len.val := by
          rw [← hMax]
          scalar_tac
        by_cases hover : left.id.clock > i
        · simp only [hover, ↓reduceIte, spec_ok]
          have hnf : ¬ left.id.clock.val + left.len.val ≤ Std.U64.max := by scalar_tac
          exact no _ hnf (fun hc => hc.fits)
        · simp only [hover, ↓reduceIte]
          have h5 : left.id.clock.val + left.len.val ≤ Std.U64.max := by scalar_tac
          step as ⟨i1, hi1⟩
          have hi1v : i1.val = left.id.clock.val + left.len.val := by scalar_tac
          cases hgap : (i1 != right.id.clock) with
          | true =>
            simp only [↓reduceIte, spec_ok]
            have hn : ¬ left.id.clock.val + left.len.val = right.id.clock.val := by
              intro e
              apply bne_true_ne hgap
              apply UScalar.eq_of_val_eq
              rw [hi1v, e]
            exact no _ hn (fun hc => hc.next)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            have h6 : left.id.clock.val + left.len.val = right.id.clock.val := by
              have e : i1 = right.id.clock := bne_false_eq hgap
              rw [← e, hi1v]
            refine spec_bind (?_ : spec _ (fun (al : Bool) => (al = true ↔
              ∃ o, right.origin_left = some o ∧ o.client = left.id.client ∧
                o.clock.val = left.id.clock.val + left.len.val - 1))) (fun al hal => ?_)
            · cases hro : right.origin_left with
              | none =>
                simp only [spec_ok]
                constructor
                · intro e
                  cases e
                · rintro ⟨o, e, _⟩
                  cases e
              | some origin =>
                simp only []
                by_cases hcl : origin.client = left.id.client
                · have hcl' : (origin.client = left.id.client) = True := eq_true hcl
                  simp only [hcl', ↓reduceIte]
                  step as ⟨i2, hi2⟩
                  have hi2v : i2.val = left.len.val - 1 := by scalar_tac
                  step as ⟨i3, hi3⟩
                  have hi3v : i3.val = left.id.clock.val + left.len.val - 1 := by scalar_tac
                  simp only [decide_eq_true_eq]
                  constructor
                  · intro e
                    refine ⟨origin, rfl, hcl, ?_⟩
                    rw [e, hi3v]
                  · rintro ⟨o, e, _, hck⟩
                    cases e
                    apply UScalar.eq_of_val_eq
                    rw [hck, hi3v]
                · simp only [hcl, ↓reduceIte, spec_ok]
                  constructor
                  · intro e
                    cases e
                  · rintro ⟨o, e, hoc, _⟩
                    cases e
                    exact absurd hoc hcl
            · by_cases halt : al = true
              · simp only [halt, ↓reduceIte]
                have h7 := hal.mp halt
                step with opt_id_eq_raw left.origin_right right.origin_right as ⟨b2, hb2⟩
                by_cases hb2t : b2 = true
                · simp only [hb2t, ↓reduceIte, spec_ok]
                  have h8 := hb2.mp hb2t
                  exact ⟨fun e => ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, e⟩, fun hh => hh.2⟩
                · simp only [hb2t, Bool.false_eq_true, ↓reduceIte, spec_ok]
                  exact no' _ (fun e => hb2t (hb2.mpr e)) (fun hc => hc.origin)
              · simp only [halt, Bool.false_eq_true, ↓reduceIte, spec_ok]
                exact no' _ (fun e => halt (hal.mpr e)) (fun hc => hc.typed)
  · simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
    exact no' _ (fun e => hbt (hb.mpr e)) (fun hc => ⟨hc.right_of, hc.left_of⟩)

/-- **The list is asked apart**: what `can_merge_items` answers for two items
is what it answers for two items of one list, and whether they are in one
list. `DocStore::merge_items` asks in this order, the list last. -/
theorem can_merge_items_and (left : doc_kernel.MergeSide) (l : Std.U32)
    (right : doc_kernel.MergeSide) (r : Std.U32) (same_container : Bool) :
    ∃ b b', doc_kernel.can_merge_items left l right r same_container = ok b ∧
      doc_kernel.can_merge_items left l right r true = ok b' ∧
      b = (b' && same_container) := by
  obtain ⟨b, e, hb⟩ := ok_of_spec (can_merge_items_spec left l right r same_container)
  obtain ⟨b', e', hb'⟩ := ok_of_spec (can_merge_items_spec left l right r true)
  refine ⟨b, b', e, e', ?_⟩
  by_cases hc : CanMerge left l right r
  · have hb't : b' = true := hb'.mpr ⟨hc, rfl⟩
    cases same_container with
    | true =>
      have hbt : b = true := hb.mpr ⟨hc, rfl⟩
      rw [hbt, hb't]
      rfl
    | false =>
      have hbf : b = false := bool_false_of_not (fun hbt => by
        have := (hb.mp hbt).2
        cases this)
      rw [hbf, hb't]
      rfl
  · have hbf : b = false := bool_false_of_not (fun hbt => hc (hb.mp hbt).1)
    have hb'f : b' = false := bool_false_of_not (fun hbt => hc (hb'.mp hbt).1)
    rw [hbf, hb'f]
    rfl

/-! ## Cuts -/

/-- How many items and blocks two cuts add. -/
def cutCount (split_start split_end : Bool) : Std.Usize :=
  match split_start, split_end with
  | true, true => 2#usize
  | true, false => 1#usize
  | false, true => 1#usize
  | false, false => 0#usize

theorem cutCount_val (split_start split_end : Bool) :
    (cutCount split_start split_end).val = split_start.toNat + split_end.toNat := by
  cases split_start <;> cases split_end <;> rfl

/-- **`cuts_live_item`**: a live item is cut at a clock it holds after its
first one, and nothing else is cut. -/
@[step]
theorem cuts_live_item_spec (live_item : Bool) (first_clock «at» : Std.U64) :
    doc_kernel.cuts_live_item live_item first_clock «at» ⦃ b =>
      (b = true ↔ live_item = true ∧ first_clock.val < «at».val) ⦄ := by
  unfold doc_kernel.cuts_live_item
  by_cases h : «at» > first_clock
  · have n : first_clock.val < «at».val := by scalar_tac
    cases live_item <;> simp [h, n, spec_ok]
  · have n : ¬ first_clock.val < «at».val := by scalar_tac
    cases live_item <;> simp [h, n, spec_ok]

/-- **`plan_delete_range_splits` keeps the two cuts and counts them.** -/
@[step]
theorem plan_delete_range_splits_spec (split_start split_end : Bool) :
    doc_kernel.plan_delete_range_splits split_start split_end ⦃ p =>
      p.split_start = split_start ∧ p.split_end = split_end ∧
      p.needed_splits = cutCount split_start split_end ⦄ := by
  unfold doc_kernel.plan_delete_range_splits
  cases split_start <;> cases split_end <;> simp [spec_ok, cutCount]

/-- What `plan_split_node` answers for a cut it makes. -/
structure SplitPlanOk (item_id : yata_store.IdCore) (item_len diff : Std.U64)
    (has_right has_parent has_parent_sub : Bool) (p : doc_kernel.SplitPlan) : Prop where
  /-- the right half starts at the clock `diff` of the item -/
  id_client : p.right_id.client = item_id.client
  id_clock : p.right_id.clock.val = item_id.clock.val + diff.val
  /-- and has the clocks the left half does not keep -/
  len : p.right_len.val = item_len.val - diff.val
  /-- it was typed after the last clock of the left half -/
  origin_client : p.right_origin_left.client = item_id.client
  origin_clock : p.right_origin_left.clock.val = item_id.clock.val + diff.val - 1
  /-- the key of a last item goes to it -/
  winner : p.update_map_winner = (!has_right && has_parent && has_parent_sub)

/-- **`plan_split_node` cuts an item inside its clocks**, or answers `None`:
for a cut at its first clock or past its last one, and for an item whose
clocks before the cut do not fit a `u64`. -/
@[step]
theorem plan_split_node_spec (item_id : yata_store.IdCore) (item_len diff : Std.U64)
    (has_right has_parent has_parent_sub : Bool) :
    doc_kernel.plan_split_node item_id item_len diff has_right has_parent has_parent_sub ⦃ o =>
      (o = none ∧ ¬ (0 < diff.val ∧ diff.val < item_len.val ∧
        item_id.clock.val + diff.val ≤ Std.U64.max)) ∨
      (∃ p, o = some p ∧ 0 < diff.val ∧ diff.val < item_len.val ∧
        item_id.clock.val + diff.val ≤ Std.U64.max ∧
        SplitPlanOk item_id item_len diff has_right has_parent has_parent_sub p) ⦄ := by
  unfold doc_kernel.plan_split_node
  by_cases hz : diff = 0#u64
  · have hz' : (diff = 0#u64) = True := eq_true hz
    simp only [hz', ↓reduceIte, spec_ok]
    refine Or.inl ⟨trivial, ?_⟩
    rintro ⟨hp, _⟩
    rw [hz] at hp
    exact absurd hp (Nat.lt_irrefl 0)
  · simp only [hz, ↓reduceIte]
    have hpos : 0 < diff.val := by scalar_tac
    by_cases hge : diff >= item_len
    · simp only [hge, ↓reduceIte, spec_ok]
      refine Or.inl ⟨trivial, ?_⟩
      rintro ⟨_, hlt, _⟩
      scalar_tac
    · simp only [hge, ↓reduceIte]
      have hlt : diff.val < item_len.val := by scalar_tac
      have hMax : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
      have hle : diff.val ≤ (core.num.U64.MAX : Std.U64).val := by
        rw [hMax]
        scalar_tac
      step as ⟨i, hi⟩
      have hiv : i.val = 2 ^ 64 - 1 - diff.val := by
        rw [← hMax]
        scalar_tac
      by_cases hover : item_id.clock > i
      · simp only [hover, ↓reduceIte, spec_ok]
        refine Or.inl ⟨trivial, ?_⟩
        rintro ⟨_, _, hfit⟩
        scalar_tac
      · simp only [hover, ↓reduceIte]
        have hfit : item_id.clock.val + diff.val ≤ Std.U64.max := by scalar_tac
        step as ⟨clock, hclock⟩
        have hcv : clock.val = item_id.clock.val + diff.val := by scalar_tac
        step as ⟨i1, hi1⟩
        have hi1v : i1.val = item_len.val - diff.val := by scalar_tac
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = item_id.clock.val + diff.val - 1 := by scalar_tac
        cases has_right <;> cases has_parent <;> cases has_parent_sub <;>
          simp only [Bool.false_eq_true, ↓reduceIte, spec_ok] <;>
          exact Or.inr ⟨_, rfl, hpos, hlt, hfit, ⟨rfl, hcv, hi1v, rfl, hi2v, rfl⟩⟩

/-- An item of the store is cut wherever the cut is inside its clocks: its
clocks fit a `u64`, so the ones before the cut do. -/
theorem plan_split_node_some (item_id : yata_store.IdCore) (item_len diff : Std.U64)
    (has_right has_parent has_parent_sub : Bool)
    (hfits : item_id.clock.val + item_len.val ≤ Std.U64.max) (hpos : 0 < diff.val)
    (hlt : diff.val < item_len.val) :
    ∃ p, doc_kernel.plan_split_node item_id item_len diff has_right has_parent has_parent_sub =
        ok (some p) ∧
      SplitPlanOk item_id item_len diff has_right has_parent has_parent_sub p := by
  obtain ⟨o, e, ho⟩ := ok_of_spec
    (plan_split_node_spec item_id item_len diff has_right has_parent has_parent_sub)
  rcases ho with ⟨_, hno⟩ | ⟨p, rfl, _, _, _, hp⟩
  · exact absurd ⟨hpos, hlt, by omega⟩ hno
  · exact ⟨p, e, hp⟩

end YoctoCore.Properties.DocKernel
