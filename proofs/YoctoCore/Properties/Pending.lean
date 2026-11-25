/-
`y_octo_core::pending`: what an update can apply now and what has to wait.

Every function is total on every input. `dep_missing` says whether a
dependency blocks a struct (`dep_missing_spec`): one on another client whose
clock the document does not hold. `find_missing_dependency_states` and
`find_missing_dependency` answer the first blocking dependency in the order
left origin, right origin, parent (`firstOf`).

`check_local_readiness` and `classify_ready_step` are the two steps of the
decision on a struct, and `classify_struct_step` is the two together
(`classify_struct_step_spec`): a skip, then the clocks of its own client (the
clock before the struct is named, and it is not below zero), then a missing
dependency, then the offset the struct is applied from, which is `0` or below
its length, with a state after it that is not below the state before.

`split_delete_range` cuts a range of clocks at the clocks the document holds
(`split_delete_range_spec`): every clock of the range is in exactly one part,
on its side of the state, and no part is empty.
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.StateVector

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 400000
set_option autoImplicit false

namespace YoctoCore.Properties.Pending

/-! ## Dependencies -/

/-- Whether the dependency `dep` blocks a struct of the client `c`, when the
document holds the clocks below `held` of the client of `dep`: the client of a
dependency on another client whose clock is not held. -/
def depMissing (c : Std.U64) (dep : Option yata_store.IdCore) (held : Nat) : Option Std.U64 :=
  match dep with
  | none => none
  | some d => if d.client = c then none else if held ≤ d.clock.val then some d.client else none

/-- The first of three answers that is one. -/
def firstOf (a b c : Option Std.U64) : Option Std.U64 :=
  match a with
  | some x => some x
  | none =>
    match b with
    | some y => some y
    | none => c

theorem bne_true_ne {a b : Std.U64} (h : (a != b) = true) : ¬ a = b := by
  intro e
  rw [e] at h
  simp at h

theorem bne_false_eq {a b : Std.U64} (h : (a != b) = false) : a = b := by
  by_contra hne
  have ht : (a != b) = true := bne_iff_ne.mpr hne
  rw [h] at ht
  cases ht

/-- **`dep_missing` answers whether the dependency blocks.** -/
@[step]
theorem dep_missing_spec (c : Std.U64) (dep : Option yata_store.IdCore) (held : Std.U64) :
    pending.dep_missing c dep held ⦃ r => r = depMissing c dep held.val ⦄ := by
  unfold pending.dep_missing
  cases dep with
  | none =>
    simp only [spec_ok]
    rfl
  | some d =>
    simp only []
    cases hb : (d.client != c) with
    | false =>
      have e : d.client = c := bne_false_eq hb
      simp only [Bool.false_eq_true, ↓reduceIte, spec_ok]
      unfold depMissing
      simp only []
      rw [ite_eq_left e]
    | true =>
      have e : ¬ d.client = c := bne_true_ne hb
      simp only [↓reduceIte]
      unfold depMissing
      simp only []
      rw [ite_eq_right e]
      by_cases hge : d.clock >= held
      · simp only [hge, ↓reduceIte, spec_ok]
        have hle : held.val ≤ d.clock.val := by scalar_tac
        rw [ite_eq_left hle]
      · simp only [hge, ↓reduceIte, spec_ok]
        have hle : ¬ held.val ≤ d.clock.val := by scalar_tac
        rw [ite_eq_right hle]

/-- A dependency on the client of the struct never blocks, whatever the
document holds. -/
theorem depMissing_same (c : Std.U64) (d : yata_store.IdCore) (held : Nat) (h : d.client = c) :
    depMissing c (some d) held = none := by
  unfold depMissing
  simp only []
  rw [ite_eq_left h]

theorem depMissing_none (c : Std.U64) (held : Nat) : depMissing c none held = none := rfl

/-- What blocks, when it blocks: another client, at a clock that is not
held. -/
theorem depMissing_some {c : Std.U64} {dep : Option yata_store.IdCore} {held : Nat} {x : Std.U64}
    (h : depMissing c dep held = some x) :
    ∃ d, dep = some d ∧ x = d.client ∧ d.client ≠ c ∧ held ≤ d.clock.val := by
  cases dep with
  | none => cases h
  | some d =>
    unfold depMissing at h
    simp only [] at h
    by_cases e : d.client = c
    · rw [ite_eq_left e] at h
      cases h
    · rw [ite_eq_right e] at h
      by_cases hle : held ≤ d.clock.val
      · rw [ite_eq_left hle] at h
        exact ⟨d, rfl, (Option.some.inj h).symm, e, hle⟩
      · rw [ite_eq_right hle] at h
        cases h

/-- **`find_missing_dependency_states` answers the first dependency that
blocks**: left origin, right origin, then parent. -/
@[step]
theorem find_missing_dependency_states_spec (c : Std.U64)
    (ol : Option yata_store.IdCore) (ls : Std.U64) (or_ : Option yata_store.IdCore)
    (rs : Std.U64) (p : Option yata_store.IdCore) (ps : Std.U64) :
    pending.find_missing_dependency_states c ol ls or_ rs p ps ⦃ r =>
      r = firstOf (depMissing c ol ls.val) (depMissing c or_ rs.val) (depMissing c p ps.val) ⦄ := by
  unfold pending.find_missing_dependency_states
  step with dep_missing_spec c ol ls as ⟨o, ho⟩
  cases o with
  | some x =>
    simp only [spec_ok]
    rw [← ho]
    rfl
  | none =>
    simp only []
    step with dep_missing_spec c or_ rs as ⟨o1, ho1⟩
    cases o1 with
    | some y =>
      simp only [spec_ok]
      rw [← ho, ← ho1]
      rfl
    | none =>
      simp only []
      refine spec_mono (dep_missing_spec c p ps) ?_
      intro r hr
      rw [← ho, ← ho1, hr]
      rfl

/-- The clocks `state` holds of the client of a dependency (`0` without
one). -/
def heldOf (state : state_vector.StateVectorCore) (dep : Option yata_store.IdCore) : Nat :=
  match dep with
  | none => 0
  | some d => StateVector.svClock state d.client

/-- `dep_state` reads the state where `dep_missing` needs it: for a
dependency on another client. Otherwise it answers `0`, which blocks no more
and no less. -/
theorem dep_state_spec (c : Std.U64) (dep : Option yata_store.IdCore)
    (state : state_vector.StateVectorCore) (hcan : StateVector.Canonical state) :
    pending.dep_state c dep state ⦃ i =>
      depMissing c dep i.val = depMissing c dep (heldOf state dep) ⦄ := by
  unfold pending.dep_state
  cases dep with
  | none => exact (spec_ok _).mpr rfl
  | some d =>
    simp only []
    cases hb : (d.client != c) with
    | false =>
      have e : d.client = c := bne_false_eq hb
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine (spec_ok _).mpr ?_
      rw [depMissing_same c d _ e, depMissing_same c d _ e]
    | true =>
      simp only [↓reduceIte]
      refine spec_mono (StateVector.get_spec state d.client hcan) ?_
      intro i hi
      rw [hi]
      rfl

/-- `dep_blocks`: whether `dep` blocks under `state`. -/
theorem dep_blocks_spec (c : Std.U64) (dep : Option yata_store.IdCore)
    (state : state_vector.StateVectorCore) (hcan : StateVector.Canonical state) :
    pending.dep_blocks c dep state ⦃ r => r = depMissing c dep (heldOf state dep) ⦄ := by
  unfold pending.dep_blocks
  step with dep_state_spec c dep state hcan as ⟨i, hi⟩
  refine spec_mono (dep_missing_spec c dep i) ?_
  intro r hr
  rw [hr, hi]

/-- **`find_missing_dependency` answers the first dependency `state` does not
cover**: left origin, right origin, then parent. -/
theorem find_missing_dependency_spec (id : yata_store.IdCore)
    (ol or_ p : Option yata_store.IdCore) (state : state_vector.StateVectorCore)
    (hcan : StateVector.Canonical state) :
    pending.find_missing_dependency id ol or_ p state ⦃ r =>
      r = firstOf (depMissing id.client ol (heldOf state ol))
        (depMissing id.client or_ (heldOf state or_))
        (depMissing id.client p (heldOf state p)) ⦄ := by
  unfold pending.find_missing_dependency
  step with dep_blocks_spec id.client ol state hcan as ⟨o, ho⟩
  cases o with
  | some x =>
    refine (spec_ok _).mpr ?_
    rw [← ho]
    rfl
  | none =>
    simp only []
    step with dep_blocks_spec id.client or_ state hcan as ⟨o1, ho1⟩
    cases o1 with
    | some y =>
      refine (spec_ok _).mpr ?_
      rw [← ho, ← ho1]
      rfl
    | none =>
      simp only []
      refine spec_mono (dep_blocks_spec id.client p state hcan) ?_
      intro r hr
      rw [← ho, ← ho1, hr]
      rfl

/-! ## The decision on a struct -/

/-- What `check_local_readiness` answers, by its cases. -/
def LocalPost (id : yata_store.IdCore) (isSkip : Bool) (held : Nat) (r : pending.LocalStep) : Prop :=
  (isSkip = true ∧ r = pending.LocalStep.Skip) ∨
  (isSkip = false ∧ held < id.clock.val ∧
    ∃ m : Std.U64, r = pending.LocalStep.MissingLocal id.client m ∧ m.val + 1 = id.clock.val) ∨
  (isSkip = false ∧ id.clock.val ≤ held ∧ r = pending.LocalStep.Ready)

/-- **`check_local_readiness`**: a skip; or the clock before the struct, which
is not below zero, when the document does not hold the clocks up to the
struct; or ready. -/
@[step]
theorem check_local_readiness_spec (id : yata_store.IdCore) (isSkip : Bool) (held : Std.U64) :
    pending.check_local_readiness id isSkip held ⦃ r => LocalPost id isSkip held.val r ⦄ := by
  unfold pending.check_local_readiness
  cases isSkip with
  | true =>
    simp only [↓reduceIte, spec_ok]
    exact Or.inl ⟨rfl, rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hgt : id.clock > held
    · simp only [hgt, ↓reduceIte]
      have hlt : held.val < id.clock.val := by scalar_tac
      step as ⟨m, hm⟩
      exact Or.inr (Or.inl ⟨rfl, hlt, m, rfl, by scalar_tac⟩)
    · simp only [hgt, ↓reduceIte, spec_ok]
      have hle : id.clock.val ≤ held.val := by scalar_tac
      exact Or.inr (Or.inr ⟨rfl, hle, rfl⟩)

/-- `applies_from` says whether a struct is applied from an offset: from its
first clock, or from one of its clocks. -/
theorem applies_from_spec (off len : Std.U64) :
    pending.applies_from off len ⦃ b => (b = true ↔ (off.val = 0 ∨ off.val < len.val)) ⦄ := by
  unfold pending.applies_from
  by_cases hz : off = 0#u64
  · have hz' : (off = 0#u64) = True := eq_true hz
    simp only [hz', ↓reduceIte, spec_ok]
    have h0 : off.val = 0 := by scalar_tac
    constructor
    · intro _
      exact Or.inl h0
    · intro _
      trivial
  · simp only [hz, ↓reduceIte, spec_ok]
    have h0 : ¬ off.val = 0 := by scalar_tac
    constructor
    · intro h
      have := of_decide_eq_true h
      exact Or.inr (by scalar_tac)
    · rintro (h | h)
      · exact absurd h h0
      · apply decide_eq_true
        scalar_tac

/-- What `classify_ready_step` answers for a struct whose earlier clocks are
there (`id.clock ≤ held`), by its cases. -/
def ReadyPost (id : yata_store.IdCore) (len held : Nat) (missing : Option Std.U64)
    (r : pending.StructStep) : Prop :=
  (∃ c, missing = some c ∧ r = pending.StructStep.MissingDep c) ∨
  (missing = none ∧ ∃ off next : Std.U64, r = pending.StructStep.Apply off next ∧
    id.clock.val + off.val = held ∧ (off.val = 0 ∨ off.val < len) ∧
    next.val = min (id.clock.val + len) 18446744073709551615 ∧ held ≤ next.val) ∨
  (missing = none ∧ r = pending.StructStep.AlreadyApplied ∧ id.clock.val < held ∧
    id.clock.val + len ≤ held)

/-- **`classify_ready_step`**: a missing dependency first; else the struct is
applied from the first clock the document lacks (an offset that is `0` or
below its length, never below zero) and the state after it is its end, not
below the state before; else every clock of it is there already. -/
theorem classify_ready_step_spec (id : yata_store.IdCore) (len held : Std.U64)
    (missing : Option Std.U64) (hready : id.clock.val ≤ held.val) :
    pending.classify_ready_step id len held missing ⦃ r =>
      ReadyPost id len.val held.val missing r ⦄ := by
  unfold pending.classify_ready_step
  cases missing with
  | some c =>
    simp only [spec_ok]
    exact Or.inl ⟨c, rfl, rfl⟩
  | none =>
    simp only []
    have hoff : (if held > id.clock then held - id.clock else ok 0#u64 : Result Std.U64) ⦃ off =>
        id.clock.val + off.val = held.val ⦄ := by
      by_cases hgt : held > id.clock
      · simp only [hgt, ↓reduceIte]
        step as ⟨off, hoff⟩
        scalar_tac
      · simp only [hgt, ↓reduceIte, spec_ok]
        scalar_tac
    step with hoff as ⟨off, hoff⟩
    step with applies_from_spec off len as ⟨b, hb⟩
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, spec_ok]
      have hno : ¬ (off.val = 0 ∨ off.val < len.val) := fun h => by
        have := hb.mpr h
        cases this
      exact Or.inr (Or.inr ⟨rfl, rfl, by omega, by omega⟩)
    | true =>
      simp only [↓reduceIte]
      have happlies : off.val = 0 ∨ off.val < len.val := hb.mp rfl
      have hMax : (core.num.U64.MAX : Std.U64).val = 18446744073709551615 := rfl
      step as ⟨room, hroom⟩
      have hroomv : room.val = 18446744073709551615 - id.clock.val := by
        rw [← hMax]
        scalar_tac
      by_cases hbig : len > room
      · simp only [hbig, ↓reduceIte, spec_ok]
        have hb2 : 18446744073709551615 - id.clock.val < len.val := by scalar_tac
        have hheld : held.val ≤ 18446744073709551615 := by scalar_tac
        refine Or.inr (Or.inl ⟨rfl, off, core.num.U64.MAX, rfl, hoff, happlies, ?_, ?_⟩)
        · rw [hMax]
          omega
        · rw [hMax]
          exact hheld
      · simp only [hbig, ↓reduceIte]
        have hb2 : len.val ≤ 18446744073709551615 - id.clock.val := by scalar_tac
        have hck : id.clock.val ≤ 18446744073709551615 := by scalar_tac
        step as ⟨next, hnext⟩
        have hnv : next.val = id.clock.val + len.val := by scalar_tac
        refine Or.inr (Or.inl ⟨rfl, off, next, rfl, hoff, happlies, ?_, ?_⟩)
        · rw [hnv]
          omega
        · rw [hnv]
          omega

/-- What `classify_struct_step` answers, by its cases, in the order they are
decided. -/
def StructPost (id : yata_store.IdCore) (len : Nat) (isSkip : Bool) (held : Nat)
    (missing : Option Std.U64) (r : pending.StructStep) : Prop :=
  (isSkip = true ∧ r = pending.StructStep.Skip) ∨
  (isSkip = false ∧ held < id.clock.val ∧
    ∃ m : Std.U64, r = pending.StructStep.MissingLocal id.client m ∧ m.val + 1 = id.clock.val) ∨
  (isSkip = false ∧ id.clock.val ≤ held ∧ ReadyPost id len held missing r)

/-- **`classify_struct_step` is total and decides in this order**: a skip;
clocks of the client of the struct that the document lacks (the one before the
struct is named: no clock below zero); a missing dependency; the offset to
apply the struct from (`0` or below its length; the state after it is not
below the state before); or a struct that is there already. -/
theorem classify_struct_step_spec (id : yata_store.IdCore) (len : Std.U64) (isSkip : Bool)
    (held : Std.U64) (missing : Option Std.U64) :
    pending.classify_struct_step id len isSkip held missing ⦃ r =>
      StructPost id len.val isSkip held.val missing r ⦄ := by
  unfold pending.classify_struct_step
  step with check_local_readiness_spec id isSkip held as ⟨ls, hls⟩
  rcases hls with ⟨hs, rfl⟩ | ⟨hs, hlt, m, rfl, hm⟩ | ⟨hs, hle, rfl⟩
  · simp only [spec_ok]
    exact Or.inl ⟨hs, rfl⟩
  · simp only [spec_ok]
    exact Or.inr (Or.inl ⟨hs, hlt, m, rfl, hm⟩)
  · simp only []
    refine spec_mono (classify_ready_step_spec id len held missing hle) ?_
    intro r hr
    exact Or.inr (Or.inr ⟨hs, hle, hr⟩)

/-- The two steps `y-octo` takes are the one decision: a struct that is
`Ready` is classified by `classify_ready_step`, and the other answers of
`check_local_readiness` are the answers of `classify_struct_step`. -/
theorem classify_struct_step_eq (id : yata_store.IdCore) (len : Std.U64) (isSkip : Bool)
    (held : Std.U64) (missing : Option Std.U64) :
    pending.classify_struct_step id len isSkip held missing =
      (do
        let ls ← pending.check_local_readiness id isSkip held
        match ls with
        | pending.LocalStep.Skip => ok pending.StructStep.Skip
        | pending.LocalStep.MissingLocal client missing_clock =>
          ok (pending.StructStep.MissingLocal client missing_clock)
        | pending.LocalStep.Ready => pending.classify_ready_step id len held missing) := by
  unfold pending.classify_struct_step
  rfl

/-! ## Deleted ranges -/

/-- A clock of a part of a split. -/
def inPart (p : Option order_range.ClockRange) (c : Nat) : Prop :=
  ∃ r, p = some r ∧ r.start.val ≤ c ∧ c < r.«end».val

/-- What `split_delete_range` answers: the part below the state and the part
from the state on, each `none` when it has no clock. -/
structure SplitPost (start stop held : Nat) (d : pending.DeleteSplit) : Prop where
  /-- the applicable part is the range below the state -/
  applicable : ∀ r, d.applicable = some r →
    r.start.val = start ∧ r.«end».val = min stop held ∧ r.start.val < r.«end».val
  /-- the pending part is the range from the state on -/
  pending : ∀ r, d.pending = some r →
    r.start.val = max start held ∧ r.«end».val = stop ∧ r.start.val < r.«end».val
  /-- no applicable part: no clock of the range is below the state -/
  noApplicable : d.applicable = none → min stop held ≤ start
  /-- no pending part: no clock of the range is at or above the state -/
  noPending : d.pending = none → stop ≤ max start held

/-- **`split_delete_range` is total and cuts the range at the state.** -/
theorem split_delete_range_spec (start stop held : Std.U64) :
    pending.split_delete_range start stop held ⦃ d =>
      SplitPost start.val stop.val held.val d ⦄ := by
  unfold pending.split_delete_range
  by_cases hall : held >= stop
  · simp only [hall, ↓reduceIte]
    have h1 : stop.val ≤ held.val := by scalar_tac
    by_cases hsome : start < stop
    · simp only [hsome, ↓reduceIte, spec_ok]
      have h2 : start.val < stop.val := by scalar_tac
      refine ⟨fun r hr => ?_, fun r hr => (nomatch hr), fun hn => (nomatch hn), fun _ => by omega⟩
      have e := Option.some.inj hr
      rw [← e]
      exact ⟨rfl, by show stop.val = min stop.val held.val; omega, h2⟩
    · simp only [hsome, ↓reduceIte, spec_ok]
      have h2 : stop.val ≤ start.val := by scalar_tac
      exact ⟨fun r hr => (nomatch hr), fun r hr => (nomatch hr), fun _ => by omega, fun _ => by omega⟩
  · simp only [hall, ↓reduceIte]
    have h1 : held.val < stop.val := by scalar_tac
    by_cases hbelow : held <= start
    · simp only [hbelow, ↓reduceIte]
      have h2 : held.val ≤ start.val := by scalar_tac
      by_cases hsome : start < stop
      · simp only [hsome, ↓reduceIte, spec_ok]
        have h3 : start.val < stop.val := by scalar_tac
        refine ⟨fun r hr => (nomatch hr), fun r hr => ?_, fun _ => by omega, fun hn => (nomatch hn)⟩
        have e := Option.some.inj hr
        rw [← e]
        exact ⟨by show start.val = max start.val held.val; omega, rfl, h3⟩
      · simp only [hsome, ↓reduceIte, spec_ok]
        have h3 : stop.val ≤ start.val := by scalar_tac
        exact ⟨fun r hr => (nomatch hr), fun r hr => (nomatch hr), fun _ => by omega, fun _ => by omega⟩
    · simp only [hbelow, ↓reduceIte, spec_ok]
      have h2 : start.val < held.val := by scalar_tac
      refine ⟨fun r hr => ?_, fun r hr => ?_, fun hn => (nomatch hn), fun hn => (nomatch hn)⟩
      · have e := Option.some.inj hr
        rw [← e]
        exact ⟨rfl, by show held.val = min stop.val held.val; omega, h2⟩
      · have e := Option.some.inj hr
        rw [← e]
        exact ⟨by show held.val = max start.val held.val; omega, rfl, h1⟩

/-- **Every clock of the range is in the applicable part if it is below the
state, and in the pending part if it is not**; no clock outside the range is
in a part. -/
theorem split_clocks {start stop held : Nat} {d : pending.DeleteSplit}
    (h : SplitPost start stop held d) (c : Nat) :
    (inPart d.applicable c ↔ start ≤ c ∧ c < stop ∧ c < held) ∧
    (inPart d.pending c ↔ start ≤ c ∧ c < stop ∧ held ≤ c) := by
  constructor
  · constructor
    · rintro ⟨r, hr, h1, h2⟩
      obtain ⟨e1, e2, _⟩ := h.applicable r hr
      omega
    · rintro ⟨h1, h2, h3⟩
      cases ha : d.applicable with
      | none =>
        have := h.noApplicable ha
        omega
      | some r =>
        obtain ⟨e1, e2, _⟩ := h.applicable r ha
        exact ⟨r, rfl, by omega, by omega⟩
  · constructor
    · rintro ⟨r, hr, h1, h2⟩
      obtain ⟨e1, e2, _⟩ := h.pending r hr
      omega
    · rintro ⟨h1, h2, h3⟩
      cases hp : d.pending with
      | none =>
        have := h.noPending hp
        omega
      | some r =>
        obtain ⟨e1, e2, _⟩ := h.pending r hp
        exact ⟨r, rfl, by omega, by omega⟩

/-- **The two parts share no clock.** -/
theorem split_disjoint {start stop held : Nat} {d : pending.DeleteSplit}
    (h : SplitPost start stop held d) (c : Nat) :
    ¬ (inPart d.applicable c ∧ inPart d.pending c) := by
  rintro ⟨ha, hp⟩
  have h1 := ((split_clocks h c).1.mp ha).2.2
  have h2 := ((split_clocks h c).2.mp hp).2.2
  omega

end YoctoCore.Properties.Pending
