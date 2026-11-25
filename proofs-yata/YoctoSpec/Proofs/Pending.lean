/-
The pending queue.

`Store.drain` only ever hands on a struct that is ready in the store it has
reached (`drain_spec`), and it stops only when nothing that is left is ready
(`drain_minimal`, `applyUpdate_pending_minimal`). These are statements about
the queue and `Store.ready`; that a ready struct is a legal delivery of the
unit-level network (the hypothesis `UnitRun` of `BRun.integrate`) is not
proved here.
-/
import YoctoSpec.Model.Store
import YoctoSpec.Proofs.BlockIntegrate

namespace YoctoSpec

open Store

/-- `ws` can be integrated one after the other, each one ready in the store
the ones before it produced. -/
def ReadySeq : Store → List Wire → Prop
  | _, [] => True
  | s, w :: t => s.ready w = true ∧ ReadySeq (s.applyWire w) t

theorem pickReady_spec {s : Store} :
    ∀ {q : List Wire} {w : Wire} {q' : List Wire}, s.pickReady q = some (w, q') →
      s.ready w = true ∧ q.Perm (w :: q') ∧ q'.length + 1 = q.length := by
  intro q
  induction q with
  | nil =>
    intro w q' h
    rw [pickReady] at h
    cases h
  | cons w₀ t ih =>
    intro w q' h
    rw [pickReady] at h
    by_cases hr : s.ready w₀ = true
    · rw [ite_eq_left hr] at h
      have e₁ : w₀ = w := congrArg Prod.fst (Option.some.inj h)
      have e₂ : t = q' := congrArg Prod.snd (Option.some.inj h)
      rw [← e₁, ← e₂]
      exact ⟨hr, List.Perm.refl _, rfl⟩
    · rw [ite_eq_right hr] at h
      cases hp : s.pickReady t with
      | none =>
        rw [hp] at h
        cases h
      | some p =>
        cases p with
        | mk r t' =>
          rw [hp] at h
          have h' : some (r, w₀ :: t') = some (w, q') := h
          have e₁ : r = w := congrArg Prod.fst (Option.some.inj h')
          have e₂ : w₀ :: t' = q' := congrArg Prod.snd (Option.some.inj h')
          obtain ⟨h₁, h₂, h₃⟩ := ih hp
          rw [← e₁, ← e₂]
          refine ⟨h₁, ?_, ?_⟩
          · exact (List.Perm.cons w₀ h₂).trans (List.Perm.swap r w₀ t')
          · rw [List.length_cons, List.length_cons]
            omega

theorem pickReady_none {s : Store} :
    ∀ {q : List Wire}, s.pickReady q = none → ∀ w, w ∈ q → s.ready w = false := by
  intro q
  induction q with
  | nil =>
    intro _ w hw
    cases hw
  | cons w₀ t ih =>
    intro h w hw
    rw [pickReady] at h
    by_cases hr : s.ready w₀ = true
    · rw [ite_eq_left hr] at h
      cases h
    · rw [ite_eq_right hr] at h
      cases hp : s.pickReady t with
      | none =>
        rcases List.mem_cons.mp hw with e | hw'
        · rw [e]
          cases hrw : s.ready w₀ with
          | false => rfl
          | true => exact absurd hrw hr
        · exact ih hp w hw'
      | some p =>
        cases p with
        | mk r t' =>
          rw [hp] at h
          cases h

theorem drain_zero (s : Store) (q : List Wire) : drain 0 s q = (s, q) := by
  rw [drain]

theorem drain_none {s : Store} {q : List Wire} (fuel : Nat) (h : s.pickReady q = none) :
    drain (fuel + 1) s q = (s, q) := by
  rw [drain]
  simp only [h]

theorem drain_some {s : Store} {q : List Wire} {w : Wire} {q' : List Wire} (fuel : Nat)
    (h : s.pickReady q = some (w, q')) :
    drain (fuel + 1) s q = drain fuel (s.applyWire w) q' := by
  rw [drain]
  simp only [h]

/-- **Soundness of the pending queue.** Draining integrates a causal sequence
`ws` of structs of the queue and leaves the others queued. -/
theorem drain_spec : ∀ (fuel : Nat) (s : Store) (q : List Wire),
    ∃ ws, (drain fuel s q).1 = ws.foldl applyWire s ∧ ReadySeq s ws ∧
      q.Perm (ws ++ (drain fuel s q).2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s q
    rw [drain_zero]
    exact ⟨[], rfl, trivial, List.Perm.refl _⟩
  | succ fuel ih =>
    intro s q
    cases hp : s.pickReady q with
    | none =>
      rw [drain_none fuel hp]
      exact ⟨[], rfl, trivial, List.Perm.refl _⟩
    | some p =>
      cases p with
      | mk w q' =>
        rw [drain_some fuel hp]
        obtain ⟨h₁, h₂, _⟩ := pickReady_spec hp
        obtain ⟨ws, e, hr, hperm⟩ := ih (s.applyWire w) q'
        refine ⟨w :: ws, ?_, ⟨h₁, hr⟩, ?_⟩
        · rw [e]
          rfl
        · exact h₂.trans (List.Perm.cons w hperm)

/-- **Minimality of the pending queue.** With enough fuel (`apply_update` gives
one unit per queued struct), nothing that stays pending is ready. -/
theorem drain_minimal : ∀ (fuel : Nat) (s : Store) (q : List Wire), q.length ≤ fuel →
    ∀ w, w ∈ (drain fuel s q).2 → (drain fuel s q).1.ready w = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro s q hq w hw
    rw [drain_zero] at hw
    cases q with
    | nil => cases hw
    | cons a t =>
      rw [List.length_cons] at hq
      omega
  | succ fuel ih =>
    intro s q hq w hw
    cases hp : s.pickReady q with
    | none =>
      rw [drain_none fuel hp] at hw ⊢
      exact pickReady_none hp w hw
    | some p =>
      cases p with
      | mk r q' =>
        rw [drain_some fuel hp] at hw ⊢
        obtain ⟨_, _, h₃⟩ := pickReady_spec hp
        exact ih (s.applyWire r) q' (by omega) w hw

/-! ## `apply_update`

Applying the delete set after the structs changes neither the state vector nor
the pending structs, so the minimality of `drain` is a statement about the
result of `applyUpdate`. -/

def blockEnd (b : Block) (c : Nat) : Nat := if b.id.client = c then b.id.clock + b.len else 0

theorem stateB_cons (b : Block) (t : List Block) (c : Nat) :
    stateB (b :: t) c = max (blockEnd b c) (stateB t c) := by
  rw [stateB]
  unfold blockEnd
  by_cases h : b.id.client = c
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    omega

theorem stateB_append (p q : List Block) (c : Nat) :
    stateB (p ++ q) c = max (stateB p c) (stateB q c) := by
  induction p with
  | nil =>
    show stateB q c = max (stateB [] c) (stateB q c)
    rw [stateB]
    omega
  | cons b t ih =>
    show stateB (b :: (t ++ q)) c = max (stateB (b :: t) c) (stateB q c)
    rw [stateB_cons, stateB_cons, ih]
    omega

theorem stateB_flatMap (f : Block → List Block) (c : Nat)
    (hf : ∀ b, stateB (f b) c = blockEnd b c) :
    ∀ bs : List Block, stateB (bs.flatMap f) c = stateB bs c := by
  intro bs
  induction bs with
  | nil => rfl
  | cons b t ih => rw [List.flatMap_cons, stateB_append, hf, ih, stateB_cons]

theorem stateB_splitBlock (x : Id) (b : Block) (c : Nat) :
    stateB (splitBlock x b) c = blockEnd b c := by
  unfold splitBlock
  by_cases h : x.client = b.id.client ∧ b.id.clock < x.clock ∧ x.clock < b.id.clock + b.len
  · rw [ite_eq_left h]
    unfold Block.splitAt
    rw [stateB_cons, stateB_cons, stateB]
    have e₁ : blockEnd (b.leftPart (x.clock - b.id.clock)) c =
        if b.id.client = c then b.id.clock + (x.clock - b.id.clock) else 0 := by
      unfold blockEnd
      rw [len_leftPart (by omega)]
      rfl
    have e₂ : blockEnd (b.rightPart (x.clock - b.id.clock)) c =
        if b.id.client = c then
          b.id.clock + (x.clock - b.id.clock) + (b.len - (x.clock - b.id.clock))
        else 0 := by
      unfold blockEnd
      rw [len_rightPart]
      rfl
    rw [e₁, e₂]
    unfold blockEnd
    by_cases hc : b.id.client = c
    · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc]
      omega
    · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
      omega
  · rw [ite_eq_right h, stateB_cons, stateB]
    omega

theorem stateB_split (bs : List Block) (x : Id) (c : Nat) : stateB (split bs x) c = stateB bs c :=
  stateB_flatMap _ c (fun b => stateB_splitBlock x b c) bs

theorem id_markBlock (c lo hi : Nat) (b : Block) : (markBlock c lo hi b).id = b.id := by
  unfold markBlock
  split <;> rfl

theorem len_markBlock (c lo hi : Nat) (b : Block) : (markBlock c lo hi b).len = b.len := by
  unfold markBlock
  split <;> rfl

theorem stateB_markRange (c' lo hi : Nat) (bs : List Block) (c : Nat) :
    stateB (markRange c' lo hi bs) c = stateB bs c := by
  unfold markRange
  induction bs with
  | nil => rfl
  | cons b t ih =>
    have e : blockEnd (markBlock c' lo hi b) c = blockEnd b c := by
      unfold blockEnd
      rw [id_markBlock, len_markBlock]
    rw [List.map_cons, stateB_cons, stateB_cons, e, ih]

theorem stateB_deleteRange (bs : List Block) (c' lo hi c : Nat) :
    stateB (deleteRange bs c' lo hi) c = stateB bs c := by
  unfold deleteRange
  rw [stateB_markRange, stateB_split, stateB_split]

theorem stateB_rangeBlocks (s : Store) (r : DelRange) (c : Nat) :
    stateB (rangeBlocks s r) c = stateB s.blocks c := by
  unfold rangeBlocks
  by_cases h : s.state r.client ≤ r.clock
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, stateB_deleteRange]

/-- Applying a delete range leaves the state vector alone. -/
theorem state_applyRange (s : Store) (r : DelRange) (c : Nat) :
    (s.applyRange r).state c = s.state c := by
  show max (stateB (rangeBlocks s r) c) (gcState s.gc c) =
    max (stateB s.blocks c) (gcState s.gc c)
  rw [stateB_rangeBlocks]

theorem pending_applyRange (s : Store) (r : DelRange) : (s.applyRange r).pending = s.pending :=
  rfl

theorem foldl_applyRange (rs : List DelRange) : ∀ s : Store,
    (rs.foldl applyRange s).pending = s.pending ∧
      ∀ c, (rs.foldl applyRange s).state c = s.state c := by
  induction rs with
  | nil =>
    intro s
    exact ⟨rfl, fun _ => rfl⟩
  | cons r t ih =>
    intro s
    obtain ⟨h₁, h₂⟩ := ih (s.applyRange r)
    exact ⟨h₁.trans (pending_applyRange s r), fun c => (h₂ c).trans (state_applyRange s r c)⟩

/-- Readiness only depends on the state vector. -/
theorem ready_congr {s s' : Store} (h : ∀ c, s.state c = s'.state c) (w : Wire) :
    s.ready w = s'.ready w := by
  have e : s.state = s'.state := funext h
  unfold ready
  rw [e]

/-- The structs `applyUpdate` leaves pending are the ones `drain` left. -/
theorem applyUpdate_pending (s : Store) (u : Update) :
    (s.applyUpdate u).pending = (drained s u).2 :=
  (foldl_applyRange (s.pendingDs ++ u.ds)
    { (drained s u).1 with pending := (drained s u).2, pendingDs := [] }).1

/-- **Minimality of `apply_update`.** No struct that is pending after
`applyUpdate` is ready in the store `applyUpdate` returns. -/
theorem applyUpdate_pending_minimal (s : Store) (u : Update) :
    ∀ w, w ∈ (s.applyUpdate u).pending → (s.applyUpdate u).ready w = false := by
  intro w hw
  rw [applyUpdate_pending] at hw
  have hst : ∀ c, (s.applyUpdate u).state c = (drained s u).1.state c :=
    (foldl_applyRange (s.pendingDs ++ u.ds)
      { (drained s u).1 with pending := (drained s u).2, pendingDs := [] }).2
  rw [ready_congr hst w]
  exact drain_minimal _ _ _ (Nat.le_refl _) w hw

end YoctoSpec
