/-
The invariant of an integrated sequence (`Legal`) and what an item must
satisfy to be integrated into it (`CanIntegrate`).

Everything is stated with positions in the sequence itself, so the document
order plays the role of the YATA total order and no abstract order has to be
constructed first.
-/
import YoctoSpec.Proofs.Position

namespace YoctoSpec

/-- The YATA rule that justifies `a` standing before `b` in `s`:

* `a` is at or before the left origin of `b`, or
* the right origin of `a` is at or before `b`, or
* (conflict) the left origin of `b` is strictly before the left origin of `a`, or
* (conflict) both have the same left origin and `a` has the smaller client. -/
def Rule (s : List Item) (a b : Item) : Prop :=
  ix s a.id ≤ ixL s b.left ∨ ixR s a.right ≤ ix s b.id ∨ ixL s b.left < ixL s a.left ∨
    (a.left = b.left ∧ a.id.client < b.id.client)

/-- Invariant of every integrated sequence. -/
structure Legal (s : List Item) : Prop where
  /-- ids are unique -/
  nodup : NodupIds s
  /-- an item is after its left origin -/
  left_lt : ∀ a, a ∈ s → ixL s a.left < ix s a.id
  /-- and before its right origin -/
  lt_right : ∀ a, a ∈ s → ix s a.id < ixR s a.right
  /-- which is integrated -/
  right_mem : ∀ a, a ∈ s → Present s a.right
  /-- the order of any two items is justified by the YATA rule -/
  rule : ∀ a, a ∈ s → ∀ b, b ∈ s → ix s a.id < ix s b.id → Rule s a b
  /-- the left origin of an item's right origin is not inside the item's own
  origin interval: the two origins were adjacent when the item was created -/
  rightLeft : ∀ a, a ∈ s → ∀ y, y ∈ s → a.right = some y.id → ixL s y.left ≤ ixL s a.left
  /-- origins are older than the item -/
  acyclic : ∃ rank : Id → Nat, ∀ a, a ∈ s → ∀ x, (a.left = some x ∨ a.right = some x) →
    rank x < rank a.id

/-- What integration needs from the new item. All of it follows from the item
having been created between two adjacent items of a legal sequence
(`canIntegrate_of_witness`). -/
structure CanIntegrate (s : List Item) (i : Item) : Prop where
  fresh : ∀ a, a ∈ s → a.id ≠ i.id
  left_mem : Present s i.left
  right_mem : Present s i.right
  left_lt_right : ixL s i.left < ixR s i.right
  rightLeft : ∀ y, y ∈ s → i.right = some y.id → ixL s y.left ≤ ixL s i.left
  /-- items of the same client are not between the origins: the creator had
  integrated them already -/
  client : ∀ y, y ∈ s → y.id.client = i.id.client →
    ix s y.id ≤ ixL s i.left ∨ ixR s i.right ≤ ix s y.id

theorem present_some {s : List Item} {x : Id} (h : ix s x ≤ s.length) : Present s (some x) := by
  intro y e
  cases e
  exact h

theorem Legal.left_present {s : List Item} (h : Legal s) {a : Item} (ha : a ∈ s) :
    Present s a.left := by
  apply present_of_ixL_lt
  have := h.left_lt a ha
  have := ix_mem ha
  omega

theorem legal_nil : Legal [] where
  nodup := List.Pairwise.nil
  left_lt := by intro a ha; cases ha
  lt_right := by intro a ha; cases ha
  right_mem := by intro a ha; cases ha
  rule := by intro a ha; cases ha
  rightLeft := by intro a ha; cases ha
  acyclic := ⟨fun _ => 0, by intro a ha; cases ha⟩

/-- No crossing origins: if `x` is before `y`, the left origin of `y` is not
strictly between the left origin of `x` and `x`. -/
theorem Legal.noCross {s : List Item} (h : Legal s) :
    ∀ x, x ∈ s → ∀ y, y ∈ s → ix s x.id < ix s y.id →
      ixL s y.left ≤ ixL s x.left ∨ ix s x.id ≤ ixL s y.left := by
  have key : ∀ d x, x ∈ s → s.length - ix s x.id ≤ d → ∀ y, y ∈ s → ix s x.id < ix s y.id →
      ixL s y.left ≤ ixL s x.left ∨ ix s x.id ≤ ixL s y.left := by
    intro d
    induction d with
    | zero =>
      intro x hx hd y hy hlt
      have := ix_mem hy
      omega
    | succ d ih =>
      intro x hx hd y hy hlt
      have hyn := ix_mem hy
      rcases h.rule x hx y hy hlt with h₁ | h₂ | h₃ | ⟨h₄, _⟩
      · exact Or.inr h₁
      · cases hr : x.right with
        | none =>
          rw [hr, ixR_none] at h₂
          omega
        | some z =>
          rw [hr, ixR_some] at h₂
          obtain ⟨w, hw, hwz⟩ := ix_le_length_iff.mp (show ix s z ≤ s.length by omega)
          rw [← hwz] at h₂ hr
          have hxw : ix s x.id < ix s w.id := by
            have := h.lt_right x hx
            rw [hr, ixR_some] at this
            exact this
          have hrl := h.rightLeft x hx w hw hr
          by_cases e : ix s w.id = ix s y.id
          · have hwy : w = y := h.nodup.eq_of_ix hw hy e
            rw [hwy] at hrl
            exact Or.inl hrl
          · rcases ih w hw (by omega) y hy (by omega) with h₅ | h₅
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
      · exact Or.inl (by omega)
      · rw [h₄]
        exact Or.inl (Nat.le_refl _)
  intro x hx
  exact key _ x hx (Nat.le_refl _)

end YoctoSpec
