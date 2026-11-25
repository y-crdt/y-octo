/-
The YATA relation of an integrated sequence is a strict total order, it is the
document order, and it is the same in every legal sequence.
-/
import YoctoSpec.Proofs.Stable

namespace YoctoSpec

/-- The YATA relation `a <_Y b` read off the origins and client ids of the two
items in `s`: `a` is at or before the left origin of `b`, or the right origin
of `a` is at or before `b`, or the two conflict (each is strictly inside the
origin interval of the other) and either the left origin of `b` is strictly
before that of `a` or the left origins are equal and `a` has the smaller
client. -/
def Precedes (s : List Item) (a b : Item) : Prop :=
  a.id ≠ b.id ∧
    (ix s a.id ≤ ixL s b.left ∨ ixR s a.right ≤ ix s b.id ∨
      (ixL s b.left < ix s a.id ∧ ix s b.id < ixR s a.right ∧
        ixL s a.left < ix s b.id ∧ ix s a.id < ixR s b.right ∧
        (ixL s b.left < ixL s a.left ∨ (a.left = b.left ∧ a.id.client < b.id.client))))

/-- On a legal sequence the YATA relation is the document order. -/
theorem precedes_iff {s : List Item} (hs : Legal s) {a b : Item} (ha : a ∈ s) (hb : b ∈ s) :
    Precedes s a b ↔ ix s a.id < ix s b.id := by
  have wa1 := hs.left_lt a ha
  have wa2 := hs.lt_right a ha
  have wb1 := hs.left_lt b hb
  have wb2 := hs.lt_right b hb
  constructor
  · rintro ⟨hne, h⟩
    by_cases hlt : ix s a.id < ix s b.id
    · exact hlt
    · exfalso
      have hne' : ix s a.id ≠ ix s b.id := fun e => hne (ix_inj e (ix_mem ha))
      have hba : ix s b.id < ix s a.id := by omega
      rcases h with h₁ | h₂ | ⟨g₁, g₂, g₃, g₄, g₅⟩
      · omega
      · omega
      · rcases hs.rule b hb a ha hba with r₁ | r₂ | r₃ | ⟨r₄, r₅⟩
        · omega
        · omega
        · rcases g₅ with g | ⟨g, _⟩
          · omega
          · rw [g] at r₃
            omega
        · rcases g₅ with g | ⟨_, g⟩
          · rw [r₄] at g
            omega
          · omega
  · intro hlt
    refine ⟨fun e => ?_, ?_⟩
    · rw [e] at hlt
      omega
    · by_cases c₁ : ix s a.id ≤ ixL s b.left
      · exact Or.inl c₁
      · by_cases c₂ : ixR s a.right ≤ ix s b.id
        · exact Or.inr (Or.inl c₂)
        · refine Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega, ?_⟩)
          rcases hs.rule a ha b hb hlt with r₁ | r₂ | r₃ | r₄
          · omega
          · omega
          · exact Or.inl r₃
          · exact Or.inr r₄

theorem precedes_irrefl (s : List Item) (a : Item) : ¬ Precedes s a a :=
  fun h => h.1 rfl

theorem precedes_asymm {s : List Item} (hs : Legal s) {a b : Item} (ha : a ∈ s) (hb : b ∈ s)
    (h₁ : Precedes s a b) (h₂ : Precedes s b a) : False := by
  have e₁ := (precedes_iff hs ha hb).mp h₁
  have e₂ := (precedes_iff hs hb ha).mp h₂
  omega

theorem precedes_trans {s : List Item} (hs : Legal s) {a b c : Item} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (h₁ : Precedes s a b) (h₂ : Precedes s b c) : Precedes s a c := by
  have e₁ := (precedes_iff hs ha hb).mp h₁
  have e₂ := (precedes_iff hs hb hc).mp h₂
  exact (precedes_iff hs ha hc).mpr (by omega)

/-- Trichotomy: two integrated items are equal or ordered one way. -/
theorem precedes_total {s : List Item} (hs : Legal s) {a b : Item} (ha : a ∈ s) (hb : b ∈ s) :
    a = b ∨ Precedes s a b ∨ Precedes s b a := by
  by_cases e : ix s a.id = ix s b.id
  · exact Or.inl (hs.nodup.eq_of_ix ha hb e)
  · by_cases hlt : ix s a.id < ix s b.id
    · exact Or.inr (Or.inl ((precedes_iff hs ha hb).mpr hlt))
    · exact Or.inr (Or.inr ((precedes_iff hs hb ha).mpr (by omega)))

/-- The YATA relation of two items is the same in every legal sequence that
contains both. -/
theorem precedes_stable {s t : List Item} (hs : Legal s) (ht : Legal t) (hc : Compat s t)
    {a b : Item} (has : a ∈ s) (hat : a ∈ t) (hbs : b ∈ s) (hbt : b ∈ t) :
    Precedes s a b ↔ Precedes t a b := by
  rw [precedes_iff hs has hbs, precedes_iff ht hat hbt]
  exact stable_iff hs ht hc has hat hbs hbt

end YoctoSpec
