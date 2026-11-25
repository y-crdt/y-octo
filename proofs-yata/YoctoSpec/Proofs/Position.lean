/-
Positions of ids in a sequence, and how they move when an item is inserted.
-/
import YoctoSpec.Model.Yata

namespace YoctoSpec

theorem ix_cons_self (a : Item) (t : List Item) : ix (a :: t) a.id = 1 := by
  simp [ix]

theorem ix_cons_ne {a : Item} {t : List Item} {x : Id} (h : a.id ≠ x) :
    ix (a :: t) x = ix t x + 1 := by
  simp [ix, h]

theorem ix_pos (s : List Item) (x : Id) : 1 ≤ ix s x := by
  cases s with
  | nil => simp [ix]
  | cons a t =>
    by_cases h : a.id = x
    · subst h; rw [ix_cons_self]; omega
    · rw [ix_cons_ne h]; omega

theorem ix_le (s : List Item) (x : Id) : ix s x ≤ s.length + 1 := by
  induction s with
  | nil => simp [ix]
  | cons a t ih =>
    by_cases h : a.id = x
    · subst h; rw [ix_cons_self]; omega
    · rw [ix_cons_ne h, List.length_cons]; omega

theorem ix_le_length_iff {s : List Item} {x : Id} :
    ix s x ≤ s.length ↔ ∃ a, a ∈ s ∧ a.id = x := by
  induction s with
  | nil =>
    constructor
    · intro h; simp [ix] at h
    · rintro ⟨a, ha, _⟩; simp at ha
  | cons a t ih =>
    by_cases h : a.id = x
    · subst h
      constructor
      · intro _; exact ⟨a, List.mem_cons_self .., rfl⟩
      · intro _; rw [ix_cons_self, List.length_cons]; omega
    · rw [ix_cons_ne h, List.length_cons]
      constructor
      · intro h'
        obtain ⟨b, hb, e⟩ := ih.mp (by omega)
        exact ⟨b, List.mem_cons_of_mem _ hb, e⟩
      · rintro ⟨b, hb, e⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact absurd e h
        · have := ih.mpr ⟨b, hb, e⟩
          omega

theorem ix_mem {s : List Item} {a : Item} (h : a ∈ s) : ix s a.id ≤ s.length :=
  ix_le_length_iff.mpr ⟨a, h, rfl⟩

theorem ix_absent {s : List Item} {x : Id} (h : ∀ a, a ∈ s → a.id ≠ x) :
    ix s x = s.length + 1 := by
  have h₁ := ix_le s x
  have h₂ : ¬ ix s x ≤ s.length := by
    intro h'
    obtain ⟨a, ha, e⟩ := ix_le_length_iff.mp h'
    exact h a ha e
  omega

theorem ix_inj {s : List Item} {x y : Id} (h : ix s x = ix s y) (hx : ix s x ≤ s.length) :
    x = y := by
  induction s with
  | nil => simp [ix] at hx
  | cons a t ih =>
    by_cases h₁ : a.id = x
    · by_cases h₂ : a.id = y
      · rw [← h₁, ← h₂]
      · exfalso
        have e₁ : ix (a :: t) x = 1 := by
          rw [← h₁]
          exact ix_cons_self a t
        have e₂ := ix_cons_ne (t := t) h₂
        have e₃ := ix_pos t y
        omega
    · have e₁ := ix_cons_ne (t := t) h₁
      by_cases h₂ : a.id = y
      · exfalso
        have e₂ : ix (a :: t) y = 1 := by
          rw [← h₂]
          exact ix_cons_self a t
        have e₃ := ix_pos t x
        omega
      · have e₂ := ix_cons_ne (t := t) h₂
        rw [List.length_cons] at hx
        exact ih (by omega) (by omega)

theorem ix_append_left {p : List Item} {x : Id} (q : List Item) (h : ix p x ≤ p.length) :
    ix (p ++ q) x = ix p x := by
  induction p with
  | nil => simp [ix] at h
  | cons a t ih =>
    by_cases h₁ : a.id = x
    · subst h₁
      rw [List.cons_append, ix_cons_self, ix_cons_self]
    · rw [ix_cons_ne h₁, List.length_cons] at h
      rw [List.cons_append, ix_cons_ne h₁, ix_cons_ne h₁, ih (by omega)]

theorem ix_append_right {p : List Item} {x : Id} (q : List Item) (h : p.length < ix p x) :
    ix (p ++ q) x = p.length + ix q x := by
  induction p with
  | nil => simp
  | cons a t ih =>
    by_cases h₁ : a.id = x
    · subst h₁
      rw [ix_cons_self, List.length_cons] at h
      omega
    · rw [ix_cons_ne h₁, List.length_cons] at h
      rw [List.cons_append, ix_cons_ne h₁, ih (by omega), List.length_cons]
      omega

theorem ix_append_cons_self {p : List Item} (c : Item) (q : List Item)
    (h : ∀ a, a ∈ p → a.id ≠ c.id) : ix (p ++ c :: q) c.id = p.length + 1 := by
  have h₁ := ix_absent h
  rw [ix_append_right _ (by omega), ix_cons_self]

/-- Ids pairwise distinct. -/
def NodupIds (s : List Item) : Prop := s.Pairwise (fun a b => a.id ≠ b.id)

theorem NodupIds.eq_of_id {s : List Item} (h : NodupIds s) {a b : Item} (ha : a ∈ s)
    (hb : b ∈ s) (e : a.id = b.id) : a = b := by
  induction s with
  | nil => cases ha
  | cons c t ih =>
    unfold NodupIds at h
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [ha', hb']
      · exfalso
        rw [ha'] at e
        exact h.1 b hb' e
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exfalso
        rw [hb'] at e
        exact h.1 a ha' e.symm
      · exact ih h.2 ha' hb'

theorem NodupIds.eq_of_ix {s : List Item} (h : NodupIds s) {a b : Item} (ha : a ∈ s)
    (hb : b ∈ s) (e : ix s a.id = ix s b.id) : a = b :=
  h.eq_of_id ha hb (ix_inj e (ix_mem ha))

theorem NodupIds.ix_mid {p q : List Item} {c : Item} (h : NodupIds (p ++ c :: q)) :
    ix (p ++ c :: q) c.id = p.length + 1 := by
  apply ix_append_cons_self
  intro a ha
  unfold NodupIds at h
  rw [List.pairwise_append] at h
  exact h.2.2 a ha c (List.mem_cons_self ..)

/-! ## Origins -/

theorem ixL_some (s : List Item) (x : Id) : ixL s (some x) = ix s x := rfl
theorem ixL_none (s : List Item) : ixL s none = 0 := rfl
theorem ixR_some (s : List Item) (x : Id) : ixR s (some x) = ix s x := rfl
theorem ixR_none (s : List Item) : ixR s none = s.length + 1 := rfl

theorem ixL_le (s : List Item) (o : Option Id) : ixL s o ≤ s.length + 1 := by
  cases o with
  | none => simp [ixL]
  | some x => exact ix_le s x

theorem ixR_pos (s : List Item) (o : Option Id) : 1 ≤ ixR s o := by
  cases o with
  | none => simp [ixR]
  | some x => exact ix_pos s x

theorem ixR_le (s : List Item) (o : Option Id) : ixR s o ≤ s.length + 1 := by
  cases o with
  | none => simp [ixR]
  | some x => exact ix_le s x

/-- An origin that is the sentinel or an integrated id. -/
def Present (s : List Item) (o : Option Id) : Prop := ∀ x, o = some x → ix s x ≤ s.length

theorem present_none (s : List Item) : Present s none := by
  intro x h; cases h

theorem present_of_ixL_lt {s : List Item} {o : Option Id} (h : ixL s o ≤ s.length) :
    Present s o := by
  intro x e; subst e; exact h

theorem Present.ixL_le {s : List Item} {o : Option Id} (h : Present s o) :
    ixL s o ≤ s.length := by
  cases o with
  | none => simp [ixL]
  | some x => exact h x rfl

theorem ixL_inj {s : List Item} {o₁ o₂ : Option Id} (h₁ : Present s o₁)
    (e : ixL s o₁ = ixL s o₂) : o₁ = o₂ := by
  cases o₁ with
  | none =>
    cases o₂ with
    | none => rfl
    | some y =>
      have := ix_pos s y
      simp only [ixL] at e
      omega
  | some x =>
    cases o₂ with
    | none =>
      have := ix_pos s x
      simp only [ixL] at e
      omega
    | some y =>
      simp only [ixL] at e
      rw [ix_inj e (h₁ x rfl)]

theorem ixL_eq_ix {s : List Item} {o : Option Id} {x : Id} (h : Present s (some x))
    (e : ixL s o = ix s x) : o = some x := by
  have := ixL_inj (o₁ := some x) (o₂ := o) h (by rw [ixL_some]; exact e.symm)
  exact this.symm

/-! ## Insertion

`sh k n` is where position `n` moves when an item is inserted after position
`k`. -/

def sh (k n : Nat) : Nat := if n ≤ k then n else n + 1

theorem sh_spec (k n : Nat) : (n ≤ k ∧ sh k n = n) ∨ (k < n ∧ sh k n = n + 1) := by
  unfold sh
  by_cases h : n ≤ k
  · rw [ite_eq_left h]; omega
  · rw [ite_eq_right h]; omega

theorem ix_ins {p q : List Item} {i : Item} {x : Id} (hx : i.id ≠ x) :
    ix (p ++ i :: q) x = sh p.length (ix (p ++ q) x) := by
  by_cases h : ix p x ≤ p.length
  · rw [ix_append_left _ h, ix_append_left _ h]
    unfold sh
    rw [ite_eq_left h]
  · have h' : p.length < ix p x := by omega
    rw [ix_append_right _ h', ix_append_right _ h', ix_cons_ne hx]
    have := ix_pos q x
    unfold sh
    rw [ite_eq_right (by omega)]
    omega

theorem ixL_ins {p q : List Item} {i : Item} {o : Option Id} (ho : o ≠ some i.id) :
    ixL (p ++ i :: q) o = sh p.length (ixL (p ++ q) o) := by
  cases o with
  | none =>
    simp only [ixL]
    unfold sh
    rw [ite_eq_left (by omega)]
  | some x =>
    simp only [ixL]
    apply ix_ins
    intro e
    exact ho (by rw [e])

theorem ixR_ins {p q : List Item} {i : Item} {o : Option Id} (ho : o ≠ some i.id) :
    ixR (p ++ i :: q) o = sh p.length (ixR (p ++ q) o) := by
  cases o with
  | none =>
    simp only [ixR, List.length_append, List.length_cons]
    unfold sh
    rw [ite_eq_right (by omega)]
    omega
  | some x =>
    simp only [ixR]
    apply ix_ins
    intro e
    exact ho (by rw [e])

theorem mem_ins {p q : List Item} {i a : Item} : a ∈ p ++ i :: q ↔ a = i ∨ a ∈ p ++ q := by
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-! ## `after` and `insertAfter` by position -/

theorem afterId_eq_drop (x : Id) (s : List Item) : afterId x s = s.drop (ix s x) := by
  induction s with
  | nil => simp [afterId]
  | cons a t ih =>
    by_cases h : a.id = x
    · subst h
      simp [afterId, ix_cons_self]
    · rw [ix_cons_ne h]
      simp [afterId, h, ih]

theorem after_eq_drop (o : Option Id) (s : List Item) : after o s = s.drop (ixL s o) := by
  cases o with
  | none => simp [after, ixL]
  | some x => simp [after, ixL, afterId_eq_drop]

theorem insertAfterId_eq (x : Id) (i : Item) (s : List Item) :
    insertAfterId x i s = s.take (ix s x) ++ i :: s.drop (ix s x) := by
  induction s with
  | nil => simp [insertAfterId]
  | cons a t ih =>
    by_cases h : a.id = x
    · subst h
      simp [insertAfterId, ix_cons_self]
    · rw [ix_cons_ne h]
      simp [insertAfterId, h, ih]

theorem insertAfter_eq (o : Option Id) (i : Item) (s : List Item) :
    insertAfter o i s = s.take (ixL s o) ++ i :: s.drop (ixL s o) := by
  cases o with
  | none => simp [insertAfter, ixL]
  | some x => simp [insertAfter, ixL, insertAfterId_eq]

end YoctoSpec
