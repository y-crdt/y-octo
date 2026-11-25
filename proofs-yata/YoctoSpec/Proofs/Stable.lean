/-
The order of two items does not depend on the sequence they are in: any two
legal sequences order their common items the same way (`stable`), so a legal
sequence is determined by its set of items (`legal_unique`).
-/
import YoctoSpec.Proofs.Insert

namespace YoctoSpec

/-- Items with the same id are the same item in both sequences. -/
def Compat (s t : List Item) : Prop := ∀ a, a ∈ s → ∀ b, b ∈ t → a.id = b.id → a = b

theorem Compat.symm {s t : List Item} (h : Compat s t) : Compat t s :=
  fun a ha b hb e => (h b hb a ha e.symm).symm

/-- Two pairs of positions are ordered the same way. -/
def Agree (x y x' y' : Nat) : Prop :=
  (x < y ∧ x' < y') ∨ (x = y ∧ x' = y') ∨ (y < x ∧ y' < x')

theorem common_of_present {s t : List Item} (hc : Compat s t) {x : Id}
    (hs : ix s x ≤ s.length) (ht : ix t x ≤ t.length) : ∃ u, u ∈ s ∧ u ∈ t ∧ u.id = x := by
  obtain ⟨u, hu, eu⟩ := ix_le_length_iff.mp hs
  obtain ⟨v, hv, ev⟩ := ix_le_length_iff.mp ht
  have huv : u = v := hc u hu v hv (by rw [eu, ev])
  refine ⟨u, hu, ?_, eu⟩
  rw [huv]
  exact hv

theorem agree_items {s t : List Item} {u c : Item} (hus : u ∈ s)
    (h₁ : ix s u.id < ix s c.id → ix t u.id < ix t c.id)
    (h₂ : ix s c.id < ix s u.id → ix t c.id < ix t u.id) :
    Agree (ix s u.id) (ix s c.id) (ix t u.id) (ix t c.id) := by
  by_cases l₁ : ix s u.id < ix s c.id
  · exact Or.inl ⟨l₁, h₁ l₁⟩
  · by_cases l₂ : ix s c.id < ix s u.id
    · exact Or.inr (Or.inr ⟨l₂, h₂ l₂⟩)
    · have e : ix s u.id = ix s c.id := by omega
      have huc : u.id = c.id := ix_inj e (ix_mem hus)
      exact Or.inr (Or.inl ⟨e, by rw [huc]⟩)

section
variable {s t : List Item} {rank : Id → Nat} {n : Nat}

/-- The induction hypothesis of `stable`: pairs of smaller rank are ordered the
same way. -/
def StableBelow (s t : List Item) (rank : Id → Nat) (n : Nat) : Prop :=
  ∀ a b, rank a.id + rank b.id < n → a ∈ s → a ∈ t → b ∈ s → b ∈ t →
    ix s a.id < ix s b.id → ix t a.id < ix t b.id

theorem agreeL (hc : Compat s t) (ih : StableBelow s t rank n) {o : Option Id} {c : Item}
    (hos : Present s o) (hot : Present t o) (hcs : c ∈ s) (hct : c ∈ t)
    (hr : ∀ x, o = some x → rank x + rank c.id < n) :
    Agree (ixL s o) (ix s c.id) (ixL t o) (ix t c.id) := by
  cases o with
  | none =>
    rw [ixL_none, ixL_none]
    have h₁ := ix_pos s c.id
    have h₂ := ix_pos t c.id
    exact Or.inl ⟨by omega, by omega⟩
  | some x =>
    rw [ixL_some, ixL_some]
    obtain ⟨u, hus, hut, eu⟩ := common_of_present hc (hos x rfl) (hot x rfl)
    have hr' := hr x rfl
    rw [← eu] at hr' ⊢
    exact agree_items hus (ih u c hr' hus hut hcs hct) (ih c u (by omega) hcs hct hus hut)

theorem agreeR (hc : Compat s t) (ih : StableBelow s t rank n) {o : Option Id} {c : Item}
    (hos : Present s o) (hot : Present t o) (hcs : c ∈ s) (hct : c ∈ t)
    (hr : ∀ x, o = some x → rank x + rank c.id < n) :
    Agree (ixR s o) (ix s c.id) (ixR t o) (ix t c.id) := by
  cases o with
  | none =>
    rw [ixR_none, ixR_none]
    have h₁ := ix_mem hcs
    have h₂ := ix_mem hct
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  | some x =>
    rw [ixR_some, ixR_some]
    obtain ⟨u, hus, hut, eu⟩ := common_of_present hc (hos x rfl) (hot x rfl)
    have hr' := hr x rfl
    rw [← eu] at hr' ⊢
    exact agree_items hus (ih u c hr' hus hut hcs hct) (ih c u (by omega) hcs hct hus hut)

theorem agreeLL (hc : Compat s t) (ih : StableBelow s t rank n) {o₁ o₂ : Option Id}
    (h₁s : Present s o₁) (h₁t : Present t o₁) (h₂s : Present s o₂) (h₂t : Present t o₂)
    (hr : ∀ x y, o₁ = some x → o₂ = some y → rank x + rank y < n) :
    Agree (ixL s o₁) (ixL s o₂) (ixL t o₁) (ixL t o₂) := by
  cases o₁ with
  | none =>
    cases o₂ with
    | none => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | some y =>
      rw [ixL_none, ixL_none, ixL_some, ixL_some]
      have e₁ := ix_pos s y
      have e₂ := ix_pos t y
      exact Or.inl ⟨by omega, by omega⟩
  | some x =>
    cases o₂ with
    | none =>
      rw [ixL_none, ixL_none, ixL_some, ixL_some]
      have e₁ := ix_pos s x
      have e₂ := ix_pos t x
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    | some y =>
      rw [ixL_some, ixL_some, ixL_some, ixL_some]
      obtain ⟨u, hus, hut, eu⟩ := common_of_present hc (h₁s x rfl) (h₁t x rfl)
      obtain ⟨v, hvs, hvt, ev⟩ := common_of_present hc (h₂s y rfl) (h₂t y rfl)
      have hr' := hr x y rfl rfl
      rw [← eu, ← ev] at hr' ⊢
      exact agree_items hus (ih u v hr' hus hut hvs hvt) (ih v u (by omega) hvs hvt hus hut)

end

/-- Two legal sequences order their common items the same way. -/
theorem stable {s t : List Item} (hs : Legal s) (ht : Legal t) (hc : Compat s t) :
    ∀ a b, a ∈ s → a ∈ t → b ∈ s → b ∈ t → ix s a.id < ix s b.id → ix t a.id < ix t b.id := by
  obtain ⟨rank, hrank⟩ := hs.acyclic
  have key : ∀ n, StableBelow s t rank n := by
    intro n
    induction n with
    | zero =>
      intro a b h
      omega
    | succ n ih =>
      intro a b hn has hat hbs hbt hlt
      by_cases hgoal : ix t a.id < ix t b.id
      · exact hgoal
      · exfalso
        have hne : ix t a.id ≠ ix t b.id := by
          intro e
          have hab : a.id = b.id := ix_inj e (ix_mem hat)
          rw [hab] at hlt
          omega
        have htlt : ix t b.id < ix t a.id := by omega
        have ral : ∀ x, a.left = some x → rank x < rank a.id :=
          fun x hx => hrank a has x (Or.inl hx)
        have rar : ∀ x, a.right = some x → rank x < rank a.id :=
          fun x hx => hrank a has x (Or.inr hx)
        have rbl : ∀ x, b.left = some x → rank x < rank b.id :=
          fun x hx => hrank b hbs x (Or.inl hx)
        have rbr : ∀ x, b.right = some x → rank x < rank b.id :=
          fun x hx => hrank b hbs x (Or.inr hx)
        have A1 := agreeL hc ih (hs.left_present has) (ht.left_present hat) hbs hbt
          (fun x hx => by have := ral x hx; omega)
        have A2 := agreeR hc ih (hs.right_mem a has) (ht.right_mem a hat) hbs hbt
          (fun x hx => by have := rar x hx; omega)
        have A3 := agreeL hc ih (hs.left_present hbs) (ht.left_present hbt) has hat
          (fun x hx => by have := rbl x hx; omega)
        have A4 := agreeR hc ih (hs.right_mem b hbs) (ht.right_mem b hbt) has hat
          (fun x hx => by have := rbr x hx; omega)
        have A5 := agreeLL hc ih (hs.left_present has) (ht.left_present hat)
          (hs.left_present hbs) (ht.left_present hbt)
          (fun x y hx hy => by have := ral x hx; have := rbl y hy; omega)
        have ws1 := hs.left_lt a has
        have ws2 := hs.lt_right a has
        have ws3 := hs.left_lt b hbs
        have ws4 := hs.lt_right b hbs
        have wt1 := ht.left_lt a hat
        have wt2 := ht.lt_right a hat
        have wt3 := ht.left_lt b hbt
        have wt4 := ht.lt_right b hbt
        have Rs : ix s a.id ≤ ixL s b.left ∨ ixR s a.right ≤ ix s b.id ∨
            ixL s b.left < ixL s a.left ∨
            (ixL s a.left = ixL s b.left ∧ ixL t a.left = ixL t b.left ∧
              a.id.client < b.id.client) := by
          rcases hs.rule a has b hbs hlt with r | r | r | ⟨r₁, r₂⟩
          · exact Or.inl r
          · exact Or.inr (Or.inl r)
          · exact Or.inr (Or.inr (Or.inl r))
          · exact Or.inr (Or.inr (Or.inr ⟨by rw [r₁], by rw [r₁], r₂⟩))
        have Rt : ix t b.id ≤ ixL t a.left ∨ ixR t b.right ≤ ix t a.id ∨
            ixL t a.left < ixL t b.left ∨
            (ixL s b.left = ixL s a.left ∧ ixL t b.left = ixL t a.left ∧
              b.id.client < a.id.client) := by
          rcases ht.rule b hbt a hat htlt with r | r | r | ⟨r₁, r₂⟩
          · exact Or.inl r
          · exact Or.inr (Or.inl r)
          · exact Or.inr (Or.inr (Or.inl r))
          · exact Or.inr (Or.inr (Or.inr ⟨by rw [r₁], by rw [r₁], r₂⟩))
        unfold Agree at A1 A2 A3 A4 A5
        rcases Rs with r | r | r | r <;> rcases Rt with q | q | q | q <;> omega
  intro a b
  exact key _ a b (Nat.lt_succ_self _)

theorem stable_iff {s t : List Item} (hs : Legal s) (ht : Legal t) (hc : Compat s t)
    {a b : Item} (has : a ∈ s) (hat : a ∈ t) (hbs : b ∈ s) (hbt : b ∈ t) :
    ix s a.id < ix s b.id ↔ ix t a.id < ix t b.id :=
  ⟨stable hs ht hc a b has hat hbs hbt, stable ht hs hc.symm a b hat has hbt hbs⟩

theorem stable_le {s t : List Item} (hs : Legal s) (ht : Legal t) (hc : Compat s t)
    {a b : Item} (has : a ∈ s) (hat : a ∈ t) (hbs : b ∈ s) (hbt : b ∈ t)
    (h : ix s a.id ≤ ix s b.id) : ix t a.id ≤ ix t b.id := by
  by_cases e : ix s a.id = ix s b.id
  · have hab : a.id = b.id := ix_inj e (ix_mem has)
    rw [hab]
    exact Nat.le_refl _
  · have := stable hs ht hc a b has hat hbs hbt (by omega)
    omega

/-- Two sequences with the same items in the same relative order are equal. -/
theorem eq_of_order {s t : List Item} (hs : NodupIds s) (ht : NodupIds t)
    (hm : ∀ a, a ∈ s ↔ a ∈ t)
    (ho : ∀ a b, a ∈ s → b ∈ s → ix s a.id < ix s b.id → ix t a.id < ix t b.id) : s = t := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => rfl
    | cons b t' =>
      have hb := (hm b).mpr (List.mem_cons_self ..)
      cases hb
  | cons a s' ih =>
    cases t with
    | nil =>
      have ha := (hm a).mp (List.mem_cons_self ..)
      cases ha
    | cons b t' =>
      have hs' := List.pairwise_cons.mp hs
      have ht' := List.pairwise_cons.mp ht
      have hab : b = a := by
        by_cases e : b = a
        · exact e
        · exfalso
          have hbs : b ∈ a :: s' := (hm b).mpr (List.mem_cons_self ..)
          have hbs' : b ∈ s' := by
            rcases List.mem_cons.mp hbs with h | h
            · exact absurd h e
            · exact h
          have hne : a.id ≠ b.id := hs'.1 b hbs'
          have h1 : ix (a :: s') a.id < ix (a :: s') b.id := by
            rw [ix_cons_self, ix_cons_ne hne]
            have := ix_pos s' b.id
            omega
          have h2 := ho a b (List.mem_cons_self ..) hbs h1
          rw [ix_cons_self] at h2
          have := ix_pos (b :: t') a.id
          omega
      rw [hab] at ht' hm ho ⊢
      congr 1
      apply ih hs'.2 ht'.2
      · intro x
        constructor
        · intro hx
          rcases List.mem_cons.mp ((hm x).mp (List.mem_cons_of_mem _ hx)) with h | h
          · exfalso
            rw [h] at hx
            exact hs'.1 a hx rfl
          · exact h
        · intro hx
          rcases List.mem_cons.mp ((hm x).mpr (List.mem_cons_of_mem _ hx)) with h | h
          · exfalso
            rw [h] at hx
            exact ht'.1 a hx rfl
          · exact h
      · intro x y hx hy hlt
        have hxa : a.id ≠ x.id := hs'.1 x hx
        have hya : a.id ≠ y.id := hs'.1 y hy
        have h := ho x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)
          (by rw [ix_cons_ne hxa, ix_cons_ne hya]; omega)
        rw [ix_cons_ne hxa, ix_cons_ne hya] at h
        omega

/-- A legal sequence is determined by its items. -/
theorem legal_unique {s t : List Item} (hs : Legal s) (ht : Legal t) (hc : Compat s t)
    (hm : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  eq_of_order hs.nodup ht.nodup hm
    (fun a b ha hb h => stable hs ht hc a b ha ((hm a).mp ha) hb ((hm b).mp hb) h)

end YoctoSpec
