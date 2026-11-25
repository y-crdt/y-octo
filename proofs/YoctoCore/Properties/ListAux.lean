/-
Lists by index: updating, inserting and removing at a position, stated with
`l[i]?` so that no proof of a bound is carried around. Only Lean core is used.
-/

set_option autoImplicit false

namespace YoctoCore.Properties.ListAux

variable {α β γ : Type}

theorem get?_lt {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : i < l.length := by
  induction l generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero => simp
    | succ j =>
      have h' : t[j]? = some a := by simpa using h
      have := ih h'
      simp only [List.length_cons]
      omega

theorem get?_none {l : List α} {i : Nat} (h : l.length ≤ i) : l[i]? = none := by
  induction l generalizing i with
  | nil => simp
  | cons x t ih =>
    cases i with
    | zero => simp at h
    | succ j =>
      have h' : t.length ≤ j := by simp only [List.length_cons] at h; omega
      simpa using ih h'

theorem get?_none_le {l : List α} {i : Nat} (h : l[i]? = none) : l.length ≤ i := by
  induction l generalizing i with
  | nil => simp
  | cons x t ih =>
    cases i with
    | zero => simp at h
    | succ j =>
      have h' : t[j]? = none := by simpa using h
      have := ih h'
      simp only [List.length_cons]
      omega

theorem get?_some {l : List α} {i : Nat} (h : i < l.length) : ∃ a, l[i]? = some a := by
  induction l generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero => exact ⟨x, by simp⟩
    | succ j =>
      have h' : j < t.length := by simp only [List.length_cons] at h; omega
      obtain ⟨a, ha⟩ := ih h'
      exact ⟨a, by simpa using ha⟩

theorem get?_mem {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : a ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero =>
      have e : x = a := by simpa using h
      rw [e]
      exact List.mem_cons_self ..
    | succ j =>
      have h' : t[j]? = some a := by simpa using h
      exact List.mem_cons_of_mem _ (ih h')

theorem mem_get? {l : List α} {a : α} (h : a ∈ l) : ∃ i : Nat, l[i]? = some a := by
  induction l with
  | nil => cases h
  | cons x t ih =>
    rcases List.mem_cons.mp h with e | h'
    · exact ⟨0, by simp [e]⟩
    · obtain ⟨i, hi⟩ := ih h'
      exact ⟨i + 1, by simpa using hi⟩

theorem get?_append_left {l r : List α} {i : Nat} (h : i < l.length) : (l ++ r)[i]? = l[i]? := by
  induction l generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero => simp
    | succ j =>
      have h' : j < t.length := by simp only [List.length_cons] at h; omega
      simpa using ih h'

theorem get?_append_right (l r : List α) (i : Nat) : (l ++ r)[l.length + i]? = r[i]? := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have e : (x :: t).length + i = (t.length + i) + 1 := by simp only [List.length_cons]; omega
    rw [e]
    simpa using ih

theorem get?_map (f : α → β) (l : List α) (i : Nat) : (l.map f)[i]? = (l[i]?).map f := by
  induction l generalizing i with
  | nil => simp
  | cons x t ih =>
    cases i with
    | zero => simp
    | succ j => simp

theorem ext_get? {l r : List α} (h : ∀ i : Nat, l[i]? = r[i]?) : l = r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => rfl
    | cons y u =>
      have := h 0
      simp at this
  | cons x t ih =>
    cases r with
    | nil =>
      have := h 0
      simp at this
    | cons y u =>
      have h0 := h 0
      have e : x = y := by simpa using h0
      have ht : t = u := ih (fun i => by simpa using h (i + 1))
      rw [e, ht]

/-! ### Updating a position -/

/-- `l` with `f` applied to its element at `i`; `l` itself beyond its end. -/
def upd : List α → Nat → (α → α) → List α
  | [], _, _ => []
  | a :: t, 0, f => f a :: t
  | a :: t, i + 1, f => a :: upd t i f

@[simp] theorem length_upd (l : List α) (i : Nat) (f : α → α) : (upd l i f).length = l.length := by
  induction l generalizing i with
  | nil => rfl
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ j => simp [upd, ih]

theorem get?_upd_self (l : List α) (i : Nat) (f : α → α) : (upd l i f)[i]? = (l[i]?).map f := by
  induction l generalizing i with
  | nil => simp [upd]
  | cons x t ih =>
    cases i with
    | zero => simp [upd]
    | succ j => simpa [upd] using ih j

theorem get?_upd_ne (l : List α) {i j : Nat} (f : α → α) (h : j ≠ i) : (upd l i f)[j]? = l[j]? := by
  induction l generalizing i j with
  | nil => simp [upd]
  | cons x t ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl h
      | succ k => simp [upd]
    | succ i' =>
      cases j with
      | zero => simp [upd]
      | succ k =>
        have h' : k ≠ i' := fun e => h (by rw [e])
        simpa [upd] using ih h'

theorem get?_upd (l : List α) (i j : Nat) (f : α → α) :
    (upd l i f)[j]? = if j = i then (l[j]?).map f else l[j]? := by
  by_cases h : j = i
  · rw [ite_eq_left h, h]
    exact get?_upd_self l i f
  · rw [ite_eq_right h]
    exact get?_upd_ne l f h

theorem set_eq_upd (l : List α) (i : Nat) (a : α) : l.set i a = upd l i (fun _ => a) := by
  induction l generalizing i with
  | nil => simp [upd]
  | cons x t ih =>
    cases i with
    | zero => simp [upd]
    | succ j => simp [upd, ih]

theorem map_upd (g : α → β) (l : List α) (i : Nat) (f : α → α) (f' : β → β)
    (h : ∀ a, g (f a) = f' (g a)) : (upd l i f).map g = upd (l.map g) i f' := by
  induction l generalizing i with
  | nil => rfl
  | cons x t ih =>
    cases i with
    | zero => simp [upd, h]
    | succ j => simp [upd, ih]

/-! ### Inserting at a position -/

/-- `a` inserted before position `i` of `l`; at the end beyond it. -/
def insAt : List α → Nat → α → List α
  | l, 0, a => a :: l
  | [], _ + 1, a => [a]
  | x :: t, i + 1, a => x :: insAt t i a

@[simp] theorem length_insAt (l : List α) (i : Nat) (a : α) : (insAt l i a).length = l.length + 1 := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ j => simp [insAt, ih]

theorem get?_insAt_lt (l : List α) {i j : Nat} (a : α) (h : j < i) (hi : i ≤ l.length) :
    (insAt l i a)[j]? = l[j]? := by
  induction l generalizing i j with
  | nil =>
    simp only [List.length_nil] at hi
    omega
  | cons x t ih =>
    cases i with
    | zero => omega
    | succ i' =>
      cases j with
      | zero => simp [insAt]
      | succ k =>
        have hi' : i' ≤ t.length := by simp only [List.length_cons] at hi; omega
        simpa [insAt] using ih (by omega) hi'

theorem get?_insAt_self (l : List α) {i : Nat} (a : α) (hi : i ≤ l.length) :
    (insAt l i a)[i]? = some a := by
  induction l generalizing i with
  | nil =>
    have e : i = 0 := by simp only [List.length_nil] at hi; omega
    rw [e]
    simp [insAt]
  | cons x t ih =>
    cases i with
    | zero => simp [insAt]
    | succ i' =>
      have hi' : i' ≤ t.length := by simp only [List.length_cons] at hi; omega
      simpa [insAt] using ih hi'

theorem get?_insAt_gt (l : List α) {i j : Nat} (a : α) (h : i ≤ j) :
    (insAt l i a)[j + 1]? = l[j]? := by
  induction l generalizing i j with
  | nil =>
    cases i with
    | zero => simp [insAt]
    | succ i' => simp [insAt]
  | cons x t ih =>
    cases i with
    | zero => simp [insAt]
    | succ i' =>
      cases j with
      | zero => omega
      | succ k => simpa [insAt] using ih (by omega : i' ≤ k)

theorem mem_insAt {l : List α} {i : Nat} {a x : α} : x ∈ insAt l i a ↔ x = a ∨ x ∈ l := by
  induction l generalizing i with
  | nil => cases i <;> simp [insAt]
  | cons y t ih =>
    cases i with
    | zero => simp [insAt]
    | succ j =>
      simp only [insAt, List.mem_cons, ih]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem nodup_insAt {l : List α} {i : Nat} {a : α} (hn : l.Nodup) (ha : ¬ a ∈ l) :
    (insAt l i a).Nodup := by
  induction l generalizing i with
  | nil => cases i <;> simp [insAt]
  | cons y t ih =>
    cases i with
    | zero => exact List.nodup_cons.mpr ⟨ha, hn⟩
    | succ j =>
      have hn' := List.nodup_cons.mp hn
      have hy : ¬ a = y := fun e => ha (by rw [e]; exact List.mem_cons_self ..)
      have hat : ¬ a ∈ t := fun h => ha (List.mem_cons_of_mem _ h)
      refine List.nodup_cons.mpr ⟨?_, ih hn'.2 hat⟩
      intro hmem
      rcases mem_insAt.mp hmem with e | h
      · exact hy e.symm
      · exact hn'.1 h

theorem map_insAt (g : α → β) (l : List α) (i : Nat) (a : α) :
    (insAt l i a).map g = insAt (l.map g) i (g a) := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ j => simp [insAt, ih]

theorem insAt_length (l : List α) (a : α) : insAt l l.length a = l ++ [a] := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [insAt, ih]

/-- `insAt` is `take ++ a :: drop`. -/
theorem insAt_eq (l : List α) (i : Nat) (a : α) : insAt l i a = l.take i ++ a :: l.drop i := by
  induction l generalizing i with
  | nil => cases i <;> simp [insAt]
  | cons x t ih =>
    cases i with
    | zero => simp [insAt]
    | succ j => simp [insAt, ih]

/-! ### Removing a position -/

/-- `l` without its element at `i`. -/
def delAt : List α → Nat → List α
  | [], _ => []
  | _ :: t, 0 => t
  | x :: t, i + 1 => x :: delAt t i

theorem length_delAt (l : List α) {i : Nat} (h : i < l.length) : (delAt l i).length + 1 = l.length := by
  induction l generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ j =>
      have h' : j < t.length := by simp only [List.length_cons] at h; omega
      have := ih h'
      simp only [delAt, List.length_cons]
      omega

theorem get?_delAt_lt (l : List α) {i j : Nat} (h : j < i) : (delAt l i)[j]? = l[j]? := by
  induction l generalizing i j with
  | nil => simp [delAt]
  | cons x t ih =>
    cases i with
    | zero => omega
    | succ i' =>
      cases j with
      | zero => simp [delAt]
      | succ k => simpa [delAt] using ih (by omega : k < i')

theorem get?_delAt_ge (l : List α) {i j : Nat} (h : i ≤ j) : (delAt l i)[j]? = l[j + 1]? := by
  induction l generalizing i j with
  | nil => simp [delAt]
  | cons x t ih =>
    cases i with
    | zero => simp [delAt]
    | succ i' =>
      cases j with
      | zero => omega
      | succ k => simpa [delAt] using ih (by omega : i' ≤ k)

theorem mem_delAt {l : List α} {i : Nat} {x : α} (h : x ∈ delAt l i) : x ∈ l := by
  induction l generalizing i with
  | nil => simp [delAt] at h
  | cons y t ih =>
    cases i with
    | zero => exact List.mem_cons_of_mem _ h
    | succ j =>
      rcases List.mem_cons.mp h with e | h'
      · rw [e]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h')

theorem nodup_delAt {l : List α} {i : Nat} (hn : l.Nodup) : (delAt l i).Nodup := by
  induction l generalizing i with
  | nil => simp [delAt]
  | cons y t ih =>
    have hn' := List.nodup_cons.mp hn
    cases i with
    | zero => exact hn'.2
    | succ j => exact List.nodup_cons.mpr ⟨fun h => hn'.1 (mem_delAt h), ih hn'.2⟩

theorem map_delAt (g : α → β) (l : List α) (i : Nat) : (delAt l i).map g = delAt (l.map g) i := by
  induction l generalizing i with
  | nil => rfl
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ j => simp [delAt, ih]

/-- `delAt` is `take ++ drop`. -/
theorem delAt_eq (l : List α) (i : Nat) : delAt l i = l.take i ++ l.drop (i + 1) := by
  induction l generalizing i with
  | nil => simp [delAt]
  | cons x t ih =>
    cases i with
    | zero => simp [delAt]
    | succ j => simp [delAt, ih]

/-! ### Distinct elements below a bound -/

theorem nodup_get?_inj {l : List α} (hn : l.Nodup) {i j : Nat} {a : α} (hi : l[i]? = some a)
    (hj : l[j]? = some a) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x t ih =>
    have hn' := List.nodup_cons.mp hn
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ k =>
        have e : x = a := by simpa using hi
        have hk : t[k]? = some a := by simpa using hj
        exact absurd (get?_mem hk) (by rw [← e]; exact hn'.1)
    | succ i' =>
      have hi' : t[i']? = some a := by simpa using hi
      cases j with
      | zero =>
        have e : x = a := by simpa using hj
        exact absurd (get?_mem hi') (by rw [← e]; exact hn'.1)
      | succ k =>
        have hk : t[k]? = some a := by simpa using hj
        rw [ih hn'.2 hi' hk]

/-- Distinct numbers below `n` are at most `n`. -/
theorem nodup_length_le : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ i, i ∈ l → i < n) → l.length ≤ n := by
  intro n
  induction n with
  | zero =>
    intro l _ hb
    cases l with
    | nil => simp
    | cons x t => exact absurd (hb x (List.mem_cons_self ..)) (by omega)
  | succ n ih =>
    intro l hn hb
    -- `l'` is `l` without `n`: at most one shorter
    have key : ∀ (l : List Nat), l.Nodup →
        ∃ l' : List Nat, l'.Nodup ∧ (∀ i, i ∈ l' ↔ i ∈ l ∧ i ≠ n) ∧ l.length ≤ l'.length + 1 ∧
          (¬ n ∈ l → l.length ≤ l'.length) := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨[], List.nodup_nil, fun i => by simp, by simp, fun _ => by simp⟩
      | cons x t iht =>
        intro hn
        have hn' := List.nodup_cons.mp hn
        obtain ⟨t', ht1, ht2, ht3, ht4⟩ := iht hn'.2
        by_cases hx : x = n
        · have hnt : ¬ n ∈ t := by rw [← hx]; exact hn'.1
          refine ⟨t', ht1, ?_, ?_, ?_⟩
          · intro i
            rw [ht2 i, List.mem_cons]
            constructor
            · intro h
              exact ⟨Or.inr h.1, h.2⟩
            · rintro ⟨h | h, h'⟩
              · exact absurd (h.trans hx) h'
              · exact ⟨h, h'⟩
          · have := ht4 hnt
            simp only [List.length_cons]
            omega
          · intro h
            exact absurd (by rw [hx]; exact List.mem_cons_self ..) h
        · have hxt' : ¬ x ∈ t' := fun h => hn'.1 ((ht2 x).mp h).1
          refine ⟨x :: t', List.nodup_cons.mpr ⟨hxt', ht1⟩, ?_, ?_, ?_⟩
          · intro i
            simp only [List.mem_cons, ht2 i]
            constructor
            · rintro (h | h)
              · exact ⟨Or.inl h, by rw [h]; exact hx⟩
              · exact ⟨Or.inr h.1, h.2⟩
            · rintro ⟨h | h, h'⟩
              · exact Or.inl h
              · exact Or.inr ⟨h, h'⟩
          · simp only [List.length_cons]
            omega
          · intro h
            have hnt : ¬ n ∈ t := fun h' => h (List.mem_cons_of_mem _ h')
            have := ht4 hnt
            simp only [List.length_cons]
            omega
    obtain ⟨l', h1, h2, h3, _⟩ := key l hn
    have hb' : ∀ i, i ∈ l' → i < n := by
      intro i hi
      have hi' := (h2 i).mp hi
      have := hb i hi'.1
      omega
    have := ih l' h1 hb'
    omega

/-! ### Members of an updated list -/

theorem get?_upd_cases {l : List α} {i j : Nat} {f : α → α} {x : α} (h : (upd l i f)[j]? = some x) :
    (j = i ∧ ∃ a, l[i]? = some a ∧ x = f a) ∨ (j ≠ i ∧ l[j]? = some x) := by
  rw [get?_upd] at h
  by_cases e : j = i
  · rw [ite_eq_left e, e] at h
    refine Or.inl ⟨e, ?_⟩
    cases ha : l[i]? with
    | none =>
      rw [ha] at h
      cases h
    | some a =>
      rw [ha] at h
      exact ⟨a, rfl, (Option.some.inj h).symm⟩
  · rw [ite_eq_right e] at h
    exact Or.inr ⟨e, h⟩

theorem mem_upd {l : List α} {i : Nat} {f : α → α} {x : α} (h : x ∈ upd l i f) :
    (∃ a, l[i]? = some a ∧ x = f a) ∨ (∃ j, j ≠ i ∧ l[j]? = some x) := by
  obtain ⟨j, hj⟩ := mem_get? h
  rcases get?_upd_cases hj with ⟨_, h'⟩ | ⟨e, h'⟩
  · exact Or.inl h'
  · exact Or.inr ⟨j, e, h'⟩

theorem upd_mem_self {l : List α} {i : Nat} {f : α → α} {a : α} (h : l[i]? = some a) :
    f a ∈ upd l i f :=
  get?_mem (i := i) (by rw [get?_upd_self, h]; rfl)

theorem upd_mem_other {l : List α} {i j : Nat} {f : α → α} {x : α} (hj : j ≠ i)
    (h : l[j]? = some x) : x ∈ upd l i f :=
  get?_mem (i := j) (by rw [get?_upd_ne l f hj]; exact h)

theorem get?_insAt_cases {l : List α} {i q : Nat} {a x : α} (hi : i ≤ l.length)
    (h : (insAt l i a)[q]? = some x) :
    (q < i ∧ l[q]? = some x) ∨ (q = i ∧ x = a) ∨ (∃ q', q = q' + 1 ∧ i ≤ q' ∧ l[q']? = some x) := by
  by_cases c1 : q < i
  · rw [get?_insAt_lt l a c1 hi] at h
    exact Or.inl ⟨c1, h⟩
  · by_cases c2 : q = i
    · rw [c2, get?_insAt_self l a hi] at h
      exact Or.inr (Or.inl ⟨c2, (Option.some.inj h).symm⟩)
    · obtain ⟨q', e⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [e, get?_insAt_gt l a (by omega : i ≤ q')] at h
      exact Or.inr (Or.inr ⟨q', e, by omega, h⟩)

/-! ### `flatMap` over an order -/

theorem flatMap_congr_mem {l : List α} {F G : α → List β} (h : ∀ a, a ∈ l → F a = G a) :
    l.flatMap F = l.flatMap G := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

theorem map_congr_mem {l : List α} {g g' : α → β} (h : ∀ a, a ∈ l → g a = g' a) :
    l.map g = l.map g' := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.map_cons, List.map_cons, h x (List.mem_cons_self ..),
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

theorem flatMap_map (g : α → β) (F : β → List γ) (l : List α) :
    (l.map g).flatMap F = l.flatMap (fun a => F (g a)) := by
  induction l with
  | nil => rfl
  | cons x t ih => rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]

theorem flatMap_singleton (g : α → β) (l : List α) : l.flatMap (fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.flatMap_cons, List.map_cons, ih]
    rfl

/-- Mapping an order with one more slot after `i`: `i` gives two elements. -/
theorem map_insAt_after [DecidableEq α] (g : α → β) (n : α) :
    ∀ (o : List α) (k : Nat) (i : α), o.Nodup → o[k]? = some i →
      (insAt o (k + 1) n).map g = o.flatMap (fun j => if j = i then [g i, g n] else [g j]) := by
  intro o
  induction o with
  | nil =>
    intro k i _ h
    simp at h
  | cons a t ih =>
    intro k i hn hk
    have hn' := List.nodup_cons.mp hn
    cases k with
    | zero =>
      have e : a = i := by simpa using hk
      have hrest : t.flatMap (fun j => if j = i then [g i, g n] else [g j]) = t.map g := by
        rw [← flatMap_singleton g t]
        apply flatMap_congr_mem
        intro j hj
        have hne : ¬ j = i := fun e' => hn'.1 (by rw [e, ← e']; exact hj)
        rw [ite_eq_right hne]
      rw [List.flatMap_cons, ite_eq_left e, hrest, e]
      simp [insAt]
    | succ k' =>
      have hk' : t[k']? = some i := by simpa using hk
      have hne : ¬ a = i := fun e => hn'.1 (by rw [e]; exact get?_mem hk')
      rw [List.flatMap_cons, ite_eq_right hne, ← ih k' i hn'.2 hk']
      simp [insAt]

/-! ### One more element at the end -/

theorem get?_snoc_cases {l : List α} {a x : α} {q : Nat} (h : (l ++ [a])[q]? = some x) :
    (q < l.length ∧ l[q]? = some x) ∨ (q = l.length ∧ x = a) := by
  by_cases c1 : q < l.length
  · rw [get?_append_left c1] at h
    exact Or.inl ⟨c1, h⟩
  · have hq : q < (l ++ [a]).length := get?_lt h
    simp only [List.length_append, List.length_cons, List.length_nil] at hq
    have e : q = l.length := by omega
    rw [e] at h
    have h' := get?_append_right l [a] 0
    simp only [Nat.add_zero] at h'
    rw [h'] at h
    have e2 : a = x := by simpa using h
    exact Or.inr ⟨e, e2.symm⟩

theorem get?_snoc_last (l : List α) (a : α) : (l ++ [a])[l.length]? = some a := by
  have h' := get?_append_right l [a] 0
  simp only [Nat.add_zero] at h'
  rw [h']
  simp

/-! ### The rest of a list from a position -/

theorem get?_drop_zero (l : List α) (k : Nat) : (l.drop k)[0]? = l[k]? := by
  simp

theorem map_drop' (g : α → β) (l : List α) (k : Nat) : (l.drop k).map g = (l.map g).drop k := by
  simp

theorem length_drop_le (l : List α) (k : Nat) : (l.drop k).length ≤ l.length := by
  induction l generalizing k with
  | nil => simp
  | cons x t ih =>
    cases k with
    | zero => simp
    | succ k' =>
      have := ih k'
      simp only [List.drop_succ_cons, List.length_cons]
      omega

theorem upd_eq_self {l : List α} {i : Nat} {f : α → α} (h : ∀ a, l[i]? = some a → f a = a) :
    upd l i f = l := by
  apply ext_get?
  intro j
  by_cases e : j = i
  · subst e
    rw [get?_upd_self]
    cases hj : l[j]? with
    | none => rfl
    | some a => simp [h a hj]
  · rw [get?_upd_ne l f e]

theorem set_eq_self {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : l.set i a = l := by
  rw [set_eq_upd]
  apply upd_eq_self
  intro b hb
  rw [h] at hb
  exact Option.some.inj hb

theorem take_succ_get : ∀ {l : List α} {i : Nat} {a : α}, l[i]? = some a →
    l.take (i + 1) = l.take i ++ [a]
  | [], i, a, h => by simp at h
  | x :: t, 0, a, h => by
    simp at h
    simp [h]
  | x :: t, i + 1, a, h => by
    have h' : t[i]? = some a := by simpa using h
    simp [take_succ_get h']

theorem drop_eq_cons_get : ∀ {l : List α} {i : Nat} {a : α}, l[i]? = some a →
    l.drop i = a :: l.drop (i + 1)
  | [], i, a, h => by simp at h
  | x :: t, 0, a, h => by
    simp at h
    simp [h]
  | x :: t, i + 1, a, h => by
    have h' : t[i]? = some a := by simpa using h
    simpa using drop_eq_cons_get h'

theorem get?_delAt_cases {l : List α} {i q : Nat} {x : α} (h : (delAt l i)[q]? = some x) :
    (q < i ∧ l[q]? = some x) ∨ (i ≤ q ∧ l[q + 1]? = some x) := by
  by_cases hq : q < i
  · rw [get?_delAt_lt l hq] at h
    exact Or.inl ⟨hq, h⟩
  · rw [get?_delAt_ge l (by omega : i ≤ q)] at h
    exact Or.inr ⟨by omega, h⟩

theorem insertIdx_eq_insAt : ∀ (l : List α) (i : Nat) (a : α), i ≤ l.length →
    l.insertIdx i a = insAt l i a
  | l, 0, a, _ => by simp [insAt]
  | [], i + 1, a, h => by simp at h
  | x :: t, i + 1, a, h => by
    have h' : i ≤ t.length := by simpa using h
    simp [insAt, insertIdx_eq_insAt t i a h']

theorem set_eq_upd_get {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) (f : α → α) :
    l.set i (f a) = upd l i f := by
  rw [set_eq_upd]
  apply ext_get?
  intro j
  rw [get?_upd, get?_upd]
  by_cases e : j = i
  · rw [e]
    simp [h]
  · simp [e]

theorem map_set_get (g : α → β) {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) (b : α)
    (f' : β → β) (hb : g b = f' (g a)) : (l.set i b).map g = upd (l.map g) i f' := by
  apply ext_get?
  intro j
  rw [get?_map, set_eq_upd, get?_upd, get?_upd, get?_map]
  by_cases e : j = i
  · rw [e]
    simp [h, hb]
  · simp [e]

theorem set_append_length : ∀ (l : List α) (x y : α) (r : List α),
    (l ++ x :: r).set l.length y = l ++ y :: r
  | [], _, _, _ => rfl
  | a :: t, x, y, r => by
    show a :: (t ++ x :: r).set t.length y = a :: (t ++ y :: r)
    rw [set_append_length t x y r]

end YoctoCore.Properties.ListAux
