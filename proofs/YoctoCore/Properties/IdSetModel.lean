/-
Open addressing with linear probing, on lists: what `y_octo_core::id_set`
keeps in its table, without the extracted code. Only Lean core is used.

A table is a list of slots, `none` for a free one. The probing of an element
starts at its home slot and goes from a slot to the next one, around the end
of the table (`slotAt`). `TableOK` says that every element of the table is
reached from its home slot without meeting a free slot: then a probe that
meets a free slot, or that went around the table, has shown that the element
is not there (`not_mem_of_free`, `not_mem_of_full`), and putting an element
into the free slot its probe ends at keeps `TableOK` (`TableOK.set`).
`countSome` counts the taken slots: a table with fewer taken slots than slots
has a free one on the way of every probe (`exists_free_step`).
-/
import YoctoCore.Properties.ListAux

set_option autoImplicit false

namespace YoctoCore.Properties.IdSetModel

open YoctoCore.Properties.ListAux

variable {α : Type}

/-! ## The way of a probe -/

/-- The slot after `i` in a table of `cap` slots. -/
def nextSlot (cap i : Nat) : Nat := if i + 1 = cap then 0 else i + 1

/-- The slot a probe from `h` looks at after `t` steps. -/
def slotAt (cap h : Nat) : Nat → Nat
  | 0 => h
  | t + 1 => nextSlot cap (slotAt cap h t)

theorem nextSlot_lt {cap i : Nat} (hi : i < cap) : nextSlot cap i < cap := by
  unfold nextSlot
  by_cases e : i + 1 = cap
  · rw [ite_eq_left e]
    omega
  · rw [ite_eq_right e]
    omega

theorem slotAt_lt {cap h : Nat} (hh : h < cap) : ∀ t, slotAt cap h t < cap
  | 0 => hh
  | t + 1 => nextSlot_lt (slotAt_lt hh t)

/-- Before the end of the table a probe goes straight on. -/
theorem slotAt_straight {cap h : Nat} : ∀ t, h + t < cap → slotAt cap h t = h + t
  | 0, _ => rfl
  | t + 1, ht => by
    show nextSlot cap (slotAt cap h t) = h + t + 1
    rw [slotAt_straight t (by omega)]
    unfold nextSlot
    exact ite_eq_right (by omega)

theorem slotAt_add (cap h a : Nat) : ∀ t, slotAt cap h (a + t) = slotAt cap (slotAt cap h a) t
  | 0 => rfl
  | t + 1 => by
    show nextSlot cap (slotAt cap h (a + t)) = nextSlot cap (slotAt cap (slotAt cap h a) t)
    rw [slotAt_add cap h a t]

/-- A probe looks at every slot of the table before it is back home. -/
theorem slotAt_cover {cap h j : Nat} (hh : h < cap) (hj : j < cap) :
    ∃ t, t < cap ∧ slotAt cap h t = j := by
  by_cases hle : h ≤ j
  · refine ⟨j - h, by omega, ?_⟩
    rw [slotAt_straight (j - h) (by omega)]
    omega
  · refine ⟨(cap - h) + j, by omega, ?_⟩
    have hlast : slotAt cap h (cap - h - 1) = cap - 1 := by
      rw [slotAt_straight (cap - h - 1) (by omega)]
      omega
    have hwrap : slotAt cap h (cap - h) = 0 := by
      have e : cap - h = (cap - h - 1) + 1 := by omega
      rw [e]
      show nextSlot cap (slotAt cap h (cap - h - 1)) = 0
      rw [hlast]
      unfold nextSlot
      exact ite_eq_left (by omega)
    rw [slotAt_add, hwrap, slotAt_straight j (by omega), Nat.zero_add]

/-! ## Taken slots -/

/-- How many slots of a table hold an element. -/
def countSome : List (Option α) → Nat
  | [] => 0
  | none :: t => countSome t
  | some _ :: t => countSome t + 1

theorem countSome_le : ∀ l : List (Option α), countSome l ≤ l.length
  | [] => Nat.le_refl 0
  | none :: t => by
    have := countSome_le t
    show countSome t ≤ t.length + 1
    omega
  | some _ :: t => by
    have := countSome_le t
    show countSome t + 1 ≤ t.length + 1
    omega

theorem countSome_append : ∀ (l r : List (Option α)), countSome (l ++ r) = countSome l + countSome r
  | [], r => by
    show countSome r = 0 + countSome r
    omega
  | none :: t, r => countSome_append t r
  | some _ :: t, r => by
    show countSome (t ++ r) + 1 = countSome t + 1 + countSome r
    rw [countSome_append t r]
    omega

theorem countSome_replicate : ∀ n : Nat, countSome (List.replicate n (none : Option α)) = 0
  | 0 => rfl
  | n + 1 => countSome_replicate n

/-- Taking a free slot takes one more slot. -/
theorem countSome_set : ∀ {l : List (Option α)} {i : Nat} (x : α), l[i]? = some none →
    countSome (l.set i (some x)) = countSome l + 1
  | [], i, _, h => by simp at h
  | a :: t, 0, x, h => by
    have e : a = none := by simpa using h
    rw [e]
    rfl
  | none :: t, i + 1, x, h => by
    have h' : t[i]? = some none := by simpa using h
    show countSome (t.set i (some x)) = countSome t + 1
    exact countSome_set x h'
  | some _ :: t, i + 1, x, h => by
    have h' : t[i]? = some none := by simpa using h
    show countSome (t.set i (some x)) + 1 = countSome t + 1 + 1
    rw [countSome_set x h']

/-- A table with fewer taken slots than slots has a free slot. -/
theorem exists_free : ∀ {l : List (Option α)}, countSome l < l.length →
    ∃ j : Nat, l[j]? = some none
  | [], h => by simp [countSome] at h
  | none :: t, _ => ⟨0, rfl⟩
  | some a :: t, h => by
    have h' : countSome t < t.length := by
      have h0 : countSome t + 1 < t.length + 1 := h
      omega
    obtain ⟨j, hj⟩ := exists_free h'
    exact ⟨j + 1, by simpa using hj⟩

/-- A table with a taken slot has a taken slot counted. -/
theorem countSome_pos_of_get : ∀ {l : List (Option α)} {j : Nat} {x : α},
    l[j]? = some (some x) → 0 < countSome l
  | [], j, _, h => by simp at h
  | some _ :: t, _, _, _ => Nat.succ_pos _
  | none :: t, 0, _, h => by simp at h
  | none :: t, j + 1, x, h => by
    have h' : t[j]? = some (some x) := by simpa using h
    show 0 < countSome t
    exact countSome_pos_of_get h'

/-! ## The table -/

/-- An element of the table. -/
def Mem (l : List (Option α)) (x : α) : Prop := some x ∈ l

/-- The first `t` slots a probe from `h` looks at are all taken. -/
def Busy (l : List (Option α)) (h t : Nat) : Prop :=
  ∀ t', t' < t → ∃ y, l[slotAt l.length h t']? = some (some y)

/-- Every element of the table is reached from its home slot without meeting
a free slot. `home` gives the home slot of an element in this table. -/
def TableOK (home : α → Nat) (l : List (Option α)) : Prop :=
  ∀ (j : Nat) (x : α), l[j]? = some (some x) →
    ∃ t, t < l.length ∧ slotAt l.length (home x) t = j ∧ Busy l (home x) t

theorem not_mem_replicate (n : Nat) (x : α) : ¬ Mem (List.replicate n (none : Option α)) x := by
  intro h
  have := List.eq_of_mem_replicate h
  cases this

theorem tableOK_replicate (home : α → Nat) (n : Nat) :
    TableOK home (List.replicate n (none : Option α)) := by
  intro j x hj
  exact absurd (get?_mem hj) (not_mem_replicate n x)

theorem tableOK_nil (home : α → Nat) : TableOK home ([] : List (Option α)) :=
  tableOK_replicate home 0

/-- A probe that meets a free slot after `t` taken slots that do not hold `x`
has shown that `x` is not in the table. -/
theorem not_mem_of_free {home : α → Nat} {l : List (Option α)} (hok : TableOK home l) {x : α}
    {t : Nat}
    (hseen : ∀ t', t' < t → ∃ y, l[slotAt l.length (home x) t']? = some (some y) ∧ y ≠ x)
    (hfree : l[slotAt l.length (home x) t]? = some none) : ¬ Mem l x := by
  intro hm
  obtain ⟨j, hj⟩ := mem_get? hm
  obtain ⟨t0, _, e0, hb⟩ := hok j x hj
  by_cases h1 : t0 < t
  · obtain ⟨y, hy, hne⟩ := hseen t0 h1
    rw [e0, hj] at hy
    exact hne (Option.some.inj (Option.some.inj hy)).symm
  · by_cases h2 : t0 = t
    · rw [← h2, e0, hj] at hfree
      cases Option.some.inj hfree
    · obtain ⟨y, hy⟩ := hb t (by omega)
      rw [hfree] at hy
      cases Option.some.inj hy

/-- A probe that went around the table over taken slots that do not hold `x`
has shown that `x` is not in the table. -/
theorem not_mem_of_full {home : α → Nat} {l : List (Option α)} (hok : TableOK home l) {x : α}
    (hseen : ∀ t', t' < l.length →
      ∃ y, l[slotAt l.length (home x) t']? = some (some y) ∧ y ≠ x) : ¬ Mem l x := by
  intro hm
  obtain ⟨j, hj⟩ := mem_get? hm
  obtain ⟨t0, h0, e0, _⟩ := hok j x hj
  obtain ⟨y, hy, hne⟩ := hseen t0 h0
  rw [e0, hj] at hy
  exact hne (Option.some.inj (Option.some.inj hy)).symm

/-- In a table with a free slot no probe goes around the table over taken
slots only. -/
theorem exists_free_step {l : List (Option α)} {h : Nat} (hh : h < l.length)
    (hc : countSome l < l.length) : ¬ Busy l h l.length := by
  intro hb
  obtain ⟨j, hj⟩ := exists_free hc
  obtain ⟨t, ht, e⟩ := slotAt_cover hh (get?_lt hj)
  obtain ⟨y, hy⟩ := hb t ht
  rw [e, hj] at hy
  cases Option.some.inj hy

theorem get?_set_self {l : List (Option α)} {i : Nat} (v : Option α) (hi : i < l.length) :
    (l.set i v)[i]? = some v := by
  rw [set_eq_upd, get?_upd_self]
  obtain ⟨a, ha⟩ := get?_some hi
  rw [ha]
  rfl

theorem get?_set_ne {l : List (Option α)} {i j : Nat} (v : Option α) (h : j ≠ i) :
    (l.set i v)[j]? = l[j]? := by
  rw [set_eq_upd, get?_upd_ne l _ h]

theorem Busy.set {l : List (Option α)} {h t : Nat} (hb : Busy l h t) (i : Nat) (x : α) :
    Busy (l.set i (some x)) h t := by
  intro t' ht'
  obtain ⟨y, hy⟩ := hb t' ht'
  rw [List.length_set]
  by_cases e : slotAt l.length h t' = i
  · exact ⟨x, by rw [e]; exact get?_set_self _ (by rw [← e]; exact get?_lt hy)⟩
  · exact ⟨y, by rw [get?_set_ne _ e]; exact hy⟩

/-- Putting `x` into the free slot its probe ends at keeps the table. -/
theorem TableOK.set {home : α → Nat} {l : List (Option α)} (hok : TableOK home l) {x : α}
    {i t : Nat} (ht : t < l.length) (hi : slotAt l.length (home x) t = i)
    (hb : Busy l (home x) t) (hfree : l[i]? = some none) :
    TableOK home (l.set i (some x)) := by
  intro j y hj
  rw [List.length_set]
  by_cases e : j = i
  · rw [e, get?_set_self _ (get?_lt hfree)] at hj
    have ey : x = y := Option.some.inj (Option.some.inj hj)
    rw [← ey, e]
    exact ⟨t, ht, hi, hb.set i x⟩
  · rw [get?_set_ne _ e] at hj
    obtain ⟨t0, h0, e0, hb0⟩ := hok j y hj
    exact ⟨t0, h0, e0, hb0.set i x⟩

/-- The elements of a table after one more went into a free slot. -/
theorem mem_set {l : List (Option α)} {i : Nat} {x : α} (hfree : l[i]? = some none) (z : α) :
    Mem (l.set i (some x)) z ↔ z = x ∨ Mem l z := by
  unfold Mem
  constructor
  · intro hm
    obtain ⟨j, hj⟩ := mem_get? hm
    by_cases e : j = i
    · rw [e, get?_set_self _ (get?_lt hfree)] at hj
      exact Or.inl (Option.some.inj (Option.some.inj hj)).symm
    · rw [get?_set_ne _ e] at hj
      exact Or.inr (get?_mem hj)
  · rintro (e | hm)
    · rw [e]
      exact get?_mem (i := i) (get?_set_self _ (get?_lt hfree))
    · obtain ⟨j, hj⟩ := mem_get? hm
      have e : j ≠ i := by
        intro e
        rw [e, hfree] at hj
        cases Option.some.inj hj
      exact get?_mem (i := j) (by rw [get?_set_ne _ e]; exact hj)

end YoctoCore.Properties.IdSetModel
