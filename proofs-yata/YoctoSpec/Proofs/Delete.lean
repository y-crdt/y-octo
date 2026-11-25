/-
Deletions: the delete set is a semilattice (`DeleteSet::merge` is idempotent,
commutative and associative), deleting commutes with integrating, and the
visible content only depends on the sequence and the set of deleted ids.
-/
import YoctoSpec.Proofs.Net

namespace YoctoSpec

namespace DeleteSet

theorem union_idem (a : DeleteSet) : a.union a = a := by
  apply ext
  intro x
  rw [mem_union]
  constructor
  · rintro (h | h) <;> exact h
  · intro h
    exact Or.inl h

theorem union_comm (a b : DeleteSet) : a.union b = b.union a := by
  apply ext
  intro x
  rw [mem_union, mem_union]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

theorem union_assoc (a b c : DeleteSet) : (a.union b).union c = a.union (b.union c) := by
  apply ext
  intro x
  rw [mem_union, mem_union, mem_union, mem_union]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem union_empty (a : DeleteSet) : a.union empty = a := by
  apply ext
  intro x
  rw [mem_union]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (not_mem_empty x)
  · intro h
    exact Or.inl h

theorem insert_idem (a : DeleteSet) (x : Id) : (a.insert x).insert x = a.insert x := by
  apply ext
  intro z
  rw [mem_insert, mem_insert]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact h
  · intro h
    exact Or.inr h

theorem insert_comm (a : DeleteSet) (x y : Id) : (a.insert x).insert y = (a.insert y).insert x := by
  apply ext
  intro z
  rw [mem_insert, mem_insert, mem_insert, mem_insert]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end DeleteSet

theorem filter_cons_true {α : Type} {p : α → Bool} {a : α} {l : List α} (h : p a = true) :
    (a :: l).filter p = a :: l.filter p := by
  rw [List.filter_cons, ite_eq_left h]

theorem filter_cons_false {α : Type} {p : α → Bool} {a : α} {l : List α} (h : p a = false) :
    (a :: l).filter p = l.filter p := by
  rw [List.filter_cons, ite_eq_right (by rw [h]; decide)]

namespace Doc

theorem ext' {d₁ d₂ : Doc} (h₁ : d₁.items = d₂.items) (h₂ : d₁.deleted = d₂.deleted) :
    d₁ = d₂ := by
  cases d₁
  cases d₂
  simp only at h₁ h₂
  rw [h₁, h₂]

/-- Deleting commutes with integrating. -/
theorem delete_integrate (d : Doc) (x : Id) (i : Item) :
    (d.delete x).integrate i = (d.integrate i).delete x := rfl

theorem deleteAll_integrate (d : Doc) (ds : DeleteSet) (i : Item) :
    (d.deleteAll ds).integrate i = (d.integrate i).deleteAll ds := rfl

theorem delete_comm (d : Doc) (x y : Id) : (d.delete x).delete y = (d.delete y).delete x := by
  refine ext' rfl ?_
  show (d.deleted.insert x).insert y = (d.deleted.insert y).insert x
  exact DeleteSet.insert_comm _ _ _

theorem delete_idem (d : Doc) (x : Id) : (d.delete x).delete x = d.delete x := by
  refine ext' rfl ?_
  show (d.deleted.insert x).insert x = d.deleted.insert x
  exact DeleteSet.insert_idem _ _

theorem deleteAll_comm (d : Doc) (a b : DeleteSet) :
    (d.deleteAll a).deleteAll b = (d.deleteAll b).deleteAll a := by
  refine ext' rfl ?_
  show (d.deleted.union a).union b = (d.deleted.union b).union a
  rw [DeleteSet.union_assoc, DeleteSet.union_comm a b, ← DeleteSet.union_assoc]

theorem deleteAll_idem (d : Doc) (a : DeleteSet) : (d.deleteAll a).deleteAll a = d.deleteAll a := by
  refine ext' rfl ?_
  show (d.deleted.union a).union a = d.deleted.union a
  rw [DeleteSet.union_assoc, DeleteSet.union_idem]

theorem deleteAll_assoc (d : Doc) (a b : DeleteSet) :
    (d.deleteAll a).deleteAll b = d.deleteAll (a.union b) := by
  refine ext' rfl ?_
  show (d.deleted.union a).union b = d.deleted.union (a.union b)
  rw [DeleteSet.union_assoc]

/-- The visible ids are the ids of the sequence that are not deleted. -/
theorem mem_visible {d : Doc} {x : Id} :
    x ∈ d.visible ↔ (∃ a, a ∈ d.items ∧ a.id = x) ∧ ¬ x ∈ d.deleted := by
  unfold visible
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, e⟩
    rw [List.mem_filter] at ha
    rw [← e]
    exact ⟨⟨a, ha.1, rfl⟩, of_decide_eq_true ha.2⟩
  · rintro ⟨⟨a, ha, e⟩, hx⟩
    refine ⟨a, ?_, e⟩
    rw [List.mem_filter]
    refine ⟨ha, decide_eq_true ?_⟩
    rw [e]
    exact hx

/-- Deleting an id removes it from the visible content and nothing else, and
keeps the order of the rest. -/
theorem visible_delete (d : Doc) (x : Id) :
    (d.delete x).visible = d.visible.filter (fun y => decide (y ≠ x)) := by
  show ((d.items.filter (fun a => decide (¬ a.id ∈ d.deleted.insert x))).map Item.id) =
    ((d.items.filter (fun a => decide (¬ a.id ∈ d.deleted))).map Item.id).filter
      (fun y => decide (y ≠ x))
  generalize d.items = l
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases h₁ : a.id ∈ d.deleted
    · have c₁ : (fun (a : Item) => decide (¬ a.id ∈ d.deleted.insert x)) a = false :=
        decide_eq_false (fun hn => hn (DeleteSet.mem_insert.mpr (Or.inr h₁)))
      have c₂ : (fun (a : Item) => decide (¬ a.id ∈ d.deleted)) a = false :=
        decide_eq_false (fun hn => hn h₁)
      rw [filter_cons_false (p := fun (a : Item) => decide (¬ a.id ∈ d.deleted.insert x)) c₁, filter_cons_false (p := fun (a : Item) => decide (¬ a.id ∈ d.deleted)) c₂]
      exact ih
    · have c₂ : (fun (a : Item) => decide (¬ a.id ∈ d.deleted)) a = true := decide_eq_true h₁
      rw [filter_cons_true (p := fun (a : Item) => decide (¬ a.id ∈ d.deleted)) c₂, List.map_cons]
      by_cases h₃ : a.id = x
      · have c₁ : (fun (a : Item) => decide (¬ a.id ∈ d.deleted.insert x)) a = false :=
          decide_eq_false (fun hn => hn (DeleteSet.mem_insert.mpr (Or.inl h₃)))
        have c₃ : (fun (y : Id) => decide (y ≠ x)) a.id = false :=
          decide_eq_false (fun hn => hn h₃)
        rw [filter_cons_false (p := fun (a : Item) => decide (¬ a.id ∈ d.deleted.insert x)) c₁, filter_cons_false (p := fun (y : Id) => decide (y ≠ x)) c₃]
        exact ih
      · have h₂ : ¬ a.id ∈ d.deleted.insert x := by
          intro h
          rcases DeleteSet.mem_insert.mp h with h | h
          · exact h₃ h
          · exact h₁ h
        have c₁ : (fun (a : Item) => decide (¬ a.id ∈ d.deleted.insert x)) a = true :=
          decide_eq_true h₂
        have c₃ : (fun (y : Id) => decide (y ≠ x)) a.id = true := decide_eq_true h₃
        rw [filter_cons_true (p := fun (a : Item) => decide (¬ a.id ∈ d.deleted.insert x)) c₁, filter_cons_true (p := fun (y : Id) => decide (y ≠ x)) c₃, List.map_cons, ih]

end Doc

end YoctoSpec
