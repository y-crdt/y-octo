/-
Unit-level (one clock per item) YATA model: identifiers, items, positions and
the canonical delete set.

Nothing from outside this project is used here: everything in `YoctoSpec.Model` is executable
and is linked into the `yocto-spec` oracle.
-/

namespace YoctoSpec

/-- `Id` of `y-octo/src/doc/common/id.rs`: a client and a clock. -/
structure Id where
  client : Nat
  clock : Nat
deriving DecidableEq, Repr, Inhabited

/-- One integrated clock of a sequence: the `ConflictItem` of
`y-octo/src/doc/common/algorithm.rs`. `left`/`right` are `origin_left_id` and
`origin_right_id`; `none` is the start/end of the parent sequence. -/
structure Item where
  id : Id
  left : Option Id
  right : Option Id
deriving DecidableEq, Repr, Inhabited

/-! ## Positions

`ix s x` is the 1-based position of the first item of `s` with id `x`, and
`s.length + 1` when there is none. Position `0` is the start sentinel and
`s.length + 1` the end sentinel, so origins compare with items directly. -/

def ix : List Item → Id → Nat
  | [], _ => 1
  | a :: t, x => if a.id = x then 1 else ix t x + 1

/-- Position of a left origin: `none` is the start of the sequence. -/
def ixL (s : List Item) : Option Id → Nat
  | none => 0
  | some x => ix s x

/-- Position of a right origin: `none` is the end of the sequence. -/
def ixR (s : List Item) : Option Id → Nat
  | none => s.length + 1
  | some x => ix s x

/-! ## Delete set

A canonical (strictly sorted) list of deleted ids, so that two delete sets
with the same members are equal as values. -/

/-- Lexicographic order on ids: client first, then clock. -/
def Id.lt (a b : Id) : Prop :=
  a.client < b.client ∨ (a.client = b.client ∧ a.clock < b.clock)

instance : LT Id := ⟨Id.lt⟩

instance (a b : Id) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.client < b.client ∨ (a.client = b.client ∧ a.clock < b.clock)))

theorem Id.lt_def (a b : Id) :
    a < b ↔ a.client < b.client ∨ (a.client = b.client ∧ a.clock < b.clock) := Iff.rfl

theorem Id.lt_irrefl (a : Id) : ¬ a < a := by
  rw [Id.lt_def]; omega

theorem Id.lt_trans {a b c : Id} (h₁ : a < b) (h₂ : b < c) : a < c := by
  rw [Id.lt_def] at *; omega

theorem Id.lt_asymm {a b : Id} (h₁ : a < b) (h₂ : b < a) : False := by
  rw [Id.lt_def] at *; omega

theorem Id.lt_of_not_lt_of_ne {a b : Id} (h₁ : ¬ a < b) (h₂ : a ≠ b) : b < a := by
  rw [Id.lt_def] at *
  have : ¬ (a.client = b.client ∧ a.clock = b.clock) := by
    intro h
    apply h₂
    cases a; cases b; simp_all
  omega

/-- Sorted insertion without duplicates. -/
def insertId (x : Id) : List Id → List Id
  | [] => [x]
  | y :: t => if x < y then x :: y :: t else if x = y then y :: t else y :: insertId x t

theorem mem_insertId {x z : Id} {l : List Id} : z ∈ insertId x l ↔ z = x ∨ z ∈ l := by
  induction l with
  | nil => simp [insertId]
  | cons y t ih =>
    rw [insertId]
    by_cases h₁ : x < y
    · rw [ite_eq_left h₁]
      simp only [List.mem_cons]
    · rw [ite_eq_right h₁]
      by_cases h₂ : x = y
      · subst h₂
        rw [ite_eq_left rfl]
        simp only [List.mem_cons]
        constructor
        · intro h; exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact h
      · rw [ite_eq_right h₂]
        simp only [List.mem_cons, ih]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)

theorem sorted_insertId {x : Id} {l : List Id} (h : l.Pairwise (· < ·)) :
    (insertId x l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [insertId]
  | cons y t ih =>
    have h' := List.pairwise_cons.mp h
    rw [insertId]
    by_cases h₁ : x < y
    · rw [ite_eq_left h₁]
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h₁
      · exact Id.lt_trans h₁ (h'.1 z hz)
    · rw [ite_eq_right h₁]
      by_cases h₂ : x = y
      · rw [ite_eq_left h₂]
        exact h
      · rw [ite_eq_right h₂]
        refine List.pairwise_cons.mpr ⟨?_, ih h'.2⟩
        intro z hz
        rcases mem_insertId.mp hz with rfl | hz
        · exact Id.lt_of_not_lt_of_ne h₁ h₂
        · exact h'.1 z hz

theorem sorted_ext {l₁ l₂ : List Id} (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b t => exact absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | cons a t₁ ih =>
    cases l₂ with
    | nil => exact absurd ((h a).mp (List.mem_cons_self ..)) (by simp)
    | cons b t₂ =>
      rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        by_cases e : a = b
        · exact e
        · exfalso
          have ha : a ∈ t₂ := by
            rcases List.mem_cons.mp ((h a).mp (List.mem_cons_self ..)) with h' | h'
            · exact absurd h' e
            · exact h'
          have hb : b ∈ t₁ := by
            rcases List.mem_cons.mp ((h b).mpr (List.mem_cons_self ..)) with h' | h'
            · exact absurd h'.symm e
            · exact h'
          exact Id.lt_asymm (h₁.1 b hb) (h₂.1 a ha)
      subst hab
      congr 1
      apply ih h₁.2 h₂.2
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with h' | h'
        · subst h'
          exact absurd (h₁.1 x hx) (Id.lt_irrefl x)
        · exact h'
      · intro hx
        rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with h' | h'
        · subst h'
          exact absurd (h₂.1 x hx) (Id.lt_irrefl x)
        · exact h'

/-- The delete set of a document: deleted ids, strictly sorted. -/
structure DeleteSet where
  ids : List Id
  sorted : ids.Pairwise (· < ·)

namespace DeleteSet

instance : Membership Id DeleteSet := ⟨fun d x => x ∈ d.ids⟩

theorem mem_def {x : Id} {d : DeleteSet} : x ∈ d ↔ x ∈ d.ids := Iff.rfl

instance (x : Id) (d : DeleteSet) : Decidable (x ∈ d) :=
  inferInstanceAs (Decidable (x ∈ d.ids))

def empty : DeleteSet := ⟨[], List.Pairwise.nil⟩

def insert (d : DeleteSet) (x : Id) : DeleteSet := ⟨insertId x d.ids, sorted_insertId d.sorted⟩

/-- `DeleteSet::merge`: every id of `b` is added to `a`. -/
def union (a b : DeleteSet) : DeleteSet := b.ids.foldl insert a

theorem ext {a b : DeleteSet} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  cases a with
  | mk ia sa =>
    cases b with
    | mk ib sb =>
      have : ia = ib := sorted_ext sa sb h
      subst this
      rfl

@[simp] theorem not_mem_empty (x : Id) : ¬ x ∈ empty := by
  simp [mem_def, empty]

@[simp] theorem mem_insert {d : DeleteSet} {x z : Id} : z ∈ d.insert x ↔ z = x ∨ z ∈ d := by
  simp only [mem_def, insert]
  exact mem_insertId

theorem mem_foldl_insert (l : List Id) (a : DeleteSet) (z : Id) :
    z ∈ l.foldl insert a ↔ z ∈ a ∨ z ∈ l := by
  induction l generalizing a with
  | nil => simp
  | cons y t ih =>
    simp only [List.foldl_cons, ih, mem_insert, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

@[simp] theorem mem_union {a b : DeleteSet} {z : Id} : z ∈ a.union b ↔ z ∈ a ∨ z ∈ b := by
  unfold union
  rw [mem_foldl_insert]
  exact Iff.rfl

end DeleteSet

/-- Unit-level document: the integrated items in document order (tombstones
included) and the delete set. -/
structure Doc where
  items : List Item
  deleted : DeleteSet

/-- Ids of the items that are not deleted, in document order. -/
def Doc.visible (d : Doc) : List Id :=
  (d.items.filter (fun a => decide (¬ a.id ∈ d.deleted))).map Item.id

end YoctoSpec
