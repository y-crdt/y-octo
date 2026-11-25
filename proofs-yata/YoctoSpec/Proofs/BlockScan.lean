/-
Facts about block sequences used to relate the block-level conflict scan to
the unit-level one: units and owners of blocks, alignment after a split, and
how the unit-level scan runs through the clocks of one block.
-/
import YoctoSpec.Proofs.Block

namespace YoctoSpec

theorem Id.ext' {a b : Id} (h₁ : a.client = b.client) (h₂ : a.clock = b.clock) : a = b := by
  cases a
  cases b
  simp_all

/-! ## Units of a block -/

theorem mem_unitsFrom_ids {c : Nat} {r : Option Id} :
    ∀ {n k : Nat} {l : Option Id} {x : Id},
      x ∈ (unitsFrom c r k l n).map Item.id ↔ x.client = c ∧ k ≤ x.clock ∧ x.clock < k + n := by
  intro n
  induction n with
  | zero =>
    intro k l x
    rw [unitsFrom, List.map_nil]
    constructor
    · intro h
      cases h
    · rintro ⟨_, h₁, h₂⟩
      omega
  | succ n ih =>
    intro k l x
    rw [unitsFrom, List.map_cons, List.mem_cons, ih]
    constructor
    · rintro (e | ⟨h₁, h₂, h₃⟩)
      · rw [e]
        exact ⟨rfl, Nat.le_refl _, by show k < k + (n + 1); omega⟩
      · exact ⟨h₁, by omega, by omega⟩
    · rintro ⟨h₁, h₂, h₃⟩
      by_cases e : x.clock = k
      · left
        exact Id.ext' h₁ e
      · right
        exact ⟨h₁, by omega, by omega⟩

theorem mem_units_ids {b : Block} {x : Id} :
    x ∈ b.units.map Item.id ↔
      x.client = b.id.client ∧ b.id.clock ≤ x.clock ∧ x.clock < b.id.clock + b.len :=
  mem_unitsFrom_ids

theorem contains_iff {b : Block} {x : Id} : b.contains x = true ↔ x ∈ b.units.map Item.id := by
  rw [mem_units_ids]
  unfold Block.contains
  exact decide_eq_true_iff

theorem units_eq_cons {b : Block} (h : 0 < b.len) :
    b.units = b.toItem ::
      unitsFrom b.id.client b.right (b.id.clock + 1) (some ⟨b.id.client, b.id.clock⟩)
        (b.len - 1) := by
  unfold Block.units
  have e : b.len = (b.len - 1) + 1 := by omega
  rw [e, unitsFrom]
  rfl

theorem toItem_mem_units {b : Block} (h : 0 < b.len) : b.toItem ∈ b.units := by
  rw [units_eq_cons h]
  exact List.mem_cons_self ..

theorem units_subset_flatten {bs : List Block} {b : Block} (hb : b ∈ bs) {u : Item}
    (hu : u ∈ b.units) : u ∈ flatten bs := by
  unfold flatten
  exact List.mem_flatMap.mpr ⟨b, hb, hu⟩

theorem mem_flatten {bs : List Block} {u : Item} :
    u ∈ flatten bs ↔ ∃ b, b ∈ bs ∧ u ∈ b.units := by
  unfold flatten
  exact List.mem_flatMap

/-- Every block holds at least one clock. -/
def BlockWF (bs : List Block) : Prop := ∀ c, c ∈ bs → 0 < c.len

/-- With distinct unit ids, a clock belongs to one block only. -/
theorem block_unique {bs : List Block} (hn : NodupIds (flatten bs)) {c c' : Block}
    (hc : c ∈ bs) (hc' : c' ∈ bs) {x : Id} (hx : x ∈ c.units.map Item.id)
    (hx' : x ∈ c'.units.map Item.id) : c = c' := by
  induction bs with
  | nil => cases hc
  | cons d t ih =>
    rw [flatten_cons] at hn
    unfold NodupIds at hn
    rw [List.pairwise_append] at hn
    have cross : ∀ e, e ∈ t → x ∈ d.units.map Item.id → x ∈ e.units.map Item.id → False := by
      intro e he h₁ h₂
      obtain ⟨u, hu, eu⟩ := List.mem_map.mp h₁
      obtain ⟨v, hv, ev⟩ := List.mem_map.mp h₂
      exact hn.2.2 u hu v (units_subset_flatten he hv) (by rw [eu, ev])
    rcases List.mem_cons.mp hc with e | h
    · rcases List.mem_cons.mp hc' with e' | h'
      · rw [e, e']
      · exfalso
        rw [e] at hx
        exact cross c' h' hx hx'
    · rcases List.mem_cons.mp hc' with e' | h'
      · exfalso
        rw [e'] at hx'
        exact cross c h hx' hx
      · exact ih hn.2.1 h h'

/-! ## Owners -/

theorem ownerB_some {bs : List Block} {x o : Id} (h : ownerB bs x = some o) :
    ∃ c, c ∈ bs ∧ c.id = o ∧ x ∈ c.units.map Item.id := by
  induction bs with
  | nil =>
    rw [ownerB] at h
    cases h
  | cons d t ih =>
    rw [ownerB] at h
    by_cases hd : d.contains x = true
    · rw [ite_eq_left hd] at h
      exact ⟨d, List.mem_cons_self .., Option.some.inj h, contains_iff.mp hd⟩
    · rw [ite_eq_right hd] at h
      obtain ⟨c, hc, e, hx⟩ := ih h
      exact ⟨c, List.mem_cons_of_mem _ hc, e, hx⟩

theorem ownerB_of_mem {bs : List Block} (hn : NodupIds (flatten bs)) {c : Block} (hc : c ∈ bs)
    {x : Id} (hx : x ∈ c.units.map Item.id) : ownerB bs x = some c.id := by
  induction bs with
  | nil => cases hc
  | cons d t ih =>
    rw [ownerB]
    by_cases hd : d.contains x = true
    · rw [ite_eq_left hd]
      have : d = c := block_unique hn (List.mem_cons_self ..) hc (contains_iff.mp hd) hx
      rw [this]
    · rw [ite_eq_right hd]
      rcases List.mem_cons.mp hc with e | h
      · exfalso
        rw [e] at hx
        exact hd (contains_iff.mpr hx)
      · have hn' : NodupIds (flatten t) := by
          rw [flatten_cons] at hn
          unfold NodupIds at hn
          rw [List.pairwise_append] at hn
          exact hn.2.1
        exact ih hn' h

/-- The owner of a clock is `c` exactly when `c` holds the clock. -/
theorem ownerB_eq_iff {bs : List Block} (hn : NodupIds (flatten bs)) (hw : BlockWF bs)
    {c : Block} (hc : c ∈ bs) {x : Id} :
    ownerB bs x = some c.id ↔ x ∈ c.units.map Item.id := by
  constructor
  · intro h
    obtain ⟨d, hd, e, hx⟩ := ownerB_some h
    -- `d` and `c` both hold the clock `c.id`
    have h₁ : c.id ∈ d.units.map Item.id := by
      rw [← e]
      exact List.mem_map.mpr ⟨d.toItem, toItem_mem_units (hw d hd), rfl⟩
    have h₂ : c.id ∈ c.units.map Item.id :=
      List.mem_map.mpr ⟨c.toItem, toItem_mem_units (hw c hc), rfl⟩
    rw [← block_unique hn hd hc h₁ h₂]
    exact hx
  · exact ownerB_of_mem hn hc

theorem ownerB_of_block {bs : List Block} {c : Block} (hc : c ∈ bs) {x : Id}
    (hx : x ∈ c.units.map Item.id) : ∃ o, ownerB bs x = some o := by
  induction bs with
  | nil => cases hc
  | cons d t ih =>
    rw [ownerB]
    by_cases hd : d.contains x = true
    · rw [ite_eq_left hd]
      exact ⟨d.id, rfl⟩
    · rw [ite_eq_right hd]
      rcases List.mem_cons.mp hc with e' | h'
      · exfalso
        rw [e'] at hx
        exact hd (contains_iff.mpr hx)
      · exact ih h'

theorem ownerB_of_present {bs : List Block} {x : Id}
    (h : ix (flatten bs) x ≤ (flatten bs).length) : ∃ o, ownerB bs x = some o := by
  obtain ⟨u, hu, e⟩ := ix_le_length_iff.mp h
  obtain ⟨c, hc, huc⟩ := mem_flatten.mp hu
  exact ownerB_of_block hc (List.mem_map.mpr ⟨u, huc, e⟩)

theorem owner_of_mem {s : List Item} {x : Id} (h : x ∈ s.map Item.id) : owner s x = some x := by
  unfold owner
  rw [ite_eq_left h]

/-! ## Alignment after a split -/

/-- No block has the clock `x` strictly inside. -/
def Aligned (x : Id) (bs : List Block) : Prop :=
  ∀ c, c ∈ bs →
    ¬ (x.client = c.id.client ∧ c.id.clock < x.clock ∧ x.clock < c.id.clock + c.len)

theorem len_leftPart {b : Block} {k : Nat} (h : k ≤ b.len) : (b.leftPart k).len = k :=
  Content.len_take h

theorem len_rightPart (b : Block) (k : Nat) : (b.rightPart k).len = b.len - k :=
  Content.len_drop _ _

theorem mem_splitBlock {x : Id} {d c : Block} (h : c ∈ splitBlock x d) :
    c = d ∨ ((x.client = d.id.client ∧ d.id.clock < x.clock ∧ x.clock < d.id.clock + d.len) ∧
      (c = d.leftPart (x.clock - d.id.clock) ∨ c = d.rightPart (x.clock - d.id.clock))) := by
  unfold splitBlock at h
  by_cases hc : x.client = d.id.client ∧ d.id.clock < x.clock ∧ x.clock < d.id.clock + d.len
  · rw [ite_eq_left hc] at h
    right
    refine ⟨hc, ?_⟩
    unfold Block.splitAt at h
    rcases List.mem_cons.mp h with e | h'
    · exact Or.inl e
    · rcases List.mem_cons.mp h' with e | h''
      · exact Or.inr e
      · cases h''
  · rw [ite_eq_right hc] at h
    rcases List.mem_cons.mp h with e | h'
    · exact Or.inl e
    · cases h'

theorem mem_split {bs : List Block} {x : Id} {c : Block} (h : c ∈ split bs x) :
    ∃ d, d ∈ bs ∧ c ∈ splitBlock x d := by
  unfold split at h
  exact List.mem_flatMap.mp h

theorem blockWF_split {bs : List Block} (hw : BlockWF bs) (x : Id) : BlockWF (split bs x) := by
  intro c hc
  obtain ⟨d, hd, hcd⟩ := mem_split hc
  have hdl := hw d hd
  rcases mem_splitBlock hcd with e | ⟨hs, e | e⟩
  · rw [e]
    exact hdl
  · rw [e, len_leftPart (by omega)]
    omega
  · rw [e, len_rightPart]
    omega

/-- After `split bs x` a block starts at `x`, if `x` is in the sequence. -/
theorem aligned_split (bs : List Block) (x : Id) : Aligned x (split bs x) := by
  intro c hc
  obtain ⟨d, _, hcd⟩ := mem_split hc
  rcases mem_splitBlock hcd with e | ⟨hs, e | e⟩
  · rw [e]
    intro hcon
    unfold splitBlock at hcd
    rw [ite_eq_left hcon] at hcd
    unfold Block.splitAt at hcd
    rcases List.mem_cons.mp hcd with e' | h'
    · -- `d` would be its own left part, which is shorter
      have h₁ : d.len = (d.leftPart (x.clock - d.id.clock)).len := by rw [← e', e]
      rw [len_leftPart (by omega)] at h₁
      omega
    · rcases List.mem_cons.mp h' with e' | h''
      · have h₁ : d.len = (d.rightPart (x.clock - d.id.clock)).len := by rw [← e', e]
        rw [len_rightPart] at h₁
        omega
      · cases h''
  · rw [e]
    intro hcon
    have h₁ : (d.leftPart (x.clock - d.id.clock)).len = x.clock - d.id.clock :=
      len_leftPart (by omega)
    have h₂ : (d.leftPart (x.clock - d.id.clock)).id = d.id := rfl
    rw [h₁, h₂] at hcon
    omega
  · rw [e]
    intro hcon
    have h₂ : (d.rightPart (x.clock - d.id.clock)).id.clock = d.id.clock + (x.clock - d.id.clock) :=
      rfl
    rw [h₂] at hcon
    omega

/-- A later split keeps earlier alignments. -/
theorem aligned_split_of_aligned {bs : List Block} {y : Id} (h : Aligned y bs) (x : Id) :
    Aligned y (split bs x) := by
  intro c hc
  obtain ⟨d, hd, hcd⟩ := mem_split hc
  have hdy := h d hd
  rcases mem_splitBlock hcd with e | ⟨hs, e | e⟩
  · rw [e]
    exact hdy
  · rw [e]
    intro hcon
    have h₁ : (d.leftPart (x.clock - d.id.clock)).len = x.clock - d.id.clock :=
      len_leftPart (by omega)
    have h₂ : (d.leftPart (x.clock - d.id.clock)).id = d.id := rfl
    rw [h₁, h₂] at hcon
    exact hdy ⟨hcon.1, hcon.2.1, by omega⟩
  · rw [e]
    intro hcon
    have h₁ : (d.rightPart (x.clock - d.id.clock)).len = d.len - (x.clock - d.id.clock) :=
      len_rightPart _ _
    have h₂ : (d.rightPart (x.clock - d.id.clock)).id.clock = d.id.clock + (x.clock - d.id.clock) :=
      rfl
    have h₃ : (d.rightPart (x.clock - d.id.clock)).id.client = d.id.client := rfl
    rw [h₁, h₂, h₃] at hcon
    exact hdy ⟨hcon.1, by omega, by omega⟩

/-! ## Steps of the scan -/

section
variable {this : Item} {right : Option Id} {ow : Id → Option Id} {c : Item} {rest : List Item}
  {left : Option Id} {before conf : List Id}

theorem fcl_nil : findConflictLeft this right ow [] left before conf = left := by
  rw [findConflictLeft]

theorem fcl_stop_right (h : right = some c.id) :
    findConflictLeft this right ow (c :: rest) left before conf = left := by
  rw [findConflictLeft, ite_eq_left h]

theorem fcl_same_commit (h₁ : right ≠ some c.id) (h₂ : this.left = c.left)
    (h₃ : c.id.client < this.id.client) :
    findConflictLeft this right ow (c :: rest) left before conf =
      findConflictLeft this right ow rest (some c.id) (c.id :: before) [] := by
  rw [findConflictLeft, ite_eq_right h₁, ite_eq_left h₂, ite_eq_left h₃]

theorem fcl_same_stop (h₁ : right ≠ some c.id) (h₂ : this.left = c.left)
    (h₃ : ¬ c.id.client < this.id.client) (h₄ : this.right = c.right) :
    findConflictLeft this right ow (c :: rest) left before conf = left := by
  rw [findConflictLeft, ite_eq_right h₁, ite_eq_left h₂, ite_eq_right h₃, ite_eq_left h₄]

theorem fcl_same_skip (h₁ : right ≠ some c.id) (h₂ : this.left = c.left)
    (h₃ : ¬ c.id.client < this.id.client) (h₄ : this.right ≠ c.right) :
    findConflictLeft this right ow (c :: rest) left before conf =
      findConflictLeft this right ow rest left (c.id :: before) (c.id :: conf) := by
  rw [findConflictLeft, ite_eq_right h₁, ite_eq_left h₂, ite_eq_right h₃, ite_eq_right h₄]

theorem fcl_other_none (h₁ : right ≠ some c.id) (h₂ : this.left ≠ c.left) (h₃ : c.left = none) :
    findConflictLeft this right ow (c :: rest) left before conf = left := by
  rw [findConflictLeft, ite_eq_right h₁, ite_eq_right h₂]
  simp only [h₃]

theorem fcl_other_unowned {cl : Id} (h₁ : right ≠ some c.id) (h₂ : this.left ≠ c.left)
    (h₃ : c.left = some cl) (h₄ : ow cl = none) :
    findConflictLeft this right ow (c :: rest) left before conf = left := by
  rw [findConflictLeft, ite_eq_right h₁, ite_eq_right h₂]
  simp only [h₃, h₄]

theorem fcl_other_stop {cl o : Id} (h₁ : right ≠ some c.id) (h₂ : this.left ≠ c.left)
    (h₃ : c.left = some cl) (h₄ : ow cl = some o) (h₅ : ¬ o ∈ c.id :: before) :
    findConflictLeft this right ow (c :: rest) left before conf = left := by
  rw [findConflictLeft, ite_eq_right h₁, ite_eq_right h₂]
  simp only [h₃, h₄]
  rw [ite_eq_right h₅]

theorem fcl_other_skip {cl o : Id} (h₁ : right ≠ some c.id) (h₂ : this.left ≠ c.left)
    (h₃ : c.left = some cl) (h₄ : ow cl = some o) (h₅ : o ∈ c.id :: before)
    (h₆ : o ∈ c.id :: conf) :
    findConflictLeft this right ow (c :: rest) left before conf =
      findConflictLeft this right ow rest left (c.id :: before) (c.id :: conf) := by
  rw [findConflictLeft, ite_eq_right h₁, ite_eq_right h₂]
  simp only [h₃, h₄]
  rw [ite_eq_left h₅, ite_eq_left h₆]

theorem fcl_other_commit {cl o : Id} (h₁ : right ≠ some c.id) (h₂ : this.left ≠ c.left)
    (h₃ : c.left = some cl) (h₄ : ow cl = some o) (h₅ : o ∈ c.id :: before)
    (h₆ : ¬ o ∈ c.id :: conf) :
    findConflictLeft this right ow (c :: rest) left before conf =
      findConflictLeft this right ow rest (some c.id) (c.id :: before) [] := by
  rw [findConflictLeft, ite_eq_right h₁, ite_eq_right h₂]
  simp only [h₃, h₄]
  rw [ite_eq_left h₅, ite_eq_right h₆]

end

/-! ## The clocks of one block -/

/-- The ids of scanned items are pushed in front of the set. -/
def pushIds (us : List Item) (acc : List Id) : List Id := us.foldl (fun acc u => u.id :: acc) acc

theorem mem_pushIds {us : List Item} {acc : List Id} {x : Id} :
    x ∈ pushIds us acc ↔ x ∈ us.map Item.id ∨ x ∈ acc := by
  induction us generalizing acc with
  | nil =>
    unfold pushIds
    constructor
    · intro h
      exact Or.inr h
    · rintro (h | h)
      · cases h
      · exact h
  | cons u t ih =>
    have e : pushIds (u :: t) acc = pushIds t (u.id :: acc) := rfl
    rw [e, ih, List.map_cons, List.mem_cons, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- Once the scan has put the clock `p` of a block on the left, the following
clocks of the block go to the left as well. -/
theorem chain_commit (this : Item) (right : Option Id) (ow : Id → Option Id) (c : Nat)
    (r : Option Id) (rest : List Item) :
    ∀ (n p : Nat) (before : List Id),
      (∀ j, p < j → j ≤ p + n → right ≠ some ⟨c, j⟩) →
      (∀ j, p ≤ j → j < p + n → this.left ≠ some ⟨c, j⟩) →
      (∀ j, p ≤ j → j < p + n → ow ⟨c, j⟩ = some ⟨c, j⟩) →
      (⟨c, p⟩ : Id) ∈ before →
      findConflictLeft this right ow (unitsFrom c r (p + 1) (some ⟨c, p⟩) n ++ rest)
          (some ⟨c, p⟩) before [] =
        findConflictLeft this right ow rest (some ⟨c, p + n⟩)
          (pushIds (unitsFrom c r (p + 1) (some ⟨c, p⟩) n) before) [] := by
  intro n
  induction n with
  | zero =>
    intro p before _ _ _ _
    rw [unitsFrom]
    rfl
  | succ n ih =>
    intro p before hR hL hO hmem
    rw [unitsFrom, List.cons_append]
    have hne : (⟨c, p⟩ : Id) ≠ ⟨c, p + 1⟩ := by
      intro e
      have := congrArg Id.clock e
      simp only at this
      omega
    rw [fcl_other_commit (cl := ⟨c, p⟩) (o := ⟨c, p⟩)
      (fun e => hR (p + 1) (by omega) (by omega) e)
      (fun e => hL p (by omega) (by omega) e) rfl (hO p (by omega) (by omega))
      (List.mem_cons_of_mem _ hmem)
      (by
        intro h
        rcases List.mem_cons.mp h with e | h'
        · exact hne e
        · cases h')]
    rw [ih (p + 1) (⟨c, p + 1⟩ :: before)
      (fun j h₁ h₂ => hR j (by omega) (by omega))
      (fun j h₁ h₂ => hL j (by omega) (by omega))
      (fun j h₁ h₂ => hO j (by omega) (by omega))
      (List.mem_cons_self ..)]
    have e : p + 1 + n = p + (n + 1) := by omega
    rw [e]
    rfl

/-- While the clock `p` of a block is pending, so are its following clocks. -/
theorem chain_skip (this : Item) (right : Option Id) (ow : Id → Option Id) (c : Nat)
    (r : Option Id) (rest : List Item) (left : Option Id) :
    ∀ (n p : Nat) (before conf : List Id),
      (∀ j, p < j → j ≤ p + n → right ≠ some ⟨c, j⟩) →
      (∀ j, p ≤ j → j < p + n → this.left ≠ some ⟨c, j⟩) →
      (∀ j, p ≤ j → j < p + n → ow ⟨c, j⟩ = some ⟨c, j⟩) →
      (⟨c, p⟩ : Id) ∈ before → (⟨c, p⟩ : Id) ∈ conf →
      findConflictLeft this right ow (unitsFrom c r (p + 1) (some ⟨c, p⟩) n ++ rest)
          left before conf =
        findConflictLeft this right ow rest left
          (pushIds (unitsFrom c r (p + 1) (some ⟨c, p⟩) n) before)
          (pushIds (unitsFrom c r (p + 1) (some ⟨c, p⟩) n) conf) := by
  intro n
  induction n with
  | zero =>
    intro p before conf _ _ _ _ _
    rw [unitsFrom]
    rfl
  | succ n ih =>
    intro p before conf hR hL hO hmem hconf
    rw [unitsFrom, List.cons_append]
    rw [fcl_other_skip (cl := ⟨c, p⟩) (o := ⟨c, p⟩)
      (fun e => hR (p + 1) (by omega) (by omega) e)
      (fun e => hL p (by omega) (by omega) e) rfl (hO p (by omega) (by omega))
      (List.mem_cons_of_mem _ hmem) (List.mem_cons_of_mem _ hconf)]
    rw [ih (p + 1) (⟨c, p + 1⟩ :: before) (⟨c, p + 1⟩ :: conf)
      (fun j h₁ h₂ => hR j (by omega) (by omega))
      (fun j h₁ h₂ => hL j (by omega) (by omega))
      (fun j h₁ h₂ => hO j (by omega) (by omega))
      (List.mem_cons_self ..) (List.mem_cons_self ..)]
    rfl

end YoctoSpec
