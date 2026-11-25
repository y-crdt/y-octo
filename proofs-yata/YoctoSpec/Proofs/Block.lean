/-
Split, merge and content GC do not change the unit-level document a block
sequence stands for; GC of either kind does not change the visible text.
-/
import YoctoSpec.Model.Block
import YoctoSpec.Proofs.Delete

namespace YoctoSpec

/-! ## Units of a run of clocks -/

theorem unitsFrom_split (c : Nat) (r : Option Id) :
    ∀ (m n k : Nat) (l : Option Id) (k' N : Nat) (l' : Option Id), 0 < m → N = m + n →
      k' = k + m → l' = some ⟨c, k + m - 1⟩ →
      unitsFrom c r k l N = unitsFrom c r k l m ++ unitsFrom c r k' l' n := by
  intro m
  induction m with
  | zero =>
    intro n k l k' N l' h
    omega
  | succ m ih =>
    intro n k l k' N l' _ hN hk' hl'
    have e : N = (m + n) + 1 := by omega
    rw [e, unitsFrom, unitsFrom]
    by_cases hm : m = 0
    · have e₁ : m + n = n := by omega
      have e₂ : k' = k + 1 := by omega
      have e₃ : l' = some ⟨c, k⟩ := by
        rw [hl']
        have : k + (m + 1) - 1 = k := by omega
        rw [this]
      rw [e₁, hm, unitsFrom, e₂, e₃]
      rfl
    · have e₃ : l' = some ⟨c, k + 1 + m - 1⟩ := by
        rw [hl']
        have : k + (m + 1) - 1 = k + 1 + m - 1 := by omega
        rw [this]
      rw [ih n (k + 1) (some ⟨c, k⟩) k' (m + n) l' (by omega) rfl (by omega) e₃]
      rfl

theorem length_unitsFrom (c : Nat) (r : Option Id) :
    ∀ (n k : Nat) (l : Option Id), (unitsFrom c r k l n).length = n := by
  intro n
  induction n with
  | zero =>
    intro k l
    rw [unitsFrom]
    rfl
  | succ n ih =>
    intro k l
    rw [unitsFrom, List.length_cons, ih]

/-- The ids of a run are its clocks. -/
theorem mem_unitsFrom_id {c : Nat} {r : Option Id} :
    ∀ {n k : Nat} {l : Option Id} {u : Item}, u ∈ unitsFrom c r k l n →
      u.id.client = c ∧ k ≤ u.id.clock ∧ u.id.clock < k + n := by
  intro n
  induction n with
  | zero =>
    intro k l u h
    rw [unitsFrom] at h
    cases h
  | succ n ih =>
    intro k l u h
    rw [unitsFrom] at h
    rcases List.mem_cons.mp h with e | h'
    · rw [e]
      refine ⟨rfl, Nat.le_refl _, ?_⟩
      show k < k + (n + 1)
      omega
    · have := ih h'
      exact ⟨this.1, by omega, by omega⟩

/-! ## flatten -/

theorem flatten_nil : flatten [] = [] := rfl

theorem flatten_cons (b : Block) (t : List Block) : flatten (b :: t) = b.units ++ flatten t := by
  unfold flatten
  rw [List.flatMap_cons]

theorem flatten_append (p q : List Block) : flatten (p ++ q) = flatten p ++ flatten q := by
  unfold flatten
  rw [List.flatMap_append]

theorem deletedIds_cons (b : Block) (t : List Block) :
    (b :: t).flatMap Block.deletedIds = b.deletedIds ++ t.flatMap Block.deletedIds := by
  rw [List.flatMap_cons]

theorem visible_nil : visible [] = [] := rfl

theorem visible_cons (b : Block) (t : List Block) :
    visible (b :: t) = (if b.deleted then [] else b.content.chars) ++ visible t := by
  unfold visible
  rw [List.flatMap_cons]

/-- The part of a block sequence the unit-level document and the visible text
depend on. -/
structure SameUnits (p q : List Block) : Prop where
  units : flatten p = flatten q
  deleted : p.flatMap Block.deletedIds = q.flatMap Block.deletedIds
  visible : visible p = visible q

theorem SameUnits.toDoc {p q : List Block} (h : SameUnits p q) : toDoc p = toDoc q := by
  unfold YoctoSpec.toDoc deletedSet
  rw [h.units, h.deleted]

theorem SameUnits.refl (p : List Block) : SameUnits p p := ⟨rfl, rfl, rfl⟩

theorem SameUnits.symm {p q : List Block} (h : SameUnits p q) : SameUnits q p :=
  ⟨h.units.symm, h.deleted.symm, h.visible.symm⟩

theorem SameUnits.trans {p q r : List Block} (h₁ : SameUnits p q) (h₂ : SameUnits q r) :
    SameUnits p r :=
  ⟨h₁.units.trans h₂.units, h₁.deleted.trans h₂.deleted, h₁.visible.trans h₂.visible⟩

theorem visible_append (p q : List Block) : visible (p ++ q) = visible p ++ visible q := by
  unfold visible
  rw [List.flatMap_append]

theorem SameUnits.append {p q p' q' : List Block} (h₁ : SameUnits p p') (h₂ : SameUnits q q') :
    SameUnits (p ++ q) (p' ++ q') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [flatten_append, flatten_append, h₁.units, h₂.units]
  · rw [List.flatMap_append, List.flatMap_append, h₁.deleted, h₂.deleted]
  · rw [visible_append, visible_append, h₁.visible, h₂.visible]

theorem SameUnits.cons (b : Block) {p q : List Block} (h : SameUnits p q) :
    SameUnits (b :: p) (b :: q) :=
  SameUnits.append (SameUnits.refl [b]) h

/-- Replacing every block by blocks with the same units keeps the document. -/
theorem sameUnits_flatMap (f : Block → List Block) (hf : ∀ b, SameUnits (f b) [b])
    (bs : List Block) : SameUnits (bs.flatMap f) bs := by
  induction bs with
  | nil => exact SameUnits.refl []
  | cons b t ih =>
    rw [List.flatMap_cons]
    exact SameUnits.append (hf b) ih

/-- Two blocks that together cover a block. -/
theorem sameUnits_pair {b l r : Block} (hu : l.units ++ r.units = b.units)
    (hdl : l.deleted = b.deleted) (hdr : r.deleted = b.deleted)
    (hc : l.content.chars ++ r.content.chars = b.content.chars) : SameUnits [l, r] [b] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [flatten_cons, flatten_cons, flatten_nil, List.append_nil, hu, flatten_cons, flatten_nil,
      List.append_nil]
  · rw [deletedIds_cons, deletedIds_cons, List.flatMap_nil, List.append_nil, deletedIds_cons,
      List.flatMap_nil, List.append_nil]
    unfold Block.deletedIds
    rw [hdl, hdr]
    by_cases hdel : b.deleted = true
    · rw [ite_eq_left hdel, ite_eq_left hdel, ite_eq_left hdel, ← List.map_append, hu]
    · rw [ite_eq_right hdel, ite_eq_right hdel, ite_eq_right hdel]
      rfl
  · rw [visible_cons, visible_cons, visible_nil, visible_cons, visible_nil, hdl, hdr]
    by_cases hdel : b.deleted = true
    · rw [ite_eq_left hdel, ite_eq_left hdel, ite_eq_left hdel]
      rfl
    · rw [ite_eq_right hdel, ite_eq_right hdel, ite_eq_right hdel, List.append_nil,
        List.append_nil, hc]

/-- A block that only differs in the content of deleted clocks. -/
theorem sameUnits_of_eq {b b' : Block} (hid : b'.id = b.id) (hl : b'.left = b.left)
    (hr : b'.right = b.right) (hd : b'.deleted = b.deleted) (hlen : b'.len = b.len)
    (hv : b.deleted = true ∨ b'.content.chars = b.content.chars) : SameUnits [b'] [b] := by
  have hu : b'.units = b.units := by
    unfold Block.units
    rw [hid, hl, hr, hlen]
  refine ⟨?_, ?_, ?_⟩
  · rw [flatten_cons, flatten_cons, hu]
  · rw [deletedIds_cons, deletedIds_cons]
    unfold Block.deletedIds
    rw [hd, hu]
  · rw [visible_cons, visible_cons, hd]
    rcases hv with h | h
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [h]

/-! ## Split -/

theorem Content.len_take {c : Content} {k : Nat} (h : k ≤ c.len) : (c.take k).len = k := by
  cases c with
  | str cs =>
    have h' : k ≤ cs.length := h
    show (cs.take k).length = k
    rw [List.length_take]
    omega
  | del n =>
    have h' : k ≤ n := h
    show min k n = k
    omega

theorem Content.len_drop (c : Content) (k : Nat) : (c.drop k).len = c.len - k := by
  cases c with
  | str cs =>
    show (cs.drop k).length = cs.length - k
    rw [List.length_drop]
  | del n => rfl

theorem Content.chars_take_drop (c : Content) (k : Nat) :
    (c.take k).chars ++ (c.drop k).chars = c.chars := by
  cases c with
  | str cs =>
    show cs.take k ++ cs.drop k = cs
    rw [List.take_append_drop]
  | del n => rfl

theorem units_leftPart (b : Block) {k : Nat} (h : k ≤ b.len) :
    (b.leftPart k).units = unitsFrom b.id.client b.right b.id.clock b.left k := by
  show unitsFrom b.id.client b.right b.id.clock b.left (b.content.take k).len = _
  rw [Content.len_take h]

theorem units_rightPart (b : Block) (k : Nat) :
    (b.rightPart k).units = unitsFrom b.id.client b.right (b.id.clock + k)
      (some ⟨b.id.client, b.id.clock + k - 1⟩) (b.len - k) := by
  show unitsFrom b.id.client b.right (b.id.clock + k) (some ⟨b.id.client, b.id.clock + k - 1⟩)
    (b.content.drop k).len = _
  rw [Content.len_drop]
  rfl

theorem units_split (b : Block) {k : Nat} (h₁ : 0 < k) (h₂ : k < b.len) :
    (b.leftPart k).units ++ (b.rightPart k).units = b.units := by
  rw [units_leftPart b (by omega), units_rightPart]
  exact (unitsFrom_split _ _ k (b.len - k) _ _ _ _ _ h₁ (by omega) rfl rfl).symm

theorem sameUnits_splitAt (b : Block) {k : Nat} (h₁ : 0 < k) (h₂ : k < b.len) :
    SameUnits (b.splitAt k) [b] :=
  sameUnits_pair (units_split b h₁ h₂) rfl rfl (Content.chars_take_drop _ _)

theorem sameUnits_splitBlock (x : Id) (b : Block) : SameUnits (splitBlock x b) [b] := by
  unfold splitBlock
  by_cases h : x.client = b.id.client ∧ b.id.clock < x.clock ∧ x.clock < b.id.clock + b.len
  · rw [ite_eq_left h]
    exact sameUnits_splitAt b (by omega) (by omega)
  · rw [ite_eq_right h]
    exact SameUnits.refl _

/-- Splitting keeps the document. -/
theorem sameUnits_split (bs : List Block) (x : Id) : SameUnits (split bs x) bs :=
  sameUnits_flatMap _ (sameUnits_splitBlock x) bs

/-- **`split` preserves the semantics.** -/
theorem flatten_split (bs : List Block) (x : Id) : flatten (split bs x) = flatten bs :=
  (sameUnits_split bs x).units

theorem toDoc_split (bs : List Block) (x : Id) : toDoc (split bs x) = toDoc bs :=
  (sameUnits_split bs x).toDoc

theorem visible_split (bs : List Block) (x : Id) : visible (split bs x) = visible bs :=
  (sameUnits_split bs x).visible

theorem flatten_splitAfter (bs : List Block) (x : Id) :
    flatten (splitAfter bs x) = flatten bs :=
  flatten_split bs _

/-! ## Merge -/

theorem Content.len_append {a b : Content} (h : a.sameKind b = true) :
    (a.append b).len = a.len + b.len := by
  cases a with
  | str x =>
    cases b with
    | str y =>
      show (x ++ y).length = x.length + y.length
      rw [List.length_append]
    | del n => cases h
  | del m =>
    cases b with
    | str y => cases h
    | del n => rfl

theorem Content.chars_append {a b : Content} (h : a.sameKind b = true) :
    (a.append b).chars = a.chars ++ b.chars := by
  cases a with
  | str x =>
    cases b with
    | str y => rfl
    | del n => cases h
  | del m =>
    cases b with
    | str y => cases h
    | del n => rfl

theorem canMerge_spec {a b : Block} (h : canMerge a b = true) :
    a.id.client = b.id.client ∧ a.id.clock + a.len = b.id.clock ∧ 0 < a.len ∧
      b.left = some a.lastId ∧ a.right = b.right ∧ a.deleted = b.deleted ∧
      a.content.sameKind b.content = true := by
  unfold canMerge at h
  rw [Bool.and_eq_true] at h
  have h₁ := of_decide_eq_true h.1
  exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2.1, h₁.2.2.2.2.2, h.2⟩

theorem units_merge {a b : Block} (h : canMerge a b = true) :
    a.units ++ b.units = (mergeBlocks a b).units := by
  obtain ⟨hc, hk, hpos, hl, hr, _, hs⟩ := canMerge_spec h
  have hlen : (mergeBlocks a b).len = a.len + b.len := Content.len_append hs
  have e := unitsFrom_split a.id.client a.right a.len b.len a.id.clock a.left
    (a.id.clock + a.len) (a.len + b.len) (some ⟨a.id.client, a.id.clock + a.len - 1⟩)
    hpos rfl rfl rfl
  have eb : b.units = unitsFrom a.id.client a.right (a.id.clock + a.len)
      (some ⟨a.id.client, a.id.clock + a.len - 1⟩) b.len := by
    unfold Block.units
    rw [hl, ← hc, ← hr, ← hk]
    rfl
  have em : (mergeBlocks a b).units =
      unitsFrom a.id.client a.right a.id.clock a.left (a.len + b.len) := by
    show unitsFrom a.id.client a.right a.id.clock a.left (mergeBlocks a b).len = _
    rw [hlen]
  rw [em, e, eb]
  rfl

theorem sameUnits_merge {a b : Block} (h : canMerge a b = true) :
    SameUnits [mergeBlocks a b] [a, b] := by
  obtain ⟨_, _, _, _, _, hd, hs⟩ := canMerge_spec h
  exact (sameUnits_pair (units_merge h) rfl hd.symm (Content.chars_append hs).symm).symm

theorem sameUnits_mergeAt : ∀ (n : Nat) (bs : List Block), SameUnits (mergeAt n bs) bs := by
  intro n
  induction n with
  | zero =>
    intro bs
    match bs with
    | [] => exact SameUnits.refl _
    | [a] => exact SameUnits.refl _
    | a :: b :: t =>
      rw [mergeAt]
      by_cases h : canMerge a b = true
      · rw [ite_eq_left h]
        exact SameUnits.append (p := [mergeBlocks a b]) (p' := [a, b]) (sameUnits_merge h)
          (SameUnits.refl t)
      · rw [ite_eq_right h]
        exact SameUnits.refl _
  | succ n ih =>
    intro bs
    match bs with
    | [] => exact SameUnits.refl _
    | [a] => exact SameUnits.refl _
    | a :: b :: t =>
      rw [mergeAt]
      exact SameUnits.cons a (ih (b :: t))

/-- **`merge` preserves the semantics.** -/
theorem flatten_mergeAt (n : Nat) (bs : List Block) : flatten (mergeAt n bs) = flatten bs :=
  (sameUnits_mergeAt n bs).units

theorem toDoc_mergeAt (n : Nat) (bs : List Block) : toDoc (mergeAt n bs) = toDoc bs :=
  (sameUnits_mergeAt n bs).toDoc

theorem visible_mergeAt (n : Nat) (bs : List Block) : visible (mergeAt n bs) = visible bs :=
  (sameUnits_mergeAt n bs).visible

theorem sameUnits_mergeAll : ∀ (bs : List Block), SameUnits (mergeAll bs) bs := by
  intro bs
  induction bs with
  | nil => exact SameUnits.refl _
  | cons a t ih =>
    rw [mergeAll]
    cases hm : mergeAll t with
    | nil =>
      rw [hm] at ih
      exact SameUnits.append (SameUnits.refl [a]) ih
    | cons b t' =>
      rw [hm] at ih
      simp only
      by_cases h : canMerge a b = true
      · rw [ite_eq_left h]
        exact (SameUnits.append (p := [mergeBlocks a b]) (p' := [a, b]) (sameUnits_merge h)
          (SameUnits.refl t')).trans (SameUnits.cons a ih)
      · rw [ite_eq_right h]
        exact SameUnits.cons a ih

theorem flatten_mergeAll (bs : List Block) : flatten (mergeAll bs) = flatten bs :=
  (sameUnits_mergeAll bs).units

theorem toDoc_mergeAll (bs : List Block) : toDoc (mergeAll bs) = toDoc bs :=
  (sameUnits_mergeAll bs).toDoc

theorem visible_mergeAll (bs : List Block) : visible (mergeAll bs) = visible bs :=
  (sameUnits_mergeAll bs).visible

/-! ## Garbage collection -/

theorem sameUnits_gcBlock (b : Block) : SameUnits [gcBlock b] [b] := by
  unfold gcBlock
  by_cases hdel : b.deleted = true
  · rw [ite_eq_left hdel]
    exact sameUnits_of_eq rfl rfl rfl rfl rfl (Or.inl hdel)
  · rw [ite_eq_right hdel]
    exact SameUnits.refl _

/-- Dropping the content of deleted items keeps the document. -/
theorem sameUnits_gcContent (bs : List Block) : SameUnits (gcContent bs) bs := by
  induction bs with
  | nil => exact SameUnits.refl _
  | cons b t ih =>
    unfold gcContent
    rw [List.map_cons]
    exact SameUnits.append (p := [gcBlock b]) (p' := [b]) (sameUnits_gcBlock b) ih

theorem toDoc_gcContent (bs : List Block) : toDoc (gcContent bs) = toDoc bs :=
  (sameUnits_gcContent bs).toDoc

/-- **`gc` preserves the visible text** (`Content::Deleted`). -/
theorem visible_gcContent (bs : List Block) : visible (gcContent bs) = visible bs :=
  (sameUnits_gcContent bs).visible

/-- **`gc` preserves the visible text** (`Node::GC`): a deleted block that
leaves the sequence was not visible. -/
theorem visible_gcNodeAt : ∀ (n : Nat) (bs : List Block),
    visible (gcNodeAt n bs).1 = visible bs := by
  intro n
  induction n with
  | zero =>
    intro bs
    cases bs with
    | nil => rfl
    | cons b t =>
      rw [gcNodeAt]
      by_cases hdel : b.deleted = true
      · rw [ite_eq_left hdel, visible_cons, ite_eq_left hdel]
        rfl
      · rw [ite_eq_right hdel]
  | succ n ih =>
    intro bs
    cases bs with
    | nil => rfl
    | cons b t =>
      rw [gcNodeAt]
      show visible (b :: (gcNodeAt n t).1) = visible (b :: t)
      rw [visible_cons, visible_cons, ih]

end YoctoSpec
