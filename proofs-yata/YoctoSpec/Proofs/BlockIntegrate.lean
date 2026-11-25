/-
Block-level integration refines unit-level integration:

  `flatten (integrateBlock bs b) = b.units.foldl integrate (flatten bs)`

The conflict scan of `DocStore::integrate` runs on blocks, with block starts in
its two sets and `origin_owner` to map origins to them. `sim` shows that it
stops at the block the unit-level scan of the first clock stops in; the other
clocks of the new block then follow their predecessor.
-/
import YoctoSpec.Proofs.BlockScan

namespace YoctoSpec

/-! ## The clocks of a block after its first -/

def Block.tailUnits (b : Block) : List Item :=
  unitsFrom b.id.client b.right (b.id.clock + 1) (some ⟨b.id.client, b.id.clock⟩) (b.len - 1)

theorem units_eq_cons' {b : Block} (h : 0 < b.len) : b.units = b.toItem :: b.tailUnits :=
  units_eq_cons h

/-- What the scan of the clocks of `c` after the first needs: the right origin
of the new item is not one of them, its left origin is not one of the clocks
before the last, and the clocks are integrated. -/
structure ChainOk (i : Item) (ow : Id → Option Id) (c : Block) : Prop where
  right : ∀ j, c.id.clock < j → j ≤ c.id.clock + (c.len - 1) → i.right ≠ some ⟨c.id.client, j⟩
  left : ∀ j, c.id.clock ≤ j → j < c.id.clock + (c.len - 1) → i.left ≠ some ⟨c.id.client, j⟩
  owned : ∀ j, c.id.clock ≤ j → j < c.id.clock + (c.len - 1) →
    ow ⟨c.id.client, j⟩ = some ⟨c.id.client, j⟩

theorem scan_block_commit {i : Item} {ow : Id → Option Id} {c : Block} (h : ChainOk i ow c)
    (hlen : 0 < c.len) (rest : List Item) (before : List Id) :
    findConflictLeft i i.right ow (c.tailUnits ++ rest) (some c.toItem.id)
        (c.toItem.id :: before) [] =
      findConflictLeft i i.right ow rest (some c.lastId)
        (pushIds c.tailUnits (c.toItem.id :: before)) [] := by
  have key := chain_commit i i.right ow c.id.client c.right rest (c.len - 1) c.id.clock
    (c.toItem.id :: before) h.right h.left h.owned (List.mem_cons_self ..)
  have e : c.id.clock + (c.len - 1) = c.id.clock + c.len - 1 := by omega
  rw [e] at key
  exact key

theorem scan_block_skip {i : Item} {ow : Id → Option Id} {c : Block} (h : ChainOk i ow c)
    (rest : List Item) (left : Option Id) (before conf : List Id) :
    findConflictLeft i i.right ow (c.tailUnits ++ rest) left (c.toItem.id :: before)
        (c.toItem.id :: conf) =
      findConflictLeft i i.right ow rest left (pushIds c.tailUnits (c.toItem.id :: before))
        (pushIds c.tailUnits (c.toItem.id :: conf)) :=
  chain_skip i i.right ow c.id.client c.right rest left (c.len - 1) c.id.clock
    (c.toItem.id :: before) (c.toItem.id :: conf) h.right h.left h.owned
    (List.mem_cons_self ..) (List.mem_cons_self ..)

theorem mem_push_block {c : Block} (hlen : 0 < c.len) {acc : List Id} {x : Id} :
    x ∈ pushIds c.tailUnits (c.toItem.id :: acc) ↔ x ∈ c.units.map Item.id ∨ x ∈ acc := by
  rw [mem_pushIds, units_eq_cons' hlen, List.map_cons, List.mem_cons, List.mem_cons]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · rintro ((h | h) | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem ids_subset_flatten {bs : List Block} {c : Block} (hc : c ∈ bs) {x : Id}
    (hx : x ∈ c.units.map Item.id) : x ∈ (flatten bs).map Item.id := by
  obtain ⟨u, hu, e⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨u, units_subset_flatten hc hu, e⟩

/-! ## The relation between the two scans -/

/-- The unit-level set holds the clocks of the blocks of the block-level set. -/
def SetRel (bs : List Block) (accU accB : List Id) : Prop :=
  ∀ x, x ∈ accU ↔ ∃ o, ownerB bs x = some o ∧ o ∈ accB

theorem setRel_nil (bs : List Block) : SetRel bs [] [] := by
  intro x
  constructor
  · intro h
    cases h
  · rintro ⟨o, _, h⟩
    cases h

theorem setRel_push {bs : List Block} (hn : NodupIds (flatten bs)) (hw : BlockWF bs) {c : Block}
    (hc : c ∈ bs) {accU accB : List Id} (h : SetRel bs accU accB) :
    SetRel bs (pushIds c.tailUnits (c.toItem.id :: accU)) (c.id :: accB) := by
  intro x
  rw [mem_push_block (hw c hc)]
  constructor
  · rintro (hx | hx)
    · exact ⟨c.id, ownerB_of_mem hn hc hx, List.mem_cons_self ..⟩
    · obtain ⟨o, ho, hm⟩ := (h x).mp hx
      exact ⟨o, ho, List.mem_cons_of_mem _ hm⟩
  · rintro ⟨o, ho, hm⟩
    rcases List.mem_cons.mp hm with e | hm'
    · rw [e] at ho
      exact Or.inl ((ownerB_eq_iff hn hw hc).mp ho)
    · exact Or.inr ((h x).mpr ⟨o, ho, hm'⟩)

/-- The block-level left neighbour and the unit-level one are the same place:
the start of the sequence, or a block and its last clock. -/
def LastOf (bs : List Block) (leftB leftU : Option Id) : Prop :=
  (leftB = none ∧ leftU = none) ∨ ∃ L, L ∈ bs ∧ leftB = some L.id ∧ leftU = some L.lastId

/-- The sequence after `repair` split it at the origins of `i`. -/
structure SimCtx (bs : List Block) (i : Item) : Prop where
  wf : BlockWF bs
  legal : Legal (flatten bs)
  /-- a block ends at the left origin -/
  leftEnd : ∀ l, i.left = some l → ∀ c, c ∈ bs → c.contains l = true → c.lastId = l
  /-- a block starts at the right origin -/
  rightStart : ∀ r, i.right = some r → ∀ c, c ∈ bs → c.contains r = true → c.id = r

/-- The left origin of a block is not one of its own clocks. -/
theorem left_not_in_block {pb cs : List Block} {c : Block}
    (hs : Legal (flatten (pb ++ c :: cs))) (hlen : 0 < c.len) {cl : Id}
    (hleft : c.toItem.left = some cl) : ¬ cl ∈ c.units.map Item.id := by
  have e : flatten (pb ++ c :: cs) = flatten pb ++ (c.toItem :: (c.tailUnits ++ flatten cs)) := by
    rw [flatten_append, flatten_cons, units_eq_cons' hlen, List.cons_append]
  have hn := hs.nodup
  have hcu : c.toItem ∈ flatten (pb ++ c :: cs) := by
    rw [e]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hlt := hs.left_lt c.toItem hcu
  rw [e] at hn hlt
  have hix := hn.ix_mid
  rw [hleft, ixL_some, hix] at hlt
  intro hmem
  obtain ⟨u, hu, eu⟩ := List.mem_map.mp hmem
  by_cases hp : ix (flatten pb) cl ≤ (flatten pb).length
  · obtain ⟨a, ha, ea⟩ := ix_le_length_iff.mp hp
    unfold NodupIds at hn
    rw [List.pairwise_append] at hn
    have hu' : u ∈ c.toItem :: (c.tailUnits ++ flatten cs) := by
      rw [units_eq_cons' hlen] at hu
      rcases List.mem_cons.mp hu with e' | h'
      · rw [e']
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h')
    exact hn.2.2 a ha u hu' (by rw [ea, eu])
  · have h₁ := ix_append_right (c.toItem :: (c.tailUnits ++ flatten cs))
      (show (flatten pb).length < ix (flatten pb) cl by omega)
    have h₂ := ix_pos (c.toItem :: (c.tailUnits ++ flatten cs)) cl
    omega

theorem chainOk_of_ctx {bs : List Block} {i : Item} (ctx : SimCtx bs i) {c : Block}
    (hc : c ∈ bs) : ChainOk i (owner (flatten bs)) c := by
  have inC : ∀ j, c.id.clock ≤ j → j < c.id.clock + c.len →
      (⟨c.id.client, j⟩ : Id) ∈ c.units.map Item.id := by
    intro j h₁ h₂
    exact mem_units_ids.mpr ⟨rfl, h₁, h₂⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j h₁ h₂ e
    have h := ctx.rightStart _ e c hc (contains_iff.mpr (inC j (by omega) (by omega)))
    have h' : c.id.clock = j := congrArg Id.clock h
    omega
  · intro j h₁ h₂ e
    have h := ctx.leftEnd _ e c hc (contains_iff.mpr (inC j (by omega) (by omega)))
    have h' : c.id.clock + c.len - 1 = j := congrArg Id.clock h
    omega
  · intro j h₁ h₂
    exact owner_of_mem (ids_subset_flatten hc (inC j (by omega) (by omega)))

/-- **The block-level scan and the unit-level scan stop at the same place.** -/
theorem sim {bs : List Block} {i : Item} (ctx : SimCtx bs i) :
    ∀ (cs pb : List Block) (leftB leftU : Option Id) (beforeB beforeU confB confU : List Id),
      bs = pb ++ cs → SetRel bs beforeU beforeB → SetRel bs confU confB →
      LastOf bs leftB leftU →
      LastOf bs
        (findConflictLeft i i.right (ownerB bs) (cs.map Block.toItem) leftB beforeB confB)
        (findConflictLeft i i.right (owner (flatten bs)) (flatten cs) leftU beforeU confU) := by
  intro cs
  induction cs with
  | nil =>
    intro pb leftB leftU beforeB beforeU confB confU _ _ _ hl
    rw [List.map_nil, flatten_nil, fcl_nil, fcl_nil]
    exact hl
  | cons c cs ih =>
    intro pb leftB leftU beforeB beforeU confB confU hbs hbef hconf hl
    have hn := ctx.legal.nodup
    have hc : c ∈ bs := by
      rw [hbs]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    have hlen := ctx.wf c hc
    have hbs' : bs = (pb ++ [c]) ++ cs := by
      rw [hbs]
      simp
    have chain := chainOk_of_ctx ctx hc
    rw [List.map_cons, flatten_cons, units_eq_cons' hlen, List.cons_append]
    have next_commit : LastOf bs
        (findConflictLeft i i.right (ownerB bs) (cs.map Block.toItem) (some c.toItem.id)
          (c.toItem.id :: beforeB) [])
        (findConflictLeft i i.right (owner (flatten bs)) (c.tailUnits ++ flatten cs)
          (some c.toItem.id) (c.toItem.id :: beforeU) []) := by
      rw [scan_block_commit chain hlen]
      exact ih (pb ++ [c]) _ _ _ _ _ _ hbs' (setRel_push hn ctx.wf hc hbef) (setRel_nil bs)
        (Or.inr ⟨c, hc, rfl, rfl⟩)
    have next_skip : LastOf bs
        (findConflictLeft i i.right (ownerB bs) (cs.map Block.toItem) leftB
          (c.toItem.id :: beforeB) (c.toItem.id :: confB))
        (findConflictLeft i i.right (owner (flatten bs)) (c.tailUnits ++ flatten cs) leftU
          (c.toItem.id :: beforeU) (c.toItem.id :: confU)) := by
      rw [scan_block_skip chain]
      exact ih (pb ++ [c]) _ _ _ _ _ _ hbs' (setRel_push hn ctx.wf hc hbef)
        (setRel_push hn ctx.wf hc hconf) hl
    -- the block and its first clock take the same branch
    by_cases hR : i.right = some c.toItem.id
    · rw [fcl_stop_right hR, fcl_stop_right hR]
      exact hl
    · by_cases hL : i.left = c.toItem.left
      · by_cases hcl : c.toItem.id.client < i.id.client
        · rw [fcl_same_commit hR hL hcl, fcl_same_commit hR hL hcl]
          exact next_commit
        · by_cases hRR : i.right = c.toItem.right
          · rw [fcl_same_stop hR hL hcl hRR, fcl_same_stop hR hL hcl hRR]
            exact hl
          · rw [fcl_same_skip hR hL hcl hRR, fcl_same_skip hR hL hcl hRR]
            exact next_skip
      · cases hleft : c.toItem.left with
        | none =>
          rw [fcl_other_none hR hL hleft, fcl_other_none hR hL hleft]
          exact hl
        | some cl =>
          have hcu : c.toItem ∈ flatten bs := units_subset_flatten hc (toItem_mem_units hlen)
          have hclp : ix (flatten bs) cl ≤ (flatten bs).length :=
            ctx.legal.left_present hcu cl hleft
          obtain ⟨o, ho⟩ := ownerB_of_present hclp
          have hou : owner (flatten bs) cl = some cl := owner_of_present hclp
          have hnot : ¬ cl ∈ c.units.map Item.id :=
            left_not_in_block (by rw [← hbs]; exact ctx.legal) hlen hleft
          have hne₁ : cl ≠ c.toItem.id := by
            intro e
            apply hnot
            rw [e]
            exact List.mem_map.mpr ⟨c.toItem, toItem_mem_units hlen, rfl⟩
          have hne₂ : o ≠ c.toItem.id := by
            intro e
            rw [e] at ho
            exact hnot ((ownerB_eq_iff hn ctx.wf hc).mp ho)
          have same : ∀ {accU accB : List Id}, SetRel bs accU accB →
              (cl ∈ c.toItem.id :: accU ↔ o ∈ c.toItem.id :: accB) := by
            intro accU accB hrel
            rw [List.mem_cons, List.mem_cons]
            constructor
            · rintro (e | h)
              · exact absurd e hne₁
              · obtain ⟨o', ho', hm⟩ := (hrel cl).mp h
                rw [ho] at ho'
                rw [Option.some.inj ho']
                exact Or.inr hm
            · rintro (e | h)
              · exact absurd e hne₂
              · exact Or.inr ((hrel cl).mpr ⟨o, ho, h⟩)
          by_cases hb : o ∈ c.toItem.id :: beforeB
          · have hb' := (same hbef).mpr hb
            by_cases hcf : o ∈ c.toItem.id :: confB
            · have hcf' := (same hconf).mpr hcf
              rw [fcl_other_skip hR hL hleft ho hb hcf, fcl_other_skip hR hL hleft hou hb' hcf']
              exact next_skip
            · have hcf' : ¬ cl ∈ c.toItem.id :: confU := fun h => hcf ((same hconf).mp h)
              rw [fcl_other_commit hR hL hleft ho hb hcf,
                fcl_other_commit hR hL hleft hou hb' hcf']
              exact next_commit
          · have hb' : ¬ cl ∈ c.toItem.id :: beforeU := fun h => hb ((same hbef).mp h)
            rw [fcl_other_stop hR hL hleft ho hb, fcl_other_stop hR hL hleft hou hb']
            exact hl

/-! ## Positions in a sequence -/

theorem exists_split {α : Type} {a : α} {l : List α} (h : a ∈ l) : ∃ p q, l = p ++ a :: q := by
  induction l with
  | nil => cases h
  | cons x t ih =>
    rcases List.mem_cons.mp h with e | h'
    · exact ⟨[], t, by rw [e]; rfl⟩
    · obtain ⟨p, q, e⟩ := ih h'
      exact ⟨x :: p, q, by rw [e]; rfl⟩

theorem afterId_append_cons {A : List Item} {a : Item} {B : List Item}
    (h : ∀ u, u ∈ A → u.id ≠ a.id) : afterId a.id (A ++ a :: B) = B := by
  induction A with
  | nil =>
    show afterId a.id (a :: B) = B
    rw [afterId, ite_eq_left rfl]
  | cons x t ih =>
    show afterId a.id (x :: (t ++ a :: B)) = B
    rw [afterId, ite_eq_right (h x (List.mem_cons_self ..))]
    exact ih (fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem insertAfterId_append_cons {A : List Item} {a : Item} {B : List Item} (i : Item)
    (h : ∀ u, u ∈ A → u.id ≠ a.id) :
    insertAfterId a.id i (A ++ a :: B) = A ++ a :: i :: B := by
  induction A with
  | nil =>
    show insertAfterId a.id i (a :: B) = a :: i :: B
    rw [insertAfterId, ite_eq_left rfl]
  | cons x t ih =>
    show insertAfterId a.id i (x :: (t ++ a :: B)) = x :: (t ++ a :: i :: B)
    rw [insertAfterId, ite_eq_right (h x (List.mem_cons_self ..)),
      ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]

theorem afterBId_append_cons {P : List Block} {L : Block} {Q : List Block}
    (h : ∀ d, d ∈ P → d.id ≠ L.id) : afterBId L.id (P ++ L :: Q) = Q := by
  induction P with
  | nil =>
    show afterBId L.id (L :: Q) = Q
    rw [afterBId, ite_eq_left rfl]
  | cons x t ih =>
    show afterBId L.id (x :: (t ++ L :: Q)) = Q
    rw [afterBId, ite_eq_right (h x (List.mem_cons_self ..))]
    exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd))

theorem insertAfterBId_append_cons {P : List Block} {L : Block} {Q : List Block} (n : Block)
    (h : ∀ d, d ∈ P → d.id ≠ L.id) :
    insertAfterBId L.id n (P ++ L :: Q) = P ++ L :: n :: Q := by
  induction P with
  | nil =>
    show insertAfterBId L.id n (L :: Q) = L :: n :: Q
    rw [insertAfterBId, ite_eq_left rfl]
  | cons x t ih =>
    show insertAfterBId L.id n (x :: (t ++ L :: Q)) = x :: (t ++ L :: n :: Q)
    rw [insertAfterBId, ite_eq_right (h x (List.mem_cons_self ..)),
      ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]

/-- Block starts before a block are different from its start. -/
theorem block_ids_prefix {P Q : List Block} {L : Block}
    (hn : NodupIds (flatten (P ++ L :: Q))) (hw : BlockWF (P ++ L :: Q)) :
    ∀ d, d ∈ P → d.id ≠ L.id := by
  intro d hd e
  rw [flatten_append, flatten_cons] at hn
  unfold NodupIds at hn
  rw [List.pairwise_append] at hn
  have h₁ : d.toItem ∈ flatten P :=
    units_subset_flatten hd (toItem_mem_units (hw d (List.mem_append_left _ hd)))
  have h₂ : L.toItem ∈ L.units ++ flatten Q :=
    List.mem_append_left _
      (toItem_mem_units (hw L (List.mem_append_right _ (List.mem_cons_self ..))))
  exact hn.2.2 _ h₁ _ h₂ e

theorem unitsFrom_snoc (c : Nat) (r : Option Id) :
    ∀ (n k : Nat) (l : Option Id),
      ∃ init last, unitsFrom c r k l (n + 1) = init ++ [last] ∧ last.id = ⟨c, k + n⟩ := by
  intro n
  induction n with
  | zero =>
    intro k l
    refine ⟨[], ⟨⟨c, k⟩, l, r⟩, ?_, rfl⟩
    rw [unitsFrom, unitsFrom]
    rfl
  | succ n ih =>
    intro k l
    obtain ⟨init, last, e, hl⟩ := ih (k + 1) (some ⟨c, k⟩)
    refine ⟨⟨⟨c, k⟩, l, r⟩ :: init, last, ?_, ?_⟩
    · rw [unitsFrom, e]
      rfl
    · rw [hl]
      exact Id.ext' rfl (by show k + 1 + n = k + (n + 1); omega)

/-- The last clock of a block. -/
theorem units_snoc {b : Block} (h : 0 < b.len) :
    ∃ init last, b.units = init ++ [last] ∧ last.id = b.lastId := by
  have e : b.len = (b.len - 1) + 1 := by omega
  obtain ⟨init, last, hu, hl⟩ := unitsFrom_snoc b.id.client b.right (b.len - 1) b.id.clock b.left
  refine ⟨init, last, ?_, ?_⟩
  · unfold Block.units
    rw [e]
    exact hu
  · rw [hl]
    exact Id.ext' rfl (by show b.id.clock + (b.len - 1) = b.id.clock + b.len - 1; omega)

/-! ## The clocks after the first follow their predecessor -/

theorem owner_some {s : List Item} {x o : Id} (h : owner s x = some o) : o = x := by
  unfold owner at h
  by_cases hm : x ∈ s.map Item.id
  · rw [ite_eq_left hm] at h
    exact (Option.some.inj h).symm
  · rw [ite_eq_right hm] at h
    cases h

/-- An item whose left origin `prev` has no other item to its right that names
`prev` is linked right after `prev`. -/
theorem integrate_after_prev {X Y : List Item} {prev u : Item} (hl : u.left = some prev.id)
    (hX : ∀ a, a ∈ X → a.id ≠ prev.id) (hY₁ : ∀ y, y ∈ Y → y.left ≠ some prev.id)
    (hY₂ : ∀ y, y ∈ Y → y.left ≠ some y.id) :
    integrate (X ++ prev :: Y) u = X ++ prev :: u :: Y := by
  unfold integrate
  rw [hl]
  have e₁ : after (some prev.id) (X ++ prev :: Y) = Y := afterId_append_cons hX
  rw [e₁]
  have e₂ : findConflictLeft u u.right (owner (X ++ prev :: Y)) Y (some prev.id) [] [] =
      some prev.id := by
    cases Y with
    | nil => exact fcl_nil
    | cons y Y' =>
      have hy : y ∈ y :: Y' := List.mem_cons_self ..
      by_cases hR : u.right = some y.id
      · exact fcl_stop_right hR
      · have hL : u.left ≠ y.left := by
          rw [hl]
          exact fun e => hY₁ y hy e.symm
        cases hyl : y.left with
        | none => exact fcl_other_none hR hL hyl
        | some yl =>
          cases how : owner (X ++ prev :: y :: Y') yl with
          | none => exact fcl_other_unowned hR hL hyl how
          | some o =>
            have ho : o = yl := owner_some how
            apply fcl_other_stop hR hL hyl how
            intro hm
            rcases List.mem_cons.mp hm with e | h'
            · exact hY₂ y hy (by rw [hyl, ← ho, e])
            · cases h'
  rw [e₂]
  exact insertAfterId_append_cons u hX

/-- The clocks of a new block after its first are integrated one after the
other, right behind their predecessor. -/
theorem fold_chain (c : Nat) (r : Option Id) :
    ∀ (n p : Nat) (X Y : List Item) (prev : Item), prev.id = ⟨c, p⟩ →
      (∀ a, a ∈ X → ∀ j, p ≤ j → a.id ≠ ⟨c, j⟩) →
      (∀ y, y ∈ Y → ∀ j, p ≤ j → y.left ≠ some ⟨c, j⟩) →
      (∀ y, y ∈ Y → y.left ≠ some y.id) →
      (unitsFrom c r (p + 1) (some ⟨c, p⟩) n).foldl integrate (X ++ prev :: Y) =
        X ++ prev :: (unitsFrom c r (p + 1) (some ⟨c, p⟩) n ++ Y) := by
  intro n
  induction n with
  | zero =>
    intro p X Y prev _ _ _ _
    rw [unitsFrom]
    rfl
  | succ n ih =>
    intro p X Y prev hp hX hY₁ hY₂
    rw [unitsFrom, List.foldl_cons]
    have step : integrate (X ++ prev :: Y) ⟨⟨c, p + 1⟩, some ⟨c, p⟩, r⟩ =
        (X ++ [prev]) ++ (⟨⟨c, p + 1⟩, some ⟨c, p⟩, r⟩ : Item) :: Y := by
      rw [integrate_after_prev (prev := prev) (by rw [hp])
        (fun a ha => by rw [hp]; exact hX a ha p (Nat.le_refl _))
        (fun y hy => by rw [hp]; exact hY₁ y hy p (Nat.le_refl _)) hY₂]
      simp
    rw [step, ih (p + 1) (X ++ [prev]) Y ⟨⟨c, p + 1⟩, some ⟨c, p⟩, r⟩ rfl ?_ ?_ hY₂]
    · simp
    · intro a ha j hj
      rcases List.mem_append.mp ha with h | h
      · exact hX a h j (by omega)
      · rcases List.mem_cons.mp h with e | h'
        · rw [e, hp]
          intro e'
          have h'' : p = j := congrArg Id.clock e'
          omega
        · cases h'
    · intro y hy j hj
      exact hY₁ y hy j (by omega)

/-! ## `repair` -/

theorem flatten_splitLeft (o : Option Id) (bs : List Block) :
    flatten (splitLeft o bs) = flatten bs := by
  cases o with
  | none => rfl
  | some l => exact flatten_splitAfter bs l

theorem flatten_splitRight (o : Option Id) (bs : List Block) :
    flatten (splitRight o bs) = flatten bs := by
  cases o with
  | none => rfl
  | some r => exact flatten_split bs r

theorem blockWF_splitLeft {bs : List Block} (hw : BlockWF bs) (o : Option Id) :
    BlockWF (splitLeft o bs) := by
  cases o with
  | none => exact hw
  | some l => exact blockWF_split hw _

theorem blockWF_splitRight {bs : List Block} (hw : BlockWF bs) (o : Option Id) :
    BlockWF (splitRight o bs) := by
  cases o with
  | none => exact hw
  | some r => exact blockWF_split hw _

theorem lastId_of_aligned {bs : List Block} {l : Id} (h : Aligned ⟨l.client, l.clock + 1⟩ bs)
    {c : Block} (hc : c ∈ bs) (hcon : c.contains l = true) : c.lastId = l := by
  have h₁ := mem_units_ids.mp (contains_iff.mp hcon)
  have h₂ := h c hc
  have h₃ : ¬ (l.client = c.id.client ∧ c.id.clock < l.clock + 1 ∧ l.clock + 1 < c.id.clock + c.len) :=
    h₂
  exact Id.ext' h₁.1.symm (by show c.id.clock + c.len - 1 = l.clock; omega)

theorem id_of_aligned {bs : List Block} {r : Id} (h : Aligned r bs) {c : Block} (hc : c ∈ bs)
    (hcon : c.contains r = true) : c.id = r := by
  have h₁ := mem_units_ids.mp (contains_iff.mp hcon)
  have h₂ := h c hc
  exact Id.ext' h₁.1.symm (by omega)

/-- After `repair` the sequence is split at both origins of the new block. -/
theorem simCtx_repair {bs : List Block} {b : Block} (hw : BlockWF bs)
    (hs : Legal (flatten bs)) :
    SimCtx (splitRight b.right (splitLeft b.left bs)) b.toItem := by
  refine ⟨blockWF_splitRight (blockWF_splitLeft hw _) _, ?_, ?_, ?_⟩
  · rw [flatten_splitRight, flatten_splitLeft]
    exact hs
  · intro l hl c hc hcon
    have hl' : b.left = some l := hl
    have ha : Aligned ⟨l.client, l.clock + 1⟩ (splitLeft b.left bs) := by
      rw [hl']
      exact aligned_split bs _
    have ha' : Aligned ⟨l.client, l.clock + 1⟩ (splitRight b.right (splitLeft b.left bs)) := by
      cases b.right with
      | none => exact ha
      | some r => exact aligned_split_of_aligned ha r
    exact lastId_of_aligned ha' hc hcon
  · intro r hr c hc hcon
    have hr' : b.right = some r := hr
    rw [hr'] at hc
    exact id_of_aligned (aligned_split _ r) hc hcon

/-- The scan on blocks ends at the block the unit-level scan of the first clock
ends in. -/
theorem scanB_lastOf {bs : List Block} {b : Block} (ctx : SimCtx bs b.toItem)
    (hi : CanIntegrate (flatten bs) b.toItem) :
    LastOf bs (scanB bs b)
      (findConflictLeft b.toItem b.right (owner (flatten bs)) (after b.left (flatten bs))
        b.left [] []) := by
  unfold scanB
  cases hl : b.left with
  | none =>
    exact sim ctx bs [] none none [] [] [] [] rfl (setRel_nil bs) (setRel_nil bs)
      (Or.inl ⟨rfl, rfl⟩)
  | some l =>
    have hn := ctx.legal.nodup
    have hlp : ix (flatten bs) l ≤ (flatten bs).length := hi.left_mem l hl
    obtain ⟨o, ho⟩ := ownerB_of_present hlp
    obtain ⟨L, hL, eL, hxL⟩ := ownerB_some ho
    have hlast : L.lastId = l := ctx.leftEnd l hl L hL (contains_iff.mpr hxL)
    obtain ⟨P, Q, hPQ⟩ := exists_split hL
    have hP : ∀ d, d ∈ P → d.id ≠ L.id :=
      block_ids_prefix (by rw [← hPQ]; exact hn) (by rw [← hPQ]; exact ctx.wf)
    obtain ⟨init, last, hinit, hlastid⟩ := units_snoc (ctx.wf L hL)
    have hF : flatten bs = (flatten P ++ init) ++ last :: flatten Q := by
      rw [hPQ, flatten_append, flatten_cons, hinit]
      simp
    have hX : ∀ a, a ∈ flatten P ++ init → a.id ≠ last.id := by
      intro a ha
      rw [hF] at hn
      unfold NodupIds at hn
      rw [List.pairwise_append] at hn
      exact hn.2.2 a ha last (List.mem_cons_self ..)
    have e₁ : (some l).bind (ownerB bs) = some o := ho
    have e₂ : afterB (some o) bs = Q := by
      rw [← eL, hPQ]
      exact afterBId_append_cons hP
    have e₃ : after (some l) (flatten bs) = flatten Q := by
      rw [hF, ← hlast, ← hlastid]
      exact afterId_append_cons hX
    rw [e₁, e₂, e₃]
    refine sim ctx Q (P ++ [L]) (some o) (some l) [] [] [] [] ?_ (setRel_nil bs) (setRel_nil bs)
      (Or.inr ⟨L, hL, by rw [eL], by rw [hlast]⟩)
    rw [hPQ]
    simp

/-- **Block-level integration is unit-level integration of the clocks of the
block, in clock order.** -/
theorem flatten_integrateBlock {bs : List Block} {b : Block} (hw : BlockWF bs)
    (hs : Legal (flatten bs)) (hb : 0 < b.len) (hi : CanIntegrate (flatten bs) b.toItem)
    (hfresh : ∀ a, a ∈ flatten bs → ∀ j, b.id.clock ≤ j → a.id ≠ ⟨b.id.client, j⟩) :
    flatten (integrateBlock bs b) = b.units.foldl integrate (flatten bs) := by
  have e₂ : flatten (splitRight b.right (splitLeft b.left bs)) = flatten bs := by
    rw [flatten_splitRight, flatten_splitLeft]
  have ctx := simCtx_repair (b := b) hw hs
  show flatten (insertAfterB (scanB (splitRight b.right (splitLeft b.left bs)) b) b
    (splitRight b.right (splitLeft b.left bs))) = _
  generalize splitRight b.right (splitLeft b.left bs) = bs₂ at e₂ ctx ⊢
  rw [← e₂] at hi hfresh hs ⊢
  have K := scanB_lastOf ctx hi
  have hint : integrate (flatten bs₂) b.toItem =
      insertAfter (findConflictLeft b.toItem b.right (owner (flatten bs₂))
        (after b.left (flatten bs₂)) b.left [] []) b.toItem (flatten bs₂) := rfl
  rw [units_eq_cons' hb, List.foldl_cons, hint]
  have hY₂ : ∀ y, y ∈ flatten bs₂ → y.left ≠ some y.id := by
    intro y hy e
    have := hs.left_lt y hy
    rw [e, ixL_some] at this
    omega
  have hY₁ : ∀ y, y ∈ flatten bs₂ → ∀ j, b.id.clock ≤ j → y.left ≠ some ⟨b.id.client, j⟩ := by
    intro y hy j hj e
    obtain ⟨a, ha, ea⟩ := ix_le_length_iff.mp (hs.left_present hy _ e)
    exact hfresh a ha j hj ea
  rcases K with ⟨eB, eU⟩ | ⟨L, hL, eB, eU⟩
  · rw [eB, eU]
    have key := fold_chain b.id.client b.right (b.len - 1) b.id.clock [] (flatten bs₂) b.toItem
      rfl (by intro a ha; cases ha) hY₁ hY₂
    show flatten (b :: bs₂) = b.tailUnits.foldl integrate (b.toItem :: flatten bs₂)
    rw [flatten_cons, units_eq_cons' hb]
    exact key.symm
  · rw [eB, eU]
    have hn := hs.nodup
    obtain ⟨P, Q, hPQ⟩ := exists_split hL
    have hP : ∀ d, d ∈ P → d.id ≠ L.id :=
      block_ids_prefix (by rw [← hPQ]; exact hn) (by rw [← hPQ]; exact ctx.wf)
    obtain ⟨init, last, hinit, hlastid⟩ := units_snoc (ctx.wf L hL)
    have hF : flatten bs₂ = (flatten P ++ init) ++ last :: flatten Q := by
      rw [hPQ, flatten_append, flatten_cons, hinit]
      simp
    have hX : ∀ a, a ∈ flatten P ++ init → a.id ≠ last.id := by
      intro a ha
      rw [hF] at hn
      unfold NodupIds at hn
      rw [List.pairwise_append] at hn
      exact hn.2.2 a ha last (List.mem_cons_self ..)
    have eblock : insertAfterB (some L.id) b bs₂ = P ++ L :: b :: Q := by
      rw [hPQ]
      exact insertAfterBId_append_cons b hP
    have eunit : insertAfter (some L.lastId) b.toItem (flatten bs₂) =
        ((flatten P ++ init) ++ [last]) ++ b.toItem :: flatten Q := by
      rw [hF, ← hlastid]
      have h := insertAfterId_append_cons (B := flatten Q) b.toItem hX
      have h' : insertAfter (some last.id) b.toItem ((flatten P ++ init) ++ last :: flatten Q) =
          (flatten P ++ init) ++ last :: b.toItem :: flatten Q := h
      rw [h']
      simp
    have inS : ∀ a, a ∈ (flatten P ++ init) ++ [last] → a ∈ flatten bs₂ := by
      intro a ha
      rw [hF]
      rcases List.mem_append.mp ha with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.mp h with e | h'
        · rw [e]
          exact List.mem_append_right _ (List.mem_cons_self ..)
        · cases h'
    have inQ : ∀ y, y ∈ flatten Q → y ∈ flatten bs₂ := by
      intro y hy
      rw [hF]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
    have key := fold_chain b.id.client b.right (b.len - 1) b.id.clock
      ((flatten P ++ init) ++ [last]) (flatten Q) b.toItem rfl
      (fun a ha j hj => hfresh a (inS a ha) j hj)
      (fun y hy j hj => hY₁ y (inQ y hy) j hj)
      (fun y hy => hY₂ y (inQ y hy))
    rw [eblock, eunit]
    have key' : b.tailUnits.foldl integrate
        (((flatten P ++ init) ++ [last]) ++ b.toItem :: flatten Q) =
        ((flatten P ++ init) ++ [last]) ++ b.toItem :: (b.tailUnits ++ flatten Q) := key
    rw [key', flatten_append, flatten_cons, flatten_cons, hinit, units_eq_cons' hb]
    simp

end YoctoSpec
