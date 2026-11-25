/-
`merge_adjacent` and `visible_ids` of `y_octo_core::yata_store` on the model
of `YataModel`.

`mergeNode` is the store after two neighbours of a timeline that are
neighbours of the sequence too became one item: it keeps the invariant
(`mergeNode_spec`) and its block sequence is `YoctoSpec.mergeAt` of the one
before (`blocks_mergeNode`), so it stands for the same document. `visM` is
what `visible_ids` answers: the first id and the length of every block that is
not deleted (`visM_blocks`), which are, clock by clock, the visible ids of the
document (`expand_visM`). Only Lean core and `YoctoSpec` are used.
-/
import YoctoSpec
import YoctoCore.Properties.ListAux
import YoctoCore.Properties.YataModel

set_option autoImplicit false

namespace YoctoCore.Properties.YataModel

open YoctoSpec
open YoctoCore.Properties.ListAux

/-! ## Lists without one position -/

theorem mem_delAt_of_ne {α : Type} {l : List α} {i : Nat} {a x : α} (hx : x ∈ l)
    (hi : l[i]? = some a) (hne : x ≠ a) : x ∈ delAt l i := by
  obtain ⟨j, hj⟩ := mem_get? hx
  by_cases h1 : j < i
  · exact get?_mem (i := j) (by rw [get?_delAt_lt l h1]; exact hj)
  · have h2 : j ≠ i := by
      intro e
      rw [e, hi] at hj
      exact hne (Option.some.inj hj).symm
    obtain ⟨j', ej⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [ej] at hj
    exact get?_mem (i := j') (by rw [get?_delAt_ge l (by omega : i ≤ j')]; exact hj)

theorem not_mem_delAt_self {α : Type} {l : List α} {i : Nat} {a : α} (hn : l.Nodup)
    (hi : l[i]? = some a) : ¬ a ∈ delAt l i := by
  intro ha
  obtain ⟨q, hq⟩ := mem_get? ha
  rcases get?_delAt_cases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := nodup_get?_inj hn h2 hi
    omega
  · have := nodup_get?_inj hn h2 hi
    omega

/-- Mapping a list with another function that differs at one position. -/
theorem map_eq_upd_map {α β : Type} {o : List α} {k : Nat} {i : α} (hn : o.Nodup)
    (hk : o[k]? = some i) (g g' : α → β) (m : β) (hi : g' i = m)
    (hother : ∀ j, j ∈ o → j ≠ i → g' j = g j) :
    o.map g' = upd (o.map g) k (fun _ => m) := by
  apply ext_get?
  intro j
  rw [get?_map, get?_upd, get?_map]
  by_cases e : j = k
  · rw [ite_eq_left e, e, hk]
    show some (g' i) = some m
    rw [hi]
  · rw [ite_eq_right e]
    cases hj : o[j]? with
    | none => rfl
    | some a =>
      show some (g' a) = some (g a)
      rw [hother a (get?_mem hj) (fun ea => e (nodup_get?_inj hn (by rw [ea] at hj; exact hj) hk))]

/-- The first position of `x` in `l`. -/
def posOf : List Nat → Nat → Nat
  | [], _ => 0
  | a :: t, x => if a = x then 0 else posOf t x + 1

theorem posOf_get? : ∀ {l : List Nat} {k a : Nat}, l.Nodup → l[k]? = some a → posOf l a = k
  | [], k, a, _, h => by simp at h
  | b :: t, 0, a, _, h => by
    have e : b = a := by simpa using h
    show (if b = a then 0 else posOf t a + 1) = 0
    exact ite_eq_left e
  | b :: t, k + 1, a, hn, h => by
    have h' : t[k]? = some a := by simpa using h
    have hn' := List.nodup_cons.mp hn
    have hne : ¬ b = a := fun e => hn'.1 (by rw [e]; exact get?_mem h')
    show (if b = a then 0 else posOf t a + 1) = k + 1
    rw [ite_eq_right hne, posOf_get? hn'.2 h']

/-! ## Timelines without one block boundary -/

theorem endAt_delAt_lt {blocks : List MBlock} {stop q i : Nat} (h : q + 1 < i) :
    endAt (delAt blocks i) stop q = endAt blocks stop q := by
  unfold endAt
  rw [get?_delAt_lt blocks h]

theorem endAt_delAt_ge {blocks : List MBlock} {stop q i : Nat} (h : i ≤ q + 1) :
    endAt (delAt blocks i) stop q = endAt blocks stop (q + 1) := by
  unfold endAt
  rw [get?_delAt_ge blocks h]

/-- The timeline of a client without the block boundary at `q`. -/
def MClient.withoutBlock (c : MClient) (q : Nat) : MClient :=
  { c with blocks := delAt c.blocks q }

/-! ## Merging two items -/

/-- `merge_adjacent`: the item at slot `r`, the block `p + 1` of the timeline
`ci`, becomes the end of the item at slot `l`, the block `p`. The slot `r`
stays in the arena and leaves the sequence. -/
def mergeNode (s : MStore) (ci p l r : Nat) : MStore :=
  { items := setLeft l (rightOf s.items r)
      (upd s.items l (fun z =>
        { z with len := z.len + (itemAt s.items r).len, right := rightOf s.items r }))
    start := s.start
    clients := upd s.clients ci (fun c => c.withoutBlock (p + 1)) }

/-- A merge keeps the invariant: the right item leaves the sequence, and only
the left one changes. -/
theorem mergeNode_spec {s : MStore} (h : WF s) {ci p l r : Nat} {c : MClient} {a b : MBlock}
    {x y : MItem} (hc : s.clients[ci]? = some c) (ha : c.blocks[p]? = some a)
    (hb : c.blocks[p + 1]? = some b) (hsa : a.kind.slot = some l) (hsb : b.kind.slot = some r)
    (hx : coreAt s.items l = some x) (hy : coreAt s.items r = some y)
    (hlr : rightOf s.items l = some r) :
    ∃ k, (order s)[k]? = some l ∧ (order s)[k + 1]? = some r ∧ WF (mergeNode s ci p l r) ∧
      order (mergeNode s ci p l r) = delAt (order s) (k + 1) ∧
      coreAt (mergeNode s ci p l r).items l = some { x with len := x.len + y.len } ∧
      (∀ j, j ≠ l → coreAt (mergeNode s ci p l r).items j = coreAt s.items j) := by
  have hcm : c ∈ s.clients := get?_mem hc
  obtain ⟨l', x', e1, e2, e3, e4, e5, hl', _⟩ := h.block_item hcm ha
  have el : l' = l := Option.some.inj (e1.symm.trans hsa)
  rw [el] at e2 hl'
  rw [hx] at e2
  have ex : x' = x := (Option.some.inj e2).symm
  rw [ex] at e3 e4 e5
  obtain ⟨r', y', g1, g2, g3, g4, g5, hr', _⟩ := h.block_item hcm hb
  have er : r' = r := Option.some.inj (g1.symm.trans hsb)
  rw [er] at g2 hr'
  rw [hy] at g2
  have ey : y' = y := (Option.some.inj g2).symm
  rw [ey] at g3 g4 g5
  have hord := h.chain
  obtain ⟨k, hk⟩ := mem_get? hl'
  have hk1 : (order s)[k + 1]? = some r := by
    rw [← hord.right k l hk]
    exact hlr
  refine ⟨k, hk, hk1, ?_⟩
  have hlb : l < s.items.length := coreAt_lt hx
  have hyc : (itemAt s.items r).core = y := itemAt_core hy
  have hylen : (itemAt s.items r).len = y.len := by
    have e : (itemAt s.items r).core.len = y.len := congrArg MItem.len hyc
    exact e
  have htl := h.timeline c hcm
  have hab : a.clock < b.clock := htl.sorted p (p + 1) a b (by omega) ha hb
  have hEp : endAt c.blocks c.stop p = b.clock := by
    unfold endAt
    rw [hb]
  have hbE : b.clock < endAt c.blocks c.stop (p + 1) := htl.lt_end hb
  -- the arena
  have hn : (mergeNode s ci p l r).items.length = s.items.length := by
    show (setLeft _ _ (upd _ _ _)).length = _
    rw [length_setLeft, length_upd]
  have core_new : ∀ j, coreAt (mergeNode s ci p l r).items j =
      if j = l then some { x with len := x.len + y.len } else coreAt s.items j := by
    intro j
    show coreAt (setLeft l (rightOf s.items r) (upd s.items l _)) j = _
    rw [coreAt_setLeft, coreAt_upd]
    by_cases e : j = l
    · rw [ite_eq_left e, ite_eq_left e, e]
      unfold coreAt at hx
      cases hz : s.items[l]? with
      | none =>
        rw [hz] at hx
        cases hx
      | some z =>
        rw [hz] at hx
        have ez : z.core = x := Option.some.inj hx
        rw [← ez, hylen]
        rfl
    · rw [ite_eq_right e, ite_eq_right e]
  have core_l : coreAt (mergeNode s ci p l r).items l = some { x with len := x.len + y.len } := by
    rw [core_new, ite_eq_left rfl]
  have core_other : ∀ j, j ≠ l → coreAt (mergeNode s ci p l r).items j = coreAt s.items j := by
    intro j h1
    rw [core_new, ite_eq_right h1]
  have right_new : ∀ j, rightOf (mergeNode s ci p l r).items j =
      if j = l then rightOf s.items r else rightOf s.items j := by
    intro j
    show rightOf (setLeft l (rightOf s.items r) (upd s.items l _)) j = _
    rw [rightOf_setLeft, rightOf_upd]
    by_cases e : j = l
    · rw [ite_eq_left e, ite_eq_left e, e]
      obtain ⟨z, hz⟩ := get?_some hlb
      rw [hz]
      rfl
    · rw [ite_eq_right e, ite_eq_right e]
  have left_new : ∀ j, j < s.items.length → leftOf (mergeNode s ci p l r).items j =
      if rightOf s.items r = some j then some l else leftOf s.items j := by
    intro j hj
    have hkeep : leftOf (upd s.items l (fun z =>
        { z with len := z.len + (itemAt s.items r).len, right := rightOf s.items r })) j =
        leftOf s.items j := leftOf_upd_keep _ _ _ (fun _ => rfl)
    show leftOf (setLeft l (rightOf s.items r) (upd s.items l _)) j = _
    rw [leftOf_setLeft _ _ _ (by rw [length_upd]; exact hj), hkeep]
  -- the chain
  have hr2 : rightOf s.items r = (order s)[k + 1 + 1]? := hord.right (k + 1) r hk1
  have hch : Chain (mergeNode s ci p l r).items (mergeNode s ci p l r).start
      (delAt (order s) (k + 1)) := by
    refine ⟨nodup_delAt hord.nodup, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hn]
      exact hord.bound i (mem_delAt hi)
    · show s.start = _
      rw [get?_delAt_lt _ (by omega : 0 < k + 1)]
      exact hord.head
    · intro k' i hk'
      rw [right_new]
      rcases get?_delAt_cases hk' with ⟨hlt, hi⟩ | ⟨hge, hi⟩
      · by_cases e : k' = k
        · have ei : i = l := by
            rw [e, hk] at hi
            exact (Option.some.inj hi).symm
          rw [ite_eq_left ei, hr2, get?_delAt_ge _ (by omega : k + 1 ≤ k' + 1), e]
        · have ei : ¬ i = l := fun ei => e (hord.pos_unique (by rw [ei] at hi; exact hi) hk)
          rw [ite_eq_right ei, hord.right k' i hi, get?_delAt_lt _ (by omega : k' + 1 < k + 1)]
      · have ei : ¬ i = l := fun ei => by
          have := hord.pos_unique (by rw [ei] at hi; exact hi) hk
          omega
        rw [ite_eq_right ei, hord.right (k' + 1) i hi,
          get?_delAt_ge _ (by omega : k + 1 ≤ k' + 1)]
    · intro k' i hk'
      have hib : i < s.items.length := hord.bound i (mem_delAt (get?_mem hk'))
      rw [left_new i hib]
      rcases get?_delAt_cases hk' with ⟨hlt, hi⟩ | ⟨hge, hi⟩
      · have hne : ¬ rightOf s.items r = some i := by
          intro e
          rw [hr2] at e
          have := hord.pos_unique e hi
          omega
        rw [ite_eq_right hne, hord.left k' i hi, get?_delAt_lt _ (by omega : k' < k + 1)]
      · by_cases e : k' = k
        · have hq : rightOf s.items r = some i := by
            rw [hr2, ← e]
            exact hi
          rw [ite_eq_left hq, get?_delAt_lt _ (by omega : k' < k + 1), e, hk]
        · have hne : ¬ rightOf s.items r = some i := by
            intro e'
            rw [hr2] at e'
            have := hord.pos_unique e' hi
            omega
          rw [ite_eq_right hne, hord.left (k' + 1) i hi,
            get?_delAt_ge _ (by omega : k + 1 ≤ k')]
    · intro i hi
      have hi0 : (order s)[0]? = some i := by
        rw [get?_delAt_lt _ (by omega : 0 < k + 1)] at hi
        exact hi
      have hib : i < s.items.length := hord.bound i (get?_mem hi0)
      have hne : ¬ rightOf s.items r = some i := by
        intro e
        rw [hr2] at e
        have := hord.pos_unique e hi0
        omega
      rw [left_new i hib, ite_eq_right hne]
      exact hord.first i hi0
  -- the timelines
  have hcl : ∀ c', c' ∈ (mergeNode s ci p l r).clients →
      c' = c.withoutBlock (p + 1) ∨ ∃ j, j ≠ ci ∧ s.clients[j]? = some c' := by
    intro c' hc'
    rcases mem_upd hc' with ⟨a0, ha0, e⟩ | hj
    · rw [hc] at ha0
      have ea : c = a0 := Option.some.inj ha0
      rw [← ea] at e
      exact Or.inl e
    · exact Or.inr hj
  have hnew_mem : c.withoutBlock (p + 1) ∈ (mergeNode s ci p l r).clients :=
    upd_mem_self (f := fun c : MClient => c.withoutBlock (p + 1)) hc
  -- a block of another timeline, or another block of this one, is not `l` or `r`
  have hother : ∀ (j : Nat) (c' : MClient) (q : Nat) (b' : MBlock) (i : Nat) (z : MItem),
      j ≠ ci → s.clients[j]? = some c' → c'.blocks[q]? = some b' → b'.kind.slot = some i →
      coreAt s.items i = some z → z.id.client = c.client → False := by
    intro j c' q b' i z hj hc' hb' hslot hz hzc
    obtain ⟨i2, x2, f1, f2, f3, _⟩ := h.block c' q b' (get?_mem hc') hb'
    have e2 : i2 = i := Option.some.inj (f1.symm.trans hslot)
    rw [e2, hz] at f2
    have ex2 : z = x2 := Option.some.inj f2
    rw [← ex2] at f3
    have ecl : c.client = c'.client := by
      rw [← hzc, f3]
    by_cases hlt : j < ci
    · exact h.distinct j ci c' c hlt hc' hc ecl.symm
    · exact h.distinct ci j c c' (by omega) hc hc' ecl
  have hxc : x.id.client = c.client := by rw [e3]
  have hyc' : y.id.client = c.client := by rw [g3]
  -- the slot of a block of this timeline: `l` at `p` only, `r` at `p + 1` only
  have slot_l : ∀ (q : Nat) (b' : MBlock), c.blocks[q]? = some b' → b'.kind.slot = some l →
      q = p := by
    intro q b' hb' hs'
    obtain ⟨i2, x2, f1, f2, f3, _⟩ := h.block c q b' hcm hb'
    have e2 : i2 = l := Option.some.inj (f1.symm.trans hs')
    rw [e2, hx] at f2
    have ex2 : x = x2 := Option.some.inj f2
    rw [← ex2, e3] at f3
    have ek : a.clock = b'.clock := congrArg Id.clock f3
    by_cases h1 : q < p
    · have := htl.sorted q p b' a h1 hb' ha
      omega
    · by_cases h2 : p < q
      · have := htl.sorted p q a b' h2 ha hb'
        omega
      · omega
  have slot_r : ∀ (q : Nat) (b' : MBlock), c.blocks[q]? = some b' → b'.kind.slot = some r →
      q = p + 1 := by
    intro q b' hb' hs'
    obtain ⟨i2, x2, f1, f2, f3, _⟩ := h.block c q b' hcm hb'
    have e2 : i2 = r := Option.some.inj (f1.symm.trans hs')
    rw [e2, hy] at f2
    have ex2 : y = x2 := Option.some.inj f2
    rw [← ex2, g3] at f3
    have ek : b.clock = b'.clock := congrArg Id.clock f3
    by_cases h1 : q < p + 1
    · have := htl.sorted q (p + 1) b' b h1 hb' hb
      omega
    · by_cases h2 : p + 1 < q
      · have := htl.sorted (p + 1) q b b' h2 hb hb'
        omega
      · omega
  have hlr_ne : l ≠ r := by
    intro e
    rw [← e] at hk1
    have := hord.pos_unique hk hk1
    omega
  have key := WF.of_order (s := mergeNode s ci p l r) (delAt (order s) (k + 1)) hch
    (by
      intro p' q' a' b' hpq ha' hb'
      have pre : ∀ (j : Nat) (c' : MClient), (mergeNode s ci p l r).clients[j]? = some c' →
          ∃ c0, s.clients[j]? = some c0 ∧ c'.client = c0.client := by
        intro j c' hj
        rcases get?_upd_cases hj with ⟨ej, a0, ha0, e⟩ | ⟨_, hj'⟩
        · exact ⟨a0, by rw [ej]; exact ha0, by rw [e]; rfl⟩
        · exact ⟨c', hj', rfl⟩
      obtain ⟨a0, ha0, ea⟩ := pre p' a' ha'
      obtain ⟨b0, hb0, eb⟩ := pre q' b' hb'
      rw [ea, eb]
      exact h.sorted p' q' a0 b0 hpq ha0 hb0)
    (by
      intro c' hc'
      rcases hcl c' hc' with e | ⟨j, _, hj⟩
      · rw [e]
        exact htl.remove (p + 1)
      · exact h.timeline c' (get?_mem hj))
    (by
      intro c' q b' hc' hb'
      rcases hcl c' hc' with e | ⟨j, hj, hcj⟩
      · rw [e] at hb' ⊢
        rcases get?_delAt_cases hb' with ⟨hq, hb0⟩ | ⟨hq, hb0⟩
        · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c q b' hcm hb0
          by_cases hqp : q = p
          · rw [hqp, ha] at hb0
            have ebb : a = b' := Option.some.inj hb0
            rw [← ebb, hqp]
            refine ⟨l, { x with len := x.len + y.len }, hsa, core_l, e3, ?_, e5⟩
            show x.len + y.len = endAt (delAt c.blocks (p + 1)) c.stop p - a.clock
            rw [endAt_delAt_ge (Nat.le_refl (p + 1))]
            rw [hEp] at e4
            omega
          · have hne : i2 ≠ l := by
              intro e2
              exact hqp (slot_l q b' hb0 (by rw [f1, e2]))
            refine ⟨i2, x2, f1, ?_, f3, ?_, f5⟩
            · rw [core_other i2 hne]
              exact f2
            · show x2.len = endAt (delAt c.blocks (p + 1)) c.stop q - b'.clock
              rw [endAt_delAt_lt (by omega : q + 1 < p + 1)]
              exact f4
        · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c (q + 1) b' hcm hb0
          have hne : i2 ≠ l := by
            intro e2
            have := slot_l (q + 1) b' hb0 (by rw [f1, e2])
            omega
          refine ⟨i2, x2, f1, ?_, f3, ?_, f5⟩
          · rw [core_other i2 hne]
            exact f2
          · show x2.len = endAt (delAt c.blocks (p + 1)) c.stop q - b'.clock
            rw [endAt_delAt_ge (by omega : p + 1 ≤ q + 1)]
            exact f4
      · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c' q b' (get?_mem hcj) hb'
        have hne : i2 ≠ l := fun e2 =>
          hother j c' q b' l x hj hcj hb' (by rw [f1, e2]) hx hxc
        exact ⟨i2, x2, f1, by
          rw [core_other i2 hne]
          exact f2, f3, f4, f5⟩)
    (by
      intro i0
      constructor
      · intro hi0
        have hold : i0 ∈ order s := mem_delAt hi0
        have hir : i0 ≠ r := fun e => not_mem_delAt_self hord.nodup hk1 (by rw [← e]; exact hi0)
        obtain ⟨c0, q, b0, hc0, hb0, hs0⟩ := (h.live i0).mp hold
        obtain ⟨j, hj⟩ := mem_get? hc0
        by_cases ej : j = ci
        · rw [ej, hc] at hj
          have ec : c = c0 := Option.some.inj hj
          rw [← ec] at hb0
          have hqne : q ≠ p + 1 := by
            intro e
            rw [e, hb] at hb0
            rw [← Option.some.inj hb0, hsb] at hs0
            exact hir (Option.some.inj hs0).symm
          by_cases hq : q < p + 1
          · exact ⟨_, q, b0, hnew_mem, by
              show (delAt c.blocks (p + 1))[q]? = some b0
              rw [get?_delAt_lt _ hq]
              exact hb0, hs0⟩
          · obtain ⟨q', eq⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
            rw [eq] at hb0
            exact ⟨_, q', b0, hnew_mem, by
              show (delAt c.blocks (p + 1))[q']? = some b0
              rw [get?_delAt_ge _ (by omega : p + 1 ≤ q')]
              exact hb0, hs0⟩
        · exact ⟨c0, q, b0, upd_mem_other ej hj, hb0, hs0⟩
      · rintro ⟨c', q, b', hc', hb', hs'⟩
        rcases hcl c' hc' with e | ⟨j, hj, hcj⟩
        · rw [e] at hb'
          rcases get?_delAt_cases hb' with ⟨hq, hb0⟩ | ⟨hq, hb0⟩
          · refine mem_delAt_of_ne ((h.live i0).mpr ⟨c, q, b', hcm, hb0, hs'⟩) hk1 ?_
            intro e'
            have := slot_r q b' hb0 (by rw [hs', e'])
            omega
          · refine mem_delAt_of_ne ((h.live i0).mpr ⟨c, q + 1, b', hcm, hb0, hs'⟩) hk1 ?_
            intro e'
            have := slot_r (q + 1) b' hb0 (by rw [hs', e'])
            omega
        · refine mem_delAt_of_ne ((h.live i0).mpr ⟨c', q, b', get?_mem hcj, hb', hs'⟩) hk1 ?_
          intro e'
          exact hother j c' q b' r y hj hcj hb' (by rw [hs', e']) hy hyc')
    (by
      intro i0 z hi0 hz hgc
      have hold : i0 ∈ order s := mem_delAt hi0
      by_cases e : i0 = l
      · rw [e, core_l] at hz
        rw [← Option.some.inj hz] at hgc ⊢
        exact h.gc l x hl' hx hgc
      · rw [core_other i0 e] at hz
        exact h.gc i0 z hold hz hgc)
  exact ⟨key.1, key.2, core_l, core_other⟩

/-! ### A merge is `YoctoSpec.mergeAt` -/

theorem unitChars_append (f : Id → Char) (c : Nat) :
    ∀ (n m k : Nat), unitChars f c k n ++ unitChars f c (k + n) m = unitChars f c k (n + m) := by
  intro n
  induction n with
  | zero =>
    intro m k
    show unitChars f c (k + 0) m = unitChars f c k (0 + m)
    rw [Nat.add_zero, Nat.zero_add]
  | succ n ih =>
    intro m k
    have e1 : k + (n + 1) = k + 1 + n := by omega
    have e2 : n + 1 + m = (n + m) + 1 := by omega
    rw [e1, e2]
    show f ⟨c, k⟩ :: (unitChars f c (k + 1) n ++ unitChars f c (k + 1 + n) m) =
      f ⟨c, k⟩ :: unitChars f c (k + 1) (n + m)
    rw [ih m (k + 1)]

/-- The block of two merged items is `Node::merge` of their blocks. -/
theorem blockOf_merge (f : Id → Char) (x y : MItem) (hgc : x.gc = y.gc)
    (hid : y.id = ⟨x.id.client, x.id.clock + x.len⟩) :
    mergeBlocks (blockOf f x) (blockOf f y) = blockOf f { x with len := x.len + y.len } := by
  cases hg : x.gc with
  | true =>
    have hg' : y.gc = true := by
      rw [← hgc]
      exact hg
    simp [mergeBlocks, blockOf, hg, hg', Content.append]
  | false =>
    have hg' : y.gc = false := by
      rw [← hgc]
      exact hg
    simp [mergeBlocks, blockOf, hg, hg', Content.append, hid, unitChars_append]

/-- The blocks of two items `merge_adjacent` merges can merge. -/
theorem canMerge_blockOf (f : Id → Char) (x y : MItem) (hpos : 0 < x.len)
    (hid : y.id = ⟨x.id.client, x.id.clock + x.len⟩)
    (hol : y.originL = some ⟨x.id.client, x.id.clock + x.len - 1⟩)
    (hor : x.originR = y.originR) (hdel : x.deleted = y.deleted) (hgc : x.gc = y.gc) :
    canMerge (blockOf f x) (blockOf f y) = true := by
  unfold canMerge
  rw [Bool.and_eq_true]
  constructor
  · apply decide_eq_true
    unfold Block.lastId
    rw [blockOf_len]
    refine ⟨?_, ?_, hpos, hol, hor, hdel⟩
    · show x.id.client = y.id.client
      rw [hid]
    · show x.id.clock + x.len = y.id.clock
      rw [hid]
  · cases hg : x.gc with
    | true =>
      have hg' : y.gc = true := by
        rw [← hgc]
        exact hg
      simp [blockOf, hg, hg', Content.sameKind]
    | false =>
      have hg' : y.gc = false := by
        rw [← hgc]
        exact hg
      simp [blockOf, hg, hg', Content.sameKind]

/-- `mergeAt` where the two blocks can merge: the second one goes, the first
one is the merged block. -/
theorem mergeAt_eq {A B : Block} (hm : canMerge A B = true) :
    ∀ (k : Nat) (bs : List Block), bs[k]? = some A → bs[k + 1]? = some B →
      mergeAt k bs = upd (delAt bs (k + 1)) k (fun _ => mergeBlocks A B)
  | _, [], hA, _ => by simp at hA
  | _, [_], _, hB => by simp at hB
  | 0, a :: b :: t, hA, hB => by
    have ea : a = A := by simpa using hA
    have eb : b = B := by simpa using hB
    rw [mergeAt, ea, eb, ite_eq_left hm]
    rfl
  | n + 1, a :: b :: t, hA, hB => by
    have hA' : (b :: t)[n]? = some A := by simpa using hA
    have hB' : (b :: t)[n + 1]? = some B := by simpa using hB
    rw [mergeAt, mergeAt_eq hm n (b :: t) hA' hB']
    rfl

/-- `merge_adjacent` on two items that continue each other is
`YoctoSpec.mergeAt` at the place of the first, and a merge that happens: the
blocks of the two items are neighbours of the sequence at `k` and `k + 1`,
they can merge, and the sequence is one block shorter. (`mergeAt` returns
its list where there are no two blocks or they cannot merge, so the equation
alone would not say that anything was merged.) -/
theorem blocks_mergeNode {s : MStore} (h : WF s) {ci p l r : Nat} {c : MClient}
    {a b : MBlock} {x y : MItem} (hc : s.clients[ci]? = some c) (ha : c.blocks[p]? = some a)
    (hb : c.blocks[p + 1]? = some b) (hsa : a.kind.slot = some l) (hsb : b.kind.slot = some r)
    (hx : coreAt s.items l = some x) (hy : coreAt s.items r = some y)
    (hlr : rightOf s.items l = some r)
    (hol : y.originL = some ⟨x.id.client, x.id.clock + x.len - 1⟩)
    (hor : x.originR = y.originR) (hdel : a.kind.dead = b.kind.dead) (hgc : x.gc = y.gc) :
    ∃ k, (order s)[k]? = some l ∧
      ∀ f : Id → Char,
        (blocks f s)[k]? = some (blockOf f x) ∧ (blocks f s)[k + 1]? = some (blockOf f y) ∧
        canMerge (blockOf f x) (blockOf f y) = true ∧
        blocks f (mergeNode s ci p l r) = mergeAt k (blocks f s) ∧
        (blocks f (mergeNode s ci p l r)).length + 1 = (blocks f s).length := by
  obtain ⟨k, hk, hk1, _, hord, core_l, core_other⟩ :=
    mergeNode_spec h hc ha hb hsa hsb hx hy hlr
  refine ⟨k, hk, fun f => ?_⟩
  have hcm : c ∈ s.clients := get?_mem hc
  obtain ⟨l', x', e1, e2, e3, e4, e5, _, hpos⟩ := h.block_item hcm ha
  have el : l' = l := Option.some.inj (e1.symm.trans hsa)
  rw [el, hx] at e2
  have ex : x' = x := (Option.some.inj e2).symm
  rw [ex] at e3 e4 e5 hpos
  obtain ⟨r', y', g1, g2, g3, _, g5, _, _⟩ := h.block_item hcm hb
  have er : r' = r := Option.some.inj (g1.symm.trans hsb)
  rw [er, hy] at g2
  have ey : y' = y := (Option.some.inj g2).symm
  rw [ey] at g3 g5
  have htl := h.timeline c hcm
  have hab : a.clock < b.clock := htl.sorted p (p + 1) a b (by omega) ha hb
  have hEp : endAt c.blocks c.stop p = b.clock := by
    unfold endAt
    rw [hb]
  have hid : y.id = ⟨x.id.client, x.id.clock + x.len⟩ := by
    rw [g3, e3, e4, hEp]
    show (⟨c.client, b.clock⟩ : Id) = ⟨c.client, a.clock + (b.clock - a.clock)⟩
    have e : a.clock + (b.clock - a.clock) = b.clock := by omega
    rw [e]
  have hdel' : x.deleted = y.deleted := by rw [e5, g5, hdel]
  have hm := canMerge_blockOf f x y hpos hid hol hor hdel' hgc
  have hA : (blocks f s)[k]? = some (blockOf f x) := by
    unfold blocks
    rw [get?_map, hk]
    show some (blockAt f s.items l) = _
    rw [blockAt_of_core hx]
  have hB : (blocks f s)[k + 1]? = some (blockOf f y) := by
    unfold blocks
    rw [get?_map, hk1]
    show some (blockAt f s.items r) = _
    rw [blockAt_of_core hy]
  have hlen : (blocks f (mergeNode s ci p l r)).length + 1 = (blocks f s).length := by
    simp only [blocks, hord, List.length_map]
    exact length_delAt (order s) (get?_lt hk1)
  refine ⟨hA, hB, hm, ?_, hlen⟩
  rw [mergeAt_eq hm k (blocks f s) hA hB]
  unfold blocks
  rw [hord, ← map_delAt]
  have hk' : (delAt (order s) (k + 1))[k]? = some l := by
    rw [get?_delAt_lt _ (by omega : k < k + 1)]
    exact hk
  refine map_eq_upd_map (nodup_delAt h.chain.nodup) hk' _ _ _ ?_ ?_
  · rw [blockAt_of_core core_l, blockOf_merge f x y hgc hid]
  · intro j _ hj
    unfold blockAt itemAt
    have e := core_other j hj
    unfold coreAt at e
    cases h1 : (mergeNode s ci p l r).items[j]? with
    | none =>
      rw [h1] at e
      cases h2 : s.items[j]? with
      | none => rfl
      | some z =>
        rw [h2] at e
        cases e
    | some z1 =>
      rw [h1] at e
      cases h2 : s.items[j]? with
      | none =>
        rw [h2] at e
        cases e
      | some z2 =>
        rw [h2] at e
        have ez : z1.core = z2.core := Option.some.inj e
        show blockOf f z1 = blockOf f z2
        rw [← blockOf_core f z1, ← blockOf_core f z2, ez]

/-- A merge stands for the same document. -/
theorem toDoc_mergeNode {f : Id → Char} {s : MStore} (h : WF s) {ci p l r : Nat} {c : MClient}
    {a b : MBlock} {x y : MItem} (hc : s.clients[ci]? = some c) (ha : c.blocks[p]? = some a)
    (hb : c.blocks[p + 1]? = some b) (hsa : a.kind.slot = some l) (hsb : b.kind.slot = some r)
    (hx : coreAt s.items l = some x) (hy : coreAt s.items r = some y)
    (hlr : rightOf s.items l = some r)
    (hol : y.originL = some ⟨x.id.client, x.id.clock + x.len - 1⟩)
    (hor : x.originR = y.originR) (hdel : a.kind.dead = b.kind.dead) (hgc : x.gc = y.gc) :
    toDoc (blocks f (mergeNode s ci p l r)) = toDoc (blocks f s) := by
  obtain ⟨k, _, e⟩ := blocks_mergeNode h hc ha hb hsa hsb hx hy hlr hol hor hdel hgc
  rw [(e f).2.2.2.1]
  exact toDoc_mergeAt k _

/-! ## The visible items -/

/-- What `visible_ids` answers for an item: nothing when it is deleted, its
first id and its length otherwise. -/
def visOf (x : MItem) : Option (Id × Nat) := if x.deleted then none else some (x.id, x.len)

/-- `visible_ids`: the first id and the length of every item of the sequence
that is not deleted. -/
def visM (s : MStore) : List (Id × Nat) := (order s).filterMap (fun i => visOf (itemAt s.items i))

/-- The same, read off the block sequence. -/
theorem visM_blocks (f : Id → Char) (s : MStore) :
    visM s = ((blocks f s).filter (fun B => !B.deleted)).map (fun B => (B.id, B.len)) := by
  unfold visM blocks
  generalize order s = o
  induction o with
  | nil => rfl
  | cons i t ih =>
    rw [List.filterMap_cons, List.map_cons, List.filter_cons, ih]
    have hlen : (blockAt f s.items i).len = (itemAt s.items i).len := blockOf_len f _
    cases hd : (itemAt s.items i).deleted with
    | true =>
      have e1 : visOf (itemAt s.items i) = none := by
        unfold visOf
        rw [hd]
        rfl
      have e2 : (!(blockAt f s.items i).deleted) = false := by
        show (!(itemAt s.items i).deleted) = false
        rw [hd]
        rfl
      rw [e1, e2]
      rfl
    | false =>
      have e1 : visOf (itemAt s.items i) = some ((itemAt s.items i).id, (itemAt s.items i).len) := by
        unfold visOf
        rw [hd]
        rfl
      have e2 : (!(blockAt f s.items i).deleted) = true := by
        show (!(itemAt s.items i).deleted) = true
        rw [hd]
        rfl
      rw [e1, e2, ← hlen]
      rfl

/-- The ids of `n` clocks of client `c` from `k` on. -/
def idRun (c : Nat) : Nat → Nat → List Id
  | _, 0 => []
  | k, n + 1 => ⟨c, k⟩ :: idRun c (k + 1) n

/-- The clocks the pairs of `visible_ids` stand for, in order. -/
def expandIds (v : List (Id × Nat)) : List Id := v.flatMap (fun e => idRun e.1.client e.1.clock e.2)

theorem map_id_unitsFrom (c : Nat) (r : Option Id) :
    ∀ (n k : Nat) (l : Option Id), (unitsFrom c r k l n).map Item.id = idRun c k n := by
  intro n
  induction n with
  | zero =>
    intro k l
    rfl
  | succ n ih =>
    intro k l
    show (⟨c, k⟩ : Id) :: (unitsFrom c r (k + 1) (some ⟨c, k⟩) n).map Item.id =
      ⟨c, k⟩ :: idRun c (k + 1) n
    rw [ih]

theorem map_id_units (B : Block) : B.units.map Item.id = idRun B.id.client B.id.clock B.len :=
  map_id_unitsFrom _ _ _ _ _

/-- A clock of a block of the sequence is deleted exactly when the block is. -/
theorem deleted_iff_block {f : Id → Char} {s : MStore} (h : WF s) {B : Block}
    (hB : B ∈ blocks f s) {u : Item} (hu : u ∈ B.units) :
    u.id ∈ deletedSet (blocks f s) ↔ B.deleted = true := by
  have hz : u.id ∈ B.units.map Item.id := List.mem_map.mpr ⟨u, hu, rfl⟩
  obtain ⟨c, p, b, hat, hdead⟩ := at_of_block h hB hz
  rw [dead_iff h]
  constructor
  · rintro ⟨c', p', b', hat', hd'⟩
    obtain ⟨_, _, eb⟩ := At.unique h hat hat'
    rw [← hdead, eb]
    exact hd'
  · intro hd
    exact ⟨c, p, b, hat, by rw [hdead]; exact hd⟩

/-- **The pairs of `visible_ids` are the visible ids of the document**, clock
by clock and in order. -/
theorem expand_visM {f : Id → Char} {s : MStore} (h : WF s) :
    expandIds (visM s) = (toDoc (blocks f s)).visible := by
  rw [visM_blocks f s]
  show _ = ((flatten (blocks f s)).filter
    (fun a => decide (¬ a.id ∈ deletedSet (blocks f s)))).map Item.id
  have key : ∀ t : List Block, (∀ B, B ∈ t → B ∈ blocks f s) →
      expandIds ((t.filter (fun B => !B.deleted)).map (fun B => (B.id, B.len))) =
        ((flatten t).filter (fun a => decide (¬ a.id ∈ deletedSet (blocks f s)))).map
          Item.id := by
    intro t
    induction t with
    | nil => exact fun _ => rfl
    | cons B t ih =>
      intro ht
      have hB : B ∈ blocks f s := ht B (List.mem_cons_self ..)
      rw [flatten_cons, List.filter_append, List.map_append,
        ← ih (fun x hx => ht x (List.mem_cons_of_mem _ hx)), List.filter_cons]
      by_cases hd : B.deleted = true
      · have e : B.units.filter (fun a => decide (¬ a.id ∈ deletedSet (blocks f s))) = [] :=
          filter_all_false (fun u hu =>
            decide_eq_false (fun hnot => hnot ((deleted_iff_block h hB hu).mpr hd)))
        have e2 : (!B.deleted) = false := by
          rw [hd]
          rfl
        rw [e, e2]
        rfl
      · have hd' : B.deleted = false := by
          cases hbd : B.deleted with
          | false => rfl
          | true => exact absurd hbd hd
        have e : B.units.filter (fun a => decide (¬ a.id ∈ deletedSet (blocks f s))) = B.units :=
          filter_all_true (fun u hu =>
            decide_eq_true (fun hin => hd ((deleted_iff_block h hB hu).mp hin)))
        have e2 : (!B.deleted) = true := by
          rw [hd']
          rfl
        rw [e, e2, map_id_units]
        rfl
  exact key (blocks f s) (fun _ hB => hB)

end YoctoCore.Properties.YataModel
