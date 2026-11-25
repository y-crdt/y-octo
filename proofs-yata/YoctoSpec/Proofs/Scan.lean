/-
Correctness of the conflict scan (`find_conflict_left`).

The scan returns the item after which the new item is linked. `scan_spec`
shows that, in a legal sequence, every item on the left of that position and
every item on its right is ordered with the new item by the YATA rule.
-/
import YoctoSpec.Proofs.Legal

namespace YoctoSpec

/-- `o` may stand before the new item `i` once `i` is inserted after position `k`. -/
def GoodA (s : List Item) (i : Item) (k : Nat) (o : Item) : Prop :=
  ix s o.id ≤ ixL s i.left ∨ ixR s o.right ≤ k ∨ ixL s i.left < ixL s o.left ∨
    (o.left = i.left ∧ o.id.client < i.id.client)

/-- The new item `i` may stand before `o` once `i` is inserted after position `k`. -/
def GoodB (s : List Item) (i : Item) (k : Nat) (o : Item) : Prop :=
  k < ixL s o.left ∨ ixR s i.right ≤ ix s o.id ∨ ixL s o.left < ixL s i.left ∨
    (i.left = o.left ∧ i.id.client < o.id.client)

/-- Result of the scan: `i` is inserted after position `k`. -/
structure ScanPost (s : List Item) (i : Item) (k : Nat) : Prop where
  lo : ixL s i.left ≤ k
  hi : k < ixR s i.right
  goodA : ∀ o, o ∈ s → ix s o.id ≤ k → GoodA s i k o
  goodB : ∀ o, o ∈ s → k < ix s o.id → GoodB s i k o

/-- A scanned item not yet known to be on the left of `i`: a sibling with a
larger client, or an item whose left origin is itself pending. -/
def Pend (s : List Item) (i : Item) (k : Nat) (o : Item) : Prop :=
  (o.left = i.left ∧ i.id.client < o.id.client) ∨ k < ixL s o.left

/-- Loop invariant after the candidates up to position `j` were scanned. -/
structure ScanInv (s : List Item) (i : Item) (j : Nat) (left : Option Id)
    (before conflicting : List Id) : Prop where
  l_le : ixL s i.left ≤ ixL s left
  le_j : ixL s left ≤ j
  j_lt : j < ixR s i.right
  /-- `before_origin` holds exactly the scanned candidates -/
  before_iff : ∀ x, x ∈ before ↔ ixL s i.left < ix s x ∧ ix s x ≤ j
  /-- `conflicting` holds exactly the candidates scanned after `left` -/
  conf_iff : ∀ x, x ∈ conflicting ↔ ixL s left < ix s x ∧ ix s x ≤ j
  goodA : ∀ o, o ∈ s → ix s o.id ≤ ixL s left → GoodA s i (ixL s left) o
  pend : ∀ o, o ∈ s → ixL s left < ix s o.id → ix s o.id ≤ j → Pend s i (ixL s left) o

theorem GoodA.mono {s : List Item} {i o : Item} {k k' : Nat} (h : GoodA s i k o) (hk : k ≤ k') :
    GoodA s i k' o := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem mem_cons_range {s : List Item} {c : Item} {l : List Id} {lo j : Nat} (hc : c ∈ s)
    (hcj : ix s c.id = j + 1) (hlo : lo ≤ j) (hl : ∀ x, x ∈ l ↔ lo < ix s x ∧ ix s x ≤ j) :
    ∀ x, x ∈ c.id :: l ↔ lo < ix s x ∧ ix s x ≤ j + 1 := by
  intro x
  rw [List.mem_cons, hl]
  constructor
  · rintro (e | ⟨h₁, h₂⟩)
    · rw [e, hcj]
      exact ⟨by omega, by omega⟩
    · exact ⟨h₁, by omega⟩
  · rintro ⟨h₁, h₂⟩
    by_cases e : ix s x = j + 1
    · left
      exact (ix_inj (by rw [hcj, e]) (ix_mem hc)).symm
    · right
      exact ⟨h₁, by omega⟩

theorem ScanInv.post {s : List Item} {i : Item} {j : Nat} {left : Option Id}
    {before conflicting : List Id} (h : ScanInv s i j left before conflicting)
    (hB : ∀ o, o ∈ s → j < ix s o.id → GoodB s i (ixL s left) o) :
    ScanPost s i (ixL s left) where
  lo := h.l_le
  hi := by
    have := h.le_j
    have := h.j_lt
    omega
  goodA := h.goodA
  goodB := by
    intro o ho hk
    by_cases hj : ix s o.id ≤ j
    · rcases h.pend o ho hk hj with ⟨e, hc⟩ | hp
      · exact Or.inr (Or.inr (Or.inr ⟨e.symm, hc⟩))
      · exact Or.inl hp
    · exact hB o ho (by omega)

theorem ScanInv.skip {s : List Item} {i : Item} {j : Nat} {left : Option Id}
    {before conflicting : List Id} (hn : NodupIds s) (h : ScanInv s i j left before conflicting)
    {c : Item} (hc : c ∈ s) (hcj : ix s c.id = j + 1) (hr : j + 1 < ixR s i.right)
    (hp : Pend s i (ixL s left) c) :
    ScanInv s i (j + 1) left (c.id :: before) (c.id :: conflicting) where
  l_le := h.l_le
  le_j := by
    have := h.le_j
    omega
  j_lt := hr
  before_iff := mem_cons_range hc hcj (by have := h.l_le; have := h.le_j; omega) h.before_iff
  conf_iff := mem_cons_range hc hcj h.le_j h.conf_iff
  goodA := h.goodA
  pend := by
    intro o ho h₁ h₂
    by_cases e : ix s o.id = j + 1
    · have hoc : o = c := hn.eq_of_ix ho hc (by rw [e, hcj])
      rw [hoc]
      exact hp
    · exact h.pend o ho h₁ (by omega)

theorem ScanInv.commit {s : List Item} {i : Item} {j : Nat} {left : Option Id}
    {before conflicting : List Id} (h : ScanInv s i j left before conflicting)
    {c : Item} (hc : c ∈ s) (hcj : ix s c.id = j + 1) (hr : j + 1 < ixR s i.right)
    (hA : ∀ o, o ∈ s → ixL s left < ix s o.id → ix s o.id ≤ j + 1 → GoodA s i (j + 1) o) :
    ScanInv s i (j + 1) (some c.id) (c.id :: before) [] where
  l_le := by
    rw [ixL_some, hcj]
    have := h.l_le
    have := h.le_j
    omega
  le_j := by
    rw [ixL_some, hcj]
    omega
  j_lt := hr
  before_iff := mem_cons_range hc hcj (by have := h.l_le; have := h.le_j; omega) h.before_iff
  conf_iff := by
    intro x
    rw [ixL_some, hcj]
    constructor
    · intro h'
      cases h'
    · rintro ⟨h₁, h₂⟩
      omega
  goodA := by
    intro o ho hk
    rw [ixL_some, hcj] at hk ⊢
    by_cases hl : ix s o.id ≤ ixL s left
    · exact (h.goodA o ho hl).mono (by have := h.le_j; omega)
    · exact hA o ho (by omega) hk
  pend := by
    intro o ho h₁ h₂
    rw [ixL_some, hcj] at h₁
    omega

theorem owner_of_present {s : List Item} {x : Id} (h : ix s x ≤ s.length) :
    owner s x = some x := by
  unfold owner
  rw [ite_eq_left]
  obtain ⟨a, ha, e⟩ := ix_le_length_iff.mp h
  exact List.mem_map.mpr ⟨a, ha, e⟩

/-- The scan started in a state satisfying the loop invariant ends at a correct
insertion position. -/
theorem scan_spec {s : List Item} {i : Item} (hs : Legal s) (hi : CanIntegrate s i) :
    ∀ (rest pre : List Item) (left : Option Id) (before conflicting : List Id),
      s = pre ++ rest → ScanInv s i pre.length left before conflicting →
      ScanPost s i (ixL s (findConflictLeft i i.right (owner s) rest left before conflicting)) := by
  intro rest
  induction rest with
  | nil =>
    intro pre left before conflicting hsp hinv
    rw [findConflictLeft]
    apply hinv.post
    intro o ho hj
    have h₁ := ix_mem ho
    have h₂ : s.length = pre.length := by rw [hsp]; simp
    omega
  | cons c rest ih =>
    intro pre left before conflicting hsp hinv
    have hc : c ∈ s := by rw [hsp]; simp
    have hcj : ix s c.id = pre.length + 1 := by
      have hn := hs.nodup
      rw [hsp] at hn ⊢
      exact hn.ix_mid
    have hlen : (pre ++ [c]).length = pre.length + 1 := by simp
    have hsp' : s = (pre ++ [c]) ++ rest := by rw [hsp]; simp
    have hcn := ix_mem hc
    have hl1 := hinv.l_le
    have hl2 := hinv.le_j
    have hl3 := hinv.j_lt
    rw [findConflictLeft]
    by_cases hR : i.right = some c.id
    · -- the scan reached the right origin
      rw [ite_eq_left hR]
      apply hinv.post
      intro o ho hj
      refine Or.inr (Or.inl ?_)
      rw [hR, ixR_some, hcj]
      omega
    · rw [ite_eq_right hR]
      have hr : pre.length + 1 < ixR s i.right := by
        cases hir : i.right with
        | none =>
          rw [ixR_none]
          omega
        | some y =>
          rw [ixR_some]
          rw [hir, ixR_some] at hl3
          have hne : ix s y ≠ ix s c.id := by
            intro e
            have hcy : c.id = y := ix_inj e.symm hcn
            exact hR (by rw [hir, hcy])
          omega
      have hcl : c.id.client ≠ i.id.client := by
        intro e
        rcases hi.client c hc e with h' | h' <;> omega
      -- the candidate itself, as an item of `s` at position `pre.length + 1`
      have isC : ∀ o, o ∈ s → ix s o.id = pre.length + 1 → o = c := by
        intro o ho e
        exact hs.nodup.eq_of_ix ho hc (by rw [e, hcj])
      by_cases hL : i.left = c.left
      · rw [ite_eq_left hL]
        by_cases hcc : c.id.client < i.id.client
        · -- same left origin, smaller client: `c` stays on the left
          rw [ite_eq_left hcc]
          apply ih (pre ++ [c]) _ _ _ hsp'
          rw [hlen]
          apply hinv.commit hc hcj hr
          intro o ho h₁ h₂
          by_cases e : ix s o.id = pre.length + 1
          · rw [isC o ho e]
            exact Or.inr (Or.inr (Or.inr ⟨hL.symm, hcc⟩))
          · rcases hinv.pend o ho h₁ (by omega) with ⟨e₁, e₂⟩ | hp
            · rcases hs.rule o ho c hc (by omega) with r₁ | r₂ | r₃ | ⟨_, r₄⟩
              · rw [← hL] at r₁
                omega
              · exact Or.inr (Or.inl (by omega))
              · rw [e₁, hL] at r₃
                omega
              · omega
            · exact Or.inr (Or.inr (Or.inl (by omega)))
        · rw [ite_eq_right hcc]
          by_cases hRR : i.right = c.right
          · -- same origins, larger client: the scan stops before `c`
            rw [ite_eq_left hRR]
            apply hinv.post
            intro o ho hj
            by_cases e : ix s o.id = pre.length + 1
            · rw [isC o ho e]
              exact Or.inr (Or.inr (Or.inr ⟨hL, by omega⟩))
            · by_cases hro : ixR s i.right ≤ ix s o.id
              · exact Or.inr (Or.inl hro)
              · rcases hs.noCross c hc o ho (by omega) with n₁ | n₂
                · by_cases e' : ixL s o.left = ixL s i.left
                  · have hol : o.left = i.left := ixL_inj (hs.left_present ho) e'
                    rcases hs.rule c hc o ho (by omega) with r₁ | r₂ | r₃ | ⟨_, r₄⟩
                    · rw [hol] at r₁
                      omega
                    · rw [← hRR] at r₂
                      omega
                    · rw [hol, hL] at r₃
                      omega
                    · exact Or.inr (Or.inr (Or.inr ⟨hol.symm, by omega⟩))
                  · rw [← hL] at n₁
                    exact Or.inr (Or.inr (Or.inl (by omega)))
                · exact Or.inl (by omega)
          · -- same left origin, larger client, other right origin: pending
            rw [ite_eq_right hRR]
            apply ih (pre ++ [c]) _ _ _ hsp'
            rw [hlen]
            exact hinv.skip hs.nodup hc hcj hr (Or.inl ⟨hL.symm, by omega⟩)
      · rw [ite_eq_right hL]
        -- a candidate whose left origin is before `i.left` ends the scan
        have stop : ixL s c.left < ixL s i.left → ScanPost s i (ixL s left) := by
          intro hlt
          apply hinv.post
          intro o ho hj
          by_cases e : ix s o.id = pre.length + 1
          · rw [isC o ho e]
            exact Or.inr (Or.inr (Or.inl hlt))
          · rcases hs.noCross c hc o ho (by omega) with n₁ | n₂
            · exact Or.inr (Or.inr (Or.inl (by omega)))
            · exact Or.inl (by omega)
        split
        next hcn' =>
          apply stop
          rw [hcn', ixL_none]
          cases hil : i.left with
          | none => exact absurd (show i.left = c.left by rw [hil, hcn']) hL
          | some x =>
            rw [ixL_some]
            exact ix_pos s x
        next cl hcl' =>
          have hclp : ix s cl ≤ s.length := hs.left_present hc cl hcl'
          have hown := owner_of_present hclp
          have hcl_lt : ix s cl < pre.length + 1 := by
            have := hs.left_lt c hc
            rw [hcl', ixL_some, hcj] at this
            exact this
          have hcl_ne : ix s cl ≠ ixL s i.left := by
            intro e
            have hil : i.left = some cl := ixL_eq_ix (present_some hclp) e.symm
            exact hL (by rw [hil, hcl'])
          have hcleft : ixL s c.left = ix s cl := by rw [hcl', ixL_some]
          split
          next hown' =>
            rw [hown] at hown'
            cases hown'
          next o' hown' =>
            have ho' : cl = o' := by
              rw [hown] at hown'
              exact Option.some.inj hown'
            rw [ho'] at hclp hcl_lt hcl_ne hcleft
            by_cases hb : o' ∈ c.id :: before
            · rw [ite_eq_left hb]
              have hrange : ixL s i.left < ix s o' := by
                rcases List.mem_cons.mp hb with e | hb'
                · rw [e, hcj] at hcl_lt
                  omega
                · exact ((hinv.before_iff o').mp hb').1
              by_cases hcf : o' ∈ c.id :: conflicting
              · -- its left origin is pending: pending as well
                rw [ite_eq_left hcf]
                have hpend : ixL s left < ix s o' := by
                  rcases List.mem_cons.mp hcf with e | hcf'
                  · rw [e, hcj] at hcl_lt
                    omega
                  · exact ((hinv.conf_iff o').mp hcf').1
                apply ih (pre ++ [c]) _ _ _ hsp'
                rw [hlen]
                exact hinv.skip hs.nodup hc hcj hr (Or.inr (by rw [hcleft]; exact hpend))
              · -- its left origin is on the left already: so is `c`
                rw [ite_eq_right hcf]
                have hle : ix s o' ≤ ixL s left := by
                  by_cases h' : ix s o' ≤ ixL s left
                  · exact h'
                  · exfalso
                    apply hcf
                    exact List.mem_cons_of_mem _
                      ((hinv.conf_iff o').mpr ⟨by omega, by omega⟩)
                apply ih (pre ++ [c]) _ _ _ hsp'
                rw [hlen]
                apply hinv.commit hc hcj hr
                intro o ho h₁ h₂
                by_cases e : ix s o.id = pre.length + 1
                · rw [isC o ho e]
                  refine Or.inr (Or.inr (Or.inl ?_))
                  rw [hcleft]
                  exact hrange
                · rcases hinv.pend o ho h₁ (by omega) with ⟨e₁, _⟩ | hp
                  · exfalso
                    rcases hs.noCross o ho c hc (by omega) with n₁ | n₂
                    · rw [hcleft, e₁] at n₁
                      omega
                    · rw [hcleft] at n₂
                      omega
                  · exact Or.inr (Or.inr (Or.inl (by omega)))
            · rw [ite_eq_right hb]
              apply stop
              rw [hcleft]
              have hnb : ¬ ixL s i.left < ix s o' := by
                intro h'
                exact hb (List.mem_cons_of_mem _ ((hinv.before_iff o').mpr ⟨h', by omega⟩))
              omega

/-- The scan `integrate` runs ends at a correct insertion position. -/
theorem scan_integrate {s : List Item} {i : Item} (hs : Legal s) (hi : CanIntegrate s i) :
    ScanPost s i
      (ixL s (findConflictLeft i i.right (owner s) (after i.left s) i.left [] [])) := by
  have hl : ixL s i.left ≤ s.length := hi.left_mem.ixL_le
  have hlen : (s.take (ixL s i.left)).length = ixL s i.left := by
    rw [List.length_take]
    omega
  apply scan_spec hs hi (after i.left s) (s.take (ixL s i.left)) i.left [] []
  · rw [after_eq_drop, List.take_append_drop]
  · rw [hlen]
    exact {
      l_le := Nat.le_refl _
      le_j := Nat.le_refl _
      j_lt := hi.left_lt_right
      before_iff := by
        intro x
        constructor
        · intro h
          cases h
        · rintro ⟨h₁, h₂⟩
          omega
      conf_iff := by
        intro x
        constructor
        · intro h
          cases h
        · rintro ⟨h₁, h₂⟩
          omega
      goodA := by
        intro o _ h
        exact Or.inl h
      pend := by
        intro o _ h₁ h₂
        omega }

end YoctoSpec
