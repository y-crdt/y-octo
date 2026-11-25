import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.OrderRange

/-- Canonical invariant for `OrderRange`: strictly non-empty, sorted,
    disjoint, non-adjacent half-open intervals `[start, end)`. -/
def CanonicalList (l : List order_range.ClockRange) : Prop :=
  (∀ (i : Nat) (hi : i < l.length), (l[i]).start.val < (l[i]).«end».val) ∧
  (∀ (i j : Nat) (hi : i < j) (hj : j < l.length), (l[i]).«end».val < (l[j]).start.val)

def Canonical (r : order_range.OrderRange) : Prop :=
  CanonicalList r.ranges.val

/-- Membership semantics: `clock` lies inside one of the stored intervals. -/
def inRangesList (l : List order_range.ClockRange) (clock : Std.U64) : Prop :=
  ∃ (k : Nat) (hk : k < l.length),
    (l[k]).start.val ≤ clock.val ∧ clock.val < (l[k]).«end».val

def inRanges (r : order_range.OrderRange) (clock : Std.U64) : Prop :=
  inRangesList r.ranges.val clock

theorem canonicalList_start_lt {l : List order_range.ClockRange} (hCan : CanonicalList l)
    {i j : Nat} (hij : i < j) (hj : j < l.length) :
    (l[i]).start.val < (l[j]).start.val := by
  have hi : i < l.length := Nat.lt_trans hij hj
  exact Nat.lt_trans (hCan.1 i hi) (hCan.2 i j hij hj)

theorem canonicalList_end_lt {l : List order_range.ClockRange} (hCan : CanonicalList l)
    {i j : Nat} (hij : i < j) (hj : j < l.length) :
    (l[i]).«end».val < (l[j]).«end».val := by
  exact Nat.lt_trans (hCan.2 i j hij hj) (hCan.1 j hj)

theorem new_spec :
    order_range.OrderRange.new ⦃ r =>
      Canonical r ∧ r.ranges.length = 0 ∧ (∀ c, ¬ inRanges r c) ⦄ := by
  unfold order_range.OrderRange.new
  simp only [spec_ok, Canonical, CanonicalList, inRanges, inRangesList]
  refine ⟨⟨by intro i hi; simp at hi, by intro i j hij hj; simp at hj⟩, by simp, ?_⟩
  intro c ⟨k, hk, _⟩
  simp at hk

theorem contains_spec (self : order_range.OrderRange) (clock : Std.U64)
    (hCan : Canonical self) :
    order_range.OrderRange.contains self clock ⦃ b => b = true ↔ inRanges self clock ⦄ := by
  unfold order_range.OrderRange.contains order_range.OrderRange.contains_loop
  let inv : Std.Usize × Std.Usize → Prop := fun (lo, hi) =>
    lo.val ≤ hi.val ∧ hi.val ≤ self.ranges.length ∧
    (∀ (k : Nat) (hk : k < self.ranges.length), k < lo.val →
      (self.ranges.val[k]).«end».val ≤ clock.val) ∧
    (∀ (k : Nat) (hk : k < self.ranges.length), hi.val ≤ k →
      clock.val < (self.ranges.val[k]).start.val)
  refine loop.spec_decr_nat
    (fun (lo, hi) => hi.val - lo.val)
    inv (fun b => b = true ↔ inRanges self clock)
    _ (0#usize, alloc.vec.Vec.len self.ranges) ?_
    ⟨by scalar_tac, by scalar_tac, by intro k hk h; scalar_tac, by intro k hk h; scalar_tac⟩
  intro ⟨lo, hi⟩ ⟨hLoHi, hHiLen, hL, hR⟩
  unfold order_range.OrderRange.contains_loop.body
  simp only
  split_ifs with hlt
  · step*
    · -- clock < r.start
      refine ⟨⟨by scalar_tac, by scalar_tac, hL, ?_⟩, by scalar_tac⟩
      intro k hk hmk
      rcases eq_or_lt_of_le hmk with rfl | hgt
      · scalar_tac
      · exact Nat.lt_trans (by scalar_tac) (canonicalList_start_lt hCan hgt hk)
    · -- clock >= r.end
      refine ⟨⟨by scalar_tac, hHiLen, ?_, hR⟩, by scalar_tac⟩
      intro k hk hkm
      have hk_le : k ≤ mid.val := by scalar_tac
      rcases eq_or_lt_of_le hk_le with rfl | hlt2
      · scalar_tac
      · exact Nat.le_trans (Nat.le_of_lt (canonicalList_end_lt hCan hlt2 (by scalar_tac))) (by scalar_tac)
    · -- in interval
      simp only [true_iff, inRanges, inRangesList]
      exact ⟨mid.val, by scalar_tac, by scalar_tac, by scalar_tac⟩
  · simp only [spec_ok, Bool.false_eq_true, false_iff, inRanges, inRangesList]
    have hEq : lo.val = hi.val := by scalar_tac
    rintro ⟨k, hk, h1, h2⟩
    by_cases hkl : k < lo.val
    · have := hL k hk hkl; omega
    · have := hR k hk (by omega); omega

theorem insert_loop0_spec (v : alloc.vec.Vec order_range.ClockRange) (start : Std.U64)
    (hCan : CanonicalList v.val) :
    order_range.OrderRange.insert_loop0 v start 0#usize (alloc.vec.Vec.len v) ⦃ first =>
      first.val ≤ v.length ∧
      (∀ (k : Nat) (hk : k < v.length), k < first.val → (v.val[k]).«end».val < start.val) ∧
      (∀ (k : Nat) (hk : k < v.length), first.val ≤ k → start.val ≤ (v.val[k]).«end».val) ⦄ := by
  unfold order_range.OrderRange.insert_loop0
  let inv : Std.Usize × Std.Usize → Prop := fun (lo, hi) =>
    lo.val ≤ hi.val ∧ hi.val ≤ v.length ∧
    (∀ (k : Nat) (hk : k < v.length), k < lo.val → (v.val[k]).«end».val < start.val) ∧
    (∀ (k : Nat) (hk : k < v.length), hi.val ≤ k → start.val ≤ (v.val[k]).«end».val)
  refine loop.spec_decr_nat
    (fun (lo, hi) => hi.val - lo.val) inv _ _ (0#usize, alloc.vec.Vec.len v) ?_
    ⟨by scalar_tac, by scalar_tac, by intro k hk h; scalar_tac, by intro k hk h; scalar_tac⟩
  intro ⟨lo, hi⟩ ⟨hLoHi, hHiLen, hL, hR⟩
  unfold order_range.OrderRange.insert_loop0.body
  simp only
  split_ifs with hlt
  · step*
    · refine ⟨⟨by scalar_tac, hHiLen, ?_, hR⟩, by scalar_tac⟩
      intro k hk hkm
      have hk_le : k ≤ mid.val := by scalar_tac
      rcases eq_or_lt_of_le hk_le with rfl | hlt2
      · scalar_tac
      · exact Nat.lt_trans (canonicalList_end_lt hCan hlt2 (by scalar_tac)) (by scalar_tac)
    · refine ⟨⟨by scalar_tac, by scalar_tac, hL, ?_⟩, by scalar_tac⟩
      intro k hk hmk
      rcases eq_or_lt_of_le hmk with rfl | hgt
      · scalar_tac
      · exact Nat.le_trans (by scalar_tac) (Nat.le_of_lt (canonicalList_end_lt hCan hgt hk))
  · simp only [spec_ok]
    have hEq : lo.val = hi.val := by scalar_tac
    refine ⟨by scalar_tac, hL, fun k hk h => hR k hk (by omega)⟩

theorem insert_loop1_spec (v : alloc.vec.Vec order_range.ClockRange) («end» : Std.U64)
    (first : Std.Usize) (hFirst : first.val ≤ v.length) (hCan : CanonicalList v.val) :
    order_range.OrderRange.insert_loop1 v «end» first (alloc.vec.Vec.len v) ⦃ last =>
      first.val ≤ last.val ∧ last.val ≤ v.length ∧
      (∀ (k : Nat) (hk : k < v.length), first.val ≤ k → k < last.val →
        (v.val[k]).start.val ≤ «end».val) ∧
      (∀ (k : Nat) (hk : k < v.length), last.val ≤ k →
        «end».val < (v.val[k]).start.val) ⦄ := by
  unfold order_range.OrderRange.insert_loop1
  let inv : Std.Usize × Std.Usize → Prop := fun (lo, hi) =>
    first.val ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ v.length ∧
    (∀ (k : Nat) (hk : k < v.length), first.val ≤ k → k < lo.val →
      (v.val[k]).start.val ≤ «end».val) ∧
    (∀ (k : Nat) (hk : k < v.length), hi.val ≤ k →
      «end».val < (v.val[k]).start.val)
  refine loop.spec_decr_nat
    (fun (lo, hi) => hi.val - lo.val) inv _ _ (first, alloc.vec.Vec.len v) ?_
    ⟨le_refl _, hFirst, by scalar_tac, by intro k hk _ h; omega, by intro k hk h; scalar_tac⟩
  intro ⟨lo, hi⟩ ⟨hFL, hLoHi, hHiLen, hL, hR⟩
  unfold order_range.OrderRange.insert_loop1.body
  simp only
  split_ifs with hlt
  · step*
    · refine ⟨⟨by scalar_tac, by scalar_tac, hHiLen, ?_, hR⟩, by scalar_tac⟩
      intro k hk hfk hkm
      have hk_le : k ≤ mid.val := by scalar_tac
      rcases eq_or_lt_of_le hk_le with rfl | hlt2
      · scalar_tac
      · exact Nat.le_trans (Nat.le_of_lt (canonicalList_start_lt hCan hlt2 (by scalar_tac))) (by scalar_tac)
    · refine ⟨⟨hFL, by scalar_tac, by scalar_tac, hL, ?_⟩, by scalar_tac⟩
      intro k hk hmk
      rcases eq_or_lt_of_le hmk with rfl | hgt
      · scalar_tac
      · exact Nat.lt_trans (by scalar_tac) (canonicalList_start_lt hCan hgt hk)
  · simp only [spec_ok]
    have hEq : lo.val = hi.val := by scalar_tac
    refine ⟨hFL, by scalar_tac, hL, fun k hk h => hR k hk (by omega)⟩

theorem insert_loop2_spec (v : alloc.vec.Vec order_range.ClockRange)
    (first : Std.Usize) (hFirst : first.val ≤ v.length) :
    order_range.OrderRange.insert_loop2 v first (alloc.vec.Vec.new order_range.ClockRange) 0#usize ⦃ out =>
      out.val = v.val.take first.val ⦄ := by
  unfold order_range.OrderRange.insert_loop2
  let inv : alloc.vec.Vec order_range.ClockRange × Std.Usize → Prop := fun (out, i) =>
    i.val ≤ first.val ∧ out.val = v.val.take i.val
  refine loop.spec_decr_nat (fun (_, i) => first.val - i.val) inv _ _
    (alloc.vec.Vec.new order_range.ClockRange, 0#usize) ?_ ⟨by scalar_tac, by simp⟩
  intro ⟨out, i⟩ ⟨hi, hOut⟩
  unfold order_range.OrderRange.insert_loop2.body
  simp only
  split_ifs with hlt
  · have hiLt : i.val < v.length := by scalar_tac
    have hCapOut : out.length < Std.Usize.max := by
      have : out.length = i.val := by
        simp [alloc.vec.Vec.length, hOut, List.length_take]
        scalar_tac
      scalar_tac
    step as ⟨cr, hCr⟩
    step as ⟨out1, hOut1⟩
    step as ⟨i1, hI1⟩
    try simp only [spec_ok]
    refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
    simp only [hOut1, hCr, hOut, hI1, List.take_succ_eq_append_getElem hiLt]
  · simp only [spec_ok]
    have heq : i.val = first.val := by scalar_tac
    rw [hOut, heq]

theorem insert_loop3_spec (v out : alloc.vec.Vec order_range.ClockRange)
    (last : Std.Usize) (hLast : last.val ≤ v.length)
    (hBound : out.length + (v.length - last.val) ≤ Std.Usize.max) :
    order_range.OrderRange.insert_loop3 v out last ⦃ out' =>
      out'.val = out.val ++ v.val.drop last.val ⦄ := by
  unfold order_range.OrderRange.insert_loop3
  let inv : alloc.vec.Vec order_range.ClockRange × Std.Usize → Prop := fun (curOut, j) =>
    last.val ≤ j.val ∧ j.val ≤ v.length ∧
    curOut.val = out.val ++ (v.val.drop last.val).take (j.val - last.val)
  refine loop.spec_decr_nat (fun (_, j) => v.length - j.val) inv _ _ (out, last) ?_
    ⟨le_refl _, hLast, by simp⟩
  intro ⟨curOut, j⟩ ⟨hLJ, hjLen, hCur⟩
  unfold order_range.OrderRange.insert_loop3.body
  simp only
  split_ifs with hlt
  · have hjLt : j.val < v.length := by scalar_tac
    have hCurLen : curOut.length = out.length + (j.val - last.val) := by
      simp only [alloc.vec.Vec.length, hCur, List.length_append, List.length_take, List.length_drop]
      scalar_tac
    have hCapOut : curOut.length < Std.Usize.max := by
      have : j.val - last.val < v.length - last.val := by scalar_tac
      omega
    step as ⟨cr, hCr⟩
    step as ⟨out1, hOut1⟩
    step as ⟨j1, hJ1⟩
    try simp only [spec_ok]
    refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
    have hSub : j1.val - last.val = (j.val - last.val) + 1 := by scalar_tac
    have hVLen : v.val.length = v.length := by simp [alloc.vec.Vec.length]
    have hDropIdx : j.val - last.val < (v.val.drop last.val).length := by
      simp only [List.length_drop, hVLen]; omega
    have hElem : (v.val.drop last.val)[j.val - last.val] = v.val[j.val] := by
      simp [List.getElem_drop]
      congr 1; omega
    simp only [hOut1, hCr, hCur]
    rw [hSub, List.take_succ_eq_append_getElem hDropIdx, hElem, List.append_assoc]
  · simp only [spec_ok]
    have heq : j.val = v.length := by scalar_tac
    rw [hCur, heq, show v.length - last.val = (v.val.drop last.val).length by
          simp [alloc.vec.Vec.length, List.length_drop],
        List.take_length]

theorem insert_spec (self : order_range.OrderRange) (start «end» : Std.U64)
    (hCan : Canonical self) (hCap : self.ranges.length < Std.Usize.max) :
    order_range.OrderRange.insert self start «end» ⦃ r' =>
      Canonical r' ∧
      r'.ranges.length ≤ self.ranges.length + 1 ∧
      (∀ c, inRanges r' c ↔
        inRanges self c ∨ (start.val ≤ c.val ∧ c.val < «end».val)) ⦄ := by
  unfold order_range.OrderRange.insert
  split_ifs with hEmpty
  · simp only [spec_ok]
    refine ⟨hCan, Nat.le_succ _, fun c => ?_⟩
    constructor
    · exact Or.inl
    · rintro (h | ⟨h1, h2⟩)
      · exact h
      · exfalso; scalar_tac
  · have hStartEnd : start.val < «end».val := by scalar_tac
    step with insert_loop0_spec self.ranges start hCan as ⟨first, hFirstLen, hL0, hR0⟩
    step with insert_loop1_spec self.ranges «end» first hFirstLen hCan as ⟨last, hFL, hLastLen, hL1, hR1⟩
    by_cases hEqFL : first = last
    · simp only [hEqFL, ↓reduceIte]
      -- No overlap/adjacency: insert single interval at `first`
      have hInsCan : CanonicalList (self.ranges.val.insertIdx first.val { start, «end» }) := by
        have hLenIns : (self.ranges.val.insertIdx first.val { start, «end» }).length = self.ranges.length + 1 := by
          simp [alloc.vec.Vec.length, List.length_insertIdx, hFirstLen]
        have get_ins (m : Nat) (hm : m < (self.ranges.val.insertIdx first.val { start, «end» }).length) :
            if m < first.val then ∃ h : m < self.ranges.length,
              (self.ranges.val.insertIdx first.val { start, «end» })[m] = self.ranges.val[m]
            else if m = first.val then
              (self.ranges.val.insertIdx first.val { start, «end» })[m] = { start, «end» }
            else ∃ h : m - 1 < self.ranges.length,
              (self.ranges.val.insertIdx first.val { start, «end» })[m] = self.ranges.val[m - 1] := by
          split_ifs with h1 h2
          · exact ⟨by omega, by simp [List.getElem_insertIdx_of_lt, h1]⟩
          · subst h2; exact by simp [List.getElem_insertIdx_self, hFirstLen]
          · exact ⟨by omega, by simp [List.getElem_insertIdx_of_gt, (by omega : first.val < m)]⟩
        constructor
        · intro i hi
          have gi := get_ins i hi
          split_ifs at gi with h1 h2
          · rcases gi with ⟨hil, hgi⟩; rw [hgi]; exact hCan.1 i hil
          · rw [gi]; exact hStartEnd
          · rcases gi with ⟨hil, hgi⟩; rw [hgi]; exact hCan.1 (i - 1) hil
        · intro i j hij hj
          have hi : i < (self.ranges.val.insertIdx first.val { start, «end» }).length := Nat.lt_trans hij hj
          have gi := get_ins i hi
          have gj := get_ins j hj
          have hLastEq : first.val = last.val := by scalar_tac
          split_ifs at gi with hi1 hi2
          · rcases gi with ⟨hil, hgi⟩
            split_ifs at gj with hj1 hj2
            · rcases gj with ⟨hjl, hgj⟩; rw [hgi, hgj]; exact hCan.2 i j hij hjl
            · rw [hgi, gj]; exact hL0 i hil hi1
            · rcases gj with ⟨hjl, hgj⟩; rw [hgi, hgj]; exact hCan.2 i (j - 1) (by omega) hjl
          · split_ifs at gj with hj1 hj2
            · omega
            · omega
            · rcases gj with ⟨hjl, hgj⟩; rw [gi, hgj]; exact hR1 (j - 1) hjl (by omega)
          · rcases gi with ⟨hil, hgi⟩
            split_ifs at gj with hj1 hj2
            · omega
            · omega
            · rcases gj with ⟨hjl, hgj⟩; rw [hgi, hgj]; exact hCan.2 (i - 1) (j - 1) (by omega) hjl
      have hInsMem (c : Std.U64) :
          inRangesList (self.ranges.val.insertIdx first.val { start, «end» }) c ↔
            inRanges self c ∨ (start.val ≤ c.val ∧ c.val < «end».val) := by
        simp only [inRangesList, inRanges, alloc.vec.Vec.length]
        have hVLen : self.ranges.val.length = self.ranges.length := by simp [alloc.vec.Vec.length]
        have hFirstLeV : first.val ≤ self.ranges.val.length := by omega
        have hLenIns : (self.ranges.val.insertIdx first.val { start, «end» }).length = self.ranges.val.length + 1 := by
          simp [List.length_insertIdx, hFirstLeV]
        constructor
        · rintro ⟨k, hk, h1, h2⟩
          rw [hLenIns] at hk
          by_cases hk1 : k < first.val
          · rw [List.getElem_insertIdx_of_lt hk1] at h1 h2
            exact Or.inl ⟨k, by omega, h1, h2⟩
          · by_cases hk2 : k = first.val
            · subst hk2
              simp only [List.getElem_insertIdx_self, hFirstLeV] at h1 h2
              exact Or.inr ⟨h1, h2⟩
            · simp only [List.getElem_insertIdx_of_gt (by omega : first.val < k)] at h1 h2
              exact Or.inl ⟨k - 1, by omega, h1, h2⟩
        · rintro (⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩)
          · by_cases hk1 : k < first.val
            · refine ⟨k, by omega, ?_⟩
              simp only [List.getElem_insertIdx_of_lt hk1]; exact ⟨h1, h2⟩
            · refine ⟨k + 1, by omega, ?_⟩
              simp only [List.getElem_insertIdx_of_gt (by omega : first.val < k + 1)]
              simpa using ⟨h1, h2⟩
          · refine ⟨first.val, by omega, ?_⟩
            simp only [List.getElem_insertIdx_self, hFirstLeV]
            exact ⟨h1, h2⟩
      split_ifs with hAtEnd
      · step as ⟨v, hvPost⟩
        try simp only [spec_ok]
        have hPushEq : v.val = self.ranges.val.insertIdx first.val { start, «end» } := by
          have : first.val = self.ranges.length := by scalar_tac
          rw [this, List.insertIdx_length_self]
          exact hvPost
        refine ⟨by simpa [Canonical, hPushEq] using hInsCan, by scalar_tac, fun c => ?_⟩
        simpa [inRanges, hPushEq] using hInsMem c
      · have hFirstLt : first.val < self.ranges.length := by scalar_tac
        step as ⟨v, v_post⟩
        try simp only [spec_ok]
        have hLenIns : (self.ranges.val.insertIdx first.val { start, «end» }).length = self.ranges.length + 1 := by
          simp [alloc.vec.Vec.length, List.length_insertIdx, hFirstLen]
        refine ⟨by simpa [Canonical, v_post, hEqFL] using hInsCan, by scalar_tac,
          fun c => by simpa [inRanges, v_post, hEqFL] using hInsMem c⟩
    · simp only [hEqFL, Bool.false_eq_true, ↓reduceIte]
      -- Merge [first, last) with [start, end)
      have hFirstNe : first.val ≠ last.val := fun h => hEqFL (UScalar.eq_of_val_eq h)
      have hFirstLtLast : first.val < last.val := by omega
      have hFirstLtLen : first.val < self.ranges.length := by omega
      have hLastPos : 1 ≤ last.val := by omega
      have hLastLeV : last.val ≤ self.ranges.val.length := by scalar_tac
      step as ⟨f, hfEq⟩
      step as ⟨last1, hLast1⟩
      step as ⟨l, hlEqRaw⟩
      have hlEq : l = self.ranges.val[last.val - 1]'(by omega) := by
        simpa [hLast1] using hlEqRaw
      have hMsSpec : (if start < f.start then ok start else ok f.start) ⦃ ms =>
          ms.val = min start.val f.start.val ⦄ := by
        split_ifs <;> simp only [spec_ok] <;> scalar_tac
      step with hMsSpec as ⟨merged_start, hMs⟩
      have hMeSpec : (if «end» > l.end then ok «end» else ok l.end) ⦃ me =>
          me.val = max «end».val l.end.val ⦄ := by
        split_ifs <;> simp only [spec_ok] <;> scalar_tac
      step with hMeSpec as ⟨merged_end, hMe⟩
      have hfEnd : start.val ≤ f.end.val := by rw [hfEq]; exact hR0 first.val hFirstLtLen (le_refl _)
      have hlStart : l.start.val ≤ «end».val := by
        rw [hlEq]; exact hL1 (last.val - 1) (by omega) (by omega) (by omega)
      have hMergedNonEmpty : merged_start.val < merged_end.val := by
        have := hCan.1 first.val hFirstLtLen
        rw [← hfEq] at this
        omega
      have hUnionCov (c : Std.U64) :
          (merged_start.val ≤ c.val ∧ c.val < merged_end.val) ↔
          ((start.val ≤ c.val ∧ c.val < «end».val) ∨
           ∃ (k : Nat) (hk : k < self.ranges.length),
             first.val ≤ k ∧ k < last.val ∧
             (self.ranges.val[k]).start.val ≤ c.val ∧ c.val < (self.ranges.val[k]).«end».val) := by
        constructor
        · rintro ⟨hc1, hc2⟩
          by_cases hltS : c.val < start.val
          · have hfc1 : f.start.val ≤ c.val := by omega
            have hfc2 : c.val < f.end.val := by omega
            exact Or.inr ⟨first.val, hFirstLtLen, le_refl _, hFirstLtLast, by rw [← hfEq]; exact ⟨hfc1, hfc2⟩⟩
          · by_cases hltE : c.val < «end».val
            · exact Or.inl ⟨by omega, hltE⟩
            · have hlc1 : l.start.val ≤ c.val := by omega
              have hlc2 : c.val < l.end.val := by omega
              exact Or.inr ⟨last.val - 1, by omega, by omega, by omega, by rw [← hlEq]; exact ⟨hlc1, hlc2⟩⟩
        · rintro (⟨h1, h2⟩ | ⟨k, hk, hfk, hkl, h1, h2⟩)
          · omega
          · have hk1 : f.start.val ≤ (self.ranges.val[k]).start.val := by
              rw [hfEq]
              rcases eq_or_lt_of_le hfk with rfl | hgt
              · exact le_refl _
              · exact Nat.le_of_lt (canonicalList_start_lt hCan hgt hk)
            have hk2 : (self.ranges.val[k]).«end».val ≤ l.end.val := by
              rw [hlEq]
              rcases eq_or_lt_of_le (by omega : k ≤ last.val - 1) with hEq | hlt2
              · subst hEq; exact le_refl _
              · exact Nat.le_of_lt (canonicalList_end_lt hCan hlt2 (by omega))
            omega
      step as ⟨firstPlus1, hFirstPlus1⟩
      split_ifs with hOne
      · -- last == first + 1: replace in place
        have hLastEqS : last.val = first.val + 1 := by scalar_tac
        step as ⟨_, index_mut_back, _, hBack⟩
        try simp only [spec_ok]
        have hSetVal : (index_mut_back { start := merged_start, «end» := merged_end }).val =
            self.ranges.val.set first.val { start := merged_start, «end» := merged_end } := by
          rw [hBack]
          simp [alloc.vec.Vec.set]
        refine ⟨?_, by simp [hSetVal], fun c => ?_⟩
        · simp only [Canonical, hSetVal]
          constructor
          · intro i hi
            simp only [List.length_set] at hi
            by_cases hif : i = first.val
            · simp [hif, List.getElem_set_self, hMergedNonEmpty]
            · simp [List.getElem_set_ne (Ne.symm hif)]; exact hCan.1 i hi
          · intro i j hij hj
            simp only [List.length_set] at hj
            have hi : i < self.ranges.length := Nat.lt_trans hij hj
            by_cases hif : i = first.val
            · have hjne : j ≠ first.val := by omega
              have hSetI : (self.ranges.val.set first.val { start := merged_start, «end» := merged_end })[i] =
                  { start := merged_start, «end» := merged_end } := by
                simp [hif, List.getElem_set_self]
              have hSetJ : (self.ranges.val.set first.val { start := merged_start, «end» := merged_end })[j] =
                  self.ranges.val[j] := by
                simp [List.getElem_set_ne (Ne.symm hjne)]
              rw [hSetI, hSetJ]
              have hjgt : last.val ≤ j := by omega
              have hRight := hR1 j hj hjgt
              have hEndEq : (self.ranges.val[last.val - 1]).«end».val = (self.ranges.val[i]).«end».val := by
                have hIdxEq : last.val - 1 = i := by omega
                simp [hIdxEq]
              have hCanR := hCan.2 i j hij hj
              rw [← hEndEq, ← hlEq] at hCanR
              rw [hMe, Nat.max_lt]
              exact ⟨hRight, hCanR⟩
            · by_cases hjf : j = first.val
              · have hilt : i < first.val := by omega
                have hSetI : (self.ranges.val.set first.val { start := merged_start, «end» := merged_end })[i] =
                    self.ranges.val[i] := by
                  simp [List.getElem_set_ne (Ne.symm hif)]
                have hSetJ : (self.ranges.val.set first.val { start := merged_start, «end» := merged_end })[j] =
                    { start := merged_start, «end» := merged_end } := by
                  simp [hjf, List.getElem_set_self]
                rw [hSetI, hSetJ]
                have hLeft := hL0 i hi hilt
                have hCanL := hCan.2 i j hij hj
                have hStartEq : (self.ranges.val[j]).start.val = f.start.val := by
                  simp [hjf, hfEq]
                rw [hStartEq] at hCanL
                rw [hMs, Nat.lt_min]
                exact ⟨hLeft, hCanL⟩
              · simp only [List.getElem_set_ne (Ne.symm hif), List.getElem_set_ne (Ne.symm hjf)]
                exact hCan.2 i j hij hj
        · simp only [inRanges, inRangesList, hSetVal, List.length_set]
          constructor
          · rintro ⟨k, hk, h1, h2⟩
            by_cases hkf : k = first.val
            · subst hkf
              simp only [List.getElem_set_self] at h1 h2
              rcases (hUnionCov c).1 ⟨h1, h2⟩ with hS | ⟨m, hm, hfm, hml, h1', h2'⟩
              · exact Or.inr hS
              · exact Or.inl ⟨m, hm, h1', h2'⟩
            · simp only [List.getElem_set_ne (Ne.symm hkf)] at h1 h2
              exact Or.inl ⟨k, hk, h1, h2⟩
          · rintro (⟨k, hk, h1, h2⟩ | hS)
            · by_cases hkf : k = first.val
              · refine ⟨k, hk, ?_⟩
                simp only [hkf, List.getElem_set_self]
                exact (hUnionCov c).2 (Or.inr ⟨k, hk, by omega, by omega, h1, h2⟩)
              · refine ⟨k, hk, ?_⟩
                simp only [List.getElem_set_ne (Ne.symm hkf)]
                exact ⟨h1, h2⟩
            · refine ⟨first.val, hFirstLtLen, ?_⟩
              simp only [List.getElem_set_self]
              exact (hUnionCov c).2 (Or.inl hS)
      · -- last > first + 1: rebuild via insert_loop2 + push + insert_loop3
        step with insert_loop2_spec self.ranges first hFirstLen as ⟨out, hOutVal⟩
        have hOutLen : out.length = first.val := by
          simp [alloc.vec.Vec.length, hOutVal, List.length_take]; omega
        have hOutCap : out.length < Std.Usize.max := by omega
        step as ⟨out1, hOut1Val⟩
        have hOut1Cap : out1.length + (self.ranges.length - last.val) ≤ Std.Usize.max := by
          have : out1.length = first.val + 1 := by scalar_tac
          omega
        step with insert_loop3_spec self.ranges out1 last hLastLen hOut1Cap as ⟨out2, hOut2Val⟩
        have hListEq : out2.val =
            self.ranges.val.take first.val ++
              [{ start := merged_start, «end» := merged_end }] ++
              self.ranges.val.drop last.val := by
          rw [hOut2Val, hOut1Val, hOutVal]
        have hOut2Len : out2.length = first.val + 1 + (self.ranges.length - last.val) := by
          simp [alloc.vec.Vec.length, hListEq, List.length_append, List.length_take, List.length_drop]
          omega
        try simp only [spec_ok]
        refine ⟨?_, by omega, fun c => ?_⟩
        · have hVLen : self.ranges.val.length = self.ranges.length := rfl
          have get_out2 (m : Nat) (hm : m < out2.length) :
              if m < first.val then ∃ h : m < self.ranges.length, out2.val[m] = self.ranges.val[m]
              else if m = first.val then out2.val[m] = { start := merged_start, «end» := merged_end }
              else ∃ h : m - (first.val + 1) + last.val < self.ranges.length,
                out2.val[m] = self.ranges.val[m - (first.val + 1) + last.val] := by
            have hTakeLen : (self.ranges.val.take first.val).length = first.val := by
              simp [List.length_take]; omega
            split_ifs with h1 h2
            · refine ⟨by omega, ?_⟩
              simp [hListEq, List.getElem_append_left, hTakeLen, h1, List.getElem_take]
            · subst h2
              simp [hListEq, List.getElem_append_left, List.getElem_append_right, hTakeLen]
            · have hmOut2 : m < first.val + 1 + (self.ranges.length - last.val) := by
                rw [← hOut2Len]; exact hm
              refine ⟨by omega, ?_⟩
              have hGe : first.val + 1 ≤ m := by omega
              have hEqIdx : m - (first.val + 1) < (self.ranges.val.drop last.val).length := by
                simp only [List.length_drop, hVLen]; omega
              simp only [hListEq, List.append_assoc]
              rw [List.getElem_append_right (by omega)]
              have hSub : m - (self.ranges.val.take first.val).length = (m - (first.val + 1)) + 1 := by
                rw [hTakeLen]; omega
              simp only [List.singleton_append, hSub, List.getElem_cons_succ, List.getElem_drop]
              congr 1; omega
          constructor
          · intro i hi
            have gi := get_out2 i hi
            split_ifs at gi with h1 h2
            · rcases gi with ⟨hil, hgi⟩; rw [hgi]; exact hCan.1 i hil
            · rw [gi]; exact hMergedNonEmpty
            · rcases gi with ⟨hil, hgi⟩; rw [hgi]; exact hCan.1 _ hil
          · intro i j hij hj
            have hi : i < out2.length := Nat.lt_trans hij hj
            have gi := get_out2 i hi
            have gj := get_out2 j hj
            split_ifs at gi with hi1 hi2
            · rcases gi with ⟨hil, hgi⟩
              split_ifs at gj with hj1 hj2
              · rcases gj with ⟨hjl, hgj⟩; rw [hgi, hgj]; exact hCan.2 i j hij hjl
              · rw [hgi, gj]
                have h1 := hL0 i hil hi1
                have h2 := hCan.2 i first.val hi1 hFirstLtLen
                rw [← hfEq] at h2
                rw [hMs, Nat.lt_min]
                exact ⟨h1, h2⟩
              · rcases gj with ⟨hjl, hgj⟩; rw [hgi, hgj]; exact hCan.2 i _ (by omega) hjl
            · split_ifs at gj with hj1 hj2
              · omega
              · omega
              · rcases gj with ⟨hjl, hgj⟩; rw [gi, hgj]
                have h1 := hR1 (j - (first.val + 1) + last.val) hjl (by omega)
                have h2 := hCan.2 (last.val - 1) (j - (first.val + 1) + last.val) (by omega) hjl
                rw [← hlEq] at h2
                rw [hMe, Nat.max_lt]
                exact ⟨h1, h2⟩
            · rcases gi with ⟨hil, hgi⟩
              split_ifs at gj with hj1 hj2
              · omega
              · omega
              · rcases gj with ⟨hjl, hgj⟩; rw [hgi, hgj]; exact hCan.2 _ _ (by omega) hjl
        · simp only [inRanges, inRangesList]
          have hVLen : self.ranges.val.length = self.ranges.length := rfl
          have hTakeLen : (self.ranges.val.take first.val).length = first.val := by
            simp [List.length_take]; omega
          constructor
          · rintro ⟨k, hk, h1, h2⟩
            have hkOut2 : k < first.val + 1 + (self.ranges.length - last.val) := by
              rw [← hOut2Len]; exact hk
            by_cases hk1 : k < first.val
            · have hk' : k < self.ranges.length := by omega
              have hEl : out2.val[k] = self.ranges.val[k] := by
                simp [hListEq, List.getElem_append_left, hTakeLen, hk1, List.getElem_take]
              rw [hEl] at h1 h2
              exact Or.inl ⟨k, hk', h1, h2⟩
            · by_cases hk2 : k = first.val
              · have hEl : out2.val[k] = ({ start := merged_start, «end» := merged_end } : order_range.ClockRange) := by
                  simp [hk2, hListEq, List.getElem_append_left, List.getElem_append_right, hTakeLen]
                rw [hEl] at h1 h2
                rcases (hUnionCov c).1 ⟨h1, h2⟩ with hS | ⟨m, hm, _, _, h1', h2'⟩
                · exact Or.inr hS
                · exact Or.inl ⟨m, hm, h1', h2'⟩
              · have hk' : k - (first.val + 1) + last.val < self.ranges.length := by omega
                have hEl : out2.val[k] = self.ranges.val[k - (first.val + 1) + last.val] := by
                  simp only [hListEq, List.append_assoc]
                  rw [List.getElem_append_right (by omega)]
                  have hSub : k - (self.ranges.val.take first.val).length = (k - (first.val + 1)) + 1 := by
                    rw [hTakeLen]; omega
                  simp only [List.singleton_append, hSub, List.getElem_cons_succ, List.getElem_drop]
                  congr 1; omega
                rw [hEl] at h1 h2
                exact Or.inl ⟨_, hk', h1, h2⟩
          · have hOut2VLen : out2.val.length = first.val + 1 + (self.ranges.length - last.val) := hOut2Len
            rintro (⟨k, hk, h1, h2⟩ | hS)
            · by_cases hk1 : k < first.val
              · have hkOut2 : k < out2.val.length := by rw [hOut2VLen]; omega
                refine ⟨k, hkOut2, ?_⟩
                have hEl : out2.val[k] = self.ranges.val[k] := by
                  simp [hListEq, List.getElem_append_left, hTakeLen, hk1, List.getElem_take]
                rw [hEl]; exact ⟨h1, h2⟩
              · by_cases hk2 : k < last.val
                · have hfOut2 : first.val < out2.val.length := by rw [hOut2VLen]; omega
                  refine ⟨first.val, hfOut2, ?_⟩
                  have hEl : out2.val[first.val] = { start := merged_start, «end» := merged_end } := by
                    simp [hListEq, List.getElem_append_left, List.getElem_append_right, hTakeLen]
                  rw [hEl]
                  exact (hUnionCov c).2 (Or.inr ⟨k, hk, by omega, hk2, h1, h2⟩)
                · have hkOut2 : first.val + 1 + (k - last.val) < out2.val.length := by rw [hOut2VLen]; omega
                  refine ⟨first.val + 1 + (k - last.val), hkOut2, ?_⟩
                  have hEl : out2.val[first.val + 1 + (k - last.val)] = self.ranges.val[k] := by
                    simp only [hListEq, List.append_assoc]
                    rw [List.getElem_append_right (by omega)]
                    have hSub : first.val + 1 + (k - last.val) - (self.ranges.val.take first.val).length =
                        (k - last.val) + 1 := by
                      rw [hTakeLen]; omega
                    simp only [List.singleton_append, hSub, List.getElem_cons_succ, List.getElem_drop]
                    congr 1; omega
                  rw [hEl]; exact ⟨h1, h2⟩
            · have hfOut2 : first.val < out2.val.length := by rw [hOut2VLen]; omega
              refine ⟨first.val, hfOut2, ?_⟩
              have hEl : out2.val[first.val] = { start := merged_start, «end» := merged_end } := by
                simp [hListEq, List.getElem_append_left, List.getElem_append_right, hTakeLen]
              rw [hEl]
              exact (hUnionCov c).2 (Or.inl hS)

theorem merge_spec (self other : order_range.OrderRange)
    (hCanSelf : Canonical self) (hCanOther : Canonical other)
    (hCap : self.ranges.length + other.ranges.length ≤ Std.Usize.max) :
    order_range.OrderRange.merge self other ⦃ r' =>
      Canonical r' ∧
      r'.ranges.length ≤ self.ranges.length + other.ranges.length ∧
      (∀ c, inRanges r' c ↔ inRanges self c ∨ inRanges other c) ⦄ := by
  unfold order_range.OrderRange.merge order_range.OrderRange.merge_loop
  let inv : order_range.OrderRange × Std.Usize → Prop := fun (r, i) =>
    Canonical r ∧ i.val ≤ other.ranges.length ∧
    r.ranges.length ≤ self.ranges.length + i.val ∧
    (∀ c, inRanges r c ↔ inRanges self c ∨ inRangesList (other.ranges.val.take i.val) c)
  have hTakeAll : other.ranges.val.take other.ranges.length = other.ranges.val := List.take_length
  refine loop.spec_decr_nat
    (fun (_, i) => other.ranges.length - i.val)
    inv _ _ (self, 0#usize) ?_
    ⟨hCanSelf, by scalar_tac, by scalar_tac, fun c => by simp [inRangesList]⟩
  intro ⟨accR, i⟩ ⟨hCanR, hiLen, hRLen, hMem⟩
  unfold order_range.OrderRange.merge_loop.body
  simp only
  split_ifs with hlt
  · have hiLt : i.val < other.ranges.length := by scalar_tac
    have hCapStep : accR.ranges.length < Std.Usize.max := by omega
    step as ⟨r, hrPost⟩
    step with insert_spec accR r.start r.end hCanR hCapStep as ⟨self1, hSelf1Can, hSelf1Len, hSelf1Mem⟩
    step as ⟨i2, hi2⟩
    try simp only [spec_ok]
    refine ⟨⟨hSelf1Can, by scalar_tac, by omega, fun c => ?_⟩, by scalar_tac⟩
    have hi2Val : i2.val = i.val + 1 := by scalar_tac
    rw [hSelf1Mem c, hMem c]
    have hTakeSucc : inRangesList (other.ranges.val.take (i.val + 1)) c ↔
        inRangesList (other.ranges.val.take i.val) c ∨
        (r.start.val ≤ c.val ∧ c.val < r.end.val) := by
      simp only [inRangesList]
      rw [List.take_succ_eq_append_getElem hiLt, hrPost]
      have hMin : min i.val other.ranges.val.length = i.val := by
        simp [alloc.vec.Vec.length] at hiLt
        exact Nat.min_eq_left (Nat.le_of_lt hiLt)
      have hTLen : (other.ranges.val.take i.val).length = i.val := by
        simp [List.length_take, hMin]
      constructor
      · rintro ⟨k, hk, h1, h2⟩
        simp only [List.length_append, List.length_cons, List.length_nil, hTLen] at hk
        by_cases hki : k < i.val
        · rw [List.getElem_append_left (by omega)] at h1 h2
          exact Or.inl ⟨k, by rw [hTLen]; exact hki, h1, h2⟩
        · have hkeq : k = i.val := by omega
          subst hkeq
          rw [List.getElem_append_right (by omega)] at h1 h2
          simp only [hTLen, Nat.sub_self, List.getElem_cons_zero] at h1 h2
          exact Or.inr ⟨h1, h2⟩
      · rintro (⟨k, hk, h1, h2⟩ | ⟨h1, h2⟩)
        · rw [hTLen] at hk
          refine ⟨k, by simp only [List.length_append, List.length_cons, List.length_nil, hTLen]; omega, ?_⟩
          rw [List.getElem_append_left (by rw [hTLen]; exact hk)]; exact ⟨h1, h2⟩
        · refine ⟨i.val, by simp only [List.length_append, List.length_cons, List.length_nil, hTLen]; omega, ?_⟩
          simp only [List.getElem_append_right (by rw [hTLen]), hTLen, Nat.sub_self, List.getElem_cons_zero]
          exact ⟨h1, h2⟩
    rw [hi2Val, hTakeSucc]
    tauto
  · simp only [spec_ok]
    have heq : i.val = other.ranges.length := by scalar_tac
    refine ⟨hCanR, by omega, fun c => ?_⟩
    rw [hMem c]
    simp [inRanges, heq, hTakeAll]

theorem merge_comm (a b : order_range.OrderRange)
    (hCanA : Canonical a) (hCanB : Canonical b)
    (hCapAB : a.ranges.length + b.ranges.length ≤ Std.Usize.max)
    (hCapBA : b.ranges.length + a.ranges.length ≤ Std.Usize.max) :
    (do
      let ab ← order_range.OrderRange.merge a b
      let ba ← order_range.OrderRange.merge b a
      ok (ab, ba)) ⦃ (ab, ba) => ∀ c, inRanges ab c ↔ inRanges ba c ⦄ := by
  step with merge_spec a b hCanA hCanB hCapAB as ⟨ab, habCan, habLen, habMem⟩
  step with merge_spec b a hCanB hCanA hCapBA as ⟨ba, hbaCan, hbaLen, hbaMem⟩
  try simp only [spec_ok]
  intro c
  rw [habMem c, hbaMem c]
  exact or_comm

theorem merge_idem (a : order_range.OrderRange)
    (hCan : Canonical a) (hCap : a.ranges.length + a.ranges.length ≤ Std.Usize.max) :
    order_range.OrderRange.merge a a ⦃ aa => ∀ c, inRanges aa c ↔ inRanges a c ⦄ := by
  refine spec_mono (merge_spec a a hCan hCan hCap) ?_
  intro aa ⟨_, _, hMem⟩ c
  rw [hMem c]
  exact iff_of_eq (or_self _)

end YoctoCore.Properties.OrderRange
