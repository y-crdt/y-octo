import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.ClockSearch

/-- Upper endpoint of a `(start, len)` segment in `u64`, saturated at `U64.max`. -/
def segEnd (p : Std.U64 × Std.U64) : Nat :=
  min Std.U64.max (p.1.val + p.2.val)

/-- Predicate stating `clock` lies inside `[p.1, segEnd p)`. -/
def inSeg (p : Std.U64 × Std.U64) (clock : Std.U64) : Prop :=
  p.1.val ≤ clock.val ∧ clock.val < segEnd p

/-- Well-formedness of a clock segment table: positive lengths and
    non-overlapping sorted intervals `(start, len)`. -/
def WellFormedSegments (segments : Slice (Std.U64 × Std.U64)) : Prop :=
  (∀ (i : Nat) (hi : i < segments.length), 0 < (segments.val[i]).2.val) ∧
  (∀ (i j : Nat) (hi : i < j) (hj : j < segments.length),
    segEnd (segments.val[i]'(Nat.lt_trans hi hj)) ≤ (segments.val[j]).1.val)

theorem find_clock_segment_loop_sound
    (segments : Slice (Std.U64 × Std.U64)) (clock : Std.U64)
    (low high : Std.Usize)
    (hInv : low.val ≤ high.val ∧ high.val ≤ segments.length) :
    clock_search.find_clock_segment_loop segments clock low high ⦃ res =>
      ∀ idx, res = some idx →
        ∃ h : idx.val < segments.length, inSeg (segments.val[idx.val]'h) clock ⦄ := by
  unfold clock_search.find_clock_segment_loop
  refine loop.spec_decr_nat
    (fun (lo, hi) => hi.val - lo.val)
    (fun (lo, hi) => lo.val ≤ hi.val ∧ hi.val ≤ segments.length)
    (fun (res : Option Std.Usize) => ∀ idx, res = some idx →
      ∃ h : idx.val < segments.length, inSeg (segments.val[idx.val]'h) clock)
    _ (low, high) ?_ hInv
  intro ⟨lo, hi⟩ ⟨hLoHi, hHiLen⟩
  unfold clock_search.find_clock_segment_loop.body
  simp only
  split_ifs with hlt
  · step as ⟨i, hiPost⟩
    step as ⟨i1, hi1Post⟩
    step as ⟨mid, hmidPost⟩
    step as ⟨p, hpPost⟩
    rcases p with ⟨start, len⟩
    try dsimp only
    have hMax : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
    have hRMax : Std.U64.rMax = 2 ^ 64 - 1 := by decide
    have hSubMax : start.val ≤ (core.num.U64.MAX : Std.U64).val := by rw [hMax]; scalar_tac
    step as ⟨i2, hi2Post⟩
    have hEndSpec : (if len > i2 then ok core.num.U64.MAX else start + len) ⦃ e =>
        e.val = segEnd (start, len) ⦄ := by
      have hU64Max : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, Std.U64.numBits]
      split_ifs with hgt
      · simp only [spec_ok, segEnd, hU64Max]
        have hI2 : i2.val = 2 ^ 64 - 1 - start.val := by rw [hi2Post, hRMax]
        have hGtVal : i2.val < len.val := by scalar_tac
        omega
      · have hLe : start.val + len.val ≤ 2 ^ 64 - 1 := by
          have hI2 : i2.val = 2 ^ 64 - 1 - start.val := by rw [hi2Post, hRMax]
          have hLeVal : len.val ≤ i2.val := by scalar_tac
          omega
        step as ⟨s, hs⟩
        try simp only [spec_ok]
        simp only [segEnd, hU64Max]
        have : s.val = start.val + len.val := by scalar_tac
        omega
    step with hEndSpec as ⟨«end», hendPost⟩
    split_ifs with hlt1 hge1
    · simp only [spec_ok]
      exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
    · step as ⟨low1, hlow1Post⟩
      try simp only [spec_ok]
      exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
    · simp only [spec_ok]
      intro idx hidx
      injection hidx with hidx'
      subst hidx'
      have hMidLen : mid.val < segments.length := by scalar_tac
      have hStartEq : (segments.val[mid.val]'hMidLen).1.val = start.val :=
        congrArg UScalar.val (congrArg Prod.fst hpPost.symm)
      refine ⟨hMidLen, by rw [hStartEq]; scalar_tac, ?_⟩
      have : clock.val < «end».val := by scalar_tac
      simpa [hpPost, hendPost] using this
  · simp only [spec_ok]
    intro idx hidx
    cases hidx

theorem find_clock_segment_total
    (segments : Slice (Std.U64 × Std.U64)) (clock : Std.U64) :
    clock_search.find_clock_segment segments clock ⦃ _ => True ⦄ := by
  unfold clock_search.find_clock_segment
  refine spec_mono (find_clock_segment_loop_sound segments clock 0#usize (Slice.len segments)
    ⟨by scalar_tac, by scalar_tac⟩) ?_
  intro _ _; exact trivial

theorem find_clock_segment_sound
    (segments : Slice (Std.U64 × Std.U64)) (clock : Std.U64) :
    clock_search.find_clock_segment segments clock ⦃ res =>
      ∀ idx, res = some idx →
        ∃ h : idx.val < segments.length, inSeg (segments.val[idx.val]'h) clock ⦄ := by
  unfold clock_search.find_clock_segment
  exact find_clock_segment_loop_sound segments clock 0#usize (Slice.len segments)
    ⟨by scalar_tac, by scalar_tac⟩

private theorem wf_seg_mono (segments : Slice (Std.U64 × Std.U64))
    (hWf : WellFormedSegments segments)
    {i j : Nat} (hij : i ≤ j) (hj : j < segments.length) :
    (segments.val[i]'(Nat.lt_of_le_of_lt hij hj)).1.val ≤ (segments.val[j]'hj).1.val := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact Nat.le_refl _
  · have hi : i < segments.length := Nat.lt_trans hlt hj
    have h1 : (segments.val[i]'hi).1.val ≤ segEnd (segments.val[i]'hi) := by
      simp only [segEnd]
      exact Nat.le_min.mpr ⟨by scalar_tac, Nat.le_add_right _ _⟩
    exact Nat.le_trans h1 (hWf.2 i j hlt hj)

theorem find_clock_segment_loop_complete
    (segments : Slice (Std.U64 × Std.U64)) (clock : Std.U64)
    (hWf : WellFormedSegments segments)
    (low high : Std.Usize)
    (hBounds : low.val ≤ high.val ∧ high.val ≤ segments.length)
    (hLeft : ∀ (k : Nat) (hk : k < segments.length), k < low.val →
      segEnd (segments.val[k]) ≤ clock.val)
    (hRight : ∀ (k : Nat) (hk : k < segments.length), high.val ≤ k →
      clock.val < (segments.val[k]).1.val) :
    clock_search.find_clock_segment_loop segments clock low high ⦃ res =>
      match res with
      | some idx =>
        ∃ h : idx.val < segments.length, inSeg (segments.val[idx.val]'h) clock
      | none =>
        ∀ (k : Nat) (hk : k < segments.length), ¬ inSeg (segments.val[k]) clock ⦄ := by
  unfold clock_search.find_clock_segment_loop
  let inv : Std.Usize × Std.Usize → Prop := fun (lo, hi) =>
    lo.val ≤ hi.val ∧ hi.val ≤ segments.length ∧
    (∀ (k : Nat) (hk : k < segments.length), k < lo.val →
      segEnd (segments.val[k]) ≤ clock.val) ∧
    (∀ (k : Nat) (hk : k < segments.length), hi.val ≤ k →
      clock.val < (segments.val[k]).1.val)
  refine loop.spec_decr_nat
    (fun (lo, hi) => hi.val - lo.val)
    inv _ _ (low, high) ?_ ⟨hBounds.1, hBounds.2, hLeft, hRight⟩
  intro ⟨lo, hi⟩ ⟨hLoHi, hHiLen, hL, hR⟩
  unfold clock_search.find_clock_segment_loop.body
  simp only
  split_ifs with hlt
  · step as ⟨i, hiPost⟩
    step as ⟨i1, hi1Post⟩
    step as ⟨mid, hmidPost⟩
    step as ⟨p, hpPost⟩
    rcases p with ⟨start, len⟩
    try dsimp only
    have hMax : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
    have hRMax : Std.U64.rMax = 2 ^ 64 - 1 := by decide
    have hSubMax : start.val ≤ (core.num.U64.MAX : Std.U64).val := by rw [hMax]; scalar_tac
    step as ⟨i2, hi2Post⟩
    have hEndSpec : (if len > i2 then ok core.num.U64.MAX else start + len) ⦃ e =>
        e.val = segEnd (start, len) ⦄ := by
      have hU64Max : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, Std.U64.numBits]
      split_ifs with hgt
      · simp only [spec_ok, segEnd, hU64Max]
        have hI2 : i2.val = 2 ^ 64 - 1 - start.val := by rw [hi2Post, hRMax]
        have hGtVal : i2.val < len.val := by scalar_tac
        omega
      · have hLe : start.val + len.val ≤ 2 ^ 64 - 1 := by
          have hI2 : i2.val = 2 ^ 64 - 1 - start.val := by rw [hi2Post, hRMax]
          have hLeVal : len.val ≤ i2.val := by scalar_tac
          omega
        step as ⟨s, hs⟩
        try simp only [spec_ok]
        simp only [segEnd, hU64Max]
        have : s.val = start.val + len.val := by scalar_tac
        omega
    step with hEndSpec as ⟨«end», hendPost⟩
    split_ifs with hlt1 hlt2
    · -- clock < start
      simp only [spec_ok]
      refine ⟨⟨by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
      · intro k hk hkl
        exact hL k hk (Nat.lt_of_lt_of_le hkl (by scalar_tac))
      · intro k hk hkm
        have hMidLen : mid.val < segments.length := by scalar_tac
        have hClkLt : clock.val < start.val := by scalar_tac
        have hmid_le : (segments.val[mid.val]'hMidLen).1.val ≤ (segments.val[k]'hk).1.val :=
          wf_seg_mono segments hWf hkm hk
        have hStart : start.val = (segments.val[mid.val]'hMidLen).1.val :=
          congrArg UScalar.val (congrArg Prod.fst hpPost)
        omega
    · -- clock >= «end»
      step as ⟨low1, hlow1Post⟩
      try simp only [spec_ok]
      have hMidLen : mid.val < segments.length := by scalar_tac
      have hEnd : segEnd (segments.val[mid.val]'hMidLen) ≤ clock.val := by
        have hStart : (start, len) = segments.val[mid.val]'hMidLen := hpPost
        have : «end».val ≤ clock.val := by scalar_tac
        rw [← hStart, ← hendPost]
        exact this
      refine ⟨⟨by scalar_tac, hHiLen, ?_, ?_⟩, by scalar_tac⟩
      · intro k hk hkm
        have hk_le : k ≤ mid.val := by scalar_tac
        rcases eq_or_lt_of_le hk_le with rfl | hk_lt
        · exact hEnd
        · have h1 := hWf.2 k mid.val hk_lt hMidLen
          have h2 : (segments.val[mid.val]'hMidLen).1.val ≤ segEnd (segments.val[mid.val]'hMidLen) := by
            simp only [segEnd]
            exact Nat.le_min.mpr ⟨by scalar_tac, Nat.le_add_right _ _⟩
          exact Nat.le_trans h1 (Nat.le_trans h2 hEnd)
      · intro k hk hkh
        exact hR k hk hkh
    · -- found
      simp only [spec_ok]
      have hMidLen : mid.val < segments.length := by scalar_tac
      have hNotLt : start.val ≤ clock.val := by scalar_tac
      have hNotGe : clock.val < «end».val := by scalar_tac
      have hStart : (start, len) = segments.val[mid.val]'hMidLen := hpPost
      refine ⟨hMidLen, ?_, ?_⟩
      · rw [← hStart]; exact hNotLt
      · rw [← hStart, ← hendPost]; exact hNotGe
  · simp only [spec_ok]
    intro k hk hin
    have hEq : lo.val = hi.val := by scalar_tac
    by_cases hkl : k < lo.val
    · have := hL k hk hkl
      exact absurd hin.2 (Nat.not_lt.mpr this)
    · have hkh : hi.val ≤ k := by omega
      have := hR k hk hkh
      exact absurd hin.1 (Nat.not_le.mpr this)

theorem find_clock_segment_wf_spec
    (segments : Slice (Std.U64 × Std.U64)) (clock : Std.U64)
    (hWf : WellFormedSegments segments) :
    clock_search.find_clock_segment segments clock ⦃ res =>
      (match res with
       | some idx =>
         ∃ h : idx.val < segments.length, inSeg (segments.val[idx.val]'h) clock
       | none =>
         ∀ (k : Nat) (hk : k < segments.length), ¬ inSeg (segments.val[k]) clock) ∧
      ((∃ (k : Nat) (hk : k < segments.length), inSeg (segments.val[k]) clock) ↔
        res.isSome) ⦄ := by
  unfold clock_search.find_clock_segment
  refine spec_mono (find_clock_segment_loop_complete segments clock hWf 0#usize (Slice.len segments)
    ⟨by scalar_tac, by scalar_tac⟩ (by intro k hk h; scalar_tac)
    (by intro k hk h; simp only [Slice.len_val] at h; omega)) ?_
  intro res hres
  refine ⟨hres, ?_⟩
  cases res with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, iff_false]
    rintro ⟨k, hk, hin⟩
    exact hres k hk hin
  | some idx =>
    simp only [Option.isSome_some, iff_true]
    exact ⟨idx.val, hres.1, hres.2⟩

end YoctoCore.Properties.ClockSearch
