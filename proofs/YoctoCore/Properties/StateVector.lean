import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.StateVector

/-- Canonical invariant for `StateVectorCore`: entries are sorted in strictly
    increasing order of client ID. -/
def CanonicalList (l : List (Std.U64 × Std.U64)) : Prop :=
  ∀ (i j : Nat) (hi : i < j) (hj : j < l.length), (l[i]).1.val < (l[j]).1.val

def Canonical (sv : state_vector.StateVectorCore) : Prop :=
  CanonicalList sv.entries.val

/-- Semantic map from client ID to its recorded clock (defaulting to `0`). -/
def svClockList : List (Std.U64 × Std.U64) → Std.U64 → Nat
  | [], _ => 0
  | (c, clk) :: rest, target => if c = target then clk.val else svClockList rest target

def svClock (sv : state_vector.StateVectorCore) (c : Std.U64) : Nat :=
  svClockList sv.entries.val c

attribute [local instance] Classical.propDecidable

/-- Whether a client key is explicitly stored in `l`. -/
def hasClientList : List (Std.U64 × Std.U64) → Std.U64 → Prop
  | [], _ => False
  | (c, _) :: rest, target => c = target ∨ hasClientList rest target

def hasClient (sv : state_vector.StateVectorCore) (c : Std.U64) : Prop :=
  hasClientList sv.entries.val c

theorem canonicalList_tail {hd : Std.U64 × Std.U64} {tl : List (Std.U64 × Std.U64)}
    (h : CanonicalList (hd :: tl)) : CanonicalList tl := by
  intro i j hij hj
  exact h (i + 1) (j + 1) (Nat.succ_lt_succ hij) (Nat.succ_lt_succ hj)

theorem hasClientList_iff_exists (l : List (Std.U64 × Std.U64)) (c : Std.U64) :
    hasClientList l c ↔ ∃ (k : Nat) (hk : k < l.length), (l[k]).1 = c := by
  induction l with
  | nil => simp [hasClientList]
  | cons hd tl ih =>
    simp only [hasClientList, ih]
    constructor
    · rintro (rfl | ⟨k, hk, hEq⟩)
      · exact ⟨0, Nat.zero_lt_succ _, rfl⟩
      · exact ⟨k + 1, Nat.succ_lt_succ hk, hEq⟩
    · rintro ⟨k, hk, hEq⟩
      cases k with
      | zero => exact Or.inl hEq
      | succ m => exact Or.inr ⟨m, Nat.lt_of_succ_lt_succ hk, hEq⟩

theorem svClockList_idx_of_unique
    (l : List (Std.U64 × Std.U64)) (hSorted : CanonicalList l)
    (idx : Nat) (hIdx : idx < l.length) :
    svClockList l (l[idx]).1 = (l[idx]).2.val ∧
    hasClientList l (l[idx]).1 := by
  induction l generalizing idx with
  | nil => cases hIdx
  | cons hd tl ih =>
    cases idx with
    | zero => simp [svClockList, hasClientList]
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hIdx
      have hNe : hd.1 ≠ (tl[k]).1 := by
        have hlt := hSorted 0 (k + 1) (Nat.zero_lt_succ k) (Nat.succ_lt_succ hk)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hlt
        intro heq
        have : hd.1.val = (tl[k]).1.val := congrArg UScalar.val heq
        omega
      have ⟨h1, h2⟩ := ih (canonicalList_tail hSorted) k hk
      simp only [List.getElem_cons_succ, svClockList, hasClientList, if_neg hNe]
      exact ⟨h1, Or.inr h2⟩

theorem svClockList_absent
    (l : List (Std.U64 × Std.U64)) (c : Std.U64)
    (hAbs : ∀ (k : Nat) (hk : k < l.length), (l[k]).1 ≠ c) :
    svClockList l c = 0 ∧ ¬ hasClientList l c := by
  induction l with
  | nil => simp [svClockList, hasClientList]
  | cons hd tl ih =>
    have hHd : hd.1 ≠ c := hAbs 0 (Nat.zero_lt_succ _)
    have hTl : ∀ (k : Nat) (hk : k < tl.length), (tl[k]).1 ≠ c :=
      fun k hk => hAbs (k + 1) (Nat.succ_lt_succ hk)
    have ⟨h1, h2⟩ := ih hTl
    simp only [svClockList, hasClientList, hHd, ↓reduceIte, false_or]
    exact ⟨h1, h2⟩

theorem svClockList_setAt
    (l : List (Std.U64 × Std.U64)) (hSorted : CanonicalList l)
    (idx : Nat) (hIdx : idx < l.length) (clk : Std.U64) (c : Std.U64) :
    svClockList (l.set idx ((l[idx]).1, clk)) c =
      if c = (l[idx]).1 then clk.val else svClockList l c := by
  induction l generalizing idx with
  | nil => cases hIdx
  | cons hd tl ih =>
    cases idx with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero, svClockList]
      by_cases hc : c = hd.1
      · simp [hc]
      · simp [hc, Ne.symm hc]
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hIdx
      have hIh := ih (canonicalList_tail hSorted) k hk
      simp only [List.set_cons_succ, List.getElem_cons_succ, svClockList]
      by_cases hhd : hd.1 = c
      · have hne : c ≠ (tl[k]).1 := by
          have hlt := hSorted 0 (k + 1) (Nat.zero_lt_succ k) (Nat.succ_lt_succ hk)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hlt
          intro heq
          subst hhd
          have : hd.1.val = (tl[k]).1.val := congrArg UScalar.val heq
          omega
        simp [hhd, hne]
      · simp [hhd, hIh]

theorem hasClientList_setAt
    (l : List (Std.U64 × Std.U64)) (idx : Nat) (hIdx : idx < l.length)
    (clk : Std.U64) (c : Std.U64) :
    hasClientList (l.set idx ((l[idx]).1, clk)) c ↔ hasClientList l c := by
  rw [hasClientList_iff_exists, hasClientList_iff_exists]
  constructor
  · rintro ⟨k, hk, hEq⟩
    simp only [List.length_set] at hk
    refine ⟨k, hk, ?_⟩
    by_cases hki : k = idx
    · subst hki; simpa using hEq
    · simpa [List.getElem_set_ne (Ne.symm hki)] using hEq
  · rintro ⟨k, hk, hEq⟩
    refine ⟨k, by simpa [List.length_set] using hk, ?_⟩
    by_cases hki : k = idx
    · subst hki; simpa using hEq
    · simpa [List.getElem_set_ne (Ne.symm hki)] using hEq

theorem svClockList_insertIdx
    (l : List (Std.U64 × Std.U64)) (idx : Nat) (hIdx : idx ≤ l.length)
    (client clock : Std.U64) (hFresh : ¬ hasClientList l client) (c : Std.U64) :
    svClockList (l.insertIdx idx (client, clock)) c =
      if c = client then clock.val else svClockList l c := by
  induction l generalizing idx with
  | nil =>
    have : idx = 0 := Nat.eq_zero_of_le_zero hIdx
    subst this
    simp [List.insertIdx, svClockList, eq_comm]
  | cons hd tl ih =>
    have hNeHd : hd.1 ≠ client := fun h => hFresh (Or.inl h)
    have hFreshTl : ¬ hasClientList tl client := fun h => hFresh (Or.inr h)
    cases idx with
    | zero =>
      simp only [List.insertIdx_zero, svClockList]
      by_cases hc : c = client
      · simp [hc, eq_comm]
      · simp [hc, Ne.symm hc]
    | succ k =>
      have hk : k ≤ tl.length := Nat.le_of_succ_le_succ hIdx
      simp only [List.insertIdx_succ_cons, svClockList]
      by_cases hhd : hd.1 = c
      · have hne : c ≠ client := fun h => hNeHd (hhd.trans h)
        simp [hhd, hne]
      · simp [hhd, ih k hk hFreshTl]

theorem hasClientList_insertIdx
    (l : List (Std.U64 × Std.U64)) (idx : Nat) (hIdx : idx ≤ l.length)
    (client clock : Std.U64) (c : Std.U64) :
    hasClientList (l.insertIdx idx (client, clock)) c ↔ c = client ∨ hasClientList l c := by
  induction l generalizing idx with
  | nil =>
    have : idx = 0 := Nat.eq_zero_of_le_zero hIdx
    subst this
    simp [List.insertIdx, hasClientList, eq_comm]
  | cons hd tl ih =>
    cases idx with
    | zero => simp [List.insertIdx, hasClientList, eq_comm]
    | succ k =>
      have hk : k ≤ tl.length := Nat.le_of_succ_le_succ hIdx
      simp only [List.insertIdx_succ_cons, hasClientList, ih k hk]
      tauto

theorem canonicalList_setAt
    (l : List (Std.U64 × Std.U64)) (hSorted : CanonicalList l)
    (idx : Nat) (hIdx : idx < l.length) (clk : Std.U64) :
    CanonicalList (l.set idx ((l[idx]).1, clk)) := by
  intro i j hij hj
  have hj' : j < l.length := by simpa [List.length_set] using hj
  have hi : i < l.length := Nat.lt_trans hij hj'
  by_cases h1 : i = idx
  · subst h1
    have h2 : j ≠ i := Nat.ne_of_gt hij
    simp only [List.getElem_set_self, List.getElem_set_ne (Ne.symm h2)]
    exact hSorted i j hij hj'
  · by_cases h2 : j = idx
    · subst h2
      simp only [List.getElem_set_ne (Ne.symm h1), List.getElem_set_self]
      exact hSorted i j hij hj'
    · simp only [List.getElem_set_ne (Ne.symm h1), List.getElem_set_ne (Ne.symm h2)]
      exact hSorted i j hij hj'

theorem canonicalList_insertIdx
    (l : List (Std.U64 × Std.U64)) (hSorted : CanonicalList l)
    (idx : Nat) (hIdx : idx ≤ l.length) (client clock : Std.U64)
    (hL : ∀ (k : Nat) (hk : k < l.length), k < idx → (l[k]).1.val < client.val)
    (hR : ∀ (k : Nat) (hk : k < l.length), idx ≤ k → client.val < (l[k]).1.val) :
    CanonicalList (l.insertIdx idx (client, clock)) := by
  intro i j hij hj
  have hLen : (l.insertIdx idx (client, clock)).length = l.length + 1 := by
    simp [List.length_insertIdx, hIdx]
  have hi : i < (l.insertIdx idx (client, clock)).length := Nat.lt_trans hij hj
  have hIl : i < l.length + 1 := by omega
  have hJl : j < l.length + 1 := by omega
  by_cases hi1 : i < idx
  · have hil : i < l.length := by omega
    have hgi : (l.insertIdx idx (client, clock))[i] = l[i] := by
      simp [List.getElem_insertIdx_of_lt, hi1]
    by_cases hj1 : j < idx
    · have hjl : j < l.length := by omega
      have hgj : (l.insertIdx idx (client, clock))[j] = l[j] := by
        simp [List.getElem_insertIdx_of_lt, hj1]
      rw [hgi, hgj]
      exact hSorted i j hij hjl
    · by_cases hj2 : j = idx
      · have hgj : (l.insertIdx idx (client, clock))[j] = (client, clock) := by
          simp [hj2, List.getElem_insertIdx_self, hIdx]
        rw [hgi, hgj]
        exact hL i hil (by omega)
      · have hjgt : idx < j := by omega
        have hjl : j - 1 < l.length := by omega
        have hgj : (l.insertIdx idx (client, clock))[j] = l[j - 1] := by
          simp [List.getElem_insertIdx_of_gt, hjgt]
        rw [hgi, hgj]
        exact hSorted i (j - 1) (by omega) hjl
  · by_cases hi2 : i = idx
    · have hgi : (l.insertIdx idx (client, clock))[i] = (client, clock) := by
        simp [hi2, List.getElem_insertIdx_self, hIdx]
      have hjgt : idx < j := by omega
      have hjl : j - 1 < l.length := by omega
      have hgj : (l.insertIdx idx (client, clock))[j] = l[j - 1] := by
        simp [List.getElem_insertIdx_of_gt, hjgt]
      rw [hgi, hgj]
      exact hR (j - 1) hjl (by omega)
    · have higt : idx < i := by omega
      have hjgt : idx < j := by omega
      have hil : i - 1 < l.length := by omega
      have hjl : j - 1 < l.length := by omega
      have hgi : (l.insertIdx idx (client, clock))[i] = l[i - 1] := by
        simp [List.getElem_insertIdx_of_gt, higt]
      have hgj : (l.insertIdx idx (client, clock))[j] = l[j - 1] := by
        simp [List.getElem_insertIdx_of_gt, hjgt]
      rw [hgi, hgj]
      exact hSorted (i - 1) (j - 1) (by omega) hjl

theorem find_index_spec (self : state_vector.StateVectorCore) (client : Std.U64)
    (hCan : Canonical self) :
    state_vector.StateVectorCore.find_index self client ⦃ (found, idx) =>
      idx.val ≤ self.entries.length ∧
      (if found then
        ∃ h : idx.val < self.entries.length, (self.entries.val[idx.val]'h).1 = client
       else
        (∀ (k : Nat) (hk : k < self.entries.length), k < idx.val →
          (self.entries.val[k]).1.val < client.val) ∧
        (∀ (k : Nat) (hk : k < self.entries.length), idx.val ≤ k →
          client.val < (self.entries.val[k]).1.val)) ⦄ := by
  unfold state_vector.StateVectorCore.find_index state_vector.StateVectorCore.find_index_loop
  let inv : Std.Usize × Std.Usize → Prop := fun (lo, hi) =>
    lo.val ≤ hi.val ∧ hi.val ≤ self.entries.length ∧
    (∀ (k : Nat) (hk : k < self.entries.length), k < lo.val →
      (self.entries.val[k]).1.val < client.val) ∧
    (∀ (k : Nat) (hk : k < self.entries.length), hi.val ≤ k →
      client.val < (self.entries.val[k]).1.val)
  refine loop.spec_decr_nat
    (fun (lo, hi) => hi.val - lo.val) inv _ _ (0#usize, alloc.vec.Vec.len self.entries) ?_
    ⟨by scalar_tac, by scalar_tac, by intro k hk h; scalar_tac, by intro k hk h; scalar_tac⟩
  intro ⟨lo, hi⟩ ⟨hLoHi, hHiLen, hL, hR⟩
  unfold state_vector.StateVectorCore.find_index_loop.body
  simp only
  split_ifs with hlt
  · step as ⟨i, hiPost⟩
    step as ⟨i1, hi1Post⟩
    step as ⟨mid, hmidPost⟩
    step as ⟨p, clk, hpPost⟩
    have hcEqVal : p = (self.entries.val[mid.val]'(by scalar_tac)).1 := by
      simpa using congrArg Prod.fst hpPost
    have hCval : p.val = (self.entries.val[mid.val]'(by scalar_tac)).1.val := by
      rw [hcEqVal]
    split_ifs with hcEq hcLt
    · try simp only [spec_ok, ↓reduceIte]
      refine ⟨by scalar_tac, by scalar_tac, ?_⟩
      apply UScalar.eq_of_val_eq
      have : p.val = client.val := congrArg UScalar.val hcEq
      omega
    · step as ⟨low1, hlow1Post⟩
      try simp only [spec_ok]
      refine ⟨⟨by scalar_tac, hHiLen, ?_, hR⟩, by scalar_tac⟩
      intro k hk hkm
      have hk_le : k ≤ mid.val := by scalar_tac
      rcases eq_or_lt_of_le hk_le with rfl | hk_lt
      · rw [← hCval]; scalar_tac
      · exact Nat.lt_trans (hCan k mid.val hk_lt (by scalar_tac)) (by rw [← hCval]; scalar_tac)
    · try simp only [spec_ok]
      refine ⟨⟨by scalar_tac, by scalar_tac, hL, ?_⟩, by scalar_tac⟩
      intro k hk hmk
      rcases eq_or_lt_of_le hmk with rfl | hgt
      · rw [← hCval]; scalar_tac
      · exact Nat.lt_trans (by rw [← hCval]; scalar_tac) (hCan mid.val k hgt hk)
  · try simp only [spec_ok, Bool.false_eq_true, ↓reduceIte]
    have hEq : lo.val = hi.val := by scalar_tac
    refine ⟨by scalar_tac, hL, ?_⟩
    intro k hk hlk
    exact hR k hk (by omega)

theorem new_spec :
    state_vector.StateVectorCore.new ⦃ sv =>
      Canonical sv ∧ sv.entries.length = 0 ∧
      (∀ c, svClock sv c = 0 ∧ ¬ hasClient sv c) ⦄ := by
  unfold state_vector.StateVectorCore.new
  simp only [spec_ok, Canonical, CanonicalList, svClock, hasClient]
  refine ⟨?_, by simp, fun c => by simp [svClockList, hasClientList]⟩
  intro i j hij hj
  simp at hj

theorem get_spec (self : state_vector.StateVectorCore) (client : Std.U64)
    (hCan : Canonical self) :
    state_vector.StateVectorCore.get self client ⦃ clk =>
      clk.val = svClock self client ⦄ := by
  unfold state_vector.StateVectorCore.get
  step with find_index_spec self client hCan as ⟨found, idx, hIdxLen, hFind⟩
  by_cases hfound : found = true
  · simp only [hfound, ↓reduceIte] at hFind ⊢
    rcases hFind with ⟨hIdxLt, hKey⟩
    step as ⟨c', clk', hIdxEq⟩
    try simp only [spec_ok]
    have hClkEq : clk'.val = (self.entries.val[idx.val]'hIdxLt).2.val := by
      have : clk' = (self.entries.val[idx.val]'hIdxLt).2 := by
        simpa using congrArg Prod.snd hIdxEq
      rw [this]
    have ⟨hEq, _⟩ := svClockList_idx_of_unique self.entries.val hCan idx.val hIdxLt
    rw [hKey] at hEq
    rw [hClkEq, svClock, hEq]
  · simp only [hfound, Bool.false_eq_true, ↓reduceIte] at hFind ⊢
    simp only [spec_ok]
    have hAbs : ∀ (k : Nat) (hk : k < self.entries.length), (self.entries.val[k]).1 ≠ client := by
      intro k hk heq
      by_cases hkl : k < idx.val
      · have := hFind.1 k hk hkl
        have : (self.entries.val[k]).1.val = client.val := congrArg UScalar.val heq
        omega
      · have := hFind.2 k hk (by omega)
        have : (self.entries.val[k]).1.val = client.val := congrArg UScalar.val heq
        omega
    have ⟨h0, _⟩ := svClockList_absent self.entries.val client hAbs
    simp [svClock, h0]

theorem contains_spec (self : state_vector.StateVectorCore) (client clock : Std.U64)
    (hCan : Canonical self) :
    state_vector.StateVectorCore.contains self client clock ⦃ b =>
      b = true ↔ clock.val ≤ svClock self client ⦄ := by
  unfold state_vector.StateVectorCore.contains
  step with get_spec self client hCan as ⟨clk, hClk⟩
  simp only [spec_ok, decide_eq_true_eq]
  rw [← hClk]
  constructor
  · intro h; scalar_tac
  · intro h; apply Nat.le_of_lt_succ; scalar_tac

theorem set_spec (self : state_vector.StateVectorCore) (client clock : Std.U64)
    (hCan : Canonical self) (hCap : self.entries.length < Std.Usize.max) :
    state_vector.StateVectorCore.set self client clock ⦃ sv' =>
      Canonical sv' ∧
      sv'.entries.length ≤ self.entries.length + 1 ∧
      (∀ c, hasClient sv' c ↔ c = client ∨ hasClient self c) ∧
      (∀ c, svClock sv' c = if c = client then clock.val else svClock self c) ⦄ := by
  unfold state_vector.StateVectorCore.set
  step with find_index_spec self client hCan as ⟨found, idx, hIdxLen, hFind⟩
  by_cases hfound : found = true
  · simp only [hfound, ↓reduceIte] at hFind ⊢
    rcases hFind with ⟨hIdxLt, hKey⟩
    have ⟨hGet, hHas⟩ := svClockList_idx_of_unique self.entries.val hCan idx.val hIdxLt
    rw [hKey] at hGet hHas
    step as ⟨i1, i2, index_mut_back, hpMut, hBack⟩
    try dsimp only
    try simp only [spec_ok]
    have hpFst : i1 = client := by
      simpa [hKey] using congrArg UScalar.val (congrArg Prod.fst hpMut) |> UScalar.eq_of_val_eq
    have hSetVal : (index_mut_back (i1, clock)).val = self.entries.val.set idx.val (client, clock) := by
      rw [hBack, hpFst]
      simp [alloc.vec.Vec.set]
    refine ⟨?_, by simp [hSetVal], ?_, ?_⟩
    · simpa [Canonical, hSetVal, hKey] using canonicalList_setAt self.entries.val hCan idx.val hIdxLt clock
    · intro c
      have hEq := hasClientList_setAt self.entries.val idx.val hIdxLt clock c
      simp only [hKey] at hEq
      simp only [hasClient, hSetVal, hEq]
      exact ⟨fun h => Or.inr h, fun h => by rcases h with rfl | h; exact hHas; exact h⟩
    · intro c
      have hSet := svClockList_setAt self.entries.val hCan idx.val hIdxLt clock c
      simp only [hKey] at hSet
      simp only [svClock, hSetVal, hSet]
  · simp only [hfound, Bool.false_eq_true, ↓reduceIte] at hFind ⊢
    have hAbs : ∀ (k : Nat) (hk : k < self.entries.length), (self.entries.val[k]).1 ≠ client := by
      intro k hk heq
      by_cases hkl : k < idx.val
      · have := hFind.1 k hk hkl
        have : (self.entries.val[k]).1.val = client.val := congrArg UScalar.val heq
        omega
      · have := hFind.2 k hk (by omega)
        have : (self.entries.val[k]).1.val = client.val := congrArg UScalar.val heq
        omega
    have ⟨hClock0, hNotHas⟩ := svClockList_absent self.entries.val client hAbs
    by_cases hAtEnd : idx = alloc.vec.Vec.len self.entries
    · simp only [hAtEnd, ↓reduceIte]
      step as ⟨v, hvPost⟩
      try simp only [spec_ok]
      have hEqIdx : idx.val = self.entries.length := by scalar_tac
      have hPushEq : v.val = self.entries.val.insertIdx self.entries.length (client, clock) := by
        rw [List.insertIdx_length_self]; exact hvPost
      refine ⟨?_, by scalar_tac, ?_, ?_⟩
      · rw [Canonical, hPushEq]
        refine canonicalList_insertIdx self.entries.val hCan self.entries.length (le_refl _) client clock ?_ ?_
        · intro k hk hkl; exact hFind.1 k hk (by omega)
        · intro k hk hkr; simp only [alloc.vec.Vec.length] at *; omega
      · intro c
        simpa [hasClient, hPushEq] using
          hasClientList_insertIdx self.entries.val self.entries.length (le_refl _) client clock c
      · intro c
        have hIns := svClockList_insertIdx self.entries.val self.entries.length (le_refl _) client clock hNotHas c
        simp only [svClock, hPushEq, hIns]
    · simp only [hAtEnd, Bool.false_eq_true, ↓reduceIte]
      have hIdxLt : idx.val < self.entries.length := by scalar_tac
      step as ⟨v, hvPost⟩
      try simp only [spec_ok]
      refine ⟨?_, by simp [alloc.vec.Vec.length, hvPost, List.length_insertIdx, Nat.le_of_lt hIdxLt], ?_, ?_⟩
      · rw [Canonical, hvPost]
        exact canonicalList_insertIdx self.entries.val hCan idx.val (Nat.le_of_lt hIdxLt) client clock hFind.1 hFind.2
      · intro c
        rw [hasClient, hvPost]
        exact hasClientList_insertIdx self.entries.val idx.val (Nat.le_of_lt hIdxLt) client clock c
      · intro c
        have hIns := svClockList_insertIdx self.entries.val idx.val (Nat.le_of_lt hIdxLt) client clock hNotHas c
        simp only [svClock, hvPost, hIns]

theorem set_max_spec (self : state_vector.StateVectorCore) (client clock : Std.U64)
    (hCan : Canonical self) (hCap : self.entries.length < Std.Usize.max) :
    state_vector.StateVectorCore.set_max self client clock ⦃ sv' =>
      Canonical sv' ∧
      sv'.entries.length ≤ self.entries.length + 1 ∧
      (∀ c, hasClient sv' c ↔ c = client ∨ hasClient self c) ∧
      (∀ c, svClock sv' c =
        if c = client then max (svClock self client) clock.val else svClock self c) ⦄ := by
  unfold state_vector.StateVectorCore.set_max
  step with find_index_spec self client hCan as ⟨found, idx, hIdxLen, hFind⟩
  by_cases hfound : found = true
  · simp only [hfound, ↓reduceIte] at hFind ⊢
    rcases hFind with ⟨hIdxLt, hKey⟩
    have ⟨hGet, hHas⟩ := svClockList_idx_of_unique self.entries.val hCan idx.val hIdxLt
    rw [hKey] at hGet hHas
    step as ⟨_, i, hIdxGet⟩
    have hiEq : i.val = (self.entries.val[idx.val]'hIdxLt).2.val := by
      simpa using congrArg UScalar.val (congrArg Prod.snd hIdxGet)
    by_cases hlt : i < clock
    · -- existing < clock
      simp only [hlt, ↓reduceIte]
      have hILt : i.val < clock.val := by scalar_tac
      step as ⟨i1, i2, index_mut_back, hpMut, hBack⟩
      try dsimp only
      try simp only [spec_ok]
      have hpFst : i1 = client := by
        simpa [hKey] using congrArg UScalar.val (congrArg Prod.fst hpMut) |> UScalar.eq_of_val_eq
      have hSetVal : (index_mut_back (i1, clock)).val = self.entries.val.set idx.val (client, clock) := by
        rw [hBack, hpFst]
        simp [alloc.vec.Vec.set]
      refine ⟨?_, by simp [Canonical, hSetVal], ?_, ?_⟩
      · simpa [Canonical, hSetVal, hKey] using canonicalList_setAt self.entries.val hCan idx.val hIdxLt clock
      · intro c
        have hEq := hasClientList_setAt self.entries.val idx.val hIdxLt clock c
        simp only [hKey] at hEq
        simp only [hasClient, hSetVal, hEq]
        exact ⟨fun h => Or.inr h, fun h => by rcases h with rfl | h; exact hHas; exact h⟩
      · intro c
        have hSet := svClockList_setAt self.entries.val hCan idx.val hIdxLt clock c
        simp only [hKey] at hSet
        simp only [svClock, hSetVal, hSet, hGet]
        split_ifs with hc
        · subst hc; omega
        · rfl
    · -- existing >= clock
      simp only [hlt, ↓reduceIte]
      have hIGe : clock.val ≤ i.val := by scalar_tac
      try simp only [spec_ok]
      refine ⟨hCan, Nat.le_succ _, ?_, ?_⟩
      · intro c; constructor
        · exact Or.inr
        · rintro (rfl | h); exact hHas; exact h
      · intro c
        split_ifs with hc
        · subst hc; simp only [svClock, hGet]; omega
        · rfl
  · simp only [hfound, Bool.false_eq_true, ↓reduceIte] at hFind ⊢
    have hAbs : ∀ (k : Nat) (hk : k < self.entries.length), (self.entries.val[k]).1 ≠ client := by
      intro k hk heq
      by_cases hkl : k < idx.val
      · have := hFind.1 k hk hkl
        have : (self.entries.val[k]).1.val = client.val := congrArg UScalar.val heq
        omega
      · have := hFind.2 k hk (by omega)
        have : (self.entries.val[k]).1.val = client.val := congrArg UScalar.val heq
        omega
    have ⟨hClock0, hNotHas⟩ := svClockList_absent self.entries.val client hAbs
    by_cases hAtEnd : idx = alloc.vec.Vec.len self.entries
    · simp only [hAtEnd, ↓reduceIte]
      -- Vec.push
      step as ⟨v, hvPost⟩
      try simp only [spec_ok]
      have hEqIdx : idx.val = self.entries.length := by scalar_tac
      have hPushEq : v.val = self.entries.val.insertIdx self.entries.length (client, clock) := by
        rw [List.insertIdx_length_self]; exact hvPost
      refine ⟨?_, by scalar_tac, ?_, ?_⟩
      · rw [Canonical, hPushEq]
        refine canonicalList_insertIdx self.entries.val hCan self.entries.length (le_refl _) client clock ?_ ?_
        · intro k hk hkl; exact hFind.1 k hk (by omega)
        · intro k hk hkr; simp only [alloc.vec.Vec.length] at *; omega
      · intro c
        simpa [hasClient, hPushEq] using
          hasClientList_insertIdx self.entries.val self.entries.length (le_refl _) client clock c
      · intro c
        have hIns := svClockList_insertIdx self.entries.val self.entries.length (le_refl _) client clock hNotHas c
        simp only [svClock, hPushEq, hIns, hClock0, Nat.zero_max]
    · simp only [hAtEnd, Bool.false_eq_true, ↓reduceIte]
      -- Vec.insert (idx < len)
      have hIdxLt : idx.val < self.entries.length := by scalar_tac
      step as ⟨v, hvPost⟩
      try simp only [spec_ok]
      refine ⟨?_, by simp [alloc.vec.Vec.length, hvPost, List.length_insertIdx, Nat.le_of_lt hIdxLt], ?_, ?_⟩
      · rw [Canonical, hvPost]
        exact canonicalList_insertIdx self.entries.val hCan idx.val (Nat.le_of_lt hIdxLt) client clock hFind.1 hFind.2
      · intro c
        rw [hasClient, hvPost]
        exact hasClientList_insertIdx self.entries.val idx.val (Nat.le_of_lt hIdxLt) client clock c
      · intro c
        have hIns := svClockList_insertIdx self.entries.val idx.val (Nat.le_of_lt hIdxLt) client clock hNotHas c
        simp only [svClock, hvPost, hIns, hClock0, Nat.zero_max]

theorem set_min_spec (self : state_vector.StateVectorCore) (client clock : Std.U64)
    (hCan : Canonical self) (hCap : self.entries.length < Std.Usize.max) :
    state_vector.StateVectorCore.set_min self client clock ⦃ sv' =>
      Canonical sv' ∧
      sv'.entries.length ≤ self.entries.length + 1 ∧
      (∀ c, hasClient sv' c ↔ c = client ∨ hasClient self c) ∧
      (∀ c, svClock sv' c =
        if c = client then
          (if hasClient self client then min (svClock self client) clock.val else clock.val)
        else svClock self c) ⦄ := by
  unfold state_vector.StateVectorCore.set_min
  step with find_index_spec self client hCan as ⟨found, idx, hIdxLen, hFind⟩
  by_cases hfound : found = true
  · simp only [hfound, ↓reduceIte] at hFind ⊢
    rcases hFind with ⟨hIdxLt, hKey⟩
    have ⟨hGet, hHas⟩ := svClockList_idx_of_unique self.entries.val hCan idx.val hIdxLt
    rw [hKey] at hGet hHas
    step as ⟨_, i, hIdxGet⟩
    have hiEq : i.val = (self.entries.val[idx.val]'hIdxLt).2.val := by
      simpa using congrArg UScalar.val (congrArg Prod.snd hIdxGet)
    by_cases hlt : i > clock
    · -- existing > clock
      simp only [hlt, ↓reduceIte]
      have hIGt : clock.val < i.val := by scalar_tac
      step as ⟨i1, i2, index_mut_back, hpMut, hBack⟩
      try dsimp only
      try simp only [spec_ok]
      have hpFst : i1 = client := by
        simpa [hKey] using congrArg UScalar.val (congrArg Prod.fst hpMut) |> UScalar.eq_of_val_eq
      have hSetVal : (index_mut_back (i1, clock)).val = self.entries.val.set idx.val (client, clock) := by
        rw [hBack, hpFst]
        simp [alloc.vec.Vec.set]
      refine ⟨?_, by simp [Canonical, hSetVal], ?_, ?_⟩
      · simpa [Canonical, hSetVal, hKey] using canonicalList_setAt self.entries.val hCan idx.val hIdxLt clock
      · intro c
        have hEq := hasClientList_setAt self.entries.val idx.val hIdxLt clock c
        simp only [hKey] at hEq
        simp only [hasClient, hSetVal, hEq]
        exact ⟨fun h => Or.inr h, fun h => by rcases h with rfl | h; exact hHas; exact h⟩
      · intro c
        have hSet := svClockList_setAt self.entries.val hCan idx.val hIdxLt clock c
        simp only [hKey] at hSet
        simp only [svClock, hSetVal, hSet, hGet]
        by_cases hc : c = client
        · subst hc; simp only [↓reduceIte, hasClient, hHas]; omega
        · simp only [hc, ↓reduceIte]
    · -- existing <= clock
      simp only [hlt, ↓reduceIte]
      have hILe : i.val ≤ clock.val := by scalar_tac
      try simp only [spec_ok]
      refine ⟨hCan, Nat.le_succ _, ?_, ?_⟩
      · intro c; constructor
        · exact Or.inr
        · rintro (rfl | h); exact hHas; exact h
      · intro c
        by_cases hc : c = client
        · subst hc; simp only [↓reduceIte, svClock, hasClient, hHas, hGet]; omega
        · simp only [hc, ↓reduceIte]
  · simp only [hfound, Bool.false_eq_true, ↓reduceIte] at hFind ⊢
    have hAbs : ∀ (k : Nat) (hk : k < self.entries.length), (self.entries.val[k]).1 ≠ client := by
      intro k hk heq
      by_cases hkl : k < idx.val
      · have := hFind.1 k hk hkl
        have : (self.entries.val[k]).1.val = client.val := congrArg UScalar.val heq
        omega
      · have := hFind.2 k hk (by omega)
        have : (self.entries.val[k]).1.val = client.val := congrArg UScalar.val heq
        omega
    have ⟨hClock0, hNotHas⟩ := svClockList_absent self.entries.val client hAbs
    by_cases hAtEnd : idx = alloc.vec.Vec.len self.entries
    · simp only [hAtEnd, ↓reduceIte]
      step as ⟨v, hvPost⟩
      try simp only [spec_ok]
      have hEqIdx : idx.val = self.entries.length := by scalar_tac
      have hPushEq : v.val = self.entries.val.insertIdx self.entries.length (client, clock) := by
        rw [List.insertIdx_length_self]; exact hvPost
      refine ⟨?_, by scalar_tac, ?_, ?_⟩
      · rw [Canonical, hPushEq]
        refine canonicalList_insertIdx self.entries.val hCan self.entries.length (le_refl _) client clock ?_ ?_
        · intro k hk hkl; exact hFind.1 k hk (by omega)
        · intro k hk hkr; simp only [alloc.vec.Vec.length] at *; omega
      · intro c
        simpa [hasClient, hPushEq] using
          hasClientList_insertIdx self.entries.val self.entries.length (le_refl _) client clock c
      · intro c
        have hIns := svClockList_insertIdx self.entries.val self.entries.length (le_refl _) client clock hNotHas c
        rw [svClock, hPushEq, hIns]
        by_cases hc : c = client
        · subst hc; simp [hasClient, hNotHas]
        · simp only [hc, ↓reduceIte, svClock]
    · simp only [hAtEnd, Bool.false_eq_true, ↓reduceIte]
      have hIdxLt : idx.val < self.entries.length := by scalar_tac
      step as ⟨v, hvPost⟩
      try simp only [spec_ok]
      refine ⟨?_, by simp [alloc.vec.Vec.length, hvPost, List.length_insertIdx, Nat.le_of_lt hIdxLt], ?_, ?_⟩
      · rw [Canonical, hvPost]
        exact canonicalList_insertIdx self.entries.val hCan idx.val (Nat.le_of_lt hIdxLt) client clock hFind.1 hFind.2
      · intro c
        rw [hasClient, hvPost]
        exact hasClientList_insertIdx self.entries.val idx.val (Nat.le_of_lt hIdxLt) client clock c
      · intro c
        have hIns := svClockList_insertIdx self.entries.val idx.val (Nat.le_of_lt hIdxLt) client clock hNotHas c
        rw [svClock, hvPost, hIns]
        by_cases hc : c = client
        · subst hc; simp [hasClient, hNotHas]
        · simp only [hc, ↓reduceIte, svClock]

theorem set_max_mono (self : state_vector.StateVectorCore) (client clock c : Std.U64)
    (hCan : Canonical self) (hCap : self.entries.length < Std.Usize.max) :
    state_vector.StateVectorCore.set_max self client clock ⦃ sv' =>
      svClock self c ≤ svClock sv' c ⦄ := by
  refine spec_mono (set_max_spec self client clock hCan hCap) ?_
  intro sv' ⟨_, _, _, hClk⟩
  rw [hClk c]
  split_ifs with hc
  · subst hc; exact Nat.le_max_left _ _
  · exact Nat.le_refl _

theorem svClockList_take_succ
    (l : List (Std.U64 × Std.U64)) (hSorted : CanonicalList l)
    (i : Nat) (hi : i < l.length) (x : Std.U64) :
    svClockList (l.take (i + 1)) x =
      if x = (l[i]).1 then (l[i]).2.val else svClockList (l.take i) x := by
  induction l generalizing i with
  | nil => cases hi
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp [List.take, svClockList, eq_comm]
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hi
      have hIh := ih (canonicalList_tail hSorted) k hk
      simp only [List.take_succ_cons, List.getElem_cons_succ, svClockList]
      by_cases hhd : hd.1 = x
      · have hne : x ≠ (tl[k]).1 := by
          have hlt := hSorted 0 (k + 1) (Nat.zero_lt_succ k) (Nat.succ_lt_succ hk)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hlt
          intro heq
          subst hhd
          have : hd.1.val = (tl[k]).1.val := congrArg UScalar.val heq
          omega
        simp [hhd, hne]
      · simp [hhd, hIh]

theorem merge_max_spec (self other : state_vector.StateVectorCore)
    (hCanSelf : Canonical self) (hCanOther : Canonical other)
    (hCap : self.entries.length + other.entries.length ≤ Std.Usize.max) :
    state_vector.StateVectorCore.merge_max self other ⦃ sv' =>
      Canonical sv' ∧
      (∀ c, svClock sv' c = max (svClock self c) (svClock other c)) ⦄ := by
  unfold state_vector.StateVectorCore.merge_max state_vector.StateVectorCore.merge_max_loop
  let prefixMax : Nat → Std.U64 → Nat := fun i c =>
    Nat.max (svClock self c) (svClockList (other.entries.val.take i) c)
  let inv : state_vector.StateVectorCore × Std.Usize → Prop := fun (sv, i) =>
    Canonical sv ∧ i.val ≤ other.entries.length ∧
    sv.entries.length ≤ self.entries.length + i.val ∧
    (∀ c, svClock sv c = prefixMax i.val c)
  have hTakeAll : other.entries.val.take other.entries.length = other.entries.val := List.take_length
  refine loop.spec_decr_nat
    (fun (_, i) => other.entries.length - i.val)
    inv
    (fun sv' => Canonical sv' ∧ ∀ c, svClock sv' c = max (svClock self c) (svClock other c))
    _ (self, 0#usize) ?_ ?_
  · intro ⟨sv, i⟩ ⟨hCan, hiLen, hSvLen, hClk⟩
    unfold state_vector.StateVectorCore.merge_max_loop.body
    simp only
    split_ifs with hlt
    · have hiLt : i.val < other.entries.length := by scalar_tac
      have hCapStep : sv.entries.length < Std.Usize.max := by omega
      step as ⟨c, clk, hcClk⟩
      have ⟨hOtherClk, _⟩ := svClockList_idx_of_unique other.entries.val hCanOther i.val hiLt
      step with set_max_spec sv c clk hCan hCapStep as ⟨self1, hSelf1Can, hSelf1Len, hSelf1Has, hSelf1Clk⟩
      step as ⟨i2, hi2⟩
      try simp only [spec_ok]
      have hi2Val : i2.val = i.val + 1 := by scalar_tac
      refine ⟨?_, by scalar_tac⟩
      refine ⟨hSelf1Can, by scalar_tac, by omega, fun x => ?_⟩
      rw [hSelf1Clk x, hClk x, hClk c]
      have hTakeSucc := svClockList_take_succ other.entries.val hCanOther i.val hiLt x
      have hEntryEq : other.entries.val[i.val] = (c, clk) := hcClk.symm
      simp only [prefixMax] at *
      rw [hi2Val, hTakeSucc, hEntryEq]
      split_ifs with hxc
      · have hAbsTake : ∀ (k : Nat) (hk : k < (other.entries.val.take i.val).length),
            ((other.entries.val.take i.val)[k]).1 ≠ c := by
          intro k hk heq
          have hkLt : k < i.val := by
            simp only [List.length_take] at hk
            exact lt_of_lt_of_le hk (Nat.min_le_left _ _)
          have hlt2 := hCanOther k i.val hkLt hiLt
          have heq2 : (other.entries.val[k]'(lt_trans hkLt hiLt)).1 = c := by
            simpa [List.getElem_take] using heq
          have : (other.entries.val[k]'(lt_trans hkLt hiLt)).1.val = c.val := congrArg UScalar.val heq2
          have : (other.entries.val[i.val]).1 = c := by rw [hEntryEq]
          have : (other.entries.val[i.val]).1.val = c.val := congrArg UScalar.val this
          omega
        have hZero := (svClockList_absent (other.entries.val.take i.val) c hAbsTake).1
        rw [hxc, hZero]
        simp
      · rfl
    · simp only [spec_ok]
      have heq : i.val = other.entries.length := by scalar_tac
      refine ⟨hCan, fun x => ?_⟩
      rw [hClk x]
      simp [prefixMax, heq, svClock, hTakeAll]
  · refine ⟨hCanSelf, by scalar_tac, by scalar_tac, fun c => by simp [prefixMax, svClockList]⟩

theorem set_max_idem (self : state_vector.StateVectorCore) (client clock : Std.U64)
    (hCan : Canonical self) (hCap : self.entries.length + 1 < Std.Usize.max) :
    (do
      let sv1 ← state_vector.StateVectorCore.set_max self client clock
      let sv2 ← state_vector.StateVectorCore.set_max sv1 client clock
      ok (sv1, sv2)) ⦃ (sv1, sv2) => ∀ c, svClock sv1 c = svClock sv2 c ⦄ := by
  step with set_max_spec self client clock hCan (by omega) as ⟨sv1, hsv1Can, hsv1Len, hsv1Has, hsv1Clk⟩
  step with set_max_spec sv1 client clock hsv1Can (by omega) as ⟨sv2, hsv2Can, hsv2Len, hsv2Has, hsv2Clk⟩
  try simp only [spec_ok]
  intro c
  by_cases hc : c = client
  · subst hc
    rw [hsv2Clk c, if_pos rfl, hsv1Clk c, if_pos rfl, Nat.max_assoc, Nat.max_self]
  · rw [hsv2Clk c, if_neg hc]

theorem merge_max_comm (a b : state_vector.StateVectorCore)
    (hCanA : Canonical a) (hCanB : Canonical b)
    (hCapAB : a.entries.length + b.entries.length ≤ Std.Usize.max)
    (hCapBA : b.entries.length + a.entries.length ≤ Std.Usize.max) :
    (do
      let ab ← state_vector.StateVectorCore.merge_max a b
      let ba ← state_vector.StateVectorCore.merge_max b a
      ok (ab, ba)) ⦃ (ab, ba) => ∀ c, svClock ab c = svClock ba c ⦄ := by
  step with merge_max_spec a b hCanA hCanB hCapAB as ⟨ab, habCan, habClk⟩
  step with merge_max_spec b a hCanB hCanA hCapBA as ⟨ba, hbaCan, hbaClk⟩
  try simp only [spec_ok]
  intro c
  rw [habClk c, hbaClk c, Nat.max_comm]

theorem merge_max_idem (a : state_vector.StateVectorCore)
    (hCan : Canonical a)
    (hCap : a.entries.length + a.entries.length ≤ Std.Usize.max) :
    state_vector.StateVectorCore.merge_max a a ⦃ aa =>
      ∀ c, svClock aa c = svClock a c ⦄ := by
  refine spec_mono (merge_max_spec a a hCan hCan hCap) ?_
  intro aa ⟨_, hClk⟩ c
  rw [hClk c, Nat.max_self]

theorem hasClientList_take_succ
    (l : List (Std.U64 × Std.U64))
    (i : Nat) (hi : i < l.length) (x : Std.U64) :
    hasClientList (l.take (i + 1)) x ↔ x = (l[i]).1 ∨ hasClientList (l.take i) x := by
  induction l generalizing i with
  | nil => cases hi
  | cons hd tl ih =>
    cases i with
    | zero => simp [List.take, hasClientList, eq_comm]
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hi
      have hIh := ih k hk
      simp only [List.take_succ_cons, List.getElem_cons_succ, hasClientList, hIh]
      tauto

theorem merge_with_spec (self other : state_vector.StateVectorCore)
    (hCanSelf : Canonical self) (hCanOther : Canonical other)
    (hCap : self.entries.length + other.entries.length ≤ Std.Usize.max) :
    state_vector.StateVectorCore.merge_with self other ⦃ sv' =>
      Canonical sv' ∧
      (∀ c, hasClient sv' c ↔ hasClient self c ∨ hasClient other c) ∧
      (∀ c, svClock sv' c =
        if hasClient self c ∧ hasClient other c then min (svClock self c) (svClock other c)
        else if hasClient self c then svClock self c
        else svClock other c) ⦄ := by
  unfold state_vector.StateVectorCore.merge_with state_vector.StateVectorCore.merge_with_loop
  let prefixHas : Nat → Std.U64 → Prop := fun i c =>
    hasClientList (other.entries.val.take i) c
  let prefixClk : Nat → Std.U64 → Nat := fun i c =>
    svClockList (other.entries.val.take i) c
  let prefixMerge : Nat → Std.U64 → Nat := fun i c =>
    if hasClient self c ∧ prefixHas i c then min (svClock self c) (prefixClk i c)
    else if hasClient self c then svClock self c
    else prefixClk i c
  let inv : state_vector.StateVectorCore × Std.Usize → Prop := fun (sv, i) =>
    Canonical sv ∧ i.val ≤ other.entries.length ∧
    sv.entries.length ≤ self.entries.length + i.val ∧
    (∀ c, hasClient sv c ↔ hasClient self c ∨ prefixHas i.val c) ∧
    (∀ c, svClock sv c = prefixMerge i.val c)
  have hTakeAll : other.entries.val.take other.entries.length = other.entries.val := List.take_length
  refine loop.spec_decr_nat
    (fun (_, i) => other.entries.length - i.val)
    inv
    (fun sv' =>
      Canonical sv' ∧
      (∀ c, hasClient sv' c ↔ hasClient self c ∨ hasClient other c) ∧
      (∀ c, svClock sv' c =
        if hasClient self c ∧ hasClient other c then min (svClock self c) (svClock other c)
        else if hasClient self c then svClock self c
        else svClock other c))
    _ (self, 0#usize) ?_ ?_
  · intro ⟨sv, i⟩ ⟨hCan, hiLen, hSvLen, hHas, hClk⟩
    unfold state_vector.StateVectorCore.merge_with_loop.body
    simp only
    split_ifs with hlt
    · have hiLt : i.val < other.entries.length := by scalar_tac
      have hCapStep : sv.entries.length < Std.Usize.max := by omega
      step as ⟨c, clk, hcClk⟩
      step with set_min_spec sv c clk hCan hCapStep as ⟨self1, hSelf1Can, hSelf1Len, hSelf1Has, hSelf1Clk⟩
      step as ⟨i2, hi2⟩
      try simp only [spec_ok]
      have hi2Val : i2.val = i.val + 1 := by scalar_tac
      have hEntryEq : other.entries.val[i.val] = (c, clk) := hcClk.symm
      refine ⟨⟨hSelf1Can, by scalar_tac, by omega, ?_, ?_⟩, by scalar_tac⟩
      · intro x
        have hSucc := hasClientList_take_succ other.entries.val i.val hiLt x
        simp only [prefixHas, hi2Val, hSucc, hEntryEq]
        rw [hSelf1Has x, hHas x]
        tauto
      · intro x
        rw [hSelf1Clk x, hClk x, hHas c, hClk c]
        have hSuccHas := hasClientList_take_succ other.entries.val i.val hiLt x
        have hSuccClk := svClockList_take_succ other.entries.val hCanOther i.val hiLt x
        have hAbsTake : ∀ (k : Nat) (hk : k < (other.entries.val.take i.val).length),
            ((other.entries.val.take i.val)[k]).1 ≠ c := by
          intro k hk heq
          have hkLt : k < i.val := by
            simp only [List.length_take] at hk
            exact lt_of_lt_of_le hk (Nat.min_le_left _ _)
          have hlt2 := hCanOther k i.val hkLt hiLt
          have heq2 : (other.entries.val[k]'(lt_trans hkLt hiLt)).1 = c := by
            simpa [List.getElem_take] using heq
          have : (other.entries.val[k]'(lt_trans hkLt hiLt)).1.val = c.val := congrArg UScalar.val heq2
          have : (other.entries.val[i.val]).1 = c := by rw [hEntryEq]
          have : (other.entries.val[i.val]).1.val = c.val := congrArg UScalar.val this
          omega
        have hAbsC := svClockList_absent (other.entries.val.take i.val) c hAbsTake
        simp only [prefixMerge, prefixHas, prefixClk, hi2Val, hSuccHas, hSuccClk, hEntryEq] at *
        by_cases hxc : x = c
        · subst hxc
          simp only [↓reduceIte, true_or, hAbsC.1, hAbsC.2, false_and, or_false]
          by_cases hs : hasClient self x
          · simp [hs]
          · simp [hs]
        · simp only [hxc, ↓reduceIte, false_or]
    · simp only [spec_ok]
      have heq : i.val = other.entries.length := by scalar_tac
      refine ⟨hCan, ?_, ?_⟩
      · intro x; rw [hHas x]; simp [prefixHas, hasClient, heq, hTakeAll]
      · intro x; rw [hClk x]
        simp only [prefixMerge, prefixHas, prefixClk, hasClient, svClock, heq, hTakeAll]
        by_cases hs : hasClientList self.entries.val x <;>
          by_cases ho : hasClientList other.entries.val x <;>
          simp [hs, ho]
  · refine ⟨hCanSelf, by scalar_tac, by scalar_tac, ?_, ?_⟩
    · intro c; simp [prefixHas, hasClientList]
    · intro c
      by_cases hs : hasClient self c
      · simp [prefixMerge, prefixHas, prefixClk, hasClientList, svClockList, hs]
      · have hAbs : ∀ (k : Nat) (hk : k < self.entries.val.length), (self.entries.val[k]'hk).1 ≠ c := by
          intro k hk heq
          exact hs ((hasClientList_iff_exists self.entries.val c).mpr ⟨k, hk, heq⟩)
        have h0 : svClock self c = 0 := (svClockList_absent self.entries.val c hAbs).1
        simp [prefixMerge, prefixHas, prefixClk, hasClientList, svClockList, hs, h0]

theorem set_max_comm (self : state_vector.StateVectorCore) (c1 k1 c2 k2 : Std.U64)
    (hCan : Canonical self) (hCap : self.entries.length + 2 ≤ Std.Usize.max) :
    (do
      let sv1 ← state_vector.StateVectorCore.set_max self c1 k1
      let sv12 ← state_vector.StateVectorCore.set_max sv1 c2 k2
      let sv2 ← state_vector.StateVectorCore.set_max self c2 k2
      let sv21 ← state_vector.StateVectorCore.set_max sv2 c1 k1
      ok (sv12, sv21)) ⦃ (sv12, sv21) => ∀ c, svClock sv12 c = svClock sv21 c ⦄ := by
  step with set_max_spec self c1 k1 hCan (by omega) as ⟨sv1, hCan1, hLen1, _, hClk1⟩
  step with set_max_spec sv1 c2 k2 hCan1 (by omega) as ⟨sv12, _, _, _, hClk12⟩
  step with set_max_spec self c2 k2 hCan (by omega) as ⟨sv2, hCan2, hLen2, _, hClk2⟩
  step with set_max_spec sv2 c1 k1 hCan2 (by omega) as ⟨sv21, _, _, _, hClk21⟩
  try simp only [spec_ok]
  intro c
  by_cases hc1 : c = c1
  · subst hc1
    by_cases hc2 : c = c2
    · subst hc2
      simp [hClk12, hClk21, hClk1, hClk2]
      omega
    · simp [hClk12, hClk21, hClk1, hClk2, hc2]
  · by_cases hc2 : c = c2
    · subst hc2
      simp [hClk12, hClk21, hClk1, hClk2, hc1]
    · simp [hClk12, hClk21, hClk1, hClk2, hc1, hc2]

end YoctoCore.Properties.StateVector
