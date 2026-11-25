import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.OrderRange

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.DeleteSet

/-- Canonical invariant for `DeleteSetCore`: entries sorted strictly by client ID,
    each entry carrying a canonical non-empty `OrderRange`. -/
def CanonicalList (l : List delete_set.DeleteSetEntry) : Prop :=
  (∀ (i : Nat) (hi : i < l.length),
    OrderRange.Canonical (l[i]).range ∧ 0 < (l[i]).range.ranges.length) ∧
  (∀ (i j : Nat) (hi : i < j) (hj : j < l.length),
    (l[i]).client.val < (l[j]).client.val)

def Canonical (ds : delete_set.DeleteSetCore) : Prop :=
  CanonicalList ds.entries.val

/-- Total number of `ClockRange` segments stored across all clients. -/
def totalRangesList : List delete_set.DeleteSetEntry → Nat
  | [] => 0
  | d :: rest => d.range.ranges.length + totalRangesList rest

def totalRanges (ds : delete_set.DeleteSetCore) : Nat :=
  totalRangesList ds.entries.val

/-- Membership semantics: `(client, clock)` is deleted iff `client` has an
    entry containing `clock`. -/
def memList (l : List delete_set.DeleteSetEntry) (client clock : Std.U64) : Prop :=
  ∃ (k : Nat) (hk : k < l.length),
    (l[k]).client = client ∧ OrderRange.inRanges (l[k]).range clock

def mem (ds : delete_set.DeleteSetCore) (client clock : Std.U64) : Prop :=
  memList ds.entries.val client clock

theorem totalRangesList_entry_le (l : List delete_set.DeleteSetEntry)
    (k : Nat) (hk : k < l.length) :
    (l[k]).range.ranges.length ≤ totalRangesList l := by
  induction l generalizing k with
  | nil => cases hk
  | cons hd tl ih =>
    cases k with
    | zero =>
      change hd.range.ranges.length ≤ hd.range.ranges.length + totalRangesList tl
      exact Nat.le_add_right _ _
    | succ m =>
      have hSub : ((hd :: tl)[m + 1]'hk).range.ranges.length =
          (tl[m]'(Nat.lt_of_succ_lt_succ hk)).range.ranges.length := rfl
      rw [hSub, totalRangesList]
      exact Nat.le_trans (ih m (Nat.lt_of_succ_lt_succ hk)) (Nat.le_add_left _ _)

theorem totalRangesList_length_le (l : List delete_set.DeleteSetEntry)
    (hNonEmpty : ∀ (i : Nat) (hi : i < l.length), 0 < (l[i]).range.ranges.length) :
    l.length ≤ totalRangesList l := by
  induction l with
  | nil => simp [totalRangesList]
  | cons hd tl ih =>
    have h0 : 0 < hd.range.ranges.length := hNonEmpty 0 (Nat.zero_lt_succ _)
    have hTl : ∀ (i : Nat) (hi : i < tl.length), 0 < (tl[i]).range.ranges.length :=
      fun i hi => hNonEmpty (i + 1) (Nat.succ_lt_succ hi)
    have hRec := ih hTl
    have hLen : (hd :: tl).length = tl.length + 1 := rfl
    rw [hLen, totalRangesList, Nat.add_comm tl.length 1]
    exact Nat.add_le_add h0 hRec

theorem totalRangesList_setAt (l : List delete_set.DeleteSetEntry)
    (idx : Nat) (hIdx : idx < l.length) (e : delete_set.DeleteSetEntry) :
    totalRangesList (l.set idx e) + (l[idx]).range.ranges.length =
      totalRangesList l + e.range.ranges.length := by
  induction l generalizing idx with
  | nil => cases hIdx
  | cons hd tl ih =>
    cases idx with
    | zero => simp [totalRangesList]; omega
    | succ m =>
      have := ih m (Nat.lt_of_succ_lt_succ hIdx)
      simp [totalRangesList] at *
      omega

theorem totalRangesList_insertIdx (l : List delete_set.DeleteSetEntry)
    (idx : Nat) (hIdx : idx ≤ l.length) (e : delete_set.DeleteSetEntry) :
    totalRangesList (l.insertIdx idx e) = totalRangesList l + e.range.ranges.length := by
  induction l generalizing idx with
  | nil =>
    have : idx = 0 := Nat.eq_zero_of_le_zero hIdx
    subst this
    simp [totalRangesList]
  | cons hd tl ih =>
    cases idx with
    | zero => simp [totalRangesList]; omega
    | succ m =>
      have := ih m (Nat.le_of_succ_le_succ hIdx)
      simp [List.insertIdx_succ_cons, totalRangesList] at *
      omega

theorem new_spec :
    delete_set.DeleteSetCore.new ⦃ ds =>
      Canonical ds ∧ ds.entries.length = 0 ∧ totalRanges ds = 0 ∧
      (∀ c clk, ¬ mem ds c clk) ⦄ := by
  unfold delete_set.DeleteSetCore.new
  simp only [spec_ok, Canonical, CanonicalList, totalRanges, totalRangesList, mem, memList]
  refine ⟨⟨by intro i hi; simp at hi, by intro i j hij hj; simp at hj⟩, by simp, rfl, ?_⟩
  intro c clk ⟨k, hk, _⟩
  simp at hk

theorem find_index_spec (self : delete_set.DeleteSetCore) (client : Std.U64)
    (hCan : Canonical self) :
    delete_set.DeleteSetCore.find_index self client ⦃ (found, idx) =>
      idx.val ≤ self.entries.length ∧
      (if found then
        ∃ h : idx.val < self.entries.length, (self.entries.val[idx.val]'h).client = client
       else
        (∀ (k : Nat) (hk : k < self.entries.length), k < idx.val →
          (self.entries.val[k]).client.val < client.val) ∧
        (∀ (k : Nat) (hk : k < self.entries.length), idx.val ≤ k →
          client.val < (self.entries.val[k]).client.val)) ⦄ := by
  unfold delete_set.DeleteSetCore.find_index delete_set.DeleteSetCore.find_index_loop
  let inv : Std.Usize × Std.Usize → Prop := fun (lo, hi) =>
    lo.val ≤ hi.val ∧ hi.val ≤ self.entries.length ∧
    (∀ (k : Nat) (hk : k < self.entries.length), k < lo.val →
      (self.entries.val[k]).client.val < client.val) ∧
    (∀ (k : Nat) (hk : k < self.entries.length), hi.val ≤ k →
      client.val < (self.entries.val[k]).client.val)
  refine loop.spec_decr_nat
    (fun (lo, hi) => hi.val - lo.val) inv _ _ (0#usize, alloc.vec.Vec.len self.entries) ?_
    ⟨by scalar_tac, by scalar_tac, by intro k hk h; scalar_tac, by intro k hk h; scalar_tac⟩
  intro ⟨lo, hi⟩ ⟨hLoHi, hHiLen, hL, hR⟩
  unfold delete_set.DeleteSetCore.find_index_loop.body
  simp only
  split_ifs with hlt
  · step as ⟨i, hiPost⟩
    step as ⟨i1, hi1Post⟩
    step as ⟨mid, hmidPost⟩
    step as ⟨dse, hdsePost⟩
    have hCval : dse.client.val = (self.entries.val[mid.val]'(by scalar_tac)).client.val := by
      rw [hdsePost]
    split_ifs with hcEq hcLt
    · try simp only [spec_ok, ↓reduceIte]
      refine ⟨by scalar_tac, by scalar_tac, ?_⟩
      apply UScalar.eq_of_val_eq
      have : dse.client.val = client.val := congrArg UScalar.val hcEq
      omega
    · step as ⟨low1, hlow1Post⟩
      try simp only [spec_ok]
      refine ⟨⟨by scalar_tac, hHiLen, ?_, hR⟩, by scalar_tac⟩
      intro k hk hkm
      have hk_le : k ≤ mid.val := by scalar_tac
      rcases eq_or_lt_of_le hk_le with rfl | hk_lt
      · rw [← hCval]; scalar_tac
      · exact Nat.lt_trans (hCan.2 k mid.val hk_lt (by scalar_tac)) (by rw [← hCval]; scalar_tac)
    · try simp only [spec_ok]
      refine ⟨⟨by scalar_tac, by scalar_tac, hL, ?_⟩, by scalar_tac⟩
      intro k hk hmk
      rcases eq_or_lt_of_le hmk with rfl | hgt
      · rw [← hCval]; scalar_tac
      · exact Nat.lt_trans (by rw [← hCval]; scalar_tac) (hCan.2 mid.val k hgt hk)
  · try simp only [spec_ok, Bool.false_eq_true, ↓reduceIte]
    have hEq : lo.val = hi.val := by scalar_tac
    refine ⟨by scalar_tac, hL, fun k hk h => hR k hk (by omega)⟩

theorem contains_spec (self : delete_set.DeleteSetCore) (client clock : Std.U64)
    (hCan : Canonical self) :
    delete_set.DeleteSetCore.contains self client clock ⦃ b =>
      b = true ↔ mem self client clock ⦄ := by
  unfold delete_set.DeleteSetCore.contains
  step with find_index_spec self client hCan as ⟨found, idx, hIdxLen, hFind⟩
  by_cases hfound : found = true
  · simp only [hfound, ↓reduceIte] at hFind ⊢
    rcases hFind with ⟨hIdxLt, hKey⟩
    step as ⟨dse, hdse⟩
    step with OrderRange.contains_spec dse.range clock (by rw [hdse]; exact (hCan.1 idx.val hIdxLt).1) as ⟨b, hb⟩
    try simp only [spec_ok]
    rw [hb]
    constructor
    · intro hin
      exact ⟨idx.val, hIdxLt, hKey, by rw [← hdse]; exact hin⟩
    · rintro ⟨k, hk, hck, hin⟩
      have hkeq : k = idx.val := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := hCan.2 k idx.val hlt hIdxLt
          rw [hKey, hck] at this; omega
        · have := hCan.2 idx.val k hgt hk
          rw [hKey, hck] at this; omega
      subst hkeq
      rw [hdse]; exact hin
  · simp only [hfound, Bool.false_eq_true, ↓reduceIte] at hFind ⊢
    simp only [spec_ok, Bool.false_eq_true, false_iff, mem, memList]
    rintro ⟨k, hk, hck, _⟩
    by_cases hkl : k < idx.val
    · have := hFind.1 k hk hkl; rw [hck] at this; omega
    · have := hFind.2 k hk (by omega); rw [hck] at this; omega

theorem insert_spec (self : delete_set.DeleteSetCore) (client start «end» : Std.U64)
    (hCan : Canonical self)
    (hCap : totalRanges self < Std.Usize.max) :
    delete_set.DeleteSetCore.insert self client start «end» ⦃ ds' =>
      Canonical ds' ∧
      totalRanges ds' ≤ totalRanges self + 1 ∧
      (∀ c clk, mem ds' c clk ↔
        mem self c clk ∨ (c = client ∧ start.val ≤ clk.val ∧ clk.val < «end».val)) ⦄ := by
  have hLenBound : self.entries.length < Std.Usize.max :=
    Nat.lt_of_le_of_lt (totalRangesList_length_le self.entries.val (fun i hi => (hCan.1 i hi).2)) hCap
  unfold delete_set.DeleteSetCore.insert
  split_ifs with hEmpty
  · simp only [spec_ok]
    refine ⟨hCan, Nat.le_succ _, fun c clk => ?_⟩
    constructor
    · exact Or.inl
    · rintro (h | ⟨_, h1, h2⟩)
      · exact h
      · exfalso; scalar_tac
  · have hSE : start.val < «end».val := by scalar_tac
    step with find_index_spec self client hCan as ⟨found, idx, hIdxLen, hFind⟩
    by_cases hfound : found = true
    · simp only [hfound, ↓reduceIte] at hFind ⊢
      rcases hFind with ⟨hIdxLt, hKey⟩
      step as ⟨dse, index_mut_back, hdse, hBack⟩
      have hOrCan : OrderRange.Canonical dse.range := by
        rw [hdse]; exact (hCan.1 idx.val hIdxLt).1
      have hOrLen : 0 < dse.range.ranges.length := by
        rw [hdse]; exact (hCan.1 idx.val hIdxLt).2
      have hOrCap : dse.range.ranges.length < Std.Usize.max := by
        have := totalRangesList_entry_le self.entries.val idx.val hIdxLt
        rw [← hdse] at this
        exact Nat.lt_of_le_of_lt this hCap
      step with OrderRange.insert_spec dse.range start «end» hOrCan hOrCap as ⟨or1, hor1Can, hor1Len, hor1Mem⟩
      try simp only [spec_ok]
      have hSetVal : (index_mut_back { dse with range := or1 }).val =
          self.entries.val.set idx.val { dse with range := or1 } := by
        rw [hBack]
        simp [alloc.vec.Vec.set]
      have hOr1NonEmpty : 0 < or1.ranges.length := by
        have : ∃ c, OrderRange.inRanges or1 c := by
          refine ⟨start, (hor1Mem start).2 (Or.inr ⟨le_refl _, hSE⟩)⟩
        rcases this with ⟨c, k, hk, _⟩
        exact Nat.lt_of_le_of_lt (Nat.zero_le k) hk
      refine ⟨?_, ?_, fun c clk => ?_⟩
      · constructor
        · intro i hi
          rw [hSetVal, List.length_set] at hi
          by_cases hii : i = idx.val
          · simp [hSetVal, hii, List.getElem_set_self, hor1Can, hOr1NonEmpty]
          · simp [hSetVal, List.getElem_set_ne (Ne.symm hii)]
            exact hCan.1 i hi
        · intro i j hij hj
          rw [hSetVal, List.length_set] at hj
          have hClientVal : dse.client.val = (self.entries.val[idx.val]'hIdxLt).client.val :=
            congrArg (fun e => e.client.val) hdse
          by_cases hii : i = idx.val
          · subst hii
            simp only [hSetVal, List.getElem_set_self, List.getElem_set_ne (Nat.ne_of_gt hij).symm]
            have := hCan.2 idx.val j hij hj
            rw [hClientVal]
            exact this
          · by_cases hji : j = idx.val
            · subst hji
              simp only [hSetVal, List.getElem_set_ne (Ne.symm hii), List.getElem_set_self]
              have := hCan.2 i idx.val hij hj
              rw [hClientVal]
              exact this
            · simp only [hSetVal, List.getElem_set_ne (Ne.symm hii), List.getElem_set_ne (Ne.symm hji)]
              exact hCan.2 i j hij hj
      · have hTot := totalRangesList_setAt self.entries.val idx.val hIdxLt { dse with range := or1 }
        simp only [totalRanges, hSetVal]
        dsimp only at hTot
        rw [← hdse] at hTot
        omega
      · simp only [mem, memList, hSetVal, List.length_set]
        constructor
        · rintro ⟨k, hk, hck, hin⟩
          by_cases hki : k = idx.val
          · subst hki
            simp only [List.getElem_set_self] at hck hin
            rw [hor1Mem clk] at hin
            rcases hin with hinOld | hNew
            · exact Or.inl ⟨idx.val, hIdxLt, by rw [hdse] at hck; exact hck, by rw [← hdse]; exact hinOld⟩
            · rw [hdse, hKey] at hck
              exact Or.inr ⟨hck.symm, hNew⟩
          · simp only [List.getElem_set_ne (Ne.symm hki)] at hck hin
            exact Or.inl ⟨k, hk, hck, hin⟩
        · rintro (⟨k, hk, hck, hin⟩ | ⟨rfl, h1, h2⟩)
          · by_cases hki : k = idx.val
            · subst hki
              refine ⟨idx.val, hIdxLt, ?_, ?_⟩
              · simp only [List.getElem_set_self]; rw [hdse]; exact hck
              · simp only [List.getElem_set_self]; rw [hor1Mem clk]; exact Or.inl (by rw [hdse]; exact hin)
            · refine ⟨k, hk, ?_⟩
              simp [List.getElem_set_ne (Ne.symm hki), hck, hin]
          · refine ⟨idx.val, hIdxLt, ?_, ?_⟩
            · simp [List.getElem_set_self, hdse, hKey]
            · simp only [List.getElem_set_self]
              exact (hor1Mem clk).2 (Or.inr ⟨h1, h2⟩)
    · simp only [hfound, Bool.false_eq_true, ↓reduceIte] at hFind ⊢
      have hFromSpec : order_range.OrderRange.from_range start «end» ⦃ or1 =>
          OrderRange.Canonical or1 ∧ or1.ranges.length = 1 ∧
          (∀ c, OrderRange.inRanges or1 c ↔ start.val ≤ c.val ∧ c.val < «end».val) ⦄ := by
        unfold order_range.OrderRange.from_range
        step with OrderRange.new_spec as ⟨r0, hr0Can, hr0Len, hr0Mem⟩
        step with OrderRange.insert_spec r0 start «end» hr0Can (by scalar_tac) as ⟨r1, hr1Can, hr1Len, hr1Mem⟩
        refine ⟨hr1Can, ?_, fun c => ?_⟩
        · have hLe1 : r1.ranges.length ≤ 1 := by omega
          have hPos1 : 0 < r1.ranges.length := by
            have : OrderRange.inRanges r1 start := (hr1Mem start).2 (Or.inr ⟨le_refl _, hSE⟩)
            rcases this with ⟨k, hk, _⟩
            exact Nat.lt_of_le_of_lt (Nat.zero_le k) hk
          omega
        · rw [hr1Mem c]
          constructor
          · rintro (h | h); exact absurd h (hr0Mem c); exact h
          · exact Or.inr
      step with hFromSpec as ⟨or1, hor1Can, hor1Len, hor1Mem⟩
      have hInsCan (hIdxLe : idx.val ≤ self.entries.length) :
          CanonicalList (self.entries.val.insertIdx idx.val { client, range := or1 }) := by
        have hLenIns : (self.entries.val.insertIdx idx.val { client, range := or1 }).length =
            self.entries.length + 1 := by
          simp [alloc.vec.Vec.length, List.length_insertIdx, hIdxLe]
        have get_ins (m : Nat) (hm : m < (self.entries.val.insertIdx idx.val { client, range := or1 }).length) :
            if m < idx.val then ∃ h : m < self.entries.length,
              (self.entries.val.insertIdx idx.val { client, range := or1 })[m] = self.entries.val[m]
            else if m = idx.val then
              (self.entries.val.insertIdx idx.val { client, range := or1 })[m] = { client, range := or1 }
            else ∃ h : m - 1 < self.entries.length,
              (self.entries.val.insertIdx idx.val { client, range := or1 })[m] = self.entries.val[m - 1] := by
          split_ifs with h1 h2
          · exact ⟨by omega, by simp [List.getElem_insertIdx_of_lt, h1]⟩
          · subst h2; exact by simp [List.getElem_insertIdx_self, hIdxLe]
          · exact ⟨by omega, by simp [List.getElem_insertIdx_of_gt, (by omega : idx.val < m)]⟩
        constructor
        · intro i hi
          have gi := get_ins i hi
          split_ifs at gi with h1 h2
          · rcases gi with ⟨hil, hgi⟩; rw [hgi]; exact hCan.1 i hil
          · rw [gi]; exact ⟨hor1Can, by simp [hor1Len]⟩
          · rcases gi with ⟨hil, hgi⟩; rw [hgi]; exact hCan.1 (i - 1) hil
        · intro i j hij hj
          have hi : i < (self.entries.val.insertIdx idx.val { client, range := or1 }).length :=
            Nat.lt_trans hij hj
          have gi := get_ins i hi
          have gj := get_ins j hj
          split_ifs at gi with hi1 hi2
          · rcases gi with ⟨hil, hgi⟩
            split_ifs at gj with hj1 hj2
            · rcases gj with ⟨hjl, hgj⟩; rw [hgi, hgj]; exact hCan.2 i j hij hjl
            · simp only [hj1, hj2, ↓reduceIte] at gj
              subst hj2
              rw [hgi, gj]; exact hFind.1 i hil hi1
            · rcases gj with ⟨hjl, hgj⟩; rw [hgi, hgj]; exact hCan.2 i (j - 1) (by omega) hjl
          · simp only [hi1, hi2, ↓reduceIte] at gi
            split_ifs at gj with hj1 hj2
            · omega
            · omega
            · rcases gj with ⟨hjl, hgj⟩
              subst hi2
              rw [gi, hgj]; exact hFind.2 (j - 1) hjl (by omega)
          · rcases gi with ⟨hil, hgi⟩
            split_ifs at gj with hj1 hj2
            · omega
            · omega
            · rcases gj with ⟨hjl, hgj⟩; rw [hgi, hgj]; exact hCan.2 (i - 1) (j - 1) (by omega) hjl
      have hInsMem (hIdxLe : idx.val ≤ self.entries.length) (c clk : Std.U64) :
          memList (self.entries.val.insertIdx idx.val { client, range := or1 }) c clk ↔
            mem self c clk ∨ (c = client ∧ start.val ≤ clk.val ∧ clk.val < «end».val) := by
        simp only [memList, mem]
        have hVLen : self.entries.val.length = self.entries.length := rfl
        have hIdxLeV : idx.val ≤ self.entries.val.length := by rw [hVLen]; exact hIdxLe
        have hLenIns :
            (self.entries.val.insertIdx idx.val { client, range := or1 }).length = self.entries.length + 1 := by
          simp [alloc.vec.Vec.length, List.length_insertIdx, hIdxLe]
        constructor
        · rintro ⟨k, hk, hck, hin⟩
          rw [hLenIns] at hk
          by_cases hk1 : k < idx.val
          · rw [List.getElem_insertIdx_of_lt hk1] at hck hin
            exact Or.inl ⟨k, by rw [hVLen]; omega, hck, hin⟩
          · by_cases hk2 : k = idx.val
            · subst hk2
              simp only [List.getElem_insertIdx_self, hIdxLeV] at hck hin
              rw [hor1Mem clk] at hin
              exact Or.inr ⟨hck.symm, hin⟩
            · rw [List.getElem_insertIdx_of_gt (by omega)] at hck hin
              exact Or.inl ⟨k - 1, by rw [hVLen]; omega, hck, hin⟩
        · rintro (⟨k, hk, hck, hin⟩ | ⟨rfl, h1, h2⟩)
          · by_cases hk1 : k < idx.val
            · refine ⟨k, by rw [hLenIns]; omega, ?_⟩
              rw [List.getElem_insertIdx_of_lt hk1]; exact ⟨hck, hin⟩
            · refine ⟨k + 1, by rw [hLenIns]; omega, ?_⟩
              rw [List.getElem_insertIdx_of_gt (by omega)]
              simpa using ⟨hck, hin⟩
          · refine ⟨idx.val, by rw [hLenIns]; omega, ?_⟩
            simp only [List.getElem_insertIdx_self, hIdxLeV]
            exact ⟨trivial, (hor1Mem clk).2 ⟨h1, h2⟩⟩
      by_cases hAtEnd : idx = alloc.vec.Vec.len self.entries
      · simp only [hAtEnd, ↓reduceIte]
        step as ⟨v, hvPost⟩
        try simp only [spec_ok]
        have hEqIdx : idx.val = self.entries.length := by scalar_tac
        have hPushEq : v.val = self.entries.val.insertIdx idx.val { client, range := or1 } := by
          rw [hEqIdx, List.insertIdx_length_self]; exact hvPost
        refine ⟨by simpa [Canonical, hPushEq] using hInsCan (by omega), ?_, ?_⟩
        · rw [totalRanges, hPushEq, totalRangesList_insertIdx _ _ (by omega)]
          simp [totalRanges, hor1Len]
        · intro c clk; simpa [mem, hPushEq] using hInsMem (by omega) c clk
      · simp only [hAtEnd, Bool.false_eq_true, ↓reduceIte]
        have hIdxLt : idx.val < self.entries.length := by scalar_tac
        step as ⟨v, hvPost⟩
        try simp only [spec_ok]
        refine ⟨?_, ?_, ?_⟩
        · rw [Canonical, hvPost]; exact hInsCan (Nat.le_of_lt hIdxLt)
        · rw [totalRanges, hvPost, totalRangesList_insertIdx _ _ (Nat.le_of_lt hIdxLt)]
          simp [totalRanges, hor1Len]
        · intro c clk; rw [mem, hvPost]; exact hInsMem (Nat.le_of_lt hIdxLt) c clk

theorem merge_spec (self other : delete_set.DeleteSetCore)
    (hCanSelf : Canonical self) (hCanOther : Canonical other)
    (hCap : totalRanges self + totalRanges other ≤ Std.Usize.max) :
    delete_set.DeleteSetCore.merge self other ⦃ ds' =>
      Canonical ds' ∧
      totalRanges ds' ≤ totalRanges self + totalRanges other ∧
      (∀ c clk, mem ds' c clk ↔ mem self c clk ∨ mem other c clk) ⦄ := by
  unfold delete_set.DeleteSetCore.merge delete_set.DeleteSetCore.merge_loop0
  -- Outer loop: invariant parameterized by entries processed [0..i)
  let prefixTot : Nat → Nat
    | i => totalRangesList (other.entries.val.take i)
  let prefixMem : Nat → Std.U64 → Std.U64 → Prop := fun i c clk =>
    memList (other.entries.val.take i) c clk
  let invOuter : delete_set.DeleteSetCore × Std.Usize → Prop := fun (ds, i) =>
    Canonical ds ∧ i.val ≤ other.entries.length ∧
    totalRanges ds ≤ totalRanges self + prefixTot i.val ∧
    (∀ c clk, mem ds c clk ↔ mem self c clk ∨ prefixMem i.val c clk)
  have hTakeAll : other.entries.val.take other.entries.length = other.entries.val := List.take_length
  refine loop.spec_decr_nat
    (fun (_, i) => other.entries.length - i.val)
    invOuter
    (fun ds' => Canonical ds' ∧ totalRanges ds' ≤ totalRanges self + totalRanges other ∧
      ∀ c clk, mem ds' c clk ↔ mem self c clk ∨ mem other c clk)
    _ (self, 0#usize) ?_
    ⟨hCanSelf, by scalar_tac, by simp [prefixTot, totalRangesList],
     fun c clk => by simp [prefixMem, memList]⟩
  intro ⟨ds, i⟩ ⟨hCanDs, hiLen, hTotDs, hMemDs⟩
  unfold delete_set.DeleteSetCore.merge_loop0.body
  simp only
  split_ifs with hlt
  · have hiLt : i.val < other.entries.length := by scalar_tac
    step*
    have hdse : dse = other.entries.val[i.val] := by assumption
    -- Inner loop spec over dse.range.ranges
    have hDseCan : OrderRange.Canonical dse.range := by
      rw [hdse]; exact (hCanOther.1 i.val hiLt).1
    have hPrefixRest :
        prefixTot i.val + dse.range.ranges.length ≤ totalRanges other := by
      -- take i ++ [dse] is take (i + 1) whose totalRanges ≤ totalRanges other
      have hTotSplit : ∀ (l : List delete_set.DeleteSetEntry) (k : Nat),
          totalRangesList (l.take k) ≤ totalRangesList l := by
        intro l k
        induction l generalizing k with
        | nil => simp [totalRangesList]
        | cons x xs ih =>
          cases k with
          | zero => simp [totalRangesList]
          | succ m =>
            simp only [List.take_succ_cons, totalRangesList]
            exact Nat.add_le_add_left (ih m) _
      have hTakeStep : other.entries.val.take (i.val + 1) =
          other.entries.val.take i.val ++ [other.entries.val[i.val]] :=
        List.take_succ_eq_append_getElem hiLt
      have hTotApp : ∀ l1 l2, totalRangesList (l1 ++ l2) = totalRangesList l1 + totalRangesList l2 := by
        intro l1 l2
        induction l1 with
        | nil => simp [totalRangesList]
        | cons x xs ih => simp [totalRangesList, ih, Nat.add_assoc]
      have hLe := hTotSplit other.entries.val (i.val + 1)
      rw [hTakeStep, hTotApp, ← hdse] at hLe
      simp only [totalRangesList, Nat.add_zero] at hLe
      simpa [prefixTot, totalRanges] using hLe
    have hInner :
        delete_set.DeleteSetCore.merge_loop0_loop0 ds other.entries i dse.client 0#usize ⦃ ds1 =>
          Canonical ds1 ∧
          totalRanges ds1 ≤ totalRanges ds + dse.range.ranges.length ∧
          (∀ c clk, mem ds1 c clk ↔
            mem ds c clk ∨
            (c = dse.client ∧
              OrderRange.inRanges dse.range clk)) ⦄ := by
      unfold delete_set.DeleteSetCore.merge_loop0_loop0
      let invIn : delete_set.DeleteSetCore × Std.Usize → Prop := fun (dsIn, j) =>
        Canonical dsIn ∧ j.val ≤ dse.range.ranges.length ∧
        totalRanges dsIn ≤ totalRanges ds + j.val ∧
        (∀ c clk, mem dsIn c clk ↔
          mem ds c clk ∨
          (c = dse.client ∧
            OrderRange.inRangesList (dse.range.ranges.val.take j.val) clk))
      refine loop.spec_decr_nat
        (fun (_, j) => dse.range.ranges.length - j.val)
        invIn _ _ (ds, 0#usize) ?_
        ⟨hCanDs, by scalar_tac, by scalar_tac, fun c clk => by simp [OrderRange.inRangesList]⟩
      intro ⟨dsIn, j⟩ ⟨hCanIn, hjLen, hTotIn, hMemIn⟩
      unfold delete_set.DeleteSetCore.merge_loop0_loop0.body
      simp only
      step as ⟨dse_1, hdse1⟩
      have hdse1Eq : dse_1 = dse := by rw [hdse1, hdse]
      split_ifs with hltIn
      · have hjLt : j.val < dse.range.ranges.length := by rw [← hdse1Eq]; scalar_tac
        have hCapIn : totalRanges dsIn < Std.Usize.max := by omega
        step as ⟨r, hrPost⟩
        have hrEq : r = dse.range.ranges.val[j.val] := by
          have : r = dse_1.range.ranges.val[j.val] := hrPost
          simpa [hdse1Eq] using this
        step with insert_spec dsIn dse.client r.start r.end hCanIn hCapIn as ⟨self1, hSelf1Can, hSelf1Len, hSelf1Mem⟩
        step as ⟨j1, hj1⟩
        try simp only [spec_ok]
        have hj1Val : j1.val = j.val + 1 := by scalar_tac
        refine ⟨⟨hSelf1Can, by scalar_tac, by omega, fun c clk => ?_⟩, by scalar_tac⟩
        rw [hj1Val, hSelf1Mem c clk, hMemIn c clk]
        have hTakeJ : OrderRange.inRangesList (dse.range.ranges.val.take (j.val + 1)) clk ↔
            OrderRange.inRangesList (dse.range.ranges.val.take j.val) clk ∨
            (r.start.val ≤ clk.val ∧ clk.val < r.end.val) := by
          simp only [OrderRange.inRangesList]
          rw [List.take_succ_eq_append_getElem hjLt, hrEq]
          have hTLen : (dse.range.ranges.val.take j.val).length = j.val := by
            simp [List.length_take]; omega
          constructor
          · rintro ⟨k, hk, h1', h2'⟩
            simp only [List.length_append, List.length_cons, List.length_nil, hTLen] at hk
            by_cases hkj : k < j.val
            · rw [List.getElem_append_left (by omega)] at h1' h2'
              exact Or.inl ⟨k, by omega, h1', h2'⟩
            · have hkeq : k = j.val := by omega
              subst hkeq
              rw [List.getElem_append_right (by omega)] at h1' h2'
              simp only [hTLen, Nat.sub_self, List.getElem_cons_zero] at h1' h2'
              exact Or.inr ⟨h1', h2'⟩
          · rintro (⟨k, hk, h1', h2'⟩ | ⟨h1', h2'⟩)
            · refine ⟨k, by simp only [List.length_append, List.length_cons, List.length_nil, hTLen]; omega, ?_⟩
              rw [List.getElem_append_left hk]; exact ⟨h1', h2'⟩
            · refine ⟨j.val, by simp only [List.length_append, List.length_cons, List.length_nil, hTLen]; omega, ?_⟩
              rw [List.getElem_append_right (by omega)]
              simp only [hTLen, Nat.sub_self, List.getElem_cons_zero]
              exact ⟨h1', h2'⟩
        constructor
        · rintro ((hOld | ⟨rfl, hPre⟩) | ⟨rfl, hNew⟩)
          · exact Or.inl hOld
          · exact Or.inr ⟨rfl, (hTakeJ).2 (Or.inl hPre)⟩
          · exact Or.inr ⟨rfl, (hTakeJ).2 (Or.inr hNew)⟩
        · rintro (hOld | ⟨rfl, hPreNew⟩)
          · exact Or.inl (Or.inl hOld)
          · rcases (hTakeJ).1 hPreNew with hPre | hNew
            · exact Or.inl (Or.inr ⟨rfl, hPre⟩)
            · exact Or.inr ⟨rfl, hNew⟩
      · try simp only [spec_ok]
        have heq : j.val = dse.range.ranges.length := by rw [← hdse1Eq]; scalar_tac
        have hTotEnd : totalRanges dsIn ≤ totalRanges ds + dse.range.ranges.length := by
          rw [← heq]; exact hTotIn
        refine ⟨hCanIn, hTotEnd, fun c clk => ?_⟩
        rw [hMemIn c clk]
        simp [OrderRange.inRanges, heq, List.take_length]
    step with hInner as ⟨ds1, hDs1Can, hDs1Tot, hDs1Mem⟩
    step as ⟨i2, hi2⟩
    try simp only [spec_ok]
    have hi2Val : i2.val = i.val + 1 := by scalar_tac
    have hTotApp : ∀ l1 l2, totalRangesList (l1 ++ l2) = totalRangesList l1 + totalRangesList l2 := by
      intro l1 l2
      induction l1 with
      | nil => simp [totalRangesList]
      | cons x xs ih => simp [totalRangesList, ih, Nat.add_assoc]
    have hTakeStep : other.entries.val.take (i.val + 1) =
        other.entries.val.take i.val ++ [other.entries.val[i.val]] :=
      List.take_succ_eq_append_getElem hiLt
    refine ⟨⟨hDs1Can, by scalar_tac, ?_, fun c clk => ?_⟩, by scalar_tac⟩
    · have : prefixTot (i.val + 1) = prefixTot i.val + dse.range.ranges.length := by
        simp only [prefixTot, hTakeStep, hTotApp, totalRangesList, Nat.add_zero, hdse]
      rw [hi2Val]
      omega
    · rw [hi2Val, hDs1Mem c clk, hMemDs c clk]
      have hMemStep : prefixMem (i.val + 1) c clk ↔
          prefixMem i.val c clk ∨ (c = dse.client ∧ OrderRange.inRanges dse.range clk) := by
        simp only [prefixMem, memList]
        rw [hTakeStep, hdse]
        have hTLen : (other.entries.val.take i.val).length = i.val := by
          simp [List.length_take]; omega
        constructor
        · rintro ⟨k, hk, hck, hin⟩
          simp only [List.length_append, List.length_cons, List.length_nil, hTLen] at hk
          by_cases hki : k < i.val
          · rw [List.getElem_append_left (by omega)] at hck hin
            exact Or.inl ⟨k, by omega, hck, hin⟩
          · have hkeq : k = i.val := by omega
            subst hkeq
            rw [List.getElem_append_right (by omega)] at hck hin
            simp only [hTLen, Nat.sub_self, List.getElem_cons_zero] at hck hin
            exact Or.inr ⟨hck.symm, hin⟩
        · rintro (⟨k, hk, hck, hin⟩ | ⟨rfl, hin⟩)
          · refine ⟨k, by simp only [List.length_append, List.length_cons, List.length_nil, hTLen]; omega, ?_⟩
            rw [List.getElem_append_left hk]; exact ⟨hck, hin⟩
          · refine ⟨i.val, by simp only [List.length_append, List.length_cons, List.length_nil, hTLen]; omega, ?_⟩
            rw [List.getElem_append_right (by omega)]
            simp only [hTLen, Nat.sub_self, List.getElem_cons_zero]
            exact ⟨trivial, hin⟩
      rw [hMemStep]
      tauto
  · simp only [spec_ok]
    have heq : i.val = other.entries.length := by scalar_tac
    refine ⟨hCanDs, by simpa [prefixTot, heq, totalRanges, hTakeAll] using hTotDs, fun c clk => ?_⟩
    rw [hMemDs c clk]
    simp [prefixMem, mem, heq, hTakeAll]

theorem merge_comm (a b : delete_set.DeleteSetCore)
    (hCanA : Canonical a) (hCanB : Canonical b)
    (hCapAB : totalRanges a + totalRanges b ≤ Std.Usize.max)
    (hCapBA : totalRanges b + totalRanges a ≤ Std.Usize.max) :
    (do
      let ab ← delete_set.DeleteSetCore.merge a b
      let ba ← delete_set.DeleteSetCore.merge b a
      ok (ab, ba)) ⦃ (ab, ba) => ∀ c clk, mem ab c clk ↔ mem ba c clk ⦄ := by
  step with merge_spec a b hCanA hCanB hCapAB as ⟨ab, _, _, habMem⟩
  step with merge_spec b a hCanB hCanA hCapBA as ⟨ba, _, _, hbaMem⟩
  try simp only [spec_ok]
  intro c clk
  rw [habMem c clk, hbaMem c clk]
  exact or_comm

theorem merge_idem (a : delete_set.DeleteSetCore)
    (hCan : Canonical a)
    (hCap : totalRanges a + totalRanges a ≤ Std.Usize.max) :
    delete_set.DeleteSetCore.merge a a ⦃ aa => ∀ c clk, mem aa c clk ↔ mem a c clk ⦄ := by
  refine spec_mono (merge_spec a a hCan hCan hCap) ?_
  intro aa ⟨_, _, hMem⟩ c clk
  rw [hMem c clk]
  exact iff_of_eq (or_self _)

end YoctoCore.Properties.DeleteSet
