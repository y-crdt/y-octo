import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 2000000

namespace YoctoCore.Properties.Utf16

/-- UTF-8 lead-byte step size (`1`, `2`, `3`, or `4`) matching
    `utf16_len` and `utf16_split_byte_offset`. -/
def leadStep (b : Std.U8) : Nat :=
  if b.val < 128 then 1
  else if b.val < 224 then 2
  else if b.val < 240 then 3
  else 4

def leadUnits (b : Std.U8) : Nat :=
  if leadStep b = 4 then 2 else 1

theorem leadUnits_le_leadStep (b : Std.U8) : leadUnits b ≤ leadStep b := by
  simp only [leadUnits, leadStep]
  split_ifs <;> omega

theorem leadStep_pos (b : Std.U8) : 1 ≤ leadStep b := by
  simp only [leadStep]
  split_ifs <;> omega

/-- Pure list-level UTF-16 length specification for valid/prefix-stepped byte sequences. -/
def utf16LenList : List Std.U8 → Nat
  | [] => 0
  | b :: rest =>
    if h : 1 + rest.length < leadStep b then 0
    else
      have : (rest.drop (leadStep b - 1)).length < rest.length + 1 := by
        simp only [List.length_drop]
        have hs := leadStep_pos b
        omega
      leadUnits b + utf16LenList (rest.drop (leadStep b - 1))
termination_by l => l.length

/-- Pure boolean UTF-8 validity check over a byte list, matching `utf8_char_step`. -/
def isValidUtf8List : List Std.U8 → Bool
  | [] => true
  | b0 :: rest =>
    if b0.val < 128 then isValidUtf8List rest
    else if 194 ≤ b0.val ∧ b0.val ≤ 223 then
      match rest with
      | b1 :: r1 => (128 ≤ b1.val ∧ b1.val ≤ 191) && isValidUtf8List r1
      | [] => false
    else if 224 ≤ b0.val ∧ b0.val ≤ 239 then
      match rest with
      | b1 :: b2 :: r2 =>
        let ok1 :=
          if b0.val = 224 then 160 ≤ b1.val ∧ b1.val ≤ 191
          else if b0.val = 237 then 128 ≤ b1.val ∧ b1.val ≤ 159
          else 128 ≤ b1.val ∧ b1.val ≤ 191
        ok1 && decide (128 ≤ b2.val ∧ b2.val ≤ 191) && isValidUtf8List r2
      | _ => false
    else if 240 ≤ b0.val ∧ b0.val ≤ 244 then
      match rest with
      | b1 :: b2 :: b3 :: r3 =>
        let ok1 :=
          if b0.val = 240 then 144 ≤ b1.val ∧ b1.val ≤ 191
          else if b0.val = 244 then 128 ≤ b1.val ∧ b1.val ≤ 143
          else 128 ≤ b1.val ∧ b1.val ≤ 191
        ok1 && decide (128 ≤ b2.val ∧ b2.val ≤ 191) &&
          decide (128 ≤ b3.val ∧ b3.val ≤ 191) && isValidUtf8List r3
      | _ => false
    else false
termination_by l => l.length

theorem isValidUtf8List_cons (b0 : Std.U8) (rest : List Std.U8) :
    isValidUtf8List (b0 :: rest) =
      (if b0.val < 128 then isValidUtf8List rest
       else if 194 ≤ b0.val ∧ b0.val ≤ 223 then
         match rest with
         | b1 :: r1 => (128 ≤ b1.val ∧ b1.val ≤ 191) && isValidUtf8List r1
         | [] => false
       else if 224 ≤ b0.val ∧ b0.val ≤ 239 then
         match rest with
         | b1 :: b2 :: r2 =>
           let ok1 :=
             if b0.val = 224 then 160 ≤ b1.val ∧ b1.val ≤ 191
             else if b0.val = 237 then 128 ≤ b1.val ∧ b1.val ≤ 159
             else 128 ≤ b1.val ∧ b1.val ≤ 191
           ok1 && decide (128 ≤ b2.val ∧ b2.val ≤ 191) && isValidUtf8List r2
         | _ => false
       else if 240 ≤ b0.val ∧ b0.val ≤ 244 then
         match rest with
         | b1 :: b2 :: b3 :: r3 =>
           let ok1 :=
             if b0.val = 240 then 144 ≤ b1.val ∧ b1.val ≤ 191
             else if b0.val = 244 then 128 ≤ b1.val ∧ b1.val ≤ 143
             else 128 ≤ b1.val ∧ b1.val ≤ 191
           ok1 && decide (128 ≤ b2.val ∧ b2.val ≤ 191) &&
             decide (128 ≤ b3.val ∧ b3.val ≤ 191) && isValidUtf8List r3
         | _ => false
       else false) := by
  conv_lhs => unfold isValidUtf8List

theorem utf16LenList_cons (b : Std.U8) (rest : List Std.U8) :
    utf16LenList (b :: rest) =
      if 1 + rest.length < leadStep b then 0
      else leadUnits b + utf16LenList (rest.drop (leadStep b - 1)) := by
  conv_lhs => unfold utf16LenList
  split_ifs <;> rfl

theorem utf16LenList_append_of_valid (a b : List Std.U8) (ha : isValidUtf8List a = true) :
    utf16LenList (a ++ b) = utf16LenList a + utf16LenList b := by
  have hMain : ∀ n (x : List Std.U8), x.length ≤ n → isValidUtf8List x = true →
      utf16LenList (x ++ b) = utf16LenList x + utf16LenList b := by
    intro n
    induction n with
    | zero =>
      intro x hx _
      cases x with
      | nil => simp [utf16LenList]
      | cons => simp at hx
    | succ m ih =>
      intro x hx haX
      cases x with
      | nil => simp [utf16LenList]
      | cons hd tl =>
        have hs := leadStep_pos hd
        by_cases hLt : 1 + tl.length < leadStep hd
        · exfalso
          rw [isValidUtf8List_cons] at haX
          simp only [leadStep] at hLt
          split_ifs at hLt with h1 h2 h3
          · omega
          · by_cases h194 : 194 ≤ hd.val
            · rw [if_neg h1, if_pos ⟨h194, by omega⟩] at haX
              rcases tl with _ | ⟨b1, r1⟩ <;> simp at haX hLt <;> omega
            · rw [if_neg h1, if_neg (by omega), if_neg (by omega), if_neg (by omega)] at haX
              simp at haX
          · rw [if_neg h1, if_neg (by omega), if_pos ⟨by omega, by omega⟩] at haX
            rcases tl with _ | ⟨b1, _ | ⟨b2, r2⟩⟩ <;> simp at haX hLt <;> omega
          · rw [if_neg h1, if_neg (by omega), if_neg (by omega)] at haX
            by_cases h4 : 240 ≤ hd.val ∧ hd.val ≤ 244
            · rw [if_pos h4] at haX
              rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r3⟩⟩⟩ <;> simp at haX hLt <;> omega
            · rw [if_neg h4] at haX
              cases haX
        · have hGe' : ¬ (1 + (tl ++ b).length < leadStep hd) := by simp; omega
          rw [List.cons_append, utf16LenList_cons, if_neg hGe', utf16LenList_cons, if_neg hLt]
          have hDrop : (tl ++ b).drop (leadStep hd - 1) = tl.drop (leadStep hd - 1) ++ b := by
            apply List.drop_append_of_le_length; omega
          have hDropLen : (tl.drop (leadStep hd - 1)).length ≤ m := by
            simp only [List.length_drop]; simp only [List.length_cons] at hx; omega
          have hValidDrop : isValidUtf8List (tl.drop (leadStep hd - 1)) = true := by
            rw [isValidUtf8List_cons] at haX
            by_cases h1 : hd.val < 128
            · have hs1 : leadStep hd = 1 := by simp [leadStep, h1]
              rw [if_pos h1] at haX
              simpa [hs1] using haX
            · by_cases h2 : hd.val < 224
              · have hs2 : leadStep hd = 2 := by simp [leadStep, h1, h2]
                rw [if_neg h1] at haX
                by_cases h194 : 194 ≤ hd.val
                · rw [if_pos ⟨h194, by omega⟩] at haX
                  rcases tl with _ | ⟨b1, r1⟩
                  · simp [hs2] at hLt
                  · simp only [Bool.and_eq_true, decide_eq_true_eq] at haX
                    simpa [hs2] using haX.2
                · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at haX
                  simp at haX
              · by_cases h3 : hd.val < 240
                · have hs3 : leadStep hd = 3 := by simp [leadStep, h1, h2, h3]
                  rw [if_neg h1, if_neg (by omega), if_pos ⟨by omega, by omega⟩] at haX
                  rcases tl with _ | ⟨b1, _ | ⟨b2, r2⟩⟩
                  · simp [hs3] at hLt
                  · simp [hs3] at hLt
                  · simp only [Bool.and_eq_true, decide_eq_true_eq] at haX
                    simpa [hs3] using haX.2
                · have hs4 : leadStep hd = 4 := by simp [leadStep, h1, h2, h3]
                  rw [if_neg h1, if_neg (by omega), if_neg (by omega)] at haX
                  by_cases h4 : 240 ≤ hd.val ∧ hd.val ≤ 244
                  · rw [if_pos h4] at haX
                    rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r3⟩⟩⟩
                    · simp [hs4] at hLt
                    · simp [hs4] at hLt
                    · simp [hs4] at hLt
                    · simp only [Bool.and_eq_true, decide_eq_true_eq] at haX
                      simpa [hs4] using haX.2
                  · rw [if_neg h4] at haX
                    cases haX
          rw [hDrop, ih _ hDropLen hValidDrop]
          omega
  exact hMain a.length a (le_refl _) ha

theorem is_cont_spec (b : Std.U8) :
    utf16.is_cont b ⦃ res => res = decide (128 ≤ b.val ∧ b.val ≤ 191) ⦄ := by
  unfold utf16.is_cont
  split_ifs <;> simp [spec_ok] <;> scalar_tac

theorem is_cont_total (b : Std.U8) :
    utf16.is_cont b ⦃ _ => True ⦄ :=
  spec_mono (is_cont_spec b) (fun _ _ => trivial)

theorem utf8_check_3_spec (b0 b1 b2 : Std.U8) :
    utf16.utf8_check_3 b0 b1 b2 ⦃ res =>
      res =
        ((if b0.val = 224 then decide (160 ≤ b1.val ∧ b1.val ≤ 191)
          else if b0.val = 237 then decide (128 ≤ b1.val ∧ b1.val ≤ 159)
          else decide (128 ≤ b1.val ∧ b1.val ≤ 191)) &&
         decide (128 ≤ b2.val ∧ b2.val ≤ 191)) ⦄ := by
  unfold utf16.utf8_check_3
  step with is_cont_spec b2 as ⟨hc2, hhc2⟩
  by_cases h2 : 128 ≤ b2.val ∧ b2.val ≤ 191
  · have hb : hc2 = true := by rw [hhc2]; exact decide_eq_true h2
    have hd2 : decide (128 ≤ b2.val ∧ b2.val ≤ 191) = true := decide_eq_true h2
    subst hb
    simp only [↓reduceIte, hd2, Bool.and_true]
    by_cases h224 : b0 = 224#u8
    · have h224v : b0.val = 224 := congrArg UScalar.val h224
      simp only [h224, h224v, ↓reduceIte]
      split_ifs <;> simp [spec_ok] <;> scalar_tac
    · have h224v : b0.val ≠ 224 := fun h => h224 (UScalar.eq_of_val_eq h)
      simp only [h224, h224v, ↓reduceIte]
      by_cases h237 : b0 = 237#u8
      · have h237v : b0.val = 237 := congrArg UScalar.val h237
        simp only [h237, h237v, ↓reduceIte]
        split_ifs <;> simp [spec_ok] <;> scalar_tac
      · have h237v : b0.val ≠ 237 := fun h => h237 (UScalar.eq_of_val_eq h)
        simp only [h237, h237v, ↓reduceIte]
        exact is_cont_spec b1
  · have hb : hc2 = false := by rw [hhc2]; exact decide_eq_false h2
    subst hb
    simp [spec_ok, h2]

theorem utf8_check_3_total (b0 b1 b2 : Std.U8) :
    utf16.utf8_check_3 b0 b1 b2 ⦃ _ => True ⦄ :=
  spec_mono (utf8_check_3_spec b0 b1 b2) (fun _ _ => trivial)

theorem utf8_check_4_spec (b0 b1 b2 b3 : Std.U8) :
    utf16.utf8_check_4 b0 b1 b2 b3 ⦃ res =>
      res =
        ((if b0.val = 240 then decide (144 ≤ b1.val ∧ b1.val ≤ 191)
          else if b0.val = 244 then decide (128 ≤ b1.val ∧ b1.val ≤ 143)
          else decide (128 ≤ b1.val ∧ b1.val ≤ 191)) &&
         decide (128 ≤ b2.val ∧ b2.val ≤ 191) &&
         decide (128 ≤ b3.val ∧ b3.val ≤ 191)) ⦄ := by
  unfold utf16.utf8_check_4
  step with is_cont_spec b2 as ⟨hc2, hhc2⟩
  by_cases h2 : 128 ≤ b2.val ∧ b2.val ≤ 191
  · have hb : hc2 = true := by rw [hhc2]; exact decide_eq_true h2
    have hd2 : decide (128 ≤ b2.val ∧ b2.val ≤ 191) = true := decide_eq_true h2
    subst hb
    simp only [↓reduceIte, hd2, Bool.and_true]
    step with is_cont_spec b3 as ⟨hc3, hhc3⟩
    by_cases h3 : 128 ≤ b3.val ∧ b3.val ≤ 191
    · have hb3 : hc3 = true := by rw [hhc3]; exact decide_eq_true h3
      have hd3 : decide (128 ≤ b3.val ∧ b3.val ≤ 191) = true := decide_eq_true h3
      subst hb3
      simp only [↓reduceIte, hd3, Bool.and_true]
      by_cases h240 : b0 = 240#u8
      · have h240v : b0.val = 240 := congrArg UScalar.val h240
        simp only [h240, h240v, ↓reduceIte]
        split_ifs <;> simp [spec_ok] <;> scalar_tac
      · have h240v : b0.val ≠ 240 := fun h => h240 (UScalar.eq_of_val_eq h)
        simp only [h240, h240v, ↓reduceIte]
        by_cases h244 : b0 = 244#u8
        · have h244v : b0.val = 244 := congrArg UScalar.val h244
          simp only [h244, h244v, ↓reduceIte]
          split_ifs <;> simp [spec_ok] <;> scalar_tac
        · have h244v : b0.val ≠ 244 := fun h => h244 (UScalar.eq_of_val_eq h)
          simp only [h244, h244v, ↓reduceIte]
          exact is_cont_spec b1
    · have hb3 : hc3 = false := by rw [hhc3]; exact decide_eq_false h3
      subst hb3
      simp [spec_ok, h3]
  · have hb : hc2 = false := by rw [hhc2]; exact decide_eq_false h2
    subst hb
    simp [spec_ok, h2]

theorem utf8_check_4_total (b0 b1 b2 b3 : Std.U8) :
    utf16.utf8_check_4 b0 b1 b2 b3 ⦃ _ => True ⦄ :=
  spec_mono (utf8_check_4_spec b0 b1 b2 b3) (fun _ _ => trivial)

private theorem utf8_slice_drop_cons (bytes : Slice Std.U8) (k : Nat) (hk : k < bytes.length) :
    bytes.val.drop k = bytes.val[k]'hk :: bytes.val.drop (k + 1) :=
  List.drop_eq_getElem_cons hk

theorem utf8_char_step_spec (bytes : Slice Std.U8) (i : Std.Usize)
    (hi : i.val < bytes.length) :
    utf16.utf8_char_step bytes i ⦃ o =>
      match o with
      | none => isValidUtf8List (bytes.val.drop i.val) = false
      | some nxt =>
        i.val < nxt.val ∧ nxt.val ≤ bytes.length ∧
        isValidUtf8List (bytes.val.drop i.val) = isValidUtf8List (bytes.val.drop nxt.val) ⦄ := by
  have hStep2 : ∀ (idx : Std.Usize) (hidx : idx.val < bytes.length),
      194 ≤ (bytes.val[idx.val]'hidx).val →
      (bytes.val[idx.val]'hidx).val ≤ 223 →
      (do
        let i1 ← Slice.len bytes - idx
        if i1 < 2#usize then ok none
        else
          let i2 ← idx + 1#usize
          let i3 ← Slice.index_usize bytes i2
          let b ← utf16.is_cont i3
          if b then
            let i4 ← idx + 2#usize
            ok (some i4)
          else ok none) ⦃ o =>
        match o with
        | none => isValidUtf8List (bytes.val.drop idx.val) = false
        | some nxt =>
          idx.val < nxt.val ∧ nxt.val ≤ bytes.length ∧
          isValidUtf8List (bytes.val.drop idx.val) = isValidUtf8List (bytes.val.drop nxt.val) ⦄ := by
    intro idx hidx hc1 hc2
    step as ⟨i1, hi1⟩
    have hb0Ge : ¬ (bytes.val[idx.val]'hidx).val < 128 := by omega
    by_cases hlt2 : i1 < 2#usize
    · simp only [hlt2, ↓reduceIte, spec_ok]
      have hRestLen : bytes.length ≤ idx.val + 1 := by scalar_tac
      have hEmpty : bytes.val.drop (idx.val + 1) = [] := List.drop_eq_nil_of_le hRestLen
      rw [utf8_slice_drop_cons bytes idx.val hidx, hEmpty, isValidUtf8List_cons]
      simp [hb0Ge, hc1, hc2]
    · simp only [hlt2, ↓reduceIte]
      have hRem2 : 2 ≤ bytes.length - idx.val := by scalar_tac
      have hB1 : idx.val + 1 < bytes.length := by omega
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step with is_cont_spec i3 as ⟨b, hb⟩
      have hDrop0 : bytes.val.drop idx.val =
          (bytes.val[idx.val]'hidx) ::
          (bytes.val[idx.val + 1]'hB1) ::
          bytes.val.drop (idx.val + 2) := by
        rw [utf8_slice_drop_cons bytes idx.val hidx, utf8_slice_drop_cons bytes (idx.val + 1) hB1]
      have hi3Eq : i3 = bytes.val[idx.val + 1]'hB1 := by
        simpa [hi2] using hi3
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, spec_ok]
        have hNotCont : ¬ (128 ≤ i3.val ∧ i3.val ≤ 191) := by
          intro hc
          have hd : decide (128 ≤ i3.val ∧ i3.val ≤ 191) = true := decide_eq_true hc
          rw [← hb] at hd; cases hd
        rw [hDrop0, isValidUtf8List_cons, ite_eq_right hb0Ge, ite_eq_left ⟨hc1, hc2⟩]
        simp [← hi3Eq, hNotCont]
      | true =>
        simp only [↓reduceIte]
        step as ⟨i4, hi4⟩
        try simp only [spec_ok]
        have hCont : 128 ≤ i3.val ∧ i3.val ≤ 191 := by
          have : decide (128 ≤ i3.val ∧ i3.val ≤ 191) = true := hb.symm
          exact decide_eq_true_eq.mp this
        refine ⟨by scalar_tac, by scalar_tac, ?_⟩
        rw [hDrop0, isValidUtf8List_cons, ite_eq_right hb0Ge, ite_eq_left ⟨hc1, hc2⟩]
        simp [← hi3Eq, hCont, hi4]
  have hStep3 : ∀ (c0 : Std.U8) (idx : Std.Usize) (hidx : idx.val < bytes.length),
      c0 = bytes.val[idx.val]'hidx →
      224 ≤ c0.val → c0.val ≤ 239 →
      (do
        let i1 ← Slice.len bytes - idx
        if i1 < 3#usize then ok none
        else
          let i2 ← idx + 1#usize
          let i3 ← Slice.index_usize bytes i2
          let i4 ← idx + 2#usize
          let i5 ← Slice.index_usize bytes i4
          let b ← utf16.utf8_check_3 c0 i3 i5
          if b then
            let i6 ← idx + 3#usize
            ok (some i6)
          else ok none) ⦃ o =>
        match o with
        | none => isValidUtf8List (bytes.val.drop idx.val) = false
        | some nxt =>
          idx.val < nxt.val ∧ nxt.val ≤ bytes.length ∧
          isValidUtf8List (bytes.val.drop idx.val) = isValidUtf8List (bytes.val.drop nxt.val) ⦄ := by
    intro c0 idx hidx hc0Eq hc1 hc2
    step as ⟨i1, hi1⟩
    by_cases hlt3 : i1 < 3#usize
    · simp only [hlt3, ↓reduceIte, spec_ok]
      have hRemLt3 : bytes.length - idx.val < 3 := by scalar_tac
      rw [utf8_slice_drop_cons bytes idx.val hidx, isValidUtf8List_cons]
      have h1 : ¬ (bytes.val[idx.val]'hidx).val < 128 := by rw [← hc0Eq]; omega
      have h2 : ¬ (194 ≤ (bytes.val[idx.val]'hidx).val ∧
          (bytes.val[idx.val]'hidx).val ≤ 223) := by
        rw [← hc0Eq]; omega
      have h3 : 224 ≤ (bytes.val[idx.val]'hidx).val ∧
          (bytes.val[idx.val]'hidx).val ≤ 239 := by
        rw [← hc0Eq]; exact ⟨hc1, hc2⟩
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
      by_cases hLt2 : bytes.length ≤ idx.val + 1
      · rw [List.drop_eq_nil_of_le hLt2]
      · have hB1 : idx.val + 1 < bytes.length := by omega
        have hEq2 : bytes.length ≤ idx.val + 2 := by omega
        rw [utf8_slice_drop_cons bytes (idx.val + 1) hB1, List.drop_eq_nil_of_le hEq2]
    · simp only [hlt3, ↓reduceIte]
      have hRem3 : 3 ≤ bytes.length - idx.val := by scalar_tac
      have hB1 : idx.val + 1 < bytes.length := by omega
      have hB2 : idx.val + 2 < bytes.length := by omega
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      step with utf8_check_3_spec c0 i3 i5 as ⟨b, hb⟩
      have hi3Eq : i3 = bytes.val[idx.val + 1]'hB1 := by
        simpa [hi2] using hi3
      have hi5Eq : i5 = bytes.val[idx.val + 2]'hB2 := by
        simpa [hi4] using hi5
      have hDrop0 : bytes.val.drop idx.val =
          c0 :: i3 :: i5 :: bytes.val.drop (idx.val + 3) := by
        rw [utf8_slice_drop_cons bytes idx.val hidx, utf8_slice_drop_cons bytes (idx.val + 1) hB1,
            utf8_slice_drop_cons bytes (idx.val + 2) hB2, ← hc0Eq, hi3Eq, hi5Eq]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, spec_ok]
        rw [hDrop0, isValidUtf8List_cons, ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_left ⟨hc1, hc2⟩]
        dsimp only
        have hBad : ¬ ((if c0.val = 224 then 160 ≤ i3.val ∧ i3.val ≤ 191
            else if c0.val = 237 then 128 ≤ i3.val ∧ i3.val ≤ 159
            else 128 ≤ i3.val ∧ i3.val ≤ 191) ∧ (128 ≤ i5.val ∧ i5.val ≤ 191)) := by
          intro ⟨hA, hB⟩
          have hT : ((if c0.val = 224 then decide (160 ≤ i3.val ∧ i3.val ≤ 191)
              else if c0.val = 237 then decide (128 ≤ i3.val ∧ i3.val ≤ 159)
              else decide (128 ≤ i3.val ∧ i3.val ≤ 191)) &&
              decide (128 ≤ i5.val ∧ i5.val ≤ 191)) = true := by
            split_ifs at hA ⊢ <;> simp_all [hB]
          rw [← hb] at hT; cases hT
        rw [Bool.and_eq_false_iff]; left
        rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
        tauto
      | true =>
        simp only [↓reduceIte]
        step as ⟨i6, hi6⟩
        try simp only [spec_ok]
        refine ⟨by scalar_tac, by scalar_tac, ?_⟩
        rw [hDrop0, isValidUtf8List_cons, ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_left ⟨hc1, hc2⟩]
        have hb' := hb.symm
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
        by_cases h224 : c0.val = 224 <;> by_cases h237 : c0.val = 237 <;>
          simp [h224, h237] at hb' <;> simp [h224, h237, hb', hi6]
  have hStep4 : ∀ (c0 : Std.U8) (idx : Std.Usize) (hidx : idx.val < bytes.length),
      c0 = bytes.val[idx.val]'hidx →
      240 ≤ c0.val → c0.val ≤ 244 →
      (do
        let i1 ← Slice.len bytes - idx
        if i1 < 4#usize then ok none
        else
          let i2 ← idx + 1#usize
          let i3 ← Slice.index_usize bytes i2
          let i4 ← idx + 2#usize
          let i5 ← Slice.index_usize bytes i4
          let i6 ← idx + 3#usize
          let i7 ← Slice.index_usize bytes i6
          let b ← utf16.utf8_check_4 c0 i3 i5 i7
          if b then
            let i8 ← idx + 4#usize
            ok (some i8)
          else ok none) ⦃ o =>
        match o with
        | none => isValidUtf8List (bytes.val.drop idx.val) = false
        | some nxt =>
          idx.val < nxt.val ∧ nxt.val ≤ bytes.length ∧
          isValidUtf8List (bytes.val.drop idx.val) = isValidUtf8List (bytes.val.drop nxt.val) ⦄ := by
    intro c0 idx hidx hc0Eq hc1 hc2
    step as ⟨i1, hi1⟩
    by_cases hlt4 : i1 < 4#usize
    · simp only [hlt4, ↓reduceIte, spec_ok]
      have hRemLt4 : bytes.length - idx.val < 4 := by scalar_tac
      rw [utf8_slice_drop_cons bytes idx.val hidx, isValidUtf8List_cons]
      have h1 : ¬ (bytes.val[idx.val]'hidx).val < 128 := by rw [← hc0Eq]; omega
      have h2 : ¬ (194 ≤ (bytes.val[idx.val]'hidx).val ∧
          (bytes.val[idx.val]'hidx).val ≤ 223) := by
        rw [← hc0Eq]; omega
      have h3 : ¬ (224 ≤ (bytes.val[idx.val]'hidx).val ∧
          (bytes.val[idx.val]'hidx).val ≤ 239) := by
        rw [← hc0Eq]; omega
      have h4 : 240 ≤ (bytes.val[idx.val]'hidx).val ∧
          (bytes.val[idx.val]'hidx).val ≤ 244 := by
        rw [← hc0Eq]; exact ⟨hc1, hc2⟩
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
      by_cases hLt2 : bytes.length ≤ idx.val + 1
      · rw [List.drop_eq_nil_of_le hLt2]
      · have hB1 : idx.val + 1 < bytes.length := by omega
        by_cases hLt3 : bytes.length ≤ idx.val + 2
        · rw [utf8_slice_drop_cons bytes (idx.val + 1) hB1, List.drop_eq_nil_of_le hLt3]
        · have hB2 : idx.val + 2 < bytes.length := by omega
          rw [utf8_slice_drop_cons bytes (idx.val + 1) hB1,
              utf8_slice_drop_cons bytes (idx.val + 2) hB2,
              List.drop_eq_nil_of_le (show bytes.length ≤ idx.val + 3 by omega)]
    · simp only [hlt4, ↓reduceIte]
      have hRem4 : 4 ≤ bytes.length - idx.val := by scalar_tac
      have hB1 : idx.val + 1 < bytes.length := by omega
      have hB2 : idx.val + 2 < bytes.length := by omega
      have hB3 : idx.val + 3 < bytes.length := by omega
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      step with utf8_check_4_spec c0 i3 i5 i7 as ⟨b, hb⟩
      have hi3Eq : i3 = bytes.val[idx.val + 1]'hB1 := by
        simpa [hi2] using hi3
      have hi5Eq : i5 = bytes.val[idx.val + 2]'hB2 := by
        simpa [hi4] using hi5
      have hi7Eq : i7 = bytes.val[idx.val + 3]'hB3 := by
        simpa [hi6] using hi7
      have hDrop0 : bytes.val.drop idx.val =
          c0 :: i3 :: i5 :: i7 :: bytes.val.drop (idx.val + 4) := by
        rw [utf8_slice_drop_cons bytes idx.val hidx, utf8_slice_drop_cons bytes (idx.val + 1) hB1,
            utf8_slice_drop_cons bytes (idx.val + 2) hB2, utf8_slice_drop_cons bytes (idx.val + 3) hB3,
            ← hc0Eq, hi3Eq, hi5Eq, hi7Eq]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, spec_ok]
        rw [hDrop0, isValidUtf8List_cons, ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨hc1, hc2⟩]
        dsimp only
        have hBad : ¬ ((if c0.val = 240 then 144 ≤ i3.val ∧ i3.val ≤ 191
            else if c0.val = 244 then 128 ≤ i3.val ∧ i3.val ≤ 143
            else 128 ≤ i3.val ∧ i3.val ≤ 191) ∧
            (128 ≤ i5.val ∧ i5.val ≤ 191) ∧ (128 ≤ i7.val ∧ i7.val ≤ 191)) := by
          intro ⟨hA, hB, hC⟩
          have hT : ((if c0.val = 240 then decide (144 ≤ i3.val ∧ i3.val ≤ 191)
              else if c0.val = 244 then decide (128 ≤ i3.val ∧ i3.val ≤ 143)
              else decide (128 ≤ i3.val ∧ i3.val ≤ 191)) &&
              decide (128 ≤ i5.val ∧ i5.val ≤ 191) &&
              decide (128 ≤ i7.val ∧ i7.val ≤ 191)) = true := by
            split_ifs at hA ⊢ <;> simp_all [hB, hC]
          rw [← hb] at hT; cases hT
        rw [Bool.and_eq_false_iff]; left
        rw [Bool.and_eq_false_iff, Bool.and_eq_false_iff,
            decide_eq_false_iff_not, decide_eq_false_iff_not, decide_eq_false_iff_not]
        tauto
      | true =>
        simp only [↓reduceIte]
        step as ⟨i8, hi8⟩
        try simp only [spec_ok]
        refine ⟨by scalar_tac, by scalar_tac, ?_⟩
        rw [hDrop0, isValidUtf8List_cons, ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨hc1, hc2⟩]
        have hb' := hb.symm
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
        by_cases h240 : c0.val = 240 <;> by_cases h244 : c0.val = 244 <;>
          simp [h240, h244] at hb' <;> simp [h240, h244, hb', hi8]
  unfold utf16.utf8_char_step
  step as ⟨b0, hb0⟩
  by_cases hlt128 : b0 < 128#u8
  · simp only [hlt128, ↓reduceIte]
    have hBound : i.val + 1 ≤ Std.Usize.max := by scalar_tac
    step as ⟨i1, hi1⟩
    try simp only [spec_ok]
    try dsimp only
    have hb0Lt : b0.val < 128 := hlt128
    refine ⟨by omega, by omega, ?_⟩
    rw [utf8_slice_drop_cons bytes i.val hi, ← hb0, isValidUtf8List_cons, ite_eq_left hb0Lt, hi1]
  · simp only [hlt128, ↓reduceIte]
    have hb0Ge128 : 128 ≤ b0.val := by scalar_tac
    split_ifs with h194 h223 h224 h239 h240 h244
    all_goals first
      | (exfalso; scalar_tac)
      | exact hStep2 i hi (by scalar_tac) (by scalar_tac)
      | exact hStep3 b0 i hi hb0 (by scalar_tac) (by scalar_tac)
      | exact hStep4 b0 i hi hb0 (by scalar_tac) (by scalar_tac)
      | (try simp only [spec_ok]
         rw [utf8_slice_drop_cons bytes i.val hi, ← hb0, isValidUtf8List_cons]
         have h1 : ¬ b0.val < 128 := by scalar_tac
         have h2 : ¬ (194 ≤ b0.val ∧ b0.val ≤ 223) := by intro ⟨a, b⟩; scalar_tac
         have h3 : ¬ (224 ≤ b0.val ∧ b0.val ≤ 239) := by intro ⟨a, b⟩; scalar_tac
         have h4 : ¬ (240 ≤ b0.val ∧ b0.val ≤ 244) := by intro ⟨a, b⟩; scalar_tac
         rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4])

theorem utf8_char_step_total (bytes : Slice Std.U8) (i : Std.Usize)
    (hi : i.val < bytes.length) :
    utf16.utf8_char_step bytes i ⦃ o =>
      match o with
      | none => True
      | some nxt => i.val < nxt.val ∧ nxt.val ≤ bytes.length ⦄ := by
  refine spec_mono (utf8_char_step_spec bytes i hi) ?_
  intro o ho
  cases o with
  | none => trivial
  | some nxt => exact ⟨ho.1, ho.2.1⟩

theorem is_valid_utf8_spec (bytes : Slice Std.U8) :
    utf16.is_valid_utf8 bytes ⦃ b => b = isValidUtf8List bytes.val ⦄ := by
  unfold utf16.is_valid_utf8 utf16.is_valid_utf8_loop
  refine loop.spec_decr_nat
    (fun i => bytes.length - i.val)
    (fun i => i.val ≤ bytes.length ∧ isValidUtf8List bytes.val = isValidUtf8List (bytes.val.drop i.val))
    (fun b => b = isValidUtf8List bytes.val) _ 0#usize ?_ ⟨by scalar_tac, by simp⟩
  intro i ⟨hiLen, hEq⟩
  unfold utf16.is_valid_utf8_loop.body
  split_ifs with hlt
  · step with utf8_char_step_spec bytes i (by scalar_tac) as ⟨o, ho⟩
    cases o with
    | none =>
      simp only [spec_ok]
      rw [hEq, ho]
    | some nxt =>
      simp only [spec_ok]
      exact ⟨ho.2.1, by rw [hEq, ho.2.2], by scalar_tac⟩
  · simp only [spec_ok]
    have hNil : bytes.val.drop i.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
    rw [hEq, hNil, isValidUtf8List]

theorem is_valid_utf8_total (bytes : Slice Std.U8) :
    utf16.is_valid_utf8 bytes ⦃ _ => True ⦄ :=
  spec_mono (is_valid_utf8_spec bytes) (fun _ _ => trivial)

theorem utf16_len_spec (bytes : Slice Std.U8) :
    utf16.utf16_len bytes ⦃ count => count.val = utf16LenList bytes.val ⦄ := by
  unfold utf16.utf16_len utf16.utf16_len_loop
  let inv : Std.Usize × Std.Usize → Prop := fun (i, count) =>
    i.val ≤ bytes.length ∧ count.val ≤ i.val ∧
    count.val + utf16LenList (bytes.val.drop i.val) = utf16LenList bytes.val
  refine loop.spec_decr_nat
    (fun (i, _) => bytes.length - i.val) inv
    (fun (count : Std.Usize) => count.val = utf16LenList bytes.val) _ (0#usize, 0#usize) ?_
    ⟨by scalar_tac, by scalar_tac, by simp⟩
  intro ⟨i, count⟩ ⟨hiLen, hCntLe, hSum⟩
  unfold utf16.utf16_len_loop.body
  simp only
  split_ifs with hlt
  · have hiLt : i.val < bytes.length := by scalar_tac
    have hStepSpec : ∀ b : Std.U8,
        (if b < 128#u8 then ok 1#usize
         else if b < 224#u8 then ok 2#usize
         else if b < 240#u8 then ok 3#usize
         else ok 4#usize) ⦃ s => s.val = leadStep b ∧ 1 ≤ s.val ∧ s.val ≤ 4 ⦄ := by
      intro b; simp only [leadStep]; split_ifs <;> simp [spec_ok] <;> scalar_tac
    step as ⟨b, hb⟩
    step with hStepSpec b as ⟨s, hsEq, hs1, hs4⟩
    step as ⟨rem, hrem⟩
    have hDropCons : bytes.val.drop i.val = b :: bytes.val.drop (i.val + 1) := by
      rw [hb]; exact List.drop_eq_getElem_cons hiLt
    have hDropLen : 1 + (bytes.val.drop (i.val + 1)).length = bytes.length - i.val := by
      simp [List.length_drop]; scalar_tac
    by_cases hshort : rem < s
    · simp only [hshort, ↓reduceIte, spec_ok]
      have hLtLead : 1 + (bytes.val.drop (i.val + 1)).length < leadStep b := by scalar_tac
      have hZero : utf16LenList (bytes.val.drop i.val) = 0 := by
        rw [hDropCons, utf16LenList_cons, if_pos hLtLead]
      omega
    · simp only [hshort, ↓reduceIte]
      have hNotLtLead : ¬ (1 + (bytes.val.drop (i.val + 1)).length < leadStep b) := by scalar_tac
      have hUnitsSpec : (if s = 4#usize then ok 2#usize else ok 1#usize) ⦃ u =>
          u.val = leadUnits b ∧ u.val ≤ s.val ⦄ := by
        by_cases h4 : s = 4#usize
        · have hs4v : s.val = 4 := congrArg UScalar.val h4
          have hlb : leadStep b = 4 := hsEq.symm.trans hs4v
          simp [h4, leadUnits, hlb, spec_ok]
        · have hsNe4 : s.val ≠ 4 := fun h => h4 (UScalar.eq_of_val_eq h)
          have hlb : leadStep b ≠ 4 := by omega
          simp [h4, leadUnits, hlb, spec_ok]; omega
      step with hUnitsSpec as ⟨units, huEq, huLe⟩
      step as ⟨i2, hi2⟩
      step as ⟨count1, hcnt1⟩
      try simp only [spec_ok]
      have hDrop2 : (bytes.val.drop (i.val + 1)).drop (leadStep b - 1) = bytes.val.drop i2.val := by
        rw [List.drop_drop]
        congr 1
        omega
      have hUnfold : utf16LenList (bytes.val.drop i.val) =
          leadUnits b + utf16LenList (bytes.val.drop i2.val) := by
        rw [hDropCons, utf16LenList_cons, if_neg hNotLtLead, hDrop2]
      exact ⟨⟨by scalar_tac, by scalar_tac, by omega⟩, by scalar_tac⟩
  · simp only [spec_ok]
    have hNil : bytes.val.drop i.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
    rw [hNil, utf16LenList] at hSum
    omega

theorem utf16_len_total (bytes : Slice Std.U8) :
    utf16.utf16_len bytes ⦃ count => count.val ≤ bytes.length ⦄ := by
  refine spec_mono (utf16_len_spec bytes) ?_
  intro count hEq
  have hLe : ∀ l : List Std.U8, utf16LenList l ≤ l.length := by
    intro l
    have hAux : ∀ n (x : List Std.U8), x.length ≤ n → utf16LenList x ≤ x.length := by
      intro n
      induction n with
      | zero =>
        intro x hx; cases x with | nil => simp [utf16LenList] | cons => simp at hx
      | succ m ih =>
        intro x hx
        cases x with
        | nil => simp [utf16LenList]
        | cons b rest =>
          rw [utf16LenList_cons]
          split_ifs with hlt
          · omega
          · have hs := leadStep_pos b
            have hu := leadUnits_le_leadStep b
            have hDrop := ih (rest.drop (leadStep b - 1)) (by simp [List.length_drop]; simp at hx; omega)
            rw [List.length_drop] at hDrop
            simp only [List.length_cons] at hx ⊢
            omega
    exact hAux l.length l (le_refl _)
  rw [hEq]
  exact hLe bytes.val

theorem utf16_len_append_of_valid (a b ab : Slice Std.U8)
    (hValid : isValidUtf8List a.val = true)
    (hApp : ab.val = a.val ++ b.val) :
    (do
      let na ← utf16.utf16_len a
      let nb ← utf16.utf16_len b
      let nab ← utf16.utf16_len ab
      ok (na, nb, nab)) ⦃ (na, nb, nab) => nab.val = na.val + nb.val ⦄ := by
  step with utf16_len_spec a as ⟨na, hna⟩
  step with utf16_len_spec b as ⟨nb, hnb⟩
  step with utf16_len_spec ab as ⟨nab, hnab⟩
  try simp only [spec_ok]
  rw [hnab, hApp, utf16LenList_append_of_valid a.val b.val hValid, hna, hnb]

private theorem isValidUtf8List_append_of_valid (a b : List Std.U8)
    (ha : isValidUtf8List a = true) (hb : isValidUtf8List b = true) :
    isValidUtf8List (a ++ b) = true := by
  have hAux : ∀ n (x : List Std.U8), x.length ≤ n →
      isValidUtf8List x = true → isValidUtf8List (x ++ b) = true := by
    intro n
    induction n with
    | zero =>
      intro x hx _; cases x with | nil => simpa | cons => simp at hx
    | succ m ih =>
      intro x hx hX
      cases x with
      | nil => simpa
      | cons hd tl =>
        rw [List.cons_append, isValidUtf8List_cons]
        rw [isValidUtf8List_cons] at hX
        by_cases h1 : hd.val < 128
        · rw [if_pos h1] at hX ⊢
          exact ih tl (by simp at hx; omega) hX
        · rw [if_neg h1] at hX ⊢
          by_cases h2 : 194 ≤ hd.val ∧ hd.val ≤ 223
          · rw [if_pos h2] at hX ⊢
            rcases tl with _ | ⟨b1, r1⟩
            · simp at hX
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at hX
              simp only [List.cons_append, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨hX.1, ih r1 (by simp at hx; omega) hX.2⟩
          · rw [if_neg h2] at hX ⊢
            by_cases h3 : 224 ≤ hd.val ∧ hd.val ≤ 239
            · rw [if_pos h3] at hX ⊢
              rcases tl with _ | ⟨b1, _ | ⟨b2, r2⟩⟩
              · simp at hX
              · simp at hX
              · simp only [Bool.and_eq_true, decide_eq_true_eq] at hX
                simp only [List.cons_append, Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨hX.1, ih r2 (by simp at hx; omega) hX.2⟩
            · rw [if_neg h3] at hX ⊢
              by_cases h4 : 240 ≤ hd.val ∧ hd.val ≤ 244
              · rw [if_pos h4] at hX ⊢
                rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r3⟩⟩⟩
                · simp at hX
                · simp at hX
                · simp at hX
                · simp only [Bool.and_eq_true, decide_eq_true_eq] at hX
                  simp only [List.cons_append, Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨hX.1, ih r3 (by simp at hx; omega) hX.2⟩
              · rw [if_neg h4] at hX; cases hX
  exact hAux a.length a (le_refl _) ha

private theorem valid_utf8_head_step_facts (l : List Std.U8) (hl : l ≠ [])
    (hValid : isValidUtf8List l = true) :
    let b := l.head hl
    leadStep b ≤ l.length ∧
    isValidUtf8List (l.take (leadStep b)) = true ∧
    isValidUtf8List (l.drop (leadStep b)) = true ∧
    utf16LenList (l.take (leadStep b)) = leadUnits b := by
  rcases l with _ | ⟨b0, tl⟩
  · contradiction
  · simp only [List.head_cons]
    rw [isValidUtf8List_cons] at hValid
    by_cases h1 : b0.val < 128
    · have hs : leadStep b0 = 1 := by simp [leadStep, h1]
      rw [if_pos h1] at hValid
      rw [hs]
      refine ⟨by simp, ?_, by simpa using hValid, ?_⟩
      · simp [List.take, isValidUtf8List, h1]
      · simp [List.take, utf16LenList, hs]
    · rw [if_neg h1] at hValid
      by_cases h2 : 194 ≤ b0.val ∧ b0.val ≤ 223
      · have hs : leadStep b0 = 2 := by simp [leadStep]; split_ifs <;> omega
        rw [if_pos h2] at hValid
        rcases tl with _ | ⟨b1, r1⟩
        · simp at hValid
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hValid
          rw [hs]
          refine ⟨by simp, ?_, by simpa using hValid.2, ?_⟩
          · rw [List.take, List.take, List.take, isValidUtf8List_cons]
            have hc1 : 128 ≤ b1.val ∧ b1.val ≤ 191 := hValid.1
            simp [h1, h2, hc1, isValidUtf8List]
          · rw [List.take, List.take, List.take, utf16LenList_cons]
            simp [hs, leadUnits, utf16LenList]
      · rw [ite_eq_right h2] at hValid
        by_cases h3 : 224 ≤ b0.val ∧ b0.val ≤ 239
        · have hs : leadStep b0 = 3 := by simp [leadStep]; split_ifs <;> omega
          rw [ite_eq_left h3] at hValid
          rcases tl with _ | ⟨b1, _ | ⟨b2, r2⟩⟩
          · simp at hValid
          · simp at hValid
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hValid
            rw [hs]
            refine ⟨by simp, ?_, by simpa using hValid.2, ?_⟩
            · rw [List.take, List.take, List.take, List.take, isValidUtf8List_cons]
              have hC := hValid.1
              simp [h1, h2, h3, hC, isValidUtf8List]
            · rw [List.take, List.take, List.take, List.take, utf16LenList_cons]
              simp [hs, leadUnits, utf16LenList]
        · rw [ite_eq_right h3] at hValid
          by_cases h4 : 240 ≤ b0.val ∧ b0.val ≤ 244
          · have hs : leadStep b0 = 4 := by simp [leadStep]; split_ifs <;> omega
            rw [ite_eq_left h4] at hValid
            rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r3⟩⟩⟩
            · simp at hValid
            · simp at hValid
            · simp at hValid
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at hValid
              rw [hs]
              refine ⟨by simp, ?_, by simpa using hValid.2, ?_⟩
              · rw [List.take, List.take, List.take, List.take, List.take, isValidUtf8List_cons]
                have hC := hValid.1
                simp [h1, h2, h3, h4, hC, isValidUtf8List]
              · rw [List.take, List.take, List.take, List.take, List.take, utf16LenList_cons]
                simp [hs, leadUnits, utf16LenList]
          · rw [if_neg h4] at hValid; cases hValid

/-- `utf16_split_byte_offset` is total on every byte slice, valid UTF-8 or not,
and always answers a byte range of the slice: `start ≤ end ≤ bytes.len()`. -/
theorem utf16_split_byte_offset_total (bytes : Slice Std.U8) (target : Std.U64) :
    utf16.utf16_split_byte_offset bytes target ⦃ res =>
      res.start.val ≤ res.«end».val ∧ res.«end».val ≤ bytes.length ⦄ := by
  unfold utf16.utf16_split_byte_offset
  have hLoop : utf16.utf16_split_byte_offset_loop bytes target 0#usize 0#u64 (Slice.len bytes)
      ⦃ (r : Std.Usize × Std.Usize × Bool) => r.1.val ≤ r.2.1.val ∧ r.2.1.val ≤ bytes.length ⦄ := by
    unfold utf16.utf16_split_byte_offset_loop
    refine loop.spec_decr_nat
      (fun (i, _) => bytes.length - i.val)
      (fun (i, _) => i.val ≤ bytes.length)
      (fun (r : Std.Usize × Std.Usize × Bool) => r.1.val ≤ r.2.1.val ∧ r.2.1.val ≤ bytes.length)
      _ (0#usize, 0#u64) ?_ (by scalar_tac)
    intro ⟨i, clock⟩ hiLen
    unfold utf16.utf16_split_byte_offset_loop.body
    simp only
    split_ifs with hlt
    · have hiLt : i.val < bytes.length := by scalar_tac
      have hStepSpec : ∀ b : Std.U8,
          (if b < 128#u8 then ok 1#usize
           else if b < 224#u8 then ok 2#usize
           else if b < 240#u8 then ok 3#usize
           else ok 4#usize) ⦃ s => 1 ≤ s.val ∧ s.val ≤ 4 ⦄ := by
        intro b; split_ifs <;> simp [spec_ok] <;> scalar_tac
      step as ⟨b, _⟩
      step with hStepSpec b as ⟨s, hs1, hs4⟩
      step as ⟨rem, hrem⟩
      by_cases hshort : rem < s
      · simp only [hshort, ↓reduceIte, spec_ok]
        exact ⟨Nat.le_refl _, by scalar_tac⟩
      · simp only [hshort, ↓reduceIte]
        have hUnitsSpec : (if s = 4#usize then ok 2#u64 else ok 1#u64) ⦃ u =>
            1 ≤ u.val ∧ u.val ≤ 2 ⦄ := by
          split_ifs <;> simp [spec_ok] <;> scalar_tac
        step with hUnitsSpec as ⟨units, hu1, hu2⟩
        have hU64Max : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
        have hRMax : Std.U64.rMax = 2 ^ 64 - 1 := by decide
        have hUnitsLeMax : units.val ≤ (core.num.U64.MAX : Std.U64).val := by rw [hU64Max]; omega
        step as ⟨maxSub, hmaxSub⟩
        have hMaxSubVal : maxSub.val = 2 ^ 64 - 1 - units.val := by rw [hmaxSub, hRMax]
        by_cases hovf : clock > maxSub
        · simp only [hovf, ↓reduceIte, spec_ok]
          exact ⟨Nat.le_refl _, by scalar_tac⟩
        · simp only [hovf, ↓reduceIte]
          have hNotGt : ¬ (maxSub.val < clock.val) := fun h => hovf h
          have hClkLe : clock.val ≤ maxSub.val := Nat.le_of_not_lt hNotGt
          have hSumLe : clock.val + units.val ≤ Std.U64.max := by
            have hU64m : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, U64.numBits]
            omega
          step as ⟨next_clock, _⟩
          have hRemGe : s.val ≤ bytes.length - i.val := by scalar_tac
          have hNextBound : i.val + s.val ≤ bytes.length := by omega
          by_cases hdone : target < next_clock
          · simp only [hdone, ↓reduceIte]
            step as ⟨i3, hi3⟩
            try simp only [spec_ok]
            exact ⟨by scalar_tac, by scalar_tac⟩
          · simp only [hdone, ↓reduceIte]
            step as ⟨i3, hi3⟩
            try simp only [spec_ok]
            exact ⟨by scalar_tac, by scalar_tac⟩
    · simp only [spec_ok]
      exact ⟨Nat.le_refl _, by scalar_tac⟩
  step with hLoop as ⟨s, e, b, hse, heb⟩
  try simp only [spec_ok]
  exact ⟨hse, heb⟩

theorem utf16_split_byte_offset_spec (bytes : Slice Std.U8) (target : Std.U64)
    (hValid : isValidUtf8List bytes.val = true) :
    utf16.utf16_split_byte_offset bytes target ⦃ res =>
      if utf16LenList bytes.val ≤ target.val then
        res.start.val = bytes.length ∧ res.«end».val = bytes.length ∧ res.split_surrogate = false
      else
        ∃ hStart : res.start.val < bytes.length,
          let lead := bytes.val[res.start.val]
          let c0 := utf16LenList (bytes.val.take res.start.val)
          res.start.val < res.«end».val ∧
          res.«end».val = res.start.val + leadStep lead ∧
          res.«end».val ≤ bytes.length ∧
          isValidUtf8List (bytes.val.take res.start.val) = true ∧
          isValidUtf8List (bytes.val.drop res.start.val) = true ∧
          c0 ≤ target.val ∧ target.val < c0 + leadUnits lead ∧
          res.split_surrogate = decide (c0 < target.val) ⦄ := by
  unfold utf16.utf16_split_byte_offset
  let inv : Std.Usize × Std.U64 → Prop := fun (i, clock) =>
    i.val ≤ bytes.length ∧
    isValidUtf8List (bytes.val.take i.val) = true ∧
    isValidUtf8List (bytes.val.drop i.val) = true ∧
    clock.val = utf16LenList (bytes.val.take i.val) ∧
    clock.val ≤ i.val ∧
    clock.val ≤ target.val
  let post : Std.Usize × Std.Usize × Bool → Prop := fun res =>
    if utf16LenList bytes.val ≤ target.val then
      res.1.val = bytes.length ∧ res.2.1.val = bytes.length ∧ res.2.2 = false
    else
      ∃ hStart : res.1.val < bytes.length,
        let lead := bytes.val[res.1.val]
        let c0 := utf16LenList (bytes.val.take res.1.val)
        res.1.val < res.2.1.val ∧
        res.2.1.val = res.1.val + leadStep lead ∧
        res.2.1.val ≤ bytes.length ∧
        isValidUtf8List (bytes.val.take res.1.val) = true ∧
        isValidUtf8List (bytes.val.drop res.1.val) = true ∧
        c0 ≤ target.val ∧ target.val < c0 + leadUnits lead ∧
        res.2.2 = decide (c0 < target.val)
  have hLoop : utf16.utf16_split_byte_offset_loop bytes target 0#usize 0#u64 (Slice.len bytes) ⦃ post ⦄ := by
    unfold utf16.utf16_split_byte_offset_loop
    refine loop.spec_decr_nat
      (fun (i, _) => bytes.length - i.val) inv post _ (0#usize, 0#u64) ?_
      ⟨by scalar_tac, by simp [isValidUtf8List], hValid, by simp [utf16LenList], by scalar_tac, by scalar_tac⟩
    intro ⟨i, clock⟩ ⟨hiLen, hPfxV, hDropV, hClk, hClkLeI, hClkLeT⟩
    unfold utf16.utf16_split_byte_offset_loop.body
    simp only
    split_ifs with hlt
    · have hiLt : i.val < bytes.length := by scalar_tac
      have hStepSpec : ∀ b : Std.U8,
          (if b < 128#u8 then ok 1#usize
           else if b < 224#u8 then ok 2#usize
           else if b < 240#u8 then ok 3#usize
           else ok 4#usize) ⦃ s => s.val = leadStep b ∧ 1 ≤ s.val ∧ s.val ≤ 4 ⦄ := by
        intro b; simp only [leadStep]; split_ifs <;> simp [spec_ok] <;> scalar_tac
      step as ⟨b, hb⟩
      step with hStepSpec b as ⟨s, hsEq, hs1, hs4⟩
      step as ⟨rem, hrem⟩
      have hBytesLen : (bytes : List Std.U8).length = bytes.length := rfl
      have hNeNil : bytes.val.drop i.val ≠ [] := by
        intro hNil
        have hL := congrArg List.length hNil
        simp only [List.length_drop, List.length_nil] at hL
        omega
      have hHeadEq : (bytes.val.drop i.val).head hNeNil = b := by
        have hDropCons := List.drop_eq_getElem_cons hiLt
        exact Option.some.inj (by rw [← List.head?_eq_some_head hNeNil, hDropCons, List.head?_cons, hb])
      have hFacts := valid_utf8_head_step_facts (bytes.val.drop i.val) hNeNil hDropV
      simp only [hHeadEq] at hFacts
      rcases hFacts with ⟨hStepLeDrop, hTakeScalarV, hDropScalarV, hScalarUnits⟩
      have hNotShort : ¬ (rem < s) := by
        rw [List.length_drop, hBytesLen] at hStepLeDrop
        scalar_tac
      simp only [hNotShort, ↓reduceIte]
      have hUnitsSpec : (if s = 4#usize then ok 2#u64 else ok 1#u64) ⦃ u =>
          u.val = leadUnits b ∧ 1 ≤ u.val ∧ u.val ≤ 2 ⦄ := by
        by_cases h4 : s = 4#usize
        · have hs4v : s.val = 4 := congrArg UScalar.val h4
          have hlb : leadStep b = 4 := hsEq.symm.trans hs4v
          simp [h4, leadUnits, hlb, spec_ok]
        · have hsNe4 : s.val ≠ 4 := fun h => h4 (UScalar.eq_of_val_eq h)
          have hlb : leadStep b ≠ 4 := by omega
          simp [h4, leadUnits, hlb, spec_ok]
      step with hUnitsSpec as ⟨units, huEq, hu1, hu2⟩
      have hU64Max : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
      have hRMax : Std.U64.rMax = 2 ^ 64 - 1 := by decide
      have hUnitsLeMax : units.val ≤ (core.num.U64.MAX : Std.U64).val := by rw [hU64Max]; omega
      step as ⟨maxSub, hmaxSub⟩
      have hMaxSubVal : maxSub.val = 2 ^ 64 - 1 - units.val := by rw [hmaxSub, hRMax]
      have hUsizeLe64 : bytes.length ≤ 2 ^ 64 - 1 := by
        have hB1 : bytes.length ≤ Std.Usize.max := by scalar_tac
        have hB2 : Std.Usize.max ≤ 2 ^ 64 - 1 := by
          simp only [Std.Usize.max, Usize.numBits]
          cases System.Platform.numBits_eq <;> simp [*]
        omega
      have hUnitsLeStep : units.val ≤ leadStep b := huEq ▸ leadUnits_le_leadStep b
      have hNotOvf : ¬ (clock > maxSub) := by
        have hLe : clock.val ≤ maxSub.val := by
          rw [List.length_drop, hBytesLen] at hStepLeDrop
          omega
        intro hgt
        have hgtv : clock.val > maxSub.val := hgt
        omega
      simp only [hNotOvf, ↓reduceIte]
      step as ⟨next_clock, hnextClk⟩
      have hTakeNext : bytes.val.take (i.val + leadStep b) =
          bytes.val.take i.val ++ (bytes.val.drop i.val).take (leadStep b) := by
        rw [List.take_add]
      have hNextPfxV : isValidUtf8List (bytes.val.take (i.val + leadStep b)) = true := by
        rw [hTakeNext]
        exact isValidUtf8List_append_of_valid _ _ hPfxV hTakeScalarV
      have hNextDropV : isValidUtf8List (bytes.val.drop (i.val + leadStep b)) = true := by
        simpa [List.drop_drop, Nat.add_comm] using hDropScalarV
      have hNextClkVal : next_clock.val = utf16LenList (bytes.val.take (i.val + leadStep b)) := by
        rw [hnextClk, hClk, hTakeNext, utf16LenList_append_of_valid _ _ hPfxV, hScalarUnits, huEq]
      by_cases hdone : target < next_clock
      · simp only [hdone, ↓reduceIte]
        step as ⟨i3, hi3⟩
        try simp only [spec_ok]
        dsimp only [post]
        have hAllLen : utf16LenList bytes.val =
            utf16LenList (bytes.val.take (i.val + leadStep b)) +
            utf16LenList (bytes.val.drop (i.val + leadStep b)) := by
          have hSplit := List.take_append_drop (i.val + leadStep b) bytes.val
          calc utf16LenList bytes.val
              = utf16LenList (bytes.val.take (i.val + leadStep b) ++ bytes.val.drop (i.val + leadStep b)) := by
                rw [hSplit]
            _ = _ := utf16LenList_append_of_valid _ _ hNextPfxV
        have hNotLe : ¬ (utf16LenList bytes.val ≤ target.val) := by
          have : target.val < next_clock.val := hdone
          omega
        rw [if_neg hNotLe]
        have hc0LeT : utf16LenList (bytes.val.take i.val) ≤ target.val := by
          rw [← hClk]; exact hClkLeT
        have hi3Step : i3.val = i.val + leadStep (bytes.val[i.val]'(by rw [hBytesLen]; exact hiLt)) := by
          rw [hi3, hsEq, ← hb]
        have hi3Le : i3.val ≤ bytes.length := by
          rw [List.length_drop, hBytesLen] at hStepLeDrop
          rw [hi3, hsEq]
          omega
        refine ⟨hiLt, ?_, hi3Step, hi3Le, hPfxV, hDropV, hc0LeT, ?_, ?_⟩
        · rw [hi3]; omega
        · have : target.val < next_clock.val := hdone
          rw [← hb]
          omega
        · rw [← hClk]
          simp [decide_eq_true_iff]
      · simp only [hdone, ↓reduceIte]
        step as ⟨i3, hi3⟩
        try simp only [spec_ok, inv]
        have hi3Val : i3.val = i.val + leadStep b := by scalar_tac
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [List.length_drop, hBytesLen] at hStepLeDrop; omega
        · rw [hi3Val]; exact hNextPfxV
        · rw [hi3Val]; exact hNextDropV
        · rw [hi3Val]; exact hNextClkVal
        · omega
        · scalar_tac
        · scalar_tac
    · simp only [spec_ok]
      dsimp only [post]
      have hFull : bytes.val.take i.val = bytes.val := by
        apply List.take_of_length_le
        scalar_tac
      have hClockFull : clock.val = utf16LenList bytes.val := by
        rw [hClk, hFull]
      have hLe : utf16LenList bytes.val ≤ target.val := by omega
      rw [if_pos hLe]
      exact ⟨by scalar_tac, by scalar_tac, rfl⟩
  step with hLoop as ⟨s, e, b, hLoopRes⟩
  simpa [post] using hLoopRes

end YoctoCore.Properties.Utf16
