import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.Varint

/-- Pure functional reference encoder for unsigned 64-bit LEB128 varints. -/
def encodeNat (n : Nat) : List Std.U8 :=
  if h : n < 128 then
    [Std.U8.ofNatCore n (by simp [Std.U8.max]; omega)]
  else
    Std.U8.ofNatCore (n % 128 + 128) (by simp [Std.U8.max]; omega) :: encodeNat (n / 128)
termination_by n

theorem encodeNat_length_pos (n : Nat) : 0 < (encodeNat n).length := by
  rw [encodeNat]
  split_ifs <;> simp

theorem encodeNat_length_bound (k : Nat) (n : Nat) (hk : 1 ≤ k) (hn : n < 2 ^ (7 * k)) :
    (encodeNat n).length ≤ k := by
  induction k generalizing n with
  | zero => omega
  | succ m ih =>
    rw [encodeNat]
    split_ifs with hlt
    · simp
    · simp only [List.length_cons]
      cases m with
      | zero =>
        have : (2 : Nat) ^ (7 * (0 + 1)) = 128 := by decide
        omega
      | succ m' =>
        have hm : 1 ≤ m' + 1 := Nat.succ_le_succ (Nat.zero_le _)
        have hpow : 2 ^ (7 * (m' + 1 + 1)) = 128 * 2 ^ (7 * (m' + 1)) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, show (2 : Nat) ^ 7 = 128 by decide, Nat.mul_comm]
        have hdiv : n / 128 < 2 ^ (7 * (m' + 1)) := by omega
        exact Nat.succ_le_succ (ih (n / 128) hm hdiv)

theorem nat_or_mul_two_pow_eq_add (a b k : Nat) (ha : a < 2 ^ k) :
    a ||| (b * 2 ^ k) = a + b * 2 ^ k := by
  have hDiv2 : ∀ (n i : Nat), Nat.testBit n (i + 1) = Nat.testBit (n / 2) i := by
    intro n i
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_comm (2 ^ i) 2,
      ← Nat.div_div_eq_div_mul]
  have hStep : ∀ (x y : Nat), x ||| (2 * y) = 2 * (x / 2 ||| y) + x % 2 := by
    intro x y
    apply Nat.eq_of_testBit_eq
    intro j
    cases j with
    | zero =>
      have hmod : (2 * (x / 2 ||| y) + x % 2) % 2 = x % 2 := by omega
      have h2y0 : (2 * y) % 2 = 0 := by omega
      simp [Nat.testBit_zero, Nat.testBit_or, hmod, h2y0]
    | succ m =>
      rw [Nat.testBit_or, hDiv2 x m, hDiv2 (2 * y) m, hDiv2 (2 * (x / 2 ||| y) + x % 2) m]
      rw [show (2 * y) / 2 = y by omega,
          show (2 * (x / 2 ||| y) + x % 2) / 2 = x / 2 ||| y by omega, Nat.testBit_or]
  induction k generalizing a with
  | zero =>
    have : a = 0 := by omega
    subst this
    simp
  | succ m ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (b * 2 ^ m) 2]
    rw [hStep a (b * 2 ^ m), ih (a / 2) (by omega)]
    omega

private theorem list_take_set_succ {α : Type _} :
    ∀ (l : List α) (k : Nat) (x : α), k < l.length →
      (l.set k x).take (k + 1) = l.take k ++ [x]
  | [], _, _, hk => by cases hk
  | _ :: _, 0, x, _ => by simp [List.set, List.take]
  | hd :: tl, k + 1, x, hk => by
    simp only [List.set, List.take, List.cons_append, List.cons.injEq, true_and]
    exact list_take_set_succ tl k x (Nat.lt_of_succ_lt_succ hk)

private theorem list_take_succ_append {α : Type _} :
    ∀ (l : List α) (k : Nat) (hk : k < l.length),
      l.take k ++ [l[k]] = l.take (k + 1)
  | [], _, hk => by cases hk
  | _ :: _, 0, _ => by simp [List.take]
  | _ :: tl, k + 1, hk => by
    simp only [List.take, List.cons_append, List.getElem_cons_succ, List.cons.injEq, true_and]
    exact list_take_succ_append tl k (Nat.lt_of_succ_lt_succ hk)

theorem decode_var_u64_total (input : Slice Std.U8) :
    varint.decode_var_u64 input ⦃ res =>
      match res with
      | .Ok (_, used) => used.val ≤ input.length ∧ used.val ≤ 10
      | .Err _ => True ⦄ := by
  unfold varint.decode_var_u64 varint.decode_var_u64_loop
  refine loop.spec_decr_nat
    (fun (_, i) => 10 - i.val)
    (fun (_, i) => i.val ≤ 10 ∧ i.val ≤ input.length)
    (fun (res : core.result.Result (Std.U64 × Std.Usize) CodecError) =>
      match res with | .Ok (_, used) => used.val ≤ input.length ∧ used.val ≤ 10 | .Err _ => True)
    _ (0#u64, 0#usize) ?_ ⟨by scalar_tac, by scalar_tac⟩
  intro ⟨value, i⟩ ⟨hi10, hiLen⟩
  unfold varint.decode_var_u64_loop.body
  simp only
  by_cases hlt : i < Slice.len input
  · simp only [hlt, ↓reduceIte]
    by_cases h10 : i < 10#usize
    · simp only [h10, ↓reduceIte]
      have hi9 : i.val ≤ 9 := by scalar_tac
      have hiLtLen : i.val < input.length := by scalar_tac
      step as ⟨b, _⟩
      by_cases h9 : i = 9#usize
      · simp only [h9, ↓reduceIte]
        by_cases hb : b > 1#u8
        · simp [hb, spec_ok]
        · simp only [hb, ↓reduceIte]
          step as ⟨_, _⟩
          step as ⟨_, _⟩
          step as ⟨_, _⟩
          step as ⟨_, _⟩
          step as ⟨_, _⟩
          step as ⟨_, _⟩
          step as ⟨i6, hi6⟩
          step as ⟨i7, _⟩
          split_ifs
          · simp only [spec_ok]; exact ⟨by scalar_tac, by scalar_tac⟩
          · simp only [spec_ok]; exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
      · simp only [h9, ↓reduceIte]
        step as ⟨_, _⟩
        step as ⟨_, _⟩
        step as ⟨_, _⟩
        step as ⟨_, _⟩
        step as ⟨_, _⟩
        step as ⟨_, _⟩
        step as ⟨i6, hi6⟩
        step as ⟨i7, _⟩
        split_ifs
        · simp only [spec_ok]; exact ⟨by scalar_tac, by scalar_tac⟩
        · simp only [spec_ok]; exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
    · simp only [h10, ↓reduceIte]
      split_ifs <;> simp [spec_ok]
  · simp only [hlt, ↓reduceIte]
    split_ifs <;> simp [spec_ok]

theorem encode_var_u64_buf_loop_spec (v : Std.U64) :
    varint.encode_var_u64_buf_loop v (Array.repeat 10#usize 0#u8) 0#usize ⦃ p =>
      p.2.2.val ≤ 9 ∧
      ∃ h : p.1.val < 128,
        p.2.1.val.take p.2.2.val ++ [Std.U8.ofNatCore p.1.val (by simp [Std.U8.max]; omega)] = encodeNat v.val ⦄ := by
  unfold varint.encode_var_u64_buf_loop
  let inv : Std.U64 × Array Std.U8 10#usize × Std.Usize → Prop := fun (x, buf, len) =>
    len.val ≤ 9 ∧ x.val < 2 ^ (7 * (10 - len.val)) ∧
    buf.val.take len.val ++ encodeNat x.val = encodeNat v.val
  refine loop.spec_decr_nat
    (fun (x, _, _) => x.val) inv _ _ (v, Array.repeat 10#usize 0#u8, 0#usize) ?_ ?_
  · intro ⟨x, buf, len⟩ ⟨hLen, hxPow, hEncEq⟩
    unfold varint.encode_var_u64_buf_loop.body
    simp only
    split_ifs with hlt9 hge
    · have hLenLt9 : len.val < 9 := by scalar_tac
      have hBufLen : buf.val.length = 10 := buf.property
      step as ⟨i, hiPost⟩
      step as ⟨i1, hi1Post⟩
      step as ⟨i2, hi2Post⟩
      step as ⟨a, haPost⟩
      step as ⟨len1, hlen1Post⟩
      step as ⟨value1, hval1Post⟩
      try simp only [spec_ok]
      have hShift : x.val >>> 7 = x.val / 128 := Nat.shiftRight_eq_div_pow _ 7
      have hPowStep : 2 ^ (7 * (10 - len.val)) = 128 * 2 ^ (7 * (10 - (len.val + 1))) := by
        have : 7 * (10 - len.val) = 7 * (10 - (len.val + 1)) + 7 := by omega
        rw [this, Nat.pow_add, show (2 : Nat) ^ 7 = 128 by decide, Nat.mul_comm]
      have hXGe128 : 128 ≤ x.val := by scalar_tac
      have hStepByte : i2 = Std.U8.ofNatCore (x.val % 128 + 128) (by simp [Std.U8.max]; omega) := by
        apply UScalar.eq_of_val_eq
        have hi : i.val = x.val % 256 := by scalar_tac
        have hMod128 : (x.val % 256) &&& 127 = x.val % 128 := by
          have := Nat.and_two_pow_sub_one_eq_mod (x.val % 256) 7
          simpa [show (2 : Nat) ^ 7 - 1 = 127 by decide] using this
        have hi2 : i2.val = (x.val % 128) ||| 128 := by
          have hi2Val : i2.val = i1.val ||| 128 := by
            rw [hi2Post]
            exact BitVec.toNat_or i1.bv (128#u8).bv
          have hi1Val : i1.val = i.val &&& 127 := by
            rw [hi1Post]
            exact BitVec.toNat_and i.bv (127#u8).bv
          rw [hi2Val, hi1Val, hi, hMod128]
        have hOr : (x.val % 128) ||| 128 = x.val % 128 + 128 := by
          have hm : x.val % 128 < 128 := Nat.mod_lt _ (by decide)
          have := nat_or_mul_two_pow_eq_add (x.val % 128) 1 7 hm
          simpa [Nat.add_comm] using this
        rw [hi2, hOr]
        simp only [Std.U8.ofNatCore, UScalar.ofNatCore, UScalar.val]
        rfl
      have haTake : a.val.take len1.val = buf.val.take len.val ++ [i2] := by
        have haVal : a.val = buf.val.set len.val i2 := by
          rw [haPost, Array.set_val_eq]
        rw [hlen1Post, haVal]
        exact list_take_set_succ buf.val len.val i2 (by omega)
      refine ⟨⟨by omega, ?_, ?_⟩, ?_⟩
      · rw [hlen1Post, hval1Post, hShift]
        omega
      · have hNotLt : ¬ (x.val < 128) := by omega
        have hUnfold : encodeNat x.val =
            Std.U8.ofNatCore (x.val % 128 + 128) (by simp [Std.U8.max]; omega) :: encodeNat (x.val / 128) := by
          rw [encodeNat, dif_neg hNotLt]
        rw [haTake, hval1Post, hShift, List.append_assoc, List.singleton_append,
            hStepByte, ← hEncEq, hUnfold]
      · rw [hval1Post, hShift]
        omega
    · simp only [spec_ok]
      have hxLt : x.val < 128 := by scalar_tac
      have hUnfold : encodeNat x.val = [Std.U8.ofNatCore x.val (by simp [Std.U8.max]; omega)] := by
        rw [encodeNat, dif_pos hxLt]
      refine ⟨hLen, hxLt, ?_⟩
      simpa [hUnfold] using hEncEq
    · have hLen9 : len.val = 9 := by scalar_tac
      rw [hLen9] at hxPow
      have hxLt : x.val < 128 := by simpa using hxPow
      have hUnfold : encodeNat x.val = [Std.U8.ofNatCore x.val (by simp [Std.U8.max]; omega)] := by
        rw [encodeNat, dif_pos hxLt]
      simp only [spec_ok]
      refine ⟨hLen, hxLt, ?_⟩
      simpa [hUnfold] using hEncEq
  · refine ⟨by simp, ?_, by simp⟩
    have hv : v.val < 2 ^ 64 := by scalar_tac
    have hpow : (2 : Nat) ^ 64 ≤ 2 ^ (7 * (10 - 0)) := Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.lt_of_lt_of_le hv hpow

theorem encode_var_u64_buf_spec (v : Std.U64) :
    varint.encode_var_u64_buf v ⦃ res =>
      1 ≤ res.2.val ∧ res.2.val ≤ 10 ∧ res.1.val.take res.2.val = encodeNat v.val ⦄ := by
  unfold varint.encode_var_u64_buf
  step with encode_var_u64_buf_loop_spec v as ⟨value1, buf1, len, hLen, hxLt, hEnc⟩
  have hBufLen : buf1.val.length = 10 := buf1.property
  step as ⟨i, hiPost⟩
  step as ⟨buf2, hbuf2Post⟩
  step as ⟨len1, hlen1Post⟩
  have hLastByte : i = Std.U8.ofNatCore value1.val (by simp [Std.U8.max]; omega) := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  have hTake : buf2.val.take len1.val = encodeNat v.val := by
    have hVal : buf2.val = buf1.val.set len.val i := by
      rw [hbuf2Post, Array.set_val_eq]
    rw [hlen1Post, hVal, list_take_set_succ buf1.val len.val i (by omega), hLastByte, hEnc]
  exact ⟨by omega, by omega, hTake⟩

theorem encode_var_u64_total (v : Std.U64) :
    varint.encode_var_u64 v ⦃ out => 1 ≤ out.length ∧ out.length ≤ 10 ∧ out.val = encodeNat v.val ⦄ := by
  unfold varint.encode_var_u64
  step with encode_var_u64_buf_spec v as ⟨buf, len, hLen1, hLen10, hTake⟩
  unfold varint.encode_var_u64_loop
  let inv : alloc.vec.Vec Std.U8 × Std.Usize → Prop := fun (out, i) =>
    i.val ≤ len.val ∧ out.val = buf.val.take i.val
  refine loop.spec_decr_nat
    (fun (_, i) => len.val - i.val) inv
    (fun (out : alloc.vec.Vec Std.U8) => 1 ≤ out.length ∧ out.length ≤ 10 ∧ out.val = encodeNat v.val)
    _ (alloc.vec.Vec.new Std.U8, 0#usize) ?_ ⟨by scalar_tac, by simp [alloc.vec.Vec.new]⟩
  intro ⟨out, i⟩ ⟨hiLe, houtVal⟩
  unfold varint.encode_var_u64_loop.body
  simp only
  split_ifs with hlt
  · have hiLtLen : i.val < len.val := by scalar_tac
    have hBufLen : buf.val.length = 10 := buf.property
    have hiLt10 : i.val < 10 := by omega
    have hCap : out.length < Std.Usize.max := by
      have : out.length = i.val := by
        simp only [alloc.vec.Vec.length, houtVal, List.length_take]
        omega
      scalar_tac
    step as ⟨i1, hi1⟩
    step as ⟨out1, hout1⟩
    step as ⟨i2, hi2⟩
    try simp only [spec_ok]
    have hi1Eq : i1 = buf.val[i.val]'(by omega) := hi1
    have hout1Val : out1.val = buf.val.take (i.val + 1) := by
      rw [hout1, houtVal, hi1Eq, list_take_succ_append buf.val i.val (by omega)]
    exact ⟨⟨by scalar_tac, by rw [hi2]; exact hout1Val⟩, by scalar_tac⟩
  · simp only [spec_ok]
    have hiEq : i.val = len.val := by scalar_tac
    have houtEnc : out.val = encodeNat v.val := by rw [houtVal, hiEq, hTake]
    have houtLen : out.length = len.val := by
      have hBufLen : buf.val.length = 10 := buf.property
      simp only [alloc.vec.Vec.length, houtVal, hiEq, List.length_take]
      omega
    exact ⟨by omega, by omega, houtEnc⟩

/-- `decode_var_i32_with_sign` is total, and what it says it read is inside
the input. -/
theorem decode_var_i32_with_sign_total (input : Slice Std.U8) :
    varint.decode_var_i32_with_sign input ⦃ r =>
      ∀ p used, r = core.result.Result.Ok (p, used) → used.val ≤ input.length ⦄ := by
  unfold varint.decode_var_i32_with_sign
  step as ⟨b, hb⟩
  split_ifs with hbTrue
  · simp [spec_ok]
  · step as ⟨first, hFirst⟩
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨num, hnum⟩
    unfold varint.decode_var_i32_with_sign_loop
    refine loop.spec_decr_nat
      (fun (_, curr, _, shift) =>
        (if (curr.val &&& 128) = 0 then 0 else 1) + (39 - min 39 shift.val))
      (fun (_, _, idx, shift) => shift.val ≤ 38 ∧ idx.val ≤ input.length)
      (fun (r : core.result.Result ((Std.I32 × Bool) × Std.Usize) CodecError) =>
        ∀ p used, r = core.result.Result.Ok (p, used) → used.val ≤ input.length)
      _ (num, first, 1#usize, 6#u32) ?_ ⟨by scalar_tac, by scalar_tac⟩
    intro ⟨num1, curr1, idx1, shift1⟩ ⟨hShift, hIdx⟩
    unfold varint.decode_var_i32_with_sign_loop.body
    simp only
    step as ⟨mflag, hmflag⟩
    cases hMore : (mflag != 0#u8)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hI32Max : (core.num.I32.MAX : Std.I32).val = 2147483647 := by decide
      have hCastMax : (IScalar.hcast .U64 core.num.I32.MAX).val = 2147483647 := by decide
      have hMaxMagSpec :
          (if (i != 0#u8) then do
             let i2 ← lift (IScalar.hcast .U64 core.num.I32.MAX)
             i2 + 1#u64
           else ok (IScalar.hcast .U64 core.num.I32.MAX)) ⦃ max_mag =>
             max_mag.val = if (i != 0#u8) = true then 2147483648 else 2147483647 ⦄ := by
        cases hNeg : (i != 0#u8)
        · simp only [Bool.false_eq_true, ↓reduceIte, spec_ok]
          exact hCastMax
        · simp only [↓reduceIte]
          step as ⟨i2, hi2⟩
          step as ⟨res, hres⟩
          rw [hi2, hCastMax] at hres
          exact hres
      step with hMaxMagSpec as ⟨max_mag, hMaxMag⟩
      by_cases hgt : num1 > max_mag
      · simp only [hgt, ↓reduceIte, spec_ok]
        intro _ _ hEq
        cases hEq
      · simp only [hgt, ↓reduceIte]
        have hNumLeMax : num1.val ≤ max_mag.val := by scalar_tac
        cases hNeg : (i != 0#u8)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hLe : num1.val ≤ 2147483647 := by
            simp only [hNeg, Bool.false_eq_true, ↓reduceIte] at hMaxMag
            omega
          step as ⟨val, hval⟩
          intro p used hEq
          cases hEq
          exact hIdx
        · simp only [↓reduceIte]
          have hMax2148 : max_mag.val = 2147483648 := by
            simp only [hNeg, ↓reduceIte] at hMaxMag
            exact hMaxMag
          step as ⟨i2', hi2'⟩
          step as ⟨i3, hi3⟩
          have hi3Val : i3.val = 2147483648 := by
            have : i2'.val = 2147483647 := by rw [hi2', hCastMax]
            scalar_tac
          by_cases hmin : num1 = i3
          · simp only [hmin, ↓reduceIte, spec_ok]
            intro p used hEq
            cases hEq
            exact hIdx
          · simp only [hmin, ↓reduceIte]
            have hBound : num1.val ≤ 2147483647 := by
              have hNe : num1.val ≠ 2147483648 := by
                intro hEq; apply hmin; apply UScalar.eq_of_val_eq; omega
              omega
            have hI32MaxEq : Std.I32.max = 2147483647 := by simp [Std.I32.max, Std.I32.numBits]
            have hI32MinEq : Std.I32.min = -2147483648 := by simp [Std.I32.min, Std.I32.numBits]
            have hCastLe : (num1.val : Int) ≤ IScalar.max .I32 := by
              simp [IScalar.max, Std.I32.numBits]
              omega
            step with UScalar.hcast_inBounds_spec .I32 num1 hCastLe as ⟨i4, hi4⟩
            have hi4Neg : Std.I32.min < i4.val := by omega
            step as ⟨val, hval⟩
            intro p used hEq
            cases hEq
            exact hIdx
    · simp only [↓reduceIte]
      have hCurrBit : (curr1.val &&& 128) ≠ 0 := by
        have hm : mflag.val ≠ 0 := by
          intro hz
          have : mflag = 0#u8 := UScalar.eq_of_val_eq (by simpa using hz)
          simp [this] at hMore
        have hEq : mflag.val = curr1.val &&& 128 := by
          rw [hmflag]; exact BitVec.toNat_and curr1.bv (128#u8).bv
        omega
      by_cases hOvf : shift1 ≥ 32#u32
      · simp only [hOvf, ↓reduceIte, spec_ok]
        intro _ _ hEq
        cases hEq
      · simp only [hOvf, ↓reduceIte]
        by_cases hEof : idx1 ≥ Slice.len input
        · simp only [hEof, ↓reduceIte, spec_ok]
          intro _ _ hEq
          cases hEq
        · simp only [hEof, ↓reduceIte]
          step as ⟨curr2, hcurr2⟩
          step as ⟨i3, hi3⟩
          step as ⟨i4, hi4⟩
          step as ⟨i5, hi5⟩
          step as ⟨num2, hnum2⟩
          step as ⟨shift2, hshift2⟩
          step as ⟨idx2, hidx2⟩
          have hShiftLt32 : shift1.val < 32 := by scalar_tac
          have hShift2Le : shift2.val ≤ 38 := by omega
          refine ⟨hShift2Le, by scalar_tac, ?_⟩
          split_ifs <;> omega

/-- `decode_var_i32` is total, and what it says it read is inside the input. -/
theorem decode_var_i32_total (input : Slice Std.U8) :
    varint.decode_var_i32 input ⦃ r =>
      ∀ val used, r = core.result.Result.Ok (val, used) → used.val ≤ input.length ⦄ := by
  unfold varint.decode_var_i32
  step with decode_var_i32_with_sign_total input as ⟨r, hr⟩
  cases r with
  | Ok val =>
    step as ⟨cf, hcf⟩
    rw [hcf]; dsimp only
    rcases val with ⟨⟨val1, neg⟩, len⟩
    show spec (ok _) _
    simp only [spec_ok]
    intro v used hEq
    cases hEq
    exact hr _ _ rfl
  | Err e =>
    step as ⟨cf, hcf⟩
    rw [hcf]; dsimp only
    unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
    simp [core.convert.FromSame, spec_ok, bind_ok]

theorem encode_var_i32_buf_spec (v : Std.I32) :
    varint.encode_var_i32_buf v ⦃ res => 1 ≤ res.2.val ∧ res.2.val ≤ 5 ⦄ := by
  unfold varint.encode_var_i32_buf
  have hLoopSpec : ∀ (buf0 : Array Std.U8 5#usize) (rem0 : Std.U64) (len0 : Std.Usize),
      1 ≤ len0.val → len0.val ≤ 5 →
      rem0.val < 2 ^ (7 * (5 - len0.val)) →
      varint.encode_var_i32_buf_loop buf0 rem0 len0 ⦃ res =>
        1 ≤ res.2.val ∧ res.2.val ≤ 5 ⦄ := by
    intro buf0 rem0 len0 h1 h5 hRem0
    unfold varint.encode_var_i32_buf_loop
    let inv : Array Std.U8 5#usize × Std.U64 × Std.Usize → Prop := fun (_, rem, len) =>
      1 ≤ len.val ∧ len.val ≤ 5 ∧ rem.val < 2 ^ (7 * (5 - len.val))
    refine loop.spec_decr_nat
      (fun (_, rem, _) => rem.val) inv _ _ (buf0, rem0, len0) ?_ ⟨h1, h5, hRem0⟩
    intro ⟨b, rem, len⟩ ⟨hb1, hb5, hRem⟩
    unfold varint.encode_var_i32_buf_loop.body
    simp only
    by_cases hlt5 : len < 5#usize
    · simp only [hlt5, ↓reduceIte]
      by_cases hgt : rem > 0#u64
      · simp only [hgt, ↓reduceIte]
        have hLenLt5 : len.val < 5 := by scalar_tac
        have hBLen : b.val.length = 5 := b.property
        have hMoreSpec : (if rem > 127#u64 then ok 128#u8 else ok 0#u8) ⦃ _ => True ⦄ := by
          split_ifs <;> simp [spec_ok]
        step with hMoreSpec as ⟨more, _⟩
        step as ⟨i, _⟩
        step as ⟨i1, _⟩
        step as ⟨i2, _⟩
        step as ⟨a, _⟩
        step as ⟨len1, hlen1⟩
        step as ⟨num1, hnum1⟩
        try simp only [spec_ok]
        have hShift : rem.val >>> 7 = rem.val / 128 := Nat.shiftRight_eq_div_pow _ 7
        refine ⟨⟨by omega, by omega, ?_⟩, ?_⟩
        · have hpow : 2 ^ (7 * (5 - len.val)) = 128 * 2 ^ (7 * (5 - (len.val + 1))) := by
            have : 7 * (5 - len.val) = 7 * (5 - (len.val + 1)) + 7 := by omega
            rw [this, Nat.pow_add, show (2 : Nat) ^ 7 = 128 by decide, Nat.mul_comm]
          rw [hlen1, hnum1, hShift]
          omega
        · rw [hnum1, hShift]; scalar_tac
      · simp only [hgt, ↓reduceIte, spec_ok]; exact ⟨hb1, hb5⟩
    · simp only [hlt5, ↓reduceIte, spec_ok]; exact ⟨hb1, hb5⟩
  have hNumSpec : (if v < 0#i32
      then
        if v = core.num.I32.MIN
        then do
          let i ← lift (IScalar.hcast .U64 core.num.I32.MAX)
          i + 1#u64
        else do
          let i ← -. v
          ok (IScalar.hcast .U64 i)
      else ok (IScalar.hcast .U64 v)) ⦃ num => num.val ≤ 2 ^ 31 ⦄ := by
    split_ifs with hlt hmin
    · have hCastMax : (IScalar.hcast .U64 core.num.I32.MAX).val = 2147483647 := by decide
      step as ⟨i, hi⟩
      step as ⟨num, hnum⟩
      try simp only [spec_ok]
      have : i.val = 2147483647 := by rw [hi, hCastMax]
      omega
    · have hI32MinEq : Std.I32.min = -2147483648 := by simp [Std.I32.min, Std.I32.numBits]
      have hU64MaxNat : UScalar.max UScalarTy.U64 = 2 ^ 64 - 1 := by
        rw [UScalar.max_UScalarTy_U64_eq]; simp [U64.max, U64.numBits]
      have hRMin : Std.I32.rMin = -2147483648 := by decide
      have hNe : v.val ≠ -2147483648 := by
        intro hEq; apply hmin; apply IScalar.eq_of_val_eq; simpa [hRMin] using hEq
      have hNotMin : v.val ≠ Std.I32.min := by rw [hI32MinEq]; exact hNe
      step as ⟨i, hi⟩
      have hvMin : Std.I32.min ≤ v.val := by scalar_tac
      have hBound : 0 ≤ i.val ∧ i.val ≤ UScalar.max .U64 := by
        have hltZ : v.val < 0 := by scalar_tac
        have hiVal : i.val = -v.val := hi
        rw [hU64MaxNat]
        omega
      have hCast : ((IScalar.hcast .U64 i).val : Int) = i.val := by
        simpa [lift] using IScalar.hcast_inBounds_spec .U64 i hBound
      try simp only [spec_ok]
      omega
    · have hI32Max : Std.I32.max = 2147483647 := by simp [Std.I32.max, Std.I32.numBits]
      have hU64MaxNat : UScalar.max UScalarTy.U64 = 2 ^ 64 - 1 := by
        rw [UScalar.max_UScalarTy_U64_eq]; simp [U64.max, U64.numBits]
      have hvMax : v.val ≤ Std.I32.max := by scalar_tac
      have hBound : 0 ≤ v.val ∧ v.val ≤ UScalar.max .U64 := by
        have hgeZ : 0 ≤ v.val := by scalar_tac
        rw [hU64MaxNat]
        omega
      have hCast : ((IScalar.hcast .U64 v).val : Int) = v.val := by
        simpa [lift] using IScalar.hcast_inBounds_spec .U64 v hBound
      simp only [spec_ok]
      omega
  step with hNumSpec as ⟨num, hNumLe⟩
  have hFirstMoreSpec : (if num > 63#u64 then ok 128#u8 else ok 0#u8) ⦃ _ => True ⦄ := by
    split_ifs <;> simp [spec_ok]
  have hFirstSignSpec : (if v < 0#i32 then ok 64#u8 else ok 0#u8) ⦃ _ => True ⦄ := by
    split_ifs <;> simp [spec_ok]
  step with hFirstMoreSpec as ⟨first_more⟩
  step with hFirstSignSpec as ⟨first_sign⟩
  step as ⟨i, _⟩
  step as ⟨i1, _⟩
  step as ⟨i2, _⟩
  step as ⟨i3, _⟩
  step as ⟨a, _⟩
  step as ⟨num1, hnum1⟩
  refine spec_mono (hLoopSpec a num1 1#usize (by decide) (by decide) ?_) (fun _ h => h)
  have hShift : num.val >>> 6 = num.val / 64 := Nat.shiftRight_eq_div_pow _ 6
  have hOne : (1#usize).val = 1 := rfl
  rw [hnum1, hShift, hOne]
  have hPow28 : (2 : Nat) ^ 28 = 268435456 := by decide
  have hPow31 : (2 : Nat) ^ 31 = 2147483648 := by decide
  omega

theorem encode_var_i32_total (v : Std.I32) :
    varint.encode_var_i32 v ⦃ out => 1 ≤ out.length ∧ out.length ≤ 5 ⦄ := by
  unfold varint.encode_var_i32
  step with encode_var_i32_buf_spec v as ⟨buf, len, hLen1, hLen5⟩
  unfold varint.encode_var_i32_loop
  let inv : alloc.vec.Vec Std.U8 × Std.Usize → Prop := fun (out, i) =>
    i.val ≤ len.val ∧ out.length = i.val
  refine loop.spec_decr_nat
    (fun (_, i) => len.val - i.val) inv
    (fun (out : alloc.vec.Vec Std.U8) => 1 ≤ out.length ∧ out.length ≤ 5)
    _ (alloc.vec.Vec.new Std.U8, 0#usize) ?_ ⟨by scalar_tac, by simp [alloc.vec.Vec.new]⟩
  intro ⟨out, i⟩ ⟨hiLe, houtLen⟩
  unfold varint.encode_var_i32_loop.body
  simp only
  split_ifs with hlt
  · have hiLtLen : i.val < len.val := by scalar_tac
    have hBufLen : buf.val.length = 5 := buf.property
    have hCap : out.length < Std.Usize.max := by scalar_tac
    step as ⟨i1, _⟩
    step as ⟨out1, hout1⟩
    step as ⟨i2, hi2⟩
    exact ⟨⟨by scalar_tac, by scalar_tac⟩, by scalar_tac⟩
  · simp only [spec_ok]
    have hiEq : i.val = len.val := by scalar_tac
    omega

/-- The copy loop of `encode_var_i32` gives the first `len` bytes of the
buffer. -/
theorem encode_var_i32_loop_prefix (buf : Array Std.U8 5#usize) (len : Std.Usize)
    (hLen : len.val ≤ 5) :
    varint.encode_var_i32_loop buf len (alloc.vec.Vec.new Std.U8) 0#usize ⦃ out =>
      out.val = buf.val.take len.val ⦄ := by
  unfold varint.encode_var_i32_loop
  let inv : alloc.vec.Vec Std.U8 × Std.Usize → Prop := fun (out, i) =>
    i.val ≤ len.val ∧ out.val = buf.val.take i.val
  refine loop.spec_decr_nat
    (fun (_, i) => len.val - i.val) inv
    (fun (out : alloc.vec.Vec Std.U8) => out.val = buf.val.take len.val)
    _ (alloc.vec.Vec.new Std.U8, 0#usize) ?_ ⟨by scalar_tac, by simp [alloc.vec.Vec.new]⟩
  intro ⟨out, i⟩ ⟨hiLe, houtVal⟩
  unfold varint.encode_var_i32_loop.body
  simp only
  split_ifs with hlt
  · have hiLtLen : i.val < len.val := by scalar_tac
    have hBufLen : buf.val.length = 5 := buf.property
    have hiLt5 : i.val < 5 := by omega
    have hCap : out.length < Std.Usize.max := by
      have : out.length = i.val := by
        simp only [alloc.vec.Vec.length, houtVal, List.length_take]
        omega
      scalar_tac
    step as ⟨i1, hi1⟩
    step as ⟨out1, hout1⟩
    step as ⟨i2, hi2⟩
    have hi1Eq : i1 = buf.val[i.val]'(by omega) := hi1
    have hout1Val : out1.val = buf.val.take (i.val + 1) := by
      rw [hout1, houtVal, hi1Eq, list_take_succ_append buf.val i.val (by omega)]
    exact ⟨⟨by scalar_tac, by rw [hi2]; exact hout1Val⟩, by scalar_tac⟩
  · simp only [spec_ok]
    have hiEq : i.val = len.val := by scalar_tac
    rw [houtVal, hiEq]

/-- **`encode_var_i32` is the valid prefix of `encode_var_i32_buf`.** Whenever
the buffer encoder answers `(buf, len)`, the vector encoder answers exactly
the bytes `buf[0..len)`, with `1 ≤ len ≤ 5`. -/
theorem encode_var_i32_prefix (v : Std.I32) (buf : Array Std.U8 5#usize) (len : Std.Usize)
    (hbuf : varint.encode_var_i32_buf v = ok (buf, len)) :
    varint.encode_var_i32 v ⦃ out =>
      out.val = buf.val.take len.val ∧ 1 ≤ len.val ∧ len.val ≤ 5 ⦄ := by
  have hspec := encode_var_i32_buf_spec v
  rw [hbuf] at hspec
  simp only [spec_ok] at hspec
  obtain ⟨hLen1, hLen5⟩ := hspec
  have hb : varint.encode_var_i32_buf v ⦃ r => r.1 = buf ∧ r.2 = len ⦄ := by
    rw [hbuf]
    exact (spec_ok _).mpr ⟨rfl, rfl⟩
  unfold varint.encode_var_i32
  step with hb as ⟨b, l, hb1, hb2⟩
  subst hb1
  subst hb2
  exact spec_mono (encode_var_i32_loop_prefix b l hLen5) (fun out h => ⟨h, hLen1, hLen5⟩)

theorem decode_var_u64_loop_encodeNat
    (buf : Slice Std.U8) (tail : List Std.U8)
    (v : Nat) (acc : Std.U64) (i : Std.Usize)
    (hi : i.val ≤ 9)
    (hAcc : acc.val < 2 ^ (7 * i.val))
    (hSum : acc.val + v * 2 ^ (7 * i.val) < 2 ^ 64)
    (hBuf : buf.val.drop i.val = encodeNat v ++ tail) :
    varint.decode_var_u64_loop buf acc i ⦃ res =>
      ∃ len : Std.Usize,
        res = .Ok (Std.U64.ofNatCore (acc.val + v * 2 ^ (7 * i.val))
          (by simp [Std.U64.max]; omega), len) ∧
        len.val = i.val + (encodeNat v).length ⦄ := by
  have hTerm : ∀ (m : Nat) (v0 : Nat) (acc0 : Std.U64) (i0 : Std.Usize),
      (encodeNat v0).length = m →
      i0.val ≤ 9 →
      acc0.val < 2 ^ (7 * i0.val) →
      (hS : acc0.val + v0 * 2 ^ (7 * i0.val) < 2 ^ 64) →
      buf.val.drop i0.val = encodeNat v0 ++ tail →
      varint.decode_var_u64_loop buf acc0 i0 ⦃ res =>
        ∃ len : Std.Usize,
          res = .Ok (Std.U64.ofNatCore (acc0.val + v0 * 2 ^ (7 * i0.val))
            (by simp [Std.U64.max]; omega), len) ∧
          len.val = i0.val + (encodeNat v0).length ⦄ := by
    intro m
    induction m with
    | zero =>
      intro v0 _ _ hZero
      have := encodeNat_length_pos v0
      omega
    | succ k ih =>
      intro v0 acc0 i0 hLenM hi0 hAcc0 hS0 hBuf0
      unfold varint.decode_var_u64_loop
      unfold loop
      unfold varint.decode_var_u64_loop.body
      have hDropLen : 0 < (buf.val.drop i0.val).length := by
        rw [hBuf0, List.length_append, hLenM]; omega
      have hBufLen : buf.val.length = buf.length := rfl
      have hiLen : i0.val < buf.length := by
        simp only [List.length_drop, hBufLen] at hDropLen
        omega
      have hi10 : i0.val < 10 := by omega
      have hByte0 : buf.val[i0.val] = (encodeNat v0)[0]'(by omega) := by
        have hDrop0 : (buf.val.drop i0.val)[0]'hDropLen = buf.val[i0.val]'hiLen := by
          simp [List.getElem_drop]
        rw [← hDrop0]
        simp only [hBuf0]
        rw [List.getElem_append_left (by omega)]
      dsimp only
      rw [if_pos (by scalar_tac), if_pos (by scalar_tac)]
      by_cases hvLt : v0 < 128
      · have hEnc : encodeNat v0 = [Std.U8.ofNatCore v0 (by simp [Std.U8.max]; omega)] := by
          rw [encodeNat, dif_pos hvLt]
        have hByteVal : (buf.val[i0.val]).val = v0 := by
          simp only [hByte0, hEnc, List.getElem_singleton]
          rfl
        have hShiftVal : i0.val * 7 < 64 := by omega
        have hBitOr : acc0.val ||| ((v0 % 128) <<< (i0.val * 7) % 2 ^ 64) =
            acc0.val + v0 * 2 ^ (7 * i0.val) := by
          have hMod : v0 % 128 = v0 := Nat.mod_eq_of_lt hvLt
          rw [hMod, Nat.shiftLeft_eq]
          have hMulLt : v0 * 2 ^ (i0.val * 7) < 2 ^ 64 := by
            rw [Nat.mul_comm i0.val 7]; omega
          rw [Nat.mod_eq_of_lt hMulLt, Nat.mul_comm i0.val 7]
          exact nat_or_mul_two_pow_eq_add acc0.val v0 (7 * i0.val) hAcc0
        have hLast : (buf.val[i0.val].val &&& 128) = 0 := by
          rw [hByteVal]
          apply Nat.eq_of_testBit_eq
          intro j
          simp only [Nat.testBit_and, Nat.zero_testBit]
          rcases Nat.lt_or_ge j 7 with hj7 | hj7
          · have : (128 : Nat).testBit j = false := by
              match j with
              | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
              | _ + 7 => omega
            simp [this]
          · have hLtPow : v0 < 2 ^ j :=
              Nat.lt_of_lt_of_le (by omega : v0 < 2 ^ 7) (Nat.pow_le_pow_right (by decide : 0 < 2) hj7)
            simp [Nat.testBit_lt_two_pow hLtPow]
        step as ⟨b, b_post⟩
        by_cases h9 : i0 = 9#usize
        · subst h9
          simp only [↓reduceIte]
          have h9Val : (9#usize).val = 9 := rfl
          have hBle1 : ¬ (b > 1#u8) := by
            have hbEq : b.val = v0 := by rw [← hByteVal, b_post]
            rw [h9Val] at hS0
            have h263 : (2 : Nat) ^ (7 * 9) = 2 ^ 63 := rfl
            have h264 : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := rfl
            have hv0Le1 : v0 ≤ 1 := by omega
            intro hgt
            have : 1 < b.val := hgt
            omega
          simp only [hBle1, ↓reduceIte]
          step as ⟨i2, i2_post⟩
          step as ⟨bits, bits_post⟩
          step as ⟨i3, i3_post⟩
          step as ⟨i4, i4_post⟩
          have hi3 : i3.val = 9 * 7 := by rw [i3_post]
          have hU32Max : UScalar.max UScalarTy.U32 = 2 ^ 32 - 1 := by
            rw [UScalar.max_UScalarTy_U32_eq]; simp [U32.max, U32.numBits]
          have hi4Eq : i4.val = 9 * 7 := by
            have h := UScalar.cast_inBounds_spec .U32 i3 (by rw [hi3, hU32Max]; omega)
            simpa [lift, ← i4_post, hi3] using h
          have hi4Lt64 : i4.val < 64 := by rw [hi4Eq]; omega
          step as ⟨i5, i5_post⟩
          step as ⟨value1, value1_post⟩
          step as ⟨i6, i6_post⟩
          step as ⟨i7, i7_post⟩
          have hi7Eq0 : i7 = 0#u8 := by
            apply UScalar.eq_of_val_eq
            have hbEq : b.val = v0 := by rw [← hByteVal, b_post]
            have : i7.val = b.val &&& 128 := by rw [i7_post]; exact BitVec.toNat_and b.bv (128#u8).bv
            rw [this, hbEq, ← hByteVal]
            exact hLast
          simp only [hi7Eq0, ↓reduceIte, bind_ok, spec_ok]
          refine ⟨i6, ?_, by simp [i6_post, hEnc]⟩
          congr 2
          apply UScalar.eq_of_val_eq
          have hv1 : value1.val = acc0.val ||| i5.val := by
            rw [value1_post]; exact BitVec.toNat_or acc0.bv i5.bv
          have hU64Size : U64.size = 2 ^ 64 := by simp [U64.size, Std.U64.numBits]
          have hi5 : i5.val = (bits.val <<< i4.val) % 2 ^ 64 := by
            rw [i5_post, hU64Size]
          have hU64MaxNat : UScalar.max UScalarTy.U64 = 2 ^ 64 - 1 := by
            rw [UScalar.max_UScalarTy_U64_eq]; simp [U64.max, U64.numBits]
          have hbits : bits.val = i2.val := by
            have hi2Lt : i2.val < 2 ^ 8 := i2.bv.isLt
            have h := UScalar.cast_inBounds_spec .U64 i2 (by rw [hU64MaxNat]; omega)
            simpa [lift, ← bits_post] using h
          have hi2 : i2.val = b.val &&& 127 := by
            rw [i2_post]; exact BitVec.toNat_and b.bv (127#u8).bv
          have hLow : b.val &&& 127 = v0 % 128 := by
            have hbEq : b.val = v0 := by rw [← hByteVal, b_post]
            have hModEq : v0 &&& 127 = v0 % 128 := by
              simpa [show (2 : Nat) ^ 7 - 1 = 127 by decide] using Nat.and_two_pow_sub_one_eq_mod v0 7
            rw [hbEq, hModEq]
          rw [hv1, hi5, hbits, hi2, hLow, hi4Eq]
          simpa [hEnc] using hBitOr
        · simp only [h9, ↓reduceIte]
          step as ⟨i2, i2_post⟩
          step as ⟨bits, bits_post⟩
          step as ⟨i3, i3_post⟩
          step as ⟨i4, i4_post⟩
          have hi4Lt64 : i4.val < 64 := by
            have : i3.val = i0.val * 7 := by scalar_tac
            have : i4.val = i3.val := by scalar_tac
            omega
          step as ⟨i5, i5_post⟩
          step as ⟨value1, value1_post⟩
          step as ⟨i6, i6_post⟩
          step as ⟨i7, i7_post⟩
          have hi7Eq0 : i7 = 0#u8 := by
            apply UScalar.eq_of_val_eq
            have hbEq : b.val = v0 := by rw [← hByteVal, b_post]
            have : i7.val = b.val &&& 128 := by rw [i7_post]; exact BitVec.toNat_and b.bv (128#u8).bv
            rw [this, hbEq]
            simpa [hByteVal] using hLast
          simp only [hi7Eq0, ↓reduceIte, bind_ok, spec_ok]
          refine ⟨i6, ?_, by scalar_tac⟩
          congr 2
          apply UScalar.eq_of_val_eq
          have hv1 : value1.val = acc0.val ||| i5.val := by
            rw [value1_post]; exact BitVec.toNat_or acc0.bv i5.bv
          have hi5 : i5.val = (bits.val <<< i4.val) % 2 ^ 64 := by scalar_tac
          have hbits : bits.val = i2.val := by scalar_tac
          have hi2 : i2.val = b.val &&& 127 := by
            rw [i2_post]; exact BitVec.toNat_and b.bv (127#u8).bv
          have hLow : b.val &&& 127 = v0 % 128 := by
            have hbEq : b.val = v0 := by rw [← hByteVal, b_post]
            have hModEq : v0 &&& 127 = v0 % 128 := by
              simpa [show (2 : Nat) ^ 7 - 1 = 127 by decide] using Nat.and_two_pow_sub_one_eq_mod v0 7
            rw [hbEq, hModEq]
          have hi4 : i4.val = i0.val * 7 := by
            have : i3.val = i0.val * 7 := by scalar_tac
            have : i4.val = i3.val := by scalar_tac
            omega
          rw [hv1, hi5, hbits, hi2, hLow, hi4]
          simpa [hEnc] using hBitOr
      · have hvGe : 128 ≤ v0 := by omega
        have hiLt9 : i0.val < 9 := by
          by_contra h
          have hiEq9 : i0.val = 9 := by omega
          rw [hiEq9] at hS0
          have : (2 : Nat) ^ (7 * 9) = 2 ^ 63 := rfl
          have : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := rfl
          omega
        have hEnc : encodeNat v0 =
            Std.U8.ofNatCore (v0 % 128 + 128) (by simp [Std.U8.max]; omega) :: encodeNat (v0 / 128) := by
          rw [encodeNat, dif_neg hvLt]
        have hLenSub : (encodeNat (v0 / 128)).length = k := by
          rw [hEnc, List.length_cons] at hLenM; omega
        have hByteVal : (buf.val[i0.val]).val = v0 % 128 + 128 := by
          simp only [hByte0, hEnc, List.getElem_cons_zero]
          rfl
        have hDrop1 : buf.val.drop (i0.val + 1) = encodeNat (v0 / 128) ++ tail := by
          have := congrArg List.tail hBuf0
          rw [← List.drop_one, List.drop_drop] at this
          try rw [Nat.add_comm 1 i0.val] at this
          simpa [hEnc] using this
        have hSum1 : acc0.val + (v0 % 128) * 2 ^ (7 * i0.val) + (v0 / 128) * 2 ^ (7 * (i0.val + 1)) < 2 ^ 64 := by
          have hpow : 2 ^ (7 * (i0.val + 1)) = 128 * 2 ^ (7 * i0.val) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
          rw [hpow, ← Nat.mul_assoc, Nat.mul_comm (v0 / 128) 128, Nat.add_assoc, ← Nat.add_mul,
            show v0 % 128 + 128 * (v0 / 128) = v0 by omega]
          exact hS0
        have hLenBufGt : i0.val < buf.length := by
          have := congrArg List.length hDrop1
          simp only [List.length_drop, List.length_append, alloc.vec.Vec.length] at *
          have hDrop0 := congrArg List.length hBuf0
          simp only [List.length_drop, List.length_append, hEnc, List.length_cons] at hDrop0
          omega
        step as ⟨b, b_post⟩
        have hNe9 : i0 ≠ 9#usize := by
          intro h
          have : i0.val = 9 := congrArg UScalar.val h
          omega
        simp only [hNe9, ↓reduceIte]
        step as ⟨i2, i2_post⟩
        step as ⟨bits, bits_post⟩
        step as ⟨i3, i3_post⟩
        step as ⟨i4, i4_post⟩
        have hi4Lt64 : i4.val < 64 := by
          have : i3.val = i0.val * 7 := by scalar_tac
          have : i4.val = i3.val := by scalar_tac
          omega
        step as ⟨i5, i5_post⟩
        step as ⟨value1, value1_post⟩
        step as ⟨i6, i6_post⟩
        step as ⟨i7, i7_post⟩
        have hi7Ne0 : i7 ≠ 0#u8 := by
          intro hzero
          have hbVal : b.val = v0 % 128 + 128 := by rw [← hByteVal, b_post]
          have h7 : Nat.testBit i7.val 7 = true := by
            have hEq : i7.val = b.val &&& 128 := by
              rw [i7_post]; exact BitVec.toNat_and b.bv (128#u8).bv
            rw [hEq, Nat.testBit_and, hbVal]
            have hm : v0 % 128 < 128 := Nat.mod_lt _ (by decide)
            have hQuot : (v0 % 128 + 128) / 128 = 1 := by omega
            simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hQuot]
          have h0 : Nat.testBit i7.val 7 = false := by simp [hzero]
          rw [h7] at h0; cases h0
        simp only [hi7Ne0, ↓reduceIte, bind_ok]
        · -- Step into recursive loop iteration
          have hValEq : value1.val = acc0.val + (v0 % 128) * 2 ^ (7 * i0.val) := by
            have hLow : (b.val &&& 127) = v0 % 128 := by
              have hb : b.val = v0 % 128 + 128 := by rw [← hByteVal, b_post]
              rw [hb]
              have hm : v0 % 128 < 128 := Nat.mod_lt _ (by decide)
              have := Nat.and_two_pow_sub_one_eq_mod (v0 % 128 + 128) 7
              simpa [show (2 : Nat) ^ 7 - 1 = 127 by decide, show (v0 % 128 + 128) % 128 = v0 % 128 by omega] using this
            have hBitOr : acc0.val ||| ((v0 % 128) <<< (i0.val * 7) % 2 ^ 64) =
                acc0.val + (v0 % 128) * 2 ^ (7 * i0.val) := by
              have hMulLt : (v0 % 128) * 2 ^ (i0.val * 7) < 2 ^ 64 := by
                have hm : v0 % 128 < 128 := Nat.mod_lt _ (by decide)
                have hp : (2 : Nat) ^ (i0.val * 7) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by omega) (by omega)
                have hBoundMul : (v0 % 128) * 2 ^ (i0.val * 7) ≤ 127 * 2 ^ 56 := Nat.mul_le_mul (by omega) hp
                exact lt_of_le_of_lt hBoundMul (by decide)
              rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hMulLt, Nat.mul_comm i0.val 7]
              exact nat_or_mul_two_pow_eq_add acc0.val (v0 % 128) (7 * i0.val) hAcc0
            have hv1 : value1.val = acc0.val ||| i5.val := by
              rw [value1_post]; exact BitVec.toNat_or acc0.bv i5.bv
            have hi5 : i5.val = (bits.val <<< i4.val) % 2 ^ 64 := by scalar_tac
            have hbits : bits.val = i2.val := by scalar_tac
            have hi2 : i2.val = b.val &&& 127 := by
              rw [i2_post]; exact BitVec.toNat_and b.bv (127#u8).bv
            have hi4 : i4.val = i0.val * 7 := by
              have : i3.val = i0.val * 7 := by scalar_tac
              have : i4.val = i3.val := by scalar_tac
              omega
            rw [hv1, hi5, hbits, hi2, hi4, hLow]
            exact hBitOr
          have hAcc1 : value1.val < 2 ^ (7 * (i0.val + 1)) := by
            rw [hValEq]
            have hpow : 2 ^ (7 * (i0.val + 1)) = 128 * 2 ^ (7 * i0.val) := by
              rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
            have hm : v0 % 128 < 128 := Nat.mod_lt _ (by decide)
            rw [hpow]
            calc acc0.val + (v0 % 128) * 2 ^ (7 * i0.val)
                < 2 ^ (7 * i0.val) + (v0 % 128) * 2 ^ (7 * i0.val) := Nat.add_lt_add_right hAcc0 _
              _ = (1 + v0 % 128) * 2 ^ (7 * i0.val) := by rw [Nat.add_mul, Nat.one_mul]
              _ ≤ 128 * 2 ^ (7 * i0.val) := Nat.mul_le_mul_right _ (by omega)
          have hEqSum : value1.val + (v0 / 128) * 2 ^ (7 * (i0.val + 1)) =
              acc0.val + v0 * 2 ^ (7 * i0.val) := by
            rw [hValEq]
            have hpow : 2 ^ (7 * (i0.val + 1)) = 128 * 2 ^ (7 * i0.val) := by
              rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
            rw [hpow, ← Nat.mul_assoc, Nat.mul_comm (v0 / 128) 128, Nat.add_assoc, ← Nat.add_mul,
              show v0 % 128 + 128 * (v0 / 128) = v0 by omega]
          have hIh := ih (v0 / 128) value1 i6 hLenSub (by scalar_tac) (by simpa [i6_post] using hAcc1)
            (by rw [hValEq]; simpa [i6_post] using hSum1) (by simpa [i6_post] using hDrop1)
          unfold varint.decode_var_u64_loop at hIh
          refine spec_mono hIh ?_
          intro res ⟨len, hRes, hLenRes⟩
          refine ⟨len, ?_, ?_⟩
          · rw [hRes]; congr 2; apply UScalar.eq_of_val_eq
            simpa [i6_post] using hEqSum
          · rw [hLenRes, hEnc, List.length_cons, i6_post]; omega
  exact hTerm (encodeNat v).length v acc i rfl hi hAcc hSum hBuf

theorem decode_encode_var_u64_buf_roundtrip (v : Std.U64) (tail : List Std.U8) (buf : Slice Std.U8) :
    varint.encode_var_u64_buf v ⦃ res =>
      buf.val = res.1.val.take res.2.val ++ tail →
      varint.decode_var_u64 buf ⦃ dec =>
        dec = .Ok (v, res.2) ⦄ ⦄ := by
  refine spec_mono (encode_var_u64_buf_spec v) ?_
  intro ⟨arr, len⟩ hSpec hBuf
  dsimp only at hSpec
  rcases hSpec with ⟨_, hLen10, hTake⟩
  unfold varint.decode_var_u64
  have hDrop : buf.val.drop 0 = encodeNat v.val ++ tail := by
    simp [hBuf, hTake]
  have hv : 0 + v.val * 2 ^ (7 * 0) < 2 ^ 64 := by
    simp; scalar_tac
  refine spec_mono (decode_var_u64_loop_encodeNat buf tail v.val 0#u64 0#usize
    (by decide) (by simp) hv hDrop) ?_
  intro dec ⟨used, hDec, hLen⟩
  have hV : Std.U64.ofNatCore v.val (by scalar_tac) = v := by
    apply UScalar.eq_of_val_eq
    rfl
  have hLenVal : used.val = len.val := by
    have hArrLen : arr.val.length = 10 := arr.property
    have hTakeLen : (arr.val.take len.val).length = (encodeNat v.val).length := congrArg List.length hTake
    rw [List.length_take, hArrLen, Nat.min_eq_left hLen10] at hTakeLen
    have hZero : (0#usize).val = 0 := rfl
    omega
  have hUsedEq : used = len := UScalar.eq_of_val_eq hLenVal
  simpa [hV, hUsedEq] using hDec

theorem decode_encode_var_u64_roundtrip (v : Std.U64) (tail : List Std.U8) (buf : Slice Std.U8) :
    varint.encode_var_u64 v ⦃ enc =>
      buf.val = enc.val ++ tail →
      varint.decode_var_u64 buf ⦃ res =>
        ∃ len : Std.Usize, res = .Ok (v, len) ∧ len.val = enc.length ⦄ ⦄ := by
  refine spec_mono (encode_var_u64_total v) ?_
  intro enc ⟨_, _, hEncVal⟩ hBuf
  unfold varint.decode_var_u64
  have hDrop : buf.val.drop 0 = encodeNat v.val ++ tail := by
    simp [hBuf, hEncVal]
  have hv : 0 + v.val * 2 ^ (7 * 0) < 2 ^ 64 := by
    simp; scalar_tac
  refine spec_mono (decode_var_u64_loop_encodeNat buf tail v.val 0#u64 0#usize
    (by decide) (by simp) hv hDrop) ?_
  intro res ⟨len, hRes, hLen⟩
  refine ⟨len, ?_, ?_⟩
  · have hV : Std.U64.ofNatCore v.val (by scalar_tac) = v := by
      apply UScalar.eq_of_val_eq
      rfl
    simpa [hV] using hRes
  · simp only [alloc.vec.Vec.length, hEncVal] at *
    simp at hLen
    exact hLen

end YoctoCore.Properties.Varint
