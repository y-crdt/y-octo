/-
The moves of the ring behind the timeline of a client
(`y_octo_core::client_blocks`): what the functions that make room for a block
or close the gap of blocks taken away do to the words of the ring, block by
block.

A function here is handed the ring it works on (`cap` slots, the first block
in the slot `head`) and is described by the word each block of that ring holds
afterwards. `ClientBlocks.lean` turns that into statements about the blocks of
the timeline.
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.ListAux
import YoctoCore.Properties.Ring

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties.ListAux

set_option maxHeartbeats 400000
set_option autoImplicit false

namespace YoctoCore.Properties.Ring

/-! ## Slots of a ring -/

theorem get?_congr {α : Type} {l : List α} {i j : Nat} (h : i = j) : l[i]? = l[j]? := by
  rw [h]

/-- Closes an equation between words of one list whose slots are given by
`slotOf` and `if`s: every case is the same slot on both sides. -/
macro "ring_slots" : tactic =>
  `(tactic| (simp only [slotOf]; split_ifs <;> exact get?_congr (by omega)))

/-- Two blocks of a ring are not in the same slot. -/
theorem slotOf_inj {cap head i j : Nat} (hh : head ≤ cap) (hi : i < cap) (hj : j < cap)
    (h : slotOf cap head i = slotOf cap head j) : i = j := by
  simp only [slotOf] at h
  split_ifs at h <;> omega

/-- A ring that starts a slot earlier: every block is one block later. -/
theorem slotOf_before {c h r : Nat} (hh : h < c) (hr : r + 1 < c) :
    slotOf c (if h = 0 then c - 1 else h - 1) (r + 1) = slotOf c h r := by
  simp only [slotOf]
  split_ifs <;> omega

/-- A ring that starts at its block `g`: every block is `g` blocks earlier. -/
theorem slotOf_shift {c h g i : Nat} (hh : h ≤ c) (hg : g < c) (hi : i + g < c) :
    slotOf c (slotOf c h g) i = slotOf c h (i + g) := by
  simp only [slotOf]
  split_ifs <;> omega

theorem val_setSlice (v : alloc.vec.Vec Std.U128) (i : Nat) (s : List Std.U128) :
    (alloc.vec.Vec.setSlice! v i s).val = v.val.setSlice! i s := by
  simp [alloc.vec.Vec.setSlice!, alloc.vec.Vec.val]

theorem get?_set_slot (l : List Std.U128) {cap head i j : Nat} (x : Std.U128) (hh : head ≤ cap)
    (hc : cap ≤ l.length) (hi : i < cap) (hj : j < cap) :
    (l.set (slotOf cap head i) x)[slotOf cap head j]? =
      if j = i then some x else l[slotOf cap head j]? := by
  rw [get?_set]
  have hil := slotOf_lt_cap hh hi
  by_cases hji : j = i
  · rw [ite_eq_left hji, ite_eq_left ⟨by rw [hji], by omega⟩]
  · rw [ite_eq_right hji, ite_eq_right (fun hc' => hji (slotOf_inj hh hj hi hc'.1))]

/-! ## A run of slots moved by one -/

/-- The slots `x..=y` of a list after `slide_up`: the slots `x + 1..=y` hold
what the slots `x..y` held. -/
theorem get?_part_up (l s s1 : List Std.U128) (x y : Nat) (hxy : x ≤ y) (hy : y < l.length)
    (hs : s = l.slice x (y + 1)) (hlen : s1.length = s.length)
    (hs1 : ∀ k : Nat, s1[k]? = if 0 < k ∧ k < s.length then s[k - 1]? else s[k]?) (p : Nat) :
    (l.setSlice! x s1)[p]? = if x < p ∧ p ≤ y then l[p - 1]? else l[p]? := by
  have hsl : s.length = y + 1 - x := by
    rw [hs, List.slice_length]
    omega
  rw [get?_setSlice l s1 x p (by omega)]
  by_cases hc : x ≤ p ∧ p < x + s1.length
  · rw [ite_eq_left hc, hs1 (p - x)]
    by_cases hp : x < p
    · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨hp, by omega⟩, hs,
        get?_slice l x (y + 1) (p - x - 1) (by omega), ite_eq_left (by omega)]
      exact get?_congr (by omega)
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hs,
        get?_slice l x (y + 1) (p - x) (by omega), ite_eq_left (by omega)]
      exact get?_congr (by omega)
  · rw [ite_eq_right hc, ite_eq_right (by omega)]

/-- The slots `x..=y` of a list after `slide_down`: the slots `x..y` hold what
the slots `x + 1..=y` held. -/
theorem get?_part_down (l s s1 : List Std.U128) (x y : Nat) (hxy : x ≤ y) (hy : y < l.length)
    (hs : s = l.slice x (y + 1)) (hlen : s1.length = s.length)
    (hs1 : ∀ k : Nat, s1[k]? = if k + 1 < s.length then s[k + 1]? else s[k]?) (p : Nat) :
    (l.setSlice! x s1)[p]? = if x ≤ p ∧ p < y then l[p + 1]? else l[p]? := by
  have hsl : s.length = y + 1 - x := by
    rw [hs, List.slice_length]
    omega
  rw [get?_setSlice l s1 x p (by omega)]
  by_cases hc : x ≤ p ∧ p < x + s1.length
  · rw [ite_eq_left hc, hs1 (p - x)]
    by_cases hp : p < y
    · rw [ite_eq_left (by omega), ite_eq_left ⟨hc.1, hp⟩, hs,
        get?_slice l x (y + 1) (p - x + 1) (by omega), ite_eq_left (by omega)]
      exact get?_congr (by omega)
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hs,
        get?_slice l x (y + 1) (p - x) (by omega), ite_eq_left (by omega)]
      exact get?_congr (by omega)
  · rw [ite_eq_right hc, ite_eq_right (by omega)]

/-! ## `move_up` and `move_down` -/

/-- `move_up`: the blocks `a + 1..=b` of the ring hold what the blocks `a..b`
held, and every other block holds what it did. -/
theorem move_up_spec (cb : client_blocks.ClientBlocksCore) (cap head a b : Std.Usize)
    (hh : head.val ≤ cap.val) (hc : cap.val ≤ cb.buf.val.length) (hab : a.val ≤ b.val)
    (hb : b.val < cap.val) :
    client_blocks.ClientBlocksCore.move_up cb cap head a b ⦃ cb' =>
      cb'.head = cb.head ∧ cb'.len = cb.len ∧ cb'.end_clock = cb.end_clock ∧
      cb'.buf.val.length = cb.buf.val.length ∧
      ∀ r : Nat, r < cap.val →
        cb'.buf.val[slotOf cap.val head.val r]? =
          if a.val < r ∧ r ≤ b.val then cb.buf.val[slotOf cap.val head.val (r - 1)]?
          else cb.buf.val[slotOf cap.val head.val r]? ⦄ := by
  unfold client_blocks.ClientBlocksCore.move_up
  have z : (0#usize : Std.Usize).val = 0 := by scalar_tac
  step as ⟨tail, htail⟩
  have htv : tail.val = cap.val - head.val := by scalar_tac
  by_cases h1 : b < tail
  · simp only [h1, ↓reduceIte]
    have hbt : b.val < cap.val - head.val := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = head.val + b.val + 1 := by scalar_tac
    step as ⟨s, back, hs, hsl, hback⟩
    step as ⟨s1, hs1l, hs1⟩
    have hs' : s.val = cb.buf.val.slice i.val (head.val + b.val + 1) := by
      rw [← hi2v]
      exact hs
    have hv : (back s1).val = cb.buf.val.setSlice! i.val s1.val := by
      rw [hback, val_setSlice]
    have hphys := get?_part_up cb.buf.val s.val s1.val i.val (head.val + b.val) (by scalar_tac)
      (by scalar_tac) hs' hs1l hs1
    refine ⟨?_, ?_⟩
    · show (back s1).val.length = cb.buf.val.length
      rw [hv, List.length_setSlice!]
    · intro r hr
      show (back s1).val[slotOf cap.val head.val r]? = _
      rw [hv, hphys]
      ring_slots
  · simp only [h1, ↓reduceIte]
    have hbt : cap.val - head.val ≤ b.val := by scalar_tac
    by_cases h2 : a >= tail
    · simp only [h2, ↓reduceIte]
      have hat : cap.val - head.val ≤ a.val := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = b.val - (cap.val - head.val) + 1 := by scalar_tac
      step as ⟨s, back, hs, hsl, hback⟩
      step as ⟨s1, hs1l, hs1⟩
      have hs' : s.val = cb.buf.val.slice i.val (b.val - (cap.val - head.val) + 1) := by
        rw [← hi2v]
        exact hs
      have hv : (back s1).val = cb.buf.val.setSlice! i.val s1.val := by
        rw [hback, val_setSlice]
      have hphys := get?_part_up cb.buf.val s.val s1.val i.val (b.val - (cap.val - head.val))
        (by scalar_tac) (by scalar_tac) hs' hs1l hs1
      refine ⟨?_, ?_⟩
      · show (back s1).val.length = cb.buf.val.length
        rw [hv, List.length_setSlice!]
      · intro r hr
        show (back s1).val[slotOf cap.val head.val r]? = _
        rw [hv, hphys]
        ring_slots
    · simp only [h2, ↓reduceIte]
      have hat : a.val < cap.val - head.val := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = b.val - (cap.val - head.val) + 1 := by scalar_tac
      step as ⟨s, back, hs, hsl, hback⟩
      step as ⟨s1, hs1l, hs1⟩
      have hs' : s.val = cb.buf.val.slice 0 (b.val - (cap.val - head.val) + 1) := by
        rw [← hi1v, ← z]
        exact hs
      have hv : (back s1).val = cb.buf.val.setSlice! 0 s1.val := by
        rw [hback, val_setSlice]
      have hp1 := get?_part_up cb.buf.val s.val s1.val 0 (b.val - (cap.val - head.val))
        (by omega) (by omega) hs' hs1l hs1
      have hvl : (back s1).val.length = cb.buf.val.length := by
        rw [hv, List.length_setSlice!]
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = cap.val - 1 := by scalar_tac
      step as ⟨word, hword⟩
      have hwb : cb.buf.val[cap.val - 1]? = some word := by
        have hg : (back s1).val[i2.val]? = some word := get?_at (by omega) hword
        rw [hv, hp1, ite_eq_right (by omega), hi2v] at hg
        exact hg
      step as ⟨old, back1, hold, hback1⟩
      have hv1 : (back1 word).val = (back s1).val.set 0 word := by
        rw [hback1]
        simp
      have hv1l : (back1 word).val.length = cb.buf.val.length := by
        rw [hv1, List.length_set, hvl]
      have hq1 : ∀ q : Nat, (back1 word).val[q]? =
          if q = 0 then cb.buf.val[cap.val - 1]? else (back s1).val[q]? := by
        intro q
        rw [hv1, get?_set]
        by_cases hq : q = 0
        · rw [ite_eq_left ⟨hq, by omega⟩, ite_eq_left hq, hwb]
        · rw [ite_eq_right (fun hc' => hq hc'.1), ite_eq_right hq]
      step as ⟨i3, hi3⟩
      step as ⟨s2, back2, hs2, hs2l, hback2⟩
      step as ⟨s3, hs3l, hs3⟩
      have hs2' : s2.val = (back1 word).val.slice i3.val (cap.val - 1 + 1) := by
        have e : cap.val - 1 + 1 = cap.val := by omega
        rw [e]
        exact hs2
      have hv2 : (back2 s3).val = (back1 word).val.setSlice! i3.val s3.val := by
        rw [hback2, val_setSlice]
      have hp3 := get?_part_up (back1 word).val s2.val s3.val i3.val (cap.val - 1) (by scalar_tac)
        (by omega) hs2' hs3l hs3
      refine ⟨?_, ?_⟩
      · show (back2 s3).val.length = cb.buf.val.length
        rw [hv2, List.length_setSlice!, hv1l]
      · intro r hr
        show (back2 s3).val[slotOf cap.val head.val r]? = _
        rw [hv2, hp3, hq1, hq1, hv, hp1, hp1]
        ring_slots

/-- `move_down`: the blocks `a..b` of the ring hold what the blocks
`a + 1..=b` held, and every other block holds what it did. -/
theorem move_down_spec (cb : client_blocks.ClientBlocksCore) (cap head a b : Std.Usize)
    (hh : head.val ≤ cap.val) (hc : cap.val ≤ cb.buf.val.length) (hab : a.val ≤ b.val)
    (hb : b.val < cap.val) :
    client_blocks.ClientBlocksCore.move_down cb cap head a b ⦃ cb' =>
      cb'.head = cb.head ∧ cb'.len = cb.len ∧ cb'.end_clock = cb.end_clock ∧
      cb'.buf.val.length = cb.buf.val.length ∧
      ∀ r : Nat, r < cap.val →
        cb'.buf.val[slotOf cap.val head.val r]? =
          if a.val ≤ r ∧ r < b.val then cb.buf.val[slotOf cap.val head.val (r + 1)]?
          else cb.buf.val[slotOf cap.val head.val r]? ⦄ := by
  unfold client_blocks.ClientBlocksCore.move_down
  have z : (0#usize : Std.Usize).val = 0 := by scalar_tac
  step as ⟨tail, htail⟩
  have htv : tail.val = cap.val - head.val := by scalar_tac
  by_cases h1 : b < tail
  · simp only [h1, ↓reduceIte]
    have hbt : b.val < cap.val - head.val := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = head.val + b.val + 1 := by scalar_tac
    step as ⟨s, back, hs, hsl, hback⟩
    step as ⟨s1, hs1l, hs1⟩
    have hs' : s.val = cb.buf.val.slice i.val (head.val + b.val + 1) := by
      rw [← hi2v]
      exact hs
    have hv : (back s1).val = cb.buf.val.setSlice! i.val s1.val := by
      rw [hback, val_setSlice]
    have hphys := get?_part_down cb.buf.val s.val s1.val i.val (head.val + b.val)
      (by scalar_tac) (by scalar_tac) hs' hs1l hs1
    refine ⟨?_, ?_⟩
    · show (back s1).val.length = cb.buf.val.length
      rw [hv, List.length_setSlice!]
    · intro r hr
      show (back s1).val[slotOf cap.val head.val r]? = _
      rw [hv, hphys]
      ring_slots
  · simp only [h1, ↓reduceIte]
    have hbt : cap.val - head.val ≤ b.val := by scalar_tac
    by_cases h2 : a >= tail
    · simp only [h2, ↓reduceIte]
      have hat : cap.val - head.val ≤ a.val := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = b.val - (cap.val - head.val) + 1 := by scalar_tac
      step as ⟨s, back, hs, hsl, hback⟩
      step as ⟨s1, hs1l, hs1⟩
      have hs' : s.val = cb.buf.val.slice i.val (b.val - (cap.val - head.val) + 1) := by
        rw [← hi2v]
        exact hs
      have hv : (back s1).val = cb.buf.val.setSlice! i.val s1.val := by
        rw [hback, val_setSlice]
      have hphys := get?_part_down cb.buf.val s.val s1.val i.val
        (b.val - (cap.val - head.val)) (by scalar_tac) (by scalar_tac) hs' hs1l hs1
      refine ⟨?_, ?_⟩
      · show (back s1).val.length = cb.buf.val.length
        rw [hv, List.length_setSlice!]
      · intro r hr
        show (back s1).val[slotOf cap.val head.val r]? = _
        rw [hv, hphys]
        ring_slots
    · simp only [h2, ↓reduceIte]
      have hat : a.val < cap.val - head.val := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨s, back, hs, hsl, hback⟩
      step as ⟨s1, hs1l, hs1⟩
      have hs' : s.val = cb.buf.val.slice i.val (cap.val - 1 + 1) := by
        have e : cap.val - 1 + 1 = cap.val := by omega
        rw [e]
        exact hs
      have hv : (back s1).val = cb.buf.val.setSlice! i.val s1.val := by
        rw [hback, val_setSlice]
      have hp1 := get?_part_down cb.buf.val s.val s1.val i.val (cap.val - 1) (by scalar_tac)
        (by omega) hs' hs1l hs1
      have hvl : (back s1).val.length = cb.buf.val.length := by
        rw [hv, List.length_setSlice!]
      step as ⟨word, hword⟩
      have hwb : cb.buf.val[0]? = some word := by
        have hg : (back s1).val[(0#usize : Std.Usize).val]? = some word :=
          get?_at (by omega) hword
        rw [hv, hp1, ite_eq_right (by scalar_tac), z] at hg
        exact hg
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = cap.val - 1 := by scalar_tac
      step as ⟨old, back1, hold, hback1⟩
      have hv1 : (back1 word).val = (back s1).val.set (cap.val - 1) word := by
        rw [hback1, ← hi1v]
        simp
      have hv1l : (back1 word).val.length = cb.buf.val.length := by
        rw [hv1, List.length_set, hvl]
      have hq1 : ∀ q : Nat, (back1 word).val[q]? =
          if q = cap.val - 1 then cb.buf.val[0]? else (back s1).val[q]? := by
        intro q
        rw [hv1, get?_set]
        by_cases hq : q = cap.val - 1
        · rw [ite_eq_left ⟨hq, by omega⟩, ite_eq_left hq, hwb]
        · rw [ite_eq_right (fun hc' => hq hc'.1), ite_eq_right hq]
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      have hi3v : i3.val = b.val - (cap.val - head.val) + 1 := by scalar_tac
      step as ⟨s2, back2, hs2, hs2l, hback2⟩
      step as ⟨s3, hs3l, hs3⟩
      have hs2' : s2.val = (back1 word).val.slice 0 (b.val - (cap.val - head.val) + 1) := by
        rw [← hi3v, ← z]
        exact hs2
      have hv2 : (back2 s3).val = (back1 word).val.setSlice! 0 s3.val := by
        rw [hback2, val_setSlice]
      have hp3 := get?_part_down (back1 word).val s2.val s3.val 0
        (b.val - (cap.val - head.val)) (by omega) (by omega) hs2' hs3l hs3
      refine ⟨?_, ?_⟩
      · show (back2 s3).val.length = cb.buf.val.length
        rw [hv2, List.length_setSlice!, hv1l]
      · intro r hr
        show (back2 s3).val[slotOf cap.val head.val r]? = _
        rw [hv2, hp3, hq1, hq1, hv, hp1, hp1]
        ring_slots

end YoctoCore.Properties.Ring
