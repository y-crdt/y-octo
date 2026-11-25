/-
The ring of words behind the timeline of a client
(`y_octo_core::client_blocks`): the word a block is kept as, the slot of a
block in a ring, the moves of a run of words by one slot, and the blocks a
ring holds.

`blocksOf` reads any values of the fields of a `ClientBlocksCore` as a list of
blocks, the way `ClientBlocksCore::ring` does. The theorems of
`ClientBlocks.lean` are about that list, so none of them assumes anything
about the representation.
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.ListAux

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties.ListAux

set_option maxHeartbeats 400000
set_option autoImplicit false

namespace YoctoCore.Properties.Ring

/-! ## From a Hoare triple to a value -/

/-- A computation that meets a postcondition answers a value that meets it. -/
theorem ok_of_spec {α : Type} {m : Result α} {p : α → Prop} (h : spec m p) :
    ∃ v, m = ok v ∧ p v := by
  cases m with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact ((spec_vis i k).mp h).elim
  | div => exact (spec_div.mp h).elim

theorem get?_at {α : Type} {l : List α} {i : Nat} {x : α} (h : i < l.length) (hx : x = l[i]) :
    l[i]? = some x := by
  rw [hx]
  exact List.getElem?_eq_getElem h

/-! ## Lists, slot by slot -/

section Lists

variable {α : Type}

theorem get?_set (l : List α) (i p : Nat) (x : α) :
    (l.set i x)[p]? = if p = i ∧ i < l.length then some x else l[p]? := by
  rw [set_eq_upd]
  by_cases h : p = i
  · rw [h, get?_upd_self]
    by_cases hi : i < l.length
    · obtain ⟨a, ha⟩ := get?_some hi
      rw [ha, ite_eq_left ⟨rfl, hi⟩]
      rfl
    · rw [get?_none (Nat.le_of_not_lt hi), ite_eq_right (fun hc => hi hc.2)]
      rfl
  · rw [get?_upd_ne _ _ h, ite_eq_right (fun hc => h hc.1)]

theorem get?_append_one (l : List α) (x : α) (p : Nat) :
    (l ++ [x])[p]? = if p < l.length then l[p]? else if p = l.length then some x else none := by
  by_cases h : p < l.length
  · rw [ite_eq_left h, get?_append_left h]
  · rw [ite_eq_right h]
    by_cases e : p = l.length
    · rw [ite_eq_left e, e, get?_snoc_last]
    · rw [ite_eq_right e]
      apply get?_none
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- A part of a list. -/
theorem get?_slice (l : List α) (a b k : Nat) (hb : b ≤ l.length) :
    (l.slice a b)[k]? = if a + k < b then l[a + k]? else none := by
  by_cases h : a + k < b
  · rw [ite_eq_left h]
    exact List.getElem?_slice a b k l ⟨hb, h⟩
  · rw [ite_eq_right h]
    apply get?_none
    rw [List.slice_length]
    omega

/-- A list with a part of it written over. -/
theorem get?_setSlice (l s : List α) (a p : Nat) (h : a + s.length ≤ l.length) :
    (l.setSlice! a s)[p]? = if a ≤ p ∧ p < a + s.length then s[p - a]? else l[p]? := by
  by_cases hc : a ≤ p ∧ p < a + s.length
  · rw [ite_eq_left hc]
    exact List.setSlice!_getElem?_middle l s a p ⟨hc.1, by omega, by omega⟩
  · rw [ite_eq_right hc]
    exact List.setSlice!_getElem?_same l s a p (by omega)

theorem get?_replicate (x : α) : ∀ n k : Nat,
    (List.replicate n x)[k]? = if k < n then some x else none
  | 0, k => by
    rw [ite_eq_right (Nat.not_lt_zero k)]
    exact get?_none (by simp)
  | n + 1, 0 => by
    rw [ite_eq_left (Nat.succ_pos n)]
    rfl
  | n + 1, k + 1 => by
    show (x :: List.replicate n x)[k + 1]? = _
    rw [List.getElem?_cons_succ, get?_replicate x n k]
    by_cases h : k < n
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- A list made longer. -/
theorem get?_resize (l : List α) (n p : Nat) (x : α) (h : l.length ≤ n) :
    (l.resize n x)[p]? = if p < l.length then l[p]? else if p < n then some x else none := by
  have e : l.resize n x = l ++ List.replicate (n - l.length) x := by
    simp [List.resize, List.take_of_length_le h]
  rw [e]
  by_cases hp : p < l.length
  · rw [ite_eq_left hp, get?_append_left hp]
  · rw [ite_eq_right hp]
    obtain ⟨k, rfl⟩ : ∃ k, p = l.length + k := ⟨p - l.length, by omega⟩
    rw [get?_append_right]
    by_cases hk : l.length + k < n
    · rw [ite_eq_left hk, get?_replicate, ite_eq_left (by omega)]
    · rw [ite_eq_right hk, get?_replicate, ite_eq_right (by omega)]

/-- The list `f 0, …, f (n - 1)`. -/
def tabulate (f : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => tabulate f n ++ [f n]

theorem length_tabulate (f : Nat → α) : ∀ n : Nat, (tabulate f n).length = n
  | 0 => rfl
  | n + 1 => by
    show (tabulate f n ++ [f n]).length = n + 1
    rw [List.length_append, length_tabulate f n]
    rfl

theorem get?_tabulate (f : Nat → α) : ∀ n i : Nat,
    (tabulate f n)[i]? = if i < n then some (f i) else none
  | 0, i => by
    rw [ite_eq_right (Nat.not_lt_zero i)]
    rfl
  | n + 1, i => by
    show (tabulate f n ++ [f n])[i]? = _
    rw [get?_append_one, length_tabulate]
    by_cases h : i < n
    · rw [ite_eq_left h, get?_tabulate f n i, ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h]
      by_cases e : i = n
      · rw [ite_eq_left e, ite_eq_left (by omega), e]
      · rw [ite_eq_right e, ite_eq_right (by omega)]

end Lists

/-! ## Words -/

/-- The number a kind is kept as: its tag, and for an item block `2 ^ 32`
times the slot of its item. -/
def kindCode : client_blocks.BlockKindCore → Nat
  | .Item s => s.val * 4294967296
  | .DeletedItem s => s.val * 4294967296 + 1
  | .Gc => 2
  | .Skip => 3

/-- The number a block is kept as: its clock, and `2 ^ 64` times its kind. -/
def wordCode (b : client_blocks.BlockRefCore) : Nat :=
  kindCode b.kind * 18446744073709551616 + b.clock.val

theorem kindCode_lt (k : client_blocks.BlockKindCore) : kindCode k < 18446744073709551616 := by
  cases k with
  | Item s =>
    simp only [kindCode]
    scalar_tac
  | DeletedItem s =>
    simp only [kindCode]
    scalar_tac
  | Gc => simp [kindCode]
  | Skip => simp [kindCode]

@[step]
theorem kind_code_spec (k : client_blocks.BlockKindCore) :
    client_blocks.kind_code k ⦃ c => c.val = kindCode k ⦄ := by
  unfold client_blocks.kind_code
  cases k with
  | Item slot =>
    simp only [client_blocks.SLOTS]
    step with UScalar.cast_inBounds_spec UScalarTy.U64 slot (by scalar_tac) as ⟨i, hi⟩
    step as ⟨c, hc⟩
    simp only [kindCode]
    scalar_tac
  | DeletedItem slot =>
    simp only [client_blocks.SLOTS]
    step with UScalar.cast_inBounds_spec UScalarTy.U64 slot (by scalar_tac) as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨c, hc⟩
    simp only [kindCode]
    scalar_tac
  | Gc => simp [spec_ok, kindCode]
  | Skip => simp [spec_ok, kindCode]

/-- `pack` answers the number of the block. -/
theorem pack_code (b : client_blocks.BlockRefCore) :
    client_blocks.pack b ⦃ w => w.val = wordCode b ⦄ := by
  unfold client_blocks.pack
  simp only [client_blocks.CLOCKS]
  have hk := kindCode_lt b.kind
  step as ⟨k, hk1⟩
  step with UScalar.cast_inBounds_spec UScalarTy.U128 k (by scalar_tac) as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step with UScalar.cast_inBounds_spec UScalarTy.U128 b.clock (by scalar_tac) as ⟨i2, hi2⟩
  step as ⟨w, hw⟩
  simp only [wordCode]
  scalar_tac

/-- `clock_of` answers what is left of the word below `2 ^ 64`. -/
theorem clock_of_val (w : Std.U128) :
    client_blocks.clock_of w ⦃ c => c.val = w.val % 18446744073709551616 ⦄ := by
  unfold client_blocks.clock_of
  simp only [client_blocks.CLOCKS]
  step as ⟨i, hi⟩
  have hi' : i.val = w.val % 18446744073709551616 := by scalar_tac
  have hlt : i.val < 18446744073709551616 := by omega
  scalar_tac

/-- `kind_of` answers the kind whose number the word holds above `2 ^ 64`,
when it holds the number of a kind there; and a kind for every word. -/
theorem kind_of_val (w : Std.U128) :
    client_blocks.kind_of w ⦃ k =>
      ∀ k0 : client_blocks.BlockKindCore,
        w.val / 18446744073709551616 = kindCode k0 → k = k0 ⦄ := by
  unfold client_blocks.kind_of
  simp only [client_blocks.CLOCKS, client_blocks.SLOTS]
  step as ⟨i, hi⟩
  have hi' : i.val = w.val / 18446744073709551616 := by scalar_tac
  have hwb : w.val < 340282366920938463463374607431768211456 := by scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.U64 i (by scalar_tac) as ⟨kind, hkind⟩
  step as ⟨i1, hi1⟩
  have hi1' : i1.val = kind.val / 4294967296 := by scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.U32 i1 (by scalar_tac) as ⟨slot, hslot⟩
  step as ⟨tag, htag⟩
  have htag' : tag.val = kind.val % 4294967296 := by scalar_tac
  by_cases h0 : tag = 0#u64
  · have h0' : (tag = 0#u64) = True := eq_true h0
    simp only [h0', ↓reduceIte, spec_ok]
    have ht : tag.val = 0 := by scalar_tac
    intro k0 hk0
    cases k0 with
    | Item s =>
      simp only [kindCode] at hk0
      have e : slot = s := by
        apply UScalar.eq_of_val_eq
        scalar_tac
      rw [e]
    | DeletedItem s =>
      simp only [kindCode] at hk0
      exfalso
      omega
    | Gc =>
      simp only [kindCode] at hk0
      exfalso
      omega
    | Skip =>
      simp only [kindCode] at hk0
      exfalso
      omega
  · simp only [h0, ↓reduceIte]
    have ht0 : tag.val ≠ 0 := by scalar_tac
    by_cases h1 : tag = 1#u64
    · have h1' : (tag = 1#u64) = True := eq_true h1
      simp only [h1', ↓reduceIte, spec_ok]
      have ht : tag.val = 1 := by scalar_tac
      intro k0 hk0
      cases k0 with
      | Item s =>
        simp only [kindCode] at hk0
        exfalso
        omega
      | DeletedItem s =>
        simp only [kindCode] at hk0
        have e : slot = s := by
          apply UScalar.eq_of_val_eq
          scalar_tac
        rw [e]
      | Gc =>
        simp only [kindCode] at hk0
        exfalso
        omega
      | Skip =>
        simp only [kindCode] at hk0
        exfalso
        omega
    · simp only [h1, ↓reduceIte]
      have ht1 : tag.val ≠ 1 := by scalar_tac
      by_cases h2 : tag = 2#u64
      · have h2' : (tag = 2#u64) = True := eq_true h2
        simp only [h2', ↓reduceIte, spec_ok]
        have ht : tag.val = 2 := by scalar_tac
        intro k0 hk0
        cases k0 with
        | Item s =>
          simp only [kindCode] at hk0
          exfalso
          omega
        | DeletedItem s =>
          simp only [kindCode] at hk0
          exfalso
          omega
        | Gc => rfl
        | Skip =>
          simp only [kindCode] at hk0
          exfalso
          omega
      · simp only [h2, ↓reduceIte, spec_ok]
        have ht2 : tag.val ≠ 2 := by scalar_tac
        intro k0 hk0
        cases k0 with
        | Item s =>
          simp only [kindCode] at hk0
          exfalso
          omega
        | DeletedItem s =>
          simp only [kindCode] at hk0
          exfalso
          omega
        | Gc =>
          simp only [kindCode] at hk0
          exfalso
          omega
        | Skip => rfl

/-- The block a word is read as: what `unpack` answers. Every word is the
word of a block. -/
def blockOf (w : Std.U128) : client_blocks.BlockRefCore :=
  match (client_blocks.unpack w).match with
  | .ok b => b
  | _ => { clock := 0#u64, kind := client_blocks.BlockKindCore.Skip }

theorem blockOf_eq {w : Std.U128} {c : Std.U64} {k : client_blocks.BlockKindCore}
    (hc : client_blocks.clock_of w = ok c) (hk : client_blocks.kind_of w = ok k) :
    client_blocks.unpack w = ok { clock := c, kind := k } ∧
      blockOf w = { clock := c, kind := k } := by
  have h : client_blocks.unpack w = ok { clock := c, kind := k } := by
    simp [client_blocks.unpack, hc, hk]
  refine ⟨h, ?_⟩
  unfold blockOf
  rw [h, Result.match.ok]

/-- `clock_of`, `kind_of` and `unpack` answer the block of the word, its clock
and its kind. -/
theorem unpack_parts (w : Std.U128) :
    client_blocks.clock_of w = ok (blockOf w).clock ∧
      client_blocks.kind_of w = ok (blockOf w).kind ∧
      client_blocks.unpack w = ok (blockOf w) := by
  obtain ⟨c, hc, _⟩ := ok_of_spec (clock_of_val w)
  obtain ⟨k, hk, _⟩ := ok_of_spec (kind_of_val w)
  obtain ⟨h, hb⟩ := blockOf_eq hc hk
  rw [hb]
  exact ⟨hc, hk, h⟩

@[step]
theorem clock_of_spec (w : Std.U128) :
    client_blocks.clock_of w ⦃ c => c = (blockOf w).clock ⦄ := by
  rw [(unpack_parts w).1]
  exact (spec_ok _).mpr rfl

@[step]
theorem kind_of_spec (w : Std.U128) :
    client_blocks.kind_of w ⦃ k => k = (blockOf w).kind ⦄ := by
  rw [(unpack_parts w).2.1]
  exact (spec_ok _).mpr rfl

@[step]
theorem unpack_spec (w : Std.U128) :
    client_blocks.unpack w ⦃ b => b = blockOf w ⦄ := by
  rw [(unpack_parts w).2.2]
  exact (spec_ok _).mpr rfl

/-- A word that holds the number of a block is read as that block. -/
theorem blockOf_of_code {w : Std.U128} {b : client_blocks.BlockRefCore}
    (h : w.val = wordCode b) : blockOf w = b := by
  obtain ⟨c, hc, hcv⟩ := ok_of_spec (clock_of_val w)
  obtain ⟨k, hk, hkv⟩ := ok_of_spec (kind_of_val w)
  have hkc := kindCode_lt b.kind
  have hcl : b.clock.val < 18446744073709551616 := by scalar_tac
  have e1 : c = b.clock := by
    apply UScalar.eq_of_val_eq
    rw [hcv, h]
    unfold wordCode
    omega
  have e2 : k = b.kind := by
    apply hkv b.kind
    rw [h]
    unfold wordCode
    omega
  rw [(blockOf_eq hc hk).2, e1, e2]

/-- `pack` answers a word that is read as the block: `unpack (pack b) = b`. -/
@[step]
theorem pack_spec (b : client_blocks.BlockRefCore) :
    client_blocks.pack b ⦃ w => blockOf w = b ⦄ :=
  spec_mono (pack_code b) (fun _ h => blockOf_of_code h)

/-! ## Slots -/

/-- The slot of the block `i` of a ring of `cap` slots whose first block is in
the slot `head`: the blocks follow each other from `head` to the last slot and
on from slot 0. -/
def slotOf (cap head i : Nat) : Nat :=
  if i < cap - head then head + i else i - (cap - head)

theorem slotOf_lt {cap head i : Nat} (h : i < cap - head) : slotOf cap head i = head + i := by
  unfold slotOf
  rw [ite_eq_left h]

theorem slotOf_ge {cap head i : Nat} (h : ¬ i < cap - head) :
    slotOf cap head i = i - (cap - head) := by
  unfold slotOf
  rw [ite_eq_right h]

theorem slotOf_lt_cap {cap head i : Nat} (hh : head ≤ cap) (hi : i < cap) :
    slotOf cap head i < cap := by
  by_cases h : i < cap - head
  · rw [slotOf_lt h]
    omega
  · rw [slotOf_ge h]
    omega

@[step]
theorem slot_of_spec (cap head index : Std.Usize) (h : head.val ≤ cap.val)
    (hi : index.val < cap.val) :
    client_blocks.slot_of cap head index ⦃ r =>
      r.val = slotOf cap.val head.val index.val ∧ r.val < cap.val ⦄ := by
  unfold client_blocks.slot_of
  step as ⟨tail, htail⟩
  have htv : tail.val = cap.val - head.val := by scalar_tac
  by_cases hlt : index < tail
  · simp only [hlt, ↓reduceIte]
    have hc : index.val < cap.val - head.val := by scalar_tac
    step as ⟨r, hr⟩
    rw [slotOf_lt hc]
    exact ⟨by scalar_tac, by scalar_tac⟩
  · simp only [hlt, ↓reduceIte]
    have hc : ¬ index.val < cap.val - head.val := by scalar_tac
    step as ⟨r, hr⟩
    rw [slotOf_ge hc]
    exact ⟨by scalar_tac, by scalar_tac⟩

@[step]
theorem slot_before_spec (cap head : Std.Usize) (h : head.val < cap.val) :
    client_blocks.slot_before cap head ⦃ r =>
      r.val = (if head.val = 0 then cap.val - 1 else head.val - 1) ∧ r.val < cap.val ⦄ := by
  unfold client_blocks.slot_before
  by_cases h0 : head = 0#usize
  · have h0' : (head = 0#usize) = True := eq_true h0
    simp only [h0', ↓reduceIte]
    have hv : head.val = 0 := by scalar_tac
    step as ⟨r, hr⟩
    rw [ite_eq_left hv]
    exact ⟨by scalar_tac, by scalar_tac⟩
  · simp only [h0, ↓reduceIte]
    have hv : ¬ head.val = 0 := by scalar_tac
    step as ⟨r, hr⟩
    rw [ite_eq_right hv]
    exact ⟨by scalar_tac, by scalar_tac⟩

@[step]
theorem at_most_spec (n most : Std.Usize) :
    client_blocks.at_most n most ⦃ r => r.val = min n.val most.val ⦄ := by
  unfold client_blocks.at_most
  by_cases h : n > most
  · simp only [h, ↓reduceIte, spec_ok]
    scalar_tac
  · simp only [h, ↓reduceIte, spec_ok]
    scalar_tac

@[step]
theorem at_least_spec (n least : Std.Usize) :
    client_blocks.at_least n least ⦃ r => r.val = max n.val least.val ⦄ := by
  unfold client_blocks.at_least
  by_cases h : n < least
  · simp only [h, ↓reduceIte, spec_ok]
    scalar_tac
  · simp only [h, ↓reduceIte, spec_ok]
    scalar_tac

/-! ## A run of words moved by one slot -/

theorem slide_up_loop_spec (s0 s : Slice Std.U128) (j : Std.Usize)
    (hinv : s.val.length = s0.val.length ∧ j.val < s0.val.length ∧
      ∀ p : Nat, s.val[p]? =
        if j.val < p ∧ p < s0.val.length then s0.val[p - 1]? else s0.val[p]?) :
    client_blocks.slide_up_loop s j ⦃ r =>
      r.val.length = s0.val.length ∧
      ∀ p : Nat, r.val[p]? =
        if 0 < p ∧ p < s0.val.length then s0.val[p - 1]? else s0.val[p]? ⦄ := by
  unfold client_blocks.slide_up_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : Slice Std.U128 × Std.Usize) => k.val)
    (fun ((w, k) : Slice Std.U128 × Std.Usize) =>
      w.val.length = s0.val.length ∧ k.val < s0.val.length ∧
      ∀ p : Nat, w.val[p]? =
        if k.val < p ∧ p < s0.val.length then s0.val[p - 1]? else s0.val[p]?)
    (fun (r : Slice Std.U128) => r.val.length = s0.val.length ∧
      ∀ p : Nat, r.val[p]? =
        if 0 < p ∧ p < s0.val.length then s0.val[p - 1]? else s0.val[p]?)
    _ (s, j) ?_ hinv
  intro ⟨w, k⟩ ⟨hwl, hk, hw⟩
  unfold client_blocks.slide_up_loop.body
  simp only
  by_cases hpos : k > 0#usize
  · simp only [hpos, ↓reduceIte]
    have hkv : 0 < k.val := by scalar_tac
    step as ⟨i, hi⟩
    have hiv : i.val = k.val - 1 := by scalar_tac
    have hil : i.val < w.val.length := by omega
    step as ⟨x, hx⟩
    have hxg : w.val[i.val]? = some x := get?_at hil hx
    have hkl : k.val < w.val.length := by omega
    step as ⟨w1, hw1⟩
    have hset : w1.val = w.val.set k.val x := by
      rw [hw1]
      simp
    refine ⟨?_, by omega, ?_, by omega⟩
    · rw [hset, List.length_set]
      exact hwl
    · intro p
      rw [hset, get?_set, hiv]
      by_cases hp : p = k.val
      · rw [ite_eq_left ⟨hp, hkl⟩, ite_eq_left ⟨by omega, by omega⟩, hp]
        have hsrc := hw i.val
        rw [ite_eq_right (by omega), hxg] at hsrc
        rw [hsrc, hiv]
      · rw [ite_eq_right (fun hc => hp hc.1), hw p]
        by_cases hc : k.val < p ∧ p < s0.val.length
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, hc.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (by omega)]
  · simp only [hpos, ↓reduceIte, spec_ok]
    have hk0 : k.val = 0 := by scalar_tac
    refine ⟨hwl, ?_⟩
    intro p
    rw [hw p, hk0]

/-- `slide_up`: every word but the first is the word that was before it. -/
@[step]
theorem slide_up_spec (s : Slice Std.U128) :
    client_blocks.slide_up s ⦃ r =>
      r.val.length = s.val.length ∧
      ∀ p : Nat, r.val[p]? =
        if 0 < p ∧ p < s.val.length then s.val[p - 1]? else s.val[p]? ⦄ := by
  unfold client_blocks.slide_up
  step as ⟨b, hb⟩
  by_cases he : s.val.length = 0
  · have hbt : b = true := Eq.mpr hb he
    simp only [hbt, ↓reduceIte, spec_ok]
    refine ⟨trivial, ?_⟩
    intro p
    rw [ite_eq_right (by omega)]
  · have hbf : b = false := by
      cases b with
      | false => rfl
      | true => exact absurd (Eq.mp hb rfl) he
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    step as ⟨j, hj⟩
    have hjv : j.val = s.val.length - 1 := by scalar_tac
    refine slide_up_loop_spec s s j ⟨rfl, by omega, ?_⟩
    intro p
    rw [ite_eq_right (by omega)]

theorem slide_down_loop_spec (s0 s : Slice Std.U128) (stop i : Std.Usize)
    (hstop : stop.val + 1 = s0.val.length)
    (hinv : s.val.length = s0.val.length ∧ i.val ≤ stop.val ∧
      ∀ p : Nat, s.val[p]? = if p < i.val then s0.val[p + 1]? else s0.val[p]?) :
    client_blocks.slide_down_loop s stop i ⦃ r =>
      r.val.length = s0.val.length ∧
      ∀ p : Nat, r.val[p]? =
        if p + 1 < s0.val.length then s0.val[p + 1]? else s0.val[p]? ⦄ := by
  unfold client_blocks.slide_down_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : Slice Std.U128 × Std.Usize) => stop.val - k.val)
    (fun ((w, k) : Slice Std.U128 × Std.Usize) =>
      w.val.length = s0.val.length ∧ k.val ≤ stop.val ∧
      ∀ p : Nat, w.val[p]? = if p < k.val then s0.val[p + 1]? else s0.val[p]?)
    (fun (r : Slice Std.U128) => r.val.length = s0.val.length ∧
      ∀ p : Nat, r.val[p]? =
        if p + 1 < s0.val.length then s0.val[p + 1]? else s0.val[p]?)
    _ (s, i) ?_ hinv
  intro ⟨w, k⟩ ⟨hwl, hk, hw⟩
  unfold client_blocks.slide_down_loop.body
  simp only
  by_cases hlt : k < stop
  · simp only [hlt, ↓reduceIte]
    have hkv : k.val < stop.val := by scalar_tac
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = k.val + 1 := by scalar_tac
    have hk1l : k1.val < w.val.length := by omega
    step as ⟨x, hx⟩
    have hxg : w.val[k1.val]? = some x := get?_at hk1l hx
    have hkl : k.val < w.val.length := by omega
    step as ⟨w1, hw1⟩
    have hset : w1.val = w.val.set k.val x := by
      rw [hw1]
      simp
    refine ⟨?_, by omega, ?_, by omega⟩
    · rw [hset, List.length_set]
      exact hwl
    · intro p
      rw [hset, get?_set, hk1v]
      by_cases hp : p = k.val
      · rw [ite_eq_left ⟨hp, hkl⟩, ite_eq_left (by omega), hp]
        have hsrc := hw k1.val
        rw [ite_eq_right (by omega), hxg] at hsrc
        rw [hsrc, hk1v]
      · rw [ite_eq_right (fun hc => hp hc.1), hw p]
        by_cases hc : p < k.val
        · rw [ite_eq_left hc, ite_eq_left (by omega)]
        · rw [ite_eq_right hc, ite_eq_right (by omega)]
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hks : k.val = stop.val := by scalar_tac
    refine ⟨hwl, ?_⟩
    intro p
    rw [hw p, hks]
    by_cases hc : p < stop.val
    · rw [ite_eq_left hc, ite_eq_left (by omega)]
    · rw [ite_eq_right hc, ite_eq_right (by omega)]

/-- `slide_down`: every word but the last is the word that was after it. -/
@[step]
theorem slide_down_spec (s : Slice Std.U128) :
    client_blocks.slide_down s ⦃ r =>
      r.val.length = s.val.length ∧
      ∀ p : Nat, r.val[p]? =
        if p + 1 < s.val.length then s.val[p + 1]? else s.val[p]? ⦄ := by
  unfold client_blocks.slide_down
  step as ⟨b, hb⟩
  by_cases he : s.val.length = 0
  · have hbt : b = true := Eq.mpr hb he
    simp only [hbt, ↓reduceIte, spec_ok]
    refine ⟨trivial, ?_⟩
    intro p
    rw [ite_eq_right (by omega)]
  · have hbf : b = false := by
      cases b with
      | false => rfl
      | true => exact absurd (Eq.mp hb rfl) he
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    step as ⟨stop, hstop⟩
    have hsv : stop.val + 1 = s.val.length := by scalar_tac
    refine slide_down_loop_spec s s stop 0#usize hsv ⟨rfl, by scalar_tac, ?_⟩
    intro p
    rw [ite_eq_right (by scalar_tac)]

/-! ## How much a full ring grows -/

theorem room_loop_spec (cap size : Std.Usize)
    (hinv : 4 ≤ size.val ∧ size.val ≤ 4294967294) :
    client_blocks.room_loop cap size ⦃ r => 4 ≤ r.val ∧ r.val ≤ 4294967294 ⦄ := by
  unfold client_blocks.room_loop
  refine loop.spec_decr_nat
    (fun (k : Std.Usize) => 4294967296 - k.val)
    (fun (k : Std.Usize) => 4 ≤ k.val ∧ k.val ≤ 4294967294)
    (fun (r : Std.Usize) => 4 ≤ r.val ∧ r.val ≤ 4294967294)
    _ size ?_ hinv
  intro k ⟨hk4, hkm⟩
  unfold client_blocks.room_loop.body
  simp only [client_blocks.MAX_BLOCKS]
  by_cases hle : k <= cap
  · simp only [hle, ↓reduceIte]
    step as ⟨i, hi⟩
    have hiv : i.val = 2147483647 := by scalar_tac
    by_cases hle2 : k <= i
    · simp only [hle2, ↓reduceIte]
      have hkv : k.val ≤ 2147483647 := by scalar_tac
      step as ⟨k1, hk1⟩
      have hk1v : k1.val = k.val * 2 := by scalar_tac
      exact ⟨by omega, by omega, by omega⟩
    · simp only [hle2, ↓reduceIte, spec_ok]
      exact ⟨hk4, hkm⟩
  · simp only [hle, ↓reduceIte, spec_ok]
    exact ⟨hk4, hkm⟩

/-- `room`: at least one slot, and no more than a ring of `MAX_BLOCKS` slots
has. -/
@[step]
theorem room_spec (cap : Std.Usize) (h : cap.val < 4294967295) :
    client_blocks.room cap ⦃ r => 1 ≤ r.val ∧ cap.val + r.val ≤ 4294967295 ⦄ := by
  unfold client_blocks.room
  step with room_loop_spec cap 4#usize ⟨by scalar_tac, by scalar_tac⟩ as ⟨size, hs4, hsm⟩
  simp only [client_blocks.MAX_BLOCKS]
  by_cases hgt : size > cap
  · simp only [hgt, ↓reduceIte]
    step as ⟨r, hr⟩
    exact ⟨by scalar_tac, by scalar_tac⟩
  · simp only [hgt, ↓reduceIte]
    step as ⟨r, hr⟩
    exact ⟨by scalar_tac, by scalar_tac⟩

/-- `growth`: a full ring takes on at least one slot and stays within
`MAX_BLOCKS`. -/
@[step]
theorem growth_spec (cap wrapped : Std.Usize) (h : cap.val < 4294967295) :
    client_blocks.growth cap wrapped ⦃ g => 1 ≤ g.val ∧ cap.val + g.val ≤ 4294967295 ⦄ := by
  unfold client_blocks.growth
  simp only [client_blocks.MORE_SLOTS]
  step as ⟨i, hi⟩
  step as ⟨i1, h1, h2⟩
  step as ⟨g, hg⟩
  have hiv : 64 ≤ i.val := by scalar_tac
  exact ⟨by scalar_tac, by scalar_tac⟩

/-! ## The blocks of a ring -/

/-- The slots of the ring: no more than `MAX_BLOCKS`. -/
def capOf (cb : client_blocks.ClientBlocksCore) : Nat := min cb.buf.val.length 4294967295

/-- The slot of the first block: one of the slots of the ring. -/
def firstOf (cb : client_blocks.ClientBlocksCore) : Nat :=
  if cb.head.val < capOf cb then cb.head.val else 0

/-- The number of blocks: no more than the ring has slots. -/
def countOf (cb : client_blocks.ClientBlocksCore) : Nat := min cb.len.val (capOf cb)

/-- The block in a slot; the block of the word 0 past the last slot. -/
def blockAt (l : List Std.U128) (p : Nat) : client_blocks.BlockRefCore :=
  match l[p]? with
  | some w => blockOf w
  | none => blockOf 0#u128

theorem blockAt_of_get? {l : List Std.U128} {p : Nat} {w : Std.U128} (h : l[p]? = some w) :
    blockAt l p = blockOf w := by
  unfold blockAt
  rw [h]

theorem blockAt_congr {l l' : List Std.U128} {p q : Nat} (h : l[p]? = l'[q]?) :
    blockAt l p = blockAt l' q := by
  unfold blockAt
  rw [h]

/-- The blocks of a timeline, in the order of their clocks: the blocks of the
ring the fields are read as. -/
def blocksOf (cb : client_blocks.ClientBlocksCore) : List client_blocks.BlockRefCore :=
  tabulate (fun i => blockAt cb.buf.val (slotOf (capOf cb) (firstOf cb) i)) (countOf cb)

theorem capOf_le_length (cb : client_blocks.ClientBlocksCore) : capOf cb ≤ cb.buf.val.length := by
  unfold capOf
  omega

theorem capOf_le_max (cb : client_blocks.ClientBlocksCore) : capOf cb ≤ 4294967295 := by
  unfold capOf
  omega

theorem firstOf_le (cb : client_blocks.ClientBlocksCore) : firstOf cb ≤ capOf cb := by
  unfold firstOf
  by_cases h : cb.head.val < capOf cb
  · rw [ite_eq_left h]
    omega
  · rw [ite_eq_right h]
    omega

theorem countOf_le (cb : client_blocks.ClientBlocksCore) : countOf cb ≤ capOf cb := by
  unfold countOf
  omega

theorem length_blocksOf (cb : client_blocks.ClientBlocksCore) :
    (blocksOf cb).length = countOf cb :=
  length_tabulate _ _

theorem get?_blocksOf (cb : client_blocks.ClientBlocksCore) (i : Nat) :
    (blocksOf cb)[i]? =
      if i < countOf cb then some (blockAt cb.buf.val (slotOf (capOf cb) (firstOf cb) i))
      else none :=
  get?_tabulate _ _ _

/-- The blocks of a ring are the list that has its block in every place. -/
theorem blocksOf_ext {cb : client_blocks.ClientBlocksCore}
    {l : List client_blocks.BlockRefCore} (hlen : l.length = countOf cb)
    (h : ∀ i : Nat, i < countOf cb →
      l[i]? = some (blockAt cb.buf.val (slotOf (capOf cb) (firstOf cb) i))) :
    blocksOf cb = l := by
  apply ext_get?
  intro i
  rw [get?_blocksOf]
  by_cases hi : i < countOf cb
  · rw [ite_eq_left hi, h i hi]
  · rw [ite_eq_right hi]
    exact (get?_none (by omega)).symm

/-- What fields that say what the ring is are read as. -/
theorem reads_of {cb : client_blocks.ClientBlocksCore} {c h n : Nat}
    (hc : cb.buf.val.length = c) (hmax : c ≤ 4294967295) (hh : cb.head.val = h)
    (hhc : h < c ∨ h = 0) (hn : cb.len.val = n) (hnc : n ≤ c) :
    capOf cb = c ∧ firstOf cb = h ∧ countOf cb = n := by
  have e : capOf cb = c := by
    unfold capOf
    omega
  refine ⟨e, ?_, ?_⟩
  · unfold firstOf
    rw [e, hh]
    by_cases hlt : h < c
    · rw [ite_eq_left hlt]
    · rw [ite_eq_right hlt]
      omega
  · unfold countOf
    rw [e, hn]
    omega

/-- `ring` answers the ring the fields are read as. -/
@[step]
theorem ring_spec (cb : client_blocks.ClientBlocksCore) :
    client_blocks.ClientBlocksCore.ring cb ⦃ cap head len =>
      cap.val = capOf cb ∧ head.val = firstOf cb ∧ len.val = countOf cb ⦄ := by
  unfold client_blocks.ClientBlocksCore.ring
  simp only [client_blocks.MAX_BLOCKS]
  step as ⟨cap, hcap⟩
  have hc : cap.val = capOf cb := by
    unfold capOf
    scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.Usize cb.head (by scalar_tac) as ⟨head, hhead⟩
  step with UScalar.cast_inBounds_spec UScalarTy.Usize cb.len (by scalar_tac) as ⟨i, hi⟩
  step as ⟨len, hlen⟩
  have hl : len.val = countOf cb := by
    unfold countOf
    scalar_tac
  by_cases hlt : head < cap
  · simp only [hlt, ↓reduceIte, spec_ok, uncurry'_pair]
    refine ⟨hc, ?_, hl⟩
    unfold firstOf
    rw [ite_eq_left (by scalar_tac)]
    exact hhead
  · simp only [hlt, ↓reduceIte, spec_ok, uncurry'_pair]
    refine ⟨hc, ?_, hl⟩
    unfold firstOf
    rw [ite_eq_right (by scalar_tac)]
    rfl

/-! ## A ring in the order of its slots -/

/-- The number of blocks is `len`, and no more than there are slots: `len`
itself is no more than `MAX_BLOCKS`. -/
theorem countOf_eq (cb : client_blocks.ClientBlocksCore) :
    countOf cb = min cb.len.val cb.buf.val.length := by
  unfold countOf capOf
  have h : cb.len.val ≤ 4294967295 := by scalar_tac
  omega

theorem firstOf_plain {cb : client_blocks.ClientBlocksCore} (h : cb.head.val = 0) :
    firstOf cb = 0 := by
  unfold firstOf
  rw [h]
  by_cases hc : 0 < capOf cb
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]

/-- A slot of a ring that starts at its first slot is the slot of its index. -/
theorem slot_plain {cb : client_blocks.ClientBlocksCore} (h : cb.head.val = 0) {i : Nat}
    (hi : i < capOf cb) : slotOf (capOf cb) (firstOf cb) i = i := by
  rw [firstOf_plain h, slotOf_lt (by omega)]
  omega

theorem get?_blocksOf_plain {cb : client_blocks.ClientBlocksCore} (h : cb.head.val = 0)
    {i : Nat} (hi : i < countOf cb) : (blocksOf cb)[i]? = some (blockAt cb.buf.val i) := by
  have hcl := countOf_le cb
  rw [get?_blocksOf, ite_eq_left hi, slot_plain h (by omega)]

/-- The blocks of words, word by word. -/
theorem get?_words (a b : List Std.U128) (i : Nat) (hi : i < a.length + b.length) :
    ((a ++ b).map blockOf)[i]? =
      some (if i < a.length then blockAt a i else blockAt b (i - a.length)) := by
  rw [List.getElem?_map]
  by_cases h : i < a.length
  · rw [ite_eq_left h, List.getElem?_append_left h]
    obtain ⟨w, hw⟩ := get?_some h
    rw [hw, blockAt_of_get? hw]
    rfl
  · rw [ite_eq_right h, List.getElem?_append_right (by omega)]
    obtain ⟨w, hw⟩ := get?_some (by omega : i - a.length < b.length)
    rw [hw, blockAt_of_get? hw]
    rfl

/-- A block of a part of a list of words is the block of the list there. -/
theorem blockAt_slice (l : List Std.U128) {a b k : Nat} (hb : b ≤ l.length) (hk : a + k < b) :
    blockAt (l.slice a b) k = blockAt l (a + k) := by
  apply blockAt_congr
  rw [get?_slice _ _ _ _ hb, ite_eq_left hk]

/-! ## The tag of a kind -/

/-- The tag of a kind: one number a kind of block. -/
def tagOfKind : client_blocks.BlockKindCore → Nat
  | .Item _ => 0
  | .DeletedItem _ => 1
  | .Gc => 2
  | .Skip => 3

/-- The tag a word keeps the kind of its block under: every tag above 2 is
the tag of a gap. -/
def wordTag (w : Std.U128) : Nat := min (w.val / 18446744073709551616 % 4294967296) 3

theorem kind_of_tag (w : Std.U128) :
    client_blocks.kind_of w ⦃ k => tagOfKind k = wordTag w ⦄ := by
  unfold client_blocks.kind_of
  simp only [client_blocks.CLOCKS, client_blocks.SLOTS]
  step as ⟨i, hi⟩
  have hi' : i.val = w.val / 18446744073709551616 := by scalar_tac
  have hwb : w.val < 340282366920938463463374607431768211456 := by scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.U64 i (by scalar_tac) as ⟨kind, hkind⟩
  have hkv : kind.val = w.val / 18446744073709551616 := by scalar_tac
  step as ⟨i1, hi1⟩
  have hi1' : i1.val = kind.val / 4294967296 := by scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.U32 i1 (by scalar_tac) as ⟨slot, hslot⟩
  step as ⟨tag, htag⟩
  have htag' : tag.val = kind.val % 4294967296 := by scalar_tac
  unfold wordTag
  by_cases h0 : tag = 0#u64
  · have h0' : (tag = 0#u64) = True := eq_true h0
    simp only [h0', ↓reduceIte, spec_ok]
    have ht : tag.val = 0 := by scalar_tac
    show (0 : Nat) = _
    omega
  · simp only [h0, ↓reduceIte]
    have ht0 : tag.val ≠ 0 := by scalar_tac
    by_cases h1 : tag = 1#u64
    · have h1' : (tag = 1#u64) = True := eq_true h1
      simp only [h1', ↓reduceIte, spec_ok]
      have ht : tag.val = 1 := by scalar_tac
      show (1 : Nat) = _
      omega
    · simp only [h1, ↓reduceIte]
      have ht1 : tag.val ≠ 1 := by scalar_tac
      by_cases h2 : tag = 2#u64
      · have h2' : (tag = 2#u64) = True := eq_true h2
        simp only [h2', ↓reduceIte, spec_ok]
        have ht : tag.val = 2 := by scalar_tac
        show (2 : Nat) = _
        omega
      · simp only [h2, ↓reduceIte, spec_ok]
        have ht2 : tag.val ≠ 2 := by scalar_tac
        show (3 : Nat) = _
        omega

/-- The tag of the kind a word reads as is the tag the word keeps. -/
theorem wordTag_eq (w : Std.U128) : tagOfKind (blockOf w).kind = wordTag w := by
  obtain ⟨k, hk, hkt⟩ := ok_of_spec (kind_of_tag w)
  have h := (unpack_parts w).2.1
  rw [hk] at h
  have e : k = (blockOf w).kind := by simpa using h
  rw [← e]
  exact hkt

@[step]
theorem tag_of_spec (w : Std.U128) :
    client_blocks.tag_of w ⦃ t => t.val = tagOfKind (blockOf w).kind ⦄ := by
  rw [wordTag_eq]
  unfold client_blocks.tag_of wordTag
  simp only [client_blocks.CLOCKS, client_blocks.SLOTS]
  step as ⟨i, hi⟩
  have hi' : i.val = w.val / 18446744073709551616 := by scalar_tac
  have hwb : w.val < 340282366920938463463374607431768211456 := by scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.U64 i (by scalar_tac) as ⟨kind, hkind⟩
  have hkv : kind.val = w.val / 18446744073709551616 := by scalar_tac
  step as ⟨tag, htag⟩
  have htag' : tag.val = kind.val % 4294967296 := by scalar_tac
  by_cases h3 : tag > 3#u64
  · simp only [h3, ↓reduceIte, spec_ok]
    have ht : 3 < tag.val := by scalar_tac
    scalar_tac
  · simp only [h3, ↓reduceIte, spec_ok]
    have ht : tag.val ≤ 3 := by scalar_tac
    scalar_tac

/-- `same_kind_words`: whether the blocks of two words are of the same kind,
by their tags. -/
@[step]
theorem same_kind_words_spec (a b : Std.U128) :
    client_blocks.same_kind_words a b ⦃ r =>
      (r = true ↔ tagOfKind (blockOf a).kind = tagOfKind (blockOf b).kind) ⦄ := by
  unfold client_blocks.same_kind_words
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    rw [← hi, ← hi1, h]
  · intro h
    apply UScalar.eq_of_val_eq
    rw [hi, hi1, h]

/-- `deleted_word`: whether the block of a word is anything but a live item. -/
@[step]
theorem deleted_word_spec (w : Std.U128) :
    client_blocks.deleted_word w ⦃ r =>
      (r = true ↔ tagOfKind (blockOf w).kind ≠ 0) ⦄ := by
  unfold client_blocks.deleted_word
  step as ⟨i, hi⟩
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro h hc
    apply h
    apply UScalar.eq_of_val_eq
    rw [hi, hc]
    scalar_tac
  · intro h hc
    apply h
    rw [← hi, hc]
    scalar_tac

/-! ## The search on a slice -/

/-- The partition point of words whose blocks follow each other. -/
theorem count_before_loop_spec (words : Slice Std.U128) (clock : Std.U64) (lo hi : Std.Usize)
    (hs : ∀ p q : Nat, p < q → q < words.val.length →
      (blockAt words.val p).clock.val < (blockAt words.val q).clock.val)
    (hinv : lo.val ≤ hi.val ∧ hi.val ≤ words.val.length ∧
      (∀ j : Nat, j < lo.val → (blockAt words.val j).clock.val ≤ clock.val) ∧
      (∀ j : Nat, hi.val ≤ j → j < words.val.length →
        clock.val < (blockAt words.val j).clock.val)) :
    client_blocks.count_before_loop words clock lo hi ⦃ r =>
      r.val ≤ words.val.length ∧
      (∀ j : Nat, j < r.val → (blockAt words.val j).clock.val ≤ clock.val) ∧
      (∀ j : Nat, r.val ≤ j → j < words.val.length →
        clock.val < (blockAt words.val j).clock.val) ⦄ := by
  unfold client_blocks.count_before_loop
  refine loop.spec_decr_nat
    (fun ((l, h) : Std.Usize × Std.Usize) => h.val - l.val)
    (fun ((l, h) : Std.Usize × Std.Usize) => l.val ≤ h.val ∧ h.val ≤ words.val.length ∧
      (∀ j : Nat, j < l.val → (blockAt words.val j).clock.val ≤ clock.val) ∧
      (∀ j : Nat, h.val ≤ j → j < words.val.length →
        clock.val < (blockAt words.val j).clock.val))
    (fun (r : Std.Usize) => r.val ≤ words.val.length ∧
      (∀ j : Nat, j < r.val → (blockAt words.val j).clock.val ≤ clock.val) ∧
      (∀ j : Nat, r.val ≤ j → j < words.val.length →
        clock.val < (blockAt words.val j).clock.val))
    _ (lo, hi) ?_ hinv
  intro ⟨l, h⟩ ⟨hlh, hhh, hbelow, habove⟩
  unfold client_blocks.count_before_loop.body
  simp only
  by_cases hlt : l < h
  · simp only [hlt, ↓reduceIte]
    step as ⟨i, hi'⟩
    step as ⟨i1, hi1⟩
    step as ⟨mid, hmid⟩
    have hmidlo : l.val ≤ mid.val := by scalar_tac
    have hmidhi : mid.val < h.val := by scalar_tac
    step as ⟨w, hw⟩
    have hg : words.val[mid.val]? = some w := get?_at (by omega) hw
    have hbm : blockAt words.val mid.val = blockOf w := blockAt_of_get? hg
    step as ⟨c, hc⟩
    by_cases hle : c <= clock
    · simp only [hle, ↓reduceIte]
      step as ⟨l1, hl1⟩
      have hle' : (blockAt words.val mid.val).clock.val ≤ clock.val := by
        rw [hbm, ← hc]
        scalar_tac
      refine ⟨by scalar_tac, hhh, ?_, habove, by scalar_tac⟩
      intro j hj
      by_cases hjm : j = mid.val
      · rw [hjm]
        exact hle'
      · have := hs j mid.val (by scalar_tac) (by omega)
        omega
    · simp only [hle, ↓reduceIte, spec_ok]
      have hgt : clock.val < (blockAt words.val mid.val).clock.val := by
        rw [hbm, ← hc]
        scalar_tac
      refine ⟨hmidlo, by omega, hbelow, ?_, by omega⟩
      intro j hj1 hj2
      by_cases hjm : j = mid.val
      · rw [hjm]
        exact hgt
      · have := hs mid.val j (by omega) hj2
        omega
  · simp only [hlt, ↓reduceIte, spec_ok]
    have heq : l.val = h.val := by scalar_tac
    refine ⟨by omega, hbelow, ?_⟩
    intro j hj1 hj2
    exact habove j (by omega) hj2

/-- `count_before`: how many of the words, whose blocks follow each other,
are of a block that starts at or before the clock. -/
theorem count_before_spec (words : Slice Std.U128) (clock : Std.U64)
    (hs : ∀ p q : Nat, p < q → q < words.val.length →
      (blockAt words.val p).clock.val < (blockAt words.val q).clock.val) :
    client_blocks.count_before words clock ⦃ r =>
      r.val ≤ words.val.length ∧
      (∀ j : Nat, j < r.val → (blockAt words.val j).clock.val ≤ clock.val) ∧
      (∀ j : Nat, r.val ≤ j → j < words.val.length →
        clock.val < (blockAt words.val j).clock.val) ⦄ := by
  unfold client_blocks.count_before
  have hl : (Slice.len words).val = words.val.length := by
    rw [Slice.len_val]
  have z : (0#usize : Std.Usize).val = 0 := by scalar_tac
  refine count_before_loop_spec words clock 0#usize (Slice.len words) hs
    ⟨by omega, by omega, ?_, ?_⟩
  · intro j hj
    omega
  · intro j hj1 hj2
    omega

end YoctoCore.Properties.Ring
