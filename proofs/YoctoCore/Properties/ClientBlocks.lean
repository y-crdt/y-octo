/-
`y_octo_core::client_blocks`: the block timeline of one client.

Every function is total on every input (the Hoare triples below have no
precondition but the invariant where one is named), and `append`,
`split_boundary`, `merge_range`, `merge_adjacent`, `mark_deleted`, `mark_gc`
and `remap_slots` keep the invariant I1 (`WF`): block starts strictly increase
below `end_clock`, so no block is empty and the blocks follow each other
without a gap.

`y-octo` keeps the timeline of every client in a `ClientBlocksCore`
(`y-octo/src/doc/store/client_blocks.rs`) and edits it through these functions
only: the fields are not visible outside the module. It reads them through
`len`, `end_clock`, `get`, `clock_at`, `word_at`, `word_end_at`, `range`,
`find` and `words` (`len_spec`, `end_clock_spec`, `get_spec`, `clock_at_spec`,
`word_at_spec`, `word_end_at_spec`, `range_spec`, `find_spec`, `words_spec`):
`words` answers the words of the blocks in the order of the timeline, as the
two runs of slots that hold them.

The blocks of a timeline are kept in a ring of words (`Ring.lean`). The
theorems here are about `blocksOf cb`, the list of blocks the fields of `cb`
are read as, whatever their values: none of them assumes anything about the
representation. `split_boundary` and `merge_range` move the blocks on the
shorter side of the edit only, and `merge_range` and `remap_slots` allocate
nothing (`RingMoves.lean`, `RingEdits.lean`). A ring whose first block is in
its first slot is read and appended to in the order of its slots; those paths
are proved to answer what the paths of a ring that wraps answer.
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.YataModel
import YoctoCore.Properties.Ring
import YoctoCore.Properties.RingMoves
import YoctoCore.Properties.RingEdits

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties.ListAux YoctoCore.Properties.YataModel
open YoctoCore.Properties.Ring

set_option maxHeartbeats 400000
set_option autoImplicit false

namespace YoctoCore.Properties.ClientBlocks

/-! ## The model of a timeline -/

def toKind : client_blocks.BlockKindCore → MKind
  | .Item i => MKind.item i.val
  | .DeletedItem i => MKind.deleted i.val
  | .Gc => MKind.gc
  | .Skip => MKind.skip

def toBlock (b : client_blocks.BlockRefCore) : MBlock := ⟨b.clock.val, toKind b.kind⟩

def toBlocks (cb : client_blocks.ClientBlocksCore) : List MBlock := (blocksOf cb).map toBlock

/-- I1 on a timeline. -/
structure WF (cb : client_blocks.ClientBlocksCore) : Prop where
  timeline : TimelineWF (toBlocks cb) cb.end_clock.val

/-- The slot of an item block. -/
def kindSlot : client_blocks.BlockKindCore → Option Std.U32
  | .Item i => some i
  | .DeletedItem i => some i
  | .Gc => none
  | .Skip => none

theorem kindSlot_val (k : client_blocks.BlockKindCore) :
    (kindSlot k).map (fun i : Std.U32 => i.val) = (toKind k).slot := by
  cases k <;> rfl

theorem toBlocks_get? (cb : client_blocks.ClientBlocksCore) (i : Nat) :
    (toBlocks cb)[i]? = ((blocksOf cb)[i]?).map toBlock :=
  get?_map _ _ _

theorem toBlocks_length (cb : client_blocks.ClientBlocksCore) :
    (toBlocks cb).length = (blocksOf cb).length := by
  simp [toBlocks]

/-! ## Kinds -/

@[step]
theorem kind_deleted_spec (k : client_blocks.BlockKindCore) :
    client_blocks.BlockKindCore.deleted k ⦃ b => b = (toKind k).dead ⦄ := by
  unfold client_blocks.BlockKindCore.deleted
  cases k <;> simp [toKind, MKind.dead]

@[step]
theorem kind_item_spec (k : client_blocks.BlockKindCore) :
    client_blocks.BlockKindCore.item k ⦃ o => o = kindSlot k ⦄ := by
  unfold client_blocks.BlockKindCore.item
  cases k <;> simp [kindSlot]

/-- Two kinds are the same kind: both live items, both deleted items, both
collected ranges or both gaps. -/
def sameKind : client_blocks.BlockKindCore → client_blocks.BlockKindCore → Bool
  | .Item _, .Item _ => true
  | .DeletedItem _, .DeletedItem _ => true
  | .Gc, .Gc => true
  | .Skip, .Skip => true
  | _, _ => false

@[step]
theorem kind_same_kind_spec (a b : client_blocks.BlockKindCore) :
    client_blocks.BlockKindCore.same_kind a b ⦃ r => r = sameKind a b ⦄ := by
  unfold client_blocks.BlockKindCore.same_kind
  cases a <;> cases b <;> simp [sameKind]

/-! ## Lists of blocks -/

theorem get?_of_getElem {α : Type} {l : List α} {i : Nat} {x : α} (h : i < l.length)
    (hx : x = l[i]) : l[i]? = some x := by
  rw [hx]
  exact List.getElem?_eq_getElem h

theorem endAt_toBlocks_some {cb : client_blocks.ClientBlocksCore} {p : Nat}
    {b : client_blocks.BlockRefCore} (h : (blocksOf cb)[p + 1]? = some b) :
    endAt (toBlocks cb) cb.end_clock.val p = b.clock.val := by
  simp [endAt, toBlocks_get?, h, toBlock]

theorem endAt_toBlocks_none {cb : client_blocks.ClientBlocksCore} {p : Nat}
    (h : (blocksOf cb).length ≤ p + 1) :
    endAt (toBlocks cb) cb.end_clock.val p = cb.end_clock.val := by
  simp [endAt, toBlocks_get?, get?_none h]

theorem toBlocks_of_append {cb cb' : client_blocks.ClientBlocksCore}
    {b : client_blocks.BlockRefCore} (h : (blocksOf cb') = (blocksOf cb) ++ [b]) :
    toBlocks cb' = toBlocks cb ++ [toBlock b] := by
  simp [toBlocks, h]

theorem toBlocks_of_insAt {cb cb' : client_blocks.ClientBlocksCore} {i : Nat}
    {b : client_blocks.BlockRefCore} (h : (blocksOf cb') = insAt (blocksOf cb) i b) :
    toBlocks cb' = insAt (toBlocks cb) i (toBlock b) := by
  unfold toBlocks
  rw [h, map_insAt]

theorem toBlocks_of_set {cb cb' : client_blocks.ClientBlocksCore} {i : Nat}
    {b : client_blocks.BlockRefCore} (h : (blocksOf cb') = (blocksOf cb).set i b) :
    toBlocks cb' = upd (toBlocks cb) i (fun _ => toBlock b) := by
  unfold toBlocks
  rw [h, set_eq_upd, map_upd toBlock _ _ _ (fun _ => toBlock b) (fun _ => rfl)]

theorem toBlocks_of_delAt {cb cb' : client_blocks.ClientBlocksCore} {i : Nat}
    (h : (blocksOf cb') = delAt (blocksOf cb) i) : toBlocks cb' = delAt (toBlocks cb) i := by
  unfold toBlocks
  rw [h, map_delAt]

/-- A block of the timeline, in the ring. -/
theorem block_at {cb : client_blocks.ClientBlocksCore} {cap head : Std.Usize} {i : Nat}
    {s : Std.Usize} {w : Std.U128} (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb)
    (hi : i < countOf cb) (hs : s.val = slotOf cap.val head.val i)
    (hw : cb.buf.val[s.val]? = some w) : (blocksOf cb)[i]? = some (blockOf w) := by
  rw [get?_blocksOf, ite_eq_left hi, ← hcap, ← hhead, ← hs, blockAt_of_get? hw]


/-! ## `new`, `len`, `is_empty`, `continues`, `end_clock` and the reads -/

@[step]
theorem new_spec :
    client_blocks.ClientBlocksCore.new ⦃ cb => blocksOf cb = [] ∧ cb.end_clock.val = 0 ∧ WF cb ⦄ := by
  unfold client_blocks.ClientBlocksCore.new
  simp only [spec_ok]
  have e : blocksOf (client_blocks.ClientBlocksCore.mk (alloc.vec.Vec.new Std.U128) 0#u32 0#u32
      0#u64) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [length_blocksOf]
    simp [countOf]
  refine ⟨e, by simp, ⟨⟨?_, ?_⟩⟩⟩
  · intro p q a b _ ha _
    simp [toBlocks, e] at ha
  · intro p a ha
    simp [toBlocks, e] at ha

@[step]
theorem len_spec (cb : client_blocks.ClientBlocksCore) :
    client_blocks.ClientBlocksCore.impl.len cb ⦃ n => n.val = (blocksOf cb).length ⦄ := by
  unfold client_blocks.ClientBlocksCore.impl.len
  step with UScalar.cast_inBounds_spec UScalarTy.Usize cb.len (by scalar_tac) as ⟨i, hi⟩
  step as ⟨n, hn⟩
  rw [length_blocksOf, countOf_eq]
  scalar_tac

@[step]
theorem is_empty_spec (cb : client_blocks.ClientBlocksCore) :
    client_blocks.ClientBlocksCore.is_empty cb ⦃ b => (b = true ↔ blocksOf cb = []) ⦄ := by
  unfold client_blocks.ClientBlocksCore.is_empty
  step as ⟨i, hi⟩
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    have h0 : i.val = 0 := by scalar_tac
    exact List.eq_nil_of_length_eq_zero (by omega)
  · intro h
    have h0 : i.val = 0 := by
      rw [hi, h]
      rfl
    apply UScalar.eq_of_val_eq
    simp [h0]

@[step]
theorem continues_spec (cb : client_blocks.ClientBlocksCore) (clock : Std.U64) :
    client_blocks.ClientBlocksCore.continues cb clock ⦃ b =>
      (b = true ↔ (blocksOf cb = [] ∨ clock = cb.end_clock)) ⦄ := by
  unfold client_blocks.ClientBlocksCore.continues
  step as ⟨b, hb⟩
  by_cases he : blocksOf cb = []
  · have hbt : b = true := hb.mpr he
    simp [spec_ok, hbt, he]
  · have hbf : b = false := by
      cases b with
      | true => exact absurd (hb.mp rfl) he
      | false => rfl
    simp [spec_ok, hbf, he]

/-- `follows`: `continues` for a caller that has the number of blocks. -/
@[step]
theorem follows_spec (cb : client_blocks.ClientBlocksCore) (blocks : Std.Usize)
    (clock : Std.U64) :
    client_blocks.ClientBlocksCore.follows cb blocks clock ⦃ b =>
      (b = true ↔ (blocks.val = 0 ∨ clock = cb.end_clock)) ⦄ := by
  unfold client_blocks.ClientBlocksCore.follows
  by_cases h : blocks = 0#usize
  · have h' : (blocks = 0#usize) = True := eq_true h
    simp only [h', ↓reduceIte, spec_ok]
    have hv : blocks.val = 0 := by scalar_tac
    simp [hv]
  · simp only [h, ↓reduceIte, spec_ok]
    have hv : blocks.val ≠ 0 := by scalar_tac
    simp [hv]

/-- `end_clock` answers the end of the timeline. -/
@[step]
theorem end_clock_spec (cb : client_blocks.ClientBlocksCore) :
    client_blocks.ClientBlocksCore.impl.end_clock cb ⦃ c => c = cb.end_clock ⦄ := by
  unfold client_blocks.ClientBlocksCore.impl.end_clock
  simp [spec_ok]

/-- `slot_at` answers the slot of a block of the timeline, and none past its
last block. -/
@[step]
theorem slot_at_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.slot_at cb index ⦃ o =>
      (o = none ∧ countOf cb ≤ index.val) ∨
        ∃ s : Std.Usize, o = some s ∧ index.val < countOf cb ∧
          s.val = slotOf (capOf cb) (firstOf cb) index.val ∧ s.val < cb.buf.val.length ⦄ := by
  unfold client_blocks.ClientBlocksCore.slot_at
  have hcl := countOf_le cb
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  have hce := countOf_eq cb
  by_cases h0 : cb.head = 0#u32
  · have h0' : (cb.head = 0#u32) = True := eq_true h0
    simp only [h0', ↓reduceIte]
    have hv : cb.head.val = 0 := by scalar_tac
    step with UScalar.cast_inBounds_spec UScalarTy.Usize cb.len (by scalar_tac) as ⟨i, hi⟩
    by_cases h1 : index >= i
    · simp only [h1, ↓reduceIte, spec_ok]
      left
      exact ⟨trivial, by scalar_tac⟩
    · simp only [h1, ↓reduceIte]
      by_cases h2 : index >= alloc.vec.Vec.len cb.buf
      · simp only [h2, ↓reduceIte, spec_ok]
        left
        exact ⟨trivial, by scalar_tac⟩
      · simp only [h2, ↓reduceIte, spec_ok]
        right
        have hlt : index.val < countOf cb := by scalar_tac
        exact ⟨index, rfl, hlt, (slot_plain hv (by omega)).symm, by scalar_tac⟩
  · simp only [h0, ↓reduceIte]
    step as ⟨cap, head, len, hcap, hhead, hlen⟩
    by_cases h : index >= len
    · simp only [h, ↓reduceIte, spec_ok]
      left
      exact ⟨trivial, by scalar_tac⟩
    · simp only [h, ↓reduceIte]
      have hlt : index.val < countOf cb := by scalar_tac
      step as ⟨s, hs, hslt⟩
      right
      exact ⟨s, rfl, hlt, by rw [hs, hcap, hhead], by omega⟩

/-- A block of the timeline, in its slot. -/
theorem block_at_slot {cb : client_blocks.ClientBlocksCore} {i : Nat} {s : Std.Usize}
    {w : Std.U128} (hi : i < countOf cb) (hs : s.val = slotOf (capOf cb) (firstOf cb) i)
    (hw : cb.buf.val[s.val]? = some w) : (blocksOf cb)[i]? = some (blockOf w) := by
  rw [get?_blocksOf, ite_eq_left hi, ← hs, blockAt_of_get? hw]

/-- `word_at` answers the word of the block at an index of the timeline. -/
@[step]
theorem word_at_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.word_at cb index ⦃ o =>
      (o = none ∧ (blocksOf cb).length ≤ index.val) ∨
        ∃ w : Std.U128, o = some w ∧ (blocksOf cb)[index.val]? = some (blockOf w) ⦄ := by
  unfold client_blocks.ClientBlocksCore.word_at
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hge⟩ | ⟨s, rfl, hlt, hs, hsl⟩
  · simp only [spec_ok]
    left
    exact ⟨trivial, by rw [length_blocksOf]; exact hge⟩
  · dsimp only
    step as ⟨w, hw⟩
    have hg : cb.buf.val[s.val]? = some w := get?_at hsl hw
    right
    exact ⟨w, rfl, block_at_slot hlt hs hg⟩

/-- `get` answers the block at an index of the timeline. -/
@[step]
theorem get_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.get cb index ⦃ o => o = (blocksOf cb)[index.val]? ⦄ := by
  unfold client_blocks.ClientBlocksCore.get
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hge⟩ | ⟨w, rfl, hw⟩
  · simp only [spec_ok]
    exact (get?_none hge).symm
  · dsimp only
    step as ⟨b, hb⟩
    rw [hw, hb]

/-- `clock_at` answers the clock the block at an index starts at. -/
@[step]
theorem clock_at_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.clock_at cb index ⦃ o =>
      (o = none ∧ (blocksOf cb).length ≤ index.val) ∨
        ∃ b : client_blocks.BlockRefCore, o = some b.clock ∧
          (blocksOf cb)[index.val]? = some b ⦄ := by
  unfold client_blocks.ClientBlocksCore.clock_at
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hge⟩ | ⟨w, rfl, hw⟩
  · simp only [spec_ok]
    left
    exact ⟨trivial, hge⟩
  · dsimp only
    step as ⟨c, hc⟩
    right
    exact ⟨blockOf w, by rw [hc], hw⟩

/-- `block_at` answers the block at an index of the timeline. -/
@[step]
theorem block_at_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize)
    (h : index.val < (blocksOf cb).length) :
    client_blocks.ClientBlocksCore.block_at cb index ⦃ b => b = (blocksOf cb)[index.val] ⦄ := by
  unfold client_blocks.ClientBlocksCore.block_at
  step as ⟨o, ho⟩
  rw [ho, List.getElem?_eq_getElem h]
  simp only [spec_ok]

/-- `word_end_at` answers the word of the block at an index and the clock the
block ends at. -/
@[step]
theorem word_end_at_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.word_end_at cb index ⦃ o =>
      (o = none ∧ (blocksOf cb).length ≤ index.val) ∨
        ∃ (w : Std.U128) (e : Std.U64), o = some (w, e) ∧
          (blocksOf cb)[index.val]? = some (blockOf w) ∧
          e.val = endAt (toBlocks cb) cb.end_clock.val index.val ⦄ := by
  unfold client_blocks.ClientBlocksCore.word_end_at
  have hcl := countOf_le cb
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  by_cases h0 : cb.head = 0#u32
  · have h0' : (cb.head = 0#u32) = True := eq_true h0
    simp only [h0', ↓reduceIte]
    have hv : cb.head.val = 0 := by scalar_tac
    step as ⟨len, hlen⟩
    have hlc : len.val = countOf cb := by rw [hlen, length_blocksOf]
    by_cases h : index >= len
    · simp only [h, ↓reduceIte, spec_ok]
      left
      exact ⟨trivial, by scalar_tac⟩
    · simp only [h, ↓reduceIte]
      have hlt : index.val < countOf cb := by scalar_tac
      step as ⟨w, hw⟩
      have hg : cb.buf.val[index.val]? = some w := get?_at (by omega) hw
      have hb : (blocksOf cb)[index.val]? = some (blockOf w) := by
        rw [get?_blocksOf_plain hv hlt, blockAt_of_get? hg]
      step as ⟨next, hnext⟩
      have hnv : next.val = index.val + 1 := by scalar_tac
      by_cases hn : next < len
      · simp only [hn, ↓reduceIte]
        have hnlt : index.val + 1 < countOf cb := by scalar_tac
        step as ⟨w2, hw2⟩
        have hg2 : cb.buf.val[index.val + 1]? = some w2 := by
          rw [← hnv]
          exact get?_at (by omega) hw2
        have hb1 : (blocksOf cb)[index.val + 1]? = some (blockOf w2) := by
          rw [get?_blocksOf_plain hv hnlt, blockAt_of_get? hg2]
        step as ⟨e, he⟩
        right
        refine ⟨w, e, rfl, hb, ?_⟩
        rw [he]
        exact (endAt_toBlocks_some hb1).symm
      · simp only [hn, ↓reduceIte, spec_ok]
        right
        exact ⟨w, cb.end_clock, rfl, hb,
          (endAt_toBlocks_none (by rw [length_blocksOf]; scalar_tac)).symm⟩
  · simp only [h0, ↓reduceIte]
    step as ⟨cap, head, len, hcap, hhead, hlen⟩
    by_cases h : index >= len
    · simp only [h, ↓reduceIte, spec_ok]
      left
      exact ⟨trivial, by rw [length_blocksOf]; scalar_tac⟩
    · simp only [h, ↓reduceIte]
      have hlt : index.val < countOf cb := by scalar_tac
      step as ⟨i, hi, hilt⟩
      step as ⟨w, hw⟩
      have hg : cb.buf.val[i.val]? = some w := get?_at (by omega) hw
      have hb := block_at hcap hhead hlt hi hg
      step as ⟨next, hnext⟩
      have hnv : next.val = index.val + 1 := by scalar_tac
      by_cases hn : next < len
      · simp only [hn, ↓reduceIte]
        have hnlt : index.val + 1 < countOf cb := by scalar_tac
        step as ⟨i2, hi2, hi2lt⟩
        step as ⟨w2, hw2⟩
        have hg2 : cb.buf.val[i2.val]? = some w2 := get?_at (by omega) hw2
        have hb1 : (blocksOf cb)[index.val + 1]? = some (blockOf w2) :=
          block_at hcap hhead hnlt (by rw [hi2, hnv]) hg2
        step as ⟨e, he⟩
        right
        refine ⟨w, e, rfl, hb, ?_⟩
        rw [he]
        exact (endAt_toBlocks_some hb1).symm
      · simp only [hn, ↓reduceIte, spec_ok]
        right
        exact ⟨w, cb.end_clock, rfl, hb,
          (endAt_toBlocks_none (by rw [length_blocksOf]; scalar_tac)).symm⟩

/-- `words`: the words of the blocks in the order of the timeline, those of
the first slice and then those of the second. -/
@[step]
theorem words_spec (cb : client_blocks.ClientBlocksCore) :
    client_blocks.ClientBlocksCore.words cb ⦃ a b =>
      (a.val ++ b.val).map Ring.blockOf = blocksOf cb ⦄ := by
  unfold client_blocks.ClientBlocksCore.words
  have hcl := countOf_le cb
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  by_cases h0 : cb.head = 0#u32
  · have h0' : (cb.head = 0#u32) = True := eq_true h0
    simp only [h0', ↓reduceIte]
    have hv : cb.head.val = 0 := by scalar_tac
    step as ⟨len, hlen⟩
    have hlc : len.val = countOf cb := by rw [hlen, length_blocksOf]
    step as ⟨s, hs, _⟩
    step as ⟨s1, hs1, _⟩
    have hsv : s.val = cb.buf.val.slice 0 len.val := hs
    have hs1v : s1.val = cb.buf.val.slice 0 0 := hs1
    have hl : s.val.length = countOf cb := by
      rw [hsv, List.slice_length]
      omega
    have hl1 : s1.val.length = 0 := by
      rw [hs1v, List.slice_length]
      omega
    symm
    apply blocksOf_ext
    · rw [List.length_map, List.length_append, hl, hl1, Nat.add_zero]
    · intro i hi
      rw [get?_words _ _ _ (by omega), ite_eq_left (by omega), slot_plain hv (by omega), hsv,
        blockAt_slice _ (by omega) (by omega)]
      exact congrArg some (blockAt_congr (get?_congr (by omega)))
  · simp only [h0, ↓reduceIte]
    step as ⟨cap, head, len, hcap, hhead, hlen⟩
    step as ⟨tail, htail⟩
    have htv : tail.val = cap.val - head.val := by scalar_tac
    by_cases hwrap : len > tail
    · simp only [hwrap, ↓reduceIte]
      have hwv : cap.val - head.val < len.val := by scalar_tac
      step as ⟨s, hs, _⟩
      step as ⟨i, hi⟩
      have hiv : i.val = len.val - (cap.val - head.val) := by scalar_tac
      step as ⟨s1, hs1, _⟩
      have hsv : s.val = cb.buf.val.slice head.val cap.val := hs
      have hs1v : s1.val = cb.buf.val.slice 0 i.val := hs1
      have hl : s.val.length = cap.val - head.val := by
        rw [hsv, List.slice_length]
        omega
      have hl1 : s1.val.length = len.val - (cap.val - head.val) := by
        rw [hs1v, List.slice_length]
        omega
      symm
      apply blocksOf_ext
      · rw [List.length_map, List.length_append, hl, hl1]
        omega
      · intro k hk
        rw [get?_words _ _ _ (by omega), hl, ← hcap, ← hhead]
        by_cases hkt : k < cap.val - head.val
        · rw [ite_eq_left hkt, slotOf_lt hkt, hsv, blockAt_slice _ (by omega) (by omega)]
        · rw [ite_eq_right hkt, slotOf_ge hkt, hs1v, blockAt_slice _ (by omega) (by omega)]
          exact congrArg some (blockAt_congr (get?_congr (by omega)))
    · simp only [hwrap, ↓reduceIte]
      have hwv : len.val ≤ cap.val - head.val := by scalar_tac
      step as ⟨i, hi⟩
      have hiv : i.val = head.val + len.val := by scalar_tac
      step as ⟨s, hs, _⟩
      step as ⟨s1, hs1, _⟩
      have hsv : s.val = cb.buf.val.slice head.val i.val := hs
      have hs1v : s1.val = cb.buf.val.slice 0 0 := hs1
      have hl : s.val.length = len.val := by
        rw [hsv, List.slice_length]
        omega
      have hl1 : s1.val.length = 0 := by
        rw [hs1v, List.slice_length]
        omega
      symm
      apply blocksOf_ext
      · rw [List.length_map, List.length_append, hl, hl1]
        omega
      · intro k hk
        rw [get?_words _ _ _ (by omega), ite_eq_left (by omega), ← hcap, ← hhead,
          slotOf_lt (by omega), hsv, blockAt_slice _ (by omega) (by omega)]

/-! ## `append` -/

/-- What `append` guarantees: it either refuses the block and changes
nothing, or puts it at the end of the timeline; and it accepts every block of
at least one clock that continues the timeline and fits. -/
structure AppendPost (cb : client_blocks.ClientBlocksCore) (block : client_blocks.BlockRefCore)
    (len : Std.U64) (r : core.result.Result Unit client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : r = core.result.Result.Ok () →
    0 < len.val ∧ ((blocksOf cb) = [] ∨ block.clock = cb.end_clock) ∧
      (blocksOf cb') = (blocksOf cb) ++ [block] ∧ cb'.end_clock.val = block.clock.val + len.val
  accepts : 0 < len.val → ((blocksOf cb) = [] ∨ block.clock = cb.end_clock) →
    block.clock.val + len.val ≤ Std.U64.max → (blocksOf cb).length < 4294967295 →
    r = core.result.Result.Ok ()

/-- A timeline of no block is the empty timeline. -/
theorem follows_iff {cb : client_blocks.ClientBlocksCore} {blocks : Std.Usize} (clock : Std.U64)
    (hlb : (blocksOf cb).length = blocks.val) :
    (blocks.val = 0 ∨ clock = cb.end_clock) ↔ (blocksOf cb = [] ∨ clock = cb.end_clock) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (List.eq_nil_of_length_eq_zero (by omega))
    · exact Or.inr h
  · rintro (h | h)
    · left
      rw [← hlb, h]
      rfl
    · exact Or.inr h

@[step]
theorem append_spec (cb : client_blocks.ClientBlocksCore) (block : client_blocks.BlockRefCore)
    (len : Std.U64) :
    client_blocks.ClientBlocksCore.append cb block len ⦃ r cb' => AppendPost cb block len r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.append
  by_cases hz : len = 0#u64
  · have hnot : ¬ 0 < len.val := by scalar_tac
    have hz' : (len = 0#u64) = True := eq_true hz
    simp only [hz', ↓reduceIte, spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun h => nomatch h), fun h _ _ _ => absurd h hnot⟩
  · simp only [hz, ↓reduceIte]
    have hpos : 0 < len.val := by scalar_tac
    have hMax : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
    have hRMax : Std.U64.rMax = 2 ^ 64 - 1 := by decide
    have hle : block.clock.val ≤ (core.num.U64.MAX : Std.U64).val := by rw [hMax]; scalar_tac
    have hcl := countOf_le cb
    have hmx := capOf_le_max cb
    by_cases h0 : cb.head = 0#u32
    · -- the blocks are in the order of the slots: the block goes after them
      have h0' : (cb.head = 0#u32) = True := eq_true h0
      simp only [h0', ↓reduceIte]
      have hv : cb.head.val = 0 := by scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.Usize cb.len (by scalar_tac) as ⟨n, hn⟩
      step as ⟨blocks, hblocks⟩
      have hbc : blocks.val = countOf cb := by
        rw [countOf_eq]
        scalar_tac
      have hlb : (blocksOf cb).length = blocks.val := by
        rw [length_blocksOf, hbc]
      step as ⟨b, hb⟩
      by_cases hcont : b = true
      · simp only [hcont, ↓reduceIte]
        have hc := (follows_iff block.clock hlb).mp (hb.mp hcont)
        step as ⟨i, hi⟩
        have hI : i.val = 2 ^ 64 - 1 - block.clock.val := by rw [hi, hRMax]
        by_cases hov : len > i
        · simp only [hov, ↓reduceIte, spec_ok, uncurry'_pair]
          refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ _ hfit _ => ?_⟩
          exfalso
          scalar_tac
        · simp only [hov, ↓reduceIte]
          by_cases hfull : blocks >= client_blocks.MAX_BLOCKS
          · simp only [hfull, ↓reduceIte, spec_ok, uncurry'_pair]
            refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ _ _ hlt => ?_⟩
            exfalso
            simp [client_blocks.MAX_BLOCKS] at hfull
            scalar_tac
          · simp only [hfull, ↓reduceIte]
            have hmax : blocks.val < 4294967295 := by
              simp [client_blocks.MAX_BLOCKS] at hfull
              scalar_tac
            by_cases hroom : blocks < alloc.vec.Vec.len cb.buf
            · simp only [hroom, ↓reduceIte]
              have hrv : blocks.val < cb.buf.val.length := by scalar_tac
              have hrc : blocks.val < capOf cb := by
                unfold capOf
                omega
              step as ⟨word, hword⟩
              step as ⟨p, hold, hback⟩
              have hset' : (p.2 word).val = cb.buf.val.set blocks.val word := by
                rw [hback]
                simp
              obtain ⟨old, back⟩ := p
              have hset : (back word).val = cb.buf.val.set blocks.val word := hset'
              step as ⟨i2, hi2⟩
              step with UScalar.cast_inBounds_spec UScalarTy.U32 i2 (by scalar_tac) as ⟨i3, hi3⟩
              step as ⟨i4, hi4⟩
              have hput : PutIn cb blocks.val blocks.val word { cb with buf := back word } :=
                putIn_plain_set hv hrc hset
              refine ⟨(fun _ h => nomatch h), fun _ => ⟨hpos, hc, ?_, by scalar_tac⟩,
                fun _ _ _ _ => rfl⟩
              rw [blocksOf_of_putIn
                  (cb'' := { cb with buf := back word, len := i3, end_clock := i4 }) hput hbc
                  (Nat.le_refl _) rfl rfl (by show i3.val = blocks.val + 1; scalar_tac), hword,
                ← hlb, insAt_length]
            · simp only [hroom, ↓reduceIte]
              have hfl : cb.buf.val.length = blocks.val := by scalar_tac
              -- `blocks` is no longer the least of two numbers: it is the slots
              clear hblocks hroom
              step as ⟨word, hword⟩
              step as ⟨v, hpush⟩
              have hput : PutIn cb blocks.val blocks.val word { cb with buf := v } :=
                putIn_plain_push hv hfl hmax hpush
              clear hpush
              step as ⟨i2, hi2⟩
              have hi2v : i2.val = blocks.val + 1 := by scalar_tac
              step with UScalar.cast_inBounds_spec UScalarTy.U32 i2 (by scalar_tac) as ⟨i3, hi3⟩
              step as ⟨i4, hi4⟩
              refine ⟨(fun _ h => nomatch h), fun _ => ⟨hpos, hc, ?_, by scalar_tac⟩,
                fun _ _ _ _ => rfl⟩
              rw [blocksOf_of_putIn
                  (cb'' := { cb with buf := v, len := i3, end_clock := i4 }) hput hbc
                  (Nat.le_refl _) rfl rfl (by show i3.val = blocks.val + 1; scalar_tac), hword,
                ← hlb, insAt_length]
      · simp only [hcont, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
        exact ⟨fun _ _ => rfl, (fun h => nomatch h),
          fun _ hc _ _ => absurd (hb.mpr ((follows_iff block.clock hlb).mpr hc)) hcont⟩
    · -- the blocks are a ring
      simp only [h0, ↓reduceIte]
      step as ⟨cap, head, blocks, hcap, hhead, hblocks⟩
      have hlb : (blocksOf cb).length = blocks.val := by
        rw [length_blocksOf, hblocks]
      step as ⟨b, hb⟩
      by_cases hcont : b = true
      · simp only [hcont, ↓reduceIte]
        have hc := (follows_iff block.clock hlb).mp (hb.mp hcont)
        step as ⟨i, hi⟩
        have hI : i.val = 2 ^ 64 - 1 - block.clock.val := by rw [hi, hRMax]
        by_cases hov : len > i
        · simp only [hov, ↓reduceIte, spec_ok, uncurry'_pair]
          refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ _ hfit _ => ?_⟩
          exfalso
          scalar_tac
        · simp only [hov, ↓reduceIte]
          by_cases hfull : blocks >= client_blocks.MAX_BLOCKS
          · simp only [hfull, ↓reduceIte, spec_ok, uncurry'_pair]
            refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ _ _ hlt => ?_⟩
            exfalso
            simp [client_blocks.MAX_BLOCKS] at hfull
            scalar_tac
          · simp only [hfull, ↓reduceIte]
            have hmax : blocks.val < 4294967295 := by
              simp [client_blocks.MAX_BLOCKS] at hfull
              scalar_tac
            step as ⟨word, hword⟩
            step with put_last_spec cb cap head blocks word hcap hhead hblocks hmax
              as ⟨cb1, hput⟩
            step as ⟨i2, hi2⟩
            step with UScalar.cast_inBounds_spec UScalarTy.U32 i2 (by scalar_tac) as ⟨i3, hi3⟩
            step as ⟨i4, hi4⟩
            refine ⟨(fun _ h => nomatch h), fun _ => ⟨hpos, hc, ?_, by scalar_tac⟩,
              fun _ _ _ _ => rfl⟩
            rw [blocksOf_of_putIn (cb'' := { cb1 with len := i3, end_clock := i4 }) hput hblocks
                (Nat.le_refl _) rfl rfl (by show i3.val = blocks.val + 1; scalar_tac), hword,
              ← hlb, insAt_length]
      · simp only [hcont, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
        exact ⟨fun _ _ => rfl, (fun h => nomatch h),
          fun _ hc _ _ => absurd (hb.mpr ((follows_iff block.clock hlb).mpr hc)) hcont⟩

/-- `append` keeps I1. -/
theorem append_wf {cb cb' : client_blocks.ClientBlocksCore} {block : client_blocks.BlockRefCore}
    {len : Std.U64} {r : core.result.Result Unit client_blocks.StoreError} (hwf : WF cb)
    (h : AppendPost cb block len r cb') : WF cb' := by
  cases r with
  | Err e =>
    rw [h.err e rfl]
    exact hwf
  | Ok u =>
    obtain ⟨hpos, hc, hb, he⟩ := h.ok rfl
    constructor
    rw [toBlocks_of_append hb, he]
    refine hwf.timeline.append ?_ ?_
    · rcases hc with hc | hc
      · left
        simp [toBlocks, hc]
      · right
        show cb.end_clock.val = block.clock.val
        rw [hc]
    · show block.clock.val < block.clock.val + len.val
      omega

/-! ## `range` and `find` -/

@[step]
theorem range_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.range cb index ⦃ o =>
      (o = none ∧ (blocksOf cb).length ≤ index.val) ∨
        ∃ (b : client_blocks.BlockRefCore) (e : Std.U64), o = some (b.clock, e) ∧
          (blocksOf cb)[index.val]? = some b ∧
          e.val = endAt (toBlocks cb) cb.end_clock.val index.val ⦄ := by
  unfold client_blocks.ClientBlocksCore.range
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hge⟩ | ⟨w, e, rfl, hb, he⟩
  · simp only [spec_ok]
    left
    exact ⟨trivial, hge⟩
  · dsimp only
    step as ⟨start, hstart⟩
    right
    exact ⟨blockOf w, e, by rw [hstart], hb, he⟩

/-- The blocks of a timeline in the order of their clocks, in the ring. -/
theorem sorted_ring {cb : client_blocks.ClientBlocksCore} (hwf : WF cb) {p q : Nat} (hpq : p < q)
    (hq : q < countOf cb) :
    (blockAt cb.buf.val (slotOf (capOf cb) (firstOf cb) p)).clock.val <
      (blockAt cb.buf.val (slotOf (capOf cb) (firstOf cb) q)).clock.val := by
  refine hwf.timeline.sorted p q (toBlock _) (toBlock _) hpq ?_ ?_
  · rw [toBlocks_get?, get?_blocksOf, ite_eq_left (by omega)]
    rfl
  · rw [toBlocks_get?, get?_blocksOf, ite_eq_left hq]
    rfl

/-- `span`: the slots that hold the block of the clock if a block holds it.
The blocks before them start at or before the clock, the blocks after them
after it, and the slots hold the blocks between in the order of the slots. -/
theorem span_spec (cb : client_blocks.ClientBlocksCore) (clock : Std.U64)
    (cap head len : Std.Usize) (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb)
    (hlen : len.val = countOf cb) (hwf : WF cb) :
    client_blocks.ClientBlocksCore.span cb clock cap head len ⦃ low high before =>
      low.val ≤ high.val ∧ high.val ≤ cb.buf.val.length ∧
      before.val + (high.val - low.val) ≤ len.val ∧
      (∀ k : Nat, k < high.val - low.val →
        slotOf cap.val head.val (before.val + k) = low.val + k) ∧
      (before.val = 0 ∨ (low.val < high.val ∧
        (blockAt cb.buf.val low.val).clock.val ≤ clock.val)) ∧
      (∀ i : Nat, before.val + (high.val - low.val) ≤ i → i < len.val →
        clock.val < (blockAt cb.buf.val (slotOf cap.val head.val i)).clock.val) ⦄ := by
  unfold client_blocks.ClientBlocksCore.span
  have hcl := countOf_le cb
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  have z : (0#usize : Std.Usize).val = 0 := by scalar_tac
  step as ⟨tail, htail⟩
  have htv : tail.val = cap.val - head.val := by scalar_tac
  by_cases hwrap : len > tail
  · simp only [hwrap, ↓reduceIte]
    have hwv : cap.val - head.val < len.val := by scalar_tac
    step as ⟨w, hw⟩
    have hg : cb.buf.val[(0#usize : Std.Usize).val]? = some w := get?_at (by omega) hw
    rw [z] at hg
    have hb0 : blockAt cb.buf.val 0 = blockOf w := blockAt_of_get? hg
    have hs0 : slotOf cap.val head.val (cap.val - head.val) = 0 := by
      rw [slotOf_ge (by omega)]
      omega
    step as ⟨c, hc⟩
    by_cases hle : c <= clock
    · simp only [hle, ↓reduceIte]
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = len.val - (cap.val - head.val) := by scalar_tac
      rw [z, htv]
      refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
      · intro k hk
        rw [slotOf_ge (by omega)]
        omega
      · right
        refine ⟨by omega, ?_⟩
        rw [hb0, ← hc]
        scalar_tac
      · intro i hi1 hi2'
        omega
    · simp only [hle, ↓reduceIte, spec_ok, uncurry'_pair]
      rw [z]
      refine ⟨by omega, by omega, by omega, ?_, Or.inl rfl, ?_⟩
      · intro k hk
        rw [Nat.zero_add, slotOf_lt (by omega)]
      · intro i hi1 hi2'
        have hgt : clock.val < (blockAt cb.buf.val 0).clock.val := by
          rw [hb0, ← hc]
          scalar_tac
        by_cases hie : i = cap.val - head.val
        · rw [hie, hs0]
          exact hgt
        · have hsr := sorted_ring hwf (p := cap.val - head.val) (q := i) (by omega) (by omega)
          rw [← hcap, ← hhead, hs0] at hsr
          omega
  · simp only [hwrap, ↓reduceIte]
    have hwv : len.val ≤ cap.val - head.val := by scalar_tac
    step as ⟨i, hi⟩
    have hiv : i.val = head.val + len.val := by scalar_tac
    rw [z]
    refine ⟨by omega, by omega, by omega, ?_, Or.inl rfl, ?_⟩
    · intro k hk
      rw [Nat.zero_add, slotOf_lt (by omega)]
    · intro i' hi1 hi2
      omega

/-- The blocks of a timeline in the order of their clocks, in a ring in the
order of its slots. -/
theorem sorted_plain {cb : client_blocks.ClientBlocksCore} (hwf : WF cb) (hv : cb.head.val = 0)
    {p q : Nat} (hpq : p < q) (hq : q < countOf cb) :
    (blockAt cb.buf.val p).clock.val < (blockAt cb.buf.val q).clock.val := by
  have hcl := countOf_le cb
  have h := sorted_ring hwf hpq hq
  rw [slot_plain hv (by omega), slot_plain hv (by omega)] at h
  exact h

/-- `first_after`: the first of a run of slots, whose blocks follow each
other, that holds a block that starts after the clock. -/
theorem first_after_spec (cb : client_blocks.ClientBlocksCore) (clock : Std.U64)
    (low high : Std.Usize) (hlh : low.val ≤ high.val) (hhi : high.val ≤ cb.buf.val.length)
    (hs : ∀ p q : Nat, low.val ≤ p → p < q → q < high.val →
      (blockAt cb.buf.val p).clock.val < (blockAt cb.buf.val q).clock.val) :
    client_blocks.ClientBlocksCore.first_after cb clock low high ⦃ r =>
      low.val ≤ r.val ∧ r.val ≤ high.val ∧
      (∀ j : Nat, low.val ≤ j → j < r.val → (blockAt cb.buf.val j).clock.val ≤ clock.val) ∧
      (∀ j : Nat, r.val ≤ j → j < high.val →
        clock.val < (blockAt cb.buf.val j).clock.val) ⦄ := by
  unfold client_blocks.ClientBlocksCore.first_after
  step as ⟨s, hsv', _⟩
  have hsv : s.val = cb.buf.val.slice low.val high.val := hsv'
  have hl : s.val.length = high.val - low.val := by
    rw [hsv, List.slice_length]
    omega
  have hat : ∀ k : Nat, k < high.val - low.val →
      blockAt s.val k = blockAt cb.buf.val (low.val + k) := by
    intro k hk
    rw [hsv]
    exact blockAt_slice _ hhi (by omega)
  have hsorted : ∀ p q : Nat, p < q → q < s.val.length →
      (blockAt s.val p).clock.val < (blockAt s.val q).clock.val := by
    intro p q hpq hq
    rw [hl] at hq
    rw [hat p (by omega), hat q hq]
    exact hs _ _ (by omega) (by omega) (by omega)
  step with count_before_spec s clock hsorted as ⟨n, hn, hbelow, habove⟩
  rw [hl] at hn
  step as ⟨r, hr⟩
  have hrv : r.val = low.val + n.val := by scalar_tac
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro j hj1 hj2
    have h := hbelow (j - low.val) (by omega)
    rw [hat _ (by omega)] at h
    have e : low.val + (j - low.val) = j := by omega
    rw [e] at h
    exact h
  · intro j hj1 hj2
    have h := habove (j - low.val) (by omega) (by rw [hl]; omega)
    rw [hat _ (by omega)] at h
    have e : low.val + (j - low.val) = j := by omega
    rw [e] at h
    exact h

/-- `plain_before`: how many blocks of a ring in the order of its slots start
at or before the clock. -/
theorem plain_before_spec (cb : client_blocks.ClientBlocksCore) (len : Std.Usize)
    (clock : Std.U64) (hv : cb.head.val = 0) (hlen : len.val = countOf cb) (hwf : WF cb) :
    client_blocks.ClientBlocksCore.plain_before cb len clock ⦃ r =>
      r.val ≤ len.val ∧
      (∀ j : Nat, j < r.val → (blockAt cb.buf.val j).clock.val ≤ clock.val) ∧
      (∀ j : Nat, r.val ≤ j → j < len.val →
        clock.val < (blockAt cb.buf.val j).clock.val) ⦄ := by
  unfold client_blocks.ClientBlocksCore.plain_before
  have hcl := countOf_le cb
  have hcb := capOf_le_length cb
  -- the search among the words of the blocks
  have hsearch : ∀ s : Slice Std.U128, s.val = cb.buf.val.slice 0 len.val →
      client_blocks.count_before s clock ⦃ r =>
        r.val ≤ len.val ∧
        (∀ j : Nat, j < r.val → (blockAt cb.buf.val j).clock.val ≤ clock.val) ∧
        (∀ j : Nat, r.val ≤ j → j < len.val →
          clock.val < (blockAt cb.buf.val j).clock.val) ⦄ := by
    intro s hsv
    have hl : s.val.length = len.val := by
      rw [hsv, List.slice_length]
      omega
    have hat : ∀ k : Nat, k < len.val → blockAt s.val k = blockAt cb.buf.val k := by
      intro k hk
      rw [hsv, blockAt_slice _ (by omega) (by omega)]
      exact blockAt_congr (get?_congr (by omega))
    refine spec_mono (count_before_spec s clock ?_) ?_
    · intro p q hpq hq
      rw [hl] at hq
      rw [hat p (by omega), hat q hq]
      exact sorted_plain hwf hv hpq (by omega)
    · rintro r ⟨hr, hbelow, habove⟩
      rw [hl] at hr
      refine ⟨hr, ?_, ?_⟩
      · intro j hj
        rw [← hat j (by omega)]
        exact hbelow j hj
      · intro j hj1 hj2
        rw [← hat j hj2]
        exact habove j hj1 (by rw [hl]; exact hj2)
  by_cases hpos : len > 0#usize
  · simp only [hpos, ↓reduceIte]
    have hlv : 0 < len.val := by scalar_tac
    step as ⟨i, hi⟩
    have hiv : i.val = len.val - 1 := by scalar_tac
    step as ⟨w, hw⟩
    have hg : cb.buf.val[i.val]? = some w := get?_at (by omega) hw
    have hbl : blockAt cb.buf.val (len.val - 1) = blockOf w := by
      rw [← hiv]
      exact blockAt_of_get? hg
    step as ⟨c, hc⟩
    by_cases hle : c <= clock
    · simp only [hle, ↓reduceIte, spec_ok]
      have hlast : (blockAt cb.buf.val (len.val - 1)).clock.val ≤ clock.val := by
        rw [hbl, ← hc]
        scalar_tac
      refine ⟨Nat.le_refl _, ?_, ?_⟩
      · intro j hj
        by_cases hjl : j = len.val - 1
        · rw [hjl]
          exact hlast
        · have h := sorted_plain hwf hv (p := j) (q := len.val - 1) (by omega) (by omega)
          omega
      · intro j hj1 hj2
        omega
    · simp only [hle, ↓reduceIte]
      step as ⟨s, hs, _⟩
      exact hsearch s hs
  · simp only [hpos, ↓reduceIte]
    step as ⟨s, hs, _⟩
    exact hsearch s hs

/-- `locate` answers the block of a ring that holds the clock, if there is
one. -/
theorem locate_spec (cb : client_blocks.ClientBlocksCore) (cap head len : Std.Usize)
    (clock : Std.U64) (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb)
    (hlen : len.val = countOf cb) (hwf : WF cb) (hclock : clock.val < cb.end_clock.val) :
    client_blocks.ClientBlocksCore.locate cb cap head len clock ⦃ o =>
      (o = none ∧ ∀ p, ¬ Holds (toBlocks cb) cb.end_clock.val p clock.val) ∨
        ∃ p : Std.Usize, o = some p ∧ Holds (toBlocks cb) cb.end_clock.val p.val clock.val ⦄ := by
  unfold client_blocks.ClientBlocksCore.locate
  have hcl := countOf_le cb
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  -- the block of an index of the timeline
  have hblock : ∀ i : Nat, i < len.val →
      (toBlocks cb)[i]? =
        some (toBlock (blockAt cb.buf.val (slotOf cap.val head.val i))) := by
    intro i hi
    rw [toBlocks_get?, get?_blocksOf, ite_eq_left (by omega), hcap, hhead]
    rfl
  have hnone : ∀ i : Nat, len.val ≤ i → (toBlocks cb)[i]? = none := by
    intro i hi
    exact get?_none (by rw [toBlocks_length, length_blocksOf]; omega)
  by_cases hz0 : len = 0#usize
  · have hz0' : (len = 0#usize) = True := eq_true hz0
    simp only [hz0', ↓reduceIte, spec_ok]
    have hlv : len.val = 0 := by scalar_tac
    left
    refine ⟨trivial, ?_⟩
    rintro p ⟨a, ha, _, _⟩
    rw [hnone p (by omega)] at ha
    cases ha
  · simp only [hz0, ↓reduceIte]
    have hlv : 0 < len.val := by scalar_tac
    step as ⟨last, hlast⟩
    have hlastv : last.val = len.val - 1 := by scalar_tac
    step as ⟨sl, hsl, hsllt⟩
    step as ⟨wl, hwl⟩
    have hgl : cb.buf.val[sl.val]? = some wl := get?_at (by omega) hwl
    have hbl : blockAt cb.buf.val (slotOf cap.val head.val last.val) = blockOf wl := by
      rw [← hsl]
      exact blockAt_of_get? hgl
    step as ⟨cl, hcl'⟩
    by_cases hle : cl <= clock
    · -- the last block holds the clock
      simp only [hle, ↓reduceIte, spec_ok]
      right
      refine ⟨last, rfl, ?_⟩
      refine ⟨_, hblock last.val (by omega), ?_, ?_⟩
      · show (blockAt cb.buf.val (slotOf cap.val head.val last.val)).clock.val ≤ clock.val
        rw [hbl, ← hcl']
        scalar_tac
      · unfold endAt
        rw [hnone (last.val + 1) (by omega)]
        exact hclock
    · simp only [hle, ↓reduceIte]
      step with span_spec cb clock cap head len hcap hhead hlen hwf
        as ⟨low, high, before, hlh, hhb, hbl', hslots, hbefore, hafter⟩
      have hsorted : ∀ p q : Nat, low.val ≤ p → p < q → q < high.val →
          (blockAt cb.buf.val p).clock.val < (blockAt cb.buf.val q).clock.val := by
        intro p q hp hpq hq
        have h1 := hslots (p - low.val) (by omega)
        have h2 := hslots (q - low.val) (by omega)
        have hsr := sorted_ring hwf (p := before.val + (p - low.val))
          (q := before.val + (q - low.val)) (by omega) (by omega)
        rw [← hcap, ← hhead, h1, h2] at hsr
        have e1 : low.val + (p - low.val) = p := by omega
        have e2 : low.val + (q - low.val) = q := by omega
        rw [e1, e2] at hsr
        exact hsr
      step with first_after_spec cb clock low high hlh hhb hsorted
        as ⟨after, hal, hah, hbelow, habove⟩
      -- every block from `before + (after - low)` on starts after the clock
      have hlater : ∀ i : Nat, before.val + (after.val - low.val) ≤ i → i < len.val →
          clock.val < (blockAt cb.buf.val (slotOf cap.val head.val i)).clock.val := by
        intro i hi1 hi2
        by_cases hin : i < before.val + (high.val - low.val)
        · have h1 := hslots (i - before.val) (by omega)
          have e : before.val + (i - before.val) = i := by omega
          rw [e] at h1
          rw [h1]
          exact habove _ (by omega) (by omega)
        · exact hafter i (by omega) hi2
      by_cases hz : after = low
      · have hz' : (after = low) = True := eq_true hz
        simp only [hz', ↓reduceIte, spec_ok]
        have hav : after.val = low.val := by rw [hz]
        left
        refine ⟨trivial, ?_⟩
        have hb0 : before.val = 0 := by
          rcases hbefore with h0 | ⟨hlt, hle⟩
          · exact h0
          · have := habove low.val (by omega) hlt
            omega
        rintro p ⟨a, ha, hle, _⟩
        by_cases hp : p < len.val
        · rw [hblock p hp] at ha
          cases ha
          have := hlater p (by omega) hp
          have hle' : (blockAt cb.buf.val (slotOf cap.val head.val p)).clock.val ≤ clock.val := hle
          omega
        · rw [hnone p (by omega)] at ha
          cases ha
      · simp only [hz, ↓reduceIte]
        have hav : low.val < after.val := by
          have hne : after.val ≠ low.val := by
            intro h
            apply hz
            apply UScalar.eq_of_val_eq
            simp [h]
          omega
        step as ⟨i, hi⟩
        step as ⟨i1, hi1⟩
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = before.val + (after.val - low.val) - 1 := by scalar_tac
        right
        refine ⟨i2, rfl, ?_⟩
        have hi2l : i2.val < len.val := by omega
        have hslot := hslots (after.val - low.val - 1) (by omega)
        have e : before.val + (after.val - low.val - 1) = i2.val := by omega
        rw [e] at hslot
        refine ⟨_, hblock i2.val hi2l, ?_, ?_⟩
        · show (blockAt cb.buf.val (slotOf cap.val head.val i2.val)).clock.val ≤ clock.val
          rw [hslot]
          exact hbelow _ (by omega) (by omega)
        · unfold endAt
          by_cases hnext : i2.val + 1 < len.val
          · rw [hblock (i2.val + 1) hnext]
            exact hlater (i2.val + 1) (by omega) hnext
          · rw [hnone (i2.val + 1) (by omega)]
            exact hclock

/-- `find` answers the block that holds the clock, if there is one. -/
@[step]
theorem find_spec (cb : client_blocks.ClientBlocksCore) (clock : Std.U64) (hwf : WF cb) :
    client_blocks.ClientBlocksCore.find cb clock ⦃ o =>
      (o = none ∧ ∀ p, ¬ Holds (toBlocks cb) cb.end_clock.val p clock.val) ∨
        ∃ p : Std.Usize, o = some p ∧ Holds (toBlocks cb) cb.end_clock.val p.val clock.val ⦄ := by
  unfold client_blocks.ClientBlocksCore.find
  by_cases hge : clock >= cb.end_clock
  · simp only [hge, ↓reduceIte, spec_ok]
    left
    refine ⟨trivial, ?_⟩
    rintro p ⟨a, _, _, hlt⟩
    have := hwf.timeline.end_le_stop p
    have : cb.end_clock.val ≤ clock.val := by scalar_tac
    omega
  · simp only [hge, ↓reduceIte]
    have hclock : clock.val < cb.end_clock.val := by scalar_tac
    by_cases h0 : cb.head = 0#u32
    · -- the blocks are in the order of the slots
      have h0' : (cb.head = 0#u32) = True := eq_true h0
      simp only [h0', ↓reduceIte]
      have hv : cb.head.val = 0 := by scalar_tac
      have hcl := countOf_le cb
      step as ⟨len, hlen⟩
      have hlc : len.val = countOf cb := by rw [hlen, length_blocksOf]
      step with plain_before_spec cb len clock hv hlc hwf as ⟨after, hal, hbelow, habove⟩
      have hblock : ∀ i : Nat, i < len.val →
          (toBlocks cb)[i]? = some (toBlock (blockAt cb.buf.val i)) := by
        intro i hi
        rw [toBlocks_get?, get?_blocksOf_plain hv (by omega)]
        rfl
      have hnone : ∀ i : Nat, len.val ≤ i → (toBlocks cb)[i]? = none := by
        intro i hi
        exact get?_none (by rw [toBlocks_length, length_blocksOf]; omega)
      by_cases hz : after = 0#usize
      · have hz' : (after = 0#usize) = True := eq_true hz
        simp only [hz', ↓reduceIte, spec_ok]
        have hav : after.val = 0 := by scalar_tac
        left
        refine ⟨trivial, ?_⟩
        rintro p ⟨a, ha, hle, _⟩
        by_cases hp : p < len.val
        · rw [hblock p hp] at ha
          cases ha
          have := habove p (by omega) hp
          have hle' : (blockAt cb.buf.val p).clock.val ≤ clock.val := hle
          omega
        · rw [hnone p (by omega)] at ha
          cases ha
      · simp only [hz, ↓reduceIte]
        have hav : 0 < after.val := by scalar_tac
        step as ⟨i1, hi1⟩
        have hi1v : i1.val = after.val - 1 := by scalar_tac
        right
        refine ⟨i1, rfl, ?_⟩
        refine ⟨_, hblock i1.val (by omega), ?_, ?_⟩
        · show (blockAt cb.buf.val i1.val).clock.val ≤ clock.val
          exact hbelow _ (by omega)
        · unfold endAt
          by_cases hnext : i1.val + 1 < len.val
          · rw [hblock (i1.val + 1) hnext]
            exact habove (i1.val + 1) (by omega) hnext
          · rw [hnone (i1.val + 1) (by omega)]
            exact hclock
    · -- the blocks are a ring
      simp only [h0, ↓reduceIte]
      step as ⟨cap, head, len, hcap, hhead, hlen⟩
      exact locate_spec cb cap head len clock hcap hhead hlen hwf hclock

/-! ## `split_boundary` -/

structure SplitBoundaryPost (cb : client_blocks.ClientBlocksCore) (index : Std.Usize)
    (clock : Std.U64) (kind : client_blocks.BlockKindCore)
    (r : core.result.Result Unit client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : r = core.result.Result.Ok () →
    ∃ b, (blocksOf cb)[index.val]? = some b ∧ b.clock.val < clock.val ∧
      clock.val < endAt (toBlocks cb) cb.end_clock.val index.val ∧
      (blocksOf cb') = insAt (blocksOf cb) (index.val + 1)
        ({ clock := clock, kind := kind } : client_blocks.BlockRefCore) ∧
      cb'.end_clock = cb.end_clock

@[step]
theorem split_boundary_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize)
    (clock : Std.U64) (kind : client_blocks.BlockKindCore) :
    client_blocks.ClientBlocksCore.split_boundary cb index clock kind ⦃ r cb' =>
      SplitBoundaryPost cb index clock kind r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.split_boundary
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, _⟩ | ⟨b, e, rfl, hb, he⟩
  · simp only [spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun h => nomatch h)⟩
  · have hlt := get?_lt hb
    show (if clock ≤ b.clock then _ else _) ⦃ r cb' =>
      SplitBoundaryPost cb index clock kind r cb' ⦄
    by_cases h1 : clock <= b.clock
    · simp only [h1, ↓reduceIte, spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun h => nomatch h)⟩
    · simp only [h1, ↓reduceIte]
      by_cases h2 : clock >= e
      · simp only [h2, ↓reduceIte, spec_ok, uncurry'_pair]
        exact ⟨fun _ _ => rfl, (fun h => nomatch h)⟩
      · simp only [h2, ↓reduceIte]
        step as ⟨cap, head, len, hcap, hhead, hlen⟩
        have hlb : (blocksOf cb).length = len.val := by
          rw [length_blocksOf, hlen]
        by_cases hfull : len >= client_blocks.MAX_BLOCKS
        · simp only [hfull, ↓reduceIte, spec_ok, uncurry'_pair]
          exact ⟨fun _ _ => rfl, (fun h => nomatch h)⟩
        · simp only [hfull, ↓reduceIte]
          have hmax : len.val < 4294967295 := by
            simp [client_blocks.MAX_BLOCKS] at hfull
            scalar_tac
          have hg1 : b.clock.val < clock.val := by scalar_tac
          have hg2 : clock.val < endAt (toBlocks cb) cb.end_clock.val index.val := by
            rw [← he]
            scalar_tac
          step as ⟨at1, hat⟩
          have hatv : at1.val = index.val + 1 := by scalar_tac
          step as ⟨word, hword⟩
          step with put_spec cb cap head len at1 word hcap hhead hlen hmax (by omega)
            as ⟨cb1, hput⟩
          step as ⟨i2, hi2⟩
          step with UScalar.cast_inBounds_spec UScalarTy.U32 i2 (by scalar_tac) as ⟨i3, hi3⟩
          refine ⟨(fun _ h => nomatch h), fun _ => ⟨b, hb, hg1, hg2, ?_, hput.end_clock⟩⟩
          rw [blocksOf_of_putIn (cb'' := { cb1 with len := i3 }) hput hlen (by omega) rfl rfl
              (by show i3.val = len.val + 1; scalar_tac), hword, hatv]

/-- `split_boundary` keeps I1 and the end of the timeline. -/
theorem split_boundary_wf {cb cb' : client_blocks.ClientBlocksCore} {index : Std.Usize}
    {clock : Std.U64} {kind : client_blocks.BlockKindCore}
    {r : core.result.Result Unit client_blocks.StoreError} (hwf : WF cb)
    (h : SplitBoundaryPost cb index clock kind r cb') : WF cb' ∧ cb'.end_clock = cb.end_clock := by
  cases r with
  | Err e =>
    rw [h.err e rfl]
    exact ⟨hwf, rfl⟩
  | Ok u =>
    obtain ⟨b, hb, h1, h2, hbl, he⟩ := h.ok rfl
    refine ⟨⟨?_⟩, he⟩
    rw [toBlocks_of_insAt hbl, he]
    exact hwf.timeline.insert (b := toBlock b) (by rw [toBlocks_get?, hb]; rfl) h1 h2

/-! ## `mark_deleted` and `mark_gc` -/

structure MarkDeletedPost (cb : client_blocks.ClientBlocksCore) (index : Std.Usize)
    (r : core.result.Result Unit client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : r = core.result.Result.Ok () →
    ∃ b i, (blocksOf cb)[index.val]? = some b ∧ kindSlot b.kind = some i ∧
      (blocksOf cb') = (blocksOf cb).set index.val
        ({ clock := b.clock, kind := client_blocks.BlockKindCore.DeletedItem i } :
          client_blocks.BlockRefCore) ∧
      cb'.end_clock = cb.end_clock
  accepts : ∀ b e, (blocksOf cb)[index.val]? = some b → r = core.result.Result.Err e →
    kindSlot b.kind = none

/-- A block of a ring written over. -/
theorem blocksOf_set {cb : client_blocks.ClientBlocksCore} {v : alloc.vec.Vec Std.U128}
    {s : Std.Usize} {index : Nat} {w : Std.U128} (hi : index < countOf cb)
    (hs : s.val = slotOf (capOf cb) (firstOf cb) index) (hv : v.val = cb.buf.val.set s.val w) :
    blocksOf { cb with buf := v } = (blocksOf cb).set index (blockOf w) := by
  have hcl := countOf_le cb
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  have hc' : capOf { cb with buf := v } = capOf cb := by
    unfold capOf
    show min v.val.length 4294967295 = _
    rw [hv, List.length_set]
  have hf' : firstOf { cb with buf := v } = firstOf cb := by
    unfold firstOf
    rw [hc']
  have hn' : countOf { cb with buf := v } = countOf cb := by
    unfold countOf
    rw [hc']
  apply blocksOf_ext
  · rw [List.length_set, length_blocksOf, hn']
  · intro i hi'
    rw [hn'] at hi'
    rw [hc', hf', get?_set, length_blocksOf]
    show _ = some (blockAt v.val (slotOf (capOf cb) (firstOf cb) i))
    have hslot : v.val[slotOf (capOf cb) (firstOf cb) i]? =
        if i = index then some w else cb.buf.val[slotOf (capOf cb) (firstOf cb) i]? := by
      rw [hv, hs]
      exact get?_set_slot _ w hfl hcb (by omega) (by omega)
    by_cases hie : i = index
    · rw [ite_eq_left ⟨hie, hi⟩]
      rw [ite_eq_left hie] at hslot
      rw [blockAt_of_get? hslot]
    · rw [ite_eq_right (fun hc => hie hc.1), get?_blocksOf, ite_eq_left hi']
      rw [ite_eq_right hie] at hslot
      exact congrArg some (blockAt_congr hslot.symm)

@[step]
theorem mark_deleted_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.mark_deleted cb index ⦃ r cb' =>
      MarkDeletedPost cb index r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.mark_deleted
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hge⟩ | ⟨slot, rfl, hlt, hslot, hslotlt⟩
  · simp only [spec_ok, uncurry'_pair]
    refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun b _ hb _ => ?_⟩
    have := get?_lt hb
    rw [length_blocksOf] at this
    omega
  · dsimp only
    step as ⟨w, hw⟩
    have hg : cb.buf.val[slot.val]? = some w := get?_at hslotlt hw
    have hb := block_at_slot hlt hslot hg
    step as ⟨block, hblock⟩
    cases hk : block.kind with
    | Item idx =>
      dsimp only
      step as ⟨w1, hw1⟩
      step as ⟨old, back, hold, hback⟩
      have hv : (back w1).val = cb.buf.val.set slot.val w1 := by
        rw [hback]
        simp
      refine ⟨(fun _ h => nomatch h), fun _ => ⟨blockOf w, idx, hb, by rw [← hblock, hk]; rfl,
        ?_, rfl⟩, (fun _ _ _ h => nomatch h)⟩
      rw [blocksOf_set hlt hslot hv, hw1, hblock]
    | DeletedItem idx =>
      simp only [spec_ok, uncurry'_pair]
      refine ⟨(fun _ h => nomatch h), fun _ => ⟨blockOf w, idx, hb, by rw [← hblock, hk]; rfl,
        ?_, rfl⟩, (fun _ _ _ h => nomatch h)⟩
      have e : ({ clock := (blockOf w).clock, kind := client_blocks.BlockKindCore.DeletedItem idx } :
          client_blocks.BlockRefCore) = blockOf w := by
        rw [← hblock, ← hk]
      rw [e]
      exact (set_eq_self hb).symm
    | Gc =>
      simp only [spec_ok, uncurry'_pair]
      refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun b _ hb' _ => ?_⟩
      rw [hb] at hb'
      cases hb'
      rw [← hblock, hk]
      rfl
    | Skip =>
      simp only [spec_ok, uncurry'_pair]
      refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun b _ hb' _ => ?_⟩
      rw [hb] at hb'
      cases hb'
      rw [← hblock, hk]
      rfl

structure MarkGcPost (cb : client_blocks.ClientBlocksCore) (index : Std.Usize)
    (r : core.result.Result Std.U32 client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : ∀ i, r = core.result.Result.Ok i →
    ∃ b, (blocksOf cb)[index.val]? = some b ∧
      b.kind = client_blocks.BlockKindCore.DeletedItem i ∧
      (blocksOf cb') = (blocksOf cb).set index.val
        ({ clock := b.clock, kind := client_blocks.BlockKindCore.Gc } :
          client_blocks.BlockRefCore) ∧
      cb'.end_clock = cb.end_clock

@[step]
theorem mark_gc_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.mark_gc cb index ⦃ r cb' => MarkGcPost cb index r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.mark_gc
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hge⟩ | ⟨slot, rfl, hlt, hslot, hslotlt⟩
  · simp only [spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun _ h => nomatch h)⟩
  · dsimp only
    step as ⟨w, hw⟩
    have hg : cb.buf.val[slot.val]? = some w := get?_at hslotlt hw
    have hb := block_at_slot hlt hslot hg
    step as ⟨block, hblock⟩
    cases hk : block.kind with
    | Item idx =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun _ h => nomatch h)⟩
    | DeletedItem idx =>
      dsimp only
      step as ⟨w1, hw1⟩
      step as ⟨old, back, hold, hback⟩
      have hv : (back w1).val = cb.buf.val.set slot.val w1 := by
        rw [hback]
        simp
      refine ⟨(fun _ h => nomatch h), fun i h => ?_⟩
      cases h
      refine ⟨blockOf w, hb, by rw [← hblock, hk], ?_, rfl⟩
      rw [blocksOf_set hlt hslot hv, hw1, hblock]
    | Gc =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun _ h => nomatch h)⟩
    | Skip =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun _ h => nomatch h)⟩

/-- Setting the kind of a block keeps I1 and the end of the timeline. -/
theorem set_kind_wf {cb cb' : client_blocks.ClientBlocksCore} {index : Nat}
    {b : client_blocks.BlockRefCore} {kind : client_blocks.BlockKindCore} (hwf : WF cb)
    (hb : (blocksOf cb)[index]? = some b)
    (hbl : (blocksOf cb') = (blocksOf cb).set index
      ({ clock := b.clock, kind := kind } : client_blocks.BlockRefCore))
    (he : cb'.end_clock = cb.end_clock) : WF cb' := by
  constructor
  rw [toBlocks_of_set hbl, he]
  apply hwf.timeline.update
  intro a ha
  rw [toBlocks_get?, hb] at ha
  cases ha
  rfl

/-! ## A run of blocks taken away: `take a ++ drop b` -/

/-- The list without its elements `a..b`, by index. -/
theorem get?_take_append_drop {α : Type} (l : List α) {a b : Nat} (hab : a ≤ b)
    (ha : a ≤ l.length) (j : Nat) :
    (l.take a ++ l.drop b)[j]? = if j < a then l[j]? else l[j + (b - a)]? := by
  have hlen : (l.take a).length = a := by
    rw [List.length_take]
    omega
  by_cases hj : j < a
  · rw [ite_eq_left hj, get?_append_left (by rw [hlen]; exact hj)]
    simp [hj]
  · obtain ⟨k, rfl⟩ : ∃ k, j = a + k := ⟨j - a, by omega⟩
    rw [ite_eq_right hj]
    have h := get?_append_right (l.take a) (l.drop b) k
    rw [hlen] at h
    rw [h, List.getElem?_drop]
    have e : b + k = a + k + (b - a) := by omega
    rw [e]

/-- Taking a run of block boundaries away keeps the timeline. -/
theorem timelineWF_take_append_drop {blocks : List MBlock} {stop : Nat}
    (h : TimelineWF blocks stop) {a b : Nat} (hab : a ≤ b) (ha : a ≤ blocks.length) :
    TimelineWF (blocks.take a ++ blocks.drop b) stop := by
  have key : ∀ (p : Nat) (x : MBlock), (blocks.take a ++ blocks.drop b)[p]? = some x →
      (p < a ∧ blocks[p]? = some x) ∨ (a ≤ p ∧ blocks[p + (b - a)]? = some x) := by
    intro p x hx
    rw [get?_take_append_drop blocks hab ha p] at hx
    by_cases hp : p < a
    · rw [ite_eq_left hp] at hx
      exact Or.inl ⟨hp, hx⟩
    · rw [ite_eq_right hp] at hx
      exact Or.inr ⟨by omega, hx⟩
  constructor
  · intro p q x y hpq hx hy
    rcases key p x hx with ⟨hp, hx'⟩ | ⟨hp, hx'⟩
    · rcases key q y hy with ⟨hq, hy'⟩ | ⟨hq, hy'⟩
      · exact h.sorted p q x y hpq hx' hy'
      · exact h.sorted p (q + (b - a)) x y (by omega) hx' hy'
    · rcases key q y hy with ⟨hq, hy'⟩ | ⟨hq, hy'⟩
      · omega
      · exact h.sorted (p + (b - a)) (q + (b - a)) x y (by omega) hx' hy'
  · intro p x hx
    rcases key p x hx with ⟨_, hx'⟩ | ⟨_, hx'⟩
    · exact h.below p x hx'
    · exact h.below (p + (b - a)) x hx'

theorem toBlocks_of_run {cb cb' : client_blocks.ClientBlocksCore} {a b : Nat}
    (h : (blocksOf cb') = (blocksOf cb).take a ++ (blocksOf cb).drop b) :
    toBlocks cb' = (toBlocks cb).take a ++ (toBlocks cb).drop b := by
  unfold toBlocks
  rw [h]
  simp

/-- A block boundary taken away `k` times at the same place: what `k` calls of
`merge_adjacent` on the same block do. -/
def delAtN {α : Type} (l : List α) (i : Nat) : Nat → List α
  | 0 => l
  | k + 1 => delAtN (delAt l i) i k

theorem get?_delAtN {α : Type} (i : Nat) : ∀ (k : Nat) (l : List α) (j : Nat),
    (delAtN l i k)[j]? = if j < i then l[j]? else l[j + k]?
  | 0, l, j => by simp [delAtN]
  | k + 1, l, j => by
    show (delAtN (delAt l i) i k)[j]? = _
    rw [get?_delAtN i k (delAt l i) j]
    by_cases hj : j < i
    · rw [ite_eq_left hj, ite_eq_left hj, get?_delAt_lt l hj]
    · rw [ite_eq_right hj, ite_eq_right hj, get?_delAt_ge l (by omega : i ≤ j + k)]
      have e : j + k + 1 = j + (k + 1) := by omega
      rw [e]

/-! ## `merge_range` -/

/-- Every two neighbours among the blocks `first..=last` are of the same
kind. -/
def SameKindRun (l : List client_blocks.BlockRefCore) (first last : Nat) : Prop :=
  ∀ (i : Nat) (a b : client_blocks.BlockRefCore), first ≤ i → i < last → l[i]? = some a →
    l[i + 1]? = some b → sameKind a.kind b.kind = true

/-- Two kinds are the same kind if and only if they have the same tag. -/
theorem sameKind_iff_tag (a b : client_blocks.BlockKindCore) :
    sameKind a b = true ↔ tagOfKind a = tagOfKind b := by
  cases a <;> cases b <;> simp [sameKind, tagOfKind]

theorem same_kind_run_loop_spec (cb : client_blocks.ClientBlocksCore)
    (cap head first last : Std.Usize) (tag : Std.U64) (i : Std.Usize)
    (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb)
    (hl : last.val < (blocksOf cb).length)
    (hinv : first.val ≤ i.val ∧ i.val ≤ last.val ∧
      ∀ (p : Nat) (b : client_blocks.BlockRefCore), first.val ≤ p → p ≤ i.val →
        (blocksOf cb)[p]? = some b → tagOfKind b.kind = tag.val) :
    client_blocks.ClientBlocksCore.same_kind_run_loop cb.buf cap head last tag i ⦃ r =>
      (r = true ↔ SameKindRun (blocksOf cb) first.val last.val) ⦄ := by
  unfold client_blocks.ClientBlocksCore.same_kind_run_loop
  have hcl := countOf_le cb
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  rw [length_blocksOf] at hl
  refine loop.spec_decr_nat
    (fun (j : Std.Usize) => last.val - j.val)
    (fun (j : Std.Usize) => first.val ≤ j.val ∧ j.val ≤ last.val ∧
      ∀ (p : Nat) (b : client_blocks.BlockRefCore), first.val ≤ p → p ≤ j.val →
        (blocksOf cb)[p]? = some b → tagOfKind b.kind = tag.val)
    (fun (r : Bool) => (r = true ↔ SameKindRun (blocksOf cb) first.val last.val))
    _ i ?_ hinv
  intro j ⟨hfj, hjl, hrun⟩
  unfold client_blocks.ClientBlocksCore.same_kind_run_loop.body
  by_cases hlt : j < last
  · simp only [hlt, ↓reduceIte]
    have hjlt : j.val < last.val := by scalar_tac
    step as ⟨next, hnext⟩
    have hnextv : next.val = j.val + 1 := by scalar_tac
    step as ⟨s2, hs2, hs2lt⟩
    step as ⟨w2, hw2⟩
    have hg2 : cb.buf.val[s2.val]? = some w2 := get?_at (by omega) hw2
    have hb : (blocksOf cb)[j.val + 1]? = some (blockOf w2) :=
      block_at hcap hhead (by omega) (by rw [hs2, hnextv]) hg2
    step as ⟨t2, ht2⟩
    by_cases hne : (t2 != tag) = true
    · -- a block of another kind
      rw [ite_eq_left hne]
      simp only [spec_ok]
      refine ⟨fun h => ?_, fun hall => ?_⟩
      · simp at h
      · exfalso
        obtain ⟨a, ha⟩ := get?_some (by rw [length_blocksOf]; omega : j.val < (blocksOf cb).length)
        have h1 := hrun j.val a hfj (Nat.le_refl _) ha
        have h2 := (sameKind_iff_tag _ _).mp (hall j.val a (blockOf w2) hfj hjlt ha hb)
        have hneq : t2 ≠ tag := by simpa using hne
        apply hneq
        apply UScalar.eq_of_val_eq
        rw [ht2, ← h2, h1]
    · rw [ite_eq_right hne]
      simp only [spec_ok]
      have hv : t2.val = tag.val := by simpa using hne
      refine ⟨by omega, by omega, ?_, by omega⟩
      intro p b hp1 hp2 hpb
      by_cases hpj : p = j.val + 1
      · rw [hpj, hb] at hpb
        cases hpb
        rw [← ht2]
        exact hv
      · exact hrun p b hp1 (by omega) hpb
  · simp only [hlt, ↓reduceIte, spec_ok]
    have heq : j.val = last.val := by scalar_tac
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    intro p a b hp1 hp2 hpa hpb
    have h1 := hrun p a hp1 (by omega) hpa
    have h2 := hrun (p + 1) b (by omega) (by omega) hpb
    exact (sameKind_iff_tag _ _).mpr (by rw [h1, h2])

/-- `same_kind_run` says whether the blocks `first..=last` can become one:
whether each of them is of the kind of the first. -/
theorem same_kind_run_spec (cb : client_blocks.ClientBlocksCore)
    (cap head first last : Std.Usize) (hcap : cap.val = capOf cb)
    (hhead : head.val = firstOf cb) (hfl : first.val ≤ last.val)
    (hl : last.val < (blocksOf cb).length) :
    client_blocks.ClientBlocksCore.same_kind_run cb cap head first last ⦃ r =>
      (r = true ↔ SameKindRun (blocksOf cb) first.val last.val) ⦄ := by
  unfold client_blocks.ClientBlocksCore.same_kind_run
  have hcl := countOf_le cb
  have hfle := firstOf_le cb
  have hcb := capOf_le_length cb
  have hl' : last.val < countOf cb := by
    rw [← length_blocksOf]
    exact hl
  step as ⟨s, hs, hslt⟩
  step as ⟨w, hw⟩
  have hg : cb.buf.val[s.val]? = some w := get?_at (by omega) hw
  have hb := block_at hcap hhead (by omega : first.val < countOf cb) hs hg
  step as ⟨tag, htag⟩
  refine same_kind_run_loop_spec cb cap head first last tag first hcap hhead hl
    ⟨Nat.le_refl _, hfl, ?_⟩
  intro p b hp1 hp2 hpb
  have e : p = first.val := by omega
  rw [e, hb] at hpb
  cases hpb
  exact htag.symm

/-- What `merge_range` guarantees: it either refuses and changes nothing, or
takes the blocks `first + 1..=last` away, so that the block at `first` reaches
to where the block at `last` ended; and it accepts every run of blocks of the
same kind. -/
structure MergeRangePost (cb : client_blocks.ClientBlocksCore) (first last : Std.Usize)
    (r : core.result.Result Unit client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : r = core.result.Result.Ok () →
    first.val ≤ last.val ∧ last.val < (blocksOf cb).length ∧
      SameKindRun (blocksOf cb) first.val last.val ∧
      (blocksOf cb') =
        (blocksOf cb).take (first.val + 1) ++ (blocksOf cb).drop (last.val + 1) ∧
      cb'.end_clock = cb.end_clock
  accepts : first.val ≤ last.val → last.val < (blocksOf cb).length →
    SameKindRun (blocksOf cb) first.val last.val → r = core.result.Result.Ok ()

/-- `last_two` says yes only of the last two blocks of a ring in the order of
its slots. -/
theorem last_two_spec (cb : client_blocks.ClientBlocksCore) (first last : Std.Usize)
    (hfl : first.val ≤ last.val) :
    client_blocks.ClientBlocksCore.last_two cb first last ⦃ b =>
      b = true →
        cb.head.val = 0 ∧ last.val = first.val + 1 ∧ last.val + 1 = (blocksOf cb).length ⦄ := by
  unfold client_blocks.ClientBlocksCore.last_two
  by_cases h0 : (cb.head != 0#u32) = true
  · rw [ite_eq_left h0]
    refine (spec_ok _).mpr ?_
    intro h
    cases h
  · rw [ite_eq_right h0]
    have hv : cb.head.val = 0 := by simpa using h0
    step as ⟨len, hlen⟩
    by_cases h1 : last >= len
    · simp only [h1, ↓reduceIte]
      refine (spec_ok _).mpr ?_
      intro h
      cases h
    · simp only [h1, ↓reduceIte]
      step as ⟨i, hi⟩
      by_cases h2 : (i != 1#usize) = true
      · rw [ite_eq_left h2]
        refine (spec_ok _).mpr ?_
        intro h
        cases h
      · rw [ite_eq_right h2]
        have hi1 : i.val = 1 := by simpa using h2
        step as ⟨i1, hi1'⟩
        intro h
        have hone : i1 = 1#usize := by simpa using h
        exact ⟨hv, by scalar_tac, by scalar_tac⟩

/-- `merge_last_two`: the last block of a ring in the order of its slots is no
longer counted, if it is of the kind of the block before it. -/
theorem merge_last_two_spec (cb : client_blocks.ClientBlocksCore) (first last : Std.Usize)
    (hv : cb.head.val = 0) (hlf : last.val = first.val + 1)
    (hll : last.val + 1 = (blocksOf cb).length) :
    client_blocks.ClientBlocksCore.merge_last_two cb first last ⦃ r cb' =>
      MergeRangePost cb first last r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.merge_last_two
  have hcl := countOf_le cb
  have hcb := capOf_le_length cb
  have hmx := capOf_le_max cb
  have hn : last.val + 1 = countOf cb := by
    rw [← length_blocksOf]
    exact hll
  step as ⟨w1, hw1⟩
  step as ⟨w2, hw2⟩
  have hg1 : cb.buf.val[first.val]? = some w1 := get?_at (by omega) hw1
  have hg2 : cb.buf.val[last.val]? = some w2 := get?_at (by omega) hw2
  have hb1 : (blocksOf cb)[first.val]? = some (blockOf w1) := by
    rw [get?_blocksOf_plain hv (by omega), blockAt_of_get? hg1]
  have hb2 : (blocksOf cb)[first.val + 1]? = some (blockOf w2) := by
    rw [← hlf, get?_blocksOf_plain hv (by omega), blockAt_of_get? hg2]
  have hrun : SameKindRun (blocksOf cb) first.val last.val ↔
      tagOfKind (blockOf w1).kind = tagOfKind (blockOf w2).kind := by
    constructor
    · intro h
      exact (sameKind_iff_tag _ _).mp (h first.val _ _ (Nat.le_refl _) (by omega) hb1 hb2)
    · intro h i a b hi1 hi2 ha hb
      have e : i = first.val := by omega
      rw [e, hb1] at ha
      rw [e, hb2] at hb
      cases ha
      cases hb
      exact (sameKind_iff_tag _ _).mpr h
  step as ⟨b, hb⟩
  by_cases hs : b = true
  · simp only [hs, ↓reduceIte]
    step with UScalar.cast_inBounds_spec UScalarTy.U32 last (by scalar_tac) as ⟨i2, hi2⟩
    refine ⟨(fun _ h => nomatch h),
      fun _ => ⟨by omega, by omega, hrun.mpr (hb.mp hs), ?_, rfl⟩, fun _ _ _ => rfl⟩
    -- nothing moves: the blocks before the last are where they were
    have hclosed : Closed cb (last.val + 1) first.val 1 cb := by
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro i hi
      rw [ite_eq_left (by omega)]
    rw [blocksOf_of_closed (cb'' := { cb with len := i2 }) hclosed hn (by omega) rfl rfl
      (by show i2.val = last.val + 1 - 1; scalar_tac), hlf]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
    refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ _ hr => ?_⟩
    exact absurd (hb.mpr (hrun.mp hr)) hs

/-- `merge_run`: the blocks `first + 1..=last` of a ring are taken away, if
each of the run is of the kind of the first. -/
theorem merge_run_spec (cb : client_blocks.ClientBlocksCore) (first last : Std.Usize)
    (hfl : first.val ≤ last.val) :
    client_blocks.ClientBlocksCore.merge_run cb first last ⦃ r cb' =>
      MergeRangePost cb first last r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.merge_run
  step as ⟨cap, head, len, hcap, hhead, hlen⟩
  have hlb : (blocksOf cb).length = len.val := by
    rw [length_blocksOf, hlen]
  by_cases h2 : last >= len
  · simp only [h2, ↓reduceIte, spec_ok, uncurry'_pair]
    refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ hl _ => ?_⟩
    exfalso
    scalar_tac
  · simp only [h2, ↓reduceIte]
    have hl : last.val < (blocksOf cb).length := by scalar_tac
    step with same_kind_run_spec cb cap head first last hcap hhead hfl hl as ⟨b, hb⟩
    by_cases hs : b = true
    · simp only [hs, ↓reduceIte]
      have hrun := hb.mp hs
      by_cases h3 : first < last
      · simp only [h3, ↓reduceIte]
        have hlt : first.val < last.val := by scalar_tac
        have hcl := countOf_le cb
        have hmx := capOf_le_max cb
        step with close_spec cb cap head len first last hcap hhead hlen hlt (by omega)
          as ⟨cb1, hclosed⟩
        step as ⟨i, hi⟩
        step as ⟨i1, hi1⟩
        step with UScalar.cast_inBounds_spec UScalarTy.U32 i1 (by scalar_tac) as ⟨i2, hi2⟩
        refine ⟨(fun _ h => nomatch h), fun _ => ⟨hfl, hl, hrun, ?_, hclosed.end_clock⟩,
          fun _ _ _ => rfl⟩
        rw [blocksOf_of_closed (cb'' := { cb1 with len := i2 }) hclosed hlen (by omega) rfl rfl
          (by show i2.val = len.val - (last.val - first.val); scalar_tac)]
        have e : first.val + (last.val - first.val) + 1 = last.val + 1 := by omega
        rw [e]
      · simp only [h3, ↓reduceIte, spec_ok, uncurry'_pair]
        have heq : first.val = last.val := by scalar_tac
        refine ⟨(fun _ h => nomatch h), fun _ => ⟨hfl, hl, hrun, ?_, rfl⟩, fun _ _ _ => rfl⟩
        rw [heq, List.take_append_drop]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
      refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ _ hrun => ?_⟩
      exact absurd (hb.mpr hrun) hs

@[step]
theorem merge_range_spec (cb : client_blocks.ClientBlocksCore) (first last : Std.Usize) :
    client_blocks.ClientBlocksCore.merge_range cb first last ⦃ r cb' =>
      MergeRangePost cb first last r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.merge_range
  by_cases h1 : first > last
  · simp only [h1, ↓reduceIte, spec_ok, uncurry'_pair]
    refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun hfl _ _ => ?_⟩
    exfalso
    scalar_tac
  · simp only [h1, ↓reduceIte]
    have hfl : first.val ≤ last.val := by scalar_tac
    step with last_two_spec cb first last hfl as ⟨b, hb⟩
    by_cases hb1 : b = true
    · simp only [hb1, ↓reduceIte]
      obtain ⟨hv, hlf, hll⟩ := hb hb1
      exact merge_last_two_spec cb first last hv hlf hll
    · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
      exact merge_run_spec cb first last hfl

/-- `merge_range` keeps I1 and the end of the timeline. -/
theorem merge_range_wf {cb cb' : client_blocks.ClientBlocksCore} {first last : Std.Usize}
    {r : core.result.Result Unit client_blocks.StoreError} (hwf : WF cb)
    (h : MergeRangePost cb first last r cb') : WF cb' ∧ cb'.end_clock = cb.end_clock := by
  cases r with
  | Err e =>
    rw [h.err e rfl]
    exact ⟨hwf, rfl⟩
  | Ok u =>
    obtain ⟨hfl, hl, _, hbl, he⟩ := h.ok rfl
    refine ⟨⟨?_⟩, he⟩
    rw [toBlocks_of_run hbl, he]
    exact timelineWF_take_append_drop hwf.timeline (by omega)
      (by rw [toBlocks_length]; omega)

/-- What `merge_range` does to the timeline, block by block: the blocks up to
`first` are the blocks they were, and the blocks after it are the blocks that
were after `last`; the blocks before `first` end where they did, and the block
at `first` and the ones after it end where the block `last - first` places
further did. So the block at `first` keeps its start and its kind and takes
the clocks of the whole run, and no other block changes. -/
theorem merge_range_blocks {cb cb' : client_blocks.ClientBlocksCore} {first last : Std.Usize}
    (h : MergeRangePost cb first last (core.result.Result.Ok ()) cb') (p : Nat) :
    (toBlocks cb')[p]? =
        (if p ≤ first.val then (toBlocks cb)[p]?
          else (toBlocks cb)[p + (last.val - first.val)]?) ∧
      endAt (toBlocks cb') cb'.end_clock.val p =
        (if p < first.val then endAt (toBlocks cb) cb.end_clock.val p
          else endAt (toBlocks cb) cb.end_clock.val (p + (last.val - first.val))) := by
  obtain ⟨hfl, hl, _, hbl, he⟩ := h.ok rfl
  have hlen : first.val + 1 ≤ (toBlocks cb).length := by
    rw [toBlocks_length]
    omega
  have key : ∀ q : Nat, (toBlocks cb')[q]? =
      if q < first.val + 1 then (toBlocks cb)[q]?
      else (toBlocks cb)[q + (last.val + 1 - (first.val + 1))]? := by
    intro q
    rw [toBlocks_of_run hbl]
    exact get?_take_append_drop (toBlocks cb) (by omega) hlen q
  have e1 : ∀ q : Nat, q + (last.val + 1 - (first.val + 1)) = q + (last.val - first.val) := by
    intro q
    omega
  constructor
  · rw [key p, e1 p]
    by_cases hp : p ≤ first.val
    · rw [ite_eq_left hp, ite_eq_left (by omega)]
    · rw [ite_eq_right hp, ite_eq_right (by omega)]
  · have hend : endAt (toBlocks cb') cb'.end_clock.val p =
        if p < first.val then endAt (toBlocks cb) cb.end_clock.val p
        else endAt (toBlocks cb) cb.end_clock.val (p + (last.val - first.val)) := by
      by_cases hp : p < first.val
      · rw [ite_eq_left hp]
        unfold endAt
        rw [key (p + 1), ite_eq_left (by omega), he]
      · rw [ite_eq_right hp]
        unfold endAt
        rw [key (p + 1), ite_eq_right (by omega), e1 (p + 1), he]
        have e : p + 1 + (last.val - first.val) = p + (last.val - first.val) + 1 := by omega
        rw [e]
    exact hend

/-- `merge_range first last` is `merge_adjacent first`, `last - first` times:
each of them takes the block boundary after `first` away (`MergePost.ok`). -/
theorem merge_range_eq_merge_adjacent {cb cb' : client_blocks.ClientBlocksCore}
    {first last : Std.Usize}
    (h : MergeRangePost cb first last (core.result.Result.Ok ()) cb') :
    (blocksOf cb') = delAtN (blocksOf cb) (first.val + 1) (last.val - first.val) := by
  obtain ⟨hfl, hl, _, hbl, _⟩ := h.ok rfl
  rw [hbl]
  apply ext_get?
  intro j
  rw [get?_take_append_drop (blocksOf cb) (by omega) (by omega) j, get?_delAtN]
  have e : last.val + 1 - (first.val + 1) = last.val - first.val := by omega
  rw [e]

/-! ## `merge_adjacent` -/

structure MergePost (cb : client_blocks.ClientBlocksCore) (index : Std.Usize)
    (r : core.result.Result Unit client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : r = core.result.Result.Ok () →
    ∃ a b, (blocksOf cb)[index.val]? = some a ∧ (blocksOf cb)[index.val + 1]? = some b ∧
      sameKind a.kind b.kind = true ∧ (blocksOf cb') = delAt (blocksOf cb) (index.val + 1) ∧
      cb'.end_clock = cb.end_clock

@[step]
theorem merge_adjacent_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.merge_adjacent cb index ⦃ r cb' =>
      MergePost cb index r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.merge_adjacent
  step as ⟨n, hn⟩
  have hbnd := capOf_le_max cb
  have hcl := countOf_le cb
  have hlb := length_blocksOf cb
  by_cases h : index >= n
  · simp only [h, ↓reduceIte, spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun h => nomatch h)⟩
  · simp only [h, ↓reduceIte]
    have hlt : index.val < (blocksOf cb).length := by scalar_tac
    step as ⟨next, hnext⟩
    have hnextv : next.val = index.val + 1 := by scalar_tac
    refine spec_mono (merge_range_spec cb index next) ?_
    rintro ⟨r, cb'⟩ hr
    have hpost : MergeRangePost cb index next r cb' := hr
    show MergePost cb index r cb'
    refine ⟨hpost.err, fun hok => ?_⟩
    obtain ⟨_, hl, hrun, hbl, he⟩ := hpost.ok hok
    obtain ⟨a, ha⟩ := get?_some hlt
    obtain ⟨b, hb⟩ := get?_some (by omega : index.val + 1 < (blocksOf cb).length)
    refine ⟨a, b, ha, hb, hrun index.val a b (Nat.le_refl _) (by omega) ha hb, ?_, he⟩
    rw [hbl, delAt_eq, hnextv]

/-- `merge_adjacent` keeps I1 and the end of the timeline. -/
theorem merge_adjacent_wf {cb cb' : client_blocks.ClientBlocksCore} {index : Std.Usize}
    {r : core.result.Result Unit client_blocks.StoreError} (hwf : WF cb)
    (h : MergePost cb index r cb') : WF cb' ∧ cb'.end_clock = cb.end_clock := by
  cases r with
  | Err e =>
    rw [h.err e rfl]
    exact ⟨hwf, rfl⟩
  | Ok u =>
    obtain ⟨a, b, _, hb, _, hbl, he⟩ := h.ok rfl
    refine ⟨⟨?_⟩, he⟩
    rw [toBlocks_of_delAt hbl, he]
    exact hwf.timeline.remove _

/-! ## `remap_slots` -/

/-- Where a table of moved slots says the item of slot `slot` went: an entry
is one more than the new slot, and `0` for a slot that held no item. -/
def movedTo (moved : List Std.U32) (slot : Nat) : Option Nat :=
  match moved[slot]? with
  | none => none
  | some m => if m.val = 0 then none else some (m.val - 1)

@[step]
theorem moved_slot_spec (moved : Slice Std.U32) (slot : Std.U32) :
    client_blocks.moved_slot moved slot ⦃ o =>
      o.map (fun t : Std.U32 => t.val) = movedTo moved.val slot.val ⦄ := by
  unfold client_blocks.moved_slot
  have hcast : slot.val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  step with UScalar.cast_inBounds_spec UScalarTy.Usize slot hcast as ⟨at1, hat⟩
  by_cases h : at1 >= Slice.len moved
  · simp only [h, ↓reduceIte, spec_ok]
    have hn : moved.val[slot.val]? = none := get?_none (by scalar_tac)
    simp [movedTo, hn]
  · simp only [h, ↓reduceIte]
    have hlt : at1.val < moved.val.length := by scalar_tac
    step as ⟨to1, hto⟩
    have hm : moved.val[slot.val]? = some to1 := by
      rw [← hat]
      exact get?_of_getElem hlt hto
    by_cases hz : to1 = 0#u32
    · have hz' : (to1 = 0#u32) = True := eq_true hz
      simp only [hz', ↓reduceIte, spec_ok]
      have h0 : to1.val = 0 := by scalar_tac
      simp [movedTo, hm, h0]
    · simp only [hz, ↓reduceIte]
      have hpos : 0 < to1.val := by scalar_tac
      step as ⟨t, ht⟩
      have htv : t.val = to1.val - 1 := by scalar_tac
      have hne : ¬ to1.val = 0 := by omega
      simp [movedTo, hm, hne, htv]

/-- `moved_kind` on the model: an item block names the slot the table gives
for its item, if it gives one. -/
def remapKind (moved : List Std.U32) : MKind → MKind
  | .item s =>
    match movedTo moved s with
    | some t => .item t
    | none => .item s
  | .deleted s =>
    match movedTo moved s with
    | some t => .deleted t
    | none => .deleted s
  | .gc => .gc
  | .skip => .skip

/-- A renamed block is deleted if and only if it was. -/
theorem remapKind_dead (moved : List Std.U32) (k : MKind) :
    (remapKind moved k).dead = k.dead := by
  cases k with
  | item s => cases h : movedTo moved s <;> simp [remapKind, h, MKind.dead]
  | deleted s => cases h : movedTo moved s <;> simp [remapKind, h, MKind.dead]
  | gc => rfl
  | skip => rfl

/-- A renamed item block names the slot the table gives for its item. -/
theorem remapKind_slot (moved : List Std.U32) {k : MKind} {s t : Nat} (hs : k.slot = some s)
    (ht : movedTo moved s = some t) : (remapKind moved k).slot = some t := by
  cases k with
  | item i =>
    have e : i = s := by simpa [MKind.slot] using hs
    subst e
    simp [remapKind, ht, MKind.slot]
  | deleted i =>
    have e : i = s := by simpa [MKind.slot] using hs
    subst e
    simp [remapKind, ht, MKind.slot]
  | gc => simp [MKind.slot] at hs
  | skip => simp [MKind.slot] at hs

/-- A block that is no item block is not renamed. -/
theorem remapKind_no_slot (moved : List Std.U32) {k : MKind} (hs : k.slot = none) :
    remapKind moved k = k := by
  cases k with
  | item i => simp [MKind.slot] at hs
  | deleted i => simp [MKind.slot] at hs
  | gc => rfl
  | skip => rfl

@[step]
theorem moved_kind_spec (moved : Slice Std.U32) (kind : client_blocks.BlockKindCore) :
    client_blocks.moved_kind moved kind ⦃ k =>
      toKind k = remapKind moved.val (toKind kind) ⦄ := by
  unfold client_blocks.moved_kind
  cases kind with
  | Item slot =>
    dsimp only
    step as ⟨o, ho⟩
    cases o with
    | none =>
      have ho' : movedTo moved.val slot.val = none := ho.symm
      simp [spec_ok, toKind, remapKind, ho']
    | some t =>
      have ho' : movedTo moved.val slot.val = some t.val := ho.symm
      simp [spec_ok, toKind, remapKind, ho']
  | DeletedItem slot =>
    dsimp only
    step as ⟨o, ho⟩
    cases o with
    | none =>
      have ho' : movedTo moved.val slot.val = none := ho.symm
      simp [spec_ok, toKind, remapKind, ho']
    | some t =>
      have ho' : movedTo moved.val slot.val = some t.val := ho.symm
      simp [spec_ok, toKind, remapKind, ho']
  | Gc => simp [spec_ok, toKind, remapKind]
  | Skip => simp [spec_ok, toKind, remapKind]

/-- The table names a new slot for the item of every item block. -/
def SlotsMoved (l : List client_blocks.BlockRefCore) (moved : List Std.U32) : Prop :=
  ∀ (p : Nat) (b : client_blocks.BlockRefCore) (s : Std.U32), l[p]? = some b →
    kindSlot b.kind = some s → ∃ t : Nat, movedTo moved s.val = some t

theorem slots_moved_loop_spec (cb : client_blocks.ClientBlocksCore)
    (cap head len : Std.Usize) (moved : Slice Std.U32) (i : Std.Usize)
    (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb) (hlen : len.val = countOf cb)
    (hinv : ∀ (p : Nat) (b : client_blocks.BlockRefCore) (s : Std.U32), p < i.val →
      (blocksOf cb)[p]? = some b → kindSlot b.kind = some s →
      ∃ t : Nat, movedTo moved.val s.val = some t) :
    client_blocks.ClientBlocksCore.slots_moved_loop cb cap head len moved i ⦃ r =>
      (r = true ↔ SlotsMoved (blocksOf cb) moved.val) ⦄ := by
  unfold client_blocks.ClientBlocksCore.slots_moved_loop
  have hcl := countOf_le cb
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  refine loop.spec_decr_nat
    (fun (j : Std.Usize) => len.val - j.val)
    (fun (j : Std.Usize) => ∀ (p : Nat) (b : client_blocks.BlockRefCore) (s : Std.U32),
      p < j.val → (blocksOf cb)[p]? = some b → kindSlot b.kind = some s →
      ∃ t : Nat, movedTo moved.val s.val = some t)
    (fun (r : Bool) => (r = true ↔ SlotsMoved (blocksOf cb) moved.val))
    _ i ?_ hinv
  intro j hj
  unfold client_blocks.ClientBlocksCore.slots_moved_loop.body
  by_cases hlt : j < len
  · simp only [hlt, ↓reduceIte]
    have hjl : j.val < countOf cb := by scalar_tac
    step as ⟨s1, hs1, hs1lt⟩
    step as ⟨w, hw⟩
    have hg : cb.buf.val[s1.val]? = some w := get?_at (by omega) hw
    have hb := block_at hcap hhead hjl hs1 hg
    step as ⟨bkc, hbkc⟩
    step as ⟨o, ho⟩
    cases o with
    | none =>
      dsimp only
      step as ⟨j1, hj1⟩
      have hj1v : j1.val = j.val + 1 := by scalar_tac
      refine ⟨?_, by omega⟩
      intro p b s hp hpb hs
      by_cases hpj : p = j.val
      · rw [hpj, hb] at hpb
        cases hpb
        rw [← hbkc, ← ho] at hs
        cases hs
      · exact hj p b s (by omega) hpb hs
    | some slot =>
      dsimp only
      step as ⟨o1, ho1⟩
      cases o1 with
      | none =>
        have hnone : movedTo moved.val slot.val = none := ho1.symm
        simp only [spec_ok]
        refine ⟨fun h => ?_, fun hall => ?_⟩
        · simp at h
        · exfalso
          obtain ⟨t, ht⟩ := hall j.val (blockOf w) slot hb (by rw [← hbkc, ← ho])
          rw [hnone] at ht
          cases ht
      | some t =>
        have hsome : movedTo moved.val slot.val = some t.val := ho1.symm
        dsimp only
        step as ⟨j1, hj1⟩
        have hj1v : j1.val = j.val + 1 := by scalar_tac
        refine ⟨?_, by omega⟩
        intro p b s hp hpb hs
        by_cases hpj : p = j.val
        · rw [hpj, hb] at hpb
          cases hpb
          rw [← hbkc, ← ho] at hs
          cases hs
          exact ⟨t.val, hsome⟩
        · exact hj p b s (by omega) hpb hs
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : countOf cb ≤ j.val := by scalar_tac
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    intro p b s hpb hs
    have hp := get?_lt hpb
    rw [length_blocksOf] at hp
    exact hj p b s (by omega) hpb hs

/-- `slots_moved` says whether the table names a new slot for every item of
the timeline. -/
theorem slots_moved_spec (cb : client_blocks.ClientBlocksCore) (cap head len : Std.Usize)
    (moved : Slice Std.U32) (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb)
    (hlen : len.val = countOf cb) :
    client_blocks.ClientBlocksCore.slots_moved cb cap head len moved ⦃ r =>
      (r = true ↔ SlotsMoved (blocksOf cb) moved.val) ⦄ := by
  unfold client_blocks.ClientBlocksCore.slots_moved
  refine slots_moved_loop_spec cb cap head len moved 0#usize hcap hhead hlen ?_
  intro p b s hp
  exfalso
  scalar_tac

/-- `rename_slots` on the model: a block with the kind the table gives it. -/
def remapBlock (moved : List Std.U32) (b : MBlock) : MBlock := ⟨b.clock, remapKind moved b.kind⟩

theorem rename_slots_loop_spec (cb0 cb : client_blocks.ClientBlocksCore)
    (cap head len : Std.Usize) (moved : Slice Std.U32) (i : Std.Usize)
    (hh : head.val ≤ cap.val) (hc : cap.val ≤ cb0.buf.val.length) (hlc : len.val ≤ cap.val)
    (hinv : cb.head = cb0.head ∧ cb.len = cb0.len ∧ cb.end_clock = cb0.end_clock ∧
      cb.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < cap.val →
        toBlock (blockAt cb.buf.val (slotOf cap.val head.val r)) =
          if r < i.val then
            remapBlock moved.val (toBlock (blockAt cb0.buf.val (slotOf cap.val head.val r)))
          else toBlock (blockAt cb0.buf.val (slotOf cap.val head.val r))) :
    client_blocks.ClientBlocksCore.rename_slots_loop cb cap head len moved i ⦃ cb' =>
      cb'.head = cb0.head ∧ cb'.len = cb0.len ∧ cb'.end_clock = cb0.end_clock ∧
      cb'.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < len.val →
        toBlock (blockAt cb'.buf.val (slotOf cap.val head.val r)) =
          remapBlock moved.val (toBlock (blockAt cb0.buf.val (slotOf cap.val head.val r))) ⦄ := by
  unfold client_blocks.ClientBlocksCore.rename_slots_loop
  refine loop.spec_decr_nat
    (fun ((_, j) : client_blocks.ClientBlocksCore × Std.Usize) => len.val - j.val)
    (fun ((c, j) : client_blocks.ClientBlocksCore × Std.Usize) =>
      c.head = cb0.head ∧ c.len = cb0.len ∧ c.end_clock = cb0.end_clock ∧
      c.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < cap.val →
        toBlock (blockAt c.buf.val (slotOf cap.val head.val r)) =
          if r < j.val then
            remapBlock moved.val (toBlock (blockAt cb0.buf.val (slotOf cap.val head.val r)))
          else toBlock (blockAt cb0.buf.val (slotOf cap.val head.val r)))
    (fun (c : client_blocks.ClientBlocksCore) =>
      c.head = cb0.head ∧ c.len = cb0.len ∧ c.end_clock = cb0.end_clock ∧
      c.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < len.val →
        toBlock (blockAt c.buf.val (slotOf cap.val head.val r)) =
          remapBlock moved.val (toBlock (blockAt cb0.buf.val (slotOf cap.val head.val r))))
    _ (cb, i) ?_ hinv
  intro ⟨c, j⟩ ⟨hch, hcl, hce, hcbl, hw⟩
  unfold client_blocks.ClientBlocksCore.rename_slots_loop.body
  simp only
  by_cases hlt : j < len
  · simp only [hlt, ↓reduceIte]
    have hjl : j.val < len.val := by scalar_tac
    step as ⟨slot, hslot, hslotlt⟩
    step as ⟨w, hwd⟩
    have hg : c.buf.val[slot.val]? = some w := get?_at (by omega) hwd
    step as ⟨block, hblock⟩
    step as ⟨kind, hkind⟩
    step as ⟨w1, hw1⟩
    step as ⟨old, back, hold, hback⟩
    step as ⟨j1, hj1⟩
    have hj1v : j1.val = j.val + 1 := by scalar_tac
    have hset : (back w1).val = c.buf.val.set slot.val w1 := by
      rw [hback]
      simp
    have hslots : ∀ r : Nat, r < cap.val → (back w1).val[slotOf cap.val head.val r]? =
        if r = j.val then some w1 else c.buf.val[slotOf cap.val head.val r]? := by
      intro r hr
      rw [hset, hslot]
      exact get?_set_slot _ w1 hh (by omega) (by omega) hr
    refine ⟨hch, hcl, hce, ?_, ?_, by omega⟩
    · show (back w1).val.length = cb0.buf.val.length
      rw [hset, List.length_set]
      exact hcbl
    · intro r hr
      show toBlock (blockAt (back w1).val (slotOf cap.val head.val r)) = _
      have hsr := hslots r hr
      by_cases hrj : r = j.val
      · rw [ite_eq_left hrj] at hsr
        rw [blockAt_of_get? hsr, hw1, ite_eq_left (by omega)]
        have hold' := hw j.val (by omega)
        rw [ite_eq_right (by omega), ← hslot, blockAt_of_get? hg] at hold'
        rw [hrj, ← hslot, ← hold', hblock]
        show (⟨(blockOf w).clock.val, toKind kind⟩ : MBlock) =
          ⟨(blockOf w).clock.val, remapKind moved.val (toKind (blockOf w).kind)⟩
        rw [hkind, hblock]
      · rw [ite_eq_right hrj] at hsr
        rw [blockAt_congr hsr, hw r hr, hj1v]
        by_cases hrl : r < j.val
        · rw [ite_eq_left hrl, ite_eq_left (by omega)]
        · rw [ite_eq_right hrl, ite_eq_right (by omega)]
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : len.val ≤ j.val := by scalar_tac
    refine ⟨hch, hcl, hce, hcbl, ?_⟩
    intro r hr
    rw [hw r (by omega), ite_eq_left (by omega)]

/-- `rename_slots` gives every block the kind the table gives it, where the
block is. -/
theorem rename_slots_spec (cb : client_blocks.ClientBlocksCore) (cap head len : Std.Usize)
    (moved : Slice Std.U32) (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb)
    (hlen : len.val = countOf cb) :
    client_blocks.ClientBlocksCore.rename_slots cb cap head len moved ⦃ cb' =>
      toBlocks cb' = (toBlocks cb).map (remapBlock moved.val) ∧
      cb'.end_clock = cb.end_clock ⦄ := by
  unfold client_blocks.ClientBlocksCore.rename_slots
  have hcl := countOf_le cb
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  have hinit : cb.head = cb.head ∧ cb.len = cb.len ∧ cb.end_clock = cb.end_clock ∧
      cb.buf.val.length = cb.buf.val.length ∧
      ∀ r : Nat, r < cap.val →
        toBlock (blockAt cb.buf.val (slotOf cap.val head.val r)) =
          if r < (0#usize : Std.Usize).val then
            remapBlock moved.val (toBlock (blockAt cb.buf.val (slotOf cap.val head.val r)))
          else toBlock (blockAt cb.buf.val (slotOf cap.val head.val r)) := by
    refine ⟨rfl, rfl, rfl, rfl, fun r _ => ?_⟩
    rw [ite_eq_right (by scalar_tac)]
  refine spec_mono (rename_slots_loop_spec cb cb cap head len moved 0#usize (by omega)
    (by omega) (by omega) hinit) ?_
  rintro cb' ⟨hh', hl', he', hbl', hw'⟩
  refine ⟨?_, he'⟩
  have hc' : capOf cb' = capOf cb := by
    unfold capOf
    rw [hbl']
  have hf' : firstOf cb' = firstOf cb := by
    unfold firstOf
    rw [hc', hh']
  have hn' : countOf cb' = countOf cb := by
    unfold countOf
    rw [hc', hl']
  apply ext_get?
  intro q
  rw [get?_map, toBlocks_get?, toBlocks_get?, get?_blocksOf, get?_blocksOf, hc', hf', hn']
  by_cases hq : q < countOf cb
  · rw [ite_eq_left hq, ite_eq_left hq]
    show some (toBlock (blockAt cb'.buf.val (slotOf (capOf cb) (firstOf cb) q))) = _
    rw [← hcap, ← hhead, hw' q (by omega)]
    rfl
  · rw [ite_eq_right hq, ite_eq_right hq]
    rfl

/-- What `remap_slots` guarantees: it either refuses and changes nothing, or
gives every item block the slot the table names for its item and leaves the
rest of every block as it is; and it accepts every table that names a slot for
every item of the timeline. -/
structure RemapPost (cb : client_blocks.ClientBlocksCore) (moved : Slice Std.U32)
    (r : core.result.Result Unit client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : r = core.result.Result.Ok () →
    SlotsMoved (blocksOf cb) moved.val ∧
      toBlocks cb' = (toBlocks cb).map (remapBlock moved.val) ∧
      cb'.end_clock = cb.end_clock
  accepts : SlotsMoved (blocksOf cb) moved.val → r = core.result.Result.Ok ()

@[step]
theorem remap_slots_spec (cb : client_blocks.ClientBlocksCore) (moved : Slice Std.U32) :
    client_blocks.ClientBlocksCore.remap_slots cb moved ⦃ r cb' =>
      RemapPost cb moved r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.remap_slots
  step as ⟨cap, head, len, hcap, hhead, hlen⟩
  step with slots_moved_spec cb cap head len moved hcap hhead hlen as ⟨b, hb⟩
  by_cases hs : b = true
  · simp only [hs, ↓reduceIte]
    step with rename_slots_spec cb cap head len moved hcap hhead hlen as ⟨cb1, hbl, he⟩
    exact ⟨(fun _ h => nomatch h), fun _ => ⟨hb.mp hs, hbl, he⟩, fun _ => rfl⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun h => nomatch h), fun hall => absurd (hb.mpr hall) hs⟩

/-- Changing the kinds of the blocks keeps the timeline. -/
theorem timelineWF_map {blocks : List MBlock} {stop : Nat} (h : TimelineWF blocks stop)
    {g : MBlock → MBlock} (hg : ∀ b, (g b).clock = b.clock) :
    TimelineWF (blocks.map g) stop := by
  have key : ∀ (p : Nat) (x : MBlock), (blocks.map g)[p]? = some x →
      ∃ x', blocks[p]? = some x' ∧ x.clock = x'.clock := by
    intro p x hx
    rw [get?_map] at hx
    cases hb : blocks[p]? with
    | none =>
      rw [hb] at hx
      cases hx
    | some x' =>
      rw [hb] at hx
      cases hx
      exact ⟨x', rfl, hg x'⟩
  constructor
  · intro p q x y hpq hx hy
    obtain ⟨x', hx', ex⟩ := key p x hx
    obtain ⟨y', hy', ey⟩ := key q y hy
    rw [ex, ey]
    exact h.sorted p q x' y' hpq hx' hy'
  · intro p x hx
    obtain ⟨x', hx', ex⟩ := key p x hx
    rw [ex]
    exact h.below p x' hx'

/-- `remap_slots` keeps I1 and the end of the timeline. -/
theorem remap_slots_wf {cb cb' : client_blocks.ClientBlocksCore} {moved : Slice Std.U32}
    {r : core.result.Result Unit client_blocks.StoreError} (hwf : WF cb)
    (h : RemapPost cb moved r cb') : WF cb' ∧ cb'.end_clock = cb.end_clock := by
  cases r with
  | Err e =>
    rw [h.err e rfl]
    exact ⟨hwf, rfl⟩
  | Ok u =>
    obtain ⟨_, hbl, he⟩ := h.ok rfl
    refine ⟨⟨?_⟩, he⟩
    rw [hbl, he]
    exact timelineWF_map hwf.timeline (fun _ => rfl)

/-- What `remap_slots` does to a block: it keeps its clock and whether it is
deleted, an item block names the slot the table gives for its item, and a
block that is no item block is the block it was. -/
theorem remap_slots_block {cb cb' : client_blocks.ClientBlocksCore} {moved : Slice Std.U32}
    (h : RemapPost cb moved (core.result.Result.Ok ()) cb') {p : Nat} {b : MBlock}
    (hb : (toBlocks cb)[p]? = some b) :
    ∃ b', (toBlocks cb')[p]? = some b' ∧ b'.clock = b.clock ∧ b'.kind.dead = b.kind.dead ∧
      (∀ s, b.kind.slot = some s →
        ∃ t, movedTo moved.val s = some t ∧ b'.kind.slot = some t) ∧
      (b.kind.slot = none → b' = b) := by
  obtain ⟨hall, hbl, _⟩ := h.ok rfl
  refine ⟨remapBlock moved.val b, ?_, rfl, remapKind_dead _ _, ?_, ?_⟩
  · simp [hbl, hb]
  · intro s hs
    rw [toBlocks_get?] at hb
    cases hc : (blocksOf cb)[p]? with
    | none =>
      rw [hc] at hb
      cases hb
    | some c =>
      rw [hc] at hb
      cases hb
      have hks : (kindSlot c.kind).map (fun i : Std.U32 => i.val) = some s := by
        rw [kindSlot_val]
        exact hs
      cases hk : kindSlot c.kind with
      | none =>
        rw [hk] at hks
        cases hks
      | some i =>
        rw [hk] at hks
        cases hks
        obtain ⟨t, ht⟩ := hall p c i hc hk
        exact ⟨t, ht, remapKind_slot _ hs ht⟩
  · intro hs
    cases b with
    | mk clock kind =>
      have hs' : kind.slot = none := hs
      show (⟨clock, remapKind moved.val kind⟩ : MBlock) = ⟨clock, kind⟩
      rw [remapKind_no_slot _ hs']

end YoctoCore.Properties.ClientBlocks
