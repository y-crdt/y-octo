/-
`y_octo_core::client_blocks`: the block timeline of one client.

Every function is total on every input (the Hoare triples below have no
precondition but the invariant where one is named), and `append`,
`split_boundary`, `merge_adjacent`, `mark_deleted` and `mark_gc` keep the
invariant I1 (`WF`): block starts strictly increase below `end_clock`, so no
block is empty and the blocks follow each other without a gap.
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.YataModel

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties.ListAux YoctoCore.Properties.YataModel

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace YoctoCore.Properties.ClientBlocks

/-! ## The model of a timeline -/

def toKind : client_blocks.BlockKindCore → MKind
  | .Item i => MKind.item i.val
  | .DeletedItem i => MKind.deleted i.val
  | .Gc => MKind.gc
  | .Skip => MKind.skip

def toBlock (b : client_blocks.BlockRefCore) : MBlock := ⟨b.clock.val, toKind b.kind⟩

def toBlocks (cb : client_blocks.ClientBlocksCore) : List MBlock := cb.blocks.val.map toBlock

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
    (toBlocks cb)[i]? = (cb.blocks.val[i]?).map toBlock :=
  get?_map _ _ _

theorem toBlocks_length (cb : client_blocks.ClientBlocksCore) :
    (toBlocks cb).length = cb.blocks.val.length := by
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
    {b : client_blocks.BlockRefCore} (h : cb.blocks.val[p + 1]? = some b) :
    endAt (toBlocks cb) cb.end_clock.val p = b.clock.val := by
  simp [endAt, toBlocks_get?, h, toBlock]

theorem endAt_toBlocks_none {cb : client_blocks.ClientBlocksCore} {p : Nat}
    (h : cb.blocks.val.length ≤ p + 1) :
    endAt (toBlocks cb) cb.end_clock.val p = cb.end_clock.val := by
  simp [endAt, toBlocks_get?, get?_none h]

theorem toBlocks_of_append {cb cb' : client_blocks.ClientBlocksCore}
    {b : client_blocks.BlockRefCore} (h : cb'.blocks.val = cb.blocks.val ++ [b]) :
    toBlocks cb' = toBlocks cb ++ [toBlock b] := by
  simp [toBlocks, h]

theorem toBlocks_of_insAt {cb cb' : client_blocks.ClientBlocksCore} {i : Nat}
    {b : client_blocks.BlockRefCore} (h : cb'.blocks.val = insAt cb.blocks.val i b) :
    toBlocks cb' = insAt (toBlocks cb) i (toBlock b) := by
  unfold toBlocks
  rw [h, map_insAt]

theorem toBlocks_of_set {cb cb' : client_blocks.ClientBlocksCore} {i : Nat}
    {b : client_blocks.BlockRefCore} (h : cb'.blocks.val = cb.blocks.val.set i b) :
    toBlocks cb' = upd (toBlocks cb) i (fun _ => toBlock b) := by
  unfold toBlocks
  rw [h, set_eq_upd, map_upd toBlock _ _ _ (fun _ => toBlock b) (fun _ => rfl)]

theorem toBlocks_of_delAt {cb cb' : client_blocks.ClientBlocksCore} {i : Nat}
    (h : cb'.blocks.val = delAt cb.blocks.val i) : toBlocks cb' = delAt (toBlocks cb) i := by
  unfold toBlocks
  rw [h, map_delAt]

/-! ## `new`, `len`, `is_empty`, `continues` -/

@[step]
theorem new_spec :
    client_blocks.ClientBlocksCore.new ⦃ cb => cb.blocks.val = [] ∧ cb.end_clock.val = 0 ∧ WF cb ⦄ := by
  unfold client_blocks.ClientBlocksCore.new
  simp only [spec_ok]
  refine ⟨by simp, by simp, ⟨⟨?_, ?_⟩⟩⟩
  · intro p q a b _ ha _
    simp [toBlocks] at ha
  · intro p a ha
    simp [toBlocks] at ha

@[step]
theorem len_spec (cb : client_blocks.ClientBlocksCore) :
    client_blocks.ClientBlocksCore.len cb ⦃ n => n.val = cb.blocks.val.length ⦄ := by
  unfold client_blocks.ClientBlocksCore.len
  simp [spec_ok]

@[step]
theorem is_empty_spec (cb : client_blocks.ClientBlocksCore) :
    client_blocks.ClientBlocksCore.is_empty cb ⦃ b => (b = true ↔ cb.blocks.val = []) ⦄ := by
  unfold client_blocks.ClientBlocksCore.is_empty alloc.vec.Vec.is_empty
  simp [spec_ok]

@[step]
theorem continues_spec (cb : client_blocks.ClientBlocksCore) (clock : Std.U64) :
    client_blocks.ClientBlocksCore.continues cb clock ⦃ b =>
      (b = true ↔ (cb.blocks.val = [] ∨ clock = cb.end_clock)) ⦄ := by
  unfold client_blocks.ClientBlocksCore.continues alloc.vec.Vec.is_empty
  by_cases he : cb.blocks.val = []
  · simp [spec_ok, he]
  · have hlen : ¬ cb.blocks.val.length = 0 := fun h => he (List.eq_nil_of_length_eq_zero h)
    simp [spec_ok, he, hlen]

/-! ## `append` -/

/-- What `append` guarantees: it either refuses the block and changes
nothing, or puts it at the end of the timeline; and it accepts every block of
at least one clock that continues the timeline and fits. -/
structure AppendPost (cb : client_blocks.ClientBlocksCore) (block : client_blocks.BlockRefCore)
    (len : Std.U64) (r : core.result.Result Unit client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : r = core.result.Result.Ok () →
    0 < len.val ∧ (cb.blocks.val = [] ∨ block.clock = cb.end_clock) ∧
      cb'.blocks.val = cb.blocks.val ++ [block] ∧ cb'.end_clock.val = block.clock.val + len.val
  accepts : 0 < len.val → (cb.blocks.val = [] ∨ block.clock = cb.end_clock) →
    block.clock.val + len.val ≤ Std.U64.max → cb.blocks.val.length < 4294967295 →
    r = core.result.Result.Ok ()

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
    step as ⟨b, hb⟩
    by_cases hcont : b = true
    · simp only [hcont, ↓reduceIte]
      have hc := hb.mp hcont
      have hMax : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
      have hRMax : Std.U64.rMax = 2 ^ 64 - 1 := by decide
      have hle : block.clock.val ≤ (core.num.U64.MAX : Std.U64).val := by rw [hMax]; scalar_tac
      step as ⟨i, hi⟩
      have hI : i.val = 2 ^ 64 - 1 - block.clock.val := by rw [hi, hRMax]
      by_cases hov : len > i
      · simp only [hov, ↓reduceIte, spec_ok, uncurry'_pair]
        refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ _ hfit _ => ?_⟩
        exfalso
        scalar_tac
      · simp only [hov, ↓reduceIte]
        by_cases hcap : alloc.vec.Vec.len cb.blocks >= client_blocks.MAX_BLOCKS
        · simp only [hcap, ↓reduceIte, spec_ok, uncurry'_pair]
          refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ _ _ hlt => ?_⟩
          exfalso
          simp [client_blocks.MAX_BLOCKS] at hcap
          scalar_tac
        · simp only [hcap, ↓reduceIte]
          have hlen : cb.blocks.val.length < Std.Usize.max := by
            simp [client_blocks.MAX_BLOCKS] at hcap
            scalar_tac
          step as ⟨v, hv⟩
          step as ⟨i2, hi2⟩
          exact ⟨(fun _ h => nomatch h), fun _ => ⟨hpos, hc, hv, by scalar_tac⟩, fun _ _ _ _ => rfl⟩
    · simp only [hcont, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun h => nomatch h), fun _ hc _ _ => absurd (hb.mpr hc) hcont⟩

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
      (o = none ∧ cb.blocks.val.length ≤ index.val) ∨
        ∃ (b : client_blocks.BlockRefCore) (e : Std.U64), o = some (b.clock, e) ∧
          cb.blocks.val[index.val]? = some b ∧
          e.val = endAt (toBlocks cb) cb.end_clock.val index.val ⦄ := by
  unfold client_blocks.ClientBlocksCore.range
  by_cases h : index >= alloc.vec.Vec.len cb.blocks
  · simp only [h, ↓reduceIte, spec_ok]
    left
    exact ⟨trivial, by scalar_tac⟩
  · simp only [h, ↓reduceIte]
    have hlt : index.val < cb.blocks.val.length := by scalar_tac
    step as ⟨brc, hbrc⟩
    step as ⟨next, hnext⟩
    have hb := get?_of_getElem hlt hbrc
    by_cases hn : next < alloc.vec.Vec.len cb.blocks
    · simp only [hn, ↓reduceIte]
      have hnlt : next.val < cb.blocks.val.length := by scalar_tac
      step as ⟨brc1, hbrc1⟩
      right
      have hb1 : cb.blocks.val[index.val + 1]? = some brc1 := by
        rw [← hnext]
        exact get?_of_getElem hnlt hbrc1
      exact ⟨brc, brc1.clock, rfl, hb, (endAt_toBlocks_some hb1).symm⟩
    · simp only [hn, ↓reduceIte, spec_ok]
      right
      exact ⟨brc, cb.end_clock, rfl, hb, (endAt_toBlocks_none (by scalar_tac)).symm⟩

/-- The partition point of a sorted timeline. -/
theorem find_loop_spec (v : alloc.vec.Vec client_blocks.BlockRefCore) (clock : Std.U64)
    (low high : Std.Usize)
    (hs : ∀ (p q : Nat) (a b : client_blocks.BlockRefCore), p < q → v.val[p]? = some a →
      v.val[q]? = some b → a.clock.val < b.clock.val)
    (hinv : low.val ≤ high.val ∧ high.val ≤ v.val.length ∧
      (∀ (j : Nat) (b : client_blocks.BlockRefCore), j < low.val → v.val[j]? = some b →
        b.clock.val ≤ clock.val) ∧
      (∀ (j : Nat) (b : client_blocks.BlockRefCore), high.val ≤ j → v.val[j]? = some b →
        clock.val < b.clock.val)) :
    client_blocks.ClientBlocksCore.find_loop v clock low high ⦃ r =>
      r.val ≤ v.val.length ∧
      (∀ (j : Nat) (b : client_blocks.BlockRefCore), j < r.val → v.val[j]? = some b →
        b.clock.val ≤ clock.val) ∧
      (∀ (j : Nat) (b : client_blocks.BlockRefCore), r.val ≤ j → v.val[j]? = some b →
        clock.val < b.clock.val) ⦄ := by
  unfold client_blocks.ClientBlocksCore.find_loop
  refine loop.spec_decr_nat
    (fun ((lo, hi) : Std.Usize × Std.Usize) => hi.val - lo.val)
    (fun ((lo, hi) : Std.Usize × Std.Usize) => lo.val ≤ hi.val ∧ hi.val ≤ v.val.length ∧
      (∀ (j : Nat) (b : client_blocks.BlockRefCore), j < lo.val → v.val[j]? = some b →
        b.clock.val ≤ clock.val) ∧
      (∀ (j : Nat) (b : client_blocks.BlockRefCore), hi.val ≤ j → v.val[j]? = some b →
        clock.val < b.clock.val))
    (fun (r : Std.Usize) => r.val ≤ v.val.length ∧
      (∀ (j : Nat) (b : client_blocks.BlockRefCore), j < r.val → v.val[j]? = some b →
        b.clock.val ≤ clock.val) ∧
      (∀ (j : Nat) (b : client_blocks.BlockRefCore), r.val ≤ j → v.val[j]? = some b →
        clock.val < b.clock.val))
    _ (low, high) ?_ hinv
  intro ⟨lo, hi⟩ ⟨hLoHi, hHiLen, hBelow, hAbove⟩
  unfold client_blocks.ClientBlocksCore.find_loop.body
  simp only
  by_cases hlt : lo < hi
  · simp only [hlt, ↓reduceIte]
    step as ⟨i, hi'⟩
    step as ⟨i1, hi1⟩
    step as ⟨mid, hmid⟩
    have hmidlt : mid.val < v.val.length := by scalar_tac
    have hmidlo : lo.val ≤ mid.val := by scalar_tac
    have hmidhi : mid.val < hi.val := by scalar_tac
    step as ⟨brc, hbrc⟩
    have hb := get?_of_getElem hmidlt hbrc
    by_cases hle : brc.clock <= clock
    · simp only [hle, ↓reduceIte]
      step as ⟨low1, hlow1⟩
      have hle' : brc.clock.val ≤ clock.val := by scalar_tac
      refine ⟨by scalar_tac, hHiLen, ?_, hAbove, by scalar_tac⟩
      intro j b hj hjb
      by_cases hjm : j = mid.val
      · rw [hjm, hb] at hjb
        cases hjb
        exact hle'
      · have hjlt : j < mid.val := by scalar_tac
        have := hs j mid.val b brc hjlt hjb hb
        omega
    · simp only [hle, ↓reduceIte, spec_ok]
      have hgt : clock.val < brc.clock.val := by scalar_tac
      refine ⟨hmidlo, by scalar_tac, hBelow, ?_, by scalar_tac⟩
      intro j b hj hjb
      by_cases hjm : j = mid.val
      · rw [hjm, hb] at hjb
        cases hjb
        exact hgt
      · have := hs mid.val j brc b (by omega) hb hjb
        omega
  · simp only [hlt, ↓reduceIte, spec_ok]
    have heq : lo.val = hi.val := by scalar_tac
    refine ⟨by scalar_tac, hBelow, ?_⟩
    intro j b hj
    exact hAbove j b (by omega)

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
    have hsorted : ∀ (p q : Nat) (a b : client_blocks.BlockRefCore), p < q →
        cb.blocks.val[p]? = some a → cb.blocks.val[q]? = some b → a.clock.val < b.clock.val := by
      intro p q a b hpq ha hb
      exact hwf.timeline.sorted p q (toBlock a) (toBlock b) hpq
        (by rw [toBlocks_get?, ha]; rfl) (by rw [toBlocks_get?, hb]; rfl)
    have hinit : (0#usize).val ≤ (alloc.vec.Vec.len cb.blocks).val ∧
        (alloc.vec.Vec.len cb.blocks).val ≤ cb.blocks.val.length ∧
        (∀ (j : Nat) (b : client_blocks.BlockRefCore), j < (0#usize).val →
          cb.blocks.val[j]? = some b → b.clock.val ≤ clock.val) ∧
        (∀ (j : Nat) (b : client_blocks.BlockRefCore), (alloc.vec.Vec.len cb.blocks).val ≤ j →
          cb.blocks.val[j]? = some b → clock.val < b.clock.val) := by
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_⟩
      · intro j b hj
        exfalso
        scalar_tac
      · intro j b hj hjb
        have := get?_lt hjb
        exfalso
        scalar_tac
    step with find_loop_spec cb.blocks clock 0#usize (alloc.vec.Vec.len cb.blocks) hsorted hinit
      as ⟨low, hlen, hbelow, habove⟩
    by_cases hz : low = 0#usize
    · have hz' : (low = 0#usize) = True := eq_true hz
      have h0 : low.val = 0 := by scalar_tac
      simp only [hz', ↓reduceIte, spec_ok]
      left
      refine ⟨trivial, ?_⟩
      rintro p ⟨a, ha, hle, _⟩
      rw [toBlocks_get?] at ha
      cases hb : cb.blocks.val[p]? with
      | none =>
        rw [hb] at ha
        cases ha
      | some b =>
        rw [hb] at ha
        cases ha
        have := habove p b (by omega) hb
        have hle' : b.clock.val ≤ clock.val := hle
        omega
    · simp only [hz, ↓reduceIte]
      have hpos : 0 < low.val := by scalar_tac
      step as ⟨i, hi⟩
      right
      refine ⟨i, rfl, ?_⟩
      have hilt : i.val < cb.blocks.val.length := by scalar_tac
      obtain ⟨b, hb⟩ := get?_some hilt
      refine ⟨toBlock b, by rw [toBlocks_get?, hb]; rfl, hbelow i.val b (by scalar_tac) hb, ?_⟩
      cases hn : cb.blocks.val[i.val + 1]? with
      | some nb =>
        rw [endAt_toBlocks_some hn]
        exact habove (i.val + 1) nb (by scalar_tac) hn
      | none =>
        rw [endAt_toBlocks_none (get?_none_le hn)]
        exact hclock

/-! ## `split_boundary` -/

structure SplitBoundaryPost (cb : client_blocks.ClientBlocksCore) (index : Std.Usize)
    (clock : Std.U64) (kind : client_blocks.BlockKindCore)
    (r : core.result.Result Unit client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : r = core.result.Result.Ok () →
    ∃ b, cb.blocks.val[index.val]? = some b ∧ b.clock.val < clock.val ∧
      clock.val < endAt (toBlocks cb) cb.end_clock.val index.val ∧
      cb'.blocks.val = insAt cb.blocks.val (index.val + 1)
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
        by_cases hcap : alloc.vec.Vec.len cb.blocks >= client_blocks.MAX_BLOCKS
        · simp only [hcap, ↓reduceIte, spec_ok, uncurry'_pair]
          exact ⟨fun _ _ => rfl, (fun h => nomatch h)⟩
        · simp only [hcap, ↓reduceIte]
          have hmax : cb.blocks.val.length < Std.Usize.max := by
            simp [client_blocks.MAX_BLOCKS] at hcap
            scalar_tac
          have hg1 : b.clock.val < clock.val := by scalar_tac
          have hg2 : clock.val < endAt (toBlocks cb) cb.end_clock.val index.val := by
            rw [← he]
            scalar_tac
          step as ⟨at1, hat⟩
          by_cases heq : at1 = alloc.vec.Vec.len cb.blocks
          · have heq' : (at1 = alloc.vec.Vec.len cb.blocks) = True := eq_true heq
            simp only [heq', ↓reduceIte]
            step as ⟨v, hv⟩
            refine ⟨(fun _ h => nomatch h), fun _ => ⟨b, hb, hg1, hg2, ?_, rfl⟩⟩
            have hidx : index.val + 1 = cb.blocks.val.length := by
              rw [← hat]
              simp [heq]
            rw [hidx, insAt_length]
            exact hv
          · simp only [heq, ↓reduceIte]
            have hatlt : at1.val < cb.blocks.val.length := by
              have hne : at1.val ≠ cb.blocks.val.length := by
                intro h
                apply heq
                apply UScalar.eq_of_val_eq
                simp [h]
              omega
            step as ⟨v, hv⟩
            refine ⟨(fun _ h => nomatch h), fun _ => ⟨b, hb, hg1, hg2, ?_, rfl⟩⟩
            rw [hv, hat, insertIdx_eq_insAt _ _ _ (by omega)]

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
    ∃ b i, cb.blocks.val[index.val]? = some b ∧ kindSlot b.kind = some i ∧
      cb'.blocks.val = cb.blocks.val.set index.val
        ({ clock := b.clock, kind := client_blocks.BlockKindCore.DeletedItem i } :
          client_blocks.BlockRefCore) ∧
      cb'.end_clock = cb.end_clock
  accepts : ∀ b e, cb.blocks.val[index.val]? = some b → r = core.result.Result.Err e →
    kindSlot b.kind = none

@[step]
theorem mark_deleted_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.mark_deleted cb index ⦃ r cb' =>
      MarkDeletedPost cb index r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.mark_deleted
  by_cases h : index >= alloc.vec.Vec.len cb.blocks
  · simp only [h, ↓reduceIte, spec_ok, uncurry'_pair]
    refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun b _ hb _ => ?_⟩
    have := get?_lt hb
    scalar_tac
  · simp only [h, ↓reduceIte]
    have hlt : index.val < cb.blocks.val.length := by scalar_tac
    step as ⟨brc, hbrc⟩
    have hb := get?_of_getElem hlt hbrc
    cases hk : brc.kind with
    | Item idx =>
      dsimp only
      step as ⟨brc1, back, h1, h2⟩
      refine ⟨(fun _ h => nomatch h), fun _ => ⟨brc, idx, hb, by rw [hk]; rfl, ?_, rfl⟩,
        (fun _ _ _ h => nomatch h)⟩
      rw [h2, h1, ← hbrc]
      simp
    | DeletedItem idx =>
      simp only [spec_ok, uncurry'_pair]
      refine ⟨(fun _ h => nomatch h), fun _ => ⟨brc, idx, hb, by rw [hk]; rfl, ?_, rfl⟩,
        (fun _ _ _ h => nomatch h)⟩
      have e : ({ clock := brc.clock, kind := client_blocks.BlockKindCore.DeletedItem idx } :
          client_blocks.BlockRefCore) = brc := by
        rw [← hk]
      rw [e]
      exact (set_eq_self hb).symm
    | Gc =>
      simp only [spec_ok, uncurry'_pair]
      refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun b _ hb' _ => ?_⟩
      rw [hb] at hb'
      cases hb'
      rw [hk]
      rfl
    | Skip =>
      simp only [spec_ok, uncurry'_pair]
      refine ⟨fun _ _ => rfl, (fun h => nomatch h), fun b _ hb' _ => ?_⟩
      rw [hb] at hb'
      cases hb'
      rw [hk]
      rfl

structure MarkGcPost (cb : client_blocks.ClientBlocksCore) (index : Std.Usize)
    (r : core.result.Result Std.U32 client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : ∀ i, r = core.result.Result.Ok i →
    ∃ b, cb.blocks.val[index.val]? = some b ∧
      b.kind = client_blocks.BlockKindCore.DeletedItem i ∧
      cb'.blocks.val = cb.blocks.val.set index.val
        ({ clock := b.clock, kind := client_blocks.BlockKindCore.Gc } :
          client_blocks.BlockRefCore) ∧
      cb'.end_clock = cb.end_clock

@[step]
theorem mark_gc_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.mark_gc cb index ⦃ r cb' => MarkGcPost cb index r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.mark_gc
  by_cases h : index >= alloc.vec.Vec.len cb.blocks
  · simp only [h, ↓reduceIte, spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun _ h => nomatch h)⟩
  · simp only [h, ↓reduceIte]
    have hlt : index.val < cb.blocks.val.length := by scalar_tac
    step as ⟨brc, hbrc⟩
    have hb := get?_of_getElem hlt hbrc
    cases hk : brc.kind with
    | Item idx =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun _ h => nomatch h)⟩
    | DeletedItem idx =>
      dsimp only
      step as ⟨brc1, back, h1, h2⟩
      refine ⟨(fun _ h => nomatch h), fun i h => ?_⟩
      cases h
      refine ⟨brc, hb, hk, ?_, rfl⟩
      rw [h2, h1, ← hbrc]
      simp
    | Gc =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun _ h => nomatch h)⟩
    | Skip =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun _ h => nomatch h)⟩

/-- Setting the kind of a block keeps I1 and the end of the timeline. -/
theorem set_kind_wf {cb cb' : client_blocks.ClientBlocksCore} {index : Nat}
    {b : client_blocks.BlockRefCore} {kind : client_blocks.BlockKindCore} (hwf : WF cb)
    (hb : cb.blocks.val[index]? = some b)
    (hbl : cb'.blocks.val = cb.blocks.val.set index
      ({ clock := b.clock, kind := kind } : client_blocks.BlockRefCore))
    (he : cb'.end_clock = cb.end_clock) : WF cb' := by
  constructor
  rw [toBlocks_of_set hbl, he]
  apply hwf.timeline.update
  intro a ha
  rw [toBlocks_get?, hb] at ha
  cases ha
  rfl

/-! ## `merge_adjacent` -/

theorem merge_loop0_spec (v : alloc.vec.Vec client_blocks.BlockRefCore) (next : Std.Usize)
    (out : alloc.vec.Vec client_blocks.BlockRefCore) (i : Std.Usize)
    (hinv : i.val ≤ next.val ∧ out.val = v.val.take i.val) (hn : next.val ≤ v.val.length) :
    client_blocks.ClientBlocksCore.merge_adjacent_loop0 v next out i ⦃ r =>
      r.val = v.val.take next.val ⦄ := by
  unfold client_blocks.ClientBlocksCore.merge_adjacent_loop0
  refine loop.spec_decr_nat
    (fun ((_, j) : alloc.vec.Vec client_blocks.BlockRefCore × Std.Usize) => next.val - j.val)
    (fun ((o, j) : alloc.vec.Vec client_blocks.BlockRefCore × Std.Usize) =>
      j.val ≤ next.val ∧ o.val = v.val.take j.val)
    (fun (r : alloc.vec.Vec client_blocks.BlockRefCore) => r.val = v.val.take next.val)
    _ (out, i) ?_ hinv
  intro ⟨o, j⟩ ⟨hj, ho⟩
  unfold client_blocks.ClientBlocksCore.merge_adjacent_loop0.body
  simp only
  by_cases hlt : j < next
  · simp only [hlt, ↓reduceIte]
    have hjl : j.val < v.val.length := by scalar_tac
    step as ⟨brc, hbrc⟩
    have hb := get?_of_getElem hjl hbrc
    have hol : o.val.length < Std.Usize.max := by
      have := congrArg List.length ho
      rw [List.length_take] at this
      scalar_tac
    step as ⟨o1, ho1⟩
    step as ⟨j1, hj1⟩
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [ho1, ho, hj1, take_succ_get hb]
  · simp only [hlt, ↓reduceIte, spec_ok]
    have heq : j.val = next.val := by scalar_tac
    rw [ho, heq]

theorem merge_loop1_spec (v out : alloc.vec.Vec client_blocks.BlockRefCore) (j : Std.Usize)
    (total : List client_blocks.BlockRefCore) (hinv : out.val ++ v.val.drop j.val = total)
    (ht : total.length ≤ Std.Usize.max) :
    client_blocks.ClientBlocksCore.merge_adjacent_loop1 v out j ⦃ r => r.val = total ⦄ := by
  unfold client_blocks.ClientBlocksCore.merge_adjacent_loop1
  refine loop.spec_decr_nat
    (fun ((_, k) : alloc.vec.Vec client_blocks.BlockRefCore × Std.Usize) =>
      v.val.length - k.val)
    (fun ((o, k) : alloc.vec.Vec client_blocks.BlockRefCore × Std.Usize) =>
      o.val ++ v.val.drop k.val = total)
    (fun (r : alloc.vec.Vec client_blocks.BlockRefCore) => r.val = total)
    _ (out, j) ?_ hinv
  intro ⟨o, k⟩ ho
  unfold client_blocks.ClientBlocksCore.merge_adjacent_loop1.body
  simp only
  by_cases hlt : k < alloc.vec.Vec.len v
  · simp only [hlt, ↓reduceIte]
    have hkl : k.val < v.val.length := by scalar_tac
    step as ⟨brc, hbrc⟩
    have hb := get?_of_getElem hkl hbrc
    have hdrop := drop_eq_cons_get hb
    have hol : o.val.length < Std.Usize.max := by
      have := congrArg List.length ho
      rw [hdrop, List.length_append, List.length_cons] at this
      scalar_tac
    step as ⟨o1, ho1⟩
    step as ⟨k1, hk1⟩
    refine ⟨?_, by scalar_tac⟩
    rw [ho1, hk1, ← ho, hdrop]
    simp
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : v.val.length ≤ k.val := by scalar_tac
    rw [← ho, List.drop_eq_nil_of_le hge]
    simp

structure MergePost (cb : client_blocks.ClientBlocksCore) (index : Std.Usize)
    (r : core.result.Result Unit client_blocks.StoreError)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → cb' = cb
  ok : r = core.result.Result.Ok () →
    ∃ a b, cb.blocks.val[index.val]? = some a ∧ cb.blocks.val[index.val + 1]? = some b ∧
      sameKind a.kind b.kind = true ∧ cb'.blocks.val = delAt cb.blocks.val (index.val + 1) ∧
      cb'.end_clock = cb.end_clock

@[step]
theorem merge_adjacent_spec (cb : client_blocks.ClientBlocksCore) (index : Std.Usize) :
    client_blocks.ClientBlocksCore.merge_adjacent cb index ⦃ r cb' =>
      MergePost cb index r cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.merge_adjacent
  by_cases h : index >= alloc.vec.Vec.len cb.blocks
  · simp only [h, ↓reduceIte, spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun h => nomatch h)⟩
  · simp only [h, ↓reduceIte]
    have hlt : index.val < cb.blocks.val.length := by scalar_tac
    step as ⟨next, hnext⟩
    by_cases hn : next >= alloc.vec.Vec.len cb.blocks
    · simp only [hn, ↓reduceIte, spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun h => nomatch h)⟩
    · simp only [hn, ↓reduceIte]
      have hnlt : next.val < cb.blocks.val.length := by scalar_tac
      step as ⟨brc, hbrc⟩
      step as ⟨brc1, hbrc1⟩
      have ha := get?_of_getElem hlt hbrc
      have hb := get?_of_getElem hnlt hbrc1
      step as ⟨same, hsame⟩
      by_cases hs : same = true
      · simp only [hs, ↓reduceIte]
        have hinit : (0#usize).val ≤ next.val ∧
            (alloc.vec.Vec.new client_blocks.BlockRefCore).val =
              cb.blocks.val.take (0#usize).val := by
          refine ⟨by scalar_tac, ?_⟩
          simp
        step with merge_loop0_spec cb.blocks next (alloc.vec.Vec.new client_blocks.BlockRefCore)
          0#usize hinit (by omega) as ⟨out, hout⟩
        step as ⟨j, hj⟩
        have htotal : (cb.blocks.val.take next.val ++ cb.blocks.val.drop (next.val + 1)).length ≤
            Std.Usize.max := by
          rw [List.length_append, List.length_take, List.length_drop]
          scalar_tac
        have hjoin : out.val ++ cb.blocks.val.drop j.val =
            cb.blocks.val.take next.val ++ cb.blocks.val.drop (next.val + 1) := by
          rw [hout, hj]
        step with merge_loop1_spec cb.blocks out j _ hjoin htotal as ⟨out1, hout1⟩
        refine ⟨(fun _ h => nomatch h), fun _ => ⟨brc, brc1, ha, by rw [← hnext]; exact hb,
          by rw [← hsame]; exact hs, ?_, rfl⟩⟩
        rw [hout1, delAt_eq, hnext]
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
        exact ⟨fun _ _ => rfl, (fun h => nomatch h)⟩

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

end YoctoCore.Properties.ClientBlocks
