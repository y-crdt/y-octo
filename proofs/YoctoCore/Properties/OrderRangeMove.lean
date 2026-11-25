import Aeneas
import YoctoCore.Code.Funs
import YoctoCore.Properties.OrderRangeRing

namespace YoctoCore.Properties.OrderRangeRing

/-- The original index supplying a slot after a memmove. -/
def movedIndex (src dst n j : Nat) :=
  if dst ≤ j ∧ j < dst+n then src+(j-dst) else j

theorem moved_empty (src dst j : Nat) : movedIndex src dst 0 j = j := by
  simp [movedIndex]

theorem moved_self (i n j : Nat) : movedIndex i i n j = j := by
  unfold movedIndex
  split <;> omega

theorem moved_forward (src dst done chunk j : Nat) (direction : dst ≤ src) :
    movedIndex src dst done (movedIndex (src+done) (dst+done) chunk j) =
      movedIndex src dst (done+chunk) j := by
  unfold movedIndex
  split <;> split <;> split <;> omega

theorem moved_backward (src dst n left chunk j : Nat) (direction : src ≤ dst)
    (fits : left + chunk ≤ n) :
    movedIndex (src+left+chunk) (dst+left+chunk) (n-left-chunk)
        (movedIndex (src+left) (dst+left) chunk j) =
      movedIndex (src+left) (dst+left) (n-left) j := by
  unfold movedIndex
  split <;> split <;> split <;> omega

/-- An offset within an unbroken physical slice adds to the physical position. -/
theorem position_offset {cap head base k : Nat} (baseValid : base+k < cap)
    (linear : position cap head base+k < cap) :
    position cap head (base+k) = position cap head base+k := by
  unfold position at *
  split <;> split <;> split at linear <;> omega

/-- A backward copy starts at the end position minus the contiguous chunk.
    The bound on the chunk prevents it from crossing physical slot zero. -/
theorem position_before_end {cap head start remaining chunk : Nat}
    (hh : head < cap) (bound : start + remaining ≤ cap)
    (positive : 0 < chunk) (live : chunk ≤ remaining)
    (contiguous : chunk ≤ position cap head (start + (remaining-1)) + 1) :
    position cap head (start + (remaining-chunk)) =
      position cap head (start + (remaining-1)) + 1 - chunk := by
  unfold position at *
  split <;> split <;> split at contiguous <;> omega

/-- Translating a physical copy into the logical coordinates of the ring. -/
theorem position_moved {cap head src dst n i : Nat} (h : head < cap)
    (si : src+n ≤ cap) (di : dst+n ≤ cap) (ix : i < cap)
    (sc : position cap head src + n ≤ cap) (dc : position cap head dst + n ≤ cap) :
    movedIndex (position cap head src) (position cap head dst) n (position cap head i) =
      position cap head (movedIndex src dst n i) := by
  by_cases hit : dst ≤ i ∧ i < dst+n
  · have klt : i-dst < n := by omega
    have eq : dst + (i-dst) = i := by omega
    have pos := position_offset (cap := cap) (head := head) (base := dst) (k := i-dst)
      (by omega) (by omega)
    rw [eq] at pos
    have phit : position cap head dst ≤ position cap head i ∧
        position cap head i < position cap head dst+n := by omega
    simp only [movedIndex,hit,phit,↓reduceIte]
    have k : position cap head i - position cap head dst = i-dst := by omega
    rw [k]
    exact (position_offset (by omega) (by omega)).symm
  · have outside : ¬(position cap head dst ≤ position cap head i ∧
        position cap head i < position cap head dst + n) := by
      rintro ⟨lo,hi⟩
      let k := position cap head i - position cap head dst
      have kn : k < n := by dsimp [k]; omega
      have eq := position_offset (cap := cap) (head := head) (base := dst) (k := k)
        (by omega) (by omega)
      have same : position cap head (dst+k) = position cap head i := by rw [eq]; dsimp [k]; omega
      have value := position_injective h (by omega : dst+k < cap) ix same
      exact hit (by omega)
    simp only [movedIndex,hit,outside,↓reduceIte]

end YoctoCore.Properties.OrderRangeRing


open Aeneas Aeneas.Std
namespace YoctoCore.Properties.OrderRangeRing

/-- Reading a destination after copying a slice reads its original source. -/
theorem copied_slice_lookup (l : List α) (src dst n j : Nat)
    (source : src + n ≤ l.length) (destination : dst + n ≤ l.length) :
    (l.setSlice! dst (l.slice src (src+n)))[j]? = l[movedIndex src dst n j]? := by
  have count : (l.slice src (src+n)).length = n := by rw [List.slice_length]; omega
  by_cases inside : dst ≤ j ∧ j < dst+n
  · rw [movedIndex, if_pos inside, List.setSlice!_getElem?_middle]
    · exact List.getElem?_slice _ _ _ _ ⟨source,by omega⟩
    · omega
  · rw [movedIndex, if_neg inside, List.setSlice!_getElem?_same]
    omega

/-- Lowering a segment copy to two non-overlapping borrows preserves the same slot map. -/
theorem copied_to_right (l : List α) (src dst n j : Nat)
    (separate : src+n ≤ dst) (dest : dst+n ≤ l.length) :
    (l.take dst ++ (l.drop dst).setSlice! 0 ((l.take dst).slice src (src+n)))[j]? =
      l[movedIndex src dst n j]? := by
  have leftLen : (l.take dst).length = dst := by rw [List.length_take]; omega
  have original : (l.take dst).slice src (src+n) = l.slice src (src+n) := by
    apply List.ext_getElem?
    intro i
    by_cases h : i < n
    · rw [List.getElem?_slice _ _ _ _ ⟨by omega,by omega⟩,
        List.getElem?_slice _ _ _ _ ⟨by omega,by omega⟩,List.getElem?_take]
      simp [show src+i < dst by omega]
    · apply Eq.trans (List.getElem?_eq_none (by rw [List.slice_length]; omega))
      exact (List.getElem?_eq_none (by rw [List.slice_length]; omega)).symm
  rw [original]
  have count : (l.slice src (src+n)).length = n := by rw [List.slice_length]; omega
  by_cases left : j < dst
  · rw [List.getElem?_append_left (by omega),List.getElem?_take]
    simp [left,movedIndex,Nat.not_le.mpr left]
  · rw [List.getElem?_append_right (by omega),leftLen]
    by_cases within : j < dst+n
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by simp only [List.length_drop,count]; omega),
        movedIndex,if_pos ⟨by omega,within⟩,Nat.sub_zero]
      exact List.getElem?_slice _ _ _ _ ⟨by omega,by omega⟩
    · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega), List.getElem?_drop, movedIndex, if_neg (by omega)]
      congr 1; omega

theorem copied_to_left (l : List α) (src dst n j : Nat)
    (separate : dst+n ≤ src) (source : src+n ≤ l.length) :
    ((l.take src).setSlice! dst ((l.drop src).take n) ++ l.drop src)[j]? =
      l[movedIndex src dst n j]? := by
  have cut : (l.take src).length = src := by rw [List.length_take]; omega
  have length : ((l.take src).setSlice! dst ((l.drop src).take n)).length = src := by
    rw [List.length_setSlice!,cut]
  have copied : ((l.drop src).take n).length = n := by
    rw [List.length_take,List.length_drop]; omega
  by_cases left : j < src
  · rw [List.getElem?_append_left (by omega)]
    by_cases within : dst ≤ j ∧ j < dst+n
    · rw [List.setSlice!_getElem?_middle _ _ _ _ (by omega),List.getElem?_take,
        if_pos (by omega),List.getElem?_drop,movedIndex,if_pos within]
    · rw [List.setSlice!_getElem?_same _ _ _ _ (by omega),List.getElem?_take,
        if_pos left,movedIndex,if_neg within]
  · rw [List.getElem?_append_right (by omega),length,List.getElem?_drop,movedIndex,if_neg (by omega)]
    congr 1; omega

end YoctoCore.Properties.OrderRangeRing
namespace YoctoCore.Properties.OrderRangeRing

/-- Logical slots read from the original buffer after the previous chunks. -/
def chunkSource (src dst count remaining j : Nat) : Nat :=
  if dst < src then movedIndex src dst (count-remaining) j
  else movedIndex (src+remaining) (dst+remaining) (count-remaining) j

theorem chunkSource_initial (src dst count j : Nat) :
    chunkSource src dst count count j = j := by
  simp [chunkSource,moved_empty]

theorem chunkSource_final (src dst count j : Nat) :
    chunkSource src dst count 0 j = movedIndex src dst count j := by
  simp [chunkSource]

theorem movedIndex_bound {cap src dst n j : Nat} (srcFits : src+n ≤ cap) (index : j < cap) :
    movedIndex src dst n j < cap := by
  unfold movedIndex
  split <;> omega

/-- A forward copy extends the initialized prefix. A backward copy extends
    the initialized suffix. In both cases the source comes from the same
    original slot as a single memmove over the entire logical interval. -/
theorem chunkSource_step (src dst count remaining n j : Nat)
    (live : remaining ≤ count) (fits : n ≤ remaining) :
    let offset := if dst < src then count-remaining else remaining-n
    chunkSource src dst count remaining (movedIndex (src+offset) (dst+offset) n j) =
      chunkSource src dst count (remaining-n) j := by
  dsimp only
  by_cases forward : dst < src
  · simp only [chunkSource,if_pos forward]
    rw [moved_forward _ _ _ _ _ (Nat.le_of_lt forward)]
    congr 1
    omega
  · simp only [chunkSource,if_neg forward]
    have rem : remaining - n + n = remaining := by omega
    have completed : count - (remaining-n) - n = count-remaining := by omega
    have glued := moved_backward src dst count (remaining-n) n j
      (by omega) (by omega)
    simpa only [Nat.add_assoc, rem, completed] using glued

end YoctoCore.Properties.OrderRangeRing

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
namespace YoctoCore.Properties.OrderRange
open OrderRangeRing

/-- A bounded snapshot copies from the original source, even if the ranges overlap. -/
private theorem move_block_spec (buf : Slice order_range.ClockRange) (src dst n : Usize)
    (size : n.val ≤ 512) (srcFits : src.val+n.val ≤ buf.length)
    (dstFits : dst.val+n.val ≤ buf.length) :
    order_range.move_block buf src dst n ⦃ out => out.length = buf.length ∧
      ∀ j, out.val[j]? = buf.val[movedIndex src.val dst.val n.val j]? ⦄ := by
  unfold order_range.move_block
  step as ⟨active,_,_,activeLen,_⟩
  step as ⟨srcEnd,hs⟩
  step as ⟨source,sourceVal,sourceLen⟩
  step as ⟨snapshot,same⟩ <;> try scalar_tac
  subst snapshot
  step as ⟨dstEnd,hd⟩
  step as ⟨target,write,_,targetLen,install⟩
  step as ⟨copied,same⟩ <;> try scalar_tac
  subst copied
  simp only [spec_ok,install, Slice.setSlice!_length, true_and, Slice.setSlice!_val, sourceVal, hs]
  intro j
  exact copied_slice_lookup _ _ _ _ j srcFits dstFits

private def ChunkState (buf out : Slice order_range.ClockRange) (src dst count remaining : Nat) :=
  out.length = buf.length ∧ remaining ≤ count ∧ ∀ j,
    out.val[j]? = buf.val[chunkSource src dst count remaining j]?

private theorem move_segment_loop_spec (buf : Slice order_range.ClockRange) (src dst count : Usize)
    (srcFits : src.val+count.val ≤ buf.length) (dstFits : dst.val+count.val ≤ buf.length) :
    order_range.move_segment_loop buf src dst count count ⦃ (out,left) =>
      left.val ≤ 512 ∧ ChunkState buf out src.val dst.val count.val left.val ⦄ := by
  let inv : Slice order_range.ClockRange × Usize → Prop := fun (out,left) =>
    ChunkState buf out src.val dst.val count.val left.val
  have block : order_range.MOVE_BLOCK.val = 512 := by unfold order_range.MOVE_BLOCK; decide
  unfold order_range.move_segment_loop
  refine loop.spec_decr_nat (fun (_,left) => left.val) inv _ _ _ ?_ ?_
  · intro ⟨v,left⟩ st
    obtain ⟨len,le,read⟩ := st
    unfold order_range.move_segment_loop.body
    simp only
    by_cases live : left > order_range.MOVE_BLOCK
    · simp only [live,↓reduceIte]
      have positive : 512 < left.val := by scalar_tac
      have advance (off : Usize)
          (hOff : src.val = dst.val ∨ off.val = if dst.val < src.val then count.val-left.val else left.val-512)
          (bounds : off.val+512 ≤ count.val) :
          (do let f ← src+off
              let t ← dst+off
              let v1 ← order_range.move_block v f t order_range.MOVE_BLOCK
              let next ← left-order_range.MOVE_BLOCK
              ok (cont (v1,next) : ControlFlow (Slice order_range.ClockRange × Usize)
                (Slice order_range.ClockRange × Usize))) ⦃ x => match x with
            | done p => p.2.val ≤ 512 ∧ ChunkState buf p.1 src.val dst.val count.val p.2.val
            | cont p => inv p ∧ p.2.val < left.val ⦄ := by
        step as ⟨f,hf⟩
        step as ⟨t,ht⟩
        step with move_block_spec v f t order_range.MOVE_BLOCK (by omega)
          (by omega) (by omega) as ⟨w,sz,written⟩
        step as ⟨next,hn⟩
        refine ⟨⟨sz.trans len,by omega,?_⟩,by omega⟩
        intro j
        rw [written,read,hf,ht,hn,block]
        rcases hOff with same | offset
        · simp [same,chunkSource,moved_self]
        rw [offset]
        exact congrArg (fun k => buf.val[k]?) (chunkSource_step _ _ _ _ _ _ le (by omega))
      by_cases dir : src < dst
      · simp only [dir,↓reduceIte]
        step as ⟨off,ho⟩
        have offVal : off.val = left.val-512 := by simpa only [block] using ho
        apply spec_mono (advance off (Or.inr (by simpa only [if_neg (show ¬dst.val < src.val by scalar_tac)] using offVal)) (by omega))
        intro z h
        cases z <;> exact h
      · simp only [dir,↓reduceIte]
        step as ⟨off,ho⟩
        have side : src.val = dst.val ∨ off.val = (if dst.val < src.val then count.val-left.val else left.val-512) := by
          by_cases same : src.val = dst.val
          · exact Or.inl same
          · exact Or.inr (by simpa only [if_pos (show dst.val < src.val by scalar_tac)] using ho)
        apply spec_mono (advance off side (by omega))
        intro z h
        cases z <;> exact h
    · simp only [live,↓reduceIte,spec_ok]
      exact ⟨by scalar_tac,len,le,read⟩
  · exact ⟨rfl,le_rfl,fun j => by rw [chunkSource_initial]⟩


/-- Moving one contiguous physical interval reads each affected slot from the
    corresponding original index. The two disjoint branches split the slice,
    while the overlapping branch composes bounded snapshots. -/
theorem move_segment_spec (buf : Slice order_range.ClockRange) (src dst count : Usize)
    (srcFits : src.val+count.val ≤ buf.length) (dstFits : dst.val+count.val ≤ buf.length) :
    order_range.move_segment buf src dst count ⦃ out => out.length = buf.length ∧
      ∀ j, out.val[j]? = buf.val[movedIndex src.val dst.val count.val j]? ⦄ := by
  unfold order_range.move_segment
  step as ⟨srcEnd,hs⟩
  by_cases right : srcEnd ≤ dst
  · simp only [right,↓reduceIte]
    step as ⟨l,r,join,ll,rl,lv,rv,finish⟩
    step as ⟨target,write,_,targetLen,set⟩
    step as ⟨source,sourceVal,sourceLen⟩
    step as ⟨copied,same⟩ <;> try scalar_tac
    subst copied
    have len : (write source).length = buf.length-dst.val := by
      change (write source).val.length = _
      rw [set,List.length_setSlice!]; exact rl
    have ⟨val,sz⟩ := finish l (write source) ll len
    refine ⟨sz,fun j => ?_⟩
    rw [val,set,sourceVal,lv,rv,hs]
    exact copied_to_right _ _ _ _ _ (by scalar_tac) dstFits
  · simp only [right,↓reduceIte]
    step as ⟨dstEnd,hd⟩
    by_cases left : dstEnd ≤ src
    · simp only [left,↓reduceIte]
      step as ⟨l,r,join,ll,rl,lv,rv,finish⟩
      step as ⟨target,write,_,targetLen,set⟩
      step as ⟨source,sourceVal,sourceLen⟩
      step as ⟨copied,same⟩ <;> try scalar_tac
      subst copied
      have len : (write source).length = src.val := by simpa only [set,Slice.setSlice!_length] using ll
      have ⟨val,sz⟩ := finish (write source) r len rl
      refine ⟨sz,fun j => ?_⟩
      rw [val,set,Slice.setSlice!_val,sourceVal,lv,rv]
      simpa [List.slice] using copied_to_left buf.val src.val dst.val count.val j (by scalar_tac) srcFits
    · simp only [left,↓reduceIte]
      step with move_segment_loop_spec buf src dst count srcFits dstFits as ⟨v,remaining,small,st⟩
      obtain ⟨size,live,lookup⟩ := st
      let finish (off : Usize)
          (offset : src.val = dst.val ∨ off.val = if dst.val < src.val then count.val-remaining.val else 0)
          (fits : off.val+remaining.val ≤ count.val) :
          (do let f ← src + off
              let t ← dst + off
              order_range.move_block v f t remaining) ⦃ w => w.length = buf.length ∧
            ∀ j, w.val[j]? = buf.val[movedIndex src.val dst.val count.val j]? ⦄ := by
        step as ⟨f,hf⟩
        step as ⟨t,ht⟩
        refine spec_mono (move_block_spec v f t remaining small (by omega) (by omega)) ?_
        rintro w ⟨wl,copy⟩
        refine ⟨wl.trans size,fun j => ?_⟩
        rw [copy,lookup,hf,ht]
        rcases offset with same | offEq
        · simp [same,chunkSource,moved_self]
        rw [offEq]
        have eq := chunkSource_step src.val dst.val count.val remaining.val remaining.val j live (Nat.le_refl _)
        simpa only [Nat.sub_self,chunkSource_final] using congrArg (fun k => buf.val[k]?) eq
      by_cases back : src < dst
      · simp only [back,↓reduceIte,bind_ok]
        exact finish 0#usize (Or.inr (by simp [show ¬dst.val < src.val by scalar_tac])) (by scalar_tac)
      · simp only [back,↓reduceIte]
        step as ⟨off,ho⟩
        apply finish off _ (by omega)
        by_cases same : src.val = dst.val
        · exact Or.inl same
        · exact Or.inr (by simpa only [if_pos (show dst.val < src.val by scalar_tac)] using ho)

end YoctoCore.Properties.OrderRange
