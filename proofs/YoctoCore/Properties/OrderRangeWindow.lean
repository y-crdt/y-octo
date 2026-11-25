import YoctoCore.Properties.OrderRangeNormalize

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.OrderRange

/-- The interval between the two cursors has been initialized from the
    incoming array. Positions on either side still hold their original values. -/
private def Copied (before after src : List order_range.ClockRange) (lo a n : Nat) : Prop :=
  before.length = after.length ∧ ∀ j, after[j]? =
    if lo ≤ j ∧ j < lo+n then src[a+(j-lo)]? else before[j]?

private theorem copied_zero (l src : List order_range.ClockRange) (lo a : Nat) :
    Copied l l src lo a 0 := by
  refine ⟨rfl, fun j => ?_⟩
  simp

private theorem copied_succ (l out src : List order_range.ClockRange) (lo a n : Nat)
    (h : Copied l out src lo a n) (dst : lo+n < out.length) (index : a+n < src.length) :
    Copied l (out.set (lo+n) src[a+n]) src lo a (n+1) := by
  refine ⟨by simpa using h.1,fun j => ?_⟩
  by_cases here : j = lo+n
  · subst j
    have on : lo ≤ lo+n ∧ lo+n < lo+(n+1) := by omega
    simp [on,dst,index]
  · have same : (lo ≤ j ∧ j < lo+(n+1)) ↔ (lo ≤ j ∧ j < lo+n) := by omega
    simp [Ne.symm here,same,h.2 j]

private theorem copy_incoming_spec (v : order_range.Ring)
    (incoming : order_range.OrderRange) (lo a b : Std.Usize)
    (hw : ringWF v 0) (hc : storageWF incoming) (ord : a.val ≤ b.val)
    (srcBound : b.val ≤ (toList incoming).length) (dstBound : lo.val+(b.val-a.val) ≤ v.len.val) :
    order_range.Ring.merge_window_loop0 v lo incoming a b a ⦃ w =>
      ringWF w 0 ∧ Copied (ringList v) (ringList w) (toList incoming) lo.val a.val (b.val-a.val) ⦄ := by
  let src := toList incoming
  let first := ringList v
  let inv : order_range.Ring × Std.Usize → Prop := fun (w,i) =>
    ringWF w 0 ∧ a.val ≤ i.val ∧ i.val ≤ b.val ∧ Copied first (ringList w) src lo.val a.val (i.val-a.val)
  unfold order_range.Ring.merge_window_loop0
  refine loop.spec_decr_nat (fun (_,i) => b.val-i.val) inv _ _ _ ?_ ?_
  · intro ⟨w,i⟩ ⟨wf,low,high,copied⟩
    unfold order_range.Ring.merge_window_loop0.body
    simp only
    by_cases live : i < b
    · simp only [live, ↓reduceIte]
      have lt : i.val < b.val := by scalar_tac
      have len := copied.1
      have vw : v.len.val = w.len.val := by
        change (ringList v).length = (ringList w).length at len
        simpa only [ringList_length v hw, ringList_length w wf] using len
      step as ⟨offset,ofVal⟩
      step as ⟨k,kv⟩
      step with at_spec incoming i hc (by omega) as ⟨x,hx⟩
      step with ring_set_list_spec w k x wf (by omega) as ⟨u,uw,list⟩
      step as ⟨j,hj⟩
      have off : a.val+(i.val-a.val) = i.val := by omega
      have dst : lo.val+(i.val-a.val) < (ringList w).length := by rw [ringList_length w wf]; omega
      have installed := copied_succ first (ringList w) src lo.val a.val (i.val-a.val) copied dst (by dsimp [src]; omega)
      refine ⟨⟨uw,by omega,by omega,?_⟩,by omega⟩
      rw [list,kv,ofVal,hx,show j.val-a.val = i.val-a.val+1 by omega]
      simpa only [off,src] using installed
    · have equal : i.val = b.val := by scalar_tac
      simp only [live,↓reduceIte,spec_ok]
      exact ⟨wf,by simpa only [equal] using copied⟩
  · exact ⟨hw,Nat.le_refl _,ord,by simpa using copied_zero first src lo.val a.val⟩

/-- The destination starts at a physical slot and wraps at most once. -/
private theorem installed_slot (buf src : List order_range.ClockRange) (head lo j : Nat)
    (hh : head < buf.length) (fits : lo+src.length ≤ buf.length) (live : j < buf.length) :
    let p := OrderRangeRing.position buf.length head lo
    let n := min src.length (buf.length-p)
    (((buf.setSlice! p (src.take n)).setSlice! 0 (src.drop n))[OrderRangeRing.position buf.length head j]?) =
      if lo ≤ j ∧ j < lo+src.length then src[j-lo]? else buf[OrderRangeRing.position buf.length head j]? := by
  dsimp only
  let p := OrderRangeRing.position buf.length head lo
  let k := OrderRangeRing.position buf.length head j
  let n := min src.length (buf.length-p)
  change ((buf.setSlice! p (src.take n)).setSlice! 0 (src.drop n))[k]? = _
  have kn := OrderRangeRing.position_lt hh live
  have nle : n ≤ src.length := Nat.min_le_left _ _
  have prefixLength : (src.take n).length = n := by simp [Nat.min_eq_left nle]
  have suffix : (src.drop n).length = src.length-n := List.length_drop
  -- Relate each physical piece to the same logical index before reading the data.
  have coord :
      (k < src.length-n → lo ≤ j ∧ j < lo+src.length ∧ n+k = j-lo) ∧
      (p ≤ k ∧ k < p+n → lo ≤ j ∧ j < lo+src.length ∧ k-p = j-lo) ∧
      (lo ≤ j ∧ j < lo+src.length → k < src.length-n ∨ p ≤ k ∧ k < p+n) := by
    dsimp only [n,k,p,OrderRangeRing.position]
    split <;> split <;> omega
  by_cases wrap : k < src.length-n
  · have ⟨l,r,idx⟩ := coord.1 wrap
    rw [List.setSlice!_getElem?_middle _ _ _ _ (by rw [suffix,List.length_setSlice!]; exact ⟨Nat.zero_le _,by omega,kn⟩),
      if_pos ⟨l,r⟩,Nat.sub_zero,List.getElem?_drop,idx]
  · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega)]
    by_cases first : p ≤ k ∧ k < p+n
    · have ⟨l,r,idx⟩ := coord.2.1 first
      rw [List.setSlice!_getElem?_middle _ _ _ _ (by omega),List.getElem?_take,
        if_pos (by omega),if_pos ⟨l,r⟩,idx]
    · have outside : ¬(lo ≤ j ∧ j < lo+src.length) := fun h => (coord.2.2 h).elim wrap first
      rw [List.setSlice!_getElem?_same _ _ _ _ (by omega),if_neg outside]

private def installMerged (v : order_range.Ring) (lo : Usize) (merged : Ranges) : Result order_range.Ring := do
  let start ← order_range.physical v.buf.len (UScalar.cast .Usize v.head) lo
  let high ← v.buf.len - start
  let first := core.cmp.impls.OrdUsize.min merged.len high
  let stop ← start + first
  let (target,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice _) v.buf ⟨start,stop⟩
  let front ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice _) merged ⟨first⟩
  let data ← core.slice.Slice.copy_from_slice order_range.ClockRange.Insts.CoreMarkerCopy target front
  let buf := back data
  let rest ← merged.len - first
  let (target2,write) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice _) buf ⟨rest⟩
  let tail ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice _) merged ⟨first⟩
  let data2 ← core.slice.Slice.copy_from_slice order_range.ClockRange.Insts.CoreMarkerCopy target2 tail
  ok {v with buf := write data2}

private theorem copy_merged_spec (v : order_range.Ring) (lo : Usize)
    (merged : Ranges) (hw : ringWF v 0) (nonempty : 0 < merged.length)
    (room : lo.val+merged.length ≤ v.len.val) :
    installMerged v lo merged ⦃ w =>
      ringWF w 0 ∧ Copied (ringList v) (ringList w) merged.val lo.val 0 merged.length ⦄ := by
  obtain ⟨hh,hl,pos,cap⟩ := hw
  unfold installMerged
  step with physical_spec v.buf.len (UScalar.cast .Usize v.head) lo (by scalar_tac) (by scalar_tac) as ⟨start,hs,bounded⟩
  step as ⟨high,hhv⟩
  let n := core.cmp.impls.OrdUsize.min merged.len high
  have nv : n.val = min merged.length (v.buf.length-start.val) := by
    dsimp [n,core.cmp.impls.OrdUsize.min]
    split <;> scalar_tac
  step as ⟨stop,stopVal⟩
  step as ⟨target,back,_,targetLen,put⟩
  step as ⟨front,frontVal,frontLen⟩
  step with core.slice.Slice.copy_from_slice.step_spec _ target front (by omega) as ⟨data,hdata⟩
  subst data
  have backLen : (back front).length = v.buf.length := by
    change (back front).val.length = v.buf.val.length
    rw [put]
    simp only [alloc.vec.Vec.setSlice!, alloc.vec.Vec.val, Slice.setSlice!_val, List.length_setSlice!]
  step as ⟨rest,restVal⟩
  have mergedLen : merged.len.val = merged.length := by scalar_tac
  have bufLen : v.buf.val.length = v.buf.length := rfl
  have restFits : rest.val ≤ (back front).length := by rw [backLen]; omega
  step as ⟨target2,back2,_,targetLen2,put2⟩
  step as ⟨tail,tailVal,tailLen⟩
  step with core.slice.Slice.copy_from_slice.step_spec _ target2 tail (by omega) as ⟨data2,hdata2⟩
  subst data2
  try simp only [spec_ok]
  let w := {v with buf := back2 tail}
  have value : w.buf.val = (v.buf.val.setSlice! start.val (merged.val.take n.val)).setSlice! 0 (merged.val.drop n.val) := by
    change (back2 tail).val = _
    rw [put2,put]
    simp only [alloc.vec.Vec.setSlice!,alloc.vec.Vec.val,Slice.setSlice!_val]
    rw [frontVal,tailVal,List.slice_zero_j]
    rfl
  have len : w.buf.val.length = v.buf.val.length := by rw [value]; simp only [List.length_setSlice!]
  have wf : ringWF w 0 := ⟨by simpa only [len] using hh,by simpa only [len] using hl,pos,by rw [len]; exact cap⟩
  refine ⟨wf,by rw [ringList_length _ ⟨hh,hl,pos,cap⟩,ringList_length _ wf],fun j => ?_⟩
  by_cases live : j < v.len.val
  · change (OrderRangeRing.toList w.buf.val v.head.val v.len.val)[j]? = _
    rw [OrderRangeRing.lookup_view _ wf.1 wf.2.1 live,len,value]
    have slot := installed_slot v.buf.val merged.val v.head.val lo.val j hh (Nat.le_trans room hl) (Nat.lt_of_lt_of_le live hl)
    have startEq : start.val = OrderRangeRing.position v.buf.length v.head.val lo.val := by simpa using hs
    simpa only [startEq,nv,Nat.zero_add,ringList,OrderRangeRing.lookup_view _ hh hl live] using slot
  · have off : ¬(lo.val ≤ j ∧ j < lo.val+merged.length) := by omega
    rw [if_neg off,List.getElem?_eq_none (by rw [ringList_length _ wf]; exact Nat.le_of_not_lt live),
      List.getElem?_eq_none (by rw [ringList_length _ ⟨hh,hl,pos,cap⟩]; omega)]

private theorem list_after_copy (r v w : order_range.Ring) (lo hi : Nat)
    (incoming : List order_range.ClockRange) (a width : Nat) (hw : ringWF r 0)
    (source : a+width ≤ incoming.length) (ord : lo ≤ hi) (last : hi ≤ r.len.val)
    (gap : Gap r v lo hi width) (cw : Copied (ringList v) (ringList w) incoming lo a width) :
    ringList w = (ringList r).take lo ++ (incoming.drop a).take width ++ (ringList r).drop hi := by
  have rlen := ringList_length r hw
  have vlen := OrderRangeRing.toList_length v.buf.val (Nat.le_of_lt gap.head) gap.fits
  change (ringList v).length = v.len.val at vlen
  have oldlen : ((ringList r).take lo).length = lo := by simp [rlen, Nat.min_eq_left (by omega : lo ≤ r.len.val)]
  have inslen : ((incoming.drop a).take width).length = width := by simp; omega
  have prelen : (((ringList r).take lo) ++ (incoming.drop a).take width).length = lo+width := by
    simp [oldlen,inslen]
  apply List.ext_getElem?
  intro j
  rw [cw.2 j]
  by_cases before : j < lo
  · have h1 : j < (((ringList r).take lo) ++ (incoming.drop a).take width).length := by omega
    rw [List.getElem?_append_left h1, List.getElem?_append_left (by omega)]
    simp [before, Nat.not_le_of_gt before, gap.prefix_eq j before]
  · by_cases inside : j < lo+width
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega),oldlen]
      simp [inside, Nat.le_of_not_gt before, show j-lo < width by omega, List.getElem?_drop]
    · rw [List.getElem?_append_right (by omega),prelen,List.getElem?_drop]
      simp only [inside, and_false,↓reduceIte]
      let k := hi + (j-(lo+width))
      have atJ : lo+width+(k-hi) = j := by dsimp [k]; omega
      by_cases live : k < r.len.val
      · simpa only [atJ,k] using gap.suffix_eq k (by dsimp [k]; omega) live
      · have size := gap.len
        have endJ : (ringList v).length ≤ j := by dsimp [k] at live; omega
        have endK : (ringList r).length ≤ hi+(j-(lo+width)) := by dsimp [k] at live; omega
        rw [List.getElem?_eq_none endJ,List.getElem?_eq_none endK]

def windowList (xs : List order_range.ClockRange) (a b : Nat) := (xs.take b).drop a

theorem window_empty (l : List order_range.ClockRange) (a : Nat) : windowList l a a = [] := by
  unfold windowList
  exact List.drop_eq_nil_of_le (by simp)

theorem window_next (l : List order_range.ClockRange) (a b : Nat) (ab : a ≤ b) (hi : b < l.length) :
    windowList l a (b+1) = windowList l a b ++ [l[b]] := by
  unfold windowList
  rw [List.take_succ_eq_append_getElem hi, List.drop_append_of_le_length (by simp; omega)]

structure RingUnion (r : order_range.Ring) (batch : List order_range.ClockRange)
    (out : order_range.Ring) : Prop where
  wf : ringWF out 0
  can : CanonicalList (ringList out)
  count : out.len.val ≤ r.len.val + batch.length
  mem : ∀ c, inRangesList (ringList out) c ↔ inRangesList (ringList r) c ∨ inRangesList batch c

theorem union_empty (r : order_range.Ring) (hw : ringWF r 0) (hc : CanonicalList (ringList r)) :
    RingUnion r [] r := by
  exact ⟨hw,hc,by simp,fun c => by simp [inRangesList_iff_mem]⟩



private theorem clock_max (a b : Std.U64) : core.cmp.impls.OrdU64.max a b = max a b := by
  unfold core.cmp.impls.OrdU64.max
  split
  · rename_i h
    exact (max_eq_left (le_of_lt h)).symm
  · rename_i h
    exact (max_eq_right (le_of_not_gt h)).symm

private theorem merged_tail_step (v : Ranges) (x : order_range.ClockRange)
    (oi ni : Std.Usize) (room : v.length < 2^30)
    (P : ControlFlow (Ranges × Std.Usize × Std.Usize) Ranges → Prop)
    (next : ∀ w : Ranges, w.val = (pushRange v.val.reverse x).reverse →
      P (cont (w,oi,ni))) :
    (do
      let n := alloc.vec.Vec.len v
      if n > 0#usize then
        let i ← n - 1#usize
        let last ← alloc.vec.Vec.index_usize v i
        if last.end >= x.start then
          let again ← alloc.vec.Vec.index_usize v i
          let mx ← lift (core.cmp.impls.OrdU64.max again.end x.end)
          let (current, write) ← alloc.vec.Vec.index_mut_usize v i
          ok (cont (write {current with «end» := mx},oi,ni))
        else
          let w ← v.push x
          ok (cont (w,oi,ni))
      else
        let w ← v.push x
        ok (cont (w,oi,ni))) ⦃ P ⦄ := by
  by_cases nonempty : v.len > 0#usize
  · simp only [nonempty,↓reduceIte]
    step as ⟨i,hi⟩
    have size : i.val+1 = v.val.length := by scalar_tac
    have live : i.val < v.val.length := by omega
    step as ⟨last,hl⟩
    let pre := v.val.take i.val
    have front : v.val = pre ++ [last] := by
      rw [hl,← List.take_succ_eq_append_getElem live,size,List.take_length]
    have rev : v.val.reverse = last :: pre.reverse := by rw [front]; simp
    by_cases touching : last.end ≥ x.start
    · simp only [touching,↓reduceIte]
      step as ⟨again,ha⟩
      step as ⟨u,hu⟩
      step as ⟨current,write,hp,hw⟩
      apply next
      rw [hw]
      have value : current = last := hp.trans hl.symm
      have same : again = last := ha.trans hl.symm
      have mx : core.cmp.impls.OrdU64.max again.end x.end = max last.end x.end := by
        rw [same,clock_max]
      simp only [alloc.vec.Vec.set,rev,pushRange,touching,↓reduceIte,hu,mx,value,
        List.reverse_cons,List.reverse_reverse]
      let item : order_range.ClockRange := {last with «end» := max last.end x.end}
      have lenSet : (v.val.set i.val item).length ≤ i.val+1 := by simp [size]
      have itemEq := take_next_set v.val i.val item live
      rw [List.take_of_length_le lenSet] at itemEq
      simpa [pre,item] using itemEq
    · simp only [touching,↓reduceIte]
      step as ⟨w,hw⟩
      apply next
      simpa only [rev,pushRange,touching,↓reduceIte,List.reverse_cons,List.reverse_reverse,←front] using hw
  · simp only [nonempty,↓reduceIte]
    have empty : v.val = [] := List.length_eq_zero_iff.mp (by scalar_tac)
    step as ⟨w,hw⟩
    apply next
    simpa [empty,pushRange] using hw

private abbrev StartsBefore (a b : order_range.ClockRange) := a.start.val ≤ b.start.val

theorem window_member {l : List order_range.ClockRange} {a b : Nat} {x : order_range.ClockRange}
    (h : x ∈ windowList l a b) : ∃ i, ∃ hi : i < l.length, a ≤ i ∧ i < b ∧ l[i] = x := by
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp h
  simp only [windowList,List.length_drop,List.length_take] at hj
  refine ⟨a+j,by omega,by omega,by omega,?_⟩
  simpa only [windowList,List.getElem_drop,List.getElem_take] using eq

/-- The two cursors enumerate all consumed ranges in nondecreasing start
    order. The reverse fold describes the contents of the production vector. -/
private structure MergedPrefix (left right : List order_range.ClockRange)
    (lo a i j : Nat) (v : Ranges) : Prop where
  sequence : ∃ xs : List order_range.ClockRange,
    xs.Perm (windowList left lo i ++ windowList right a j) ∧
    xs.Pairwise StartsBefore ∧ v.val = (xs.foldl pushRange []).reverse ∧
    (∀ x ∈ xs, ∀ k (hk : k < left.length), i ≤ k → StartsBefore x left[k]) ∧
    (∀ x ∈ xs, ∀ k (hk : k < right.length), j ≤ k → StartsBefore x right[k])

private theorem fold_count (l rev : List order_range.ClockRange) :
    (l.foldl pushRange rev).length ≤ rev.length + l.length := by
  induction l generalizing rev with
  | nil => simp
  | cons x l ih =>
    have n : (pushRange rev x).length ≤ rev.length+1 := by
      cases rev with
      | nil => simp [pushRange]
      | cons y ys => simp only [pushRange]; split <;> simp
    have rest := ih (pushRange rev x)
    simp only [List.foldl_cons,List.length_cons]
    omega

private theorem prefix_count {left right : List order_range.ClockRange} {lo a i j : Nat} {v : Ranges}
    (h : MergedPrefix left right lo a i j v) :
    v.length ≤ (i-lo)+(j-a) := by
  obtain ⟨xs,perm,_,eq,_,_⟩ := h.sequence
  have count := fold_count xs []
  have len := perm.length_eq
  change v.val.length ≤ _
  rw [eq,List.length_reverse]
  simp only [List.length_nil,Nat.zero_add] at count
  simp only [List.length_append,windowList,List.length_drop,List.length_take] at len
  omega

private theorem prefix_step_left {left right : List order_range.ClockRange} {lo a i j : Nat}
    {v w : Ranges} (h : MergedPrefix left right lo a i j v)
    (loi : lo ≤ i) (hi : i < left.length) (can : CanonicalList left)
    (ordered : ∀ k (hk : k < right.length), j ≤ k → StartsBefore left[i] right[k])
    (value : w.val = (pushRange v.val.reverse left[i]).reverse) :
    MergedPrefix left right lo a (i+1) j w := by
  obtain ⟨xs,perm,ord,eq,old,new⟩ := h.sequence
  refine ⟨xs ++ [left[i]],?_,?_,?_,?_,?_⟩
  · rw [window_next left lo i loi hi]
    exact (perm.append_right _).trans (by
      simp only [List.append_assoc]
      exact List.Perm.append_left _ (List.perm_append_comm))
  · apply List.pairwise_append.mpr
    exact ⟨ord,by simp,fun x mem y hy => by obtain rfl := List.mem_singleton.mp hy; exact old x mem i hi (by omega)⟩
  · simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,eq,List.reverse_reverse] using value
  · intro x mem k hk lower
    rcases List.mem_append.mp mem with mem | mem
    · exact old x mem k hk (by omega)
    · have e := List.mem_singleton.mp mem
      subst x
      exact Nat.le_of_lt (canonicalList_start_lt can (by omega) hk)
  · intro x mem k hk lower
    rcases List.mem_append.mp mem with mem | mem
    · exact new x mem k hk lower
    · obtain rfl := List.mem_singleton.mp mem
      exact ordered k hk lower

private theorem prefix_swap {left right : List order_range.ClockRange} {lo a i j : Nat} {v : Ranges}
    (h : MergedPrefix left right lo a i j v) : MergedPrefix right left a lo j i v := by
  obtain ⟨xs,perm,order,value,l,r⟩ := h.sequence
  exact ⟨xs,perm.trans List.perm_append_comm,order,value,r,l⟩

/-- Merge exactly the two requested slices. Each live iteration consumes one
    old or one incoming range, coalescing at the tail of the output vector. -/
private theorem stream_merge_spec (r : order_range.Ring) (inc : order_range.OrderRange)
    (lo hi a b : Std.Usize) (hr : ringWF r 0) (lc : CanonicalList (ringList r))
    (rc : Canonical inc) (lh : lo.val ≤ hi.val) (ab : a.val ≤ b.val)
    (hl : hi.val ≤ (ringList r).length) (br : b.val ≤ (toList inc).length)
    (room : hi.val-lo.val + (b.val-a.val) ≤ 2^30) (empty : Ranges) (he : empty.val = []) :
    order_range.Ring.merge_window_loop1 r hi inc b empty lo a ⦃ out =>
      CanonicalList out.val ∧ out.length ≤ hi.val-lo.val + (b.val-a.val) ∧
      ∀ c, inRangesList out.val c ↔ inRangesList (windowList (ringList r) lo.val hi.val) c ∨
          inRangesList (windowList (toList inc) a.val b.val) c ⦄ := by
  let l := (ringList r).take hi.val
  let s := (toList inc).take b.val
  have ll : l.length = hi.val := by simp [l,Nat.min_eq_left hl]
  have sl : s.length = b.val := by simp [s,Nat.min_eq_left br]
  have takeCan (v : List order_range.ClockRange) (k : Nat) (h : CanonicalList v) : CanonicalList (v.take k) := by
    refine ⟨fun i hi => ?_,fun i j ij hj => ?_⟩
    · simp only [List.length_take] at hi
      simpa only [List.getElem_take] using h.1 i (by omega)
    · simp only [List.length_take] at hj
      simpa only [List.getElem_take] using h.2 i j ij (by omega)
  have oldLen := ringList_length r hr
  have lc' := takeCan _ hi.val lc
  have rc' := takeCan _ b.val rc.2
  let inv : Ranges × Std.Usize × Std.Usize → Prop := fun (v,i,j) =>
    lo.val ≤ i.val ∧ i.val ≤ hi.val ∧ a.val ≤ j.val ∧ j.val ≤ b.val ∧
      MergedPrefix l s lo.val a.val i.val j.val v
  unfold order_range.Ring.merge_window_loop1
  refine loop.spec_decr_nat (fun (_,i,j) => hi.val-i.val+(b.val-j.val)) inv _ _ _ ?_ ?_
  · intro ⟨v,i,j⟩ ⟨ilo,ihi,ja,jb,h⟩
    let P : ControlFlow (Ranges × Std.Usize × Std.Usize) Ranges → Prop := fun z => match z with
      | cont w => inv w ∧ hi.val-w.2.1.val+(b.val-w.2.2.val) < hi.val-i.val+(b.val-j.val)
      | done out => CanonicalList out.val ∧ out.length ≤ hi.val-lo.val+(b.val-a.val) ∧
          ∀ c, inRangesList out.val c ↔ inRangesList (windowList (ringList r) lo.val hi.val) c ∨
            inRangesList (windowList (toList inc) a.val b.val) c
    have count := prefix_count h
    have takeLeft (il : i.val < hi.val) (x : order_range.ClockRange) (get : x = l[i.val]'(by omega))
        (ord : ∀ k (hk : k < s.length), j.val ≤ k → StartsBefore x s[k])
        (i' : Std.Usize) (eq : i'.val = i.val+1) :
        ∀ w : Ranges, w.val = (pushRange v.val.reverse x).reverse → P (cont (w,i',j)) := by
      intro w val
      refine ⟨⟨by omega,by omega,ja,jb,?_⟩,by dsimp; omega⟩
      rw [eq]
      exact prefix_step_left h ilo (by omega) lc' (get ▸ ord) (get ▸ val)
    have takeRight (jl : j.val < b.val) (x : order_range.ClockRange) (get : x = s[j.val]'(by omega))
        (ord : ∀ k (hk : k < l.length), i.val ≤ k → StartsBefore x l[k])
        (j' : Std.Usize) (eq : j'.val = j.val+1) :
        ∀ w : Ranges, w.val = (pushRange v.val.reverse x).reverse → P (cont (w,i,j')) := by
      intro w val
      refine ⟨⟨ilo,ihi,by omega,by omega,?_⟩,by dsimp; omega⟩
      rw [eq]
      exact prefix_swap (prefix_step_left (prefix_swap h) ja (by omega) rc' (get ▸ ord) (get ▸ val))
    unfold order_range.Ring.merge_window_loop1.body
    simp only
    by_cases old : i < hi
    · have il : i.val < hi.val := by scalar_tac
      have ne : i ≠ hi := by scalar_tac
      have spare : v.length < 2^30 := by omega
      simp only [old,ne,↓reduceIte]
      by_cases new : j < b
      · have jl : j.val < b.val := by scalar_tac
        simp only [new,↓reduceIte]
        step with ring_at_list_spec r hr i (by omega) as ⟨x,hx⟩
        step with at_spec inc j rc.1 (by omega) as ⟨y,hy⟩
        have ex : x = l[i.val]'(by omega) := by simpa only [l,List.getElem_take] using hx
        have ey : y = s[j.val]'(by omega) := by simpa only [s,List.getElem_take] using hy
        by_cases earlier : y.start < x.start
        · simp only [earlier,↓reduceIte]
          step as ⟨j',eq⟩
          refine spec_mono (merged_tail_step v y i j' spare P ?_) ?_
          rotate_left
          · intro z hz
            cases z <;> exact hz
          apply takeRight jl y ey _ j' eq
          intro k hk ge
          change y.start.val ≤ _
          by_cases same : k = i.val
          · subst k; rw [←ex]; scalar_tac
          · have le := canonicalList_start_lt lc' (show i.val < k by omega) hk
            rw [←ex] at le
            scalar_tac
        · simp only [earlier,↓reduceIte]
          step as ⟨i',eq⟩
          refine spec_mono (merged_tail_step v x i' j spare P ?_) ?_
          rotate_left
          · intro z hz
            cases z <;> exact hz
          apply takeLeft il x ex _ i' eq
          intro k hk ge
          change x.start.val ≤ _
          by_cases same : k = j.val
          · subst k; rw [←ey]; scalar_tac
          · have le := canonicalList_start_lt rc' (show j.val < k by omega) hk
            rw [←ey] at le
            scalar_tac
      · simp only [new,↓reduceIte]
        step with ring_at_list_spec r hr i (by omega) as ⟨x,hx⟩
        step as ⟨i',eq⟩
        refine spec_mono (merged_tail_step v x i' j spare P ?_) ?_
        rotate_left
        · intro z hz
          cases z <;> exact hz
        exact takeLeft il x (by simpa only [l,List.getElem_take] using hx)
          (fun k hk ge => by
            have : b.val ≤ j.val := by scalar_tac
            omega) i' eq
    · have endI : i = hi := by scalar_tac
      simp only [old,↓reduceIte]
      simp only [endI,↓reduceIte]
      by_cases new : j < b
      · have jl : j.val < b.val := by scalar_tac
        simp only [new,↓reduceIte]
        step with at_spec inc j rc.1 (by omega) as ⟨y,hy⟩
        step as ⟨j',eq⟩
        refine spec_mono (merged_tail_step v y hi j' (by omega) P ?_) ?_
        rotate_left
        · intro z hz
          cases z <;> simpa only [P,endI] using hz
        rw [←endI]
        exact takeRight jl y (by simpa only [s,List.getElem_take] using hy)
          (fun k hk ge => by
            have : i.val = hi.val := congrArg UScalar.val endI
            omega) j' eq
      · simp only [new,↓reduceIte,spec_ok]
        have endJ : j.val = b.val := by scalar_tac
        obtain ⟨xs,perm,order,val,_,_⟩ := h.sequence
        have p : xs.Perm (windowList (ringList r) lo.val hi.val ++ windowList (toList inc) a.val b.val) := by
          simpa only [l,s,endI,endJ,windowList,List.take_take,Nat.min_self] using perm
        have valid (x) (mem : x ∈ xs) : x.start.val < x.end.val := by
          rcases List.mem_append.mp (p.mem_iff.mp mem) with left | right
          · obtain ⟨k,hk,_,_,rfl⟩ := window_member left
            exact lc.1 _ _
          · obtain ⟨k,hk,_,_,rfl⟩ := window_member right
            exact rc.2.1 _ _
        have sem : CanonicalList v.val ∧ ∀ c, inRangesList v.val c ↔ inRangesList xs c := by
          rw [val]
          by_cases nil : xs = []
          · simp [nil,CanonicalList]
          · exact fold_single xs nil valid order
        refine ⟨sem.1,by omega,fun c => ?_⟩
        rw [sem.2,←inRangesList_append]
        simp only [inRangesList_iff_mem,p.mem_iff]
  · refine ⟨Nat.le_refl _,lh,Nat.le_refl _,ab,⟨⟨[],?_,by simp,by simpa using he,by simp,by simp⟩⟩⟩
    simp [window_empty]

private theorem window_parts {α : Type} (l : List α) (lo hi : Nat) (ord : lo ≤ hi) :
    l.take lo ++ (l.take hi).drop lo ++ l.drop hi = l := by
  have first : (l.take hi).take lo = l.take lo := by rw [List.take_take, Nat.min_eq_left ord]
  rw [←first,List.take_append_drop,List.take_append_drop]

/-- A nonempty half-open output interval retains its left and its last
    occupied clocks. These witnesses transfer separation from the inputs. -/
private theorem covered_between (out sources : List order_range.ClockRange)
    (wf : CanonicalList out) (coverage : ∀ c, inRangesList out c → inRangesList sources c)
    (x : order_range.ClockRange) (mem : x ∈ out) :
    (∃ y ∈ sources, y.start.val ≤ x.start.val) ∧ (∃ y ∈ sources, x.end.val ≤ y.end.val) := by
  have valid := ((canonical_pairwise _).mp wf).1 x mem
  have first : inRangesList out x.start :=
    (inRangesList_iff_mem _ _).mpr ⟨x,mem,Nat.le_refl _,valid⟩
  let last : Std.U64 := Std.U64.ofNatCore (x.end.val-1) (by scalar_tac)
  have clock : last.val = x.end.val-1 := by rfl
  have finalClock : inRangesList out last :=
    (inRangesList_iff_mem _ _).mpr ⟨x,mem,by omega,by omega⟩
  obtain ⟨a,ha,low,_⟩ := (inRangesList_iff_mem _ _).mp (coverage _ first)
  obtain ⟨b,hb,_,high⟩ := (inRangesList_iff_mem _ _).mp (coverage _ finalClock)
  exact ⟨⟨a,ha,low⟩,⟨b,hb,by omega⟩⟩

private theorem window_replacement (pre old post extra out : List order_range.ClockRange)
    (can : CanonicalList (pre ++ old ++ post)) (middle : CanonicalList out)
    (left : ∀ x ∈ pre, ∀ y ∈ extra, BeforeRange x y)
    (right : ∀ x ∈ extra, ∀ y ∈ post, BeforeRange x y)
    (cover : ∀ c, inRangesList out c ↔ inRangesList old c ∨ inRangesList extra c) :
    CanonicalList (pre ++ out ++ post) ∧ ∀ c,
      inRangesList (pre ++ out ++ post) c ↔ inRangesList (pre ++ old ++ post) c ∨ inRangesList extra c := by
  obtain ⟨both,postCan,toPost⟩ := (canonical_append _ _).mp can
  obtain ⟨preCan,_,fromPre⟩ := (canonical_append _ _).mp both
  have endpoint := covered_between out (old ++ extra) middle
    (fun c h => (inRangesList_append old extra c).mpr ((cover c).mp h))
  constructor
  · apply (canonical_append _ _).mpr
    refine ⟨(canonical_append _ _).mpr ⟨preCan,middle,?_⟩,postCan,?_⟩
    · intro p hp x hx
      obtain ⟨w,hw,lower⟩ := (endpoint x hx).1
      have sep : BeforeRange p w := (List.mem_append.mp hw).elim (fromPre p hp w) (left p hp w)
      exact Nat.lt_of_lt_of_le sep lower
    · intro x hx y hy
      rcases List.mem_append.mp hx with hp | ho
      · exact toPost _ (List.mem_append_left _ hp) _ hy
      · obtain ⟨w,hw,upper⟩ := (endpoint x ho).2
        have sep : BeforeRange w y := (List.mem_append.mp hw).elim
          (fun hold => toPost w (List.mem_append_right _ hold) y hy) (fun hex => right w hex y hy)
        exact Nat.lt_of_le_of_lt upper sep
  · intro c
    simp only [inRangesList_append,cover]
    tauto

theorem window_as_take (l : List order_range.ClockRange) (i j : Nat) :
    windowList l i j = (l.drop i).take (j-i) := by
  unfold windowList
  exact List.drop_take ..

theorem window_index (l : List order_range.ClockRange) (lo hi j : Nat)
    (hj : j < l.length) (low : lo ≤ j) (high : j < hi) : l[j] ∈ windowList l lo hi := by
  have bound : j-lo < (windowList l lo hi).length := by simp [windowList]; omega
  have atJ : (windowList l lo hi)[j-lo] = l[j] := by
    simp only [windowList,List.getElem_drop,List.getElem_take,show lo+(j-lo) = j by omega]
  exact atJ ▸ List.getElem_mem bound

private theorem canonical_window (l : List order_range.ClockRange) (i j : Nat) (h : CanonicalList l) :
    CanonicalList (windowList l i j) := by
  have sub : (windowList l i j).Sublist l := (List.drop_sublist ..).trans (List.take_sublist ..)
  obtain ⟨valid,order⟩ := (canonical_pairwise _).mp h
  exact (canonical_pairwise _).mpr ⟨fun x hx => valid x (sub.subset hx),order.sublist sub⟩

/-- The old intervals outside the selected window have a strict gap to
    every incoming interval. The singleton fast path also needs the two
    outer old intervals inside the window to touch that singleton. -/
structure WindowBounds (old src : List order_range.ClockRange) (lo hi a b : Nat) : Prop where
  left : ∀ x ∈ old.take lo, ∀ y ∈ windowList src a b, BeforeRange x y
  right : ∀ x ∈ windowList src a b, ∀ y ∈ old.drop hi, BeforeRange x y
  overlap : ∀ (_one : b = a+1) (nonempty : lo < hi) (bound : hi ≤ old.length) (source : a < src.length),
    src[a].start.val ≤ old[lo].end.val ∧ old[hi-1].start.val ≤ src[a].end.val

theorem merge_window_spec (r : order_range.Ring) (lo hi : Std.Usize)
    (inc : order_range.OrderRange) (a b : Std.Usize) (hw : ringWF r 0)
    (hc : CanonicalList (ringList r)) (ic : Canonical inc) (lh : lo.val ≤ hi.val)
    (hb : hi.val ≤ r.len.val) (ab : a.val ≤ b.val) (sb : b.val ≤ (toList inc).length)
    (room : r.len.val+(b.val-a.val) ≤ 2^30)
    (edges : WindowBounds (ringList r) (toList inc) lo.val hi.val a.val b.val) :
    order_range.Ring.merge_window r lo hi inc a b ⦃ out =>
      RingUnion r (windowList (toList inc) a.val b.val) out ⦄ := by
  let old := ringList r
  let src := toList inc
  let batch := windowList src a.val b.val
  let inside := windowList old lo.val hi.val
  have len : old.length = r.len.val := ringList_length r hw
  have realLen := ringList_length r hw
  have srcLen : src.length = (toList inc).length := rfl
  have bLen : batch.length = b.val-a.val := by simp [batch,windowList,src,Nat.min_eq_left sb]
  have parts : old.take lo.val ++ inside ++ old.drop hi.val = old := window_parts old _ _ lh
  have replace (middle : List order_range.ClockRange) (can : CanonicalList middle)
      (members : ∀ c, inRangesList middle c ↔ inRangesList inside c ∨ inRangesList batch c) :
      CanonicalList (old.take lo.val ++ middle ++ old.drop hi.val) ∧
      ∀ c, inRangesList (old.take lo.val ++ middle ++ old.drop hi.val) c ↔
        inRangesList old c ∨ inRangesList batch c := by
    have h := window_replacement (old.take lo.val) inside (old.drop hi.val) batch middle
      (by rw [parts]; exact hc) can edges.left edges.right members
    simpa only [parts] using h
  have gapWF (v : order_range.Ring) (n : Nat) (g : Gap r v lo.val hi.val n) (pos : 0 < n) :
      ringWF v 0 := ⟨g.head,g.fits,by have := g.len; omega,g.bound⟩
  unfold order_range.Ring.merge_window
  by_cases no : a = b
  · simp only [no,↓reduceIte,spec_ok,window_empty]
    exact union_empty r hw hc
  · simp only [no,↓reduceIte]
    have more : a.val < b.val := by scalar_tac
    by_cases none : lo = hi
    · simp only [none,↓reduceIte]
      step as ⟨width,n⟩
      step with make_gap_spec r hi hi width hw (Nat.le_refl _) hb (by omega) as ⟨v,g⟩
      have gap := g.len
      rw [none] at gapWF
      step with copy_incoming_spec v inc hi a b (gapWF v _ g (by omega)) ic.1 ab sb (by omega)
        as ⟨w,wf,copied⟩
      have frame := list_after_copy r v w hi.val hi.val src a.val width.val hw (by omega)
        (Nat.le_refl _) hb g (by simpa only [n] using copied)
      have value : ringList w = old.take lo.val ++ batch ++ old.drop hi.val := by
        simpa only [none,batch,window_as_take,n] using frame
      have sem := replace batch (canonical_window _ _ _ ic.2) (by
        intro c; simp [inside,none,window_empty,inRangesList_iff_mem])
      refine ⟨wf,by rw [value]; exact sem.1,?_,by rw [value]; exact sem.2⟩
      change w.len.val ≤ r.len.val + batch.length
      have nEq := congrArg UScalar.val none
      have sizes := congrArg List.length value
      simp only [List.length_append,List.length_take,List.length_drop,ringList_length w wf] at sizes
      omega
    · simp only [none,↓reduceIte]
      step as ⟨width,n⟩
      have hit : lo.val < hi.val := by scalar_tac
      by_cases single : width = 1#usize
      · simp only [single,↓reduceIte,lift,bind_ok]
        have one : b.val = a.val+1 := by scalar_tac
        have al : a.val < src.length := by dsimp [src]; omega
        step with at_spec inc a ic.1 al as ⟨x,hx⟩
        step with ring_at_list_spec r hw lo (by omega) as ⟨f,hf⟩
        step as ⟨k,hk⟩
        step with ring_at_list_spec r hw k (by omega) as ⟨z,hz⟩
        let m : order_range.ClockRange := ⟨core.cmp.impls.OrdU64.min f.start x.start,
          core.cmp.impls.OrdU64.max z.end x.end⟩
        have ms : m.start.val = min x.start.val f.start.val := by
          dsimp [m,core.cmp.impls.OrdU64.min]; split <;> scalar_tac
        have me : m.end.val = max x.end.val z.end.val := by
          dsimp [m,core.cmp.impls.OrdU64.max]; split <;> scalar_tac
        have onlyX : batch = [x] := by
          dsimp [batch]
          rw [one,window_next _ _ _ (Nat.le_refl _) al,window_empty,hx,List.nil_append]
        have onlyX' : windowList (toList inc) a.val b.val = [x] := onlyX
        obtain ⟨first,last⟩ := edges.overlap one hit (by omega) al
        have sem := merged_window old lo.val hi.val x m hc (by simpa only [hx] using ic.2.1 a.val al)
          hit (by omega)
          (fun j hj lower => edges.left old[j] (by
            simpa only [windowList,List.drop_zero] using window_index old 0 lo.val j hj (Nat.zero_le _) lower) x (by rw [onlyX']; simp))
          (by simpa only [hx] using first) (by simpa only [hx] using last)
          (fun j hj greater => edges.right x (by rw [onlyX']; simp) old[j] (by
            have p : j = hi.val+(j-hi.val) := by omega
            have eq : (old.drop hi.val)[j-hi.val]'(by simp; omega) = old[j] := by simp [←p]
            exact eq ▸ List.getElem_mem _))
          (by simpa only [hf] using ms) (by simpa only [hz,hk] using me)
        step with make_gap_spec r lo hi 1#usize hw lh hb (by scalar_tac) as ⟨v,g⟩
        step with fill_gap r v lo hi m hw lh hb g as ⟨w,head,size,fit,cap,value⟩
        have n' := g.len
        refine ⟨⟨head,fit,by rw [size]; omega,cap⟩,by rw [value]; exact sem.1,by rw [size,bLen]; omega,?_⟩
        intro c
        rw [value,onlyX',inRangesList_singleton]
        exact sem.2 c
      · simp only [single,↓reduceIte]
        step as ⟨oldSize,hOld⟩
        step as ⟨capacity,hcap⟩
        step with stream_merge_spec r inc lo hi a b hw hc ic lh ab (by omega) sb (by omega)
          (alloc.vec.Vec.with_capacity _ capacity) rfl as ⟨middle,can,count,mem⟩
        have sem := replace middle.val can mem
        have positive : 0 < middle.length := by
          have active := ic.2.1 a.val (by omega)
          let x := (toList inc)[a.val]'(by omega)
          have xi : x ∈ batch := by
            exact window_index src a.val b.val a.val (by dsimp [src]; omega) (Nat.le_refl _) more
          have found := (mem x.start).mpr (Or.inr ((inRangesList_iff_mem _ _).mpr
            ⟨x,xi,Nat.le_refl _,active⟩))
          obtain ⟨k,hk,_⟩ := found
          exact Nat.zero_lt_of_lt hk
        have nVal : middle.len.val = middle.length := by scalar_tac
        have install :
            (do let v ← order_range.Ring.make_gap r lo hi middle.len
                installMerged v lo middle) ⦃ out => RingUnion r batch out ⦄ := by
          step with make_gap_spec r lo hi middle.len hw lh hb (by omega) as ⟨v,g⟩
          step with copy_merged_spec v lo middle (gapWF v _ g (by omega)) positive (by have := g.len; omega)
            as ⟨w,wf,copied⟩
          have frame := list_after_copy r v w lo.val hi.val middle.val 0 middle.length hw (by simp)
            lh hb (by simpa only [nVal] using g) copied
          simp only [List.drop_zero,List.take_length] at frame
          refine ⟨wf,by rw [frame]; exact sem.1,?_,by rw [frame]; exact sem.2⟩
          have sizes := congrArg List.length frame
          simp only [List.length_append,List.length_take,List.length_drop,ringList_length w wf] at sizes
          change middle.val.length ≤ _ at count
          change _ ≤ _+batch.length
          omega
        simp only [lift,bind_ok]
        by_cases atZero : lo = 0#usize
        · simp only [atZero,↓reduceIte]
          by_cases atEnd : hi = UScalar.cast .Usize r.len
          · simp only [atEnd,↓reduceIte]
            by_cases reuse : r.buf.len ≤ middle.len
            · simp only [reuse,↓reduceIte]
              step with capacity_hint_spec r hw as ⟨hint,_⟩
              by_cases enough : hint ≤ middle.len
              · simp only [enough,↓reduceIte,spec_ok]
                have total : middle.length ≤ 2^30 := by omega
                have castLen : (UScalar.cast .U32 middle.len).val = middle.length := by scalar_tac
                have zero : (0#u32).val = 0 := by decide
                have list : ringList ⟨middle,0#u32,UScalar.cast .U32 middle.len⟩ = middle.val := by
                  simp only [ringList,zero,castLen,OrderRangeRing.toList_initial,List.take_length]
                have loNat : lo.val = 0 := by rw [atZero]; decide
                have hiNat : hi.val = old.length := by rw [len,atEnd]; scalar_tac
                have semantic := sem.2
                simp only [loNat,hiNat,List.take_zero,List.nil_append,List.drop_length,List.append_nil] at semantic
                have wf : ringWF ⟨middle,0#u32,UScalar.cast .U32 middle.len⟩ 0 := by
                  change (0#u32).val < middle.length ∧ (UScalar.cast .U32 middle.len).val ≤ middle.length ∧
                    0+1 ≤ (UScalar.cast .U32 middle.len).val ∧ middle.length ≤ 2^30
                  rw [zero,castLen]
                  exact ⟨positive,Nat.le_refl _,positive,total⟩
                refine ⟨wf,by rw [list]; exact can,?_,by rw [list]; exact semantic⟩
                change (UScalar.cast .U32 middle.len).val ≤ r.len.val+batch.length
                rw [castLen,bLen]
                omega
              · simpa only [enough,↓reduceIte,atZero,atEnd,installMerged,batch,src] using install
            · simpa only [reuse,↓reduceIte,atZero,atEnd,installMerged,batch,src] using install
          · simpa only [atEnd,↓reduceIte,atZero,installMerged,batch,src] using install
        · simpa only [atZero,↓reduceIte,installMerged,batch,src] using install


end YoctoCore.Properties.OrderRange
