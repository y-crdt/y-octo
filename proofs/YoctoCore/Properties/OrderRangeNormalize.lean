import YoctoCore.Properties.OrderRange
import YoctoCore.Properties.OrderRangeSort
open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.OrderRange

/-- The most recently written range is kept at the head of this specification
    accumulator. The production loop stores the same prefix in forward order. -/
def pushRange (rev : List order_range.ClockRange) (x : order_range.ClockRange) :
    List order_range.ClockRange :=
  match rev with
  | [] => [x]
  | last :: tail =>
    if x.start ≤ last.end then {last with «end» := max last.end x.end} :: tail else x :: rev

private theorem fold_ranges (tail : List order_range.ClockRange) (last : order_range.ClockRange)
    (rest : List order_range.ClockRange)
    (can : CanonicalList (tail.reverse ++ [last]))
    (sorted : rest.Pairwise (fun a b => a.start.val ≤ b.start.val))
    (valid : ∀ x ∈ rest, x.start.val < x.end.val)
    (lower : ∀ x ∈ rest, last.start.val ≤ x.start.val) :
    let out := (rest.foldl pushRange (last::tail)).reverse
    CanonicalList out ∧ ∀ c, inRangesList out c ↔
      inRangesList (tail.reverse ++ [last]) c ∨ inRangesList rest c := by
  induction rest generalizing last tail with
  | nil =>
    simp [List.reverse_cons, can, inRangesList_iff_mem]
  | cons x xs ih =>
    obtain ⟨follows, order⟩ := List.pairwise_cons.mp sorted
    have xv := valid x (by simp)
    have lb := lower x (by simp)
    have remaining : ∀ y ∈ xs, y.start.val < y.end.val :=
      fun y hy => valid y (List.mem_cons_of_mem _ hy)
    have add (c : Std.U64) : inRangesList (x::xs) c ↔ inRangesList [x] c ∨ inRangesList xs c :=
      inRangesList_append [x] xs c
    by_cases touch : x.start ≤ last.end
    · let joined : order_range.ClockRange := {last with «end» := max last.end x.end}
      have maxEnd : joined.end.val = max last.end.val x.end.val := by
        by_cases le : last.end ≤ x.end
        · simp only [joined, max_eq_right le, Nat.max_eq_right (show last.end.val ≤ x.end.val by scalar_tac)]
        · simp only [joined, max_eq_left (le_of_not_ge le), Nat.max_eq_left (show x.end.val ≤ last.end.val by scalar_tac)]
      have jc : CanonicalList (tail.reverse ++ [joined]) :=
        canonical_last _ last joined can rfl (by change last.start.val < joined.end.val; omega)
      have step := ih tail joined jc order remaining (fun y hy => lower y (List.mem_cons_of_mem _ hy))
      simp only [List.foldl_cons, pushRange, touch, ↓reduceIte]
      refine ⟨step.1, fun c => ?_⟩
      have joinedMem := coalesce_mem_iff tail.reverse last x c lb (by scalar_tac)
      have two : tail.reverse ++ [last,x] = (tail.reverse ++ [last]) ++ [x] := by simp
      rw [two, inRangesList_append (tail.reverse ++ [last]) [x]] at joinedMem
      rw [step.2, add]
      change (inRangesList (tail.reverse ++ [joined]) c ∨ _) ↔ _
      rw [show inRangesList (tail.reverse ++ [joined]) c ↔ _ from joinedMem]
      tauto
    · have sep : BeforeRange last x := by unfold BeforeRange; scalar_tac
      have next := canonical_push _ _ _ can sep xv
      have cc : CanonicalList ((last::tail).reverse ++ [x]) := by simpa only [List.reverse_cons] using next
      have step := ih (last::tail) x cc order remaining follows
      simp only [List.foldl_cons, pushRange, touch, ↓reduceIte]
      refine ⟨step.1, fun c => ?_⟩
      rw [step.2, add, List.reverse_cons, inRangesList_append (tail.reverse ++ [last]) [x]]
      tauto

abbrev Ranges := alloc.vec.Vec order_range.ClockRange

theorem take_next_set {α : Type} (l : List α) (k : Nat) (x : α) (hk : k < l.length) :
    (l.set k x).take (k+1) = l.take k ++ [x] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ k => simp [List.set, List.take, ih k (by simpa using hk)]

theorem fold_single (l : List order_range.ClockRange) (hl : l ≠ [])
    (valid : ∀ r ∈ l, r.start.val < r.end.val)
    (ordered : l.Pairwise (fun a b => a.start.val ≤ b.start.val)) :
    CanonicalList (l.foldl pushRange []).reverse ∧
      ∀ c, inRangesList (l.foldl pushRange []).reverse c ↔ inRangesList l c := by
  cases l with
  | nil => contradiction
  | cons x tail =>
    obtain ⟨lower, pairs⟩ := List.pairwise_cons.mp ordered
    have one : CanonicalList [x] :=
      (canonical_pairwise _).mpr ⟨by simpa using valid x (by simp), by simp⟩
    obtain ⟨h, mem⟩ := fold_ranges [] x tail one pairs
      (fun r hr => valid r (List.mem_cons_of_mem _ hr)) lower
    refine ⟨h, fun c => ?_⟩
    change inRangesList (tail.foldl pushRange [x]).reverse c ↔ inRangesList (x :: tail) c
    exact (mem c).trans (inRangesList_append [x] tail c).symm

/-- The write cursor delimits the canonicalized prefix. The unread suffix
    stays at its original indices even when adjacent input ranges coalesce. -/
private theorem coalesce_loop_spec (input : Ranges) (stop : Std.Usize)
    (many : 1 ≤ stop.val) (fits : stop.val ≤ input.length) :
    order_range.coalesce_sorted_prefix_loop input stop 1#usize 1#usize ⦃ (n,v) =>
      v.length = input.length ∧ n.val ≤ stop.val ∧
      v.val.take n.val = ((input.val.take stop.val).foldl pushRange []).reverse ⦄ := by
  let inv : Ranges × Std.Usize × Std.Usize → Prop := fun (v,used,read) =>
    v.length = input.length ∧ 0 < used.val ∧ used.val ≤ read.val ∧ read.val ≤ stop.val ∧
    v.val.take used.val = ((input.val.take read.val).foldl pushRange []).reverse ∧
    v.val.drop read.val = input.val.drop read.val
  unfold order_range.coalesce_sorted_prefix_loop
  refine loop.spec_decr_nat (fun (_,_,read) => stop.val-read.val) inv _ _ _ ?_ ?_
  · intro ⟨v,used,read⟩ ⟨lv, pos, ur, bound, pre, unread⟩
    unfold order_range.coalesce_sorted_prefix_loop.body
    simp only
    by_cases live : read < stop
    · simp only [live, ↓reduceIte]
      have rv : read.val < v.val.length := by scalar_tac
      have ri : read.val < input.val.length := by scalar_tac
      step as ⟨x,hx⟩
      step as ⟨last,hl⟩
      step as ⟨old,ho⟩
      have us : last.val+1 = used.val := by omega
      have li : last.val < v.val.length := by scalar_tac
      have front : v.val.take used.val = v.val.take last.val ++ [old] := by
        rw [← us, List.take_succ_eq_append_getElem li, ho]
      have folded : (input.val.take read.val).foldl pushRange [] =
          old :: (v.val.take last.val).reverse := by
        have h := congrArg List.reverse (pre.symm.trans front)
        simpa using h
      have originalX : input.val[read.val] = x := by
        have e := congrArg (fun l : List order_range.ClockRange => l[0]?) unread
        simpa [List.getElem?_drop, List.getElem?_eq_getElem rv, List.getElem?_eq_getElem ri, hx] using e.symm
      have finish (out : Ranges) (n : Std.Usize) (len : out.length = v.length)
          (npos : 0 < n.val) (nread : n.val ≤ read.val+1)
          (written : out.val.take n.val = (pushRange (old :: (v.val.take last.val).reverse) x).reverse)
          (suffix : out.val.drop (read.val+1) = v.val.drop (read.val+1)) :
          (do let j ← read + 1#usize; ok (cont (out,n,j) : ControlFlow (Ranges × Std.Usize × Std.Usize) (Std.Usize × Ranges))) ⦃ r =>
            match r with
            | done y => y.2.length = input.length ∧ y.1.val ≤ stop.val ∧
                y.2.val.take y.1.val = ((input.val.take stop.val).foldl pushRange []).reverse
            | cont z => inv z ∧ stop.val-z.2.2.val < stop.val-read.val ⦄ := by
        step as ⟨j,hj⟩
        refine ⟨⟨len.trans lv,npos,by omega,by scalar_tac,?_,?_⟩, by scalar_tac⟩
        · rw [hj,List.take_succ_eq_append_getElem ri,List.foldl_append,folded,originalX]
          exact written
        · have s := congrArg (List.drop 1) unread
          rw [hj, suffix]
          simpa only [List.drop_drop, Nat.add_comm 1] using s
      by_cases touch : x.start ≤ old.end
      · simp only [touch, ↓reduceIte]
        step as ⟨same,hsame⟩
        have eq : same = old := hsame.trans ho.symm
        rw [eq]
        by_cases taller : x.end > old.end
        · simp only [taller, ↓reduceIte]
          step as ⟨p, he, hw⟩
          rcases p with ⟨a, write⟩
          simp only at he hw
          subst write
          let out := alloc.vec.Vec.set v last ({x with start := a.start})
          change (do let w ← ok out; let j ← read + 1#usize
                     ok (cont (w,used,j) : ControlFlow (Ranges × Std.Usize × Std.Usize) (Std.Usize × Ranges))) ⦃ _ ⦄
          simp only [bind_ok]
          refine spec_mono (finish out used (by simp [out, alloc.vec.Vec.length, alloc.vec.Vec.set]) pos (by omega) ?_ ?_) ?_
          · have sameOld : a = old := he.trans ho.symm
            simp only [out,alloc.vec.Vec.set,←us,pushRange,touch,↓reduceIte,
              max_eq_right (le_of_lt taller),sameOld,List.reverse_cons,List.reverse_reverse]
            simpa using take_next_set v.val last.val ({old with «end» := x.end}) li
          · simp [out, alloc.vec.Vec.set, OrderRangeHeap.drop_set_before _ _ _ _ (show last.val < read.val+1 by omega)]
          · intro z hz
            cases z with
            | done y => rcases y with ⟨n,u⟩; exact hz
            | cont w => exact hz
        · simp only [taller, ↓reduceIte, bind_ok]
          refine spec_mono (finish v used rfl pos (by omega) ?_ rfl) ?_
          · simpa [pushRange, touch, max_eq_left (le_of_not_gt taller)] using front
          · intro z hz
            cases z with
            | done y => rcases y with ⟨n,u⟩; exact hz
            | cont w => exact hz
      · simp only [touch, ↓reduceIte]
        step as ⟨p, _, hw⟩
        rcases p with ⟨ignored,write⟩
        simp only at hw
        subst write
        step as ⟨n,hn⟩
        let out := alloc.vec.Vec.set v used x
        refine spec_mono (finish out n (by simp [out, alloc.vec.Vec.length, alloc.vec.Vec.set]) (by omega) (by omega) ?_ ?_) ?_
        · simp [out,alloc.vec.Vec.set, hn, take_next_set _ _ _ (show used.val < v.val.length by omega),
            pushRange, touch, front, List.reverse_cons]
        · simp [out,alloc.vec.Vec.set, OrderRangeHeap.drop_set_before _ _ _ _ (show used.val < read.val+1 by omega)]
        · intro z hz
          cases z with
            | done y => rcases y with ⟨n,u⟩; exact hz
            | cont w => exact hz
    · simp only [live, ↓reduceIte, spec_ok]
      exact ⟨lv, by omega, by simpa only [show read.val = stop.val by scalar_tac] using pre⟩
  · have h : 0 < input.val.length := by scalar_tac
    have one : (1#usize).val = 1 := by decide
    have first : input.val.take 1 = [input.val[0]] := by
      exact List.take_succ_eq_append_getElem h
    simp [inv, one, first, pushRange, many]

private theorem coalesce_sorted_prefix_spec (input : Ranges) (n : Std.Usize)
    (positive : 1 ≤ n.val) (fits : n.val ≤ input.length)
    (valid : ∀ x ∈ input.val.take n.val, x.start.val < x.end.val)
    (ordered : (input.val.take n.val).Pairwise OrderRangeSort.Ordered) :
    order_range.coalesce_sorted_prefix input n ⦃ (used,out) =>
      out.length = input.length ∧ used.val ≤ n.val ∧ CanonicalList (out.val.take used.val) ∧
      ∀ c, inRangesList (out.val.take used.val) c ↔ inRangesList (input.val.take n.val) c ⦄ := by
  have size : (input.val.take n.val).length = n.val := by
    rw [List.length_take, Nat.min_eq_left fits]
  have sem := fold_single (input.val.take n.val) (by intro h; simp [h] at size; omega)
    valid (ordered.imp (fun h => by unfold OrderRangeSort.Ordered OrderRangeSort.Earlier at h; omega))
  unfold order_range.coalesce_sorted_prefix
  apply spec_mono (coalesce_loop_spec input n positive fits)
  rintro ⟨used,out⟩ ⟨len,bound,fold⟩
  exact ⟨len,bound,fold.symm ▸ sem.1,fun c => fold.symm ▸ sem.2 c⟩

private theorem filter_members (l : List order_range.ClockRange) (c : Std.U64) :
    inRangesList (l.filter OrderRangeSort.validRange) c ↔ inRangesList l c := by
  simp only [inRangesList_iff_mem, List.mem_filter, OrderRangeSort.validRange, decide_eq_true_eq]
  grind

theorem canonicalize_spec (ranges : Ranges) :
    order_range.canonicalize ranges ⦃ (len,out) => out.length = ranges.length ∧
      len.val ≤ out.length ∧ CanonicalList (out.val.take len.val) ∧
      ∀ c, inRangesList (out.val.take len.val) c ↔ inRangesList ranges.val c ⦄ := by
  unfold order_range.canonicalize
  step with is_canonical_spec (alloc.vec.Vec.deref ranges) as ⟨b, hb⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step with OrderRangeSort.nonempty_prefix_spec ranges as ⟨n,buf,bl,fit,kept⟩
    have valid (r) (mem : r ∈ buf.val.take n.val) : r.start.val < r.end.val := by
      rw [kept] at mem
      simpa only [OrderRangeSort.validRange,decide_eq_true_eq] using (List.mem_filter.mp mem).2
    by_cases short : n < 2#usize
    · simp only [short, ↓reduceIte, spec_ok]
      refine ⟨bl,fit,⟨fun i h => valid _ (List.getElem_mem h),?_⟩,?_⟩
      · intro i j lt hj
        have hn : n.val < 2 := by scalar_tac
        simp only [List.length_take] at hj
        omega
      · intro c
        rw [kept,filter_members]
    · simp only [short, ↓reduceIte]
      step with OrderRangeSort.sort_prefix_spec buf n fit as ⟨sorted,post⟩
      obtain ⟨perm,frame,order⟩ := post
      let l := sorted.val.take n.val
      have pp : l.Perm (buf.val.take n.val) := OrderRangeHeap.take_perm perm frame
      have sl : sorted.length = buf.length := perm.length_eq
      have hn : 2 ≤ n.val := by scalar_tac
      step with coalesce_sorted_prefix_spec sorted n (by omega) (by omega)
        (fun r mem => valid r (pp.mem_iff.mp mem)) order as ⟨num,out,os,count,can,sem⟩
      refine ⟨os.trans (sl.trans bl),by omega,can,?_⟩
      intro c
      rw [sem c]
      have eq : inRangesList l c ↔ inRangesList (buf.val.take n.val) c := by
        simp only [inRangesList_iff_mem,pp.mem_iff]
      rwa [kept,filter_members] at eq
  · simp only [↓reduceIte,spec_ok]
    have all : ranges.val.take (alloc.vec.Vec.len ranges).val = ranges.val := by
      have hn : (alloc.vec.Vec.len ranges).val = ranges.val.length := by scalar_tac
      simp [hn]
    refine ⟨rfl,by scalar_tac,?_,?_⟩
    · rw [all]
      simpa [alloc.vec.Vec.deref] using hb.mp rfl
    · simp only [all,iff_self,implies_true]

theorem from_vec_with_capacity_spec (ranges : Ranges) (hint : Std.Usize)
    (limit : ranges.length ≤ 2^30) :
    order_range.OrderRange.from_vec_with_capacity ranges hint ⦃ out =>
      Canonical out ∧ ∀ c, inRanges out c ↔ inRangesList ranges.val c ⦄ := by
  unfold order_range.OrderRange.from_vec_with_capacity
  step with canonicalize_spec ranges as ⟨len,buf,bl,fit,can,mem⟩
  step with from_prefix_spec buf len hint fit (by omega) can as ⟨out,oc,view⟩
  exact ⟨oc, fun c => by simpa only [inRanges,view] using mem c⟩

theorem from_vec_spec (ranges : Ranges) (limit : ranges.length ≤ 2^30) :
    order_range.OrderRange.from_vec ranges ⦃ out =>
      Canonical out ∧ ∀ c, inRanges out c ↔ inRangesList ranges.val c ⦄ :=
  from_vec_with_capacity_spec ranges 0#usize limit
private theorem ordered_filter_spec (buf : Slice order_range.ClockRange) :
    order_range.ordered_needs_filter buf ⦃ result => match result with
      | none => True
      | some flag => buf.val.Pairwise OrderRangeSort.Ordered ∧
          (flag = false → ∀ x ∈ buf.val, x.start.val < x.end.val) ⦄ := by
  let inv : Bool × Usize → Prop := fun (flag,i) =>
    i.val ≤ buf.length ∧ (buf.val.take i.val).Pairwise OrderRangeSort.Ordered ∧
      (flag = false → ∀ x ∈ buf.val.take i.val, x.start.val < x.end.val)
  unfold order_range.ordered_needs_filter order_range.ordered_needs_filter_loop
  refine loop.spec_decr_nat (fun (_,i) => buf.length-i.val) inv _ _ _ ?_ ?_
  · intro ⟨flag,i⟩ ⟨bound,order,valid⟩
    unfold order_range.ordered_needs_filter_loop.body
    by_cases live : i < Slice.len buf
    · simp only [live,↓reduceIte]
      have inside : i.val < buf.val.length := by scalar_tac
      step as ⟨x,hx⟩
      have append (next : Usize) (hn : next.val = i.val+1)
          (earlier : ∀ y ∈ buf.val.take i.val, OrderRangeSort.Ordered y x) :
          inv (flag || decide (x.start ≥ x.end), next) ∧ buf.length-next.val < buf.length-i.val := by
        have view : buf.val.take next.val = buf.val.take i.val ++ [x] := by
          rw [hn,List.take_succ_eq_append_getElem inside,hx]
        refine ⟨⟨by scalar_tac,?_,?_⟩,by scalar_tac⟩
        · rw [view,List.pairwise_append]
          exact ⟨order,by simp,by simpa using earlier⟩
        · intro no y hy
          rw [view,List.mem_append] at hy
          have flags : flag = false ∧ ¬x.start ≥ x.end := by simpa using no
          rcases hy with before | last
          · exact valid flags.1 y before
          · have eq : y = x := by simpa using last
            subst y
            scalar_tac
      split_ifs with nz
      · step as ⟨j,hj⟩
        step as ⟨prev,hp⟩
        step with OrderRangeSort.before_spec x prev as ⟨b,cmp⟩
        cases b with
        | true => simp [spec_ok]
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte]
          step as ⟨next,hn⟩
          apply append next hn
          have follows : OrderRangeSort.Ordered prev x := by intro h; cases cmp.mpr h
          intro y hy
          obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp hy
          rw [List.getElem_take] at eq
          have kp : k ≤ j.val := by simp at hk; omega
          subst y
          rcases eq_or_lt_of_le kp with eq | lt
          · simpa [eq,hp] using follows
          · apply OrderRangeSort.ordered_trans _ follows
            have before := List.pairwise_iff_getElem.mp order k j.val hk (by simp; scalar_tac) lt
            simpa only [List.getElem_take,hp] using before
      · step as ⟨next,hn⟩
        apply append next hn
        have zero : i.val = 0 := by scalar_tac
        simp [zero]
    · simp only [live,↓reduceIte,spec_ok]
      have all : buf.val.take i.val = buf.val := List.take_of_length_le (by scalar_tac)
      simpa only [all] using And.intro order valid
  · simp [inv]


/-- Both the filtered and the already-valid branch pass the same logical
    prefix to the in-place coalescer. Ranges outside the prefix are unused. -/
private theorem build_ordered_prefix (v input : Ranges) (n hint : Usize)
    (valid : ∀ r ∈ v.val.take n.val, r.start.val < r.end.val)
    (order : (v.val.take n.val).Pairwise OrderRangeSort.Ordered)
    (size : n.val ≤ v.length) (cap : n.val ≤ 2^30)
    (mem : ∀ c, inRangesList (v.val.take n.val) c ↔ inRangesList input.val c) :
    (do
      let (buf,used) ← if n < 2#usize then ok (v,n) else do
        let (k,w) ← order_range.coalesce_sorted_prefix v n
        ok (w,k)
      let out ← order_range.OrderRange.from_prefix buf used hint
      ok (core.result.Result.Ok out : core.result.Result order_range.OrderRange Ranges))
      ⦃ status => match status with
        | .Ok out => Canonical out ∧ ∀ c, inRanges out c ↔ inRangesList input.val c
        | .Err orig => orig = input ⦄ := by
  by_cases few : n < 2#usize
  · simp only [few,↓reduceIte,bind_ok]
    have cc : CanonicalList (v.val.take n.val) := by
      refine ⟨fun i hi => valid _ (List.getElem_mem hi),?_⟩
      intro i j lt hj
      simp only [List.length_take] at hj
      have small : n.val < 2 := by scalar_tac
      omega
    step with from_prefix_spec v n hint size cap cc as ⟨out,oc,view⟩
    exact ⟨oc,fun c => by simpa only [inRanges,view] using mem c⟩
  · simp only [few,↓reduceIte]
    step with coalesce_sorted_prefix_spec v n (by scalar_tac) size valid order as ⟨pair,sz,k,cc,eq⟩
    rcases pair with ⟨used,buf⟩
    dsimp only at sz k cc eq
    step with from_prefix_spec buf used hint (by omega) (by omega) cc as ⟨out,oc,view⟩
    exact ⟨oc,fun c => by simpa only [inRanges,view] using (eq c).trans (mem c)⟩

/-- The ordered fast path either returns the original input intact or constructs
    its canonical set of clocks. The unordered fallback can reuse that input. -/
theorem try_from_ordered_with_capacity_spec (v : Ranges) (hint : Usize) :
    order_range.OrderRange.try_from_ordered_with_capacity v hint ⦃ status => match status with
      | .Ok out => Canonical out ∧ ∀ c, inRanges out c ↔ inRangesList v.val c
      | .Err orig => orig = v ⦄ := by
  unfold order_range.OrderRange.try_from_ordered_with_capacity
  step with max_ranges_spec as ⟨limit,eq⟩
  by_cases large : v.len > limit
  · simp [large,spec_ok]
  · simp only [large,↓reduceIte]
    have len : v.len.val = v.length := by scalar_tac
    have cap : v.len.val ≤ 2^30 := by scalar_tac
    have full : v.val.take v.len.val = v.val := List.take_of_length_le (by scalar_tac)
    step with is_canonical_spec (alloc.vec.Vec.deref v) as ⟨canonical,check⟩
    cases canonical with
    | true =>
      simp only [↓reduceIte]
      step with from_prefix_spec v v.len hint (by omega) cap
        (by rw [full]; simpa [alloc.vec.Vec.deref] using check.mp rfl) as ⟨out,oc,view⟩
      exact ⟨oc,by simp only [inRanges,view,full,iff_self,implies_true]⟩
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte]
      step with ordered_filter_spec (alloc.vec.Vec.deref v) as ⟨status,scan⟩
      cases status with
      | none => simp [spec_ok]
      | some flag =>
        obtain ⟨ordered,valid⟩ := scan
        cases flag with
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte,bind_ok]
          exact build_ordered_prefix v v v.len hint
            (by rw [full]; simpa [alloc.vec.Vec.deref] using valid rfl)
            (by rw [full]; simpa [alloc.vec.Vec.deref] using ordered)
            (by omega) cap (by intro c; rw [full])
        | true =>
          simp only [↓reduceIte]
          step with OrderRangeSort.nonempty_prefix_spec v as ⟨pair,wl,fit,kept⟩
          rcases pair with ⟨n,w⟩
          dsimp only at wl fit kept
          change (do
            let (input,stop) ← ok (w,n)
            let (buf,used) ← if stop < 2#usize then ok (input,stop) else do
              let (k,b) ← order_range.coalesce_sorted_prefix input stop
              ok (b,k)
            let out ← order_range.OrderRange.from_prefix buf used hint
            ok (core.result.Result.Ok out : core.result.Result order_range.OrderRange Ranges)) ⦃ _ ⦄
          simp only [bind_ok]
          refine build_ordered_prefix w v n hint ?_ ?_ fit (by omega) ?_
          · rw [kept]
            intro x member
            simpa [OrderRangeSort.validRange] using (List.mem_filter.mp member).2
          · rw [kept]
            have order : v.val.Pairwise OrderRangeSort.Ordered := by
              simpa [alloc.vec.Vec.deref] using ordered
            exact order.sublist (List.filter_sublist ..)
          · intro c
            rw [kept,filter_members]

end YoctoCore.Properties.OrderRange
