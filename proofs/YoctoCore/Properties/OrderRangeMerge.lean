import YoctoCore.Properties.OrderRangeWindow
import YoctoCore.Properties.OrderRangeUnion

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.OrderRange

/-- A logarithmic scan estimate only influences which union algorithm runs.
    Its arithmetic is bounded even if every remaining item costs a full move. -/
private theorem span_spec (n : Std.Usize) (cap : n.val ≤ 2^30) :
    order_range.Ring.splice_loop4 0#u64 n ⦃ steps => steps.val ≤ 2*n.val ⦄ := by
  let inv : Std.U64 × Std.Usize → Prop := fun (s,k) => s.val+2*k.val ≤ 2*n.val
  unfold order_range.Ring.splice_loop4
  refine loop.spec_decr_nat (fun (_,k) => k.val) inv _ _ _ ?_ ?_
  · intro ⟨s,k⟩ h
    change s.val+2*k.val ≤ _ at h
    unfold order_range.Ring.splice_loop4.body
    simp only
    cases nz : k != 0#usize with
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte,spec_ok]
      omega
    | true =>
      simp only [↓reduceIte]
      have positive : 0 < k.val := by scalar_tac
      step as ⟨s',hs⟩
      step as ⟨k',hk⟩
      exact ⟨by change s'.val+2*k'.val ≤ _; scalar_tac,by scalar_tac⟩

  · change (0#u64).val + 2*n.val ≤ _
    scalar_tac

/-- After two disjoint incoming ranges have been located, at most one old
    range can touch both. Thus every previously removed fragment lies before
    the insertion point used by the next cost estimate. -/
private theorem removed_before {l : List order_range.ClockRange} (can : CanonicalList l)
    {first past rem : Nat} {r : order_range.ClockRange}
    (last : past ≤ l.length) (removal : rem ≤ first)
    (overlap : 1 < past-first)
    (inside : ∀ j, ∀ hj : j < l.length, first ≤ j → j < past → l[j].start.val ≤ r.end.val) :
    ∀ k, ∀ hk : k < l.length, k < rem+(past-first-1) → l[k].end.val < r.end.val := by
  intro k hk lt
  have j : k < past-1 := by omega
  have tail := inside (past-1) (by omega) (by omega) (by omega)
  have gap := can.2 k (past-1) j (by omega)
  omega

private theorem insert_batch_spec (r : order_range.Ring) (inc : order_range.OrderRange)
    (start finish : Std.Usize) (hr : ringWF r 0) (can : CanonicalList (ringList r))
    (hc : Canonical inc) (ab : start.val ≤ finish.val) (limit : finish.val ≤ (toList inc).length)
    (room : r.len.val + (finish.val-start.val) ≤ 2^30) :
    order_range.Ring.splice_loop6 r inc finish start ⦃ out =>
      RingUnion r (windowList (toList inc) start.val finish.val) out ⦄ := by
  let src := toList inc
  let inv : order_range.Ring × Std.Usize → Prop := fun (w,i) =>
    start.val ≤ i.val ∧ i.val ≤ finish.val ∧ RingUnion r (windowList src start.val i.val) w
  unfold order_range.Ring.splice_loop6
  refine loop.spec_decr_nat (fun (_,i) => finish.val-i.val) inv _ _ _ ?_ ?_
  · intro ⟨w,i⟩ ⟨lo,hi,u⟩
    unfold order_range.Ring.splice_loop6.body
    simp only
    by_cases live : i < finish
    · simp only [live,↓reduceIte]
      have ilt : i.val < src.length := by dsimp [src]; scalar_tac
      have xfit := hc.2.1 i.val ilt
      step with at_spec inc i hc.1 ilt as ⟨x,hx⟩
      step with max_ranges_spec as ⟨cap,eq⟩
      step with ring_try_insert_spec w x cap u.wf u.can (by simpa only [hx] using xfit) eq as ⟨s,w',e⟩
      have count := u.count
      have width : (windowList src start.val i.val).length = i.val-start.val := by
        simp [windowList, Nat.min_eq_left (Nat.le_of_lt ilt)]
      rw [width] at count
      cases s with
      | Err error =>
        obtain ⟨_,_,full⟩ := e
        exfalso
        scalar_tac
      | Ok _ =>
        simp only [core.result.Result.is_ok,massert,bind_ok,↓reduceIte]
        step as ⟨j,hj⟩
        refine ⟨⟨by omega,by scalar_tac,?_⟩,by scalar_tac⟩
        rw [hj,window_next src _ _ lo ilt,←hx]
        refine ⟨⟨e.head,e.fits,by have := e.positive; omega,e.bound⟩,e.canonical,?_,?_⟩
        · simp only [List.length_append,List.length_singleton,width]
          have := e.count
          omega
        · intro c
          rw [e.mem,u.mem,inRangesList_append,inRangesList_singleton]
          tauto
    · have endEq : i.val = finish.val := by scalar_tac
      simp only [live,↓reduceIte,spec_ok]
      simpa only [endEq] using u
  · exact ⟨Nat.le_refl _,ab, by rw [window_empty]; exact union_empty r hr can⟩

private def StartsCut (l : List order_range.ClockRange) (pivot : Std.U64) (k : Nat) : Prop :=
  k ≤ l.length ∧ (∀ j (hj : j < l.length), j < k → l[j].start.val ≤ pivot.val) ∧
    ∀ j (hj : j < l.length), k ≤ j → pivot.val < l[j].start.val

private def EndsCut (l : List order_range.ClockRange) (pivot : Std.U64) (base k : Nat) : Prop :=
  base ≤ k ∧ k ≤ l.length ∧ (∀ j (hj : j < l.length), base ≤ j → j < k → l[j].end.val < pivot.val) ∧
    ∀ j (hj : j < l.length), k ≤ j → pivot.val ≤ l[j].end.val

private theorem starts_cut_stop {l : List order_range.ClockRange} (c : CanonicalList l)
    (p : Std.U64) {k : Nat} (hi : k < l.length) (edge : p.val < l[k].start.val) :
    ∀ j (hj : j < l.length), k ≤ j → p.val < l[j].start.val := by
  intro j hj ge
  rcases eq_or_lt_of_le ge with rfl|lt
  · exact edge
  · exact Nat.lt_trans edge (canonicalList_start_lt c lt hj)

private theorem ends_cut_stop {l : List order_range.ClockRange} (c : CanonicalList l)
    (p : Std.U64) {k : Nat} (pos : 0 < k) (hi : k ≤ l.length)
    (edge : l[k-1].end.val < p.val) :
    ∀ j (hj : j < l.length), j < k → l[j].end.val < p.val := by
  intro j hj lt
  by_cases e : j = k-1
  · subst j; exact edge
  · have := canonicalList_end_lt c (show j < k-1 by omega) (show k-1 < l.length by omega)
    omega

private theorem front_incoming_scan (s : order_range.OrderRange) (count : Std.Usize) (p : Std.U64)
    (can : Canonical s) (full : count.val = (toList s).length) :
    order_range.Ring.splice_loop0 s count p 0#usize ⦃ k => StartsCut (toList s) p k.val ⦄ := by
  let l := toList s
  let inv := fun k : Std.Usize => k.val ≤ l.length ∧ ∀ j (hj : j < l.length), j < k.val → l[j].start.val ≤ p.val
  unfold order_range.Ring.splice_loop0
  refine loop.spec_decr_nat (fun k => count.val-k.val) inv _ _ _ ?_ ?_
  · intro k ⟨bound,seen⟩
    unfold order_range.Ring.splice_loop0.body
    by_cases live : k < count
    · simp only [live,↓reduceIte]
      have lt : k.val < l.length := by dsimp [l]; scalar_tac
      step with at_spec s k can.1 lt as ⟨x,hx⟩
      by_cases keep : x.start ≤ p
      · simp only [keep,↓reduceIte]
        step as ⟨k',hk⟩
        refine ⟨⟨by omega,?_⟩,by scalar_tac⟩
        intro j hj old
        by_cases e : j = k.val
        · subst j; rw [←hx]; scalar_tac
        · exact seen j hj (by omega)
      · simp only [keep,↓reduceIte,spec_ok]
        exact ⟨bound,seen,starts_cut_stop can.2 p lt (by rw [←hx]; scalar_tac)⟩
    · simp only [live,↓reduceIte,spec_ok]
      exact ⟨bound,seen,fun j hj ge => by dsimp [l] at *; scalar_tac⟩
  · simp [inv]

private theorem front_ring_scan (s : order_range.Ring) (p : Std.U64)
    (wf : ringWF s 0) (can : CanonicalList (ringList s)) :
    order_range.Ring.splice_loop1 s p 0#usize ⦃ (buf,head,len,k) =>
      buf = s.buf ∧ head = s.head ∧ len = s.len ∧ StartsCut (ringList s) p k.val ⦄ := by
  let l := ringList s
  let count := UScalar.cast .Usize s.len
  have full : count.val = l.length := by dsimp [l,count]; rw [ringList_length s wf]; scalar_tac
  let inv := fun k : Std.Usize => k.val ≤ l.length ∧ ∀ j (hj : j < l.length), j < k.val → l[j].start.val ≤ p.val
  unfold order_range.Ring.splice_loop1
  refine loop.spec_decr_nat (fun k => count.val-k.val) inv _ _ _ ?_ ?_
  · intro k ⟨bound,seen⟩
    unfold order_range.Ring.splice_loop1.body
    simp only [lift,bind_ok]
    by_cases live : k < UScalar.cast .Usize s.len
    · simp only [live,↓reduceIte]
      have lt : k.val < l.length := by dsimp [count] at full; scalar_tac
      step with ring_at_list_spec s wf k (by rwa [←ringList_length s wf]) as ⟨x,hx⟩
      by_cases keep : x.start ≤ p
      · simp only [keep,↓reduceIte]
        step as ⟨k',hk⟩
        refine ⟨⟨by omega,?_⟩,by scalar_tac⟩
        intro j hj old
        by_cases e : j = k.val
        · subst j; rw [←hx]; scalar_tac
        · exact seen j hj (by omega)
      · simp only [keep,↓reduceIte,spec_ok]
        exact ⟨by trivial,by trivial,by trivial,bound,seen,starts_cut_stop can p lt (by rw [←hx]; scalar_tac)⟩
    · simp only [live,↓reduceIte,spec_ok]
      exact ⟨rfl,rfl,rfl,bound,seen,fun j hj ge => by dsimp [l,count] at *; scalar_tac⟩
  · simp [inv]

private theorem back_incoming_scan (s : order_range.OrderRange) (base count : Std.Usize) (p : Std.U64)
    (can : Canonical s) (full : count.val = (toList s).length) (range : base ≤ count) :
    order_range.Ring.splice_loop2 s base p count ⦃ k => EndsCut (toList s) p base.val k.val ⦄ := by
  let l := toList s
  let inv := fun k : Std.Usize => base.val ≤ k.val ∧ k.val ≤ l.length ∧
    ∀ j (hj : j < l.length), k.val ≤ j → p.val ≤ l[j].end.val
  unfold order_range.Ring.splice_loop2
  refine loop.spec_decr_nat (fun k => k.val) inv _ _ _ ?_ ?_
  · intro k ⟨floor,bound,seen⟩
    unfold order_range.Ring.splice_loop2.body
    by_cases live : base < k
    · simp only [live,↓reduceIte]
      have pos : 0 < k.val := by scalar_tac
      step as ⟨t,ht⟩
      have idx : t.val < l.length := by omega
      step with at_spec s t can.1 idx as ⟨x,hx⟩
      by_cases keep : x.end ≥ p
      · simp only [keep,↓reduceIte,spec_ok]
        refine ⟨⟨by scalar_tac,by omega,?_⟩,by omega⟩
        intro j hj ge
        by_cases e : j = t.val
        · subst j; rw [←hx]; scalar_tac
        · exact seen j hj (by omega)
      · simp only [keep,↓reduceIte,spec_ok]
        have last : l[k.val-1].end.val < p.val := by
          have lt : l[t.val].end.val < p.val := by rw [←hx]; scalar_tac
          simpa only [ht] using lt
        exact ⟨floor,bound,fun j hj _ small => ends_cut_stop can.2 p pos bound last j hj small,seen⟩
    · simp only [live,↓reduceIte,spec_ok]
      exact ⟨floor,bound,fun j hj ge small => by scalar_tac,seen⟩
  · exact ⟨by scalar_tac,by dsimp [l]; omega,fun j hj ge => by dsimp [l] at hj; omega⟩

private theorem back_ring_scan (s : order_range.Ring) (count : Std.Usize) (p : Std.U64)
    (wf : ringWF s 0) (can : CanonicalList (ringList s)) (full : count.val = s.len.val) :
    order_range.Ring.splice_loop3 s.buf s.head s.len p count ⦃ k => EndsCut (ringList s) p 0 k.val ⦄ := by
  let l := ringList s
  have total : l.length = s.len.val := ringList_length s wf
  let inv := fun k : Std.Usize => 0 ≤ k.val ∧ k.val ≤ l.length ∧
    ∀ j (hj : j < l.length), k.val ≤ j → p.val ≤ l[j].end.val
  unfold order_range.Ring.splice_loop3
  refine loop.spec_decr_nat (fun k => k.val) inv _ _ _ ?_ ?_
  · intro k ⟨floor,bound,seen⟩
    unfold order_range.Ring.splice_loop3.body
    by_cases live : k > 0#usize
    · simp only [live,↓reduceIte]
      have pos : 0 < k.val := by scalar_tac
      step as ⟨t,ht⟩
      have idx : t.val < l.length := by omega
      step with ring_at_list_spec s wf t (by omega) as ⟨x,hx⟩
      by_cases keep : x.end ≥ p
      · simp only [keep,↓reduceIte,spec_ok]
        refine ⟨⟨by scalar_tac,by omega,?_⟩,by omega⟩
        intro j hj ge
        by_cases e : j = t.val
        · subst j; rw [←hx]; scalar_tac
        · exact seen j hj (by omega)
      · simp only [keep,↓reduceIte,spec_ok]
        have last : l[k.val-1].end.val < p.val := by
          have lt : l[t.val].end.val < p.val := by rw [←hx]; scalar_tac
          simpa only [ht] using lt
        exact ⟨floor,bound,fun j hj _ small => ends_cut_stop can p pos bound last j hj small,seen⟩
    · simp only [live,↓reduceIte,spec_ok]
      exact ⟨floor,bound,fun j hj ge small => by scalar_tac,seen⟩
  · exact ⟨by scalar_tac,by omega,fun j hj ge => by omega⟩

private theorem cost_scan_spec (r : order_range.Ring) (inc : order_range.OrderRange)
    (low high : Std.Usize) (window steps : Std.U64) (hw : ringWF r 0)
    (hc : CanonicalList (ringList r)) (ic : Canonical inc) (ord : low.val ≤ high.val)
    (endBound : high.val ≤ (toList inc).length)
    (room : r.len.val+(high.val-low.val) ≤ 2^30) (wBound : window.val ≤ 5*2^30)
    (sBound : steps.val ≤ 2*r.len.val) :
    order_range.Ring.splice_loop5 r.buf r.head r.len inc high window steps
      (UScalar.cast .Usize r.len) 0#usize 0#usize 0#u64 low ⦃ _ => True ⦄ := by
  let l := ringList r
  let src := toList inc
  have ll : l.length = r.len.val := ringList_length r hw
  let inv : Std.Usize × Std.Usize × Std.Usize × Std.U64 × Std.Usize → Prop :=
    fun (current,added,removed,_,i) =>
      low.val ≤ i.val ∧ i.val ≤ high.val ∧ added.val ≤ i.val-low.val ∧
      removed.val ≤ l.length ∧ current.val+removed.val = l.length+added.val ∧
      ∀ k (hk : k < l.length), k < removed.val →
        ∀ j (hj : j < src.length), i.val ≤ j → l[k].end.val < src[j].start.val
  unfold order_range.Ring.splice_loop5
  refine loop.spec_decr_nat (fun (_,_,_,_,i) => high.val-i.val) inv _ _ _ ?_ ?_
  · intro ⟨current,added,removed,cost,i⟩ ⟨floor,ceiling,addedBound,removedBound,total,old⟩
    unfold order_range.Ring.splice_loop5.body
    simp only
    by_cases live : i < high
    · simp only [live,↓reduceIte]
      by_cases within : cost ≤ window
      · simp only [within,↓reduceIte]
        have il : i.val < src.length := by dsimp [src]; scalar_tac
        have cap : r.len.val+added.val ≤ 2^30 := by omega
        have costCap : cost.val ≤ 5*2^30 := by scalar_tac
        step with at_spec inc i ic.1 il as ⟨x,hx⟩
        unfold order_range.Ring.upper
        simp only [lift,bind_ok]
        step with lower_partition_spec r hw x.start hc as ⟨first,firstBound,before,firstEnd⟩
        step with upper_partition_spec r hw x.end first firstBound hc as ⟨past,ab,lastBound,inside,after⟩
        change first.val ≤ l.length at firstBound
        change past.val ≤ l.length at lastBound
        have remFirst : removed.val ≤ first.val := by
          by_contra h
          have k : first.val < l.length := by omega
          have lhs := old _ k (by omega) _ il (Nat.le_refl _)
          have rhs := firstEnd first.val k (Nat.le_refl _)
          rw [hx] at rhs
          exact Nat.not_lt_of_ge rhs lhs
        step as ⟨overlap,ov⟩
        step as ⟨sum,base⟩
        let now := core.num.Usize.saturating_sub sum removed
        have nowEq : now.val = sum.val-removed.val := by
          change (sum.val-removed.val) % 2^System.Platform.numBits = _
          apply Nat.mod_eq_of_lt
          rcases System.Platform.numBits_eq with bits | bits <;> rw [bits] <;> omega
        have currentBound : current.val ≤ 2^30 := by omega
        have midFit : now.val+overlap.val ≤ current.val := by omega
        step as ⟨cost1,price⟩
        have costBound : cost1.val ≤ 7*2^30 := by omega
        have preserved (j : Std.Usize) (jj : j.val = i.val+1) :
            ∀ k (hk : k < l.length), k < removed.val →
              ∀ t (ht : t < src.length), j.val ≤ t → l[k].end.val < src[t].start.val :=
          fun k hk small t ht late => old k hk small t ht (by omega)
        by_cases disjoint : overlap = 0#usize
        · simp only [disjoint,↓reduceIte]
          step as ⟨rest,hrest⟩
          have minBound : (core.cmp.impls.OrdUsize.min now rest).val ≤ 2^30 := by
            unfold core.cmp.impls.OrdUsize.min; split <;> scalar_tac
          step as ⟨cost2,hCost⟩
          step as ⟨added',ha⟩
          step as ⟨current',hc'⟩
          step as ⟨j,hj⟩
          exact ⟨⟨by omega,by scalar_tac,by omega,removedBound,by omega,preserved j hj⟩,by scalar_tac⟩
        · simp only [disjoint,↓reduceIte]
          by_cases one : overlap = 1#usize
          · simp only [one,↓reduceIte]
            step as ⟨cost2,hCost⟩
            step as ⟨j,hj⟩
            exact ⟨⟨by omega,by scalar_tac,by omega,removedBound,total,preserved j hj⟩,by scalar_tac⟩
          · simp only [one,↓reduceIte]
            have several : 1 < overlap.val := by scalar_tac
            step as ⟨next,hnext⟩
            step as ⟨past',hp⟩
            step as ⟨rest,hrest⟩
            have small : (core.cmp.impls.OrdUsize.min next rest).val ≤ 2^30+1 := by
              unfold core.cmp.impls.OrdUsize.min; split <;> scalar_tac
            step as ⟨movement,hm⟩
            step as ⟨cost2,hCost⟩
            step as ⟨less,hn⟩
            step as ⟨rem,hr⟩
            step as ⟨cur,hc'⟩
            step as ⟨j,hj⟩
            refine ⟨⟨by omega,by scalar_tac,by omega,by omega,by omega,?_⟩,by scalar_tac⟩
            intro k hk prior t ht later
            have edge := removed_before hc lastBound remFirst (by omega) inside k hk (by omega)
            have gap := ic.2.2 i.val t (by omega) ht
            rw [hx] at edge
            exact Nat.lt_trans edge gap
      · simp only [within,↓reduceIte,spec_ok]
    · simp only [live,↓reduceIte,spec_ok]
  · simp only [inv]
    refine ⟨Nat.le_refl _,ord,by scalar_tac,by scalar_tac,by dsimp [l]; rw [ringList_length r hw]; scalar_tac,?_⟩
    intro k hk impossible
    scalar_tac

/-- It suffices to compare the two endpoints of a canonical incoming window
    with the old prefix and suffix. -/
private theorem splice_bounds {old src : List order_range.ClockRange} {lo hi a b : Nat}
    (can : CanonicalList src) (ab : a < b) (sb : b ≤ src.length)
    (left : ∀ i (h : i < old.length), i < lo → old[i].end.val < src[a].start.val)
    (right : ∀ i (h : i < old.length), hi ≤ i → src[b-1].end.val < old[i].start.val)
    (touch : ∀ (_ : b = a+1) (_ : lo < hi) (_ : hi ≤ old.length),
      src[a].start.val ≤ old[lo].end.val ∧ old[hi-1].start.val ≤ src[a].end.val) :
    WindowBounds old src lo hi a b := by
  constructor
  · intro x hx y hy
    obtain ⟨i,il,_,before,eq⟩ := window_member (a := 0) (by simpa [windowList] using hx : x ∈ windowList old 0 lo)
    obtain ⟨j,jl,aj,_,ey⟩ := window_member hy
    subst x; subst y
    have edge := left i il before
    rcases Nat.eq_or_lt_of_le aj with e|lt
    · subst j; exact edge
    · exact Nat.lt_trans edge (canonicalList_start_lt can lt jl)
  · intro x hx y hy
    obtain ⟨j,jl,_,jb,ex⟩ := window_member hx
    obtain ⟨k,hk,ey⟩ := List.mem_iff_getElem.mp hy
    have kl : hi+k < old.length := by simp only [List.length_drop] at hk; omega
    have e : old[hi+k] = y := by simpa only [List.getElem_drop] using ey
    subst x; subst y
    rw [List.getElem_drop]
    have edge := right (hi+k) kl (by omega)
    by_cases last : j = b-1
    · subst j; exact edge
    · exact Nat.lt_trans (canonicalList_end_lt can (show j < b-1 by omega) (by omega)) edge
  · intro one live bound _
    exact touch one live bound

private theorem join_union {r v w : order_range.Ring} {xs ys zs : List order_range.ClockRange}
    (first : RingUnion r xs v) (second : RingUnion v ys w)
    (size : xs.length+ys.length = zs.length)
    (cover : ∀ c, inRangesList xs c ∨ inRangesList ys c ↔ inRangesList zs c) : RingUnion r zs w := by
  refine ⟨second.wf,second.can,by have := first.count; have := second.count; omega,?_⟩
  intro c
  rw [second.mem,first.mem,or_assoc,cover]

private theorem join_windows (src : List order_range.ClockRange) (a b n : Nat) (ab : a ≤ b) (bn : b ≤ n) (fits : n ≤ src.length) :
    windowList src a b ++ windowList src b n = windowList src a n := by
  unfold windowList
  have p : (src.take n).take b = src.take b := by rw [List.take_take,Nat.min_eq_left bn]
  rw [←p,←List.drop_append_of_le_length (l₁ := (src.take n).take b)]
  · rw [List.take_append_drop]
  · simp only [List.length_take]; omega

private theorem join_adjacent {src : List order_range.ClockRange} {a b n : Nat}
    {r v w : order_range.Ring} (ab : a ≤ b) (bn : b ≤ n) (fits : n ≤ src.length)
    (first : RingUnion r (windowList src a b) v) (second : RingUnion v (windowList src b n) w) :
    RingUnion r (windowList src a n) w := by
  have h := join_windows src a b n ab bn fits
  apply join_union first second
  · simpa only [List.length_append] using congrArg List.length h
  · intro c; rw [←h,inRangesList_append]

private theorem join_reversed {src : List order_range.ClockRange} {a b n : Nat}
    {r v w : order_range.Ring} (ab : a ≤ b) (bn : b ≤ n) (fits : n ≤ src.length)
    (first : RingUnion r (windowList src b n) v) (second : RingUnion v (windowList src a b) w) :
    RingUnion r (windowList src a n) w := by
  have h := join_windows src a b n ab bn fits
  apply join_union first second
  · rw [Nat.add_comm]; simpa only [List.length_append] using congrArg List.length h
  · intro c; rw [←h,inRangesList_append,or_comm]

private def spliceMiddle (r : order_range.Ring) (inc : order_range.OrderRange) (low high : Std.Usize) : Result order_range.Ring := do
  if low = high
  then ok r
  else
    let n ← lift (UScalar.cast .Usize r.len)
    let cr4 ← order_range.OrderRange.at inc low
    let lo ← order_range.Ring.lower r cr4.start
    let i6 ← high - 1#usize
    let cr5 ← order_range.OrderRange.at inc i6
    let hi ← order_range.Ring.upper r cr5.end lo
    let i7 ← hi - lo
    let i8 ← lift (UScalar.cast .U64 i7)
    let i9 ← high - low
    let i10 ← lift (UScalar.cast .U64 i9)
    let i11 ← i8 + i10
    let i12 ← n - hi
    let i13 ← lift (core.cmp.impls.OrdUsize.min lo i12)
    let i14 ← lift (UScalar.cast .U64 i13)
    let i15 ← 3#u64 * i14
    let window ← i11 + i15
    let steps ← order_range.Ring.splice_loop4 0#u64 n
    let cost ←
      order_range.Ring.splice_loop5 r.buf r.head r.len
        inc high window steps n 0#usize 0#usize 0#u64 low
    if cost <= window
    then order_range.Ring.splice_loop6 r inc high low
    else order_range.Ring.merge_window r lo hi inc low high


private def spliceBack (r : order_range.Ring) (inc : order_range.OrderRange) (count low : Std.Usize) : Result order_range.Ring := do
  if low = count then ok r else
    let n ← lift (UScalar.cast .Usize r.len)
    let last ← n - 1#usize
    let x ← order_range.Ring.at r last
    let high ← order_range.Ring.splice_loop2 inc low x.start count
    if high < count then
      let y ← order_range.OrderRange.at inc high
      let stop ← lift (UScalar.cast .Usize r.len)
      let kept ← order_range.Ring.splice_loop3 r.buf r.head r.len y.start stop
      let stop' ← lift (UScalar.cast .Usize r.len)
      let out ← order_range.Ring.merge_window r kept stop' inc high count
      spliceMiddle out inc low high
    else spliceMiddle r inc low high

private theorem middle_spec (r : order_range.Ring) (inc : order_range.OrderRange) (low high : Std.Usize)
    (wf : ringWF r 0) (can : CanonicalList (ringList r)) (ic : Canonical inc)
    (ord : low.val ≤ high.val) (fits : high.val ≤ (toList inc).length)
    (room : r.len.val + (high.val-low.val) ≤ 2^30) :
    spliceMiddle r inc low high ⦃ out => RingUnion r (windowList (toList inc) low.val high.val) out ⦄ := by
  unfold spliceMiddle
  by_cases empty : low = high
  · simp only [empty,↓reduceIte,spec_ok,window_empty]
    exact union_empty _ wf can
  · simp only [empty,↓reduceIte,lift,bind_ok]
    have live : low.val < high.val := by scalar_tac
    have size := ringList_length r wf
    let n := UScalar.cast .Usize r.len
    have nn : n.val = r.len.val := by dsimp [n]; scalar_tac
    step with at_spec inc low ic.1 (by omega) as ⟨x,hx⟩
    unfold order_range.Ring.upper
    simp only [lift,bind_ok]
    step with lower_partition_spec r wf x.start can as ⟨lo,loFit,before,hitL⟩
    step as ⟨last,lastEq⟩
    step with at_spec inc last ic.1 (by omega) as ⟨y,hy⟩
    step with upper_partition_spec r wf y.end lo loFit can as ⟨hi,bounds,hiFit,hitR,after⟩
    have endEq : y = (toList inc)[high.val-1]' (by omega) := by simpa only [lastEq] using hy
    have edges : WindowBounds (ringList r) (toList inc) lo.val hi.val low.val high.val := by
      apply splice_bounds ic.2 live fits
      · simpa only [←hx] using before
      · simpa only [←endEq] using after
      · intro one ne endBound
        have e : high.val-1 = low.val := by omega
        constructor
        · simpa only [hx] using hitL lo.val (by omega) (Nat.le_refl _)
        · simpa only [endEq,e] using hitR (hi.val-1) (by omega) (by omega) (by omega)
    step as ⟨oldSize,os⟩
    step as ⟨newSize,ns⟩
    step as ⟨base,price⟩
    step as ⟨rest,rs⟩
    have minBound : (core.cmp.impls.OrdUsize.min lo rest).val ≤ r.len.val := by
      unfold core.cmp.impls.OrdUsize.min; split <;> scalar_tac
    step as ⟨movement,ms⟩
    step as ⟨window,ws⟩
    have wBound : window.val ≤ 5*2^30 := by scalar_tac
    step with span_spec n (by omega) as ⟨steps,sBound⟩
    step with cost_scan_spec r inc low high window steps wf can ic ord fits room wBound (by dsimp [n] at nn; scalar_tac) as ⟨cost⟩
    split
    · exact insert_batch_spec r inc low high wf can ic ord fits room
    · exact merge_window_spec r lo hi inc low high wf can ic bounds (by omega) ord fits room edges

private theorem back_spec (r : order_range.Ring) (inc : order_range.OrderRange) (count low : Std.Usize)
    (wf : ringWF r 0) (can : CanonicalList (ringList r)) (ic : Canonical inc)
    (ord : low.val ≤ count.val) (fits : count.val = (toList inc).length)
    (room : r.len.val + (count.val-low.val) ≤ 2^30) :
    spliceBack r inc count low ⦃ out => RingUnion r (windowList (toList inc) low.val count.val) out ⦄ := by
  unfold spliceBack
  by_cases empty : low = count
  · simp only [empty,↓reduceIte,spec_ok,window_empty]
    exact union_empty _ wf can
  · simp only [empty,↓reduceIte,lift,bind_ok]
    let n := UScalar.cast .Usize r.len
    have nn : n.val = r.len.val := by dsimp [n]; scalar_tac
    have size := ringList_length r wf
    have pos := wf.2.2.1
    step as ⟨last,lastEq⟩
    step with ring_at_list_spec r wf last (by scalar_tac) as ⟨x,hx⟩
    step with back_incoming_scan inc low count x.start ic fits (by scalar_tac) as ⟨high,h⟩
    obtain ⟨lowHigh,highCount,early,late⟩ := h
    by_cases suffix : high < count
    · simp only [suffix,↓reduceIte]
      have source : high.val < count.val := by scalar_tac
      step with at_spec inc high ic.1 (by omega) as ⟨y,hy⟩
      step with back_ring_scan r n y.start wf can nn as ⟨kept,hk⟩
      obtain ⟨_,endBound,before,touch⟩ := hk
      have edges : WindowBounds (ringList r) (toList inc) kept.val n.val high.val count.val := by
        apply splice_bounds ic.2 source (Nat.le_of_eq fits)
        · intro i fit prior; simpa only [hy] using before i fit (Nat.zero_le _) prior
        · intro i fit beyond; omega
        · intro one live _
          constructor
          · simpa only [hy] using touch kept.val (by omega) (Nat.le_refl _)
          · have edge := late high.val (by omega) (Nat.le_refl _)
            simpa only [hx,lastEq] using edge
      step with merge_window_spec r kept n inc high count wf can ic (by omega) (by omega)
        (by omega) (by omega) (by omega) edges as ⟨w,u⟩
      have cw := u.count
      simp only [windowList,List.length_drop,List.length_take,Nat.min_eq_left (Nat.le_of_eq fits)] at cw
      exact spec_mono (middle_spec w inc low high u.wf u.can ic lowHigh highCount (by omega))
        (fun _ v => join_reversed lowHigh (by omega) (Nat.le_of_eq fits) u v)
    · have eq : high = count := by scalar_tac
      subst high
      simp only [suffix,↓reduceIte]
      exact middle_spec r inc low count wf can ic ord (Nat.le_of_eq fits) room

private theorem splice_spec (r : order_range.Ring) (inc : order_range.OrderRange)
    (wf : ringWF r 0) (can : CanonicalList (ringList r)) (ic : Canonical inc)
    (room : r.len.val+(toList inc).length ≤ 2^30) :
    order_range.Ring.splice r inc ⦃ w => RingUnion r (toList inc) w ⦄ := by
  unfold order_range.Ring.splice
  -- Aeneas emits a fresh loop name for each syntactic copy of the continuation.
  -- The corresponding loop bodies and initial states are identical.
  have same7 : order_range.Ring.splice_loop7 = order_range.Ring.splice_loop4 := by
    have body : order_range.Ring.splice_loop7.body = order_range.Ring.splice_loop4.body := rfl
    unfold order_range.Ring.splice_loop7 order_range.Ring.splice_loop4
    rw [body]
  have same8 : order_range.Ring.splice_loop8 = order_range.Ring.splice_loop5 := by
    have body : order_range.Ring.splice_loop8.body = order_range.Ring.splice_loop5.body := rfl
    unfold order_range.Ring.splice_loop8 order_range.Ring.splice_loop5
    rw [body]
  have same9 : order_range.Ring.splice_loop9 = order_range.Ring.splice_loop6 := by
    have body : order_range.Ring.splice_loop9.body = order_range.Ring.splice_loop6.body := rfl
    unfold order_range.Ring.splice_loop9 order_range.Ring.splice_loop6
    rw [body]
  have same10 : order_range.Ring.splice_loop10 = order_range.Ring.splice_loop2 := by
    have body : order_range.Ring.splice_loop10.body = order_range.Ring.splice_loop2.body := rfl
    unfold order_range.Ring.splice_loop10 order_range.Ring.splice_loop2
    rw [body]
  have same11 : order_range.Ring.splice_loop11 = order_range.Ring.splice_loop3 := by
    have body : order_range.Ring.splice_loop11.body = order_range.Ring.splice_loop3.body := rfl
    unfold order_range.Ring.splice_loop11 order_range.Ring.splice_loop3
    rw [body]
  have same12 : order_range.Ring.splice_loop12 = order_range.Ring.splice_loop4 := by
    have body : order_range.Ring.splice_loop12.body = order_range.Ring.splice_loop4.body := rfl
    unfold order_range.Ring.splice_loop12 order_range.Ring.splice_loop4
    rw [body]
  have same13 : order_range.Ring.splice_loop13 = order_range.Ring.splice_loop5 := by
    have body : order_range.Ring.splice_loop13.body = order_range.Ring.splice_loop5.body := rfl
    unfold order_range.Ring.splice_loop13 order_range.Ring.splice_loop5
    rw [body]
  have same14 : order_range.Ring.splice_loop14 = order_range.Ring.splice_loop6 := by
    have body : order_range.Ring.splice_loop14.body = order_range.Ring.splice_loop6.body := rfl
    unfold order_range.Ring.splice_loop14 order_range.Ring.splice_loop6
    rw [body]
  have same15 : order_range.Ring.splice_loop15 = order_range.Ring.splice_loop4 := by
    have body : order_range.Ring.splice_loop15.body = order_range.Ring.splice_loop4.body := rfl
    unfold order_range.Ring.splice_loop15 order_range.Ring.splice_loop4
    rw [body]
  have same16 : order_range.Ring.splice_loop16 = order_range.Ring.splice_loop5 := by
    have body : order_range.Ring.splice_loop16.body = order_range.Ring.splice_loop5.body := rfl
    unfold order_range.Ring.splice_loop16 order_range.Ring.splice_loop5
    rw [body]
  have same17 : order_range.Ring.splice_loop17 = order_range.Ring.splice_loop6 := by
    have body : order_range.Ring.splice_loop17.body = order_range.Ring.splice_loop6.body := rfl
    unfold order_range.Ring.splice_loop17 order_range.Ring.splice_loop6
    rw [body]
  simp only [same7, same8, same9, same10, same11, same12, same13, same14, same15, same16, same17]
  have full (n : Nat) (hn : n = (toList inc).length) :
      windowList (toList inc) 0 n = toList inc := by simp [windowList,hn]
  have pos := wf.2.2.1
  have size := ringList_length r wf
  have zero : (0#usize).val = 0 := by decide
  step with len_spec inc ic.1 as ⟨count,cn⟩
  step with ring_at_list_spec r wf 0#usize (by scalar_tac) as ⟨first,hf⟩
  step with front_incoming_scan inc count first.end ic cn as ⟨low,lc⟩
  obtain ⟨lowBound,left,incomingAfter⟩ := lc
  by_cases active : low > 0#usize
  · simp only [active,↓reduceIte]
    have lp : 0 < low.val := by scalar_tac
    step as ⟨last,lastEq⟩
    step with at_spec inc last ic.1 (by omega) as ⟨x,hx⟩
    step with front_ring_scan r x.end wf can as ⟨buf,head,n,joined,bufEq,headEq,numEq,cut⟩
    subst buf; subst head; subst n
    obtain ⟨bound,hit,after⟩ := cut
    have edges : WindowBounds (ringList r) (toList inc) 0 joined.val 0 low.val := by
      apply splice_bounds ic.2 lp lowBound
      · intro i _ h; omega
      · intro i il ge
        simpa only [hx,lastEq] using after i il ge
      · intro one live stop
        constructor
        · simpa only [hf,zero] using left 0 (by omega) lp
        · have eq : last.val = 0 := by omega
          simpa only [hx,eq] using hit (joined.val-1) (by omega) (by omega)
    step with merge_window_spec r 0#usize joined inc 0#usize low wf can ic (by scalar_tac)
      (by omega) (by scalar_tac) lowBound (by scalar_tac) edges as ⟨s,u⟩
    have countBound := u.count
    simp only [windowList,List.drop_zero,List.length_take,Nat.min_eq_left lowBound] at countBound
    change spliceBack s inc count low ⦃ w => RingUnion r (toList inc) w ⦄
    refine spec_mono (back_spec s inc count low u.wf u.can ic (by omega) cn (by omega)) ?_
    intro out v
    have all := join_adjacent (a := 0) (Nat.zero_le _) (by omega) (Nat.le_of_eq cn) u v
    simpa only [full count.val cn] using all
  · simp only [active,↓reduceIte]
    have lz : low.val = 0 := by scalar_tac
    change spliceBack r inc count low ⦃ w => RingUnion r (toList inc) w ⦄
    exact spec_mono (back_spec r inc count low wf can ic (by omega) cn (by omega))
      (fun _ h => by simpa only [lz,full count.val cn] using h)

def UnionPost (a b out : order_range.OrderRange) : Prop :=
  Canonical out ∧ (toList out).length ≤ (toList a).length + (toList b).length ∧
  ∀ c, inRanges out c ↔ inRanges a c ∨ inRanges b c

private theorem union_swap {a b v : order_range.OrderRange} (h : UnionPost a b v) : UnionPost b a v :=
  ⟨h.1,by simpa only [Nat.add_comm] using h.2.1,fun c => (h.2.2 c).trans or_comm⟩

private theorem insert_inline (r : order_range.OrderRange) (a : Array order_range.ClockRange 1#usize)
    (x : order_range.ClockRange) (items : a.val = [x]) (hc : Canonical r)
    (room : (toList r).length+(toList ⟨.Single a⟩).length ≤ 2^30) :
    order_range.OrderRange.insert r x.start x.end ⦃ out => UnionPost r ⟨.Single a⟩ out ⦄ := by
  by_cases valid : x.start.val < x.end.val
  · have inline : toList ⟨.Single a⟩ = [x] := by simp [toList,items,valid]
    rw [inline,List.length_singleton] at room
    refine spec_mono (insert_spec r x.start x.end hc (by omega)) ?_
    intro out ⟨oc,count,mem⟩
    exact ⟨oc,by simpa only [inline,List.length_singleton] using count,fun c => by
      simpa only [inRanges,inline,inRangesList_singleton] using mem c⟩
  · have empty : x.start ≥ x.end := by scalar_tac
    have inline : toList ⟨.Single a⟩ = [] := by simp [toList,items,valid]
    unfold order_range.OrderRange.insert order_range.OrderRange.try_insert
    simp [empty,core.result.Result.is_ok,massert,bind_ok,spec_ok,UnionPost,hc,inRanges,inline,inRangesList_iff_mem]

private theorem inline_union (r : order_range.OrderRange) (a : Array order_range.ClockRange 1#usize)
    (hr : Canonical r) (room : (toList r).length+(toList ⟨.Single a⟩).length ≤ 2^30) :
    (do let x ← Array.index_usize a 0#usize
        order_range.OrderRange.insert r x.start x.end) ⦃ out => UnionPost r ⟨.Single a⟩ out ⦄ := by
  obtain ⟨x,items⟩ := single_val a
  step as ⟨y,hy⟩
  have eq : y = x := by simpa [items] using hy
  rw [eq]
  exact insert_inline r a x items hr room

private theorem merge_with_room_spec (self other : order_range.OrderRange) (hc : Canonical self)
    (oc : Canonical other) (room : (toList self).length+(toList other).length ≤ 2^30) :
    order_range.OrderRange.merge_with_room self other ⦃ out =>
      Canonical out ∧ (toList out).length ≤ (toList self).length+(toList other).length ∧
      ∀ c, inRanges out c ↔ inRanges self c ∨ inRanges other c ⦄ := by
  unfold order_range.OrderRange.merge_with_room
  step with partial_eq_spec self other hc.1 oc.1 as ⟨same,eq⟩
  by_cases equal : same = true
  · simp only [equal,↓reduceIte,spec_ok]
    have list := eq.mp equal
    exact ⟨hc,by omega,fun c => by simp [inRanges,list]⟩
  have no : same = false := Bool.eq_false_iff.mpr equal
  simp only [no, Bool.false_eq_true, ↓reduceIte]
  rcases other with ⟨a|s⟩
  · exact inline_union self a hc room
  · rcases self with ⟨a|r⟩
    · simp only
      obtain ⟨x,items⟩ := single_val a
      step as ⟨old,ho⟩
      have e : old = x := by simpa [items] using ho
      unfold order_range.OrderRange.Insts.CoreCloneClone.clone order_range.Repr.Insts.CoreCloneClone.clone
      simp only
      step with ring_clone_spec s oc.1 as ⟨copy,wf,list⟩
      have cloneCan : Canonical ⟨.Many copy⟩ := ⟨wf,by simpa only [toList,list] using oc.2⟩
      have same : toList ⟨.Many copy⟩ = toList ⟨.Many s⟩ := list
      simp only [e]
      refine spec_mono (insert_inline ⟨.Many copy⟩ a x items cloneCan (by rw [same]; omega)) ?_
      intro out h
      have rev := union_swap h
      simpa only [UnionPost,inRanges,same] using rev
    · simp only
      have ws : ringWF r := hc.1
      have simple : ringWF r 0 := ⟨ws.1,ws.2.1,by have := ws.2.2.1; omega,ws.2.2.2⟩
      have len := ringList_length r ws
      step with splice_spec r ⟨.Many s⟩ simple hc.2 oc (by simpa only [toList,len] using room) as ⟨w,u⟩
      have wl := ringList_length w u.wf
      by_cases one : w.len = 1#u32
      · simp only [one,↓reduceIte]
        have wn : w.len.val = 1 := by rw [one]; decide
        step with ring_at_list_spec w u.wf 0#usize (by scalar_tac) as ⟨x,hx⟩
        have list : ringList w = [x] := by
          cases eq : ringList w with
          | nil => simp [eq] at wl; omega
          | cons y ys =>
            have yy : x = y := by simpa [eq] using hx
            have nil : ys.length = 0 := by simp [eq] at wl; omega
            simp [yy,List.length_eq_zero_iff.mp nil]
        have valid := u.can.1 0 (by simp [list])
        have ⟨can,view⟩ := single_valid_list (Array.make 1#usize [x]) x rfl (by simpa [list] using valid)
        have n := u.count
        refine ⟨can,?_,?_⟩
        · rw [view,List.length_singleton]
          simpa only [toList,len,wn] using n
        · intro c
          change inRangesList (toList _) c ↔ _
          rw [view]
          simpa only [inRanges,toList,list] using u.mem c
      · simp only [one,↓reduceIte,spec_ok]
        have enough : 2 ≤ w.len.val := by have := u.wf.2.2.1; scalar_tac
        exact ⟨⟨⟨u.wf.1,u.wf.2.1,enough,u.wf.2.2.2⟩,u.can⟩,
          by simpa only [toList,wl,len] using u.count,u.mem⟩

private theorem canonical_size (r : order_range.OrderRange) (wf : storageWF r) :
    (toList r).length ≤ 2^30 := by
  rcases r with ⟨a|ring⟩
  · obtain ⟨x,h⟩ := single_val a
    change (a.val.filter _).length ≤ _
    exact (List.length_filter_le ..).trans (by rw [h,List.length_singleton]; decide)
  · change (ringList ring).length ≤ _
    rw [ringList_length ring wf]
    exact wf.2.1.trans wf.2.2.2

/-- Public merges test the size of the canonical union and preserve the entire receiver on rejection. -/
def TryUnionPost (self : order_range.OrderRange) (src : ClockList) (limit : Nat)
    (result : core.result.Result Unit CodecError × order_range.OrderRange) : Prop :=
  (result.1 = .Ok () ↔ UnionFits (toList self) src limit) ∧
    match result.1 with
    | .Ok _ => Canonical result.2 ∧ ∀ c, inRanges result.2 c ↔ inRanges self c ∨ inRangesList src c
    | .Err e => e = CodecError.LimitExceeded ∧ result.2 = self

private theorem try_sliced_merge (self other : order_range.OrderRange) (limit : Usize)
    (hc : Canonical self) (oc : Canonical other) (cap : limit.val ≤ 2^30) :
    (do let (first,second) ← order_range.OrderRange.as_slices other
        order_range.OrderRange.try_union_slices self first second limit)
      ⦃ res => TryUnionPost self (toList other) limit.val res ⦄ := by
  step with as_slices_spec other oc.1 as ⟨first,second,view⟩
  have sum := congrArg List.length view
  rw [List.length_append] at sum
  have bound := canonical_size other oc.1
  have fits : first.length+second.length ≤ Usize.max := by scalar_tac
  refine spec_mono (try_union_slices_spec self first second limit hc
    (by rw [view]; exact oc.2) fits cap) ?_
  rintro ⟨status,out⟩ ⟨accepted,result⟩
  rw [view] at accepted result
  exact ⟨accepted,by cases status <;> exact result⟩

private theorem try_fast_ok {self other out : order_range.OrderRange} {cap : Nat}
    (h : UnionPost self other out) (room : (toList self).length+(toList other).length ≤ cap) :
    TryUnionPost self (toList other) cap (.Ok (),out) := by
  have fits : UnionFits (toList self) (toList other) cap :=
    ⟨toList out,h.1.2,h.2.1.trans room,h.2.2⟩
  exact ⟨⟨fun _ => fits,fun _ => rfl⟩,h.1,h.2.2⟩

theorem try_merge_from_spec (self other : order_range.OrderRange) (hc : Canonical self) (oc : Canonical other) :
    order_range.OrderRange.try_merge_from self other ⦃ res => TryUnionPost self (toList other) (2^30) res ⦄ := by
  unfold order_range.OrderRange.try_merge_from
  have size := canonical_size self hc.1
  step with len_spec other oc.1 as ⟨m,hm⟩
  step with len_spec self hc.1 as ⟨n,hn⟩
  step with max_ranges_spec as ⟨cap,eq⟩
  step as ⟨space,hs⟩
  split
  · simpa only [eq] using try_sliced_merge self other cap hc oc (by omega)
  · have room : (toList self).length+(toList other).length ≤ 2^30 := by scalar_tac
    step with merge_with_room_spec self other hc oc room as ⟨out,can,bound,mem⟩
    exact try_fast_ok ⟨can,bound,mem⟩ room

private theorem checked_success (out : order_range.OrderRange) {Q : order_range.OrderRange → Prop}
    (h : Q out) :
    (do let b ← core.result.Result.is_ok (.Ok () : core.result.Result Unit CodecError)
        massert b
        ok out) ⦃ Q ⦄ := by
  simpa [core.result.Result.is_ok,massert,bind_ok,spec_ok] using h

theorem merge_from_final_spec (self other : order_range.OrderRange) (hc : Canonical self)
    (oc : Canonical other) (fits : UnionFits (toList self) (toList other) (2^30)) :
    order_range.OrderRange.merge_from self other ⦃ out => UnionPost self other out ⦄ := by
  unfold order_range.OrderRange.merge_from
  apply spec_bind (try_merge_from_spec self other hc oc)
  rintro ⟨status,out⟩ h
  have good := h.1.mpr fits
  change status = _ at good
  subst status
  apply checked_success out
  obtain ⟨c,mem⟩ := h.2
  exact ⟨c,canonical_union_count hc.2 oc.2 c.2 mem,mem⟩

theorem merge_from_spec (self other : order_range.OrderRange) (hc : Canonical self)
    (oc : Canonical other) (room : (toList self).length+(toList other).length ≤ 2^30) :
    order_range.OrderRange.merge_from self other ⦃ out => UnionPost self other out ⦄ :=
  merge_from_final_spec self other hc oc (unionFits_of_room hc.2 oc.2 room)

theorem merge_spec (self other : order_range.OrderRange) (hc : Canonical self)
    (oc : Canonical other) (room : (toList self).length+(toList other).length ≤ 2^30) :
    order_range.OrderRange.merge self other ⦃ out => Canonical out ∧
      (toList out).length ≤ (toList self).length+(toList other).length ∧
      ∀ c, inRanges out c ↔ inRanges self c ∨ inRanges other c ⦄ := merge_from_spec self other hc oc room

theorem try_merge_owned_spec (self other : order_range.OrderRange) (hc : Canonical self) (oc : Canonical other) :
    order_range.OrderRange.try_merge_owned self other ⦃ res => TryUnionPost self (toList other) (2^30) res ⦄ := by
  unfold order_range.OrderRange.try_merge_owned
  have size := canonical_size self hc.1
  step with len_spec other oc.1 as ⟨m,hm⟩
  step with len_spec self hc.1 as ⟨n,hn⟩
  step with max_ranges_spec as ⟨cap,eq⟩
  step as ⟨space,hs⟩
  split
  · simpa only [eq] using try_sliced_merge self other cap hc oc (by omega)
  · have room : (toList self).length+(toList other).length ≤ 2^30 := by scalar_tac
    rcases self with ⟨a|r⟩
    · obtain ⟨x,items⟩ := single_val a
      dsimp only
      step as ⟨old,ho⟩
      have equal : old = x := by simpa [items] using ho
      rw [equal]
      step with insert_inline other a x items oc (by omega) as ⟨out,h⟩
      exact try_fast_ok (union_swap h) room
    · step with merge_with_room_spec ⟨.Many r⟩ other hc oc room as ⟨out,can,bound,mem⟩
      exact try_fast_ok ⟨can,bound,mem⟩ room

theorem merge_owned_final_spec (self other : order_range.OrderRange) (hc : Canonical self)
    (oc : Canonical other) (fits : UnionFits (toList self) (toList other) (2^30)) :
    order_range.OrderRange.merge_owned self other ⦃ out => UnionPost self other out ⦄ := by
  unfold order_range.OrderRange.merge_owned
  apply spec_bind (try_merge_owned_spec self other hc oc)
  rintro ⟨status,out⟩ h
  have good := h.1.mpr fits
  change status = _ at good
  subst status
  apply checked_success out
  obtain ⟨can,mem⟩ := h.2
  exact ⟨can,canonical_union_count hc.2 oc.2 can.2 mem,mem⟩

theorem merge_owned_spec (self other : order_range.OrderRange) (hc : Canonical self)
    (oc : Canonical other) (room : (toList self).length+(toList other).length ≤ 2^30) :
    order_range.OrderRange.merge_owned self other ⦃ out => Canonical out ∧
      (toList out).length ≤ (toList self).length+(toList other).length ∧
      ∀ c, inRanges out c ↔ inRanges self c ∨ inRanges other c ⦄ :=
  merge_owned_final_spec self other hc oc (unionFits_of_room hc.2 oc.2 room)

private theorem raw_ok (self out : order_range.OrderRange) (xs : ClockList) (limit : Nat)
    (can : Canonical out) (size : (toList out).length ≤ limit)
    (mem : ∀ c, inRanges out c ↔ inRanges self c ∨ inRangesList xs c) :
    TryUnionPost self xs limit (.Ok (),out) :=
  ⟨⟨fun _ => ⟨toList out,can.2,size,mem⟩,fun _ => rfl⟩,can,mem⟩

private theorem extend_by_union (self : order_range.OrderRange) (v : Ranges) (limit : Usize)
    (can : Canonical self) (cap : limit.val ≤ 2^30) :
    (do let (n,w) ← order_range.canonicalize v
        let s ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice _) w ⟨n⟩
        let empty ← lift (Array.to_slice (Std.Array.empty order_range.ClockRange))
        order_range.OrderRange.try_union_slices self s empty limit)
      ⦃ r => TryUnionPost self v.val limit.val r ⦄ := by
  step with canonicalize_spec v as ⟨n,w,_,bound,canonical,mem⟩
  step as ⟨s,view,_⟩
  let empty := Array.to_slice (Std.Array.empty order_range.ClockRange)
  have ev : empty.val = [] := by simp [empty,Std.Array.empty,Array.to_slice]
  have incomingView : s.val ++ empty.val = w.val.take n.val := by simp [ev,view,List.slice]
  have same := unionFits_congr_right (old := toList self) limit.val mem
  simp only [lift,bind_ok]
  apply spec_mono (try_union_slices_spec self s empty limit can (by rw [incomingView]; exact canonical)
    (by change s.val.length + empty.val.length ≤ _; rw [ev]; simpa using s.bound) cap)
  rintro ⟨status,out⟩ ⟨accept,result⟩
  rw [incomingView] at accept result
  refine ⟨accept.trans same,?_⟩
  cases status with
  | Err e => exact result
  | Ok u => exact ⟨result.1,fun c => (result.2 c).trans (or_congr Iff.rfl (mem c))⟩

theorem try_extend_vec_with_limit_spec (self : order_range.OrderRange) (v : Ranges) (hint limit : Usize)
    (can : Canonical self) :
    order_range.OrderRange.try_extend_vec_with_limit self v hint limit
      ⦃ res => TryUnionPost self v.val (min limit.val (2^30)) res ⦄ := by
  unfold order_range.OrderRange.try_extend_vec_with_limit
  step with max_ranges_spec as ⟨top,ht⟩
  let cap := core.cmp.impls.OrdUsize.min limit top
  have hc : cap.val = min limit.val (2^30) := by
    unfold cap core.cmp.impls.OrdUsize.min
    split <;> scalar_tac
  simp only [lift,bind_ok]
  step with len_spec self can.1 as ⟨n,hn⟩
  have slow := extend_by_union self v cap can (by omega)
  simp only [hc,lift,bind_ok] at slow
  split
  · exact slow
  · rename_i large
    step as ⟨room,hr⟩
    by_cases overflow : v.len > room
    · simp only [overflow,↓reduceIte]; exact slow
    · simp only [overflow,↓reduceIte]
      have len : v.len.val = v.length := by scalar_tac
      have fits : (toList self).length + v.length ≤ min limit.val (2^30) := by scalar_tac
      split
      · have empty : v.val = [] := List.length_eq_zero_iff.mp (by scalar_tac)
        apply (spec_ok _).mpr
        exact raw_ok self self v.val (min limit.val (2^30)) can (by omega) (by simp [empty,inRangesList_iff_mem])
      · have lengthOne : v.val.length = 1 := by scalar_tac
        step as ⟨x,hx⟩
        have one : v.val = [x] := by
          cases eq : v.val with
          | nil => simp [eq] at lengthOne
          | cons a tail =>
            have ax : x = a := by simpa [eq] using hx
            have z : tail.length = 0 := by simpa [eq] using lengthOne
            simp [ax,List.length_eq_zero_iff.mp z]
        step with insert_spec self x.start x.end can (by omega) as ⟨out,oc,num,mem⟩
        exact raw_ok self out v.val (min limit.val (2^30)) oc (by omega) (by simpa only [one,inRangesList_singleton] using mem)
      · unfold order_range.OrderRange.from_vec_with_capacity
        step with canonicalize_spec v as ⟨pair,wl,limitN,wc,mem⟩
        rcases pair with ⟨num,w⟩
        change w.length = v.length at wl
        change num.val ≤ w.length at limitN
        step with from_prefix_spec w num hint limitN (by omega) wc as ⟨other,oc,view⟩
        have count : (toList other).length ≤ v.length := by rw [view,List.length_take]; omega
        step with merge_owned_spec self other can oc (by omega) as ⟨out,c,bound,h⟩
        exact raw_ok self out v.val (min limit.val (2^30)) c (by omega) (by simpa only [inRanges,view,mem] using h)

theorem try_extend_vec_with_capacity_spec (self : order_range.OrderRange) (v : Ranges)
    (hint : Usize) (can : Canonical self) :
    order_range.OrderRange.try_extend_vec_with_capacity self v hint
      ⦃ r => TryUnionPost self v.val (2^30) r ⦄ := by
  unfold order_range.OrderRange.try_extend_vec_with_capacity
  step with max_ranges_spec as ⟨cap,hc⟩
  simpa only [hc,min_self] using try_extend_vec_with_limit_spec self v hint cap can

theorem extend_vec_final_spec (self : order_range.OrderRange) (v : Ranges) (hint : Usize)
    (can : Canonical self) (fits : UnionFits (toList self) v.val (2^30)) :
    order_range.OrderRange.extend_vec_with_capacity self v hint
      ⦃ out => Canonical out ∧ ∀ c, inRanges out c ↔ inRanges self c ∨ inRangesList v.val c ⦄ := by
  unfold order_range.OrderRange.extend_vec_with_capacity
  apply spec_bind (try_extend_vec_with_capacity_spec self v hint can)
  rintro ⟨status,out⟩ h
  have ok := h.1.mpr fits
  change status = _ at ok
  subst status
  exact checked_success out h.2

theorem extend_vec_with_capacity_spec (self : order_range.OrderRange) (v : Ranges) (hint : Std.Usize)
    (can : Canonical self) (room : (toList self).length+v.length ≤ 2^30) :
    order_range.OrderRange.extend_vec_with_capacity self v hint ⦃ out => Canonical out ∧
      (toList out).length ≤ (toList self).length+v.length ∧
      ∀ c, inRanges out c ↔ inRanges self c ∨ inRangesList v.val c ⦄ := by
  have witness : ∃ inc : ClockList, CanonicalList inc ∧ inc.length ≤ v.length ∧
      ∀ c, inRangesList inc c ↔ inRangesList v.val c := by
    have h := canonicalize_spec v
    cases e : order_range.canonicalize v with
    | ret pair =>
      rcases pair with ⟨n,w⟩
      rw [e] at h
      obtain ⟨size,fit,c,sem⟩ := (spec_ok _).mp h
      exact ⟨_,c,by rw [List.length_take]; omega,sem⟩
    | vis i k => rw [e] at h; exact ((spec_vis i k).mp h).elim
    | div => rw [e] at h; exact (spec_div.mp h).elim
  obtain ⟨inc,ci,length,same⟩ := witness
  have fits := (unionFits_congr_right (old := toList self) (2^30) same).mp
    (unionFits_of_room can.2 ci (by omega))
  refine spec_mono (extend_vec_final_spec self v hint can fits) ?_
  rintro out ⟨oc,sem⟩
  have bound := canonical_union_count can.2 ci oc.2
    (fun c => (sem c).trans (or_congr Iff.rfl (same c).symm))
  exact ⟨oc,by omega,sem⟩

theorem extend_vec_spec (self : order_range.OrderRange) (v : Ranges)
    (can : Canonical self) (room : (toList self).length+v.length ≤ 2^30) :
    order_range.OrderRange.extend_vec self v ⦃ out => Canonical out ∧
      (toList out).length ≤ (toList self).length+v.length ∧
      ∀ c, inRanges out c ↔ inRanges self c ∨ inRangesList v.val c ⦄ :=
  extend_vec_with_capacity_spec self v 0#usize can room

theorem merge_comm (a b : order_range.OrderRange) (ha : Canonical a) (hb : Canonical b)
    (room : (toList a).length+(toList b).length ≤ 2^30) :
    (do let ab ← order_range.OrderRange.merge a b; let ba ← order_range.OrderRange.merge b a
        ok (ab,ba)) ⦃ (ab,ba) => ∀ c, inRanges ab c ↔ inRanges ba c ⦄ := by
  step with merge_spec a b ha hb room as ⟨ab,_,_,hab⟩
  step with merge_spec b a hb ha (by omega) as ⟨ba,_,_,hba⟩
  intro c
  rw [hab,hba,or_comm]

theorem merge_idem (a : order_range.OrderRange) (ha : Canonical a)
    (room : (toList a).length+(toList a).length ≤ 2^30) :
    order_range.OrderRange.merge a a ⦃ out => ∀ c, inRanges out c ↔ inRanges a c ⦄ := by
  refine spec_mono (merge_spec a a ha ha room) ?_
  intro out h c
  simpa only [or_self] using h.2.2 c

end YoctoCore.Properties.OrderRange
