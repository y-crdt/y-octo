import Aeneas
import YoctoCore.Code.Funs
import YoctoCore.Properties.OrderRangeHeap

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.OrderRangeSort

abbrev Ranges := alloc.vec.Vec order_range.ClockRange

def Earlier (a b : order_range.ClockRange) : Prop :=
  a.start.val < b.start.val ∨ (a.start.val = b.start.val ∧ a.end.val < b.end.val)

theorem before_spec (a b : order_range.ClockRange) :
    order_range.before a b ⦃ v => v = true ↔ Earlier a b ⦄ := by
  unfold order_range.before Earlier
  split_ifs <;> simp [spec_ok] <;> scalar_tac

def Ordered (a b : order_range.ClockRange) : Prop := ¬ Earlier b a

theorem ordered_trans {a b c : order_range.ClockRange} :
    Ordered a b → Ordered b c → Ordered a c := by unfold Ordered Earlier; omega

private theorem pick_child_spec (cur : Ranges) (hole left right stop : Std.Usize)
    (held : order_range.ClockRange) (hl : left.val = 2 * hole.val + 1)
    (hr : right.val = left.val + 1) (hb : left.val < stop.val) (hs : stop.val ≤ cur.length) :
    (if right < stop then do
       let a ← alloc.vec.Vec.index_usize cur left
       let b ← alloc.vec.Vec.index_usize cur right
       let prefer ← order_range.before a b
       if prefer then ok right else ok left
     else ok left) ⦃ c =>
       0 < c.val ∧ c.val < stop.val ∧ (c.val - 1) / 2 = hole.val ∧
       ∀ j, 0 < j → j < stop.val → (j - 1) / 2 = hole.val →
         Ordered (OrderRangeHeap.filled cur.val hole.val held j)
           (OrderRangeHeap.filled cur.val hole.val held c.val) ⦄ := by
  have leftLive : left.val < cur.val.length := by scalar_tac
  have lne : left.val ≠ hole.val := by omega
  have rne : right.val ≠ hole.val := by omega
  have children (j : Nat) (hj : 0 < j) (hp : (j - 1) / 2 = hole.val) :
      j = left.val ∨ j = right.val := by omega
  by_cases h : right < stop
  · simp only [h, ↓reduceIte]
    have rightLive : right.val < cur.val.length := by scalar_tac
    step as ⟨a, ha⟩
    step as ⟨b, hbb⟩
    step with before_spec a b as ⟨prefer, hp⟩
    cases prefer <;> simp only [Bool.false_eq_true, ↓reduceIte, spec_ok] at *
    all_goals
      refine ⟨by scalar_tac, by scalar_tac, by omega, ?_⟩
      intro j hj _ par
      rcases children j hj par with e | e <;> subst j <;>
        simp [OrderRangeHeap.filled, lne, rne, List.getElem?_eq_getElem leftLive,
          List.getElem?_eq_getElem rightLive, Ordered, Earlier, ← ha, ← hbb] at *; omega
  · simp only [h, ↓reduceIte, spec_ok]
    refine ⟨by omega, hb, by omega, ?_⟩
    intro j hj hjs par
    have eq : j = left.val := by rcases children j hj par with e | e <;> scalar_tac
    subst j
    simp [Ordered, Earlier]

/-- Filling the current hole with the held root recovers the input multiset.
    Every continuation moves strictly downwards within the heap prefix. -/
theorem sift_down_loop_perm (buf : Ranges) (root stop : Std.Usize)
    (held : order_range.ClockRange) (hr : root.val < stop.val) (hs : stop.val ≤ buf.length) :
    order_range.sift_down_loop buf root stop held ⦃ (out, hole) =>
      hole.val < stop.val ∧ out.length = buf.length ∧
      (out.val.set hole.val held).Perm (buf.val.set root.val held) ∧
      out.val.drop stop.val = buf.val.drop stop.val ⦄ := by
  unfold order_range.sift_down_loop
  let inv : Ranges × Std.Usize → Prop := fun (cur, hole) =>
    hole.val < stop.val ∧ cur.length = buf.length ∧
    (cur.val.set hole.val held).Perm (buf.val.set root.val held) ∧
    cur.val.drop stop.val = buf.val.drop stop.val
  refine loop.spec_decr_nat (fun (_, hole) => stop.val - hole.val) inv inv _
    (buf, root) ?_ ⟨hr, rfl, List.Perm.refl _, rfl⟩
  intro ⟨cur, hole⟩ ⟨hHole, hLen, hPerm, hTail⟩
  unfold order_range.sift_down_loop.body
  step as ⟨half, hHalf⟩
  split_ifs with hInner
  · step as ⟨dbl, hDbl⟩
    step as ⟨left, hLeft⟩
    step as ⟨right, hRight⟩
    have hL : hole.val < left.val ∧ left.val < stop.val := by scalar_tac
    have pick :
        (if right < stop then do
            let a ← alloc.vec.Vec.index_usize cur left
            let b ← alloc.vec.Vec.index_usize cur right
            let prefer ← order_range.before a b
            if prefer then ok right else ok left
          else ok left) ⦃ c => hole.val < c.val ∧ c.val < stop.val ⦄ := by
      split_ifs with hr'
      · step as ⟨a, ha⟩
        step as ⟨b, hb⟩
        step with before_spec a b as ⟨choose, _⟩
        cases choose <;> simp [spec_ok] <;> scalar_tac
      · simpa [spec_ok] using hL
    step with pick as ⟨child, hc0, hc⟩
    step as ⟨v, hv⟩
    step with before_spec held v as ⟨choose, _⟩
    split_ifs
    · step as ⟨old, back, hOld, hBack⟩
      have hWrite : (back v).val = cur.val.set hole.val (cur.val[child.val]'(by scalar_tac)) := by
        rw [hBack, hv]
        simp [alloc.vec.Vec.set]
      refine ⟨⟨hc, ?_, ?_, ?_⟩, by omega⟩
      · simp [alloc.vec.Vec.length, hWrite, ← hLen]
      · rw [hWrite]
        exact (OrderRangeHeap.move_hole_perm cur.val hole.val child.val (by scalar_tac)
          (by scalar_tac) (by omega) held).trans hPerm
      · rw [hWrite, OrderRangeHeap.drop_set_before _ _ _ _ hHole, hTail]
    · simpa [spec_ok, inv] using And.intro hHole (And.intro hLen (And.intro hPerm hTail))
  · simpa [spec_ok, inv] using And.intro hHole (And.intro hLen (And.intro hPerm hTail))

/-- The comparison performed at each iteration picks a child dominating both
    subtrees. Filling the final hole restores every heap edge below the root. -/
theorem sift_down_loop_order (buf : Ranges) (root stop : Std.Usize)
    (held : order_range.ClockRange) (hr : root.val < stop.val) (hs : stop.val ≤ buf.length)
    (heap : OrderRangeHeap.HeapFrom Ordered buf.val (root.val + 1) stop.val)
    (hheld : held = buf.val[root.val]'(by scalar_tac)) :
    order_range.sift_down_loop buf root stop held ⦃ (out, hole) =>
      hole.val < stop.val ∧ out.length = buf.length ∧
      OrderRangeHeap.HeapFrom Ordered (out.val.set hole.val held) root.val stop.val ⦄ := by
  let inv : Ranges × Std.Usize → Prop := fun (v, i) =>
    i.val < stop.val ∧ v.length = buf.length ∧
    OrderRangeHeap.SiftHole Ordered (OrderRangeHeap.filled v.val i.val held) root.val stop.val i.val
  unfold order_range.sift_down_loop
  refine loop.spec_decr_nat (fun (_, i) => stop.val - i.val) inv _ _ _ ?_ ?_
  · intro ⟨v, i⟩ ⟨hi, hlen, hheap⟩
    have live : i.val < v.val.length := by scalar_tac
    let f := OrderRangeHeap.filled v.val i.val held
    unfold order_range.sift_down_loop.body
    step as ⟨half, hhalf⟩
    split_ifs with h
    · step as ⟨d, hd⟩
      step as ⟨left, hl⟩
      step as ⟨right, hright⟩
      step with pick_child_spec v i left right stop held (by scalar_tac)
        (by scalar_tac) (by scalar_tac) (by scalar_tac) as ⟨child, hpos, hstop, hp, dominates⟩
      have parentLt : i.val < child.val := by omega
      have childLive : child.val < v.val.length := by scalar_tac
      step as ⟨x, hx⟩
      step with before_spec held x as ⟨choose, hcmp⟩
      have childVal : f child.val = x := by
        simp [f, OrderRangeHeap.filled, Nat.ne_of_gt parentLt, List.getElem?_eq_getElem childLive, hx]
      have holeVal : f i.val = held := by simp [f, OrderRangeHeap.filled]
      split_ifs with go
      · step as ⟨_, write, _, hw⟩
        have hwv : (write x).val = v.val.set i.val v.val[child.val] := by
          simp [hw, alloc.vec.Vec.set, hx]
        have he := hcmp.mp go
        have cmp : Ordered (f i.val) (f child.val) := by
          rw [holeVal, childVal]; unfold Earlier at he; unfold Ordered Earlier; omega
        refine ⟨⟨hstop, by simp [alloc.vec.Vec.length, hwv, ← hlen], ?_⟩, by omega⟩
        rw [hwv, OrderRangeHeap.move_hole_values v.val i.val child.val live childLive (by omega) held]
        exact OrderRangeHeap.promote_child hheap hpos hstop hp cmp dominates
      · simp only [spec_ok]
        refine ⟨hi, hlen, OrderRangeHeap.finish_sift_list v.val held live hheap ?_⟩
        intro j hj hb hjp
        apply ordered_trans (dominates j hj hb hjp)
        change Ordered (f child.val) (f i.val)
        rw [childVal, holeVal]
        exact fun earlier => go (hcmp.mpr earlier)
    · simp only [spec_ok]
      refine ⟨hi, hlen, OrderRangeHeap.finish_sift_list v.val held live hheap ?_⟩
      intro j hj hb hjp
      have hhalf' : stop.val / 2 ≤ i.val := by scalar_tac
      change (j - 1) / 2 = i.val at hjp
      omega
  · refine ⟨hr, rfl, ?_⟩
    subst held
    rw [OrderRangeHeap.filled_at_root buf.val root.val (by scalar_tac)]
    exact OrderRangeHeap.start_sift buf.val _ hs heap

theorem sift_down_frame (buf : Ranges) (root stop : Std.Usize)
    (hr : root.val < stop.val) (hs : stop.val ≤ buf.length) :
    order_range.sift_down buf root stop ⦃ out =>
      out.val.Perm buf.val ∧ out.val.drop stop.val = buf.val.drop stop.val ⦄ := by
  unfold order_range.sift_down
  step as ⟨held, hHeld⟩
  step with sift_down_loop_perm buf root stop held hr hs as ⟨cur, hole, hh, hl, hp, ht⟩
  step as ⟨v, back, hv, hb⟩
  rw [hb]
  constructor
  · simpa [alloc.vec.Vec.set, hHeld, List.set_getElem_self] using hp
  · simpa [alloc.vec.Vec.set, OrderRangeHeap.drop_set_before _ _ _ _ hh] using ht

theorem sift_down_perm (buf : Ranges) (root stop : Std.Usize)
    (hr : root.val < stop.val) (hs : stop.val ≤ buf.length) :
    order_range.sift_down buf root stop ⦃ out => out.val.Perm buf.val ⦄ :=
  spec_mono (sift_down_frame buf root stop hr hs) (fun _ h => h.1)

theorem sift_down_order (buf : Ranges) (root stop : Std.Usize)
    (hr : root.val < stop.val) (hs : stop.val ≤ buf.length)
    (heap : OrderRangeHeap.HeapFrom Ordered buf.val (root.val + 1) stop.val) :
    order_range.sift_down buf root stop ⦃ out =>
      OrderRangeHeap.HeapFrom Ordered out.val root.val stop.val ⦄ := by
  unfold order_range.sift_down
  step as ⟨held, hheld⟩
  step with sift_down_loop_order buf root stop held hr hs heap hheld as ⟨cur, hole, hh, hlen, hp⟩
  step as ⟨_, write, _, hw⟩
  simpa [hw, alloc.vec.Vec.set] using hp

/-- Building the heap extends the established parent invariant one root to
    the left per iteration and keeps elements after the active prefix intact. -/
theorem heapify_order (buf : Ranges) (stop root : Std.Usize) (hr : root.val ≤ stop.val)
    (hs : stop.val ≤ buf.length) (heap : OrderRangeHeap.HeapFrom Ordered buf.val root.val stop.val) :
    order_range.heapsort_loop0 buf stop root ⦃ out =>
      out.val.Perm buf.val ∧ out.val.drop stop.val = buf.val.drop stop.val ∧
      OrderRangeHeap.HeapFrom Ordered out.val 0 stop.val ⦄ := by
  unfold order_range.heapsort_loop0
  let inv : Ranges × Std.Usize → Prop := fun (v, k) =>
    k.val ≤ stop.val ∧ v.val.Perm buf.val ∧ v.val.drop stop.val = buf.val.drop stop.val ∧
      OrderRangeHeap.HeapFrom Ordered v.val k.val stop.val
  refine loop.spec_decr_nat (fun (_, k) => k.val) inv _ _ (buf, root) ?_
    ⟨hr, List.Perm.refl _, rfl, heap⟩
  intro ⟨v, k⟩ ⟨hk, perm, frame, edges⟩
  unfold order_range.heapsort_loop0.body
  simp only
  split_ifs with h
  · step as ⟨j, hj⟩
    have he : j.val + 1 = k.val := by scalar_tac
    have live : j.val < stop.val := by scalar_tac
    have bounds : stop.val ≤ v.length := by simpa [alloc.vec.Vec.length, perm.length_eq] using hs
    have spec := spec_and (sift_down_frame v j stop live bounds)
      (sift_down_order v j stop live bounds (by simpa only [he] using edges))
    step with spec as ⟨out, hp, hf, ho⟩
    exact ⟨⟨by omega, hp.trans perm, hf.trans frame, ho⟩, by scalar_tac⟩
  · have hz : k.val = 0 := by scalar_tac
    exact (by simpa only [spec_ok, hz] using And.intro perm (And.intro frame edges))

theorem heapify_perm (buf : Ranges) (stop root : Std.Usize)
    (hr : root.val ≤ stop.val) (hs : stop.val ≤ buf.length) :
    order_range.heapsort_loop0 buf stop root ⦃ out => out.val.Perm buf.val ⦄ := by
  unfold order_range.heapsort_loop0
  let inv : Ranges × Std.Usize → Prop := fun (v, k) => k.val ≤ stop.val ∧ v.val.Perm buf.val
  refine loop.spec_decr_nat (fun (_, k) => k.val) inv _ _ (buf, root) ?_
    ⟨hr, List.Perm.refl _⟩
  intro ⟨v, k⟩ ⟨hk, hp⟩
  unfold order_range.heapsort_loop0.body
  simp only
  split_ifs
  · step as ⟨k', hk'⟩
    have hv : stop.val ≤ v.length := by simpa [alloc.vec.Vec.length, hp.length_eq] using hs
    step with sift_down_perm v k' stop (by scalar_tac) hv as ⟨v', hp'⟩
    exact ⟨⟨by scalar_tac, hp'.trans hp⟩, by scalar_tac⟩
  · simpa only [spec_ok] using hp

theorem drain_heap_perm (buf : Ranges) (stop : Std.Usize) (hs : stop.val ≤ buf.length) :
    order_range.heapsort_loop1 buf stop ⦃ out => out.val.Perm buf.val ⦄ := by
  unfold order_range.heapsort_loop1
  let inv : Ranges × Std.Usize → Prop := fun (v, k) => k.val ≤ v.length ∧ v.val.Perm buf.val
  refine loop.spec_decr_nat (fun (_, k) => k.val) inv _ _ (buf, stop) ?_
    ⟨hs, List.Perm.refl _⟩
  intro ⟨v, k⟩ ⟨hk, hp⟩
  unfold order_range.heapsort_loop1.body
  simp only
  split_ifs
  · step as ⟨last, hLast⟩
    step as ⟨a, ha⟩
    step as ⟨b, hb⟩
    step as ⟨_, writeLast, _, hwl⟩
    have hLastLen : (writeLast b).length = v.length := by simp [hwl, alloc.vec.Vec.set, alloc.vec.Vec.length]
    step as ⟨_, writeFirst, _, hwf⟩
    have swapped : (writeFirst a).val.Perm v.val := by
      simp [hwf, hwl, alloc.vec.Vec.set, ha, hb]
      apply OrderRangeHeap.swap_perm; scalar_tac
    have hLen := swapped.length_eq
    step with sift_down_perm (writeFirst a) 0#usize last (by scalar_tac) (by scalar_tac) as ⟨v', hv'⟩
    have hv'len := hv'.length_eq
    exact ⟨⟨by scalar_tac, hv'.trans (swapped.trans hp)⟩, by scalar_tac⟩
  · simpa only [spec_ok] using hp

theorem drain_heap_order (buf : Ranges) (stop : Std.Usize) (hs : stop.val ≤ buf.length)
    (heap : OrderRangeHeap.HeapFrom Ordered buf.val 0 stop.val) :
    order_range.heapsort_loop1 buf stop ⦃ out =>
      out.val.Perm buf.val ∧ out.val.drop stop.val = buf.val.drop stop.val ∧
      (out.val.take stop.val).Pairwise Ordered ⦄ := by
  unfold order_range.heapsort_loop1
  let inv : Ranges × Std.Usize → Prop := fun (v, k) =>
    k.val ≤ stop.val ∧ v.val.Perm buf.val ∧ v.val.drop stop.val = buf.val.drop stop.val ∧
    OrderRangeHeap.HeapFrom Ordered v.val 0 k.val ∧ OrderRangeHeap.DrainOrder Ordered v.val k.val stop.val
  refine loop.spec_decr_nat (fun (_, k) => k.val) inv _ _ (buf, stop) ?_
    ⟨Nat.le_refl _, List.Perm.refl _, rfl, heap, fun _ h₁ h₂ => False.elim (by omega)⟩
  intro ⟨v, k⟩ ⟨hk, hp, frame, edges, tail⟩
  have size : v.length = buf.length := hp.length_eq
  unfold order_range.heapsort_loop1.body
  simp only
  split_ifs with h
  · step as ⟨last, hLast⟩
    have he : last.val + 1 = k.val := by scalar_tac
    have hl : 0 < last.val := by scalar_tac
    have live : last.val < v.val.length := by scalar_tac
    step as ⟨a, ha⟩
    step as ⟨b, hb⟩
    step as ⟨_, writeLast, _, hwl⟩
    have hLastLen : (writeLast b).length = v.length := by simp [hwl, alloc.vec.Vec.set, alloc.vec.Vec.length]
    step as ⟨_, writeFirst, _, hwf⟩
    let w := writeFirst a
    have swapped : w.val = (v.val.set last.val v.val[0]).set 0 v.val[last.val] := by
      simp [w, hwf, hwl, alloc.vec.Vec.set, ha, hb]
    have ps : w.val.Perm v.val := by
      rw [swapped]; exact OrderRangeHeap.swap_perm _ _ _ live (by omega) (by omega)
    have hsw := OrderRangeHeap.pop_root (fun x => by simp [Ordered, Earlier]) (@ordered_trans)
      v.val last.val stop.val hl live (by simpa only [he] using edges) (by simpa only [he] using tail)
    rw [← swapped] at hsw
    have hs' : last.val ≤ w.length := by change last.val ≤ w.val.length; rw [ps.length_eq]; omega
    have both := spec_and (sift_down_frame w 0#usize last (by scalar_tac) hs')
      (sift_down_order w 0#usize last (by scalar_tac) hs' hsw.1)
    step with both as ⟨out, p, f, heap'⟩
    have sframe := congrArg (List.drop (stop.val - last.val)) f
    have add : last.val + (stop.val-last.val) = stop.val := by omega
    simp only [List.drop_drop, add] at sframe
    rw [swapped, OrderRangeHeap.drop_set_before _ _ _ _ (by omega),
      OrderRangeHeap.drop_set_before _ _ _ _ (by omega)] at sframe
    exact ⟨⟨by omega, p.trans (ps.trans hp), sframe.trans frame, heap',
      OrderRangeHeap.drain_frame p f hsw.2⟩, by omega⟩
  · simp only [spec_ok]
    exact ⟨hp, frame, OrderRangeHeap.drain_complete (by scalar_tac) tail⟩

/-- Heapsort orders the requested prefix lexicographically, preserves the
    complete multiset, and leaves all slots above the prefix untouched. -/
theorem heapsort_spec (buf : Ranges) (stop : Std.Usize) (hs : stop.val ≤ buf.length) :
    order_range.heapsort buf stop ⦃ out => out.val.Perm buf.val ∧
      out.val.drop stop.val = buf.val.drop stop.val ∧ (out.val.take stop.val).Pairwise Ordered ⦄ := by
  unfold order_range.heapsort
  step as ⟨mid, hm⟩
  have heap := OrderRangeHeap.leaves_heap Ordered buf.val stop.val
  step with heapify_order buf stop mid (by scalar_tac) hs (by simpa only [hm] using heap)
    as ⟨v, hp, hf, hh⟩
  have size := hp.length_eq
  step with drain_heap_order v stop (by scalar_tac) hh as ⟨out, perm, frame, ordered⟩
  exact ⟨perm.trans hp, frame.trans hf, ordered⟩

theorem heapsort_perm (buf : Ranges) (stop : Std.Usize) (hs : stop.val ≤ buf.length) :
    order_range.heapsort buf stop ⦃ out => out.val.Perm buf.val ⦄ := by
  unfold order_range.heapsort
  step as ⟨mid, hm⟩
  step with heapify_perm buf stop mid (by scalar_tac) hs as ⟨v, hv⟩
  have hlen := hv.length_eq
  step with drain_heap_perm v stop (by scalar_tac) as ⟨out, hout⟩
  exact hout.trans hv

theorem insert_sorted_loop_perm (buf : Ranges) (i : Std.Usize) (held : order_range.ClockRange)
    (hi : i.val < buf.length) :
    order_range.insert_sorted_loop buf i held ⦃ (out, k) =>
      k.val < out.length ∧ (out.val.set k.val held).Perm (buf.val.set i.val held) ⦄ := by
  unfold order_range.insert_sorted_loop
  let inv : Ranges × Std.Usize → Prop := fun (v, k) =>
    k.val < v.length ∧ (v.val.set k.val held).Perm (buf.val.set i.val held)
  refine loop.spec_decr_nat (fun (_, k) => k.val) inv inv _ (buf, i) ?_ ⟨hi, List.Perm.refl _⟩
  intro ⟨v, k⟩ ⟨hk, hp⟩
  unfold order_range.insert_sorted_loop.body
  simp only
  split_ifs
  · step as ⟨j, hj⟩
    step as ⟨prev, hprev⟩
    step with before_spec held prev as ⟨b, hb⟩
    split_ifs
    · step as ⟨r, hr⟩
      step as ⟨_, write, _, hw⟩
      have hj' : j.val < v.val.length := by scalar_tac
      have moved := OrderRangeHeap.move_hole_perm v.val k.val j.val hk hj' (by scalar_tac) held
      refine ⟨⟨?_, ?_⟩, by scalar_tac⟩
      · simpa [hw, alloc.vec.Vec.set, alloc.vec.Vec.length] using hj'
      · simpa [hw, alloc.vec.Vec.set, hr] using moved.trans hp
    · simpa [spec_ok, inv] using And.intro hk hp
  · simpa [spec_ok, inv] using And.intro hk hp

theorem insert_sorted_perm (buf : Ranges) (i : Std.Usize) (hi : i.val < buf.length) :
    order_range.insert_sorted buf i ⦃ v => v.val.Perm buf.val ⦄ := by
  unfold order_range.insert_sorted
  step as ⟨held, hh⟩
  step with insert_sorted_loop_perm buf i held hi as ⟨v, j, hj, hp⟩
  step as ⟨_, write, _, hw⟩
  rw [hw]
  simpa [alloc.vec.Vec.set, hh, List.set_getElem_self] using hp

/-- Insertion moves the predecessor into the hole until the held range
    fits. Every slot strictly above the insertion prefix keeps its value. -/
theorem insert_sorted_loop_order (buf : Ranges) (endIdx : Std.Usize)
    (held : order_range.ClockRange) (hi : endIdx.val < buf.length)
    (sorted : (buf.val.take endIdx.val).Pairwise Ordered) :
    order_range.insert_sorted_loop buf endIdx held ⦃ (out, k) =>
      k.val ≤ endIdx.val ∧ out.length = buf.length ∧
      out.val.drop (endIdx.val+1) = buf.val.drop (endIdx.val+1) ∧
      ((out.val.set k.val held).take (endIdx.val+1)).Pairwise Ordered ⦄ := by
  let stop := endIdx.val+1
  let inv : Ranges × Std.Usize → Prop := fun (v, k) =>
    k.val < stop ∧ v.length = buf.length ∧ v.val.drop stop = buf.val.drop stop ∧
    OrderRangeHeap.InsertHole Ordered (OrderRangeHeap.filled v.val k.val held) k.val stop
  unfold order_range.insert_sorted_loop
  refine loop.spec_decr_nat (fun (_, k) => k.val) inv _ _ _ ?_ ?_
  · intro ⟨v, k⟩ ⟨hk, hlen, frame, edges⟩
    let f := OrderRangeHeap.filled v.val k.val held
    have here : k.val < v.val.length := by dsimp [stop] at hk; scalar_tac
    have fillVal : f k.val = held := by simp [f, OrderRangeHeap.filled]
    have finish (fits : 0 < k.val → Ordered (f (k.val-1)) (f k.val)) :
        ((v.val.set k.val held).take stop).Pairwise Ordered := by
      apply List.pairwise_iff_getElem.mpr
      intro a b ha hb hab
      have aLive : a < (v.val.set k.val held).length := by simp at ha ⊢; omega
      have bLive : b < (v.val.set k.val held).length := by simp at hb ⊢; omega
      have bStop : b < stop := by simp at hb; omega
      have eq := OrderRangeHeap.filled_write v.val k.val here held
      have result := OrderRangeHeap.complete_insert (@ordered_trans) edges hk fits a b hab bStop
      change Ordered (OrderRangeHeap.filled v.val k.val held a) (OrderRangeHeap.filled v.val k.val held b) at result
      rw [← eq] at result
      simpa only [List.getElem_take, List.getElem?_eq_getElem aLive, List.getElem?_eq_getElem bLive,
        Option.getD_some] using result
    unfold order_range.insert_sorted_loop.body
    simp only
    split_ifs with positive
    · step as ⟨prev, hp⟩
      step as ⟨x, hx⟩
      step with before_spec held x as ⟨choose, cmp⟩
      have pe : prev.val + 1 = k.val := by scalar_tac
      have pLive : prev.val < v.val.length := by omega
      have pval : f prev.val = x := by
        simp [f, OrderRangeHeap.filled, show prev.val ≠ k.val by omega, List.getElem?_eq_getElem pLive, hx]
      split_ifs with go
      · step as ⟨y, hy⟩
        step as ⟨_, write, _, hw⟩
        have updated : (write y).val = v.val.set k.val v.val[prev.val] := by simp [hw, alloc.vec.Vec.set, hy]
        have grows : Ordered (f k.val) (f prev.val) := by
          rw [fillVal, pval]; have earlier := cmp.mp go
          unfold Earlier at earlier; unfold Ordered Earlier; omega
        refine ⟨⟨by omega, by simp [alloc.vec.Vec.length, updated, ← hlen],
          by simpa only [updated, OrderRangeHeap.drop_set_before _ _ _ _ hk] using frame, ?_⟩, by omega⟩
        rw [updated, OrderRangeHeap.move_hole_values v.val k.val prev.val here pLive (by omega) held]
        have shifted := OrderRangeHeap.shift_predecessor (le := Ordered) (f := f) (k := prev.val) (stop := stop)
          (by simpa only [pe] using edges) (by omega) (by simpa only [pe] using grows)
        simpa only [pe] using shifted
      · simp only [spec_ok]
        exact ⟨Nat.le_of_lt_succ hk, hlen, frame, finish (fun _ => by
          rw [← hp, pval, fillVal]; exact fun earlier => go (cmp.mpr earlier))⟩
    · simp only [spec_ok]
      exact ⟨Nat.le_of_lt_succ hk, hlen, frame, finish (fun h => False.elim (by scalar_tac))⟩
  · refine ⟨Nat.lt_succ_self _, rfl, rfl, ?_⟩
    constructor
    · intro a b ab bs an bn
      have bpre : b < endIdx.val := by dsimp [stop] at bs; omega
      have al : a < (buf.val.take endIdx.val).length := by simp; scalar_tac
      have bl : b < (buf.val.take endIdx.val).length := by simp; scalar_tac
      have aa : a < buf.val.length := by scalar_tac
      have bb : b < buf.val.length := by scalar_tac
      simpa [OrderRangeHeap.filled, an, bn, List.getElem?_eq_getElem aa, List.getElem?_eq_getElem bb]
        using List.pairwise_iff_getElem.mp sorted a b al bl ab
    · intro j hj hs; dsimp [stop] at hs; omega

theorem insert_sorted_order (buf : Ranges) (i : Std.Usize) (hi : i.val < buf.length)
    (sorted : (buf.val.take i.val).Pairwise Ordered) :
    order_range.insert_sorted buf i ⦃ out => out.length = buf.length ∧
      out.val.drop (i.val+1) = buf.val.drop (i.val+1) ∧
      (out.val.take (i.val+1)).Pairwise Ordered ⦄ := by
  unfold order_range.insert_sorted
  step as ⟨held, _⟩
  step with insert_sorted_loop_order buf i held hi sorted as ⟨v, k, hk, size, frame, ordered⟩
  step as ⟨_, write, _, hw⟩
  have eq : (write held).val = v.val.set k.val held := by simp [hw, alloc.vec.Vec.set]
  exact ⟨by simpa [alloc.vec.Vec.length, eq] using size,
    by simpa only [eq, OrderRangeHeap.drop_set_before _ _ _ _ (by omega : k.val < i.val+1)] using frame,
    by simpa only [eq] using ordered⟩

theorem sort_short_suffix_spec (buf : Ranges) (i stop : Std.Usize) (hi : i.val ≤ stop.val)
    (hs : stop.val ≤ buf.length) (ordered : (buf.val.take i.val).Pairwise Ordered) :
    order_range.sort_short_suffix buf i stop ⦃ out => out.val.Perm buf.val ∧
      out.val.drop stop.val = buf.val.drop stop.val ∧ (out.val.take stop.val).Pairwise Ordered ⦄ := by
  unfold order_range.sort_short_suffix order_range.sort_short_suffix_loop
  let inv : Ranges × Std.Usize → Prop := fun (v, k) => k.val ≤ stop.val ∧
    v.val.Perm buf.val ∧ v.val.drop stop.val = buf.val.drop stop.val ∧
    (v.val.take k.val).Pairwise Ordered
  refine loop.spec_decr_nat (fun (_, k) => stop.val - k.val) inv _ _ _
    ?_ ⟨hi, List.Perm.refl _, rfl, ordered⟩
  intro ⟨v, k⟩ ⟨bound, perm, frame, sorted⟩
  unfold order_range.sort_short_suffix_loop.body
  simp only
  split_ifs with go
  · have len := perm.length_eq
    have live : k.val < v.length := by scalar_tac
    have spec := spec_and (insert_sorted_perm v k live) (insert_sorted_order v k live sorted)
    step with spec as ⟨out, perm', _, frame', sorted'⟩
    step as ⟨next, hn⟩
    have cut : k.val+1+(stop.val-(k.val+1)) = stop.val := by scalar_tac
    have suffix := congrArg (List.drop (stop.val-(k.val+1))) frame'
    simp only [List.drop_drop, cut] at suffix
    exact ⟨⟨by scalar_tac, perm'.trans perm, suffix.trans frame, by simpa [hn] using sorted'⟩, by scalar_tac⟩
  · have done : k.val = stop.val := by scalar_tac
    simpa only [spec_ok, done] using And.intro perm (And.intro frame sorted)

theorem sort_short_suffix_perm (buf : Ranges) (i stop : Std.Usize) (hs : stop.val ≤ buf.length) :
    order_range.sort_short_suffix buf i stop ⦃ out => out.val.Perm buf.val ⦄ := by
  unfold order_range.sort_short_suffix order_range.sort_short_suffix_loop
  let inv : Ranges × Std.Usize → Prop := fun (v, _) => v.val.Perm buf.val
  refine loop.spec_decr_nat (fun (_, k) => buf.length - k.val) inv _ _ (buf, i) ?_ (List.Perm.refl _)
  intro ⟨v, k⟩ hp
  change v.val.Perm buf.val at hp
  have hl := hp.length_eq
  unfold order_range.sort_short_suffix_loop.body
  simp only
  split_ifs
  · step with insert_sorted_perm v k (by scalar_tac) as ⟨v', hp'⟩
    step as ⟨k', hk'⟩
    exact ⟨hp'.trans hp, by scalar_tac⟩
  · simpa only [spec_ok] using hp

theorem reverse_prefix_perm (buf : Ranges) (stop : Std.Usize) (hs : stop.val ≤ buf.length) :
    order_range.reverse_prefix buf stop ⦃ out => out.val.Perm buf.val ⦄ := by
  unfold order_range.reverse_prefix order_range.reverse_prefix_loop
  let inv : Ranges × Std.Usize → Prop := fun (v, _) => v.val.Perm buf.val
  refine loop.spec_decr_nat (fun (_, i) => stop.val - i.val) inv _ _ _ ?_ (List.Perm.refl _)
  intro ⟨v, i⟩ hp
  change v.val.Perm buf.val at hp
  have hlen := hp.length_eq
  unfold order_range.reverse_prefix_loop.body
  step as ⟨half, hhalf⟩
  split_ifs
  · step as ⟨last, hlast⟩
    step as ⟨j, hj⟩
    step as ⟨left, hl⟩
    step as ⟨right, hr⟩
    step as ⟨_, writeLeft, _, hw⟩
    have hwl : (writeLeft right).length = v.length := by
      simp [hw, alloc.vec.Vec.set, alloc.vec.Vec.length]
    step as ⟨_, writeRight, _, hw'⟩
    step as ⟨i', hi'⟩
    refine ⟨?_, by scalar_tac⟩
    apply List.Perm.trans _ hp
    simp [hw', hw, alloc.vec.Vec.set, hl, hr]
    apply OrderRangeHeap.swap_perm; scalar_tac
  · simpa only [spec_ok] using hp

/-- The reverse fast path reflects each index of the active prefix and
    preserves the suffix in its original slots. -/
theorem reverse_prefix_spec (buf : Ranges) (stop : Std.Usize) (hs : stop.val ≤ buf.length) :
    order_range.reverse_prefix buf stop ⦃ out =>
      out.length = buf.length ∧ ∀ j : Nat,
        out.val[j]? = buf.val[if j < stop.val then stop.val - 1 - j else j]? ⦄ := by
  let source (done j : Nat) :=
    if j < done ∨ (stop.val-done ≤ j ∧ j < stop.val) then stop.val-1-j else j
  let inv : Ranges × Std.Usize → Prop := fun (v, i) =>
    v.length = buf.length ∧ i.val ≤ stop.val / 2 ∧
      ∀ j : Nat, v.val[j]? = buf.val[source i.val j]?
  unfold order_range.reverse_prefix order_range.reverse_prefix_loop
  refine loop.spec_decr_nat (fun (_, i) => stop.val - i.val) inv _ _ _ ?_ ?_
  · intro ⟨v, i⟩ ⟨hlen, hi, values⟩
    unfold order_range.reverse_prefix_loop.body
    step as ⟨half, hhalf⟩
    split_ifs with go
    · step as ⟨last, hlast⟩
      step as ⟨j, hj⟩
      have lij : i.val < j.val := by scalar_tac
      have li : i.val < v.val.length := by scalar_tac
      have lj : j.val < v.val.length := by scalar_tac
      step as ⟨left, hl⟩
      step as ⟨right, hr⟩
      step as ⟨_, wr, _, hwr⟩
      have hwl : (wr right).length = v.length := by simp [hwr, alloc.vec.Vec.set, alloc.vec.Vec.length]
      step as ⟨_, wr', _, hwr'⟩
      step as ⟨next, hn⟩
      have newBuf : (wr' left).val = (v.val.set i.val right).set j.val left := by
        simp [hwr', hwr, alloc.vec.Vec.set]
      have lval : some left = buf.val[i.val]? := by
        have ix : source i.val i.val = i.val := by unfold source; split <;> omega
        simpa [ix, List.getElem?_eq_getElem li, hl] using values i.val
      have rval : some right = buf.val[j.val]? := by
        have ix : source i.val j.val = j.val := by unfold source; split <;> omega
        simpa [ix, List.getElem?_eq_getElem lj, hr] using values j.val
      refine ⟨⟨by simp [alloc.vec.Vec.length, newBuf, ← hlen], by scalar_tac, ?_⟩, by scalar_tac⟩
      intro k
      by_cases el : k = i.val
      · subst k
        have ix : source next.val i.val = j.val := by unfold source; split <;> omega
        simpa [newBuf, ix, li, Nat.ne_of_lt lij, Nat.ne_of_gt lij] using rval
      · by_cases er : k = j.val
        · subst k
          have ix : source next.val j.val = i.val := by unfold source; split <;> omega
          simpa [newBuf, ix, lj] using lval
        · have ix : source next.val k = source i.val k := by unfold source; split <;> split <;> omega
          simpa [newBuf, ix, el, er, Ne.symm el, Ne.symm er] using values k
    · simp only [spec_ok]
      refine ⟨hlen, ?_⟩
      intro k
      have eq : source i.val k = (if k < stop.val then stop.val-1-k else k) := by
        have done : i.val = stop.val / 2 := by scalar_tac
        unfold source
        split <;> split <;> omega
      simpa only [eq] using values k
  · refine ⟨rfl, by scalar_tac, ?_⟩
    intro k
    have ix : source 0 k = k := by unfold source; split <;> omega
    simp [ix]

theorem descending_scan_spec (buf : Ranges) (stop j : Std.Usize)
    (hs : stop.val ≤ buf.length) (hj : 0 < j.val) (hjs : j.val ≤ stop.val) :
    order_range.sort_prefix_loop0_loop0 buf stop j ⦃ k => j.val ≤ k.val ∧ k.val ≤ stop.val ⦄ := by
  unfold order_range.sort_prefix_loop0_loop0
  let inv := fun (k : Std.Usize) => j.val ≤ k.val ∧ k.val ≤ stop.val
  refine loop.spec_decr_nat (fun k => stop.val - k.val) inv inv _ j ?_ ⟨Nat.le_refl _, hjs⟩
  intro k ⟨hjk, hks⟩
  unfold order_range.sort_prefix_loop0_loop0.body
  by_cases h : k < stop
  · simp only [h, ↓reduceIte]
    step as ⟨prev, hp⟩
    step as ⟨a, ha⟩
    step as ⟨b, hb⟩
    step with before_spec a b as ⟨c, hc⟩
    split_ifs
    · simpa only [spec_ok] using And.intro hjk hks
    · step as ⟨k', hk'⟩
      exact ⟨⟨by scalar_tac, by scalar_tac⟩, by scalar_tac⟩
  · simpa [h, spec_ok] using And.intro hjk hks

private abbrev Desc (a b : order_range.ClockRange) := Ordered b a

theorem descending_scan_order (buf : Ranges) (stop j : Std.Usize)
    (hs : stop.val ≤ buf.length) (hj : 0 < j.val) (hjs : j.val ≤ stop.val)
    (run : (buf.val.take j.val).Pairwise Desc) :
    order_range.sort_prefix_loop0_loop0 buf stop j ⦃ k =>
      j.val ≤ k.val ∧ k.val ≤ stop.val ∧ (buf.val.take k.val).Pairwise Desc ⦄ := by
  unfold order_range.sort_prefix_loop0_loop0
  let inv := fun (k : Std.Usize) =>
    j.val ≤ k.val ∧ k.val ≤ stop.val ∧ (buf.val.take k.val).Pairwise Desc
  refine loop.spec_decr_nat (fun k => stop.val-k.val) inv inv _ j ?_ ⟨Nat.le_refl _, hjs, run⟩
  intro k ⟨lower, upper, sorted⟩
  unfold order_range.sort_prefix_loop0_loop0.body
  by_cases go : k < stop
  · simp only [go, ↓reduceIte]
    step as ⟨prev, hp⟩
    step as ⟨a, ha⟩
    step as ⟨b, hb⟩
    step with before_spec a b as ⟨brk, cmp⟩
    split_ifs with breaks
    · simpa only [spec_ok] using And.intro lower (And.intro upper sorted)
    · step as ⟨next, hn⟩
      refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [hn]
      apply OrderRangeHeap.pairwise_next (le := Desc) (fun h₁ h₂ => ordered_trans h₂ h₁) buf.val (by scalar_tac) sorted
      intro _
      change ¬Earlier _ _
      have neg : ¬Earlier a b := fun earlier => breaks (cmp.mpr earlier)
      simpa only [ha, hb, hp] using neg
  · simpa only [go, ↓reduceIte, spec_ok] using And.intro lower (And.intro upper sorted)

theorem reverse_sorted (buf : Ranges) (stop : Std.Usize) (hs : stop.val ≤ buf.length)
    (run : (buf.val.take stop.val).Pairwise Desc) :
    order_range.reverse_prefix buf stop ⦃ out => out.val.Perm buf.val ∧
      out.val.drop stop.val = buf.val.drop stop.val ∧ (out.val.take stop.val).Pairwise Ordered ⦄ := by
  refine spec_mono (spec_and (reverse_prefix_perm buf stop hs) (reverse_prefix_spec buf stop hs)) ?_
  intro out ⟨perm, size, slots⟩
  have valAt (j : Nat) (hj : j < stop.val) :
      out.val[j]'(by scalar_tac) = buf.val[stop.val-1-j]'(by scalar_tac) := by
    have a : j < out.val.length := by scalar_tac
    have b : stop.val-1-j < buf.val.length := by scalar_tac
    simpa [hj, List.getElem?_eq_getElem a, List.getElem?_eq_getElem b] using slots j
  refine ⟨perm, ?_, ?_⟩
  · apply List.ext_getElem?
    intro j
    simp only [List.getElem?_drop]
    simpa [show ¬stop.val+j < stop.val by omega] using slots (stop.val+j)
  · apply List.pairwise_iff_getElem.mpr
    intro a b ha hb ab
    have hbs : b < stop.val := by simp at hb; omega
    rw [List.getElem_take, List.getElem_take, valAt a (by omega), valAt b hbs]
    have pair := List.pairwise_iff_getElem.mp run (stop.val-1-b) (stop.val-1-a)
      (by simp; scalar_tac) (by simp; scalar_tac) (by omega)
    simpa [Desc] using pair

def SortPost (buf : Ranges) (stop : Std.Usize) (out : Ranges) :=
  out.val.Perm buf.val ∧ out.val.drop stop.val = buf.val.drop stop.val ∧
    (out.val.take stop.val).Pairwise Ordered

private theorem at_most_one_sorted (l : List order_range.ClockRange) (rel : _ → _ → Prop) :
    (l.take 1).Pairwise rel := by cases l <;> simp

/-- The production dispatch first scans the adjacent keys. It reverses a
    descending prefix, including an initial run of equal keys, or finishes
    with insertion sort or heapsort. Each path preserves the same suffix. -/
theorem sort_prefix_spec (buf : Ranges) (stop : Std.Usize) (size : stop.val ≤ buf.length) :
    order_range.sort_prefix buf stop ⦃ out => SortPost buf stop out ⦄ := by
  let inv := fun (k : Std.Usize) => 0 < k.val ∧ (buf.val.take k.val).Pairwise Ordered
  unfold order_range.sort_prefix order_range.sort_prefix_loop0
  refine loop.spec_decr_nat (fun k => stop.val-k.val) inv (SortPost buf stop) _ 1#usize ?_
    ⟨by decide, at_most_one_sorted buf.val _⟩
  intro i ⟨pos, asc⟩
  unfold order_range.sort_prefix_loop0.body
  by_cases live : i < stop
  · simp only [live, ↓reduceIte]
    have inside : i.val < buf.val.length := by scalar_tac
    step as ⟨x, hx⟩
    step as ⟨prev, hp⟩
    step as ⟨p, hprev⟩
    step with before_spec x p as ⟨choose, cmp⟩
    have fallback (next : Ranges → Result (ControlFlow Std.Usize Ranges))
        (post : ControlFlow Std.Usize Ranges → Prop)
        (finish : ∀ v, SortPost buf stop v → next v ⦃ post ⦄) :
        (if stop ≤ 8#usize then do let v ← order_range.sort_short_suffix buf i stop; next v
         else do let v ← order_range.heapsort buf stop; next v) ⦃ post ⦄ := by
      split
      · step with sort_short_suffix_spec buf i stop (by scalar_tac) size asc as ⟨v, perm, frame, sorted⟩
        exact finish v ⟨perm, frame, sorted⟩
      · step with heapsort_spec buf stop size as ⟨v, perm, frame, sorted⟩
        exact finish v ⟨perm, frame, sorted⟩
    let post := fun (r : ControlFlow Std.Usize Ranges) => match r with
      | .done v => SortPost buf stop v
      | .cont k => inv k ∧ stop.val-k.val < stop.val-i.val
    have done (v : Ranges) (h : SortPost buf stop v) : ok (ControlFlow.done v) ⦃ post ⦄ := by
      simpa only [spec_ok, post] using h
    have scan (run : (buf.val.take i.val).Pairwise Desc) (desc : Ordered x p) :
        (do
          let j ← i + 1#usize
          let past ← order_range.sort_prefix_loop0_loop0 buf stop j
          if past = stop then do let v ← order_range.reverse_prefix buf stop; ok (ControlFlow.done v : ControlFlow Std.Usize Ranges)
          else if stop ≤ 8#usize then do let v ← order_range.sort_short_suffix buf i stop; ok (ControlFlow.done v : ControlFlow Std.Usize Ranges)
          else do let v ← order_range.heapsort buf stop; ok (ControlFlow.done v : ControlFlow Std.Usize Ranges)) ⦃ post ⦄ := by
      step as ⟨j, hj⟩
      have run' : (buf.val.take j.val).Pairwise Desc := by
        rw [hj]
        apply OrderRangeHeap.pairwise_next (le := Desc) (fun h₁ h₂ => ordered_trans h₂ h₁) buf.val inside run
        intro _
        simpa only [Desc, hx, hprev, hp] using desc
      step with descending_scan_order buf stop j size (by omega) (by scalar_tac) run' as ⟨past, _, _, desc'⟩
      by_cases completed : past = stop
      · subst past
        simp only [↓reduceIte]
        step with reverse_sorted buf stop size desc' as ⟨out, perm, frame, sorted⟩
        exact ⟨perm, frame, sorted⟩
      · simp only [completed, ↓reduceIte]
        exact fallback (fun v => ok (ControlFlow.done v : ControlFlow Std.Usize Ranges)) post done
    cases choose
    · simp only [Bool.false_eq_true, ↓reduceIte]
      step as ⟨next, hn⟩
      refine ⟨⟨by omega, ?_⟩, by scalar_tac⟩
      rw [hn]
      apply OrderRangeHeap.pairwise_next (@ordered_trans) _ inside asc
      intro _
      change ¬Earlier _ _
      have neg : ¬Earlier x p := fun e => Bool.noConfusion (cmp.mpr e)
      simpa only [hx, hprev, hp] using neg
    · have desc : Ordered x p := by
        have he := cmp.mp rfl
        unfold Ordered Earlier at *; omega
      have identical (j : Std.Usize) : order_range.sort_prefix_loop0_loop1 buf stop j =
          order_range.sort_prefix_loop0_loop0 buf stop j := by
        have body : order_range.sort_prefix_loop0_loop1.body buf stop =
            order_range.sort_prefix_loop0_loop0.body buf stop := by funext k; rfl
        unfold order_range.sort_prefix_loop0_loop1 order_range.sort_prefix_loop0_loop0
        rw [body]
      simp only [identical, ↓reduceIte]
      by_cases first : i = 1#usize
      · rw [ite_eq_left first]
        have one : (1#usize).val = 1 := by decide
        refine spec_mono (scan (by simpa only [first, one] using at_most_one_sorted buf.val Desc) desc) ?_
        intro r hr
        cases r <;> exact hr
      · simp only [first, ↓reduceIte]
        step as ⟨a, ha⟩
        step as ⟨z, hz⟩
        step with before_spec a z as ⟨rising, risingSpec⟩
        cases rising
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have run : (buf.val.take i.val).Pairwise Desc := by
            apply OrderRangeHeap.descending_tie (fun v => by simp [Ordered, Earlier]) (@ordered_trans)
              buf.val (by scalar_tac) pos asc
            change ¬ Earlier _ _
            have neg : ¬Earlier a z := fun e => Bool.noConfusion (risingSpec.mpr e)
            simpa only [ha, hz, hp] using neg
          refine spec_mono (scan run desc) ?_
          intro r hr
          cases r <;> exact hr
        · simp only [↓reduceIte]
          apply spec_mono (fallback (fun v => ok (ControlFlow.done v : ControlFlow Std.Usize Ranges)) post done)
          intro r hr
          cases r <;> exact hr
  · simp only [live, ↓reduceIte, spec_ok]
    refine ⟨List.Perm.refl _, rfl, ?_⟩
    have smaller := asc.sublist (List.take_sublist stop.val (buf.val.take i.val))
    simpa only [List.take_take, Nat.min_eq_left (show stop.val ≤ i.val by scalar_tac)] using smaller

theorem sort_prefix_perm (buf : Ranges) (stop : Std.Usize) (hs : stop.val ≤ buf.length) :
    order_range.sort_prefix buf stop ⦃ out => out.val.Perm buf.val ⦄ := by
  exact spec_mono (sort_prefix_spec buf stop hs) (fun _ post => post.1)

def validRange (r : order_range.ClockRange) : Bool := decide (r.start.val < r.end.val)

/-- The initial scan leaves an already valid prefix in its original slots. -/
theorem initial_nonempty_spec (buf : Ranges) :
    order_range.nonempty_prefix_loop0 buf 0#usize ⦃ k =>
      k.val ≤ buf.length ∧ (buf.val.take k.val).filter validRange = buf.val.take k.val ⦄ := by
  unfold order_range.nonempty_prefix_loop0
  let inv := fun (k : Std.Usize) =>
    k.val ≤ buf.length ∧ (buf.val.take k.val).filter validRange = buf.val.take k.val
  refine loop.spec_decr_nat (fun k => buf.length - k.val) inv inv _ _ ?_ (by simp [inv])
  intro k ⟨hk, hv⟩
  unfold order_range.nonempty_prefix_loop0.body
  simp only
  by_cases h : k < alloc.vec.Vec.len buf
  · simp only [h, ↓reduceIte]
    have hlt : k.val < buf.val.length := by scalar_tac
    step as ⟨v, hval⟩
    split_ifs with hvalid
    · step as ⟨k', hk'⟩
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      have ht : validRange buf.val[k.val] = true := by
        simp only [validRange, decide_eq_true_eq]
        rw [← hval]
        scalar_tac
      rw [hk', List.take_succ_eq_append_getElem hlt, List.filter_append, hv]
      simp [ht]
    · simpa only [spec_ok] using And.intro hk hv
  · simpa only [h, ↓reduceIte, spec_ok] using And.intro hk hv

private theorem take_write_next {α : Type} (xs : List α) (k : Nat) (x : α) (hk : k < xs.length) :
    (xs.set k x).take (k+1) = xs.take k ++ [x] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons a xs ih =>
    cases k with
    | zero => simp
    | succ k => simp [List.set, List.take, ih k (by simpa using hk)]

private theorem read_original {buf original : Ranges} {read : Nat}
    (hb : read < buf.length) (ho : read < original.length)
    (h : ∀ (i : Nat) (hi : i < buf.length) (hj : i < original.length),
      read ≤ i → buf.val[i] = original.val[i]) :
    buf.val[read] = original.val[read] := h read hb ho (Nat.le_refl _)

/-- In the compaction loop the written prefix is the filter of the consumed
    input. Source elements at and above the read cursor are still available. -/
theorem nonempty_prefix_spec (original : Ranges) :
    order_range.nonempty_prefix original ⦃ (n, out) =>
      out.length = original.length ∧ n.val ≤ out.length ∧
      out.val.take n.val = original.val.filter validRange ⦄ := by
  unfold order_range.nonempty_prefix
  step with initial_nonempty_spec original as ⟨start, hs, hvalid⟩
  unfold order_range.nonempty_prefix_loop1
  let inv : Ranges × Std.Usize × Std.Usize → Prop := fun (v, used, read) =>
    v.length = original.length ∧ used.val ≤ read.val ∧ read.val ≤ v.length ∧
    v.val.take used.val = (original.val.take read.val).filter validRange ∧
    ∀ (i : Nat) (hi : i < v.length) (hj : i < original.length),
      read.val ≤ i → v.val[i] = original.val[i]
  refine loop.spec_decr_nat (fun (_, _, r) => original.length - r.val) inv _ _ _ ?_
    ⟨rfl, Nat.le_refl _, hs, hvalid.symm, fun _ _ _ _ => rfl⟩
  intro ⟨v, used, read⟩ ⟨hsize, hu, hr, hpre, hsuffix⟩
  unfold order_range.nonempty_prefix_loop1.body
  simp only
  by_cases hlt : read < alloc.vec.Vec.len v
  · simp only [hlt, ↓reduceIte]
    have hv : read.val < v.length := by scalar_tac
    have ho : read.val < original.val.length := by scalar_tac
    step as ⟨x, hx⟩
    have hxo : x = original.val[read.val] := hx.trans (read_original hv ho hsuffix)
    by_cases valid : x.start < x.end
    · simp only [valid, ↓reduceIte]
      step as ⟨current, _, hw⟩
      rcases current with ⟨old, write⟩
      step as ⟨used', hu'⟩
      let out := write x
      have hwv : out.val = v.val.set used.val x := by simp_all [out, alloc.vec.Vec.set]
      step as ⟨read', hr'⟩
      have hws : out.length = v.length := by simp [alloc.vec.Vec.length, hwv]
      refine ⟨⟨hws.trans hsize, by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
      · rw [hwv, hu', take_write_next _ _ _ (by scalar_tac), hr',
          List.take_succ_eq_append_getElem ho, List.filter_append, hpre, ← hxo]
        have hxv : validRange x = true := by simp [validRange]; scalar_tac
        simp [hxv]
      · intro i hi hj hge
        have hne : used.val ≠ i := by scalar_tac
        have hi' : i < v.length := by scalar_tac
        have unchanged : out.val[i]'hi = v.val[i]'hi' := by
          have e := congrArg (fun l : List order_range.ClockRange => l[i]?) hwv
          change out.val[i]? = (v.val.set used.val x)[i]? at e
          have ho' : i < out.val.length := hi
          rw [List.getElem?_eq_getElem ho'] at e
          simpa [List.getElem?_set, hne, Ne.symm hne, List.getElem?_eq_getElem hi'] using e
        exact unchanged.trans (hsuffix i hi' hj (by scalar_tac))
    · simp only [valid, ↓reduceIte, bind_ok]
      step as ⟨read', hr'⟩
      refine ⟨⟨hsize, by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
      · rw [hr', List.take_succ_eq_append_getElem ho, List.filter_append, ← hxo]
        have hxv : validRange x = false := by simp [validRange]; scalar_tac
        simpa [hxv] using hpre
      · exact fun i hi hj hge => hsuffix i hi hj (by scalar_tac)
  · simp only [hlt, ↓reduceIte, spec_ok]
    have heq : read.val = original.val.length := by scalar_tac
    exact ⟨hsize, by omega, by simpa [heq] using hpre⟩

end YoctoCore.Properties.OrderRangeSort
