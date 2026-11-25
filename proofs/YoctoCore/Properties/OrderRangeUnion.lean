import YoctoCore.Properties.OrderRangeNormalize

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

namespace YoctoCore.Properties.OrderRange

private theorem head_bounds {x : order_range.ClockRange} {xs : List order_range.ClockRange}
    (can : CanonicalList (x :: xs)) :
    x.start.val < x.end.val ∧ CanonicalList xs ∧
    (∀ y ∈ xs, x.end.val < y.start.val) := by
  obtain ⟨valid, pairs⟩ := (canonical_pairwise _).mp can
  obtain ⟨after, tail⟩ := List.pairwise_cons.mp pairs
  exact ⟨valid x (by simp), (canonical_pairwise _).mpr
    ⟨fun y hy => valid y (by simp [hy]), tail⟩, after⟩

private theorem head_minimum {x : order_range.ClockRange} {xs : List order_range.ClockRange}
    (can : CanonicalList (x :: xs)) (c : U64) (h : inRangesList (x :: xs) c) :
    x.start.val ≤ c.val := by
  obtain ⟨valid, _, after⟩ := head_bounds can
  obtain ⟨y, hy, lo, _⟩ := (inRangesList_iff_mem _ _).mp h
  rcases List.mem_cons.mp hy with rfl | tail
  · exact lo
  · have := after y tail
    omega

private theorem end_gap {x : order_range.ClockRange} {xs : List order_range.ClockRange}
    (can : CanonicalList (x :: xs)) : ¬inRangesList (x :: xs) x.end := by
  obtain ⟨_, _, after⟩ := head_bounds can
  rintro h
  obtain ⟨y, hy, lo, hi⟩ := (inRangesList_iff_mem _ _).mp h
  rcases List.mem_cons.mp hy with rfl | tail
  · omega
  · have := after y tail
    omega

private theorem belongs_to_head (x : order_range.ClockRange) (xs : List order_range.ClockRange)
    (c : U64) (lo : x.start.val ≤ c.val) (hi : c.val < x.end.val) : inRangesList (x :: xs) c :=
  (inRangesList_iff_mem _ _).mpr ⟨x, by simp, lo, hi⟩

private theorem tail_after_head {x : order_range.ClockRange} {xs : List order_range.ClockRange}
    (can : CanonicalList (x :: xs)) (c : U64) (h : inRangesList xs c) : x.end.val < c.val := by
  obtain ⟨y, hy, lo, _⟩ := (inRangesList_iff_mem _ _).mp h
  exact lt_of_lt_of_le ((head_bounds can).2.2 y hy) lo

/-- Canonical separated half-open intervals are determined by their clock membership. -/
theorem canonical_ext {l r : List order_range.ClockRange} (hl : CanonicalList l)
    (hr : CanonicalList r) (mem : ∀ c, inRangesList l c ↔ inRangesList r c) : l = r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => rfl
    | cons y ys =>
      have no := (mem y.start).mpr (belongs_to_head y ys y.start (by omega) (head_bounds hr).1)
      exact by simp [inRangesList_iff_mem] at no
  | cons x xs ih =>
    have xv := (head_bounds hl).1
    have hx := (mem x.start).mp (belongs_to_head x xs x.start (by omega) xv)
    cases r with
    | nil => exact by simp [inRangesList_iff_mem] at hx
    | cons y ys =>
      have yv := (head_bounds hr).1
      have hy := (mem y.start).mpr (belongs_to_head y ys y.start (by omega) yv)
      have xlo := head_minimum hl y.start hy
      have ylo := head_minimum hr x.start hx
      have starts : x.start.val = y.start.val := by omega
      have ends : x.end.val = y.end.val := by
        apply Nat.le_antisymm
        · by_contra h
          exact end_gap hr ((mem y.end).mp (belongs_to_head x xs y.end (by omega) (by omega)))
        · by_contra h
          exact end_gap hl ((mem x.end).mpr (belongs_to_head y ys x.end (by omega) (by omega)))
      have same : x = y := by
        cases x; cases y
        congr 1 <;> apply UScalar.eq_of_val_eq <;> assumption
      subst y
      congr 1
      apply ih (head_bounds hl).2.1 (head_bounds hr).2.1
      intro c
      have all := mem c
      change inRangesList ([x] ++ xs) c ↔ inRangesList ([x] ++ ys) c at all
      rw [inRangesList_append, inRangesList_append, inRangesList_singleton] at all
      have lbound := tail_after_head hl c
      have rbound := tail_after_head hr c
      constructor
      · intro h
        rcases all.mp (Or.inr h) with head | found
        · have := lbound h; omega
        · exact found
      · intro h
        rcases all.mpr (Or.inr h) with head | found
        · have := rbound h; omega
        · exact found


abbrev ClockList := List order_range.ClockRange

private def precedes (a b : order_range.ClockRange) : Bool := decide (a.start.val ≤ b.start.val)

/-- Remaining canonical union after the two cursors, starting from a reverse accumulator.
    Incoming ranges precede old ranges at equal starts, as in the extracted code. -/
def finishUnion (old incoming acc : ClockList) : ClockList :=
  ((incoming.merge old precedes).foldl pushRange acc).reverse

private theorem fold_length_floor (xs acc : ClockList) :
    acc.length ≤ (xs.foldl pushRange acc).length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    have first : acc.length ≤ (pushRange acc x).length := by
      cases acc with
      | nil => simp
      | cons last tail => simp only [pushRange]; split <;> simp
    exact first.trans (ih _)

theorem finishUnion_length_floor (a b acc : ClockList) :
    acc.length ≤ (finishUnion a b acc).length := by
  simpa only [finishUnion,List.length_reverse] using fold_length_floor (b.merge a precedes) acc

theorem finishUnion_left (x : order_range.ClockRange) (xs incoming acc : ClockList)
    (first : ∀ y, incoming.head? = some y → x.start.val < y.start.val) :
    finishUnion (x :: xs) incoming acc = finishUnion xs incoming (pushRange acc x) := by
  cases incoming with
  | nil => simp [finishUnion]
  | cons y ys =>
    have later : ¬y.start.val ≤ x.start.val := Nat.not_le_of_lt (first y rfl)
    simp [finishUnion,precedes,later]

theorem finishUnion_right (y : order_range.ClockRange) (old ys acc : ClockList)
    (first : ∀ x, old.head? = some x → y.start.val ≤ x.start.val) :
    finishUnion old (y :: ys) acc = finishUnion old ys (pushRange acc y) := by
  cases old with
  | nil => simp [finishUnion]
  | cons x xs =>
    have earlier := first x rfl
    simp [finishUnion,precedes,earlier]

theorem finishUnion_semantics (old inc : ClockList) (left : CanonicalList old) (right : CanonicalList inc) :
    CanonicalList (finishUnion old inc []) ∧
    ∀ c, inRangesList (finishUnion old inc []) c ↔ inRangesList old c ∨ inRangesList inc c := by
  let sequence := inc.merge old precedes
  have sorted (l : ClockList) (h : CanonicalList l) : l.Pairwise (fun a b => precedes a b = true) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj ij
    simpa [precedes] using Nat.le_of_lt (canonicalList_start_lt h ij hj)
  have perm : sequence.Perm (inc ++ old) := List.merge_perm_append precedes
  have valid (x) (hx : x ∈ sequence) : x.start.val < x.end.val := by
    rcases List.mem_append.mp (perm.mem_iff.mp hx) with hi | ho
    · exact ((canonical_pairwise inc).mp right).1 x hi
    · exact ((canonical_pairwise old).mp left).1 x ho
  have order : sequence.Pairwise (fun a b => a.start.val ≤ b.start.val) := by
    have merged := List.pairwise_merge (le := precedes)
      (by intro a b c h k; simp [precedes] at *; omega)
      (by intro a b; simp [precedes]; omega) inc old (sorted inc right) (sorted old left)
    simpa [sequence,precedes] using merged
  have result : CanonicalList (finishUnion old inc []) ∧
      ∀ c, inRangesList (finishUnion old inc []) c ↔ inRangesList sequence c := by
    by_cases empty : sequence = []
    · change CanonicalList (sequence.foldl pushRange []).reverse ∧ ∀ c, inRangesList (sequence.foldl pushRange []).reverse c ↔ inRangesList sequence c
      simp [empty,CanonicalList]
    · exact fold_single sequence empty valid order
  refine ⟨result.1,fun c => ?_⟩
  rw [result.2,←inRangesList_append]
  simp only [inRangesList_iff_mem,(perm.trans List.perm_append_comm).mem_iff]

/-- There exists a canonical representation of the exact union within the fragment limit. -/
def UnionFits (old inc : ClockList) (limit : Nat) : Prop :=
  ∃ l : ClockList, CanonicalList l ∧ l.length ≤ limit ∧
    ∀ c, inRangesList l c ↔ inRangesList old c ∨ inRangesList inc c

theorem unionFits_iff {old inc : ClockList} (hc : CanonicalList old)
    (ic : CanonicalList inc) (limit : Nat) :
    UnionFits old inc limit ↔ (finishUnion old inc []).length ≤ limit := by
  have ⟨can,mem⟩ := finishUnion_semantics old inc hc ic
  constructor
  · rintro ⟨l,hc,room,sem⟩
    have eq := canonical_ext hc can fun c => (sem c).trans (mem c).symm
    simpa only [←eq] using room
  · intro room
    exact ⟨_,can,room,mem⟩

private theorem finishUnion_length (old inc : ClockList) :
    (finishUnion old inc []).length ≤ old.length + inc.length := by
  have upper (seq acc : ClockList) : (seq.foldl pushRange acc).length ≤ acc.length+seq.length := by
    induction seq generalizing acc with
    | nil => simp
    | cons x xs ih =>
      have one : (pushRange acc x).length ≤ acc.length+1 := by
        cases acc with
        | nil => simp [pushRange]
        | cons last tail => simp only [pushRange]; split <;> simp
      simp only [List.foldl_cons,List.length_cons]
      have next := ih (pushRange acc x)
      omega
  have size := (List.merge_perm_append (xs := inc) (ys := old) (le := precedes)).length_eq
  simpa only [finishUnion,List.length_reverse,List.length_nil,Nat.zero_add,size,List.length_append,Nat.add_comm,Nat.add_zero] using
    upper (inc.merge old precedes) []

theorem unionFits_of_room {old inc : ClockList} {cap : Nat} (co : CanonicalList old) (ci : CanonicalList inc)
    (room : old.length+inc.length ≤ cap) : UnionFits old inc cap :=
  (unionFits_iff co ci cap).mpr ((finishUnion_length old inc).trans room)

theorem canonical_union_count {old inc out : ClockList}
    (co : CanonicalList old) (ci : CanonicalList inc) (cr : CanonicalList out)
    (mem : ∀ c, inRangesList out c ↔ inRangesList old c ∨ inRangesList inc c) :
    out.length ≤ old.length+inc.length := by
  have ⟨can,sem⟩ := finishUnion_semantics old inc co ci
  rw [canonical_ext cr can (fun c => (mem c).trans (sem c).symm)]
  exact finishUnion_length old inc

/-- Renormalizing an incoming vector preserves the final-capacity condition. -/
theorem unionFits_congr_right {old a b : ClockList} (limit : Nat)
    (equiv : ∀ c, inRangesList a c ↔ inRangesList b c) :
    UnionFits old a limit ↔ UnionFits old b limit := by
  constructor
  · rintro ⟨out,can,count,mem⟩
    exact ⟨out,can,count,fun c => (mem c).trans (or_congr Iff.rfl (equiv c))⟩
  · rintro ⟨out,can,count,mem⟩
    exact ⟨out,can,count,fun c => (mem c).trans (or_congr Iff.rfl (equiv c).symm)⟩

/-- A disjoint next element starts a component which no later step removes. -/
theorem finishUnion_exceeds {old incoming acc : ClockList} {limit : Nat}
    (x : order_range.ClockRange) (full : acc.length = limit)
    (apart : ∀ last, acc.head? = some last → last.end.val < x.start.val) :
    limit < (finishUnion old incoming (pushRange acc x)).length := by
  have raised : (pushRange acc x).length = limit+1 := by
    cases acc with
    | nil => simp only [List.length_nil] at full; subst limit; rfl
    | cons last tail =>
      have later := apart last rfl
      have split : ¬x.start ≤ last.end := by scalar_tac
      simp only [pushRange, split, ↓reduceIte, List.length_cons]
      simp only [List.length_cons] at full
      omega
  exact Nat.lt_of_lt_of_le (by omega) (finishUnion_length_floor old incoming _)

/-- Construction accepts any raw input for which a canonical representation fits. -/
theorem from_vec_with_capacity_final_spec (ranges : Ranges) (hint : Usize)
    (fits : UnionFits [] ranges.val (2^30)) :
    order_range.OrderRange.from_vec_with_capacity ranges hint ⦃ out =>
      Canonical out ∧ ∀ c, inRanges out c ↔ inRangesList ranges.val c ⦄ := by
  unfold order_range.OrderRange.from_vec_with_capacity
  step with canonicalize_spec ranges as ⟨n,buf,_,size,can,mem⟩
  obtain ⟨witness,wc,room,spec⟩ := fits
  have eq : buf.val.take n.val = witness := by
    apply canonical_ext can wc
    intro c
    have empty : ¬inRangesList [] c := by simp [inRangesList_iff_mem]
    exact (mem c).trans (by simpa only [empty,false_or] using (spec c).symm)
  have length : (buf.val.take n.val).length = n.val := by
    rw [List.length_take,Nat.min_eq_left size]
  have bound : n.val ≤ 2^30 := by rw [←length,eq]; exact room
  step with from_prefix_spec buf n hint size bound can as ⟨out,oc,view⟩
  exact ⟨oc,fun c => by simpa only [inRanges,view] using mem c⟩

theorem from_vec_final_spec (ranges : Ranges) (fits : UnionFits [] ranges.val (2^30)) :
    order_range.OrderRange.from_vec ranges ⦃ out =>
      Canonical out ∧ ∀ c, inRanges out c ↔ inRangesList ranges.val c ⦄ :=
  from_vec_with_capacity_final_spec ranges 0#usize fits


private abbrev UnionResult := core.result.Result Unit CodecError × order_range.OrderRange
private abbrev UnionState := Ranges × Usize × Usize

/-- The unconsumed suffix supplied to the stream after incrementing a cursor. -/
private theorem drop_cursor (xs : ClockList) {i : Nat} (live : i < xs.length) :
    xs.drop i = xs[i] :: xs.drop (i+1) := by
  exact List.drop_eq_getElem_cons live

private theorem choose_union_input (self : order_range.OrderRange)
    (first second : Slice order_range.ClockRange) (n count i j : Usize)
    (P : Usize × Usize × order_range.ClockRange → Prop)
    (valid : storageWF self) (size : n.val = (toList self).length)
    (incoming : count.val = first.length + second.length)
    (oldBound : i.val ≤ n.val) (newBound : j.val ≤ count.val)
    (live : i.val < n.val ∨ j.val < count.val)
    (takeOld : ∀ (x : order_range.ClockRange) (ix : i.val < (toList self).length),
      x = (toList self)[i.val] →
      (∀ y, ((first.val ++ second.val).drop j.val).head? = some y → x.start.val < y.start.val) →
      ∀ next : Usize, next.val = i.val+1 → P (next,j,x))
    (takeNew : ∀ (x : order_range.ClockRange) (jx : j.val < (first.val ++ second.val).length),
      x = (first.val ++ second.val)[j.val] →
      (∀ y, ((toList self).drop i.val).head? = some y → x.start.val ≤ y.start.val) →
      ∀ next : Usize, next.val = j.val+1 → P (i,next,x)) :
    (if j = count then do
       let x ← order_range.OrderRange.at self i
       let next ← i + 1#usize
       ok (next,j,x)
     else do
       let x ← if j < first.len then Slice.index_usize first j else do
         let k ← j - first.len
         Slice.index_usize second k
       if i < n then
         let old ← order_range.OrderRange.at self i
         if old.start < x.start then
           let next ← i + 1#usize
           ok (next,j,old)
         else
           let next ← j + 1#usize
           ok (i,next,x)
       else
         let next ← j + 1#usize
         ok (i,next,x)) ⦃ P ⦄ := by
  let incomingList := first.val ++ second.val
  have allSize : incomingList.length = count.val := by simp [incomingList,incoming]
  by_cases endNew : j = count
  · simp only [endNew,↓reduceIte]
    have ix : i.val < (toList self).length := by rw [endNew] at live; omega
    step with at_spec self i valid ix as ⟨x,hx⟩
    step as ⟨next,hn⟩
    rw [←endNew]
    apply takeOld x ix hx _ next hn
    have endAt : (first.val ++ second.val).length ≤ j.val := by rw [endNew,←allSize]
    intro y hy
    rw [List.drop_of_length_le endAt] at hy
    contradiction
  · have jl : j.val < count.val := by
      have different : j.val ≠ count.val := fun eq => endNew (UScalar.eq_of_val_eq eq)
      omega
    have jx : j.val < incomingList.length := by omega
    have read :
        (if j < first.len then Slice.index_usize first j else do
          let k ← j - first.len
          Slice.index_usize second k) ⦃ x => x = incomingList[j.val] ⦄ := by
      by_cases left : j < first.len
      · simp only [left,↓reduceIte]
        have il : j.val < first.length := by scalar_tac
        step with Slice.index_usize_spec first j il as ⟨x,hx⟩
        simpa only [incomingList,List.getElem_append_left il] using hx
      · simp only [left,↓reduceIte]
        have after : first.length ≤ j.val := by scalar_tac
        step as ⟨k,hk⟩
        have kl : k.val < second.length := by scalar_tac
        step with Slice.index_usize_spec second k kl as ⟨x,hx⟩
        have fl : first.len.val = first.val.length := by scalar_tac
        simpa only [incomingList,List.getElem_append_right after,hk,fl] using hx
    simp only [endNew,↓reduceIte]
    step with read as ⟨x,hx⟩
    by_cases available : i < n
    · simp only [available,↓reduceIte]
      have ix : i.val < (toList self).length := by scalar_tac
      step with at_spec self i valid ix as ⟨old,ho⟩
      by_cases earlier : old.start < x.start
      · simp only [earlier,↓reduceIte]
        step as ⟨next,hn⟩
        apply takeOld old ix ho _ next hn
        intro y hy
        change (incomingList.drop j.val).head? = some y at hy
        rw [drop_cursor incomingList jx] at hy
        have eq : incomingList[j.val] = y := Option.some.inj hy
        rw [←eq,←hx]; exact earlier
      · simp only [earlier,↓reduceIte]
        step as ⟨next,hn⟩
        apply takeNew x jx hx _ next hn
        intro y hy
        rw [drop_cursor (toList self) ix] at hy
        have eq : (toList self)[i.val] = y := Option.some.inj hy
        rw [←eq,←ho]; scalar_tac
    · simp only [available,↓reduceIte]
      step as ⟨next,hn⟩
      apply takeNew x jx hx _ next hn
      intro y hy
      rw [List.drop_of_length_le (show (toList self).length ≤ i.val by scalar_tac)] at hy
      contradiction


private theorem union_clock_max (a b : Std.U64) : core.cmp.impls.OrdU64.max a b = max a b := by
  unfold core.cmp.impls.OrdU64.max
  split
  · rename_i h
    exact (max_eq_left (le_of_lt h)).symm
  · rename_i h
    exact (max_eq_right (le_of_not_gt h)).symm

private theorem bounded_union_step (v : Ranges) (x : order_range.ClockRange)
    (oi ni limit : Std.Usize) (self : order_range.OrderRange)
    (bounded : v.length ≤ limit.val) (cap : limit.val ≤ 2^30)
    (P : ControlFlow (Ranges × Std.Usize × Std.Usize) UnionResult → Prop)
    (reject : v.length = limit.val →
      (∀ last, v.val.reverse.head? = some last → last.end.val < x.start.val) →
      P (done (core.result.Result.Err CodecError.LimitExceeded,self)))
    (next : ∀ w : Ranges, w.length ≤ limit.val → w.val = (pushRange v.val.reverse x).reverse →
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
          if n = limit then ok (done (core.result.Result.Err CodecError.LimitExceeded,self))
          else do
            let w ← v.push x
            ok (cont (w,oi,ni))
      else
        if n = limit then ok (done (core.result.Result.Err CodecError.LimitExceeded,self))
        else do
          let w ← v.push x
          ok (cont (w,oi,ni))) ⦃ P ⦄ := by
  have vlen : v.len.val = v.length := by scalar_tac
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
      · rw [hw]; simpa [alloc.vec.Vec.set] using bounded
      rw [hw]
      have value : current = last := hp.trans hl.symm
      have same : again = last := ha.trans hl.symm
      have mx : core.cmp.impls.OrdU64.max again.end x.end = max last.end x.end := by
        rw [same,union_clock_max]
      simp only [alloc.vec.Vec.set,rev,pushRange,touching,↓reduceIte,hu,mx,value,
        List.reverse_cons,List.reverse_reverse]
      let item : order_range.ClockRange := {last with «end» := max last.end x.end}
      have lenSet : (v.val.set i.val item).length ≤ i.val+1 := by simp [size]
      have itemEq := take_next_set v.val i.val item live
      rw [List.take_of_length_le lenSet] at itemEq
      simpa [pre,item] using itemEq
    · simp only [touching,↓reduceIte]
      by_cases full : v.len = limit
      · simp only [full,↓reduceIte,spec_ok]
        apply reject (vlen.symm.trans (congrArg UScalar.val full))
        intro y hy
        rw [rev] at hy
        have same : last = y := Option.some.inj hy
        subst y
        exact Nat.lt_of_not_ge touching
      · have room : v.length < 2^30 := by
          have diff : v.len.val ≠ limit.val := fun eq => full (UScalar.eq_of_val_eq eq)
          omega
        simp only [full,↓reduceIte]
        step as ⟨w,hw⟩
        apply next
        · have diff : v.len.val ≠ limit.val := fun eq => full (UScalar.eq_of_val_eq eq)
          have room' : v.length < limit.val := by omega
          change w.val.length ≤ limit.val
          rw [hw,List.length_append,List.length_singleton]
          exact Nat.succ_le_of_lt room'
        simpa only [rev,pushRange,touching,↓reduceIte,List.reverse_cons,List.reverse_reverse,←front] using hw
  · simp only [nonempty,↓reduceIte]
    have empty : v.val = [] := List.length_eq_zero_iff.mp (by scalar_tac)
    by_cases full : v.len = limit
    · simp only [full,↓reduceIte,spec_ok]
      apply reject (vlen.symm.trans (congrArg UScalar.val full))
      simp [empty]
    · have room : v.length < 2^30 := by simp [empty,alloc.vec.Vec.length]
      simp only [full,↓reduceIte]
      step as ⟨w,hw⟩
      apply next
      · have diff : v.len.val ≠ limit.val := fun eq => full (UScalar.eq_of_val_eq eq)
        have len := congrArg List.length hw
        simp [empty] at len
        scalar_tac
      simpa [empty,pushRange] using hw


/-- The error case returns the same representation, including every backing slot. -/
private def UnionOutcome (self : order_range.OrderRange) (incoming : ClockList)
    (limit : Nat) (result : UnionResult) : Prop :=
  match result.1 with
  | .Ok _ => Canonical result.2 ∧ toList result.2 = finishUnion (toList self) incoming [] ∧
      (toList result.2).length ≤ limit
  | .Err e => e = CodecError.LimitExceeded ∧ result.2 = self ∧
      limit < (finishUnion (toList self) incoming []).length

private theorem try_union_loop_spec (self : order_range.OrderRange)
    (first second : Slice order_range.ClockRange) (limit n count : Usize)
    (can : Canonical self) (ic : CanonicalList (first.val ++ second.val))
    (size : n.val = (toList self).length)
    (incoming : count.val = first.length + second.length)
    (cap : limit.val ≤ 2^30) :
    order_range.OrderRange.try_union_slices_loop self first second limit
      (alloc.vec.Vec.new _) 0#usize 0#usize n count
      ⦃ result => UnionOutcome self (first.val ++ second.val) limit.val result ⦄ := by
  let old := toList self
  let src := first.val ++ second.val
  let final := finishUnion old src []
  have sl : src.length = count.val := by simp [src,incoming]
  let inv : UnionState → Prop := fun (v,i,j) =>
    i.val ≤ n.val ∧ j.val ≤ count.val ∧ v.length ≤ limit.val ∧
    finishUnion (old.drop i.val) (src.drop j.val) v.val.reverse = final
  unfold order_range.OrderRange.try_union_slices_loop
  refine loop.spec_decr_nat (fun (_,i,j) => n.val-i.val+(count.val-j.val)) inv _ _ _ ?_ ?_
  · intro ⟨v,i,j⟩ ⟨ib,jb,bounded,acc⟩
    let P : ControlFlow UnionState UnionResult → Prop := fun z => match z with
      | done r => UnionOutcome self src limit.val r
      | cont w => inv w ∧ n.val-w.2.1.val+(count.val-w.2.2.val) < n.val-i.val+(count.val-j.val)
    let selected : Usize × Usize × order_range.ClockRange → Prop := fun (oi,ni,x) =>
      oi.val ≤ n.val ∧ ni.val ≤ count.val ∧
      n.val-oi.val+(count.val-ni.val) < n.val-i.val+(count.val-j.val) ∧
      finishUnion (old.drop oi.val) (src.drop ni.val) (pushRange v.val.reverse x) = final
    have chooseOld (x : order_range.ClockRange) (ix : i.val < old.length)
        (eq : x = old[i.val])
        (ordered : ∀ y, (src.drop j.val).head? = some y → x.start.val < y.start.val)
        (oi : Usize) (stepI : oi.val = i.val+1) : selected (oi,j,x) := by
      refine ⟨by dsimp [old] at ix; omega,jb,by dsimp [old] at ix; omega,?_⟩
      rw [stepI,←finishUnion_left x _ _ _ ordered,eq,←drop_cursor old ix]
      exact acc
    have chooseNew (x : order_range.ClockRange) (jx : j.val < src.length)
        (eq : x = src[j.val])
        (ordered : ∀ y, (old.drop i.val).head? = some y → x.start.val ≤ y.start.val)
        (ni : Usize) (stepJ : ni.val = j.val+1) : selected (i,ni,x) := by
      refine ⟨ib,by omega,by omega,?_⟩
      rw [stepJ,←finishUnion_right x _ _ _ ordered,eq,←drop_cursor src jx]
      exact acc
    have advance (oi ni : Usize) (x : order_range.ClockRange) (picked : selected (oi,ni,x)) :=
      bounded_union_step v x oi ni limit self bounded cap P
        (by
          intro full apart
          have overflow := finishUnion_exceeds (old := old.drop oi.val) (incoming := src.drop ni.val)
            (acc := v.val.reverse) x (by simpa using full) apart
          refine ⟨rfl,rfl,?_⟩
          change limit.val < final.length
          rw [←picked.2.2.2]
          exact overflow)
        (by
          intro w fits eq
          refine ⟨⟨picked.1,picked.2.1,fits,?_⟩,picked.2.2.1⟩
          simpa only [eq,List.reverse_reverse] using picked.2.2.2)
    unfold order_range.OrderRange.try_union_slices_loop.body
    dsimp only
    by_cases il : i < n
    · rw (occs := .pos [1]) [if_pos il]
      step with choose_union_input self first second n count i j selected can.1 size incoming ib jb
        (Or.inl (by scalar_tac)) chooseOld chooseNew as ⟨oi,ni,x,hp⟩
      exact spec_mono (advance oi ni x hp) (fun z hz => by cases z <;> exact hz)
    · by_cases jl : j < count
      · rw (occs := .pos [1]) [if_neg il]
        rw (occs := .pos [1]) [if_pos jl]
        step with choose_union_input self first second n count i j selected can.1 size incoming ib jb
          (Or.inr (by scalar_tac)) chooseOld chooseNew as ⟨oi,ni,x,hp⟩
        exact spec_mono (advance oi ni x hp) (fun z hz => by cases z <;> exact hz)
      · simp only [if_neg il,if_neg jl]
        have oi : old.length ≤ i.val := by dsimp [old]; scalar_tac
        have ni : src.length ≤ j.val := by scalar_tac
        have view : v.val = final := by
          simpa [List.drop_of_length_le oi,List.drop_of_length_le ni,finishUnion] using acc
        have model := finishUnion_semantics old src can.2 ic
        have all : v.val.take v.len.val = v.val := List.take_of_length_le (by scalar_tac)
        step with from_prefix_spec v v.len 0#usize (by scalar_tac) (by scalar_tac)
          (by rw [all,view]; exact model.1) as ⟨out,oc,contents⟩
        exact ⟨oc,contents.trans (all.trans view),by rw [contents,all]; exact bounded⟩
  · simp [inv,alloc.vec.Vec.new,final]

/-- Bounded streaming merge succeeds exactly when the canonical union fits. -/
theorem try_union_slices_spec (self : order_range.OrderRange) (first second : Slice order_range.ClockRange)
    (limit : Usize) (can : Canonical self) (ic : CanonicalList (first.val ++ second.val))
    (size : first.length + second.length ≤ Usize.max) (cap : limit.val ≤ 2^30) :
    order_range.OrderRange.try_union_slices self first second limit ⦃ result =>
      (result.1 = .Ok () ↔ UnionFits (toList self) (first.val ++ second.val) limit.val) ∧
      match result.1 with
      | .Ok _ => Canonical result.2 ∧ ∀ c, inRanges result.2 c ↔
          inRanges self c ∨ inRangesList (first.val ++ second.val) c
      | .Err e => e = CodecError.LimitExceeded ∧ result.2 = self ⦄ := by
  unfold order_range.OrderRange.try_union_slices
  step with len_spec self can.1 as ⟨n,hn⟩
  step as ⟨count,hs⟩
  apply spec_mono (try_union_loop_spec self first second limit n count can ic hn (by scalar_tac) cap)
  rintro ⟨status,out⟩ h
  rw [unionFits_iff can.2 ic]
  cases status with
  | Ok u =>
    obtain ⟨oc,eq,bound⟩ := h
    cases u
    exact ⟨by simp [←eq,bound],oc,fun c => by
      change inRangesList (toList out) c ↔ _
      rw [eq]
      exact (finishUnion_semantics _ _ can.2 ic).2 c⟩
  | Err e =>
    obtain ⟨he,same,overflow⟩ := h
    exact ⟨by simp [Nat.not_le_of_lt overflow],he,same⟩

end YoctoCore.Properties.OrderRange
