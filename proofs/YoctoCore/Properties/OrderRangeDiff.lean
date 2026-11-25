import YoctoCore.Properties.OrderRange
open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.OrderRange

private abbrev ClockRanges := List order_range.ClockRange

/-- Consume the old ranges contained in one new range. The result records
    the first unconsumed index and the gaps written so far, even on failure. -/
private def diffScan (finish : Std.U64) : ClockRanges → Nat → Std.U64 →
    ClockRanges → Option Nat × ClockRanges
  | [], i, pos, acc =>
    (some i, if pos < finish then acc ++ [⟨pos,finish⟩] else acc)
  | old :: rest, i, pos, acc =>
    if old.start < finish then
      if old.start < pos ∨ finish < old.end then (none, acc)
      else diffScan finish rest (i+1) old.end
        (if pos < old.start then acc ++ [⟨pos,old.start⟩] else acc)
    else (some i, if pos < finish then acc ++ [⟨pos,finish⟩] else acc)

private theorem drop_head_step {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    l.drop i = l[i] :: l.drop (i+1) := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [List.drop_succ_cons, List.getElem_cons_succ] using ih i (by simpa using h)

private theorem diff_one_scan (self : order_range.OrderRange) (wf : storageWF self)
    (start : Std.Usize) (r : order_range.ClockRange) (buf : alloc.vec.Vec order_range.ClockRange)
    (index : start.val ≤ (toList self).length)
    (room : buf.length + ((toList self).length-start.val) + 1 ≤ Usize.max) :
    order_range.OrderRange.diff_one self start r buf ⦃ (next,out) =>
      (next.map UScalar.val, out.val) =
        diffScan r.end ((toList self).drop start.val) start.val r.start buf.val ⦄ := by
  let src := toList self
  let expected := diffScan r.end (src.drop start.val) start.val r.start buf.val
  let inv : Std.Usize × (alloc.vec.Vec order_range.ClockRange) × Std.U64 → Prop := fun (i,out,pos) =>
    i.val ≤ src.length ∧ out.length + (src.length-i.val) + 1 ≤ Usize.max ∧
    diffScan r.end (src.drop i.val) i.val pos out.val = expected
  unfold order_range.OrderRange.diff_one order_range.OrderRange.diff_one_loop
  refine loop.spec_decr_nat (fun (i,_,_) => src.length-i.val) inv _ _ _ ?_ ⟨index,room,rfl⟩
  intro ⟨i,out,pos⟩ ⟨bound,capacity,model⟩
  unfold order_range.OrderRange.diff_one_loop.body
  simp only
  step with len_spec self wf as ⟨n,hn⟩
  have finishCase (eq : (some i.val, if pos < r.end then out.val ++ [⟨pos,r.end⟩] else out.val) = expected) :
      (if pos < r.end then do
          let v ← alloc.vec.Vec.push out (⟨pos,r.end⟩ : order_range.ClockRange)
          ok (done (some i,v) : ControlFlow (Std.Usize × _ × Std.U64) _)
        else ok (done (some i,out))) ⦃ c => match c with
          | done (next, v) => (next.map UScalar.val, v.val) = expected
          | cont s => inv s ∧ src.length-s.1.val < src.length-i.val ⦄ := by
    split_ifs with emit
    · step as ⟨v,hv⟩
      simpa only [hv,emit,↓reduceIte,Option.map_some] using eq
    · simpa only [spec_ok,Option.map_some,emit,↓reduceIte] using eq
  by_cases live : i < n
  · simp only [live, ↓reduceIte]
    have hi : i.val < src.length := by change i.val < (toList self).length; scalar_tac
    step with at_spec self i wf hi as ⟨old,ho⟩
    rw [drop_head_step src i.val hi, ← ho, diffScan] at model
    by_cases before : old.start < r.end
    · simp only [before, ↓reduceIte] at model ⊢
      by_cases partialLeft : old.start < pos
      · simpa only [partialLeft, true_or, ↓reduceIte, spec_ok, Option.map_none] using model
      · simp only [partialLeft, false_or, ↓reduceIte] at model ⊢
        by_cases partialRight : old.end > r.end
        · simpa only [partialRight, ↓reduceIte, spec_ok, Option.map_none] using model
        · simp only [partialRight, ↓reduceIte] at model ⊢
          by_cases gap : pos < old.start
          · simp only [gap, ↓reduceIte] at model ⊢
            step as ⟨v,hv⟩
            step as ⟨j,hj⟩
            have count : v.length = out.length+1 := by simp [alloc.vec.Vec.length,hv]
            exact ⟨⟨by omega, by omega, by simpa only [hv,hj] using model⟩,by omega⟩
          · simp only [gap, ↓reduceIte,bind_ok] at model ⊢
            step as ⟨j,hj⟩
            exact ⟨⟨by omega,by omega,by simpa only [hj] using model⟩,by omega⟩
    · simp only [before, ↓reduceIte] at model ⊢
      exact spec_mono (finishCase model) (by intro z hz; cases z <;> exact hz)
  · simp only [live, ↓reduceIte]
    have hi : src.length ≤ i.val := by change (toList self).length ≤ i.val; scalar_tac
    rw [List.drop_eq_nil_of_le hi, diffScan] at model
    exact spec_mono (finishCase model) (by intro z hz; cases z <;> exact hz)

private def gapList (lo hi : Std.U64) : ClockRanges :=
  if lo < hi then [⟨lo,hi⟩] else []

private theorem gapList_spec (lo hi : Std.U64) :
    CanonicalList (gapList lo hi) ∧ (gapList lo hi).length ≤ 1 ∧
    (∀ x ∈ gapList lo hi, x.start = lo ∧ x.end = hi) ∧
    ∀ c, inRangesList (gapList lo hi) c ↔ lo.val ≤ c.val ∧ c.val < hi.val := by
  unfold gapList
  split
  · simp [canonical_pairwise, inRangesList_singleton]
    scalar_tac
  · simp [canonical_pairwise, inRangesList_iff_mem]
    scalar_tac

private theorem appendGap (l : ClockRanges) (lo hi : Std.U64) :
    (if lo < hi then l ++ [⟨lo,hi⟩] else l) = l ++ gapList lo hi := by
  unfold gapList
  split <;> simp

private structure WindowDiff (input acc : ClockRanges) (pos finish : Std.U64)
    (i next : Nat) (out : ClockRanges) : Prop where
  parts : ∃ consumed rest gaps : ClockRanges,
    input = consumed ++ rest ∧ next = i + consumed.length ∧ out = acc ++ gaps ∧
    (∀ x ∈ consumed, pos.val ≤ x.start.val ∧ x.end.val ≤ finish.val) ∧
    (∀ x ∈ rest, finish.val ≤ x.start.val) ∧
    CanonicalList gaps ∧ (∀ x ∈ gaps, pos.val ≤ x.start.val ∧ x.end.val ≤ finish.val) ∧
    gaps.length ≤ consumed.length + 1 ∧
    ∀ c, inRangesList gaps c ↔
      pos.val ≤ c.val ∧ c.val < finish.val ∧ ¬inRangesList consumed c

private theorem diffScan_stop (l acc : ClockRanges) (pos finish : Std.U64) (i : Nat) (h : ∀ x ∈ l, finish.val ≤ x.start.val) :
      WindowDiff l acc pos finish i i (if pos < finish then acc ++ [⟨pos,finish⟩] else acc) := by
    obtain ⟨cg,ng,ends,mem⟩ := gapList_spec pos finish
    refine ⟨[], l, gapList pos finish, by simp, by simp, appendGap _ _ _,
      by simp, h, cg, ?_, by simpa using ng, ?_⟩
    · intro x hx
      obtain ⟨a,b⟩ := ends x hx
      simp [a,b]
    · intro c
      simpa only [inRangesList_iff_mem, List.not_mem_nil, false_and, exists_false, not_false_eq_true,
        and_true] using mem c

private theorem diffScan_semantics (l : ClockRanges) (can : CanonicalList l)
    (finish pos : Std.U64) (bound : pos.val ≤ finish.val) (i : Nat) (acc : ClockRanges) :
    match diffScan finish l i pos acc with
    | (some next,out) => WindowDiff l acc pos finish i next out
    | (none,_) => ∃ x ∈ l, x.start.val < pos.val ∨
        x.start.val < finish.val ∧ finish.val < x.end.val := by
  induction l generalizing pos i acc with
  | nil => exact diffScan_stop _ _ _ _ _ (by simp)
  | cons x xs ih =>
    obtain ⟨valid, pairs⟩ := (canonical_pairwise _).mp can
    obtain ⟨sep, ordered⟩ := List.pairwise_cons.mp pairs
    have xv := valid x (by simp)
    have tailCan := (canonical_pairwise _).mpr
      ⟨fun y hy => valid y (List.mem_cons_of_mem _ hy), ordered⟩
    unfold diffScan
    by_cases before : x.start < finish
    · simp only [before,↓reduceIte]
      by_cases bad : x.start < pos ∨ finish < x.end
      · simp only [bad,↓reduceIte]
        exact ⟨x, by simp, by rcases bad with h|h <;> scalar_tac⟩
      · simp only [bad,↓reduceIte]
        have lower : pos.val ≤ x.start.val := by scalar_tac
        have upper : x.end.val ≤ finish.val := by scalar_tac
        let first := gapList pos x.start
        obtain ⟨gc,gn,ge,gm⟩ := gapList_spec pos x.start
        rw [appendGap]
        generalize hv : diffScan finish xs (i+1) x.end (acc ++ gapList pos x.start) = ans
        have result := ih tailCan x.end upper (i+1) (acc ++ first)
        dsimp only [first] at result
        rw [hv] at result
        rcases ans with ⟨opt,out⟩
        cases opt with
        | none =>
          obtain ⟨y,hy,err⟩ := result
          have edge := sep y hy
          exact ⟨y, List.mem_cons_of_mem _ hy, by unfold BeforeRange at edge; omega⟩
        | some next =>
          obtain ⟨⟨ls,rs,ds,input,ni,output,active,pending,dc,de,dn,dm⟩⟩ := result
          refine ⟨x::ls,rs,first ++ ds,by simp [input],by simp [ni]; omega,
            by simpa [first,List.append_assoc] using output,?_,pending,?_,?_,?_,?_⟩
          · intro y hy
            rcases List.mem_cons.mp hy with rfl|hy
            · exact ⟨lower,upper⟩
            · have := active y hy
              omega
          · apply (canonical_append _ _).mpr
            refine ⟨gc,dc,?_⟩
            intro a ha b hb
            have ea := (ge a ha).2
            have eb := (de b hb).1
            unfold BeforeRange
            rw [ea]
            omega
          · intro y hy
            rcases List.mem_append.mp hy with hy|hy
            · obtain ⟨a,b⟩ := ge y hy
              rw [a,b]
              omega
            · have := de y hy
              omega
          · change (gapList pos x.start ++ ds).length ≤ (x::ls).length+1
            simp only [List.length_append,List.length_cons]
            omega
          · intro c
            have splitMem : inRangesList (x::ls) c ↔
                (x.start.val ≤ c.val ∧ c.val < x.end.val) ∨ inRangesList ls c := by
              simpa only [List.cons_append,List.nil_append,inRangesList_singleton] using inRangesList_append [x] ls c
            have after (h : inRangesList ls c) : x.end.val ≤ c.val := by
              obtain ⟨y,hy,hc,_⟩ := (inRangesList_iff_mem _ _).mp h
              have := active y hy
              omega
            rw [inRangesList_append,gm,dm,splitMem]
            constructor
            · rintro (⟨lb,ub⟩ | ⟨lb,ub,absent⟩)
              · exact ⟨lb,by omega,fun h => h.elim (fun e => by omega) (fun e => by have := after e; omega)⟩
              · exact ⟨by omega,ub,fun h => h.elim (fun e => by omega) absent⟩
            · rintro ⟨lb,ub,ex⟩
              by_cases left : c.val < x.start.val
              · exact Or.inl ⟨lb,left⟩
              · have endBefore : x.end.val ≤ c.val := by
                  by_contra below
                  exact ex (Or.inl ⟨by omega,by omega⟩)
                exact Or.inr ⟨endBefore,ub,fun member => ex (Or.inr member)⟩
    · simp only [before,↓reduceIte]
      apply diffScan_stop
      intro y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · scalar_tac
      · have edge := sep y hy
        unfold BeforeRange at edge
        scalar_tac

private def CoversClocks (outer inner : ClockRanges) : Prop :=
  ∀ c, inRangesList inner c → inRangesList outer c

/-- All intervals whose input cursors have advanced already contribute their
    exact difference. Each output interval belongs to a single new interval. -/
private structure DiffPrefix (taken left news out : ClockRanges) : Prop where
  covered : CoversClocks news taken
  later : ∀ a ∈ news, ∀ b ∈ left, a.end.val ≤ b.start.val
  canonical : CanonicalList out
  owner : ∀ x ∈ out, ∃ r ∈ news, r.start.val ≤ x.start.val ∧ x.end.val ≤ r.end.val
  length : out.length ≤ taken.length + news.length
  mem : ∀ c, inRangesList out c ↔ inRangesList news c ∧ ¬inRangesList taken c

private theorem no_past (news : ClockRanges) (c : Std.U64)
    (h : ∀ a ∈ news, a.end.val ≤ c.val) : ¬inRangesList news c := by
  rintro hc
  obtain ⟨a,ha,_,edge⟩ := (inRangesList_iff_mem _ _).mp hc
  exact (Nat.not_lt_of_ge (h a ha)) edge

private theorem no_future (news : ClockRanges) (c : Std.U64)
    (h : ∀ a ∈ news, c.val < a.start.val) : ¬inRangesList news c := by
  rintro hc
  obtain ⟨a,ha,edge,_⟩ := (inRangesList_iff_mem _ _).mp hc
  exact (Nat.not_le_of_gt (h a ha)) edge

private theorem diff_prefix_step (taken used pending news out gaps : ClockRanges)
    (r : order_range.ClockRange) (old : DiffPrefix taken (used ++ pending) news out)
    (sep : ∀ x ∈ news, x.end.val < r.start.val)
    (consumed : ∀ x ∈ used, r.start.val ≤ x.start.val ∧ x.end.val ≤ r.end.val)
    (remaining : ∀ x ∈ pending, r.end.val ≤ x.start.val)
    (gc : CanonicalList gaps)
    (within : ∀ x ∈ gaps, r.start.val ≤ x.start.val ∧ x.end.val ≤ r.end.val)
    (gn : gaps.length ≤ used.length+1)
    (gm : ∀ c, inRangesList gaps c ↔ r.start.val ≤ c.val ∧ c.val < r.end.val ∧ ¬inRangesList used c) :
    DiffPrefix (taken ++ used) pending (news ++ [r]) (out ++ gaps) := by
  have belongs (c : Std.U64) (h : inRangesList used c) :
      r.start.val ≤ c.val ∧ c.val < r.end.val := by
    obtain ⟨x,hx,a,b⟩ := (inRangesList_iff_mem _ _).mp h
    have := consumed x hx
    omega
  have disjoint (c : Std.U64) (h : r.start.val ≤ c.val) : ¬inRangesList news c := by
    apply no_past
    intro a ha
    have := sep a ha
    omega
  constructor
  · intro c hc
    rw [inRangesList_append, inRangesList_singleton]
    exact ((inRangesList_append _ _ _).mp hc).imp (old.covered c) (belongs c)
  · intro a ha b hb
    rcases List.mem_append.mp ha with ha|ha
    · exact old.later a ha b (List.mem_append_right _ hb)
    · obtain rfl := List.mem_singleton.mp ha
      exact remaining b hb
  · apply (canonical_append _ _).mpr
    refine ⟨old.canonical,gc,?_⟩
    intro x hx y hy
    obtain ⟨a,ha,_,xa⟩ := old.owner x hx
    have ar := sep a ha
    have ry := (within y hy).1
    unfold BeforeRange
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · obtain ⟨a,ha,e⟩ := old.owner x hx
      exact ⟨a,List.mem_append_left _ ha,e⟩
    · exact ⟨r,by simp,within x hx⟩
  · have := old.length
    simp only [List.length_append,List.length_singleton]
    omega
  · intro c
    rw [inRangesList_append out gaps,old.mem,gm,inRangesList_append news [r],
      inRangesList_singleton,inRangesList_append taken used]
    have c1 := old.covered c
    have c2 := belongs c
    have c3 := disjoint c
    tauto

private theorem diff_prefix_failure (taken left news future out : ClockRanges)
    (r : order_range.ClockRange) (old : DiffPrefix taken left news out)
    (valid : ∀ y ∈ left, y.start.val < y.end.val)
    (rv : r.start.val < r.end.val)
    (after : ∀ a ∈ future, r.end.val < a.start.val)
    (x : order_range.ClockRange) (hx : x ∈ left)
    (bad : x.start.val < r.start.val ∨ x.start.val < r.end.val ∧ r.end.val < x.end.val) :
    ¬ CoversClocks (news ++ r :: future) (taken ++ left) := by
  intro cov
  have impossible (c : Std.U64) (a : x.start.val ≤ c.val) (b : c.val < x.end.val)
      (outside : ¬(r.start.val ≤ c.val ∧ c.val < r.end.val)) (stop : c.val ≤ r.end.val) : False := by
    have used := cov c ((inRangesList_iff_mem _ _).mpr ⟨x,List.mem_append_right _ hx,a,b⟩)
    have earlier : ¬inRangesList news c := no_past _ _ (by
      intro y hy
      have h := old.later y hy x hx
      omega)
    have later : ¬inRangesList future c := no_future _ _ (by
      intro y hy
      have h := after y hy
      omega)
    have cons : inRangesList (r::future) c ↔
        (r.start.val ≤ c.val ∧ c.val < r.end.val) ∨ inRangesList future c := by
      simpa only [List.cons_append, List.nil_append, inRangesList_singleton] using inRangesList_append [r] future c
    rw [inRangesList_append,cons] at used
    tauto
  rcases bad with a|⟨a,b⟩
  · exact impossible x.start (Nat.le_refl _) (valid x hx) (by omega) (by omega)
  · exact impossible r.end (Nat.le_of_lt a) b (by omega) (Nat.le_refl _)

private theorem diff_prefix_leftover (taken left news out : ClockRanges)
    (old : DiffPrefix taken left news out) (x : order_range.ClockRange) (hx : x ∈ left)
    (valid : x.start.val < x.end.val) : ¬ CoversClocks news (taken ++ left) := by
  intro cov
  exact no_past news x.start (fun a ha => old.later a ha x hx)
    (cov x.start ((inRangesList_iff_mem _ _).mpr ⟨x,List.mem_append_right _ hx,Nat.le_refl _,valid⟩))

private theorem split_consumed {α : Type} (l used rest : List α) (i next : Nat)
    (hi : i ≤ l.length) (after : l.drop i = used ++ rest) (hn : next = i + used.length) :
    next ≤ l.length ∧ l.take next = l.take i ++ used ∧ l.drop next = rest := by
  let front := l.take i
  have fl : front.length = i := by simp [front, Nat.min_eq_left hi]
  have eq : l = (front ++ used) ++ rest := by
    rw [List.append_assoc, ← after, List.take_append_drop]
  have n : next = (front ++ used).length := by simp [fl,hn]
  have a : next ≤ l.length := by rw [eq,n]; simp
  refine ⟨a,?_,?_⟩
  · change l.take next = front ++ used
    conv => lhs; rw [eq,n,List.take_left]
  · rw [eq,n,List.drop_left]

private theorem canonical_size (r : order_range.OrderRange) (hc : Canonical r) :
    (toList r).length ≤ 2^30 := by
  rcases r with ⟨a|ring⟩
  · have len := List.length_filter_le (fun x : order_range.ClockRange => decide (x.start.val < x.end.val)) a.val
    have one : a.val.length = 1 := by simp
    change (a.val.filter _).length ≤ _
    omega
  · change (ringList ring).length ≤ _
    rw [ringList_length ring hc.1]
    exact Nat.le_trans hc.1.2.1 hc.1.2.2.2

private def DiffPost (old new out : ClockRanges) : Prop :=
  CanonicalList out ∧
  (CoversClocks new old → ∀ c, inRangesList out c ↔ inRangesList new c ∧ ¬inRangesList old c) ∧
  (¬CoversClocks new old → out = [])

theorem diff_range_spec (self new : order_range.OrderRange) (hc : Canonical self) (nc : Canonical new) :
    order_range.OrderRange.diff_range self new ⦃ out => CanonicalList out.val ∧
      ((∀ c, inRanges self c → inRanges new c) → ∀ c, inRangesList out.val c ↔
        inRanges new c ∧ ¬inRanges self c) ∧
      (¬(∀ c, inRanges self c → inRanges new c) → out.val = []) ⦄ := by
  let src := toList self
  let dst := toList new
  let inv : alloc.vec.Vec order_range.ClockRange × Std.Usize × Std.Usize → Prop := fun (out,i,j) =>
    i.val ≤ src.length ∧ j.val ≤ dst.length ∧
    DiffPrefix (src.take i.val) (src.drop i.val) (dst.take j.val) out.val
  change order_range.OrderRange.diff_range self new ⦃ out => DiffPost src dst out.val ⦄
  have noCover (h : ¬CoversClocks dst src) : DiffPost src dst [] :=
    ⟨by simp [canonical_pairwise], fun impossible => False.elim (h impossible), fun _ => rfl⟩
  have sizes : src.length + dst.length + 1 ≤ Usize.max := by
    have a := canonical_size self hc
    have b := canonical_size new nc
    dsimp [src,dst]
    scalar_tac
  unfold order_range.OrderRange.diff_range order_range.OrderRange.diff_range_loop
  refine loop.spec_decr_nat (fun (_,_,j) => dst.length-j.val) inv _ _ _ ?_ ?_
  · intro ⟨out,i,j⟩ ⟨hi,hj,state⟩
    unfold order_range.OrderRange.diff_range_loop.body
    simp only
    step with len_spec new nc.1 as ⟨n,hn⟩
    by_cases live : j < n
    · simp only [live,↓reduceIte]
      have jl : j.val < dst.length := by dsimp [dst]; scalar_tac
      step with at_spec new j nc.1 jl as ⟨r,hr⟩
      have splitNew : dst = dst.take j.val ++ r :: dst.drop (j.val+1) := by
        rw [hr, ←drop_head_step dst j.val jl, List.take_append_drop]
      have splitOld := (List.take_append_drop i.val src).symm
      have dc : CanonicalList (dst.take j.val ++ r :: dst.drop (j.val+1)) := splitNew ▸ nc.2
      obtain ⟨_,right,sides⟩ := (canonical_append _ _).mp dc
      have right' := (canonical_pairwise _).mp right
      have before := fun x hx => sides x hx r (by simp)
      have after := (List.pairwise_cons.mp right'.2).1
      have rv := right'.1 r (by simp)
      have sc : CanonicalList (src.drop i.val) :=
        ((canonical_append _ _).mp (by rw [List.take_append_drop]; exact hc.2 : CanonicalList (src.take i.val ++ src.drop i.val))).2.1
      have room : out.length + (src.length-i.val) + 1 ≤ Usize.max := by
        have h := state.length
        simp only [List.length_take,Nat.min_eq_left hi,Nat.min_eq_left hj] at h
        change out.val.length + _ + _ ≤ _
        omega
      step with diff_one_scan self hc.1 i r out hi room as ⟨opt,out1,model⟩
      have spec := diffScan_semantics (src.drop i.val) sc r.end r.start (Nat.le_of_lt rv) i.val out.val
      rw [← model] at spec
      cases opt with
      | none =>
        obtain ⟨x,hx,bad⟩ := spec
        simp only [spec_ok]
        change DiffPost src dst []
        apply noCover
        have no := diff_prefix_failure _ _ _ _ _ _ state ((canonical_pairwise _).mp sc).1 rv after x hx bad
        simpa only [←splitOld,←splitNew] using no
      | some next =>
        obtain ⟨⟨used,rest,gaps,div,cursor,output,consumed,remains,gc,within,count,mem⟩⟩ := spec
        have ⟨nh,taken,left⟩ := split_consumed src used rest i.val next.val hi div cursor
        have advance := diff_prefix_step _ _ _ _ _ _ _ (div ▸ state) before consumed remains gc within count mem
        step as ⟨j',hj'⟩
        refine ⟨⟨nh, by omega, ?_⟩,by omega⟩
        rw [taken,left,hj',List.take_succ_eq_append_getElem jl,←hr,output]
        exact advance
    · simp only [live,↓reduceIte]
      have je : j.val = dst.length := by dsimp [dst] at *; scalar_tac
      have all : dst.take j.val = dst := by simp [je]
      rw [all] at state
      step with len_spec self hc.1 as ⟨n,hn⟩
      by_cases extra : i < n
      · simp only [extra,↓reduceIte,spec_ok]
        have ie : i.val < src.length := by dsimp [src]; scalar_tac
        have hx : src[i.val] ∈ src.drop i.val := (drop_head_step src i.val ie).symm ▸ List.mem_cons_self ..
        have valid := hc.2.1 i.val ie
        have no := diff_prefix_leftover _ _ _ _ state _ hx valid
        exact noCover (by simpa only [List.take_append_drop] using no)
      · simp only [extra,↓reduceIte,spec_ok]
        have ie : i.val = src.length := by dsimp [src] at *; scalar_tac
        have a : src.take i.val = src := by simp [ie]
        rw [a] at state
        exact ⟨state.canonical,fun _ => state.mem, fun h => False.elim (h state.covered)⟩
  · have z : (0#usize).val = 0 := by decide
    simp only [inv,z,List.take_zero,List.drop_zero,Nat.zero_le,true_and]
    exact ⟨by simp [CoversClocks,inRangesList_iff_mem],by simp,by simp [canonical_pairwise],by simp,
      by simp,by simp [inRangesList_iff_mem]⟩
end YoctoCore.Properties.OrderRange
