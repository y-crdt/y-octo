import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.OrderRangeMove

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 1000000

namespace YoctoCore.Properties.OrderRange

def CanonicalList (l : List order_range.ClockRange) : Prop :=
  (∀ (i : Nat) (hi : i < l.length), (l[i]).start.val < (l[i]).«end».val) ∧
  (∀ (i j : Nat) (hi : i < j) (hj : j < l.length), (l[i]).«end».val < (l[j]).start.val)


def ringList (r : order_range.Ring) : List order_range.ClockRange :=
  OrderRangeRing.toList r.buf.val r.head.val r.len.val

/-- Public fragmented values have at least two ranges. During a splice the
    ring may temporarily contain one, before the outer representation folds it. -/
def ringWF (r : order_range.Ring) (extra : Nat := 1) : Prop :=
  r.head.val < r.buf.val.length ∧ r.len.val ≤ r.buf.val.length ∧
  extra + 1 ≤ r.len.val ∧ r.buf.val.length ≤ 2^30

def toList (r : order_range.OrderRange) : List order_range.ClockRange :=
  match r.repr with
  | .Single a => a.val.filter (fun x => decide (x.start.val < x.end.val))
  | .Many ring => ringList ring

def storageWF (r : order_range.OrderRange) : Prop :=
  match r.repr with
  | .Single a => ∀ x ∈ a.val, x.start.val < x.end.val ∨ x = order_range.EMPTY
  | .Many ring => ringWF ring

def Canonical (r : order_range.OrderRange) : Prop :=
  storageWF r ∧ CanonicalList (toList r)

def inRangesList (l : List order_range.ClockRange) (clock : Std.U64) : Prop :=
  ∃ (k : Nat) (hk : k < l.length),
    (l[k]).start.val ≤ clock.val ∧ clock.val < (l[k]).«end».val


def inRanges (r : order_range.OrderRange) (clock : Std.U64) : Prop :=
  inRangesList (toList r) clock

theorem canonicalList_start_lt {l : List order_range.ClockRange} (hCan : CanonicalList l)
    {i j : Nat} (hij : i < j) (hj : j < l.length) :
    (l[i]).start.val < (l[j]).start.val := by
  have hi : i < l.length := Nat.lt_trans hij hj
  exact Nat.lt_trans (hCan.1 i hi) (hCan.2 i j hij hj)

theorem canonicalList_end_lt {l : List order_range.ClockRange} (hCan : CanonicalList l)
    {i j : Nat} (hij : i < j) (hj : j < l.length) :
    (l[i]).«end».val < (l[j]).«end».val := by
  exact Nat.lt_trans (hCan.2 i j hij hj) (hCan.1 j hj)


theorem single_val (a : Array order_range.ClockRange 1#usize) :
    ∃ x, a.val = [x] := by
  have hlen : a.val.length = 1 := by simp
  cases h : a.val with
  | nil => simp [h] at hlen
  | cons x xs =>
    refine ⟨x, ?_⟩
    have hxs : xs.length = 0 := by simpa [h] using hlen
    simp [List.length_eq_zero_iff.mp hxs]

theorem ringList_length {extra : Nat} (r : order_range.Ring) (h : ringWF r extra) :
    (ringList r).length = r.len.val :=
  OrderRangeRing.toList_length r.buf.val (Nat.le_of_lt h.1) h.2.1

theorem inRangesList_iff_mem (l : List order_range.ClockRange) (c : Std.U64) :
    inRangesList l c ↔ ∃ r ∈ l, r.start.val ≤ c.val ∧ c.val < r.end.val := by
  constructor
  · rintro ⟨k, hk, hstart, hend⟩
    exact ⟨l[k], List.getElem_mem hk, hstart, hend⟩
  · rintro ⟨r, hr, hstart, hend⟩
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hr
    exact ⟨k, hk, by simpa [he] using hstart, by simpa [he] using hend⟩

theorem inRangesList_append (l r : List order_range.ClockRange) (c : Std.U64) :
    inRangesList (l ++ r) c ↔ inRangesList l c ∨ inRangesList r c := by
  simp only [inRangesList_iff_mem, List.mem_append]
  grind

theorem inRangesList_singleton (r : order_range.ClockRange) (c : Std.U64) :
    inRangesList [r] c ↔ r.start.val ≤ c.val ∧ c.val < r.end.val := by
  simp [inRangesList_iff_mem]

/-- Compaction may replace the last written range and a touching read
    range with their union. Its prefix has already been compacted. -/
theorem coalesce_mem_iff (pre : List order_range.ClockRange)
    (a b : order_range.ClockRange) (c : Std.U64)
    (ha : a.start.val ≤ b.start.val) (hb : b.start.val ≤ a.end.val) :
    inRangesList (pre ++ [{start := a.start, «end» := max a.end b.end}]) c ↔
      inRangesList (pre ++ [a,b]) c := by
  rw [inRangesList_append, inRangesList_append, inRangesList_singleton]
  simp only [inRangesList_iff_mem, List.mem_cons, List.not_mem_nil, or_false]
  by_cases h : a.end ≤ b.end
  · rw [max_eq_right h]
    have hend : a.end.val ≤ b.end.val := by scalar_tac
    grind
  · rw [max_eq_left (le_of_not_ge h)]
    have hend : b.end.val ≤ a.end.val := by scalar_tac
    grind

abbrev BeforeRange (a b : order_range.ClockRange) := a.end.val < b.start.val

theorem canonical_pairwise (l : List order_range.ClockRange) :
    CanonicalList l ↔ (∀ a ∈ l, a.start.val < a.end.val) ∧ l.Pairwise BeforeRange := by
  constructor
  · intro ⟨valid, separated⟩
    constructor
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      exact valid i hi
    · apply List.pairwise_iff_getElem.mpr
      intro i j _ hj ij
      exact separated i j ij hj
  · intro ⟨valid, pairs⟩
    exact ⟨fun i h => valid _ (List.getElem_mem h),
      fun i j ij hj => List.pairwise_iff_getElem.mp pairs i j (by omega) hj ij⟩

theorem canonical_append (l r : List order_range.ClockRange) :
    CanonicalList (l ++ r) ↔ CanonicalList l ∧ CanonicalList r ∧
      ∀ a ∈ l, ∀ b ∈ r, BeforeRange a b := by
  simp only [canonical_pairwise, List.mem_append, List.pairwise_append]
  grind

/-- Updating the end of the last range preserves canonicality as long as
    its start remains fixed and the new range is nonempty. -/
theorem canonical_last (pre : List order_range.ClockRange) (old new : order_range.ClockRange)
    (can : CanonicalList (pre ++ [old])) (start : new.start = old.start)
    (valid : new.start.val < new.end.val) : CanonicalList (pre ++ [new]) := by
  obtain ⟨pc, _, sep⟩ := (canonical_append _ _).mp can
  apply (canonical_append _ _).mpr
  refine ⟨pc, (canonical_pairwise _).mpr ⟨by simpa using valid, by simp⟩, ?_⟩
  intro a ha b hb
  obtain rfl := List.mem_singleton.mp hb
  simpa only [BeforeRange, start] using sep a ha old (by simp)

theorem canonical_push (pre : List order_range.ClockRange) (last next : order_range.ClockRange)
    (can : CanonicalList (pre ++ [last])) (sep : BeforeRange last next)
    (valid : next.start.val < next.end.val) : CanonicalList ((pre ++ [last]) ++ [next]) := by
  obtain ⟨_, lc, separated⟩ := (canonical_append _ _).mp can
  have lv := ((canonical_pairwise _).mp lc).1 last (by simp)
  apply (canonical_append _ _).mpr
  refine ⟨can, (canonical_pairwise _).mpr ⟨by simpa using valid, by simp⟩, ?_⟩
  intro a ha b hb
  obtain rfl := List.mem_singleton.mp hb
  rcases List.mem_append.mp ha with h | h
  · have := separated a h last (by simp)
    unfold BeforeRange at *
    omega
  · simpa only [List.mem_singleton.mp h] using sep

private theorem in_take (l : List order_range.ClockRange) (lo : Nat) (c : Std.U64) :
    inRangesList (l.take lo) c ↔ ∃ k, ∃ hk : k < l.length, k < lo ∧
      l[k].start.val ≤ c.val ∧ c.val < l[k].end.val := by
  unfold inRangesList
  constructor
  · rintro ⟨k, hk, h⟩
    have bound : k < min lo l.length := by simpa only [List.length_take] using hk
    exact ⟨k, by omega, by omega, by simpa only [List.getElem_take] using h⟩
  · rintro ⟨k, hk, before, h⟩
    exact ⟨k, by simp only [List.length_take]; omega, by simpa only [List.getElem_take] using h⟩

private theorem in_drop (l : List order_range.ClockRange) (hi : Nat) (c : Std.U64) :
    inRangesList (l.drop hi) c ↔ ∃ k, ∃ hk : k < l.length, hi ≤ k ∧
      l[k].start.val ≤ c.val ∧ c.val < l[k].end.val := by
  unfold inRangesList
  constructor
  · rintro ⟨k, hk, h⟩
    have bound : k < l.length-hi := by simpa only [List.length_drop] using hk
    exact ⟨hi+k, by omega, by omega, by simpa only [List.getElem_drop] using h⟩
  · rintro ⟨k, hk, after, h⟩
    refine ⟨k-hi, by simp only [List.length_drop]; omega, ?_⟩
    simpa only [List.getElem_drop, show hi+(k-hi) = k by omega] using h

private theorem splice_members (l : List order_range.ClockRange) (lo hi : Nat)
    (x merged : order_range.ClockRange) (_order : lo ≤ hi)
    (cover : ∀ c : Std.U64, (merged.start.val ≤ c.val ∧ c.val < merged.end.val) ↔
      (x.start.val ≤ c.val ∧ c.val < x.end.val) ∨ ∃ k, ∃ hk : k < l.length,
        lo ≤ k ∧ k < hi ∧ l[k].start.val ≤ c.val ∧ c.val < l[k].end.val) (c : Std.U64) :
    inRangesList (l.take lo ++ merged :: l.drop hi) c ↔
      inRangesList l c ∨ (x.start.val ≤ c.val ∧ c.val < x.end.val) := by
  change inRangesList (l.take lo ++ ([merged] ++ l.drop hi)) c ↔ _
  rw [inRangesList_append, inRangesList_append, inRangesList_singleton, in_take, in_drop, cover]
  unfold inRangesList
  grind

private theorem splice_canonical (l : List order_range.ClockRange) (lo hi : Nat)
    (x : order_range.ClockRange) (hc : CanonicalList l) (_order : lo ≤ hi)
    (valid : x.start.val < x.end.val)
    (prior : ∀ j, ∀ hj : j < l.length, j < lo → l[j].end.val < x.start.val)
    (later : ∀ j, ∀ hj : j < l.length, hi ≤ j → x.end.val < l[j].start.val) :
    CanonicalList (l.take lo ++ x :: l.drop hi) := by
  have ⟨good, pairs⟩ := (canonical_pairwise l).mp hc
  have left (a) (ha : a ∈ l.take lo) : BeforeRange a x := by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    simp only [List.length_take] at hj
    simpa only [BeforeRange, List.getElem_take] using prior j (by omega) (by omega)
  have right (a) (ha : a ∈ l.drop hi) : BeforeRange x a := by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    simp only [List.length_drop] at hj
    simpa only [BeforeRange, List.getElem_drop] using later (hi+j) (by omega) (by omega)
  apply (canonical_pairwise _).mpr
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact good _ ((List.take_sublist ..).subset h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact valid
      · exact good _ ((List.drop_sublist ..).subset h)
  · apply List.pairwise_append.mpr
    refine ⟨pairs.sublist (List.take_sublist ..), List.pairwise_cons.mpr ⟨right, pairs.sublist (List.drop_sublist ..)⟩, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | h
    · exact left a ha
    · have h1 := left a ha
      have h2 := right b h
      unfold BeforeRange at *
      omega

theorem merged_window (l : List order_range.ClockRange) (lo hi : Nat)
    (x m : order_range.ClockRange) (can : CanonicalList l) (valid : x.start.val < x.end.val)
    (overlap : lo < hi) (bound : hi ≤ l.length)
    (before : ∀ j, ∀ hj : j < l.length, j < lo → l[j].end.val < x.start.val)
    (firstEnd : x.start.val ≤ (l[lo]'(by omega)).end.val)
    (lastStart : (l[hi-1]'(by omega)).start.val ≤ x.end.val)
    (after : ∀ j, ∀ hj : j < l.length, hi ≤ j → x.end.val < l[j].start.val)
    (ms : m.start.val = min x.start.val (l[lo]'(by omega)).start.val)
    (me : m.end.val = max x.end.val (l[hi-1]'(by omega)).end.val) :
    CanonicalList (l.take lo ++ m :: l.drop hi) ∧ ∀ c,
      inRangesList (l.take lo ++ m :: l.drop hi) c ↔ inRangesList l c ∨
        (x.start.val ≤ c.val ∧ c.val < x.end.val) := by
  constructor
  · apply splice_canonical _ _ _ _ can (by omega) (by omega)
    · intro j hj hjl
      have := before j hj hjl
      have := can.2 j lo hjl (by omega)
      omega
    · intro j hj hjh
      have := after j hj hjh
      have := can.2 (hi-1) j (by omega) hj
      omega
  · apply splice_members _ _ _ _ _ (by omega)
    intro c
    constructor
    · rintro ⟨low, high⟩
      by_cases left : c.val < x.start.val
      · exact Or.inr ⟨lo, by omega, Nat.le_refl _, overlap, by omega, by omega⟩
      · by_cases right : x.end.val ≤ c.val
        · exact Or.inr ⟨hi-1, by omega, by omega, by omega, by omega, by omega⟩
        · exact Or.inl ⟨by omega, by omega⟩
    · rintro (h | ⟨j, hj, lower, upper, low, high⟩)
      · exact ⟨by omega, by omega⟩
      · have lstart : l[lo].start.val ≤ l[j].start.val := by
          rcases eq_or_lt_of_le lower with eq | lt
          · subst j; exact Nat.le_refl _
          · exact Nat.le_of_lt (canonicalList_start_lt can lt hj)
        have rend : l[j].end.val ≤ l[hi-1].end.val := by
          rcases eq_or_lt_of_le (show j ≤ hi-1 by omega) with eq | lt
          · subst j; exact Nat.le_refl _
          · exact Nat.le_of_lt (canonicalList_end_lt can lt (by omega))
        exact ⟨by omega, by omega⟩

private theorem disjoint_window (l : List order_range.ClockRange) (atIdx : Nat)
    (x : order_range.ClockRange) (can : CanonicalList l) (valid : x.start.val < x.end.val)
    (before : ∀ j, ∀ hj : j < l.length, j < atIdx → l[j].end.val < x.start.val)
    (after : ∀ j, ∀ hj : j < l.length, atIdx ≤ j → x.end.val < l[j].start.val) :
    CanonicalList (l.take atIdx ++ x :: l.drop atIdx) ∧ ∀ c,
      inRangesList (l.take atIdx ++ x :: l.drop atIdx) c ↔ inRangesList l c ∨
        (x.start.val ≤ c.val ∧ c.val < x.end.val) := by
  refine ⟨splice_canonical _ _ _ _ can (Nat.le_refl _) valid before after, ?_⟩
  apply splice_members _ _ _ _ _ (Nat.le_refl _)
  intro c
  grind

theorem physical_spec (cap head i : Std.Usize)
    (hh : head.val < cap.val) (hi : i.val < cap.val) :
    order_range.physical cap head i ⦃ p =>
      p.val = OrderRangeRing.position cap.val head.val i.val ∧ p.val < cap.val ⦄ := by
  unfold order_range.physical
  step as ⟨tail, ht⟩
  split_ifs with h
  · have hlt : i.val < cap.val - head.val := by scalar_tac
    simp only [OrderRangeRing.position, ite_eq_left hlt]
    step*
  · have hle : ¬ i.val < cap.val - head.val := by scalar_tac
    simp only [OrderRangeRing.position, ite_eq_right hle]
    step*

/-- Internal moves can read any initialized slot, including temporary space
    outside the current logical length. -/
theorem ring_at_physical_spec (r : order_range.Ring) (i : Std.Usize)
    (hh : r.head.val < r.buf.length) (hi : i.val < r.buf.length) :
    order_range.Ring.at r i ⦃ x =>
      x = r.buf.val[OrderRangeRing.position r.buf.length r.head.val i.val]'(OrderRangeRing.position_lt hh hi) ⦄ := by
  unfold order_range.Ring.at
  simp only [lift]
  step with physical_spec as ⟨p, hp, hpl⟩; try scalar_tac
  step as ⟨v, hv⟩
  have hpos : p.val = OrderRangeRing.position r.buf.length r.head.val i.val := by simpa using hp
  simpa only [← hpos] using hv

theorem ring_at_spec {extra : Nat} (r : order_range.Ring) (i : Std.Usize) (hw : ringWF r extra)
    (hi : i.val < r.len.val) :
    order_range.Ring.at r i ⦃ x => some x = (ringList r)[i.val]? ⦄ := by
  rcases hw with ⟨hh, hl, _, _⟩
  unfold order_range.Ring.at
  simp only [lift]
  step with physical_spec as ⟨p, hp, hpLt⟩; try scalar_tac
  step as ⟨v, hv⟩
  have hi' : i.val < (ringList r).length := by
    simpa only [ringList, OrderRangeRing.toList_length r.buf.val (Nat.le_of_lt hh) hl] using hi
  rw [List.getElem?_eq_getElem hi']
  congr 1
  have hpos : p.val = OrderRangeRing.position r.buf.val.length r.head.val i.val := by
    simpa using hp
  apply hv.trans
  simpa only [ringList, ← hpos] using (OrderRangeRing.toList_get r.buf.val hh hl hi).symm

theorem ring_at_list_spec {extra : Nat} (r : order_range.Ring) (hr : ringWF r extra)
    (i : Std.Usize) (hi : i.val < r.len.val) :
    order_range.Ring.at r i ⦃ x =>
      x = (ringList r)[i.val]'(by rwa [ringList_length r hr]) ⦄ := by
  step with ring_at_spec r i hr hi as ⟨x, hx⟩
  simpa [List.getElem?_eq_getElem (by rwa [ringList_length r hr] : i.val < (ringList r).length)] using hx

theorem ring_set_physical_spec (r : order_range.Ring) (i : Std.Usize) (x : order_range.ClockRange)
    (hh : r.head.val < r.buf.length) (hi : i.val < r.buf.length) :
    order_range.Ring.set r i x ⦃ r' =>
      r'.head = r.head ∧ r'.len = r.len ∧
      r'.buf.val = r.buf.val.set (OrderRangeRing.position r.buf.length r.head.val i.val) x ⦄ := by
  unfold order_range.Ring.set
  simp only [lift]
  step with physical_spec as ⟨p, hp, hbound⟩; try scalar_tac
  step as ⟨_, write, _, hWrite⟩
  rw [hWrite]
  simp [alloc.vec.Vec.set, hp]

/-- Writing an active slot updates precisely its logical index across wraparound. -/
theorem ring_set_list_spec {extra : Nat} (ring : order_range.Ring) (i : Std.Usize)
    (x : order_range.ClockRange) (hw : ringWF ring extra) (hi : i.val < ring.len.val) :
    order_range.Ring.set ring i x ⦃ out =>
      ringWF out extra ∧ ringList out = (ringList ring).set i.val x ⦄ := by
  rcases hw with ⟨hh, hl, hm, hc⟩
  have hiCap : i.val < ring.buf.val.length := by omega
  refine spec_mono (ring_set_physical_spec ring i x hh hiCap) ?_
  intro out ⟨hHead, hLen, hBuf⟩
  have hsize : out.buf.val.length = ring.buf.val.length := by simp [hBuf]
  constructor
  · simpa only [ringWF, hHead, hLen, hsize] using And.intro hh (And.intro hl (And.intro hm hc))
  · unfold ringList
    rw [hHead, hLen, hBuf]
    exact OrderRangeRing.set_active ring.buf.val hh hl hi x

theorem ring_set_spare_spec (r : order_range.Ring) (i : Std.Usize) (x : order_range.ClockRange)
    (hh : r.head.val < r.buf.length) (hl : r.len.val ≤ i.val) (hi : i.val < r.buf.length) :
    order_range.Ring.set r i x ⦃ out =>
      out.head = r.head ∧ out.len = r.len ∧ out.buf.length = r.buf.length ∧ ringList out = ringList r ⦄ := by
  refine spec_mono (ring_set_physical_spec r i x hh hi) ?_
  intro out ⟨hHead, hLen, hBuf⟩
  refine ⟨hHead, hLen, by simp [alloc.vec.Vec.length, hBuf], ?_⟩
  unfold ringList
  rw [hHead, hLen, hBuf]
  exact OrderRangeRing.set_inactive r.buf.val hh hl hi x

/-- The entire initialized buffer viewed from the head, including the slots
    a move may use temporarily outside the active interval. -/
private def slotsOf (r : order_range.Ring) :=
  OrderRangeRing.toList r.buf.val r.head.val r.buf.length

private theorem slots_length (r : order_range.Ring) (hh : r.head.val < r.buf.length) :
    (slotsOf r).length = r.buf.length :=
  OrderRangeRing.toList_length _ (Nat.le_of_lt hh) (Nat.le_refl _)

private theorem read_slot (r : order_range.Ring) (i : Std.Usize)
    (hh : r.head.val < r.buf.length) (hi : i.val < r.buf.length) :
    order_range.Ring.at r i ⦃ x => some x = (slotsOf r)[i.val]? ⦄ := by
  refine spec_mono (ring_at_physical_spec r i hh hi) ?_
  intro x hx
  have live : i.val < (slotsOf r).length := by rwa [slots_length r hh]
  rw [List.getElem?_eq_getElem live]
  congr 1
  exact hx.trans (OrderRangeRing.toList_get r.buf.val hh (Nat.le_refl _) hi).symm

private theorem write_slot (r : order_range.Ring) (i : Std.Usize) (x : order_range.ClockRange)
    (hh : r.head.val < r.buf.length) (hi : i.val < r.buf.length) :
    order_range.Ring.set r i x ⦃ out => out.head = r.head ∧ out.len = r.len ∧
      out.buf.length = r.buf.length ∧ slotsOf out = (slotsOf r).set i.val x ⦄ := by
  refine spec_mono (ring_set_physical_spec r i x hh hi) ?_
  intro out ⟨head, len, buf⟩
  have size : out.buf.length = r.buf.length := by simp [alloc.vec.Vec.length, buf]
  refine ⟨head, len, size, ?_⟩
  unfold slotsOf
  rw [size, head, buf]
  exact OrderRangeRing.set_active r.buf.val hh (Nat.le_refl _) hi x

open OrderRangeRing

private abbrev RangeBuf := alloc.vec.Vec order_range.ClockRange

/-- Contents of a partly moved buffer, expressed in logical indices so that
    splitting either physical slice at the end of the array is transparent. -/
private def MovingSlots (initial current : RangeBuf) (cap head src dst count remaining : Nat) :=
  current.length = cap ∧ remaining ≤ count ∧ ∀ j < cap,
    current.val[position cap head j]? =
      initial.val[position cap head (chunkSource src dst count remaining j)]?

private theorem umin_val (a b : Std.Usize) :
    (core.cmp.impls.OrdUsize.min a b).val = min a.val b.val := by
  unfold core.cmp.impls.OrdUsize.min
  split <;> scalar_tac

private theorem move_slots_loop_spec (buf : RangeBuf) (src dst count cap head : Usize)
    (size : cap.val = buf.length) (hh : head.val < cap.val)
    (si : src.val+count.val ≤ cap.val) (di : dst.val+count.val ≤ cap.val) :
    order_range.Ring.move_slots_loop buf src dst count cap head count ⦃ out =>
      MovingSlots buf out cap.val head.val src.val dst.val count.val 0 ⦄ := by
  let inv : RangeBuf × Usize → Prop := fun (v,left) => MovingSlots buf v cap.val head.val src.val dst.val count.val left.val
  unfold order_range.Ring.move_slots_loop
  refine loop.spec_decr_nat (fun (_,left) => left.val) inv _ _ (buf,count) ?_ ?_
  · intro ⟨v,left⟩ ⟨lv,remaining,contents⟩
    unfold order_range.Ring.move_slots_loop.body
    simp only
    by_cases live : left ≠ 0#usize
    · have guard : (left != 0#usize) = true := by simp [live]
      simp only [guard,↓reduceIte]
      have pos : 0 < left.val := by scalar_tac
      let offset := fun (n : Nat) => if dst.val < src.val then count.val-left.val else left.val-n
      let Pieces := fun (f t n : Usize) =>
        0 < n.val ∧ n.val ≤ left.val ∧
        f.val = position cap.val head.val (src.val+offset n.val) ∧
        t.val = position cap.val head.val (dst.val+offset n.val) ∧
        f.val+n.val ≤ cap.val ∧ t.val+n.val ≤ cap.val
      have advance (f t n : Usize) (pieces : Pieces f t n) :
          (do let slice ← order_range.move_segment v.slice f t n
              let left' ← left - n
              ok (cont ((⟨slice⟩ : RangeBuf),left') : ControlFlow (RangeBuf × Usize) RangeBuf)) ⦃ z =>
            match z with
            | done out => MovingSlots buf out cap.val head.val src.val dst.val count.val 0
            | cont pair => inv pair ∧ pair.2.val < left.val ⦄ := by
        obtain ⟨pn,bn,hf,ht,fc,tc⟩ := pieces
        step with move_segment_spec v.slice f t n (fc.trans_eq lv.symm) (tc.trans_eq lv.symm) as ⟨s,ls,copy⟩
        step as ⟨next,hn⟩
        refine ⟨⟨by simpa [alloc.vec.Vec.length,alloc.vec.Vec.val] using ls.trans lv,by omega,?_⟩,by omega⟩
        intro j hj
        have bounds : offset n.val + n.val ≤ count.val := by dsimp [offset]; split <;> omega
        let k := movedIndex (src.val+offset n.val) (dst.val+offset n.val) n.val j
        have lk : k < cap.val := movedIndex_bound (by omega) hj
        have align := position_moved (head := head.val) hh
          (show src.val+offset n.val+n.val ≤ cap.val by omega)
          (show dst.val+offset n.val+n.val ≤ cap.val by omega) hj
          (hf ▸ fc) (ht ▸ tc)
        change s.val[_]? = _
        rw [copy,hf,ht,align,hn]
        have read := contents k lk
        simp only [alloc.vec.Vec.val] at read
        rw [read]
        simp only [alloc.vec.Vec.val,k,offset,chunkSource_step _ _ _ _ _ _ remaining bn]
      have choose : (
        if dst < src
        then
          do
          let done1 ← count - left
          let i ← src + done1
          let from1 ← order_range.physical cap head i
          let i1 ← dst + done1
          let to1 ← order_range.physical cap head i1
          let i2 ← cap - from1
          let i3 ← lift (core.cmp.impls.OrdUsize.min left i2)
          let i4 ← cap - to1
          let i5 ← lift (core.cmp.impls.OrdUsize.min i3 i4)
          ok (from1, to1, i5)
        else
          do
          let i ← left - 1#usize
          let i1 ← src + i
          let i2 ← order_range.physical cap head i1
          let «end» ← i2 + 1#usize
          let i3 ← dst + i
          let i4 ← order_range.physical cap head i3
          let dest_end ← i4 + 1#usize
          let i5 ← lift (core.cmp.impls.OrdUsize.min left «end»)
          let n1 ← lift (core.cmp.impls.OrdUsize.min i5 dest_end)
          let i6 ← «end» - n1
          let i7 ← dest_end - n1
          ok (i6, i7, n1)) ⦃ p => Pieces p.1 p.2.1 p.2.2 ⦄ := by
        by_cases forward : dst < src
        · simp only [forward,↓reduceIte,lift,bind_ok]
          step as ⟨progressed,hd⟩
          step as ⟨i,hi⟩
          step with physical_spec cap head i hh (by scalar_tac) as ⟨f,hf,fc⟩
          step as ⟨j,hj⟩
          step with physical_spec cap head j hh (by scalar_tac) as ⟨t,ht,tc⟩
          step as ⟨a,ha⟩
          step as ⟨b,hb⟩
          have lt : dst.val < src.val := by scalar_tac
          refine ⟨?_,?_,?_,?_,?_,?_⟩
          · simp only [umin_val]; omega
          · simp only [umin_val]; omega
          · simpa only [offset,ite_eq_left lt,hi,hd] using hf
          · simpa only [offset,ite_eq_left lt,hj,hd] using ht
          · simp only [umin_val]; omega
          · simp only [umin_val]; omega
        · simp only [forward,↓reduceIte,lift,bind_ok]
          step as ⟨prev,hp⟩
          step as ⟨i,hi⟩
          step with physical_spec cap head i hh (by scalar_tac) as ⟨f,hf,fc⟩
          step as ⟨endF,ef⟩
          step as ⟨j,hj⟩
          step with physical_spec cap head j hh (by scalar_tac) as ⟨t,ht,tc⟩
          step as ⟨endT,et⟩
          let n := core.cmp.impls.OrdUsize.min (core.cmp.impls.OrdUsize.min left endF) endT
          have bound : n.val = min (min left.val endF.val) endT.val := by
            simp only [n,umin_val]
          step as ⟨first,hfirst⟩
          step as ⟨second,hsecond⟩
          have fn : 0 < n.val := by omega
          have sn := position_before_end (start := src.val) (remaining := left.val) hh (by omega) fn (show n.val ≤ left.val by omega)
          have tn := position_before_end (start := dst.val) (remaining := left.val) hh (by omega) fn (show n.val ≤ left.val by omega)
          have nf : ¬dst.val < src.val := by scalar_tac
          change first.val = endF.val-n.val at hfirst
          change second.val = endT.val-n.val at hsecond
          change Pieces first second n
          have ff : position cap.val head.val (src.val+(left.val-1)) = f.val := by
            simpa only [hi,hp] using hf.symm
          have tt : position cap.val head.val (dst.val+(left.val-1)) = t.val := by
            simpa only [hj,hp] using ht.symm
          refine ⟨fn,by omega,?_,?_,by omega,by omega⟩
          · simp only [offset,ite_eq_right nf,sn (by rw [ff]; omega),ff]; omega
          · simp only [offset,ite_eq_right nf,tn (by rw [tt]; omega),tt]; omega
      apply spec_bind choose
      rintro ⟨f,t,n⟩ parts
      simp only [lift,bind_ok,alloc.vec.Vec.deref_mut]
      refine spec_mono (advance f t n parts) ?_
      intro z hz
      cases z <;> exact hz
    · have z : left.val = 0 := by scalar_tac
      have guard : (left != 0#usize) = false := by simp [Classical.not_not.mp live]
      simp only [guard,Bool.false_eq_true,↓reduceIte,spec_ok]
      exact ⟨lv,Nat.zero_le _,by simpa only [z] using contents⟩
  · refine ⟨size.symm,Nat.le_refl _,fun j _ => ?_⟩
    rw [chunkSource_initial]


private theorem slots_lookup (r : order_range.Ring) (hh : r.head.val < r.buf.length)
    {j : Nat} (live : j < r.buf.length) :
    (slotsOf r)[j]? = r.buf.val[position r.buf.length r.head.val j]? := by
  rw [List.getElem?_eq_getElem (by rw [slots_length r hh]; exact live),
      List.getElem?_eq_getElem (position_lt hh live)]
  exact congrArg some (OrderRangeRing.toList_get _ hh (Nat.le_refl _) live)

theorem move_slots_spec (r : order_range.Ring) (src dst count : Usize)
    (hh : r.head.val < r.buf.length) (si : src.val+count.val ≤ r.buf.length)
    (di : dst.val+count.val ≤ r.buf.length) :
    order_range.Ring.move_slots r src dst count ⦃ out =>
      out.head = r.head ∧ out.len = r.len ∧ out.buf.length = r.buf.length ∧
      ∀ j, (slotsOf out)[j]? = (slotsOf r)[movedIndex src.val dst.val count.val j]? ⦄ := by
  unfold order_range.Ring.move_slots
  by_cases empty : count = 0#usize
  · simp only [empty,↓reduceIte,spec_ok,true_and]
    intro j
    rw [show (0#usize).val = 0 by decide, moved_empty]
  · by_cases same : src = dst
    · simp only [empty,same,↓reduceIte,spec_ok,true_and]
      intro j
      have noChange : movedIndex dst.val dst.val count.val j = j := by
        unfold movedIndex; split <;> omega
      rw [noChange]
    · simp only [empty,same,↓reduceIte,lift,bind_ok]
      let cap := alloc.vec.Vec.len r.buf
      let head := UScalar.cast .Usize r.head
      have he : head.val = r.head.val := by scalar_tac
      have ce : cap.val = r.buf.length := by scalar_tac
      step with move_slots_loop_spec r.buf src dst count cap head ce (by omega) (by omega) (by omega) as ⟨v,moved⟩
      obtain ⟨lv,_,lookup⟩ := moved
      let out := {r with buf := v}
      have sz : out.buf.length = r.buf.length := lv.trans ce
      have ho : out.head.val < out.buf.length := by change r.head.val < v.length; rw [lv,ce]; exact hh
      refine ⟨sz,?_⟩
      intro j
      by_cases live : j < r.buf.length
      · have inside := movedIndex_bound (dst := dst.val) si live
        rw [slots_lookup out ho (by omega),slots_lookup r hh inside]
        have valid : j < cap.val := ce.symm ▸ live
        have h : v.val[position cap.val head.val j]? =
            r.buf.val[position cap.val head.val (chunkSource src.val dst.val count.val 0 j)]? := lookup j valid
        rw [chunkSource_final,he,ce] at h
        change v.val[position v.length r.head.val j]? = _
        rw [show v.length = r.buf.length from sz]
        exact h
      · have outside : movedIndex src.val dst.val count.val j = j := by
          unfold movedIndex; split <;> omega
        rw [outside,List.getElem?_eq_none (by rw [slots_length out ho,sz]; omega),
          List.getElem?_eq_none (by rw [slots_length r hh]; omega)]

private theorem ring_two_pieces {α : Type} (l : List α) (head n : Nat) (hs : head ≤ l.length)
    (hn : n ≤ l.length) :
    let k := min n (l.length - head)
    (l.drop head).take k ++ l.take (n-k) = OrderRangeRing.toList l head n := by
  dsimp only
  unfold OrderRangeRing.toList
  rw [List.take_append]
  simp only [List.length_drop, List.take_take]
  by_cases contiguous : n ≤ l.length-head
  · have tail : n - (l.length-head) = 0 := by omega
    simp [Nat.min_eq_left contiguous, tail]
  · have tail : l.length-head ≤ n := by omega
    have fits : n-(l.length-head) ≤ head := by omega
    simp [Nat.min_eq_right tail, Nat.min_eq_left fits, List.take_of_length_le]
    omega

private theorem ring_slices_nonempty_spec {extra : Nat} (r : order_range.Ring) (hw : ringWF r extra) :
    order_range.Ring.slices r ⦃ (a,b) => a.val ++ b.val = ringList r ∧ 0 < a.length ⦄ := by
  have ⟨hh,hl,positive,hc⟩ := hw
  unfold order_range.Ring.slices
  simp only [lift, bind_ok]
  step as ⟨tail,ht⟩
  let first := core.cmp.impls.OrdUsize.min (UScalar.cast .Usize r.len) tail
  have fl : first.val = min r.len.val (r.buf.val.length-r.head.val) := by
    dsimp [first,core.cmp.impls.OrdUsize.min]; split <;> scalar_tac
  step as ⟨endIdx,he⟩
  step as ⟨a,ha,_⟩
  step as ⟨wrap,hw'⟩
  step as ⟨b,hb,_⟩
  have headEq : (UScalar.cast .Usize r.head).val = r.head.val := by scalar_tac
  have endEq : endIdx.val = r.head.val + first.val := by scalar_tac
  have wrapEq : wrap.val = r.len.val - first.val := by scalar_tac
  constructor
  · simpa [ha,hb,List.slice,headEq,endEq,wrapEq,fl,ringList] using
      (ring_two_pieces r.buf.val r.head.val r.len.val (by omega) hl)
  · change 0 < a.val.length
    rw [ha,List.slice_length,headEq,endEq]
    omega

theorem ring_slices_spec {extra : Nat} (r : order_range.Ring) (hw : ringWF r extra) :
    order_range.Ring.slices r ⦃ (a,b) => a.val ++ b.val = ringList r ⦄ := by
  apply spec_mono (ring_slices_nonempty_spec r hw)
  rintro ⟨a,b⟩ ⟨view,_⟩
  exact view

/-- Partition at the first interval whose end reaches the requested clock. -/
private def EndCut (l : List order_range.ClockRange) (clock : U64) (n : Nat) :=
  n ≤ l.length ∧ (∀ i (h : i < l.length), i < n → l[i].end.val < clock.val) ∧
    ∀ i (h : i < l.length), n ≤ i → clock.val ≤ l[i].end.val

private theorem cut_first_piece (first second : List order_range.ClockRange) (clock : U64)
    (n : Nat) (can : CanonicalList (first ++ second)) (part : EndCut first clock n)
    (last : Nat) (finalIndex : last+1 = first.length)
    (reached : clock.val ≤ (first[last]'(by omega)).end.val) :
    EndCut (first ++ second) clock n := by
  obtain ⟨bound,before,after⟩ := part
  refine ⟨by simp; omega,?_,?_⟩
  · intro k hk lt
    simpa only [List.getElem_append_left (show k < first.length by omega)] using before k (by omega) lt
  · intro k hk ge
    by_cases inFirst : k < first.length
    · simpa only [List.getElem_append_left inFirst] using after k inFirst ge
    · have ordered := canonicalList_end_lt can (by omega : last < k) hk
      rw [List.getElem_append_left (show last < first.length by omega)] at ordered
      omega

private theorem cut_second_piece (first second : List order_range.ClockRange) (clock : U64)
    (n : Nat) (can : CanonicalList first) (part : EndCut second clock n)
    (last : Nat) (finalIndex : last+1 = first.length)
    (before : (first[last]'(by omega)).end.val < clock.val) :
    EndCut (first ++ second) clock (first.length+n) := by
  obtain ⟨bound,lower,upper⟩ := part
  refine ⟨by simp; omega,?_,?_⟩
  · intro k hk lt
    by_cases inFirst : k < first.length
    · rw [List.getElem_append_left inFirst]
      by_cases isLast : k = last
      · subst k; exact before
      · exact Nat.lt_trans (canonicalList_end_lt can (by omega) (by omega)) before
    · rw [List.getElem_append_right (by omega)]
      exact lower _ (by simp only [List.length_append] at hk; omega) (by omega)
  · intro k hk ge
    rw [List.getElem_append_right (by omega)]
    exact upper _ (by simp only [List.length_append] at hk; omega) (by omega)

private theorem lower_slice_spec (ranges : Slice order_range.ClockRange) (start : Std.U64)
    (hCan : CanonicalList ranges.val) :
    order_range.Ring.lower_loop start ranges 0#usize (Slice.len ranges) ⦃ first =>
      EndCut ranges.val start first.val ⦄ := by
  unfold order_range.Ring.lower_loop
  let inv : Std.Usize × Std.Usize → Prop := fun (lo, hi) =>
    lo.val ≤ hi.val ∧ hi.val ≤ ranges.val.length ∧
    (∀ (k : Nat) (hk : k < ranges.val.length), k < lo.val → (ranges.val[k]).«end».val < start.val) ∧
    (∀ (k : Nat) (hk : k < ranges.val.length), hi.val ≤ k → start.val ≤ (ranges.val[k]).«end».val)
  refine loop.spec_decr_nat
    (fun (lo, hi) => hi.val - lo.val) inv _ _ (0#usize, Slice.len ranges) ?_
    ⟨by scalar_tac, by scalar_tac, by intro k hk h; scalar_tac, by intro k hk h; scalar_tac⟩
  intro ⟨lo, hi⟩ ⟨hLoHi, hHiLen, hL, hR⟩
  unfold order_range.Ring.lower_loop.body
  simp only
  split_ifs with hlt
  · step as ⟨d, hd⟩
    step as ⟨half, hhalf⟩
    step as ⟨mid, hmid⟩
    have hm : mid.val < ranges.val.length := by scalar_tac
    step as ⟨v, hv⟩
    split_ifs <;> try step
    all_goals try simp only [spec_ok]
    all_goals rw [hv] at *
    · refine ⟨⟨by scalar_tac, hHiLen, ?_, hR⟩, by scalar_tac⟩
      intro k hk hkm
      have hk_le : k ≤ mid.val := by scalar_tac
      rcases eq_or_lt_of_le hk_le with rfl | hlt2
      · scalar_tac
      · exact Nat.lt_trans (canonicalList_end_lt hCan hlt2 (by scalar_tac)) (by scalar_tac)
    · refine ⟨⟨by scalar_tac, by scalar_tac, hL, ?_⟩, by scalar_tac⟩
      intro k hk hmk
      rcases eq_or_lt_of_le hmk with rfl | hgt
      · scalar_tac
      · exact Nat.le_trans (by scalar_tac) (Nat.le_of_lt (canonicalList_end_lt hCan hgt hk))
  · simp only [spec_ok]
    have hEq : lo.val = hi.val := by scalar_tac
    refine ⟨by scalar_tac, hL, fun k hk h => hR k hk (by omega)⟩

theorem lower_partition_spec {extra : Nat} (r : order_range.Ring) (hr : ringWF r extra) (start : Std.U64)
    (hCan : CanonicalList (ringList r)) :
    order_range.Ring.lower r start ⦃ first =>
      first.val ≤ (ringList r).length ∧
      (∀ (k : Nat) (hk : k < (ringList r).length), k < first.val → ((ringList r)[k]).«end».val < start.val) ∧
      (∀ (k : Nat) (hk : k < (ringList r).length), first.val ≤ k → start.val ≤ ((ringList r)[k]).«end».val) ⦄ := by
  unfold order_range.Ring.lower
  step with ring_slices_nonempty_spec r hr as ⟨first,second,view,positive⟩
  have can : CanonicalList (first.val ++ second.val) := by rw [view]; exact hCan
  obtain ⟨left,right,_⟩ := (canonical_append _ _).mp can
  have total := congrArg List.length view
  rw [List.length_append,ringList_length r hr] at total
  have nonempty : first.length ≠ 0 := Nat.ne_of_gt positive
  have guard : decide (first.length = 0) = false := by simp [nonempty]
  simp only [core.slice.Slice.is_empty,guard,bind_ok,Bool.false_eq_true,↓reduceIte]
  let Good : Slice order_range.ClockRange × Usize → Prop := fun (s,off) =>
    CanonicalList s.val ∧ ∀ i, EndCut s.val start i → EndCut (first.val ++ second.val) start (off.val+i)
  have choose : (do
      let j ← first.len - 1#usize
      let x ← Slice.index_usize first j
      if x.end < start then ok (second,first.len) else ok (first,0#usize)) ⦃ Good ⦄ := by
    step as ⟨j,hj⟩
    step as ⟨x,hx⟩
    have last : j.val + 1 = first.val.length := by scalar_tac
    by_cases passed : x.end < start
    · simp only [passed,↓reduceIte,spec_ok]
      refine ⟨right,fun i part => ?_⟩
      have before : (first.val[j.val]).end.val < start.val := by rw [←hx]; scalar_tac
      have off : first.len.val = first.val.length := by scalar_tac
      rw [off]
      exact cut_second_piece _ _ _ i left part j.val last before
    · simp only [passed,↓reduceIte,spec_ok]
      refine ⟨left,fun i part => ?_⟩
      have reached : start.val ≤ (first.val[j.val]).end.val := by rw [←hx]; scalar_tac
      simpa using cut_first_piece _ _ _ i can part j.val last reached
  apply spec_bind choose
  rintro ⟨s,off⟩ ⟨ordered,partition⟩
  step with lower_slice_spec s start ordered as ⟨i,cut⟩
  have combined := partition i.val cut
  rw [view] at combined
  have fits := combined.1
  have room := ringList_length r hr
  step as ⟨n,hn⟩
  simpa only [hn,EndCut] using combined

theorem upper_partition_spec {extra : Nat} (r : order_range.Ring) (hr : ringWF r extra) («end» : Std.U64)
    (first : Std.Usize) (hFirst : first.val ≤ (ringList r).length) (hCan : CanonicalList (ringList r)) :
    order_range.Ring.upper_loop r.buf r.head r.len «end» first (UScalar.cast .Usize r.len) ⦃ last =>
      first.val ≤ last.val ∧ last.val ≤ (ringList r).length ∧
      (∀ (k : Nat) (hk : k < (ringList r).length), first.val ≤ k → k < last.val →
        ((ringList r)[k]).start.val ≤ «end».val) ∧
      (∀ (k : Nat) (hk : k < (ringList r).length), last.val ≤ k →
        «end».val < ((ringList r)[k]).start.val) ⦄ := by
  have hlength := ringList_length r hr
  unfold order_range.Ring.upper_loop
  let inv : Std.Usize × Std.Usize → Prop := fun (lo, hi) =>
    first.val ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ (ringList r).length ∧
    (∀ (k : Nat) (hk : k < (ringList r).length), first.val ≤ k → k < lo.val →
      ((ringList r)[k]).start.val ≤ «end».val) ∧
    (∀ (k : Nat) (hk : k < (ringList r).length), hi.val ≤ k →
      «end».val < ((ringList r)[k]).start.val)
  refine loop.spec_decr_nat
    (fun (lo, hi) => hi.val - lo.val) inv _ _ (first, UScalar.cast .Usize r.len) ?_
    ⟨le_refl _, by scalar_tac, by scalar_tac, by intro k hk _ h; omega, by intro k hk h; scalar_tac⟩
  intro ⟨lo, hi⟩ ⟨hFL, hLoHi, hHiLen, hL, hR⟩
  unfold order_range.Ring.upper_loop.body
  simp only
  split_ifs with hlt
  · step as ⟨d, hd⟩
    step as ⟨half, hhalf⟩
    step as ⟨mid, hmid⟩
    have hm : mid.val < r.len.val := by scalar_tac
    step with ring_at_list_spec r hr mid hm as ⟨v, hv⟩
    split_ifs <;> try step
    all_goals try simp only [spec_ok]
    all_goals rw [hv] at *
    · refine ⟨⟨by scalar_tac, by scalar_tac, hHiLen, ?_, hR⟩, by scalar_tac⟩
      intro k hk hfk hkm
      have hk_le : k ≤ mid.val := by scalar_tac
      rcases eq_or_lt_of_le hk_le with rfl | hlt2
      · scalar_tac
      · exact Nat.le_trans (Nat.le_of_lt (canonicalList_start_lt hCan hlt2 (by scalar_tac))) (by scalar_tac)
    · refine ⟨⟨hFL, by scalar_tac, by scalar_tac, hL, ?_⟩, by scalar_tac⟩
      intro k hk hmk
      rcases eq_or_lt_of_le hmk with rfl | hgt
      · scalar_tac
      · exact Nat.lt_trans (by scalar_tac) (canonicalList_start_lt hCan hgt hk)
  · simp only [spec_ok]
    have hEq : lo.val = hi.val := by scalar_tac
    refine ⟨hFL, by scalar_tac, hL, fun k hk h => hR k hk (by omega)⟩

/-- Checking adjacent boundaries suffices to establish canonicality for every
    pair, including for a borrowed slice backed by a larger allocation. -/
theorem is_canonical_spec (buf : Slice order_range.ClockRange) :
    order_range.is_canonical buf ⦃ result => result = true ↔ CanonicalList buf.val ⦄ := by
  unfold order_range.is_canonical order_range.is_canonical_loop
  let inv := fun (i : Std.Usize) => i.val ≤ buf.length ∧
    (∀ k (hk : k < buf.val.length), k < i.val → buf.val[k].start.val < buf.val[k].end.val) ∧
    (∀ k j (hkj : k < j) (hj : j < buf.val.length), j < i.val →
      buf.val[k].end.val < buf.val[j].start.val)
  refine loop.spec_decr_nat (fun i => buf.length - i.val) inv _ _ 0#usize ?_ ?_
  · intro i ⟨hi, nonempty, disjoint⟩
    unfold order_range.is_canonical_loop.body
    simp only
    by_cases h : i < Slice.len buf
    · simp only [h, ↓reduceIte]
      have bound : i.val < buf.val.length := by scalar_tac
      step as ⟨r, hr⟩
      by_cases he : r.start ≥ r.end
      · simp only [he, ↓reduceIte, spec_ok, Bool.false_eq_true, false_iff]
        intro hc
        have hv := hc.1 i.val bound
        rw [← hr] at hv
        scalar_tac
      · have hv : buf.val[i.val].start.val < buf.val[i.val].end.val := by rw [← hr]; scalar_tac
        have extend (hprev : ∀ (k : Nat) (hk : k < i.val),
            (buf.val[k]'(by omega)).end.val < buf.val[i.val].start.val) (n : Std.Usize) (hn : n.val = i.val + 1) :
            inv n ∧ buf.length - n.val < buf.length - i.val := by
          refine ⟨⟨by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
          · intro k hk hkn
            by_cases hki : k = i.val
            · subst k; exact hv
            · exact nonempty k hk (by omega)
          · intro k j hkj hj hjn
            by_cases hji : j = i.val
            · subst j; exact hprev k hkj
            · exact disjoint k j hkj hj (by omega)
        simp only [he, ↓reduceIte]
        split_ifs with hn
        · step as ⟨p, hp⟩
          step as ⟨prev, hprev⟩
          have hpLt : p.val < i.val := by scalar_tac
          by_cases overlap : prev.end ≥ r.start
          · simp only [overlap, ↓reduceIte, spec_ok, Bool.false_eq_true, false_iff]
            intro hc
            have hs := hc.2 p.val i.val hpLt bound
            rw [← hprev, ← hr] at hs
            scalar_tac
          · simp only [overlap, ↓reduceIte]
            step as ⟨n, hs⟩
            apply extend _ n hs
            intro k hki
            have hpB : p.val < buf.val.length := by omega
            have sep : buf.val[p.val].end.val < buf.val[i.val].start.val := by rw [← hprev, ← hr]; scalar_tac
            by_cases eq : k = p.val
            · subst k; exact sep
            · have hs1 := disjoint k p.val (by omega) hpB hpLt
              have hs2 := nonempty p.val hpB hpLt
              omega
        · step as ⟨n, hs⟩
          apply extend _ n hs
          intro k hki
          scalar_tac
    · simp only [h, ↓reduceIte, spec_ok, true_iff]
      have he : i.val = buf.val.length := by scalar_tac
      exact ⟨fun k hk => nonempty k hk (by omega), fun k j hjk hj => disjoint k j hjk hj (by omega)⟩
  · simp [inv]

theorem new_spec :
    order_range.OrderRange.new ⦃ r =>
      Canonical r ∧ (toList r).length = 0 ∧ (∀ c, ¬ inRanges r c) ⦄ := by
  simp [order_range.OrderRange.new, spec_ok, Canonical, storageWF, toList,
    order_range.EMPTY, CanonicalList, inRanges, inRangesList, Array.make]

theorem from_range_spec (start «end» : Std.U64) :
    order_range.OrderRange.from_range start «end» ⦃ r =>
      Canonical r ∧
      (toList r).length = (if start.val < «end».val then 1 else 0) ∧
      ∀ clk, inRanges r clk ↔ start.val ≤ clk.val ∧ clk.val < «end».val ⦄ := by
  unfold order_range.OrderRange.from_range
  by_cases h : start < «end»
  · have hlt : start.val < «end».val := by scalar_tac
    simp [h, hlt, spec_ok, Canonical, storageWF, toList, CanonicalList,
      inRanges, inRangesList, Array.make]
    omega
  · have hle : ¬ start.val < «end».val := by scalar_tac
    simp [h, hle, spec_ok, Canonical, storageWF, toList, order_range.EMPTY, CanonicalList,
      inRanges, inRangesList, Array.make]
    omega

theorem len_spec (r : order_range.OrderRange) (hw : storageWF r) :
    order_range.OrderRange.len r ⦃ n => n.val = (toList r).length ⦄ := by
  rcases r with ⟨a | ring⟩
  · obtain ⟨x, hx⟩ := single_val a
    unfold order_range.OrderRange.len
    step as ⟨v, hv⟩
    have eq : v = x := by simpa [hx] using hv
    subst v
    split_ifs with h
    · have hh : x.start.val < x.end.val := by scalar_tac
      simp [spec_ok, toList, hx, hh]
    · have hh : ¬ x.start.val < x.end.val := by scalar_tac
      simp [spec_ok, toList, hx, hh]
  · simp only [toList, order_range.OrderRange.len, spec_ok, ringList_length ring hw]
    scalar_tac

theorem at_spec (r : order_range.OrderRange) (i : Std.Usize) (hw : storageWF r)
    (hi : i.val < (toList r).length) :
    order_range.OrderRange.at r i ⦃ x => x = (toList r)[i.val] ⦄ := by
  rcases r with ⟨a | ring⟩
  · obtain ⟨x, hx⟩ := single_val a
    by_cases h : x.start.val < x.end.val
    · have hi0 : i.val = 0 := by simp [toList, hx, h] at hi; omega
      unfold order_range.OrderRange.at
      step as ⟨v, hv⟩
      simpa [toList, hx, h, hi0] using hv
    · simp [toList, hx, h] at hi
  · unfold order_range.OrderRange.at
    have hl := ringList_length ring hw
    step with ring_at_spec ring i hw (by simpa only [toList, hl] using hi) as ⟨x, hx⟩
    have hi' : i.val < (ringList ring).length := hi
    exact Option.some.inj (hx.trans (List.getElem?_eq_getElem hi'))

theorem get_spec (r : order_range.OrderRange) (i : Std.Usize) (hw : storageWF r) :
    order_range.OrderRange.get r i ⦃ x => x = (toList r)[i.val]? ⦄ := by
  unfold order_range.OrderRange.get
  step with len_spec r hw as ⟨n, hn⟩
  split_ifs with h
  · have hi : i.val < (toList r).length := by scalar_tac
    step with at_spec r i hw hi as ⟨x, hx⟩
    simp [hx, List.getElem?_eq_getElem hi]
  · have hi : (toList r).length ≤ i.val := by scalar_tac
    simp [spec_ok, List.getElem?_eq_none hi]

theorem first_spec (r : order_range.OrderRange) (hw : storageWF r) :
    order_range.OrderRange.first r ⦃ x => x = (toList r)[0]? ⦄ := by
  exact get_spec r 0#usize hw

theorem last_spec (r : order_range.OrderRange) (hw : storageWF r) :
    order_range.OrderRange.last r ⦃ x => x = (toList r)[(toList r).length - 1]? ⦄ := by
  unfold order_range.OrderRange.last
  step with len_spec r hw as ⟨len, hlen⟩
  split_ifs with empty
  · have hz : (toList r).length = 0 := by scalar_tac
    simp [List.length_eq_zero_iff.mp hz, spec_ok]
  · step as ⟨i, hi⟩
    have bound : i.val < (toList r).length := by scalar_tac
    step with at_spec r i hw bound as ⟨value, hv⟩
    have index : (toList r).length - 1 = i.val := by scalar_tac
    simp only [index, List.getElem?_eq_getElem bound, hv]

theorem contains_spec (r : order_range.OrderRange) (c : Std.U64) (hw : Canonical r) :
    order_range.OrderRange.contains r c ⦃ b => b = true ↔ inRanges r c ⦄ := by
  rcases r with ⟨a | ring⟩
  · obtain ⟨x, hx⟩ := single_val a
    unfold order_range.OrderRange.contains
    step as ⟨v, hv⟩
    have he : v = x := by simpa [hx] using hv
    subst v
    by_cases hNonempty : x.start.val < x.end.val
    · split_ifs <;> simp [spec_ok, inRanges, toList, hx, hNonempty, inRangesList_singleton] <;> scalar_tac
    · split_ifs <;> simp [spec_ok, inRanges, toList, hx, hNonempty, inRangesList]; scalar_tac
  · obtain ⟨hr, hcan⟩ := hw
    change ringWF ring at hr
    change CanonicalList (ringList ring) at hcan
    unfold order_range.OrderRange.contains order_range.Ring.upper
    simp only [lift, bind_ok]
    step with upper_partition_spec ring hr c 0#usize (by simp) hcan as
      ⟨bound, _, hBound, hLeft, hRight⟩
    split_ifs with hPos
    · step as ⟨i, hi⟩
      have hiN : i.val + 1 = bound.val := by scalar_tac
      have hiR : i.val < ring.len.val := by
        rw [ringList_length ring hr] at hBound
        omega
      step with ring_at_list_spec ring hr i hiR as ⟨x, hx⟩
      simp only [decide_eq_true_eq, inRanges, toList, inRangesList]
      have hiL : i.val < (ringList ring).length := by omega
      constructor
      · intro h
        refine ⟨i.val, hiL, hLeft i.val hiL (by simp) (by omega), ?_⟩
        rw [← hx]
        scalar_tac
      · rintro ⟨k, hk, hstart, hend⟩
        have hklt : k < bound.val := by
          by_contra! hn
          exact (Nat.not_lt_of_ge hstart) (hRight k hk hn)
        by_cases heq : k = i.val
        · subst k; rw [hx]; scalar_tac
        · have hlt := canonicalList_end_lt hcan (by omega : k < i.val) hiL
          rw [hx]; scalar_tac
    · simp only [spec_ok, Bool.false_eq_true, false_iff, inRanges, toList, inRangesList]
      rintro ⟨k, hk, hstart, _⟩
      have hz : bound.val = 0 := by scalar_tac
      exact (Nat.not_lt_of_ge hstart) (hRight k hk (by omega))

/-- Copying the active prefix when the input has more than MAX_RANGES slots
    does not change any retained interval. -/
theorem copy_prefix_spec (ranges : alloc.vec.Vec order_range.ClockRange)
    (len : Std.Usize) (hl : len.val ≤ ranges.length) :
    order_range.OrderRange.from_prefix_loop ranges len
      (alloc.vec.Vec.with_capacity order_range.ClockRange len) 0#usize
      ⦃ out => out.val = ranges.val.take len.val ⦄ := by
  unfold order_range.OrderRange.from_prefix_loop
  let inv : (alloc.vec.Vec order_range.ClockRange) × Std.Usize → Prop :=
    fun (v, i) => i.val ≤ len.val ∧ v.val = ranges.val.take i.val
  refine loop.spec_decr_nat (fun (_, i) => len.val - i.val) inv _ _ _ ?_ ?_
  · intro ⟨v, i⟩ ⟨hi, hv⟩
    unfold order_range.OrderRange.from_prefix_loop.body
    simp only
    split_ifs with hlt
    · have hi' : i.val < ranges.val.length := by scalar_tac
      have hlen : v.length = i.val := by
        simp [alloc.vec.Vec.length, hv, Nat.min_eq_left (Nat.le_of_lt hi')]
      step as ⟨r, hr⟩
      step as ⟨v', hv'⟩
      step as ⟨i', hi''⟩
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [hi'', List.take_succ_eq_append_getElem hi', hv', hv, hr]
    · have he : i.val = len.val := by scalar_tac
      simpa only [spec_ok, he] using hv
  · simp [inv, alloc.vec.Vec.with_capacity]

/-- Large growth copies only the live ranges and unwraps them into logical order. -/
theorem grow_copy_spec {extra : Nat} (ring : order_range.Ring) (hr : ringWF ring extra) (capacity : Std.Usize) :
    order_range.Ring.grow_loop0 ring.buf ring.head ring.len
      (alloc.vec.Vec.with_capacity order_range.ClockRange capacity) 0#usize
      ⦃ out => out.val = ringList ring ⦄ := by
  unfold order_range.Ring.grow_loop0
  let inv : alloc.vec.Vec order_range.ClockRange × Std.Usize → Prop :=
    fun (v, i) => i.val ≤ ring.len.val ∧ v.val = (ringList ring).take i.val
  have hlen := ringList_length ring hr
  refine loop.spec_decr_nat (fun (_, i) => ring.len.val - i.val) inv _ _ _ ?_ ?_
  · intro ⟨v, i⟩ ⟨hi, hv⟩
    unfold order_range.Ring.grow_loop0.body
    simp only [lift, bind_ok]
    split_ifs with h
    · have hi' : i.val < ring.len.val := by scalar_tac
      have hiL : i.val < (ringList ring).length := by omega
      have hsize : v.length = i.val := by
        simp [alloc.vec.Vec.length, hv, Nat.min_eq_left (Nat.le_of_lt hiL)]
      step with ring_at_list_spec ring hr i hi' as ⟨x, hx⟩
      step as ⟨out, ho⟩
      step as ⟨j, hj⟩
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [hj, List.take_succ_eq_append_getElem hiL, ho, hv, hx]
    · have he : i.val = (ringList ring).length := by scalar_tac
      simpa [he, spec_ok] using hv
  · simp [inv, alloc.vec.Vec.with_capacity]

/-- After reserving a contiguous destination, growth initializes its spare
    suffix without modifying the copied ranges. -/
theorem grow_pad_spec (initial : alloc.vec.Vec order_range.ClockRange) (needed : Std.Usize)
    (hs : initial.length ≤ needed.val) :
    order_range.Ring.grow_loop1 needed initial ⦃ out =>
      out.length = needed.val ∧ out.val.take initial.length = initial.val ⦄ := by
  unfold order_range.Ring.grow_loop1
  let inv := fun (v : alloc.vec.Vec order_range.ClockRange) =>
    initial.length ≤ v.length ∧ v.length ≤ needed.val ∧ v.val.take initial.length = initial.val
  refine loop.spec_decr_nat (fun v => needed.val - v.length) inv _ _ initial ?_ ?_
  · intro v ⟨hle, hmax, hpre⟩
    unfold order_range.Ring.grow_loop1.body
    dsimp only
    split_ifs with hlt
    · step as ⟨out, hout⟩
      have hLen : out.length = v.length + 1 := by simp [alloc.vec.Vec.length, hout]
      refine ⟨⟨by omega, by scalar_tac, ?_⟩, by scalar_tac⟩
      simpa [hout, List.take_append, Nat.sub_eq_zero_of_le hle] using hpre
    · simp only [spec_ok]
      exact ⟨by scalar_tac, hpre⟩
  · simp [inv, hs, alloc.vec.Vec.length]

/-- After expanding the ring, the wrapped low segment is copied to newly
    initialized slots above the old capacity. Every other slot is unchanged. -/
theorem grow_wrapped_low_spec (initial : alloc.vec.Vec order_range.ClockRange)
    (cap wrapped : Std.Usize) (hw : wrapped.val ≤ cap.val)
    (hsize : cap.val + wrapped.val ≤ initial.length) :
    order_range.Ring.grow_loop3 initial cap wrapped 0#usize ⦃ out =>
      out.length = initial.length ∧ ∀ j : Nat, out.val[j]? =
        initial.val[if cap.val ≤ j ∧ j < cap.val + wrapped.val then j - cap.val else j]? ⦄ := by
  let inv : alloc.vec.Vec order_range.ClockRange × Std.Usize → Prop := fun (v, i) =>
    v.length = initial.length ∧ i.val ≤ wrapped.val ∧ ∀ j : Nat, v.val[j]? =
      initial.val[if cap.val ≤ j ∧ j < cap.val + i.val then j-cap.val else j]?
  unfold order_range.Ring.grow_loop3
  refine loop.spec_decr_nat (fun (_, i) => wrapped.val - i.val) inv _ _ _ ?_ ?_
  · intro ⟨v, i⟩ ⟨hlen, hi, values⟩
    unfold order_range.Ring.grow_loop3.body
    simp only
    split_ifs with h
    · have live : i.val < v.val.length := by scalar_tac
      step as ⟨x, hx⟩
      step as ⟨slot, hs⟩
      step as ⟨_, write, _, hwv⟩
      step as ⟨next, hn⟩
      have he : (write x).val = v.val.set slot.val x := by simp [hwv, alloc.vec.Vec.set]
      have source : some x = initial.val[i.val]? := by
        have hb : ¬cap.val ≤ i.val := by scalar_tac
        simpa [hb, List.getElem?_eq_getElem live, hx] using values i.val
      refine ⟨⟨by simp [alloc.vec.Vec.length, he, ← hlen], by scalar_tac, ?_⟩, by scalar_tac⟩
      intro j
      by_cases eq : j = slot.val
      · subst j
        have hslot : slot.val < v.val.length := by scalar_tac
        have hnew : cap.val ≤ slot.val ∧ slot.val < cap.val + next.val := by omega
        have hsub : slot.val - cap.val = i.val := by omega
        simpa [he, hslot, hnew, hsub] using source
      · have same : (cap.val ≤ j ∧ j < cap.val + next.val) ↔
            (cap.val ≤ j ∧ j < cap.val + i.val) := by omega
        simpa [he, same, eq, Ne.symm eq] using values j
    · have eq : i.val = wrapped.val := by scalar_tac
      simpa only [spec_ok, eq] using And.intro hlen values
  · simp [inv]
    intro j
    rw [ite_eq_right (by omega)]

/-- If it is cheaper to move the upper physical segment, the backward loop
    preserves source values even when the two spans overlap. -/
theorem grow_wrapped_high_spec (initial : alloc.vec.Vec order_range.ClockRange)
    (head added cap : Std.Usize) (hh : head.val ≤ cap.val)
    (hsize : cap.val + added.val ≤ initial.length) :
    order_range.Ring.grow_loop4 initial head added cap ⦃ out =>
      out.length = initial.length ∧ ∀ j : Nat, out.val[j]? =
        initial.val[if head.val + added.val ≤ j ∧ j < cap.val + added.val then j-added.val else j]? ⦄ := by
  let inv : alloc.vec.Vec order_range.ClockRange × Std.Usize → Prop := fun (v, i) =>
    v.length = initial.length ∧ head.val ≤ i.val ∧ i.val ≤ cap.val ∧ ∀ j : Nat, v.val[j]? =
      initial.val[if i.val + added.val ≤ j ∧ j < cap.val + added.val then j-added.val else j]?
  unfold order_range.Ring.grow_loop4
  refine loop.spec_decr_nat (fun (_, i) => i.val) inv _ _ _ ?_ ?_
  · intro ⟨v, i⟩ ⟨hlen, hlo, hhi, values⟩
    unfold order_range.Ring.grow_loop4.body
    simp only
    split_ifs with h
    · step as ⟨prev, hp⟩
      step as ⟨x, hx⟩
      step as ⟨slot, hs⟩
      step as ⟨_, write, _, hwv⟩
      have live : prev.val < v.val.length := by scalar_tac
      have he : (write x).val = v.val.set slot.val x := by simp [hwv, alloc.vec.Vec.set]
      have source : some x = initial.val[prev.val]? := by
        have hb : ¬ i.val + added.val ≤ prev.val := by scalar_tac
        simpa [hb, List.getElem?_eq_getElem live, hx] using values prev.val
      refine ⟨⟨by simp [alloc.vec.Vec.length, he, ← hlen], by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
      intro j
      by_cases eq : j = slot.val
      · subst j
        have hslot : slot.val < v.val.length := by scalar_tac
        have hnew : prev.val + added.val ≤ slot.val ∧ slot.val < cap.val + added.val := by scalar_tac
        have hsub : slot.val - added.val = prev.val := by omega
        simpa [he, hslot, hnew, hsub] using source
      · have same : (prev.val + added.val ≤ j ∧ j < cap.val + added.val) ↔
            (i.val + added.val ≤ j ∧ j < cap.val + added.val) := by scalar_tac
        simpa [he, same, eq, Ne.symm eq] using values j
    · have eq : i.val = head.val := by scalar_tac
      simpa only [spec_ok, eq] using And.intro hlen values
  · refine ⟨rfl, hh, Nat.le_refl _, ?_⟩
    intro j
    rw [ite_eq_right (by omega)]

private theorem take_set_boundary {α : Type} (l : List α) (k : Nat) (x : α) :
    (l.set k x).take k = l.take k := by
  induction l generalizing k with
  | nil => simp
  | cons a xs ih =>
    cases k with
    | zero => simp
    | succ k => simp [List.set, List.take, ih]

/-- A spare capacity marker may occupy one extra physical slot. Installing
    it preserves the active prefix even for an arbitrary caller-supplied hint. -/
theorem budget_slot_spec (buf : alloc.vec.Vec order_range.ClockRange)
    (len hint : Std.Usize) (hl : len.val ≤ buf.length) (hc : buf.length ≤ 2^30)
    (hh : hint.val ≤ 2^30) :
    (if hint > alloc.vec.Vec.len buf then do
       let value : order_range.ClockRange := ⟨UScalar.cast .U64 hint, 0#u64⟩
       if len = alloc.vec.Vec.len buf then alloc.vec.Vec.push buf value
       else do
         let (_, write) ← alloc.vec.Vec.index_mut_usize buf len
         ok (write value)
     else if len < alloc.vec.Vec.len buf then do
       let (_, write) ← alloc.vec.Vec.index_mut_usize buf len
       ok (write order_range.EMPTY)
     else ok buf) ⦃ out =>
       len.val ≤ out.length ∧ out.length ≤ 2^30 ∧ out.val.take len.val = buf.val.take len.val ⦄ := by
  split_ifs with hHint hFull hFree
  · step as ⟨out, hout⟩
    have heq : len.val = buf.val.length := by scalar_tac
    simp [alloc.vec.Vec.length, hout, heq]
    scalar_tac
  · have hi : len.val < buf.length := by scalar_tac
    step as ⟨_, write, _, hw⟩
    simp [hw, alloc.vec.Vec.set, alloc.vec.Vec.length, take_set_boundary] at *
    omega
  · have hi : len.val < buf.val.length := by scalar_tac
    step as ⟨_, write, _, hw⟩
    simpa [hw, alloc.vec.Vec.set, alloc.vec.Vec.length, take_set_boundary] using And.intro hl hc
  · simp only [spec_ok]
    exact ⟨hl, hc, True.intro⟩

theorem max_ranges_spec : order_range.MAX_RANGES ⦃ cap => cap.val = 2^30 ⦄ := by
  unfold order_range.MAX_RANGES
  have bits := System.Platform.numBits_eq
  step as ⟨n, hn⟩ <;> rcases bits with h | h <;> simp_all [Nat.shiftLeft_eq] <;> scalar_tac

private theorem umax_val (a b : Std.Usize) :
    (core.cmp.impls.OrdUsize.max a b).val = max a.val b.val := by
  unfold core.cmp.impls.OrdUsize.max
  split <;> scalar_tac

private theorem grow_target_spec (cap needed hint limit : Std.Usize)
    (hc : cap.val ≤ needed.val) (hn : needed.val ≤ limit.val) (hh : hint.val ≤ limit.val)
    (bound : limit.val = 2^30) :
    (if hint > cap then
      if needed ≤ hint then do
        let d ← cap * 2#usize
        let n ← needed + 1#usize
        ok (core.cmp.impls.OrdUsize.min (core.cmp.impls.OrdUsize.max d n) hint)
      else do
        let d ← (core.cmp.impls.OrdUsize.max cap hint) * 2#usize
        ok (core.cmp.impls.OrdUsize.max needed (core.cmp.impls.OrdUsize.min d limit))
     else do
       let d ← (core.cmp.impls.OrdUsize.max cap hint) * 2#usize
       ok (core.cmp.impls.OrdUsize.max needed (core.cmp.impls.OrdUsize.min d limit))) ⦃ next =>
         needed.val ≤ next.val ∧ next.val ≤ limit.val ⦄ := by
  have hm := umax_val cap hint
  split_ifs <;> step* <;> simp only [umax_val, umin_val] <;> scalar_tac

structure Grown (r : order_range.Ring) (needed : Std.Usize) (out : order_range.Ring)
    (extra : Nat := 1) : Prop where
  wf : ringWF out extra
  len_eq : out.len = r.len
  fits : needed.val ≤ out.buf.length
  view : ringList out = ringList r

/-- Growing a wrapped buffer preserves every active range in logical order.
    The new capacity covers the request and fits both the physical index and
    head representations. -/
theorem ring_grow_spec {extra : Nat} (r : order_range.Ring) (needed hint : Std.Usize) (hw : ringWF r extra)
    (hl : r.len.val ≤ needed.val) (hn : needed.val ≤ 2^30) (hh : hint.val ≤ 2^30) :
    order_range.Ring.grow r needed hint ⦃ out => Grown r needed out extra ⦄ := by
  let cap := alloc.vec.Vec.len r.buf
  have hcap : cap.val = r.buf.val.length := rfl
  have ⟨headLive, lenLive, many, capBound⟩ := hw
  have u32Bound : UScalar.max UScalarTy.U32 = 2^32-1 := by
    rw [UScalar.max_UScalarTy_U32_eq]; simp [U32.max, U32.numBits]
  have alias2 (v n) : order_range.Ring.grow_loop2 v n = order_range.Ring.grow_loop1 n v := rfl
  have alias5 : order_range.Ring.grow_loop5 = order_range.Ring.grow_loop4 := rfl
  have alias6 : order_range.Ring.grow_loop6 = order_range.Ring.grow_loop0 := rfl
  have alias7 : order_range.Ring.grow_loop7 = order_range.Ring.grow_loop1 := rfl
  have alias8 (v n) : order_range.Ring.grow_loop8 v n = order_range.Ring.grow_loop1 n v := rfl
  have alias9 : order_range.Ring.grow_loop9 = order_range.Ring.grow_loop3 := rfl
  have alias10 : order_range.Ring.grow_loop10 = order_range.Ring.grow_loop4 := rfl
  have alias11 : order_range.Ring.grow_loop11 = order_range.Ring.grow_loop4 := rfl
  unfold order_range.Ring.grow
  have capEq : alloc.vec.Vec.len r.buf = cap := rfl
  dsimp only
  simp only [capEq, alias2, alias5, alias6, alias7, alias8, alias9, alias10, alias11]
  by_cases small : needed < cap
  · simp only [small, ↓reduceIte, spec_ok]; exact ⟨hw, rfl, by scalar_tac, rfl⟩
  simp only [small, ↓reduceIte]
  by_cases finished : needed = cap ∧ hint = 0#usize
  · simp only [finished.1, finished.2, ↓reduceIte, spec_ok]
    exact ⟨hw, rfl, Nat.le_refl _, rfl⟩
  have normalize (x : Result order_range.Ring) :
      (if needed = cap then if hint = 0#usize then ok r else x else x) = x := by
    split <;> simp_all
  rw [normalize]
  step with max_ranges_spec as ⟨limit, bound⟩
  have limitOk : needed ≤ limit := by scalar_tac
  simp only [massert, limitOk, ↓reduceIte, lift, bind_ok]
  have hm := umax_val cap hint
  step as ⟨doubleCap, hd⟩ <;> try scalar_tac
  by_cases large : needed > doubleCap
  · simp only [large, ↓reduceIte]
    step with grow_copy_spec r hw needed as ⟨v, hv⟩
    have size : v.length = r.len.val := by
      simpa [alloc.vec.Vec.length, hv] using ringList_length r hw
    step with grow_pad_spec v needed (by omega) as ⟨out, ho, pre⟩
    have zero : (0#u32).val = 0 := by decide
    change out.val.length = needed.val at ho
    refine ⟨⟨by simpa only [zero] using (show 0 < out.val.length by omega), by scalar_tac, many, by scalar_tac⟩, rfl, by scalar_tac, ?_⟩
    change OrderRangeRing.toList out.val (0#u32).val r.len.val = ringList r
    rw [zero, OrderRangeRing.toList_initial, ← size, pre, hv]
  · simp only [large, ↓reduceIte]
    step with grow_target_spec cap needed hint limit (by scalar_tac) (by omega) (by omega) bound
      as ⟨next, lower, upper⟩
    step with grow_pad_spec r.buf next (by scalar_tac) as ⟨padded, plen, pre⟩
    step as ⟨tail, htail⟩
    have ht : tail.val = r.buf.val.length - r.head.val := by scalar_tac
    by_cases wraps : tail < UScalar.cast .Usize r.len
    · simp only [wraps, ↓reduceIte]
      step as ⟨wrapped, hwrap⟩
      step as ⟨added, hadd⟩
      have wval : wrapped.val = r.len.val - (r.buf.val.length - r.head.val) := by scalar_tac
      have aval : cap.val + added.val = next.val := by scalar_tac
      have wcap : wrapped.val ≤ cap.val := by omega
      by_cases low : wrapped ≤ tail ∧ wrapped ≤ added
      · simp only [low.1, low.2, ↓reduceIte]
        step with grow_wrapped_low_spec padded cap wrapped wcap (by scalar_tac) as ⟨out, ol, slots⟩
        have view := OrderRangeRing.grow_view_low r.buf.val padded.val out.val r.head.val r.len.val
          headLive lenLive (by scalar_tac) (by scalar_tac) pre ol (by rw [← wval]; exact slots)
        exact ⟨⟨by scalar_tac, by scalar_tac, many, by scalar_tac⟩, rfl, by scalar_tac, view⟩
      · have choose (x y : Result order_range.Ring) :
            (if wrapped ≤ tail then if wrapped ≤ added then x else y else y) = y := by
          split <;> simp_all
        rw [choose]
        step with grow_wrapped_high_spec padded (UScalar.cast .Usize r.head) added cap
          (by scalar_tac) (by scalar_tac) as ⟨out, ol, slots⟩
        step as ⟨newHead, nh⟩
        have nv : newHead.val = r.head.val + added.val := by scalar_tac
        have cast := UScalar.cast_inBounds_spec .U32 newHead (by rw [u32Bound]; omega)
        have nc : (UScalar.cast .U32 newHead).val = r.head.val + added.val := by simpa [lift, nv] using cast
        have plenList : padded.val.length = next.val := plen
        have olenList : out.val.length = next.val := ol.trans plen
        have view := OrderRangeRing.grow_view_high r.buf.val padded.val out.val r.head.val r.len.val
          added.val headLive lenLive (by omega) pre ol (by simpa [← hcap] using slots)
        refine ⟨⟨?_, by scalar_tac, many, by scalar_tac⟩, rfl, by scalar_tac, ?_⟩
        · change (UScalar.cast .U32 newHead).val < out.val.length
          omega
        · simpa only [ringList, nc] using view
    · simp only [wraps, ↓reduceIte, spec_ok]
      have view := OrderRangeRing.grow_view_contiguous r.buf.val padded.val r.head.val r.len.val
        headLive (by scalar_tac) (by scalar_tac) pre
      exact ⟨⟨by scalar_tac, by scalar_tac, many, by scalar_tac⟩, rfl, by scalar_tac, view⟩

/-- The first inactive slot can guide growth only within the representable
    capacity. Its contents need no invariant. -/
theorem capacity_hint_spec {extra : Nat} (r : order_range.Ring) (hw : ringWF r extra) :
    order_range.Ring.capacity_hint r ⦃ n => n.val ≤ 2^30 ⦄ := by
  rcases hw with ⟨hh, hl, _, hc⟩
  unfold order_range.Ring.capacity_hint
  simp only [lift, bind_ok]
  by_cases full : UScalar.cast .Usize r.len = alloc.vec.Vec.len r.buf
  · simp [full, spec_ok]
  · simp only [full, ↓reduceIte]
    have hi : (UScalar.cast .Usize r.len).val < r.buf.length := by scalar_tac
    step with ring_at_physical_spec r _ hh hi as ⟨slot, _⟩
    split_ifs <;> simp [spec_ok]
    step with max_ranges_spec as ⟨cap, hcap⟩
    split_ifs <;> simp only [spec_ok] <;> try scalar_tac
    have bound : slot.start.val ≤ cap.val := by scalar_tac
    have cast := UScalar.cast_inBounds_spec .Usize slot.start (by apply Nat.le_trans bound; scalar_tac)
    have eq : (UScalar.cast .Usize slot.start).val = slot.start.val := by simpa [lift] using cast
    omega

/-- Slots outside the replacement correspond to the original logical prefix
    and suffix. The caller writes the new interval(s) into the gap. -/
private def GapSlots (r v : order_range.Ring) (lo hi width : Nat) : Prop :=
  (∀ j, j < lo → (slotsOf v)[j]? = (ringList r)[j]?) ∧
  (∀ j, hi ≤ j → j < r.len.val →
    (slotsOf v)[lo + width + (j-hi)]? = (ringList r)[j]?)

structure Gap (r out : order_range.Ring) (lo hi width : Nat) : Prop where
  head : out.head.val < out.buf.length
  len : out.len.val = r.len.val - (hi-lo) + width
  fits : out.len.val ≤ out.buf.length
  bound : out.buf.length ≤ 2^30
  prefix_eq : ∀ j, j < lo → (ringList out)[j]? = (ringList r)[j]?
  suffix_eq : ∀ j, hi ≤ j → j < r.len.val →
    (ringList out)[lo+width+(j-hi)]? = (ringList r)[j]?

private theorem slot_active (r : order_range.Ring) (head : r.head.val < r.buf.length)
    (len : r.len.val ≤ r.buf.length) {j : Nat} (hj : j < r.len.val) :
    (slotsOf r)[j]? = (ringList r)[j]? :=
  (OrderRangeRing.lookup_full _ head len hj).symm

private theorem usize_u32_exact (n : Std.Usize) (h : n.val ≤ 2^30) :
    (UScalar.cast .U32 n).val = n.val := by
  have bound : UScalar.max UScalarTy.U32 = 2^32-1 := by
    rw [UScalar.max_UScalarTy_U32_eq]; simp [U32.max, U32.numBits]
  simpa [lift] using UScalar.cast_inBounds_spec .U32 n (by rw [bound]; omega)

private theorem gap_finish_spec (r v : order_range.Ring) (lo hi width : Nat)
    (len taken count hint : Std.Usize) (hlen : len.val = r.len.val)
    (ht : taken.val = hi-lo) (hw : count.val = width) (order : lo ≤ hi) (last : hi ≤ r.len.val)
    (hh : v.head.val < v.buf.length) (fits : r.len.val-(hi-lo)+width ≤ v.buf.length)
    (cap : v.buf.length ≤ 2^30) (slots : GapSlots r v lo hi width) :
    (do
      let n ← len-taken
      let n ← n+count
      let out := {v with len := UScalar.cast .U32 n}
      if UScalar.cast .Usize out.len < alloc.vec.Vec.len out.buf then
        order_range.Ring.set out (UScalar.cast .Usize out.len) {start := UScalar.cast .U64 hint, «end» := 0#u64}
      else ok out) ⦃ out => Gap r out lo hi width ⦄ := by
  step as ⟨n, hn⟩
  step as ⟨k, hk⟩
  have kn : k.val = r.len.val - (hi-lo) + width := by omega
  have cast := usize_u32_exact k (by omega)
  let out := {v with len := UScalar.cast .U32 k}
  have ol : out.len.val = r.len.val-(hi-lo)+width := cast.trans kn
  have ready : Gap r out lo hi width := by
    refine ⟨hh, ol, by change out.len.val ≤ v.buf.length; omega, cap, ?_, ?_⟩
    · intro j hj
      rw [← slot_active out hh (by change out.len.val ≤ v.buf.length; omega) (by omega)]
      exact slots.1 j hj
    · intro j hj hj'
      rw [← slot_active out hh (by change out.len.val ≤ v.buf.length; omega) (by omega)]
      exact slots.2 j hj hj'
  by_cases spare : UScalar.cast .Usize out.len < alloc.vec.Vec.len out.buf
  · change (if UScalar.cast .Usize out.len < alloc.vec.Vec.len out.buf then _ else _) ⦃ _ ⦄
    rw [ite_eq_left spare]
    step with ring_set_spare_spec out (UScalar.cast .Usize out.len) ⟨UScalar.cast .U64 hint, 0#u64⟩ hh (by scalar_tac) (by scalar_tac) as ⟨w, wh, wl, wb, wv⟩
    exact ⟨by simpa only [wh, wb] using ready.head, by simpa only [wl] using ready.len,
      by simpa only [wl, wb] using ready.fits, by simpa only [wb] using ready.bound,
      by simpa only [wv] using ready.prefix_eq, by simpa only [wv] using ready.suffix_eq⟩
  · change (if UScalar.cast .Usize out.len < alloc.vec.Vec.len out.buf then _ else _) ⦃ _ ⦄
    simpa only [spare, ↓reduceIte, spec_ok] using ready

/-- Replacing a window keeps the slots on both sides in their original
    order, regardless of which side is shorter or wraps around the buffer. -/
theorem make_gap_spec {extra : Nat} (r : order_range.Ring) (lo hi width : Std.Usize) (hw : ringWF r extra)
    (ord : lo.val ≤ hi.val) (last : hi.val ≤ r.len.val)
    (limit : r.len.val-(hi.val-lo.val)+width.val ≤ 2^30) :
    order_range.Ring.make_gap r lo hi width ⦃ out => Gap r out lo.val hi.val width.val ⦄ := by
  have ⟨head, sized, _, cap⟩ := hw
  change r.head.val < r.buf.length at head
  change r.len.val ≤ r.buf.length at sized
  change r.buf.length ≤ 2^30 at cap
  let len := UScalar.cast .Usize r.len
  have leq : len.val = r.len.val := by scalar_tac
  unfold order_range.Ring.make_gap
  simp only [lift, bind_ok]
  step as ⟨taken, ht⟩
  step as ⟨suffix, hs⟩
  have sv : suffix.val = r.len.val-hi.val := by scalar_tac
  by_cases same : width = taken
  · simp only [same, ↓reduceIte, spec_ok]
    refine ⟨head, by omega, sized, cap, fun _ _ => rfl, ?_⟩
    intro j h _
    rw [show lo.val+taken.val+(j-hi.val) = j by omega]
  · simp only [same, ↓reduceIte]
    step with capacity_hint_spec r hw as ⟨hint, hintBound⟩
    by_cases grows : width > taken
    · simp only [grows, ↓reduceIte]
      step as ⟨added, ha⟩
      have ap : 0 < added.val := by scalar_tac
      step as ⟨needed, hn⟩
      have need : needed.val = r.len.val+added.val := by scalar_tac
      step with ring_grow_spec r needed hint hw (by omega) (by omega) hintBound as ⟨g, gspec⟩
      obtain ⟨gw, gl, fits, gv⟩ := gspec
      have old (j : Nat) (hj : j < r.len.val) : (slotsOf g)[j]? = (ringList r)[j]? := by
        rw [slot_active g gw.1 gw.2.1 (by simpa only [gl] using hj), gv]
      by_cases front : lo < suffix
      · simp only [front, ↓reduceIte]
        step as ⟨distance, hd⟩
        have gh : g.head.val < g.buf.length := gw.1
        step with physical_spec (alloc.vec.Vec.len g.buf) (UScalar.cast .Usize g.head) distance (by scalar_tac) (by scalar_tac) as ⟨p, hp, pb⟩
        have pval : p.val = OrderRangeRing.position g.buf.length g.head.val (g.buf.length-added.val) := by
          simpa only [show (alloc.vec.Vec.len g.buf).val = g.buf.length by scalar_tac,
            show distance.val = g.buf.length-added.val by scalar_tac,
            show (UScalar.cast .Usize g.head).val = g.head.val by scalar_tac] using hp
        let rewound := {g with head := UScalar.cast .U32 p}
        have rp : rewound.head.val = p.val := usize_u32_exact p (by have := gw.2.2.2; scalar_tac)
        have rh : rewound.head.val < rewound.buf.length := by rw [rp]; exact pb
        have old' (j : Nat) (hj : j < r.len.val) :
            (slotsOf rewound)[j+added.val]? = (ringList r)[j]? := by
          rw [← old j hj]
          change (OrderRangeRing.toList g.buf.val rewound.head.val g.buf.length)[j+added.val]? = _
          rw [rp, pval]
          exact OrderRangeRing.rewind_lookup _ gw.1 ap (by change j+added.val < g.buf.length; omega)
        step with move_slots_spec rewound added 0#usize lo rh (by change _ ≤ g.buf.length; omega) (by scalar_tac)
          as ⟨v, vh, _, vb, slots⟩
        apply gap_finish_spec r v lo.val hi.val width.val len taken width hint leq ht rfl ord last
          (by simpa only [vh, vb] using rh) (by rw [vb]; omega)
          (by simpa only [vb] using gw.2.2.2)
        constructor
        · intro j hj
          simpa [slots, movedIndex, hj, Nat.add_comm] using old' j (by omega)
        · intro j hj endJ
          have idx : lo.val+width.val+(j-hi.val) = j+added.val := by omega
          rw [idx, slots, movedIndex, ite_eq_right (by scalar_tac)]
          exact old' j endJ
      · simp only [front, ↓reduceIte]
        step as ⟨dst,hdst⟩
        step with move_slots_spec g hi dst suffix gw.1 (by omega) (by omega) as ⟨v, vh, _, vb, slots⟩
        apply gap_finish_spec r v lo.val hi.val width.val len taken width hint leq ht rfl ord last
          (by simpa only [vh, vb] using gw.1) (by omega) (by simpa only [vb] using gw.2.2.2)
        constructor
        · intro j hj
          rw [slots, movedIndex, ite_eq_right (by omega)]
          exact old j (by omega)
        · intro j hj endJ
          rw [slots, movedIndex, ite_eq_left (by omega)]
          rw [show hi.val + (lo.val + width.val + (j-hi.val) - dst.val) = j by omega]
          exact old j endJ
    · have shrinks : width < taken := by scalar_tac
      simp only [grows, shrinks, ↓reduceIte]
      step as ⟨cut, hcut⟩
      by_cases front : lo < suffix
      · simp only [front, ↓reduceIte]
        step with move_slots_spec r 0#usize cut lo head (by scalar_tac) (by scalar_tac) as ⟨v, vh, _, vb, values⟩
        step with physical_spec (alloc.vec.Vec.len v.buf) (UScalar.cast .Usize v.head) cut (by scalar_tac) (by scalar_tac) as ⟨p, hp, pb⟩
        let advanced := {v with head := UScalar.cast .U32 p}
        have pp : advanced.head.val = p.val := usize_u32_exact p (by scalar_tac)
        have pv : p.val = OrderRangeRing.position v.buf.length v.head.val cut.val := by
          simpa only [show (alloc.vec.Vec.len v.buf).val = v.buf.length by scalar_tac,
            show (UScalar.cast .Usize v.head).val = v.head.val by scalar_tac] using hp
        have shifted (j : Nat) (hj : cut.val+j < v.buf.length) :
            (slotsOf advanced)[j]? = (slotsOf v)[cut.val+j]? := by
          change (OrderRangeRing.toList v.buf.val advanced.head.val v.buf.length)[j]? = _
          rw [pp, pv]
          exact OrderRangeRing.advance_lookup _ (by simpa only [vh, vb] using head) hj
        apply gap_finish_spec r advanced lo.val hi.val width.val len taken width hint leq ht rfl ord last
          (by rw [pp]; exact pb) (by change _ ≤ v.buf.length; omega) (by change v.buf.length ≤ _; omega)
        constructor
        · intro j hj
          rw [shifted j (by omega), values, movedIndex, ite_eq_left (by omega)]
          rw [show 0 + (cut.val+j-cut.val) = j by omega]
          exact slot_active r head sized (by omega)
        · intro j hj endJ
          have idx : cut.val+(lo.val+width.val+(j-hi.val)) = j := by omega
          rw [shifted _ (by omega), idx, values, movedIndex, ite_eq_right (by omega)]
          exact slot_active r head sized endJ
      · simp only [front, ↓reduceIte]
        step as ⟨dst,hdst⟩
        step with move_slots_spec r hi dst suffix head (by omega) (by omega) as ⟨v, vh, _, vb, values⟩
        apply gap_finish_spec r v lo.val hi.val width.val len taken width hint leq ht rfl ord last
          (by simpa only [vh, vb] using head) (by omega) (by omega)
        constructor
        · intro j hj
          rw [values, movedIndex, ite_eq_right (by omega)]
          exact slot_active r head sized (by omega)
        · intro j hj endJ
          rw [values, movedIndex, ite_eq_left (by omega), show hi.val+(lo.val+width.val+(j-hi.val)-dst.val) = j by omega]
          exact slot_active r head sized endJ

/-- Writing the replacement into a one-slot gap realizes a list splice,
    including when the remaining ring contains only one range. -/
theorem fill_gap {extra : Nat} (r v : order_range.Ring) (lo hi : Std.Usize) (x : order_range.ClockRange)
    (hw : ringWF r extra) (order : lo.val ≤ hi.val) (last : hi.val ≤ r.len.val)
    (g : Gap r v lo.val hi.val 1) :
    order_range.Ring.set v lo x ⦃ out =>
      out.head.val < out.buf.length ∧ out.len = v.len ∧ out.len.val ≤ out.buf.length ∧
      out.buf.length ≤ 2^30 ∧ ringList out = (ringList r).take lo.val ++ x :: (ringList r).drop hi.val ⦄ := by
  have active : lo.val < v.len.val := by have := g.len; omega
  step with ring_set_physical_spec v lo x g.head (Nat.lt_of_lt_of_le active g.fits)
    as ⟨out, oh, ol, ob⟩
  have size : out.buf.length = v.buf.length := by simp [alloc.vec.Vec.length, ob]
  have list : ringList out = (ringList v).set lo.val x := by
    unfold ringList
    rw [oh, ol, ob]
    exact OrderRangeRing.set_active v.buf.val g.head g.fits active x
  have srcLen := ringList_length r hw
  have tgtLen : (ringList v).length = v.len.val := OrderRangeRing.toList_length _ (Nat.le_of_lt g.head) g.fits
  refine ⟨by simpa only [oh, size] using g.head, ol, by simpa only [ol, size] using g.fits,
    by simpa only [size] using g.bound, ?_⟩
  rw [list]
  have plen : ((ringList r).take lo.val).length = lo.val := by simp [srcLen]; omega
  apply List.ext_getElem?
  intro i
  by_cases before : i < lo.val
  · rw [List.getElem?_append_left (by omega)]
    simp [before, show lo.val ≠ i by omega, g.prefix_eq i before]
  · by_cases atGap : i = lo.val
    · subst i
      rw [List.getElem?_append_right (by omega), plen, Nat.sub_self]
      simp [show lo.val < (ringList v).length by omega]
    · have beyond : lo.val < i := by omega
      let j := hi.val + (i-lo.val-1)
      have idx : lo.val+1+(j-hi.val) = i := by dsimp [j]; omega
      have off : i-lo.val = (i-lo.val-1)+1 := by omega
      rw [List.getElem?_append_right (by omega), plen, off, List.getElem?_cons_succ, List.getElem?_drop]
      have hne : lo.val ≠ i := by omega
      simp only [List.getElem?_set, hne, ↓reduceIte]
      by_cases inside : j < r.len.val
      · simpa only [idx, j] using g.suffix_eq j (by dsimp [j]; omega) inside
      · have oldEnd : (ringList r).length ≤ j := by omega
        have newEnd : (ringList v).length ≤ i := by have := g.len; dsimp [j] at *; omega
        rw [List.getElem?_eq_none newEnd]
        exact (List.getElem?_eq_none oldEnd).symm

structure InsertedRing (r out : order_range.Ring) (x : order_range.ClockRange) : Prop where
  head : out.head.val < out.buf.length
  fits : out.len.val ≤ out.buf.length
  bound : out.buf.length ≤ 2^30
  positive : 0 < out.len.val
  count : out.len.val ≤ r.len.val+1
  canonical : CanonicalList (ringList out)
  mem : ∀ c, inRangesList (ringList out) c ↔ inRangesList (ringList r) c ∨
    (x.start.val ≤ c.val ∧ c.val < x.end.val)

/-- Strict gaps exclude adjacency at both ends of the new interval. -/
def Separate (l : List order_range.ClockRange) (x : order_range.ClockRange) : Prop :=
  ∀ i (h : i < l.length), l[i].end.val < x.start.val ∨ x.end.val < l[i].start.val

theorem ring_try_insert_exact {extra : Nat} (r : order_range.Ring) (x : order_range.ClockRange)
    (limit : Std.Usize) (hw : ringWF r extra) (hc : CanonicalList (ringList r))
    (valid : x.start.val < x.end.val) (bound : limit.val = 2^30) :
    order_range.Ring.try_insert r x limit ⦃ (status, out) => match status with
      | .Ok _ => InsertedRing r out x ∧ ¬ (r.len.val = 2^30 ∧ Separate (ringList r) x)
      | .Err e => e = .LimitExceeded ∧ out = r ∧ r.len.val = 2^30 ∧ Separate (ringList r) x ⦄ := by
  let src := ringList r
  have size := ringList_length r hw
  have cap : r.len.val ≤ 2^30 := Nat.le_trans hw.2.1 hw.2.2.2
  unfold order_range.Ring.try_insert
  simp only [lift, bind_ok]
  step with lower_partition_spec r hw x.start hc as ⟨lo, loBound, before, firstEnd⟩
  have findPast :
      (if lo = UScalar.cast .Usize r.len then ok lo else do
        let cr ← order_range.Ring.at r lo
        if cr.start > x.end then ok lo else order_range.Ring.upper r x.end lo) ⦃ hi =>
          lo.val ≤ hi.val ∧ hi.val ≤ (ringList r).length ∧
          (∀ k (hk : k < (ringList r).length), lo.val ≤ k → k < hi.val →
            (ringList r)[k].start.val ≤ x.end.val) ∧
          ∀ k (hk : k < (ringList r).length), hi.val ≤ k → x.end.val < (ringList r)[k].start.val ⦄ := by
    by_cases exhausted : lo = UScalar.cast .Usize r.len
    · simp only [exhausted,↓reduceIte,spec_ok]
      have atEnd : lo.val = r.len.val := by scalar_tac
      refine ⟨le_rfl,by scalar_tac,fun _ _ a b => False.elim (by omega),?_⟩
      intro k hk ge
      scalar_tac
    · simp only [exhausted,↓reduceIte]
      have live : lo.val < r.len.val := by scalar_tac
      step with ring_at_list_spec r hw lo live as ⟨cr,hcr⟩
      by_cases gap : cr.start > x.end
      · simp only [gap,↓reduceIte,spec_ok]
        refine ⟨le_rfl,loBound,fun _ _ a b => False.elim (by omega),?_⟩
        intro k hk ge
        rw [hcr] at gap
        have atLo : x.end.val < (ringList r)[lo.val].start.val := by scalar_tac
        rcases eq_or_lt_of_le ge with eq | lt
        · simpa only [←eq] using atLo
        · exact Nat.lt_trans atLo (canonicalList_start_lt hc lt hk)
      · simp only [gap,↓reduceIte]
        simpa only [order_range.Ring.upper,lift,bind_ok] using upper_partition_spec r hw x.end lo loBound hc
  step with findPast as ⟨hi, ord, hiBound, lastStart, after⟩
  have last : hi.val ≤ r.len.val := by omega
  have write (m : order_range.ClockRange) (can : CanonicalList (src.take lo.val ++ m :: src.drop hi.val))
      (member : ∀ c, inRangesList (src.take lo.val ++ m :: src.drop hi.val) c ↔
         inRangesList src c ∨ (x.start.val ≤ c.val ∧ c.val < x.end.val))
      (fits : r.len.val-(hi.val-lo.val)+1 ≤ 2^30)
      (accepted : ¬ (r.len.val = 2^30 ∧ Separate (ringList r) x)) :
      (do
        let v ← order_range.Ring.make_gap r lo hi 1#usize
        let out ← order_range.Ring.set v lo m
        ok (core.result.Result.Ok (), out)) ⦃ (status, out) => match status with
          | .Ok _ => InsertedRing r out x ∧ ¬ (r.len.val = 2^30 ∧ Separate (ringList r) x)
          | .Err e => e = CodecError.LimitExceeded ∧ out = r ∧ r.len.val = 2^30 ∧ Separate (ringList r) x ⦄ := by
    step with make_gap_spec r lo hi 1#usize hw ord last fits as ⟨v, gap⟩
    step with fill_gap r v lo hi m hw ord last gap as ⟨out, hh, ol, os, ob, ov⟩
    have len : v.len.val = r.len.val-(hi.val-lo.val)+1 := gap.len
    exact ⟨⟨hh, os, ob, by rw [ol]; omega, by rw [ol]; omega, by simpa only [ov] using can,
      by simpa only [ov] using member⟩, accepted⟩
  by_cases hit : lo < hi
  · simp only [hit, ↓reduceIte]
    have lt : lo.val < hi.val := by scalar_tac
    step with ring_at_list_spec r hw lo (by omega) as ⟨f, hf⟩
    step as ⟨j, hj⟩
    step with ring_at_list_spec r hw j (by omega) as ⟨z, hz⟩
    let m : order_range.ClockRange := {
      start := core.cmp.impls.OrdU64.min x.start f.start
      «end» := core.cmp.impls.OrdU64.max x.end z.end }
    have ms : m.start.val = min x.start.val f.start.val := by
      dsimp [m, core.cmp.impls.OrdU64.min]; split_ifs <;> scalar_tac
    have me : m.end.val = max x.end.val z.end.val := by
      dsimp [m, core.cmp.impls.OrdU64.max]; split_ifs <;> scalar_tac
    have ⟨can, mem⟩ := merged_window src lo.val hi.val x m hc valid lt hiBound before
      (firstEnd _ (by omega) (Nat.le_refl _)) (lastStart _ (by omega) (by omega) (by omega)) after
      (by simpa only [hf] using ms) (by simpa only [hz, hj] using me)
    apply write m can mem (by omega)
    intro ⟨_,sep⟩
    have alive : lo.val < (ringList r).length := by omega
    have apart := sep lo.val alive
    have left := firstEnd lo.val alive (Nat.le_refl _)
    have right := lastStart lo.val alive (Nat.le_refl _) lt
    omega
  · simp only [hit, ↓reduceIte]
    have eq : hi.val = lo.val := by scalar_tac
    by_cases full : UScalar.cast .Usize r.len = limit
    · simp only [full, ↓reduceIte, spec_ok]
      refine ⟨rfl, rfl, by scalar_tac, ?_⟩
      intro i live
      by_cases low : i < lo.val
      · exact Or.inl (before i live low)
      · exact Or.inr (after i live (by omega))
    · simp only [full, ↓reduceIte]
      have less : r.len.val < limit.val := by scalar_tac
      have ⟨can, mem⟩ := disjoint_window src lo.val x hc valid before (by simpa only [eq] using after)
      exact write x (by simpa only [eq] using can) (by simpa only [eq] using mem) (by omega) (by intro h; omega)

theorem ring_try_insert_spec {extra : Nat} (r : order_range.Ring) (x : order_range.ClockRange)
    (limit : Std.Usize) (hw : ringWF r extra) (hc : CanonicalList (ringList r))
    (valid : x.start.val < x.end.val) (bound : limit.val = 2^30) :
    order_range.Ring.try_insert r x limit ⦃ (status, out) => match status with
      | .Ok _ => InsertedRing r out x
      | .Err e => e = .LimitExceeded ∧ out = r ∧ r.len.val = 2^30 ⦄ := by
  apply spec_mono (ring_try_insert_exact r x limit hw hc valid bound)
  rintro ⟨s,w⟩ h
  cases s with
  | Ok u => exact h.1
  | Err e => exact ⟨h.1,h.2.1,h.2.2.1⟩


theorem is_empty_spec (r : order_range.OrderRange) (hw : storageWF r) :
    order_range.OrderRange.is_empty r ⦃ b => b = true ↔ toList r = [] ⦄ := by
  rcases r with ⟨a|ring⟩
  · obtain ⟨x, hx⟩ := single_val a
    unfold order_range.OrderRange.is_empty
    step as ⟨v, hv⟩
    have eq : v = x := by simpa [hx] using hv
    by_cases h : x.start.val < x.end.val
    · have empty : ¬v.start ≥ v.end := by subst v; scalar_tac
      simp [empty, toList, hx, h]
    · have empty : v.start ≥ v.end := by subst v; scalar_tac
      simp [empty, toList, hx, h]
  · have n := ringList_length ring hw
    have live := hw.2.2.1
    have positive : ringList ring ≠ [] := by intro e; simp [e] at n; omega
    simp [order_range.OrderRange.is_empty, toList, positive]

theorem as_slices_spec (r : order_range.OrderRange) (hw : storageWF r) :
    order_range.OrderRange.as_slices r ⦃ (a,b) => a.val ++ b.val = toList r ⦄ := by
  rcases r with ⟨a|ring⟩
  · obtain ⟨x, hx⟩ := single_val a
    unfold order_range.OrderRange.as_slices
    step as ⟨v,hv⟩
    have eq : v = x := by simpa [hx] using hv
    subst v
    split_ifs with h
    · have valid : x.start.val < x.end.val := by scalar_tac
      simp [toList, hx, valid, Array.to_slice, Std.Array.empty, lift, bind_ok]
    · have invalid : ¬ x.start.val < x.end.val := by scalar_tac
      simp [toList, hx, invalid, Std.Array.empty, Array.to_slice, lift, bind_ok]
  · exact ring_slices_spec ring hw


private theorem extend_slice_spec (v : alloc.vec.Vec order_range.ClockRange)
    (s : Slice order_range.ClockRange) (room : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice order_range.ClockRange.Insts.CoreCloneClone v s
      ⦃ out => out.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [room, ↓reduceDIte]
  apply spec_bind (@List.clone_spec _ order_range.ClockRange.Insts.CoreCloneClone.clone
    s.val (by intros; rfl))
  intro out h
  simp [spec_ok,h,alloc.vec.Vec.from,alloc.vec.Vec.val]

private theorem range_limit_fits_usize : 2^30 ≤ Usize.max := by scalar_tac

/-- Cloning a wrapped ring copies its logical sequence into a contiguous
    buffer, starting at index zero. -/
theorem ring_clone_spec (r : order_range.Ring) (hw : ringWF r) :
    order_range.Ring.Insts.CoreCloneClone.clone r ⦃ out =>
      ringWF out ∧ ringList out = ringList r ⦄ := by
  unfold order_range.Ring.Insts.CoreCloneClone.clone
  simp only [lift, bind_ok]
  let n := UScalar.cast .Usize r.len
  step with ring_slices_spec r hw as ⟨first, second, pieces⟩
  have hlen := ringList_length r hw
  have total : first.val.length + second.val.length = r.len.val := by
    simpa only [List.length_append] using (congrArg List.length pieces).trans hlen
  step with extend_slice_spec (alloc.vec.Vec.with_capacity order_range.ClockRange n) first
    (by simp [alloc.vec.Vec.with_capacity,alloc.vec.Vec.length]) as ⟨v1, hv1⟩
  have firstCopy : v1.val = first.val := by simpa [alloc.vec.Vec.with_capacity] using hv1
  have room : v1.length + second.length ≤ Usize.max := by
    change v1.val.length + second.val.length ≤ Usize.max
    rw [firstCopy,total]
    exact hw.2.1.trans (hw.2.2.2.trans range_limit_fits_usize)
  step with extend_slice_spec v1 second
    room as ⟨v,hv⟩
  have hv : v.val = ringList r := by simpa only [firstCopy,pieces] using hv
  unfold ringList at hlen
  have hnonempty := hw.2.2.1
  have hzero : (0#u32).val = 0 := by decide
  simp only [ringWF, ringList, hzero, OrderRangeRing.toList_initial, hv]
  exact ⟨⟨by omega, by omega, hw.2.2.1, by have := hw.2.1; have := hw.2.2.2; omega⟩,
    List.take_of_length_le (by omega)⟩

private theorem initial_ring (buf : alloc.vec.Vec order_range.ClockRange)
    (len : Std.Usize) (hm : 2 ≤ len.val) (hl : len.val ≤ buf.length)
    (hb : buf.length ≤ 2^30) :
    let out : order_range.OrderRange := ⟨.Many ⟨buf, 0#u32, UScalar.cast .U32 len⟩⟩
    storageWF out ∧ toList out = buf.val.take len.val := by
  have hc : UScalar.max UScalarTy.U32 = 2^32-1 := by
    rw [UScalar.max_UScalarTy_U32_eq]; simp [U32.max, U32.numBits]
  have castLen : (UScalar.cast .U32 len).val = len.val := by
    have h := UScalar.cast_inBounds_spec .U32 len (by rw [hc]; omega)
    simpa [lift] using h
  have zero : (0#u32).val = 0 := by decide
  simp only [storageWF, ringWF, toList, ringList, castLen, zero, OrderRangeRing.toList_initial]
  exact ⟨⟨by scalar_tac, hl, hm, hb⟩, True.intro⟩

/-- Encoding an already canonical prefix preserves its exact logical contents
    for every hint, including a hint larger than the backing allocation. -/
theorem from_prefix_spec (ranges : alloc.vec.Vec order_range.ClockRange)
    (len hint : Std.Usize) (hl : len.val ≤ ranges.length) (hc : len.val ≤ 2^30)
    (hcan : CanonicalList (ranges.val.take len.val)) :
    order_range.OrderRange.from_prefix ranges len hint ⦃ out =>
      Canonical out ∧ toList out = ranges.val.take len.val ⦄ := by
  unfold order_range.OrderRange.from_prefix
  split
  · rename_i he
    refine spec_mono new_spec ?_
    intro out ⟨hCanon, hz, _⟩
    exact ⟨hCanon, by simpa [he] using List.length_eq_zero_iff.mp hz⟩
  · rename_i he
    have hr : 0 < ranges.val.length := by scalar_tac
    step as ⟨x, hx⟩
    have htake : ranges.val.take len.val = [x] := by
      rw [he, show 1 = 0+1 by decide, List.take_succ_eq_append_getElem hr]
      simp [hx]
    have hvalid : x.start.val < x.end.val := by
      rw [htake] at hcan
      exact hcan.1 0 (by simp)
    unfold order_range.OrderRange.from_range
    have h : x.start < x.end := by scalar_tac
    simp [h, hvalid, htake, Canonical, storageWF, toList, CanonicalList, Array.make, spec_ok]
    omega
  · have hmany : 2 ≤ len.val := by
      have hn0 : len.val ≠ 0 := by assumption
      have hn1 : len.val ≠ 1 := by assumption
      omega
    step with max_ranges_spec as ⟨cap, hcap⟩
    have hlimit : len ≤ cap := by scalar_tac
    simp only [massert, hlimit, ↓reduceIte, lift, bind_ok]
    let budget := core.cmp.impls.OrdUsize.min hint cap
    have hbudget : budget.val ≤ 2^30 := by
      dsimp [budget, core.cmp.impls.OrdUsize.min]
      split <;> scalar_tac
    by_cases hlarge : alloc.vec.Vec.len ranges > cap
    · simp only [hlarge, ↓reduceIte]
      step with copy_prefix_spec ranges len hl as ⟨v, hv⟩
      have hvlen : v.length = len.val := by simp [alloc.vec.Vec.length, hv, Nat.min_eq_left hl]
      step with budget_slot_spec v len budget (by omega) (by omega) hbudget as
        ⟨out, ho, hb, he⟩
      obtain ⟨hw, ht⟩ := initial_ring out len hmany ho hb
      rw [hv, List.take_take, Nat.min_self] at he
      exact ⟨⟨hw, by rwa [ht, he]⟩, ht.trans he⟩
    · simp only [hlarge, ↓reduceIte]
      step with budget_slot_spec ranges len budget hl (by scalar_tac) hbudget as
        ⟨out, ho, hb, he⟩
      obtain ⟨hw, ht⟩ := initial_ring out len hmany ho hb
      exact ⟨⟨hw, by rwa [ht, he]⟩, ht.trans he⟩

/-- Checked construction preserves every interval and its position for any
    capacity hint when the input satisfies the public ordering contract. -/
theorem from_sorted_disjoint_with_capacity_spec (ranges : alloc.vec.Vec order_range.ClockRange)
    (hint : Std.Usize) (hc : CanonicalList ranges.val) (hl : ranges.length ≤ 2^30) :
    order_range.OrderRange.from_sorted_disjoint_with_capacity ranges hint ⦃ out =>
      Canonical out ∧ toList out = ranges.val ⦄ := by
  unfold order_range.OrderRange.from_sorted_disjoint_with_capacity
  step with is_canonical_spec (alloc.vec.Vec.deref ranges) as ⟨b, hb⟩
  have accepted : b = true := hb.mpr (by simpa [alloc.vec.Vec.deref] using hc)
  simp only [accepted, massert, ↓reduceIte, bind_ok]
  have hlen : (alloc.vec.Vec.len ranges).val = ranges.val.length := by scalar_tac
  have htake : ranges.val.take (alloc.vec.Vec.len ranges).val = ranges.val := by simp [hlen]
  simpa only [htake] using from_prefix_spec ranges (alloc.vec.Vec.len ranges) hint
    (by scalar_tac) (by scalar_tac) (htake.symm ▸ hc)

theorem from_sorted_disjoint_spec (ranges : alloc.vec.Vec order_range.ClockRange)
    (hc : CanonicalList ranges.val) (hl : ranges.length ≤ 2^30) :
    order_range.OrderRange.from_sorted_disjoint ranges ⦃ out =>
      Canonical out ∧ toList out = ranges.val ⦄ := by
  exact from_sorted_disjoint_with_capacity_spec ranges 0#usize hc hl

theorem canonicalize_canonical_spec (ranges : alloc.vec.Vec order_range.ClockRange)
    (hc : CanonicalList ranges.val) :
    order_range.canonicalize ranges ⦃ (len, out) => len.val = ranges.length ∧ out = ranges ⦄ := by
  unfold order_range.canonicalize
  step with is_canonical_spec (alloc.vec.Vec.deref ranges) as ⟨b, hb⟩
  have accepted : b = true := hb.mpr (by simpa [alloc.vec.Vec.deref] using hc)
  simp [accepted, spec_ok]

def InsertPost (self : order_range.OrderRange) (start finish : Std.U64)
    (result : core.result.Result Unit CodecError × order_range.OrderRange) : Prop :=
  Canonical result.2 ∧ (toList result.2).length ≤ (toList self).length + 1 ∧
    match result.1 with
    | .Ok _ => ∀ c, inRanges result.2 c ↔ inRanges self c ∨ start.val ≤ c.val ∧ c.val < finish.val
    | .Err e => e = CodecError.LimitExceeded ∧ result.2 = self ∧ (toList self).length = 2^30

theorem single_valid_list (a : Array order_range.ClockRange 1#usize) (x : order_range.ClockRange)
    (hx : a.val = [x]) (valid : x.start.val < x.end.val) :
    Canonical ⟨.Single a⟩ ∧ toList ⟨.Single a⟩ = [x] := by
  simp only [Canonical, storageWF, toList, hx, List.filter_cons, valid, decide_true, ↓reduceIte,
    List.filter_nil, canonical_pairwise]
  simp [valid]

private theorem two_items (a b : order_range.ClockRange) (w : alloc.vec.Vec order_range.ClockRange)
    (av : a.start.val < a.end.val) (bv : b.start.val < b.end.val) (sep : a.end.val < b.start.val)
    (vals : w.val = [a,b]) :
    let out : order_range.OrderRange := ⟨.Many ⟨w, 0#u32, 2#u32⟩⟩
    Canonical out ∧ toList out = [a,b] := by
  have zero : (0#u32).val = 0 := by decide
  have two : (2#u32).val = 2 := by decide
  simp [Canonical, storageWF, ringWF, toList, ringList, vals, zero, two, OrderRangeRing.toList_initial,
    canonical_pairwise, BeforeRange, av, bv, sep]

theorem try_insert_semantics (self : order_range.OrderRange) (start finish : Std.U64) (hc : Canonical self) :
    order_range.OrderRange.try_insert self start finish ⦃ (status, out) =>
      Canonical out ∧ (toList out).length ≤ (toList self).length + 1 ∧
        match status with
        | .Ok _ => ∀ c, inRanges out c ↔ inRanges self c ∨ start.val ≤ c.val ∧ c.val < finish.val
        | .Err e => e = CodecError.LimitExceeded ∧ out = self ∧ (toList self).length = 2^30 ⦄ := by
  unfold order_range.OrderRange.try_insert
  by_cases empty : start ≥ finish
  · simp only [empty, ↓reduceIte, spec_ok]
    refine ⟨hc, Nat.le_succ _, fun c => ?_⟩
    have le : finish.val ≤ start.val := by scalar_tac
    grind
  simp only [empty, ↓reduceIte]
  have valid : start.val < finish.val := by scalar_tac
  let x : order_range.ClockRange := ⟨start, finish⟩
  rcases self with ⟨a | ring⟩
  · obtain ⟨old, arr⟩ := single_val a
    step as ⟨v, hv⟩
    have elem : a.val[0] = old := by simp [arr]
    have eq : v = old := by simpa [arr] using hv
    subst v
    simp only [elem]
    by_cases ev : old.start ≥ old.end
    · simp only [ev, ↓reduceIte]
      step as ⟨out, upd⟩
      have vals : out.val = [x] := by simp [upd, Array.set_val_eq, arr, x]
      have ⟨can, view⟩ := single_valid_list out x vals valid
      have oldEmpty : ¬old.start.val < old.end.val := by scalar_tac
      simp [can, inRanges, inRangesList_iff_mem, toList, vals, arr, oldEmpty, x, valid]
    · have ov : old.start.val < old.end.val := by scalar_tac
      have oldView := (single_valid_list a old arr ov).2
      simp only [ev, ↓reduceIte, lift, bind_ok]
      have disjoint (l r : order_range.ClockRange) (lv : l.start.val < l.end.val)
          (rv : r.start.val < r.end.val) (separated : l.end.val < r.start.val)
          (items : [l,r].Perm [old,x]) :
          (do
            let v ← alloc.vec.Vec.push (alloc.vec.Vec.with_capacity order_range.ClockRange 2#usize) l
            let w ← alloc.vec.Vec.push v r
            ok (core.result.Result.Ok (), (⟨.Many ⟨w, 0#u32, 2#u32⟩⟩ : order_range.OrderRange))) ⦃
            result => InsertPost ⟨.Single a⟩ start finish result ⦄ := by
        have initLen : (alloc.vec.Vec.with_capacity order_range.ClockRange 2#usize).length = 0 := rfl
        step as ⟨v, hv⟩
        have vLen : v.length = 1 := by simp [alloc.vec.Vec.length, hv, alloc.vec.Vec.with_capacity]
        step as ⟨w, hw⟩
        have vals : w.val = [l,r] := by simp [hw, hv, alloc.vec.Vec.with_capacity]
        have ⟨can, view⟩ := two_items l r w lv rv separated vals
        refine ⟨can, by simp [view, oldView], fun c => ?_⟩
        simp only [inRanges, view, oldView]
        have eq : inRangesList [l,r] c ↔ inRangesList [old,x] c := by
          simp only [inRangesList_iff_mem, items.mem_iff]
        exact eq.trans (by simpa only [List.cons_append, List.nil_append, inRangesList_singleton, x] using inRangesList_append [old] [x] c)
      by_cases ab : start ≤ old.end
      · simp only [ab, ↓reduceIte]
        by_cases ba : old.start ≤ finish
        · simp only [ba, ↓reduceIte]
          step as ⟨out, upd⟩
          let merged : order_range.ClockRange := ⟨core.cmp.impls.OrdU64.min old.start start,
            core.cmp.impls.OrdU64.max old.end finish⟩
          have ms : merged.start.val = min old.start.val start.val := by dsimp [merged, core.cmp.impls.OrdU64.min]; split <;> scalar_tac
          have me : merged.end.val = max old.end.val finish.val := by dsimp [merged, core.cmp.impls.OrdU64.max]; split <;> scalar_tac
          have vals : out.val = [merged] := by simp [upd, Array.set_val_eq, arr, merged]
          have ⟨can, view⟩ := single_valid_list out merged vals (by omega)
          refine ⟨can, by simp [oldView, view], fun c => ?_⟩
          simp only [inRanges, view, oldView, inRangesList_singleton]
          have h1 : start.val ≤ old.end.val := by scalar_tac
          have h2 : old.start.val ≤ finish.val := by scalar_tac
          omega
        · have first : start < old.start := by scalar_tac
          simp only [ba, first, ↓reduceIte]
          exact disjoint x old valid ov (by change finish.val < old.start.val; scalar_tac) (List.Perm.swap _ _ _)
      · have first : ¬ start < old.start := by scalar_tac
        simp only [ab, first, ↓reduceIte]
        exact disjoint old x ov valid (by change old.end.val < start.val; scalar_tac) (List.Perm.refl _)
  · have wf : ringWF ring := hc.1
    have length := ringList_length ring wf
    simp only
    step with max_ranges_spec as ⟨limit, hl⟩
    step with ring_try_insert_spec ring x limit wf hc.2 valid hl as ⟨status, out, h⟩
    cases status with
    | Err err =>
      obtain ⟨he, rfl, full⟩ := h
      simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        bind_ok, spec_ok, hc, he, toList, length, full]
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have outLen : (ringList out).length = out.len.val :=
        OrderRangeRing.toList_length _ (Nat.le_of_lt h.head) h.fits
      by_cases one : out.len = 1#u32
      · simp only [one, ↓reduceIte]
        have n : out.len.val = 1 := by rw [one]; decide
        step with read_slot out 0#usize h.head (by have := h.fits; scalar_tac) as ⟨v, hv⟩
        have hit : some v = (ringList out)[0]? := hv.trans (slot_active out h.head h.fits (by scalar_tac))
        have view : ringList out = [v] := by
          cases e : ringList out with
          | nil => simp [e] at hit
          | cons a l =>
            have eq : v = a := by simpa [e] using hit
            have len0 : l.length = 0 := by simp [e] at outLen; omega
            simp [eq, List.length_eq_zero_iff.mp len0]
        have vv := h.canonical.1 0 (by simp [view])
        have vv' : v.start.val < v.end.val := by simpa [view] using vv
        have ⟨can, singleton⟩ := single_valid_list (Array.make 1#usize [v]) v rfl vv'
        refine ⟨can, ?_, fun c => ?_⟩
        · rw [singleton]
          change 1 ≤ (ringList ring).length + 1
          omega
        · simp only [inRanges, singleton]
          simpa only [toList, view, x] using h.mem c
      · simp only [one, ↓reduceIte, spec_ok]
        have many : 2 ≤ out.len.val := by have := h.positive; scalar_tac
        exact ⟨⟨⟨h.head, h.fits, many, h.bound⟩, h.canonical⟩,
          by simpa only [toList, outLen, length] using h.count, h.mem⟩

/-- Exactly the nonempty, strictly separated insertion into a full client
    exceeds the representation limit. -/
def InsertExceeds (self : order_range.OrderRange) (start finish : Std.U64) : Prop :=
  start.val < finish.val ∧ (toList self).length = 2^30 ∧ Separate (toList self) ⟨start,finish⟩

theorem try_insert_spec (self : order_range.OrderRange) (start finish : Std.U64) (hc : Canonical self) :
    order_range.OrderRange.try_insert self start finish ⦃ (status, out) =>
      InsertPost self start finish (status,out) ∧
      (status = .Err .LimitExceeded ↔ InsertExceeds self start finish) ⦄ := by
  apply spec_and (try_insert_semantics self start finish hc)
  rcases self with ⟨a|ring⟩
  · apply spec_mono (try_insert_semantics ⟨.Single a⟩ start finish hc)
    rintro ⟨s,w⟩ ⟨_,_,result⟩
    obtain ⟨v,eq⟩ := single_val a
    have size : (toList ⟨.Single a⟩).length ≤ 1 := by
      simpa only [toList,eq,List.length_cons,List.length_nil] using
        (List.length_filter_le (fun v : order_range.ClockRange => decide (v.start.val < v.end.val)) [v])
    have no : ¬ InsertExceeds ⟨.Single a⟩ start finish := by intro h; have := h.2.1; omega
    cases s with
    | Ok _ => simp [no]
    | Err e => obtain ⟨_,_,full⟩ := result; omega
  · unfold order_range.OrderRange.try_insert
    by_cases empty : start ≥ finish
    · have no : ¬ start.val < finish.val := by scalar_tac
      simp [empty,InsertExceeds,no,spec_ok]
    simp only [empty,↓reduceIte]
    have wf : ringWF ring := hc.1
    have valid : start.val < finish.val := by scalar_tac
    have count := ringList_length ring wf
    step with max_ranges_spec as ⟨cap,bound⟩
    step with ring_try_insert_exact ring ⟨start,finish⟩ cap wf hc.2 valid bound as ⟨s,w,h⟩
    cases s with
    | Err e =>
      obtain ⟨he,_,full,sep⟩ := h
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,he,
        bind_ok,spec_ok,InsertExceeds,toList,valid,count,full,sep]
    | Ok u =>
      have no : ¬ InsertExceeds ⟨.Many ring⟩ start finish := by
        intro h'
        exact h.2 ⟨by simpa only [toList,count] using h'.2.1,h'.2.2⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      by_cases single : w.len = 1#u32
      · simp only [single,↓reduceIte]
        step with ring_at_physical_spec w 0#usize h.1.head (by have := h.1.fits; scalar_tac) as ⟨v,_⟩
        simp [no]
      · simp [single,no,spec_ok]

theorem insert_spec (r : order_range.OrderRange) (start finish : Std.U64) (hc : Canonical r)
    (room : (toList r).length < 2^30) :
    order_range.OrderRange.insert r start finish ⦃ out => Canonical out ∧
      (toList out).length ≤ (toList r).length + 1 ∧ ∀ c,
      inRanges out c ↔ inRanges r c ∨ start.val ≤ c.val ∧ c.val < finish.val ⦄ := by
  unfold order_range.OrderRange.insert
  step with try_insert_semantics r start finish hc as ⟨status, out, can, count, result⟩
  cases status with
  | Err _ => obtain ⟨_, _, full⟩ := result; omega
  | Ok _ => simpa [core.result.Result.is_ok, bind_ok, massert, spec_ok] using And.intro can (And.intro count result)


private theorem range_ne_spec (a b : order_range.ClockRange) :
    core.cmp.PartialEq.ne.trait_default order_range.ClockRange.Insts.CoreCmpPartialEqClockRange a b
      ⦃ different => different = true ↔ a ≠ b ⦄ := by
  cases a with | mk lo hi =>
    cases b with | mk lo' hi' =>
      by_cases l : lo = lo' <;> by_cases h : hi = hi' <;>
        simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
          order_range.ClockRange.Insts.CoreCmpPartialEqClockRange.eq,l,h,spec_ok]

private theorem equal_run_spec (a b : Slice order_range.ClockRange) :
    order_range.equal_run a b ⦃ same => same = true ↔ a.val = b.val ⦄ := by
  unfold order_range.equal_run
  by_cases sizes : a.length = b.length
  · have len : a.len = b.len := UScalar.eq_of_val_eq (by simpa using sizes)
    simp [len]
    unfold order_range.equal_run_loop
    let inv (i : Usize) := i.val ≤ a.length ∧
      ∀ k, k < i.val → a.val[k]? = b.val[k]?
    refine loop.spec_decr_nat (fun i => a.length - i.val) inv _ _ _ ?_ ?_
    · intro i ⟨bound, prior⟩
      unfold order_range.equal_run_loop.body
      by_cases live : i < a.len
      · simp only [live,↓reduceIte]
        have ia : i.val < a.val.length := by scalar_tac
        have ib : i.val < b.val.length := by scalar_tac
        step as ⟨x,hx⟩
        step as ⟨y,hy⟩
        step with range_ne_spec x y as ⟨d,hd⟩
        cases d with
        | true =>
          have ne := hd.mp rfl
          simp only [↓reduceIte,spec_ok,Bool.false_eq_true,false_iff]
          intro eq
          have lookup := congrArg (fun l : List order_range.ClockRange => l[i.val]?) eq
          rw [List.getElem?_eq_getElem ia,List.getElem?_eq_getElem ib] at lookup
          exact ne (hx.trans ((Option.some.inj lookup).trans hy.symm))
        | false =>
          have equal : x = y := by by_contra h; cases hd.mpr h
          simp only [Bool.false_eq_true,↓reduceIte]
          step as ⟨j,hj⟩
          refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
          intro k hk
          by_cases atCurrent : k = i.val
          · subst k
            simp [List.getElem?_eq_getElem ia,List.getElem?_eq_getElem ib,←hx,←hy,equal]
          · apply prior k (by omega)
      · simp only [live,↓reduceIte,spec_ok,true_iff]
        apply List.ext_getElem
        · exact sizes
        · intro k hka hkb
          have eq := prior k (by scalar_tac)
          simpa [List.getElem?_eq_getElem hka,List.getElem?_eq_getElem hkb] using eq
    · simp [inv]
  · have len : a.len ≠ b.len := by intro h; apply sizes; exact congrArg UScalar.val h
    have diff : a.val ≠ b.val := fun h => sizes (congrArg List.length h)
    simp [len,diff,spec_ok]

private theorem same_prefix_iff {α : Type} {a b c d : List α} (eq : a.length = c.length) :
    a ++ b = c ++ d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    constructor
    · calc
        a = (a ++ b).take a.length := by simp
        _ = (c ++ d).take c.length := by rw [h,eq]
        _ = c := by simp
    · calc
        b = (a ++ b).drop a.length := by simp
        _ = (c ++ d).drop c.length := by rw [h,eq]
        _ = d := by simp
  · rintro ⟨rfl,rfl⟩
    rfl

private theorem equal_three_pieces {α : Type} (a tail b rest : List α)
    (first : a.length ≤ b.length) (total : a.length + tail.length = b.length + rest.length) :
    a ++ tail = b ++ rest ↔
    a = b.take a.length ∧ tail.take (b.length - a.length) = b.drop a.length ∧
      tail.drop (b.length - a.length) = rest := by
  let k := b.length - a.length
  have hk : k ≤ tail.length := by dsimp [k]; omega
  have ha : a.length = (b.take a.length).length := by simp [Nat.min_eq_left first]
  have hb : (tail.take k).length = (b.drop a.length).length := by simp [k,Nat.min_eq_left hk]
  calc
    a ++ tail = b ++ rest ↔
        a ++ (tail.take k ++ tail.drop k) = b.take a.length ++ (b.drop a.length ++ rest) := by
          rw [List.take_append_drop,←List.append_assoc,List.take_append_drop]
    _ ↔ _ := by rw [same_prefix_iff ha,same_prefix_iff hb]

private theorem equal_runs_spec (a tail b rest : Slice order_range.ClockRange)
    (first : a.length ≤ b.length) (total : a.length + tail.length = b.length + rest.length) :
    order_range.equal_runs a tail b rest ⦃ same => same = true ↔ a.val ++ tail.val = b.val ++ rest.val ⦄ := by
  have lengths : a.len.val = a.length := by scalar_tac
  have parts := equal_three_pieces a.val tail.val b.val rest.val first total
  unfold order_range.equal_runs
  step as ⟨k,hk⟩
  have kv : k.val = b.length - a.length := by scalar_tac
  have fits : k.val ≤ tail.length := by omega
  step as ⟨front,hfront,_⟩
  step with equal_run_spec a front as ⟨x,hx⟩
  have one : x = true ↔ a.val = b.val.take a.length := by simpa [hfront,List.slice,lengths] using hx
  cases x with
  | false => simp [parts,←one,spec_ok]
  | true =>
    simp only [↓reduceIte]
    step as ⟨left,hleft,_⟩
    step as ⟨right,hright,_⟩
    step with equal_run_spec left right as ⟨y,hy⟩
    have two : y = true ↔ tail.val.take k.val = b.val.drop a.length := by
      simpa [hleft,hright,List.slice,lengths] using hy
    cases y with
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte,spec_ok,false_iff]
      intro eq
      have middle := (parts.mp eq).2.1
      exact Bool.noConfusion (two.mpr (by simpa only [kv] using middle))
    | true =>
      simp only [↓reduceIte]
      step as ⟨last,hlast,_⟩
      step with equal_run_spec last rest as ⟨z,hz⟩
      have lastEq : z = true ↔ tail.val.drop k.val = rest.val := by
        simpa [hlast,List.slice] using hz
      constructor
      · intro same
        apply parts.mpr
        exact ⟨one.mp rfl, by simpa only [kv] using two.mp rfl,
          by simpa only [kv] using lastEq.mp same⟩
      · intro eq
        apply lastEq.mpr
        simpa only [kv] using (parts.mp eq).2.2

theorem partial_eq_spec (a b : order_range.OrderRange) (ha : storageWF a) (hb : storageWF b) :
    order_range.OrderRange.Insts.CoreCmpPartialEqOrderRange.eq a b
        ⦃ same => same = true ↔ toList a = toList b ⦄ := by
  unfold order_range.OrderRange.Insts.CoreCmpPartialEqOrderRange.eq
  step with len_spec a ha as ⟨n,hn⟩
  step with len_spec b hb as ⟨m,hm⟩
  by_cases lengths : n = m
  · subst m
    simp
    step with as_slices_spec a ha as ⟨af,at',va⟩
    step with as_slices_spec b hb as ⟨bf,bt,vb⟩
    have x := congrArg List.length va
    have y := congrArg List.length vb
    simp only [List.length_append] at x y
    have total : af.length + at'.length = bf.length + bt.length := x.trans (hn.symm.trans (hm.trans y.symm))
    split_ifs with first
    · apply spec_mono (equal_runs_spec af at' bf bt (by scalar_tac) total)
      intro result h
      simpa only [va,vb] using h
    · apply spec_mono (equal_runs_spec bf bt af at' (by scalar_tac) total.symm)
      intro result h
      rw [va,vb] at h
      exact h.trans eq_comm
  · have diff : toList a ≠ toList b := fun eq =>
      lengths (UScalar.eq_of_val_eq (hn.trans ((congrArg List.length eq).trans hm.symm)))
    simp [lengths,diff,spec_ok]

end YoctoCore.Properties.OrderRange
