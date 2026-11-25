import Std

set_option autoImplicit false

namespace YoctoCore.Properties.OrderRangeHeap

theorem drop_set_before {α : Type} (l : List α) (i cut : Nat) (x : α) (hi : i < cut) :
    (l.set i x).drop cut = l.drop cut := by
  induction l generalizing i cut with
  | nil => simp
  | cons a l ih =>
    cases cut with
    | zero => omega
    | succ cut =>
      cases i with
      | zero => rfl
      | succ i => exact ih i cut (by omega)

/-- Moving the child into the current hole moves the hole to the child's slot.
Filling that hole with the held value represents the same multiset throughout. -/
theorem move_hole_perm {α : Type} (l : List α) (i j : Nat)
    (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j) (held : α) :
    ((l.set i l[j]).set j held).Perm (l.set i held) := by
  classical
  apply List.perm_iff_count.mpr
  intro x
  have hi' : (if l[i] == x then 1 else 0) ≤ l.count x := by
    split
    · rename_i e
      exact List.one_le_count_iff.mpr ((beq_iff_eq.mp e) ▸ List.getElem_mem hi)
    · omega
  have hj' : (if l[j] == x then 1 else 0) ≤ l.count x := by
    split
    · rename_i e
      exact List.one_le_count_iff.mpr ((beq_iff_eq.mp e) ▸ List.getElem_mem hj)
    · omega
  have hb : j < (l.set i l[j]).length := by simpa using hj
  rw [List.count_set hb, List.getElem_set_ne hne, List.count_set hi, List.count_set hi]
  split <;> split <;> split <;> omega

theorem swap_perm {α : Type} (l : List α) (i j : Nat)
    (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j) :
    ((l.set i l[j]).set j l[i]).Perm l := by
  have stored := move_hole_perm l i j hi hj hne l[i]
  have same : l.set i l[i] = l := by
    apply List.ext_getElem
    · simp
    · intro k hk hk'
      by_cases h : k = i
      · subst k
        simp
      · simp
  rwa [same] at stored

/-- All parents at or after `first` dominate their children in the active
    heap prefix. Heap construction decreases `first` to zero. -/
def HeapFrom {α : Type} (le : α → α → Prop) (l : List α) (first stop : Nat) : Prop :=
  ∀ (child : Nat) (hc : child < stop) (hl : child < l.length),
    0 < child → first ≤ (child - 1) / 2 →
      le (l[child]) (l[(child - 1) / 2]'(by omega))

theorem leaves_heap {α : Type} (le : α → α → Prop) (l : List α) (stop : Nat) :
    HeapFrom le l (stop / 2) stop := by
  intro child hc hl hp hf
  omega

theorem root_dominates {α : Type} {le : α → α → Prop}
    (refl : ∀ x, le x x) (trans : ∀ {x y z}, le x y → le y z → le x z)
    (l : List α) {stop : Nat} (hs : stop ≤ l.length) (heap : HeapFrom le l 0 stop)
    (i : Nat) (hi : i < stop) :
    le (l[i]'(by omega)) (l[0]'(by omega)) := by
  by_cases hz : i = 0
  · subst i
    apply refl
  · have hp : (i - 1) / 2 < i := by omega
    exact trans (heap i hi (by omega) (by omega) (by omega))
      (root_dominates refl trans l hs heap ((i - 1) / 2) (by omega))
termination_by i
decreasing_by omega

private abbrev parent (child : Nat) := (child - 1) / 2

/-- During sift-down only edges out of the hole may fail. Its children can
    already move up one level without exceeding the parent above the hole. -/
structure SiftHole {α : Type} (le : α → α → Prop) (atIndex : Nat → α)
    (first stop hole : Nat) : Prop where
  edges : ∀ j, 0 < j → j < stop → first ≤ parent j → parent j ≠ hole →
    le (atIndex j) (atIndex (parent j))
  canLift : ∀ j, 0 < j → j < stop → parent j = hole → 0 < hole → first ≤ parent hole →
    le (atIndex j) (atIndex (parent hole))

def exchange {α : Type} (atIndex : Nat → α) (i j k : Nat) : α :=
  if k = i then atIndex j else if k = j then atIndex i else atIndex k

def filled {α : Type} (l : List α) (hole : Nat) (held : α) (k : Nat) : α :=
  if k = hole then held else l[k]?.getD held

theorem filled_at_root {α : Type} (l : List α) (root : Nat) (hr : root < l.length) :
    filled l root l[root] = fun j => l[j]?.getD l[root] := by
  funext j
  by_cases h : j = root
  · subst j; simp [filled, List.getElem?_eq_getElem hr]
  · simp [filled, h]

theorem filled_write {α : Type} (l : List α) (hole : Nat) (hh : hole < l.length) (held : α) :
    (fun j => (l.set hole held)[j]?.getD held) = filled l hole held := by
  funext j
  by_cases h : j = hole
  · subst j; simp [filled, hh]
  · simp [filled, h, Ne.symm h]

theorem move_hole_values {α : Type} (l : List α) (hole child : Nat)
    (hh : hole < l.length) (hc : child < l.length) (hd : hole ≠ child) (held : α) :
    filled (l.set hole l[child]) child held = exchange (filled l hole held) hole child := by
  funext k
  by_cases h : k = hole
  · subst k
    simp [exchange, filled, hd, Ne.symm hd, hh, hc]
  · by_cases eq : k = child
    · subst k; simp [exchange, filled, h]
    · simp [exchange, filled, h, eq, Ne.symm h]

theorem start_sift {α : Type} {le : α → α → Prop} (l : List α) (fallback : α)
    {first stop : Nat} (hs : stop ≤ l.length) (heap : HeapFrom le l (first + 1) stop) :
    SiftHole le (fun j => l[j]?.getD fallback) first stop first := by
  constructor
  · intro j hj hb hf hn
    have h1 : j < l.length := by omega
    have h2 : parent j < l.length := by unfold parent; omega
    simpa only [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some]
      using heap j hb h1 hj (show first + 1 ≤ parent j by omega)
  · intro j hj hb hep hf hparent
    unfold parent at hparent
    omega

/-- Moving the larger child to the hole transfers the sole possible heap
    violation to the child. -/
theorem promote_child {α : Type} {le : α → α → Prop} {f : Nat → α}
    {first stop hole chosen : Nat} (inv : SiftHole le f first stop hole)
    (childPos : 0 < chosen) (childBound : chosen < stop) (childOf : parent chosen = hole)
    (aboveHeld : le (f hole) (f chosen))
    (largest : ∀ j, 0 < j → j < stop → parent j = hole → le (f j) (f chosen)) :
    SiftHole le (exchange f hole chosen) first stop chosen := by
  have hlt : hole < chosen := by unfold parent at childOf; omega
  constructor
  · intro j hj hb hf hp
    by_cases jh : j = hole
    · subst j
      have hparent : parent hole < hole := by unfold parent; omega
      have hp1 : parent hole ≠ hole := by omega
      simpa [exchange, hp1, hp] using inv.canLift chosen childPos childBound childOf hj hf
    · by_cases jc : j = chosen
      · subst j
        simpa [exchange, childOf, jh] using aboveHeld
      · by_cases ph : parent j = hole
        · simpa [exchange, jh, jc, ph] using largest j hj hb ph
        · simpa [exchange, jh, jc, ph, hp] using inv.edges j hj hb hf ph
  · intro j hj hb hjp _ hfirst
    have jgt : chosen < j := by unfold parent at hjp; omega
    rw [childOf] at hfirst
    have hneed : first ≤ parent j := by omega
    have old := inv.edges j hj hb hneed (by omega)
    have jh : j ≠ hole := by omega
    have jc : j ≠ chosen := by omega
    simpa [exchange, jh, jc, childOf, hjp] using old

theorem finish_sift {α : Type} {le : α → α → Prop} {f : Nat → α}
    {first stop hole : Nat} (inv : SiftHole le f first stop hole)
    (fits : ∀ j, 0 < j → j < stop → parent j = hole → le (f j) (f hole)) :
    ∀ j, 0 < j → j < stop → first ≤ parent j → le (f j) (f (parent j)) := by
  intro j hj hb hf
  by_cases h : parent j = hole
  · simpa [h] using fits j hj hb h
  · exact inv.edges j hj hb hf h

theorem finish_sift_list {α : Type} {le : α → α → Prop} (l : List α)
    (held : α) {first stop hole : Nat} (hh : hole < l.length)
    (inv : SiftHole le (filled l hole held) first stop hole)
    (fits : ∀ j, 0 < j → j < stop → parent j = hole →
      le (filled l hole held j) (filled l hole held hole)) :
    HeapFrom le (l.set hole held) first stop := by
  intro j hb hj hp hf
  have h := finish_sift inv fits j hp hb hf
  rw [← filled_write l hole hh held] at h
  have hp' : parent j < (l.set hole held).length := by unfold parent; omega
  simpa only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hp', Option.getD_some] using h

/-- Each element in the sorted suffix dominates the entire prefix before it.
    When at most one heap element remains, this covers every ordered pair. -/
def DrainOrder {α : Type} (le : α → α → Prop) (l : List α) (heapEnd stop : Nat) : Prop :=
  ∀ j, heapEnd ≤ j → j < stop → ∀ hj : j < l.length,
    ∀ x ∈ l.take j, le x l[j]

theorem take_perm {α : Type} {before after : List α} {k : Nat}
    (p : after.Perm before) (tail : after.drop k = before.drop k) :
    (after.take k).Perm (before.take k) := by
  classical
  apply List.perm_iff_count.mpr
  intro x
  have h := (List.perm_iff_count.mp p) x
  have ha := congrArg (List.count x) (List.take_append_drop k after)
  have hb := congrArg (List.count x) (List.take_append_drop k before)
  simp only [List.count_append, tail] at ha hb
  omega

theorem drain_frame {α : Type} {le : α → α → Prop} {before after : List α} {k stop : Nat}
    (p : after.Perm before) (frame : after.drop k = before.drop k)
    (ord : DrainOrder le before k stop) : DrainOrder le after k stop := by
  intro j hkj hj hja x hx
  have hjb : j < before.length := p.length_eq ▸ hja
  have shift := congrArg (List.drop (j-k)) frame
  have eq : k + (j-k) = j := by omega
  simp only [List.drop_drop, eq] at shift
  have head := congrArg List.head? shift
  simp only [List.head?_drop, List.getElem?_eq_getElem hja, List.getElem?_eq_getElem hjb,
    Option.some.injEq] at head
  rw [head]
  exact ord j hkj hj hjb x ((take_perm p shift).mem_iff.mp hx)

/-- Moving the root to the last heap slot extends the sorted suffix by one.
    The only potentially violated edges now leave the new root. -/
theorem pop_root {α : Type} {le : α → α → Prop}
    (refl : ∀ x, le x x) (trans : ∀ {x y z}, le x y → le y z → le x z)
    (l : List α) (last stop : Nat) (hl : 0 < last) (hb : last < l.length)
    (heap : HeapFrom le l 0 (last+1)) (ord : DrainOrder le l (last+1) stop) :
    let out := (l.set last l[0]).set 0 l[last]
    HeapFrom le out 1 last ∧ DrainOrder le out last stop := by
  let out := (l.set last l[0]).set 0 l[last]
  have hlen : out.length = l.length := by simp [out]
  have perm : out.Perm l := swap_perm l last 0 hb (by omega) (by omega)
  have frame : out.drop (last+1) = l.drop (last+1) := by
    unfold out
    rw [drop_set_before _ _ _ _ (by omega), drop_set_before _ _ _ _ (by omega)]
  constructor
  · intro j hj hjl hn hp
    have p : parent j < last := by unfold parent; omega
    have h := heap j (by omega) (by omega) hn (by omega)
    have h1 : last ≠ j := by omega
    have h2 : 0 ≠ j := by omega
    have h3 : last ≠ (j-1)/2 := by omega
    have h4 : 0 ≠ (j-1)/2 := by omega
    simpa only [List.getElem_set_ne h1, List.getElem_set_ne h2, List.getElem_set_ne h3,
      List.getElem_set_ne h4] using h
  · intro j hlow hj hjl x hx
    by_cases same : j = last
    · subst j
      have larger : x ∈ out.take (last+1) := by
        have eq := List.take_succ_eq_append_getElem (show last < out.length by omega)
        rw [eq]
        exact List.mem_append_left _ hx
      have member := (take_perm perm frame).mem_iff.mp larger
      obtain ⟨i, hi, hv⟩ := List.mem_iff_getElem.mp member
      have live : i < last+1 := by simp at hi; omega
      have h := root_dominates refl trans l (by omega : last+1 ≤ l.length) heap i live
      rw [List.getElem_take] at hv
      simpa only [List.getElem_set_ne (by omega : 0 ≠ last), List.getElem_set_self, hv] using h
    · exact drain_frame perm frame ord j (by omega) hj hjl x hx

theorem drain_complete {α : Type} {le : α → α → Prop} {l : List α} {k stop : Nat}
    (hk : k ≤ 1) (ord : DrainOrder le l k stop) :
    (l.take stop).Pairwise le := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hb : j < l.length ∧ j < stop := by simp at hj; omega
  have hii : i < (l.take j).length := by simp; omega
  have earlier : l[i] ∈ l.take j := by
    have h := List.getElem_mem hii
    rwa [List.getElem_take] at h
  simpa only [List.getElem_take] using ord j (by omega) hb.2 hb.1 l[i] earlier

/-- Ignoring the hole leaves a sorted prefix. The held value is no larger
    than each element already shifted to its right. -/
structure InsertHole {α : Type} (le : α → α → Prop) (f : Nat → α) (k stop : Nat) : Prop where
  others : ∀ i j, i < j → j < stop → i ≠ k → j ≠ k → le (f i) (f j)
  right : ∀ j, k < j → j < stop → le (f k) (f j)

theorem shift_predecessor {α : Type} {le : α → α → Prop} {f : Nat → α}
    {k stop : Nat} (inv : InsertHole le f (k+1) stop) (hk : k+1 < stop)
    (go : le (f (k+1)) (f k)) : InsertHole le (exchange f (k+1) k) k stop := by
  constructor
  · intro i j hij hj hin hjn
    by_cases ie : i = k+1
    · subst i
      simpa [exchange, show j ≠ k+1 by omega, hjn] using
        inv.others k j (by omega) hj (by omega) (by omega)
    · by_cases je : j = k+1
      · subst j
        simpa [exchange, ie, hin] using inv.others i k (by omega) (by omega) ie (by omega)
      · simpa [exchange, ie, hin, je, hjn] using inv.others i j hij hj ie je
  · intro j hj hs
    by_cases je : j = k+1
    · subst j; simpa [exchange] using go
    · simpa [exchange, je, show j ≠ k by omega] using inv.right j (by omega) hs

theorem complete_insert {α : Type} {le : α → α → Prop}
    (trans : ∀ {a b c}, le a b → le b c → le a c)
    {f : Nat → α} {k stop : Nat} (inv : InsertHole le f k stop) (hk : k < stop)
    (left : 0 < k → le (f (k-1)) (f k)) :
    ∀ i j, i < j → j < stop → le (f i) (f j) := by
  intro i j hij hj
  by_cases ie : i = k
  · subst i; exact inv.right j hij hj
  · by_cases je : j = k
    · subst j
      by_cases ep : i = k-1
      · subst i; exact left (by omega)
      · exact trans (inv.others i (k-1) (by omega) (by omega) ie (by omega)) (left (by omega))
    · exact inv.others i j hij hj ie je

/-- Extend a sorted prefix using only the comparison against its last slot. -/
theorem pairwise_next {α : Type} {le : α → α → Prop}
    (trans : ∀ {a b c}, le a b → le b c → le a c)
    (l : List α) {k : Nat} (hk : k < l.length) (ordered : (l.take k).Pairwise le)
    (last : ∀ h : 0 < k, le (l[k-1]'(by omega)) l[k]) :
    (l.take (k+1)).Pairwise le := by
  rw [List.take_succ_eq_append_getElem hk, List.pairwise_append]
  refine ⟨ordered, by simp, ?_⟩
  intro a ha b hb
  obtain rfl := List.mem_singleton.mp hb
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have h : i < k := by simp at hi; omega
  by_cases eq : i = k-1
  · simpa only [List.getElem_take, eq] using last (by omega)
  · have hp : k-1 < (l.take k).length := by simp; omega
    exact trans (List.pairwise_iff_getElem.mp ordered i (k-1) hi hp (by omega))
      (by simpa only [List.getElem_take] using last (by omega))

/-- A nondecreasing run whose endpoints are in reverse order is also
    nonincreasing. This includes a run of equal keys before a descent. -/
theorem descending_tie {α : Type} {le : α → α → Prop}
    (refl : ∀ x, le x x) (trans : ∀ {a b c}, le a b → le b c → le a c)
    (l : List α) {k : Nat} (hk : k ≤ l.length) (pos : 0 < k)
    (ordered : (l.take k).Pairwise le) (ends : le (l[k-1]'(by omega)) (l[0]'(by omega))) :
    (l.take k).Pairwise (fun a b => le b a) := by
  have cmp (i j : Nat) (ij : i ≤ j) (hb : j < k) :
      le (l[i]'(by omega)) (l[j]'(by omega)) := by
    rcases Nat.eq_or_lt_of_le ij with e | h
    · subst j; apply refl
    · have hpair := List.pairwise_iff_getElem.mp ordered i j (by simp; omega) (by simp; omega) h
      rw [List.getElem_take, List.getElem_take] at hpair
      exact hpair
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [List.getElem_take]
  have b : j < k := by simp at hj; omega
  exact trans (cmp j (k-1) (by omega) (by omega)) (trans ends (cmp 0 i (by omega) (by omega)))

end YoctoCore.Properties.OrderRangeHeap
