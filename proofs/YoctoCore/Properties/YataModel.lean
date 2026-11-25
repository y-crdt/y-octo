/-
The store of `y_octo_core::yata_store` over `Nat`: an arena of items that name
their neighbours by slot, the first item of the sequence, and the block
timeline of every client. `YataStore.lean` shows that the extracted Rust
functions compute the operations defined here; `Refinement.lean` shows that
these are the operations of `YoctoSpec` on the block sequence a store stands
for. Only Lean core and `YoctoSpec` are used.
-/
import YoctoSpec
import YoctoCore.Properties.ListAux

set_option autoImplicit false

namespace YoctoCore.Properties.YataModel

open YoctoSpec
open YoctoCore.Properties.ListAux

/-- `ItemCore`. -/
structure MItem where
  id : Id
  len : Nat
  originL : Option Id
  originR : Option Id
  left : Option Nat
  right : Option Nat
  deleted : Bool
  gc : Bool
deriving Inhabited

/-- `BlockKindCore`. -/
inductive MKind where
  | item (i : Nat)
  | deleted (i : Nat)
  | gc
  | skip
deriving Inhabited

/-- `BlockKindCore::item`. -/
def MKind.slot : MKind → Option Nat
  | .item i => some i
  | .deleted i => some i
  | .gc => none
  | .skip => none

/-- `BlockKindCore::deleted`. -/
def MKind.dead : MKind → Bool
  | .item _ => false
  | .deleted _ => true
  | .gc => true
  | .skip => true

/-- `BlockRefCore`. -/
structure MBlock where
  clock : Nat
  kind : MKind
deriving Inhabited

/-- `ClientEntryCore` with its `ClientBlocksCore`: `stop` is `end_clock`. -/
structure MClient where
  client : Nat
  blocks : List MBlock
  stop : Nat
deriving Inhabited

/-- `YataStoreCore`. -/
structure MStore where
  items : List MItem
  start : Option Nat
  clients : List MClient
deriving Inhabited

/-! ## Links -/

def rightOf (items : List MItem) (i : Nat) : Option Nat := (items[i]?).bind MItem.right

def leftOf (items : List MItem) (i : Nat) : Option Nat := (items[i]?).bind MItem.left

/-- An item without its links: what the timelines and the block sequence see. -/
def MItem.core (x : MItem) : MItem := { x with left := none, right := none }

def coreAt (items : List MItem) (i : Nat) : Option MItem := (items[i]?).map MItem.core

theorem rightOf_upd (l : List MItem) (p i : Nat) (f : MItem → MItem) :
    rightOf (upd l p f) i = if i = p then ((l[i]?).map f).bind MItem.right else rightOf l i := by
  unfold rightOf
  rw [get?_upd]
  by_cases h : i = p
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem leftOf_upd (l : List MItem) (p i : Nat) (f : MItem → MItem) :
    leftOf (upd l p f) i = if i = p then ((l[i]?).map f).bind MItem.left else leftOf l i := by
  unfold leftOf
  rw [get?_upd]
  by_cases h : i = p
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem rightOf_upd_keep (l : List MItem) (p i : Nat) {f : MItem → MItem}
    (hf : ∀ x, (f x).right = x.right) : rightOf (upd l p f) i = rightOf l i := by
  rw [rightOf_upd]
  by_cases h : i = p
  · rw [ite_eq_left h]
    unfold rightOf
    cases l[i]? with
    | none => rfl
    | some x => exact hf x
  · rw [ite_eq_right h]

theorem leftOf_upd_keep (l : List MItem) (p i : Nat) {f : MItem → MItem}
    (hf : ∀ x, (f x).left = x.left) : leftOf (upd l p f) i = leftOf l i := by
  rw [leftOf_upd]
  by_cases h : i = p
  · rw [ite_eq_left h]
    unfold leftOf
    cases l[i]? with
    | none => rfl
    | some x => exact hf x
  · rw [ite_eq_right h]

theorem coreAt_upd (l : List MItem) (p i : Nat) (f : MItem → MItem) :
    coreAt (upd l p f) i = if i = p then (l[i]?).map (fun x => (f x).core) else coreAt l i := by
  unfold coreAt
  rw [get?_upd]
  by_cases h : i = p
  · rw [ite_eq_left h, ite_eq_left h]
    cases l[i]? with
    | none => rfl
    | some x => rfl
  · rw [ite_eq_right h, ite_eq_right h]

theorem coreAt_upd_keep (l : List MItem) (p i : Nat) {f : MItem → MItem}
    (hf : ∀ x, (f x).core = x.core) : coreAt (upd l p f) i = coreAt l i := by
  rw [coreAt_upd]
  by_cases h : i = p
  · rw [ite_eq_left h]
    unfold coreAt
    cases l[i]? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · rw [ite_eq_right h]

theorem rightOf_append_left {l r : List MItem} {i : Nat} (h : i < l.length) :
    rightOf (l ++ r) i = rightOf l i := by
  unfold rightOf
  rw [get?_append_left h]

theorem leftOf_append_left {l r : List MItem} {i : Nat} (h : i < l.length) :
    leftOf (l ++ r) i = leftOf l i := by
  unfold leftOf
  rw [get?_append_left h]

theorem coreAt_append_left {l r : List MItem} {i : Nat} (h : i < l.length) :
    coreAt (l ++ r) i = coreAt l i := by
  unfold coreAt
  rw [get?_append_left h]

theorem get?_append_new (l : List MItem) (x : MItem) : (l ++ [x])[l.length]? = some x := by
  simp

theorem rightOf_none {l : List MItem} {i : Nat} (h : l.length ≤ i) : rightOf l i = none := by
  unfold rightOf
  rw [get?_none h]
  rfl

theorem leftOf_none {l : List MItem} {i : Nat} (h : l.length ≤ i) : leftOf l i = none := by
  unfold leftOf
  rw [get?_none h]
  rfl

theorem coreAt_none {l : List MItem} {i : Nat} (h : l.length ≤ i) : coreAt l i = none := by
  unfold coreAt
  rw [get?_none h]
  rfl

theorem coreAt_some {l : List MItem} {i : Nat} (h : i < l.length) : ∃ c, coreAt l i = some c := by
  obtain ⟨x, hx⟩ := get?_some h
  exact ⟨x.core, by unfold coreAt; rw [hx]; rfl⟩

theorem coreAt_lt {l : List MItem} {i : Nat} {c : MItem} (h : coreAt l i = some c) : i < l.length := by
  unfold coreAt at h
  cases hx : l[i]? with
  | none => rw [hx] at h; cases h
  | some x => exact get?_lt hx

/-! ## The sequence as a chain of slots -/

/-- `order` lists the slots of the sequence from `start` on: each names its
successor as `right` and its predecessor as `left`. -/
structure Chain (items : List MItem) (start : Option Nat) (order : List Nat) : Prop where
  nodup : order.Nodup
  bound : ∀ i, i ∈ order → i < items.length
  head : start = order[0]?
  right : ∀ k i, order[k]? = some i → rightOf items i = order[k + 1]?
  left : ∀ k i, order[k + 1]? = some i → leftOf items i = order[k]?
  first : ∀ i, order[0]? = some i → leftOf items i = none

/-- The slots reached from `cur` through `right`, at most `fuel` of them. -/
def walk (items : List MItem) : Nat → Option Nat → List Nat
  | 0, _ => []
  | _ + 1, none => []
  | fuel + 1, some i => i :: walk items fuel (rightOf items i)

theorem walk_none (items : List MItem) (fuel : Nat) : walk items fuel none = [] := by
  cases fuel <;> rfl

theorem walk_suffix {items : List MItem} {order : List Nat}
    (hr : ∀ k i, order[k]? = some i → rightOf items i = order[k + 1]?) :
    ∀ (suf pre : List Nat) (fuel : Nat), order = pre ++ suf → suf.length ≤ fuel →
      walk items fuel suf[0]? = suf := by
  intro suf
  induction suf with
  | nil =>
    intro pre fuel _ _
    have e : ([] : List Nat)[0]? = none := by simp
    rw [e, walk_none]
  | cons i t ih =>
    intro pre fuel he hf
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hi : order[pre.length]? = some i := by
        rw [he]
        simp
      have hnext : rightOf items i = t[0]? := by
        rw [hr pre.length i hi, he]
        have := get?_append_right pre (i :: t) 1
        simpa using this
      have ht : walk items f t[0]? = t :=
        ih (pre ++ [i]) f (by rw [he]; simp) (by simp only [List.length_cons] at hf; omega)
      have e : (i :: t)[0]? = some i := by simp
      rw [e]
      show i :: walk items f (rightOf items i) = i :: t
      rw [hnext, ht]

/-- A chain is the walk from its start: the store determines the order. -/
theorem Chain.walk_eq {items : List MItem} {start : Option Nat} {order : List Nat}
    (h : Chain items start order) : walk items items.length start = order := by
  have hlen : order.length ≤ items.length := nodup_length_le _ _ h.nodup h.bound
  rw [h.head]
  exact walk_suffix h.right order [] items.length rfl hlen

theorem Chain.unique {items : List MItem} {start : Option Nat} {o₁ o₂ : List Nat}
    (h₁ : Chain items start o₁) (h₂ : Chain items start o₂) : o₁ = o₂ := by
  rw [← h₁.walk_eq, ← h₂.walk_eq]

/-- Position of a slot in the order. -/
theorem Chain.pos_unique {items : List MItem} {start : Option Nat} {order : List Nat}
    (h : Chain items start order) {j k i : Nat} (hj : order[j]? = some i) (hk : order[k]? = some i) :
    j = k :=
  nodup_get?_inj h.nodup hj hk

/-- Items that keep their links keep the chain. -/
theorem Chain.congr {items items' : List MItem} {start : Option Nat} {order : List Nat}
    (h : Chain items start order) (hlen : items'.length = items.length)
    (hr : ∀ i, i ∈ order → rightOf items' i = rightOf items i)
    (hl : ∀ i, i ∈ order → leftOf items' i = leftOf items i) : Chain items' start order where
  nodup := h.nodup
  bound := by
    intro i hi
    rw [hlen]
    exact h.bound i hi
  head := h.head
  right := by
    intro k i hk
    rw [hr i (get?_mem hk)]
    exact h.right k i hk
  left := by
    intro k i hk
    rw [hl i (get?_mem hk)]
    exact h.left k i hk
  first := by
    intro i hi
    rw [hl i (get?_mem hi)]
    exact h.first i hi

/-! ### Linking a new item -/

/-- The item after `prev`; the first item of the sequence without `prev`. -/
def nextOf (items : List MItem) (start : Option Nat) : Option Nat → Option Nat
  | none => start
  | some p => rightOf items p

def setRight (n : Nat) : Option Nat → List MItem → List MItem
  | none, l => l
  | some p, l => upd l p (fun x => { x with right := some n })

def setLeft (n : Nat) : Option Nat → List MItem → List MItem
  | none, l => l
  | some q, l => upd l q (fun x => { x with left := some n })

/-- The arena after `it` took the next slot as the right neighbour of `prev`. -/
def linkItems (items : List MItem) (start prev : Option Nat) (it : MItem) : List MItem :=
  setLeft items.length (nextOf items start prev)
    (setRight items.length prev
      (items ++ [{ it with left := prev, right := nextOf items start prev }]))

def linkStart (items : List MItem) (start : Option Nat) : Option Nat → Option Nat
  | none => some items.length
  | some _ => start

@[simp] theorem length_setRight (n : Nat) (o : Option Nat) (l : List MItem) :
    (setRight n o l).length = l.length := by
  cases o <;> simp [setRight]

@[simp] theorem length_setLeft (n : Nat) (o : Option Nat) (l : List MItem) :
    (setLeft n o l).length = l.length := by
  cases o <;> simp [setLeft]

@[simp] theorem length_linkItems (items : List MItem) (start prev : Option Nat) (it : MItem) :
    (linkItems items start prev it).length = items.length + 1 := by
  simp [linkItems]

theorem rightOf_setLeft (n : Nat) (o : Option Nat) (l : List MItem) (i : Nat) :
    rightOf (setLeft n o l) i = rightOf l i := by
  cases o with
  | none => rfl
  | some q => exact rightOf_upd_keep l q i (fun _ => rfl)

theorem leftOf_setRight (n : Nat) (o : Option Nat) (l : List MItem) (i : Nat) :
    leftOf (setRight n o l) i = leftOf l i := by
  cases o with
  | none => rfl
  | some p => exact leftOf_upd_keep l p i (fun _ => rfl)

theorem coreAt_setLeft (n : Nat) (o : Option Nat) (l : List MItem) (i : Nat) :
    coreAt (setLeft n o l) i = coreAt l i := by
  cases o with
  | none => rfl
  | some q => exact coreAt_upd_keep l q i (fun _ => rfl)

theorem coreAt_setRight (n : Nat) (o : Option Nat) (l : List MItem) (i : Nat) :
    coreAt (setRight n o l) i = coreAt l i := by
  cases o with
  | none => rfl
  | some p => exact coreAt_upd_keep l p i (fun _ => rfl)

theorem rightOf_setRight (n : Nat) (o : Option Nat) (l : List MItem) {i : Nat} (hi : i < l.length) :
    rightOf (setRight n o l) i = if o = some i then some n else rightOf l i := by
  cases o with
  | none => simp [setRight]
  | some p =>
    show rightOf (upd l p _) i = _
    rw [rightOf_upd]
    by_cases h : i = p
    · have e : (some p = some i) := by rw [h]
      rw [ite_eq_left h, ite_eq_left e]
      obtain ⟨x, hx⟩ := get?_some hi
      rw [hx]
      rfl
    · have e : ¬ (some p = some i) := fun e => h (Option.some.inj e).symm
      rw [ite_eq_right h, ite_eq_right e]

theorem leftOf_setLeft (n : Nat) (o : Option Nat) (l : List MItem) {i : Nat} (hi : i < l.length) :
    leftOf (setLeft n o l) i = if o = some i then some n else leftOf l i := by
  cases o with
  | none => simp [setLeft]
  | some q =>
    show leftOf (upd l q _) i = _
    rw [leftOf_upd]
    by_cases h : i = q
    · have e : (some q = some i) := by rw [h]
      rw [ite_eq_left h, ite_eq_left e]
      obtain ⟨x, hx⟩ := get?_some hi
      rw [hx]
      rfl
    · have e : ¬ (some q = some i) := fun e => h (Option.some.inj e).symm
      rw [ite_eq_right h, ite_eq_right e]

/-- Linking leaves the items as they are, links aside. -/
theorem coreAt_linkItems (items : List MItem) (start prev : Option Nat) (it : MItem) (i : Nat) :
    coreAt (linkItems items start prev it) i =
      if i = items.length then some it.core else coreAt items i := by
  unfold linkItems
  rw [coreAt_setLeft, coreAt_setRight]
  by_cases h : i = items.length
  · rw [ite_eq_left h, h]
    unfold coreAt
    rw [get?_append_new]
    rfl
  · rw [ite_eq_right h]
    by_cases hlt : i < items.length
    · exact coreAt_append_left hlt
    · rw [coreAt_none (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
        coreAt_none (by omega)]

theorem rightOf_linkItems_old (items : List MItem) (start prev : Option Nat) (it : MItem) {i : Nat}
    (hi : i < items.length) :
    rightOf (linkItems items start prev it) i =
      if prev = some i then some items.length else rightOf items i := by
  unfold linkItems
  rw [rightOf_setLeft, rightOf_setRight _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
    rightOf_append_left hi]

theorem leftOf_linkItems_old (items : List MItem) (start prev : Option Nat) (it : MItem) {i : Nat}
    (hi : i < items.length) :
    leftOf (linkItems items start prev it) i =
      if nextOf items start prev = some i then some items.length else leftOf items i := by
  unfold linkItems
  rw [leftOf_setLeft _ _ _ (by simp only [length_setRight, List.length_append, List.length_cons, List.length_nil]; omega),
    leftOf_setRight, leftOf_append_left hi]

theorem rightOf_linkItems_new (items : List MItem) (start prev : Option Nat) (it : MItem)
    (hp : ∀ p, prev = some p → p < items.length) :
    rightOf (linkItems items start prev it) items.length = nextOf items start prev := by
  unfold linkItems
  rw [rightOf_setLeft]
  cases prev with
  | none =>
    show rightOf (items ++ [_]) items.length = _
    unfold rightOf
    rw [get?_append_new]
    rfl
  | some p =>
    have hne : items.length ≠ p := by
      have := hp p rfl
      omega
    show rightOf (upd _ p _) items.length = _
    rw [rightOf_upd, ite_eq_right hne]
    unfold rightOf
    rw [get?_append_new]
    rfl

theorem leftOf_linkItems_new (items : List MItem) (start prev : Option Nat) (it : MItem)
    (hq : ∀ q, nextOf items start prev = some q → q < items.length) :
    leftOf (linkItems items start prev it) items.length = prev := by
  unfold linkItems
  rw [leftOf_setLeft _ _ _ (by simp only [length_setRight, List.length_append, List.length_cons, List.length_nil]; omega)]
  have hne : ¬ (nextOf items start prev = some items.length) := by
    intro e
    have := hq _ e
    omega
  rw [ite_eq_right hne, leftOf_setRight]
  unfold leftOf
  rw [get?_append_new]
  rfl

/-- The slot before position `k` of an order. -/
def prevAt (order : List Nat) : Nat → Option Nat
  | 0 => none
  | j + 1 => order[j]?

theorem Chain.nextOf_prevAt {items : List MItem} {start : Option Nat} {order : List Nat}
    (h : Chain items start order) {k : Nat} (hk : k ≤ order.length) :
    nextOf items start (prevAt order k) = order[k]? := by
  cases k with
  | zero => exact h.head
  | succ j =>
    obtain ⟨p, hp⟩ := get?_some (show j < order.length by omega)
    show nextOf items start order[j]? = _
    rw [hp]
    exact h.right j p hp

/-- A new item linked at position `k` of the sequence: the chain is the old
one with the new slot at `k`. -/
theorem Chain.link {items : List MItem} {start : Option Nat} {order : List Nat}
    (h : Chain items start order) {k : Nat} (hk : k ≤ order.length) (it : MItem) :
    Chain (linkItems items start (prevAt order k) it) (linkStart items start (prevAt order k))
      (insAt order k items.length) := by
  have hnx := h.nextOf_prevAt hk
  have hfresh : ¬ items.length ∈ order := fun hm => by
    have := h.bound _ hm
    omega
  have hp : ∀ p, prevAt order k = some p → p < items.length := by
    intro p e
    cases k with
    | zero => cases e
    | succ j => exact h.bound p (get?_mem e)
  have hq : ∀ q, nextOf items start (prevAt order k) = some q → q < items.length := by
    intro q e
    rw [hnx] at e
    exact h.bound q (get?_mem e)
  -- the new order by position
  have new_lt : ∀ j, j < k → (insAt order k items.length)[j]? = order[j]? :=
    fun j hj => get?_insAt_lt order _ hj hk
  have new_eq : (insAt order k items.length)[k]? = some items.length := get?_insAt_self order _ hk
  have new_gt : ∀ j, k ≤ j → (insAt order k items.length)[j + 1]? = order[j]? :=
    fun j hj => get?_insAt_gt order _ hj
  -- which old slot is `prev`, which is `next`
  have prev_iff : ∀ j i, order[j]? = some i → (prevAt order k = some i ↔ j + 1 = k) := by
    intro j i hj
    constructor
    · intro e
      cases k with
      | zero => cases e
      | succ k' =>
        have : k' = j := h.pos_unique e hj
        omega
    · intro e
      rw [← e]
      exact hj
  have next_iff : ∀ j i, order[j]? = some i →
      (nextOf items start (prevAt order k) = some i ↔ j = k) := by
    intro j i hj
    rw [hnx]
    constructor
    · intro e
      exact (h.pos_unique e hj).symm
    · intro e
      rw [← e]
      exact hj
  refine ⟨nodup_insAt h.nodup hfresh, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [length_linkItems]
    rcases mem_insAt.mp hi with e | hm
    · omega
    · have := h.bound i hm
      omega
  · cases k with
    | zero =>
      show some items.length = _
      exact new_eq.symm
    | succ j =>
      obtain ⟨p, hpj⟩ := get?_some (show j < order.length by omega)
      have e : prevAt order (j + 1) = some p := hpj
      rw [e, new_lt 0 (by omega)]
      exact h.head
  · -- right links
    intro j i hj
    by_cases hjk : j < k
    · rw [new_lt j hjk] at hj
      have hib := h.bound i (get?_mem hj)
      rw [rightOf_linkItems_old _ _ _ _ hib]
      by_cases hlast : j + 1 = k
      · rw [ite_eq_left ((prev_iff j i hj).mpr hlast), hlast]
        exact new_eq.symm
      · rw [ite_eq_right (fun e => hlast ((prev_iff j i hj).mp e)), new_lt (j + 1) (by omega)]
        exact h.right j i hj
    · by_cases hjk' : j = k
      · rw [hjk', new_eq] at hj
        have e : i = items.length := (Option.some.inj hj).symm
        rw [e, rightOf_linkItems_new _ _ _ _ hp, hnx, hjk', new_gt k (Nat.le_refl k)]
      · obtain ⟨j', ej⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [ej] at hj ⊢
        rw [new_gt j' (by omega)] at hj
        have hib := h.bound i (get?_mem hj)
        rw [rightOf_linkItems_old _ _ _ _ hib,
          ite_eq_right (fun e => by have := (prev_iff j' i hj).mp e; omega),
          new_gt (j' + 1) (by omega)]
        exact h.right j' i hj
  · -- left links
    intro j i hj
    by_cases hjk : j + 1 < k
    · rw [new_lt (j + 1) hjk] at hj
      have hib := h.bound i (get?_mem hj)
      rw [leftOf_linkItems_old _ _ _ _ hib,
        ite_eq_right (fun e => by have := (next_iff (j + 1) i hj).mp e; omega),
        new_lt j (by omega)]
      exact h.left j i hj
    · by_cases hjk' : j + 1 = k
      · rw [hjk', new_eq] at hj
        have e : i = items.length := (Option.some.inj hj).symm
        rw [e, leftOf_linkItems_new _ _ _ _ hq, new_lt j (by omega), ← hjk']
        rfl
      · -- `j ≥ k`: the element at `j + 1` is the old one at `j`
        rw [new_gt j (by omega)] at hj
        have hib := h.bound i (get?_mem hj)
        rw [leftOf_linkItems_old _ _ _ _ hib]
        by_cases hjk'' : j = k
        · rw [ite_eq_left ((next_iff j i hj).mpr hjk''), hjk'']
          exact new_eq.symm
        · obtain ⟨j', ej⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          rw [ite_eq_right (fun e => hjk'' ((next_iff j i hj).mp e)), ej, new_gt j' (by omega)]
          rw [ej] at hj
          exact h.left j' i hj
  · -- the first item has no left neighbour
    intro i hi
    cases k with
    | zero =>
      rw [new_eq] at hi
      have e : i = items.length := (Option.some.inj hi).symm
      rw [e, leftOf_linkItems_new _ _ _ _ hq]
      rfl
    | succ k' =>
      rw [new_lt 0 (by omega)] at hi
      have hib := h.bound i (get?_mem hi)
      rw [leftOf_linkItems_old _ _ _ _ hib,
        ite_eq_right (fun e => by have := (next_iff 0 i hi).mp e; omega)]
      exact h.first i hi

/-! ## Timelines -/

/-- Where the block at `p` ends: where the next one starts, or at `stop`. -/
def endAt (blocks : List MBlock) (stop p : Nat) : Nat :=
  match blocks[p + 1]? with
  | some b => b.clock
  | none => stop

/-- I1: the blocks of a timeline start at strictly increasing clocks below
`stop`. A block ends where the next one starts, so none is empty and they
follow each other without a gap. -/
structure TimelineWF (blocks : List MBlock) (stop : Nat) : Prop where
  sorted : ∀ (p q : Nat) (a b : MBlock), p < q → blocks[p]? = some a → blocks[q]? = some b →
    a.clock < b.clock
  below : ∀ (p : Nat) (a : MBlock), blocks[p]? = some a → a.clock < stop

theorem TimelineWF.lt_end {blocks : List MBlock} {stop : Nat} (h : TimelineWF blocks stop)
    {p : Nat} {a : MBlock} (hp : blocks[p]? = some a) : a.clock < endAt blocks stop p := by
  unfold endAt
  cases hb : blocks[p + 1]? with
  | none => exact h.below p a hp
  | some b => exact h.sorted p (p + 1) a b (by omega) hp hb

theorem TimelineWF.end_le {blocks : List MBlock} {stop : Nat} (h : TimelineWF blocks stop)
    {p q : Nat} {b : MBlock} (hpq : p < q) (hq : blocks[q]? = some b) :
    endAt blocks stop p ≤ b.clock := by
  unfold endAt
  cases hb : blocks[p + 1]? with
  | none =>
    have h1 := get?_lt hq
    have h2 := get?_none_le hb
    omega
  | some c =>
    by_cases e : p + 1 = q
    · rw [e, hq] at hb
      cases hb
      exact Nat.le_refl _
    · have := h.sorted (p + 1) q c b (by omega) hb hq
      exact Nat.le_of_lt this

theorem TimelineWF.end_le_stop {blocks : List MBlock} {stop : Nat} (h : TimelineWF blocks stop)
    (p : Nat) : endAt blocks stop p ≤ stop := by
  unfold endAt
  cases hb : blocks[p + 1]? with
  | none => exact Nat.le_refl _
  | some c => exact Nat.le_of_lt (h.below (p + 1) c hb)

/-- The block at `p` holds the clock `x`. -/
def Holds (blocks : List MBlock) (stop p x : Nat) : Prop :=
  ∃ a : MBlock, blocks[p]? = some a ∧ a.clock ≤ x ∧ x < endAt blocks stop p

/-- A clock is in one block only. -/
theorem TimelineWF.holds_unique {blocks : List MBlock} {stop : Nat} (h : TimelineWF blocks stop)
    {p q x : Nat} (hp : Holds blocks stop p x) (hq : Holds blocks stop q x) : p = q := by
  obtain ⟨a, ha, ha1, ha2⟩ := hp
  obtain ⟨b, hb, hb1, hb2⟩ := hq
  by_cases h1 : p < q
  · have := h.end_le h1 hb
    omega
  · by_cases h2 : q < p
    · have := h.end_le h2 ha
      omega
    · omega

/-! ## The invariant -/

/-- The slots of the sequence, from its first item on. -/
def order (s : MStore) : List Nat := walk s.items s.items.length s.start

/-- The slot `i` is on a timeline. -/
def Live (clients : List MClient) (i : Nat) : Prop :=
  ∃ (c : MClient) (p : Nat) (b : MBlock), c ∈ clients ∧ c.blocks[p]? = some b ∧ b.kind.slot = some i

/-- I2, I5: the block `b` at `p` of the timeline of `c` is an item of the
arena, with the id, the length and the deleted state the timeline gives it. -/
def BlockOK (items : List MItem) (c : MClient) (p : Nat) (b : MBlock) : Prop :=
  ∃ (i : Nat) (x : MItem), b.kind.slot = some i ∧ coreAt items i = some x ∧
    x.id = ⟨c.client, b.clock⟩ ∧ x.len = endAt c.blocks c.stop p - b.clock ∧
    x.deleted = b.kind.dead

/-- The invariant of a store.
- `distinct`: one timeline per client;
- `timeline` (I1): every timeline is strictly increasing, without empty blocks;
- `block` (I2, I5): every block is an item of the arena whose id, length and
  deleted state are the ones of the block;
- `chain` (I3): the items of the sequence are linked both ways, without a cycle;
- `live`: the sequence holds exactly the items of the timelines;
- `gc` (I8): only deleted items have dropped their content. -/
structure WF (s : MStore) : Prop where
  distinct : ∀ (p q : Nat) (a b : MClient), p < q → s.clients[p]? = some a →
    s.clients[q]? = some b → a.client ≠ b.client
  timeline : ∀ c : MClient, c ∈ s.clients → TimelineWF c.blocks c.stop
  block : ∀ (c : MClient) (p : Nat) (b : MBlock), c ∈ s.clients → c.blocks[p]? = some b →
    BlockOK s.items c p b
  chain : Chain s.items s.start (order s)
  live : ∀ i : Nat, i ∈ order s ↔ Live s.clients i
  gc : ∀ (i : Nat) (x : MItem), i ∈ order s → coreAt s.items i = some x → x.gc = true →
    x.deleted = true

/-- The invariant from any list that is a chain of the store. -/
theorem WF.of_order {s : MStore} (o : List Nat) (hchain : Chain s.items s.start o)
    (hd : ∀ (p q : Nat) (a b : MClient), p < q → s.clients[p]? = some a →
      s.clients[q]? = some b → a.client ≠ b.client)
    (ht : ∀ c : MClient, c ∈ s.clients → TimelineWF c.blocks c.stop)
    (hb : ∀ (c : MClient) (p : Nat) (b : MBlock), c ∈ s.clients → c.blocks[p]? = some b →
      BlockOK s.items c p b)
    (hl : ∀ i : Nat, i ∈ o ↔ Live s.clients i)
    (hg : ∀ (i : Nat) (x : MItem), i ∈ o → coreAt s.items i = some x → x.gc = true →
      x.deleted = true) :
    WF s ∧ order s = o := by
  have e : order s = o := hchain.walk_eq
  exact ⟨⟨hd, ht, hb, by rw [e]; exact hchain, by rw [e]; exact hl, by rw [e]; exact hg⟩, e⟩

theorem WF.empty : WF ⟨[], none, []⟩ := by
  have hc : Chain ([] : List MItem) none [] :=
    { nodup := List.nodup_nil
      bound := fun _ h => by cases h
      head := by simp
      right := fun _ _ h => by simp at h
      left := fun _ _ h => by simp at h
      first := fun _ h => by simp at h }
  refine (WF.of_order (s := ⟨[], none, []⟩) [] hc ?_ ?_ ?_ ?_ ?_).1
  · intro p q a b _ h
    simp at h
  · intro c h
    cases h
  · intro c p b h
    cases h
  · intro i
    constructor
    · intro h
      cases h
    · rintro ⟨c, p, b, h, _⟩
      cases h
  · intro i x h
    cases h

/-- One timeline per client. -/
theorem WF.client_unique {s : MStore} (h : WF s) {c c' : MClient} (hc : c ∈ s.clients)
    (hc' : c' ∈ s.clients) (e : c.client = c'.client) : c = c' := by
  obtain ⟨p, hp⟩ := mem_get? hc
  obtain ⟨q, hq⟩ := mem_get? hc'
  by_cases h1 : p < q
  · exact absurd e (h.distinct p q c c' h1 hp hq)
  · by_cases h2 : q < p
    · exact absurd e.symm (h.distinct q p c' c h2 hq hp)
    · have e' : p = q := by omega
      rw [e', hq] at hp
      exact (Option.some.inj hp).symm

/-- The block `b` at `p` of the timeline of `c` holds the id `z`. -/
structure At (s : MStore) (z : Id) (c : MClient) (p : Nat) (b : MBlock) : Prop where
  mem : c ∈ s.clients
  client : c.client = z.client
  block : c.blocks[p]? = some b
  ge : b.clock ≤ z.clock
  lt : z.clock < endAt c.blocks c.stop p

/-- An id is in one block of one timeline only. -/
theorem At.unique {s : MStore} (h : WF s) {z : Id} {c c' : MClient} {p p' : Nat} {b b' : MBlock}
    (h₁ : At s z c p b) (h₂ : At s z c' p' b') : c = c' ∧ p = p' ∧ b = b' := by
  have ec : c = c' := h.client_unique h₁.mem h₂.mem (h₁.client.trans h₂.client.symm)
  subst ec
  have ep : p = p' := (h.timeline c h₁.mem).holds_unique ⟨b, h₁.block, h₁.ge, h₁.lt⟩
    ⟨b', h₂.block, h₂.ge, h₂.lt⟩
  subst ep
  have eb := h₁.block.symm.trans h₂.block
  exact ⟨rfl, rfl, Option.some.inj eb⟩

/-- The item of a block of a timeline is in the sequence. -/
theorem WF.block_item {s : MStore} (h : WF s) {c : MClient} {p : Nat} {b : MBlock}
    (hc : c ∈ s.clients) (hb : c.blocks[p]? = some b) :
    ∃ (i : Nat) (x : MItem), b.kind.slot = some i ∧ coreAt s.items i = some x ∧
      x.id = ⟨c.client, b.clock⟩ ∧ x.len = endAt c.blocks c.stop p - b.clock ∧
      x.deleted = b.kind.dead ∧ i ∈ order s ∧ 0 < x.len := by
  obtain ⟨i, x, h1, h2, h3, h4, h5⟩ := h.block c p b hc hb
  have hlt := (h.timeline c hc).lt_end hb
  exact ⟨i, x, h1, h2, h3, h4, h5, (h.live i).mpr ⟨c, p, b, hc, hb, h1⟩, by omega⟩

/-- An item of the sequence is the block of a timeline its id names. -/
theorem WF.item_block {s : MStore} (h : WF s) {i : Nat} {x : MItem} (hi : i ∈ order s)
    (hx : coreAt s.items i = some x) :
    ∃ (c : MClient) (p : Nat) (b : MBlock), c ∈ s.clients ∧ c.blocks[p]? = some b ∧
      b.kind.slot = some i ∧ c.client = x.id.client ∧ b.clock = x.id.clock ∧
      x.len = endAt c.blocks c.stop p - b.clock ∧ x.deleted = b.kind.dead ∧ 0 < x.len := by
  obtain ⟨c, p, b, hc, hb, hs⟩ := (h.live i).mp hi
  obtain ⟨i', x', h1, h2, h3, h4, h5, _, h7⟩ := h.block_item hc hb
  have ei : i' = i := Option.some.inj (h1.symm.trans hs)
  rw [ei, hx] at h2
  have ex : x = x' := Option.some.inj h2
  rw [← ex] at h3 h4 h5 h7
  refine ⟨c, p, b, hc, hb, hs, ?_, ?_, h4, h5, h7⟩
  · rw [h3]
  · rw [h3]

/-- Every item of the sequence has a core. -/
theorem WF.core_of_mem {s : MStore} (h : WF s) {i : Nat} (hi : i ∈ order s) :
    ∃ x, coreAt s.items i = some x :=
  coreAt_some (h.chain.bound i hi)

/-- An item of the sequence that holds `z` is the block of a timeline that
holds `z`. -/
theorem WF.at_of_contains {s : MStore} (h : WF s) {i : Nat} {x : MItem} {z : Id}
    (hi : i ∈ order s) (hx : coreAt s.items i = some x) (hc : z.client = x.id.client)
    (h1 : x.id.clock ≤ z.clock) (h2 : z.clock < x.id.clock + x.len) :
    ∃ (c : MClient) (p : Nat) (b : MBlock), At s z c p b ∧ b.kind.slot = some i := by
  obtain ⟨c, p, b, hcm, hb, hs, e1, e2, e3, _, e5⟩ := h.item_block hi hx
  refine ⟨c, p, b, ⟨hcm, by rw [e1, hc], hb, by omega, by omega⟩, hs⟩

/-- Two items of the sequence that hold the same id are the same slot. -/
theorem WF.slot_unique {s : MStore} (h : WF s) {i j : Nat} {x y : MItem} {z : Id}
    (hi : i ∈ order s) (hj : j ∈ order s) (hx : coreAt s.items i = some x)
    (hy : coreAt s.items j = some y) (hxc : z.client = x.id.client) (hx1 : x.id.clock ≤ z.clock)
    (hx2 : z.clock < x.id.clock + x.len) (hyc : z.client = y.id.client)
    (hy1 : y.id.clock ≤ z.clock) (hy2 : z.clock < y.id.clock + y.len) : i = j := by
  obtain ⟨c, p, b, ha, hs⟩ := h.at_of_contains hi hx hxc hx1 hx2
  obtain ⟨c', p', b', ha', hs'⟩ := h.at_of_contains hj hy hyc hy1 hy2
  obtain ⟨_, _, eb⟩ := At.unique h ha ha'
  rw [eb] at hs
  exact Option.some.inj (hs.symm.trans hs')

/-- The item of the block that holds `z`. -/
theorem At.item {s : MStore} (h : WF s) {z : Id} {c : MClient} {p : Nat} {b : MBlock}
    (ha : At s z c p b) :
    ∃ (i : Nat) (x : MItem), b.kind.slot = some i ∧ coreAt s.items i = some x ∧
      x.id = ⟨z.client, b.clock⟩ ∧ x.len = endAt c.blocks c.stop p - b.clock ∧
      x.deleted = b.kind.dead ∧ i ∈ order s ∧ 0 < x.len := by
  obtain ⟨i, x, h1, h2, h3, h4, h5, h6, h7⟩ := h.block_item ha.mem ha.block
  rw [ha.client] at h3
  exact ⟨i, x, h1, h2, h3, h4, h5, h6, h7⟩

/-! ## The block sequence of a store -/

/-- The characters `f` assigns to the `n` clocks of client `c` from `k` on. -/
def unitChars (f : Id → Char) (c : Nat) : Nat → Nat → List Char
  | _, 0 => []
  | k, n + 1 => f ⟨c, k⟩ :: unitChars f c (k + 1) n

theorem length_unitChars (f : Id → Char) (c : Nat) : ∀ (n k : Nat), (unitChars f c k n).length = n := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    simp only [unitChars, List.length_cons, ih]

/-- The block an item stands for. The core holds no text: a live item stands
for the text `f` assigns to its clocks. -/
def blockOf (f : Id → Char) (x : MItem) : Block :=
  { id := x.id
    left := x.originL
    right := x.originR
    deleted := x.deleted
    content :=
      if x.gc then Content.del x.len
      else Content.str (unitChars f x.id.client x.id.clock x.len) }

theorem blockOf_len (f : Id → Char) (x : MItem) : (blockOf f x).len = x.len := by
  unfold Block.len blockOf
  by_cases h : x.gc = true
  · simp only [h, ite_true]
    rfl
  · simp only [h]
    exact length_unitChars f _ _ _

theorem blockOf_core (f : Id → Char) (x : MItem) : blockOf f x.core = blockOf f x := rfl

def itemAt (items : List MItem) (i : Nat) : MItem := (items[i]?).getD default

def blockAt (f : Id → Char) (items : List MItem) (i : Nat) : Block := blockOf f (itemAt items i)

theorem blockAt_of_core {f : Id → Char} {items : List MItem} {i : Nat} {x : MItem}
    (h : coreAt items i = some x) : blockAt f items i = blockOf f x := by
  unfold coreAt at h
  unfold blockAt itemAt
  cases hy : items[i]? with
  | none =>
    rw [hy] at h
    cases h
  | some y =>
    rw [hy] at h
    have e : y.core = x := Option.some.inj h
    rw [← e]
    rfl

/-- The block sequence a store stands for (`abs`). -/
def blocks (f : Id → Char) (s : MStore) : List Block := (order s).map (blockAt f s.items)

theorem mem_blocks {f : Id → Char} {s : MStore} (h : WF s) {B : Block} (hB : B ∈ blocks f s) :
    ∃ (i : Nat) (x : MItem), i ∈ order s ∧ coreAt s.items i = some x ∧ B = blockOf f x := by
  obtain ⟨i, hi, e⟩ := List.mem_map.mp hB
  obtain ⟨x, hx⟩ := h.core_of_mem hi
  exact ⟨i, x, hi, hx, by rw [← e, blockAt_of_core hx]⟩

/-- Every block of the sequence holds a clock. -/
theorem blocks_wf {f : Id → Char} {s : MStore} (h : WF s) : BlockWF (blocks f s) := by
  intro B hB
  obtain ⟨i, x, hi, hx, e⟩ := mem_blocks h hB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hlen⟩ := h.item_block hi hx
  rw [e, blockOf_len]
  exact hlen

/-! ## Splitting an item -/

theorem itemAt_core {items : List MItem} {i : Nat} {x : MItem} (h : coreAt items i = some x) :
    (itemAt items i).core = x := by
  unfold coreAt at h
  unfold itemAt
  cases hy : items[i]? with
  | none =>
    rw [hy] at h
    cases h
  | some y =>
    rw [hy] at h
    exact Option.some.inj h

theorem endAt_insAt_lt {blocks : List MBlock} {stop q i : Nat} (nb : MBlock) (h : q + 1 < i)
    (hi : i ≤ blocks.length) : endAt (insAt blocks i nb) stop q = endAt blocks stop q := by
  unfold endAt
  rw [get?_insAt_lt blocks nb h hi]

theorem endAt_insAt_eq {blocks : List MBlock} {stop q i : Nat} (nb : MBlock) (h : q + 1 = i)
    (hi : i ≤ blocks.length) : endAt (insAt blocks i nb) stop q = nb.clock := by
  unfold endAt
  rw [h, get?_insAt_self blocks nb hi]

theorem endAt_insAt_gt {blocks : List MBlock} {stop q i : Nat} (nb : MBlock) (h : i ≤ q) :
    endAt (insAt blocks i nb) stop (q + 1) = endAt blocks stop q := by
  unfold endAt
  rw [get?_insAt_gt blocks nb (by omega : i ≤ q + 1)]

theorem endAt_insAt_self {blocks : List MBlock} {stop q : Nat} (nb : MBlock) :
    endAt (insAt blocks (q + 1) nb) stop (q + 1) = endAt blocks stop q := by
  unfold endAt
  rw [get?_insAt_gt blocks nb (Nat.le_refl (q + 1))]

/-- A block boundary strictly inside the block at `p` keeps the timeline. -/
theorem TimelineWF.insert {blocks : List MBlock} {stop : Nat} (h : TimelineWF blocks stop)
    {p : Nat} {b nb : MBlock} (hb : blocks[p]? = some b) (h1 : b.clock < nb.clock)
    (h2 : nb.clock < endAt blocks stop p) : TimelineWF (insAt blocks (p + 1) nb) stop := by
  have hp := get?_lt hb
  have hle : p + 1 ≤ blocks.length := by omega
  have mono : ∀ (q : Nat) (a : MBlock), q ≤ p → blocks[q]? = some a → a.clock ≤ b.clock := by
    intro q a hq ha
    by_cases e : q = p
    · rw [e, hb] at ha
      rw [← Option.some.inj ha]
      exact Nat.le_refl _
    · exact Nat.le_of_lt (h.sorted q p a b (by omega) ha hb)
  constructor
  · intro q r a c hqr ha hc
    rcases get?_insAt_cases hle ha with ⟨hq, ha'⟩ | ⟨hq, ea⟩ | ⟨q', eq, hq', ha'⟩
    · rcases get?_insAt_cases hle hc with ⟨hr, hc'⟩ | ⟨hr, ec⟩ | ⟨r', er, hr', hc'⟩
      · exact h.sorted q r a c hqr ha' hc'
      · rw [ec]
        have := mono q a (by omega) ha'
        omega
      · exact h.sorted q r' a c (by omega) ha' hc'
    · rcases get?_insAt_cases hle hc with ⟨hr, hc'⟩ | ⟨hr, ec⟩ | ⟨r', er, hr', hc'⟩
      · omega
      · omega
      · rw [ea]
        have := h.end_le (show p < r' by omega) hc'
        omega
    · rcases get?_insAt_cases hle hc with ⟨hr, hc'⟩ | ⟨hr, ec⟩ | ⟨r', er, hr', hc'⟩
      · omega
      · omega
      · exact h.sorted q' r' a c (by omega) ha' hc'
  · intro q a ha
    rcases get?_insAt_cases hle ha with ⟨hq, ha'⟩ | ⟨hq, ea⟩ | ⟨q', eq, hq', ha'⟩
    · exact h.below q a ha'
    · rw [ea]
      have := h.end_le_stop p
      omega
    · exact h.below q' a ha'

/-- Taking a block boundary away keeps the timeline. -/
theorem TimelineWF.remove {blocks : List MBlock} {stop : Nat} (h : TimelineWF blocks stop)
    (i : Nat) : TimelineWF (delAt blocks i) stop := by
  constructor
  · intro p q a b hpq ha hb
    rcases get?_delAt_cases ha with ⟨hp, ha'⟩ | ⟨hp, ha'⟩
    · rcases get?_delAt_cases hb with ⟨hq, hb'⟩ | ⟨hq, hb'⟩
      · exact h.sorted p q a b hpq ha' hb'
      · exact h.sorted p (q + 1) a b (by omega) ha' hb'
    · rcases get?_delAt_cases hb with ⟨hq, hb'⟩ | ⟨hq, hb'⟩
      · omega
      · exact h.sorted (p + 1) (q + 1) a b (by omega) ha' hb'
  · intro p a ha
    rcases get?_delAt_cases ha with ⟨_, ha'⟩ | ⟨_, ha'⟩
    · exact h.below p a ha'
    · exact h.below (p + 1) a ha'

/-- Changing a block without moving its start keeps the timeline. -/
theorem TimelineWF.update {blocks : List MBlock} {stop : Nat} (h : TimelineWF blocks stop)
    (i : Nat) {g : MBlock → MBlock} (hg : ∀ b, blocks[i]? = some b → (g b).clock = b.clock) :
    TimelineWF (upd blocks i g) stop := by
  have key : ∀ (p : Nat) (a : MBlock), (upd blocks i g)[p]? = some a →
      ∃ a', blocks[p]? = some a' ∧ a.clock = a'.clock := by
    intro p a ha
    rcases get?_upd_cases ha with ⟨e, a', ha', ea⟩ | ⟨_, ha'⟩
    · refine ⟨a', by rw [e]; exact ha', ?_⟩
      rw [ea]
      exact hg a' ha'
    · exact ⟨a, ha', rfl⟩
  constructor
  · intro p q a b hpq ha hb
    obtain ⟨a', ha', ea⟩ := key p a ha
    obtain ⟨b', hb', eb⟩ := key q b hb
    rw [ea, eb]
    exact h.sorted p q a' b' hpq ha' hb'
  · intro p a ha
    obtain ⟨a', ha', ea⟩ := key p a ha
    rw [ea]
    exact h.below p a' ha'

/-- The right half of an item split after its first `d` clocks. -/
def MItem.rightHalf (x : MItem) (d : Nat) : MItem :=
  { id := ⟨x.id.client, x.id.clock + d⟩
    len := x.len - d
    originL := some ⟨x.id.client, x.id.clock + d - 1⟩
    originR := x.originR
    left := none
    right := none
    deleted := x.deleted
    gc := x.gc }

/-- The kind of the right half of a split block: the same state, another slot. -/
def MKind.reslot (k : MKind) (n : Nat) : MKind := if k.dead then .deleted n else .item n

theorem MKind.slot_reslot (k : MKind) (n : Nat) : (k.reslot n).slot = some n := by
  cases k <;> simp [MKind.reslot, MKind.dead, MKind.slot]

theorem MKind.dead_reslot (k : MKind) (n : Nat) : (k.reslot n).dead = k.dead := by
  cases k <;> simp [MKind.reslot, MKind.dead]

/-- The timeline of a client with one more block boundary. -/
def MClient.withBlock (c : MClient) (q : Nat) (nb : MBlock) : MClient :=
  { c with blocks := insAt c.blocks q nb }

/-- `split_node`: the item at slot `i`, the block `p` of the timeline `ci`,
keeps its first `d` clocks; the rest is a new item right after it. -/
def splitNode (s : MStore) (ci p i d : Nat) : MStore :=
  { items := linkItems (upd s.items i (fun y => { y with len := d })) s.start (some i)
      ((itemAt s.items i).rightHalf d)
    start := s.start
    clients := upd s.clients ci (fun c =>
      c.withBlock (p + 1)
        ⟨(itemAt s.items i).id.clock + d,
          ((c.blocks[p]?).getD default).kind.reslot s.items.length⟩) }

/-- A split keeps the invariant: the new slot follows the split item in the
sequence, and only the two halves change. -/
theorem splitNode_spec {s : MStore} (h : WF s) {ci p i d : Nat} {c : MClient} {b : MBlock}
    {x : MItem} (hc : s.clients[ci]? = some c) (hb : c.blocks[p]? = some b)
    (hs : b.kind.slot = some i) (hx : coreAt s.items i = some x) (hd0 : 0 < d) (hd : d < x.len) :
    ∃ k, (order s)[k]? = some i ∧ WF (splitNode s ci p i d) ∧
      order (splitNode s ci p i d) = insAt (order s) (k + 1) s.items.length ∧
      coreAt (splitNode s ci p i d).items i = some { x with len := d } ∧
      coreAt (splitNode s ci p i d).items s.items.length = some (x.rightHalf d) ∧
      (∀ j, j ≠ i → j ≠ s.items.length →
        coreAt (splitNode s ci p i d).items j = coreAt s.items j) ∧
      (splitNode s ci p i d).items.length = s.items.length + 1 := by
  have hcm : c ∈ s.clients := get?_mem hc
  obtain ⟨i', x', e1, e2, e3, e4, e5, hi', _⟩ := h.block_item hcm hb
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei] at e2 hi'
  rw [hx] at e2
  have ex : x' = x := (Option.some.inj e2).symm
  rw [ex] at e3 e4 e5
  have hi : i ∈ order s := hi'
  obtain ⟨k, hk⟩ := mem_get? hi
  refine ⟨k, hk, ?_⟩
  have hib : i < s.items.length := coreAt_lt hx
  have hyc : (itemAt s.items i).core = x := itemAt_core hx
  have hyclock : (itemAt s.items i).id.clock = b.clock := by
    have e : (itemAt s.items i).core.id = x.id := congrArg MItem.id hyc
    have e' : (itemAt s.items i).id = x.id := e
    rw [e', e3]
  have hxclient : x.id.client = c.client := by rw [e3]
  have hxclock : x.id.clock = b.clock := by rw [e3]
  have htl := h.timeline c hcm
  have hpl := get?_lt hb
  have hn : (upd s.items i (fun y => { y with len := d })).length = s.items.length :=
    length_upd _ _ _
  -- the arena
  have core_new : ∀ j, coreAt (splitNode s ci p i d).items j =
      if j = s.items.length then some ((itemAt s.items i).rightHalf d).core
      else if j = i then some { x with len := d } else coreAt s.items j := by
    intro j
    show coreAt (linkItems _ _ _ _) j = _
    rw [coreAt_linkItems, hn]
    by_cases e : j = s.items.length
    · rw [ite_eq_left e, ite_eq_left e]
    · rw [ite_eq_right e, ite_eq_right e, coreAt_upd]
      by_cases e' : j = i
      · rw [ite_eq_left e', ite_eq_left e', e']
        unfold coreAt at hx
        cases hy : s.items[i]? with
        | none =>
          rw [hy] at hx
          cases hx
        | some y =>
          rw [hy] at hx
          have ey : y.core = x := Option.some.inj hx
          rw [← ey]
          rfl
      · rw [ite_eq_right e', ite_eq_right e']
  have core_i : coreAt (splitNode s ci p i d).items i = some { x with len := d } := by
    rw [core_new, ite_eq_right (by omega : ¬ i = s.items.length), ite_eq_left rfl]
  have core_n : coreAt (splitNode s ci p i d).items s.items.length = some (x.rightHalf d) := by
    rw [core_new, ite_eq_left rfl, ← hyc]
    rfl
  have core_other : ∀ j, j ≠ i → j ≠ s.items.length →
      coreAt (splitNode s ci p i d).items j = coreAt s.items j := by
    intro j h1 h2
    rw [core_new, ite_eq_right h2, ite_eq_right h1]
  have hlen : (splitNode s ci p i d).items.length = s.items.length + 1 := by
    show (linkItems _ _ _ _).length = _
    rw [length_linkItems, hn]
  -- the chain
  have hch1 : Chain (upd s.items i (fun y => { y with len := d })) s.start (order s) :=
    h.chain.congr hn (fun j _ => rightOf_upd_keep _ _ _ (fun _ => rfl))
      (fun j _ => leftOf_upd_keep _ _ _ (fun _ => rfl))
  have hklt : k + 1 ≤ (order s).length := by
    have := get?_lt hk
    omega
  have hch2 := hch1.link hklt ((itemAt s.items i).rightHalf d)
  have eprev : prevAt (order s) (k + 1) = some i := hk
  rw [eprev, hn] at hch2
  have hch : Chain (splitNode s ci p i d).items (splitNode s ci p i d).start
      (insAt (order s) (k + 1) s.items.length) := hch2
  -- the timelines
  have hnb : (⟨(itemAt s.items i).id.clock + d,
      ((c.blocks[p]?).getD default).kind.reslot s.items.length⟩ : MBlock) =
      ⟨b.clock + d, b.kind.reslot s.items.length⟩ := by
    rw [hyclock, hb]
    rfl
  have hcl : ∀ c', c' ∈ (splitNode s ci p i d).clients →
      c' = c.withBlock (p + 1) ⟨b.clock + d, b.kind.reslot s.items.length⟩ ∨
      ∃ j, j ≠ ci ∧ s.clients[j]? = some c' := by
    intro c' hc'
    rcases mem_upd hc' with ⟨a, ha, e⟩ | hj
    · rw [hc] at ha
      have ea : c = a := Option.some.inj ha
      rw [← ea] at e
      left
      rw [e]
      show c.withBlock (p + 1) ⟨(itemAt s.items i).id.clock + d,
        ((c.blocks[p]?).getD default).kind.reslot s.items.length⟩ = _
      rw [hnb]
    · exact Or.inr hj
  have hnew_mem : c.withBlock (p + 1) ⟨b.clock + d, b.kind.reslot s.items.length⟩ ∈
      (splitNode s ci p i d).clients := by
    have h0 := upd_mem_self (f := fun c : MClient =>
      c.withBlock (p + 1)
        ⟨(itemAt s.items i).id.clock + d,
          ((c.blocks[p]?).getD default).kind.reslot s.items.length⟩) hc
    have h1 : c.withBlock (p + 1) ⟨(itemAt s.items i).id.clock + d,
        ((c.blocks[p]?).getD default).kind.reslot s.items.length⟩ ∈
        (splitNode s ci p i d).clients := h0
    rw [hnb] at h1
    exact h1
  have hother : ∀ (j : Nat) (c' : MClient) (q : Nat) (b' : MBlock), j ≠ ci →
      s.clients[j]? = some c' → c'.blocks[q]? = some b' → b'.kind.slot ≠ some i := by
    intro j c' q b' hj hc' hb' hslot
    obtain ⟨i2, x2, f1, f2, f3, _⟩ := h.block c' q b' (get?_mem hc') hb'
    have e2 : i2 = i := Option.some.inj (f1.symm.trans hslot)
    rw [e2, hx] at f2
    have ex2 : x = x2 := Option.some.inj f2
    rw [← ex2, e3] at f3
    have ecl : c.client = c'.client := congrArg Id.client f3
    by_cases hlt : j < ci
    · exact h.distinct j ci c' c hlt hc' hc ecl.symm
    · exact h.distinct ci j c c' (by omega) hc hc' ecl
  have key := WF.of_order (s := splitNode s ci p i d) (insAt (order s) (k + 1) s.items.length) hch
    (by
      intro p' q' a' b' hpq ha' hb'
      have pre : ∀ (j : Nat) (c' : MClient), (splitNode s ci p i d).clients[j]? = some c' →
          ∃ c0, s.clients[j]? = some c0 ∧ c'.client = c0.client := by
        intro j c' hj
        rcases get?_upd_cases hj with ⟨ej, a, ha, e⟩ | ⟨_, hj'⟩
        · exact ⟨a, by rw [ej]; exact ha, by rw [e]; rfl⟩
        · exact ⟨c', hj', rfl⟩
      obtain ⟨a0, ha0, ea⟩ := pre p' a' ha'
      obtain ⟨b0, hb0, eb⟩ := pre q' b' hb'
      rw [ea, eb]
      exact h.distinct p' q' a0 b0 hpq ha0 hb0)
    (by
      intro c' hc'
      rcases hcl c' hc' with e | ⟨j, _, hj⟩
      · rw [e]
        exact htl.insert hb (by show b.clock < b.clock + d; omega)
          (by show b.clock + d < endAt c.blocks c.stop p; omega)
      · exact h.timeline c' (get?_mem hj))
    (by
      intro c' q b' hc' hb'
      rcases hcl c' hc' with e | ⟨j, hj, hcj⟩
      · rw [e] at hb' ⊢
        have hle : p + 1 ≤ c.blocks.length := by omega
        rcases get?_insAt_cases hle hb' with ⟨hq, hb0⟩ | ⟨hq, eb⟩ | ⟨q', eq, hq', hb0⟩
        · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c q b' hcm hb0
          by_cases hqp : q = p
          · rw [hqp, hb] at hb0
            have ebb : b = b' := Option.some.inj hb0
            rw [← ebb, hqp]
            refine ⟨i, { x with len := d }, hs, core_i, e3, ?_, e5⟩
            show d = endAt (insAt c.blocks (p + 1) _) c.stop p - b.clock
            rw [endAt_insAt_eq _ rfl hle]
            show d = b.clock + d - b.clock
            omega
          · have hne : i2 ≠ i := by
              intro e2
              rw [e2, hx] at f2
              have ex2 : x = x2 := Option.some.inj f2
              rw [← ex2, e3] at f3
              have : b.clock = b'.clock := congrArg Id.clock f3
              have := htl.sorted q p b' b (by omega) hb0 hb
              omega
            refine ⟨i2, x2, f1, ?_, f3, ?_, f5⟩
            · rw [core_other i2 hne (by have := coreAt_lt f2; omega)]
              exact f2
            · show x2.len = endAt (insAt c.blocks (p + 1) _) c.stop q - b'.clock
              rw [endAt_insAt_lt _ (by omega) hle]
              exact f4
        · rw [hq, eb]
          refine ⟨s.items.length, x.rightHalf d, MKind.slot_reslot _ _, core_n, ?_, ?_, ?_⟩
          · show (⟨x.id.client, x.id.clock + d⟩ : Id) = ⟨c.client, b.clock + d⟩
            rw [hxclient, hxclock]
          · show x.len - d = endAt (insAt c.blocks (p + 1) _) c.stop (p + 1) - (b.clock + d)
            rw [endAt_insAt_self]
            omega
          · show x.deleted = (b.kind.reslot s.items.length).dead
            rw [MKind.dead_reslot]
            exact e5
        · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c q' b' hcm hb0
          have hne : i2 ≠ i := by
            intro e2
            rw [e2, hx] at f2
            have ex2 : x = x2 := Option.some.inj f2
            rw [← ex2, e3] at f3
            have : b.clock = b'.clock := congrArg Id.clock f3
            have := htl.sorted p q' b b' (by omega) hb hb0
            omega
          rw [eq]
          refine ⟨i2, x2, f1, ?_, f3, ?_, f5⟩
          · rw [core_other i2 hne (by have := coreAt_lt f2; omega)]
            exact f2
          · show x2.len = endAt (insAt c.blocks (p + 1) _) c.stop (q' + 1) - b'.clock
            rw [endAt_insAt_gt _ hq']
            exact f4
      · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c' q b' (get?_mem hcj) hb'
        have hne : i2 ≠ i := fun e2 => hother j c' q b' hj hcj hb' (by rw [f1, e2])
        exact ⟨i2, x2, f1, by
          rw [core_other i2 hne (by have := coreAt_lt f2; omega)]
          exact f2, f3, f4, f5⟩)
    (by
      intro i0
      constructor
      · intro hi0
        rcases mem_insAt.mp hi0 with e | hold
        · rw [e]
          exact ⟨_, p + 1, _, hnew_mem, get?_insAt_self _ _ (by omega), MKind.slot_reslot _ _⟩
        · obtain ⟨c0, q, b0, hc0, hb0, hs0⟩ := (h.live i0).mp hold
          obtain ⟨j, hj⟩ := mem_get? hc0
          by_cases ej : j = ci
          · rw [ej, hc] at hj
            have ec : c = c0 := Option.some.inj hj
            rw [← ec] at hb0
            by_cases hq : q < p + 1
            · exact ⟨_, q, b0, hnew_mem, by
                show (insAt c.blocks (p + 1) _)[q]? = some b0
                rw [get?_insAt_lt _ _ hq (by omega)]
                exact hb0, hs0⟩
            · exact ⟨_, q + 1, b0, hnew_mem, by
                show (insAt c.blocks (p + 1) _)[q + 1]? = some b0
                rw [get?_insAt_gt _ _ (by omega : p + 1 ≤ q)]
                exact hb0, hs0⟩
          · exact ⟨c0, q, b0, upd_mem_other ej hj, hb0, hs0⟩
      · rintro ⟨c', q, b', hc', hb', hs'⟩
        apply mem_insAt.mpr
        rcases hcl c' hc' with e | ⟨j, _, hcj⟩
        · rw [e] at hb'
          rcases get?_insAt_cases (by omega : p + 1 ≤ c.blocks.length) hb' with
            ⟨_, hb0⟩ | ⟨_, eb⟩ | ⟨q', _, _, hb0⟩
          · exact Or.inr ((h.live i0).mpr ⟨c, q, b', hcm, hb0, hs'⟩)
          · rw [eb, MKind.slot_reslot] at hs'
            exact Or.inl (Option.some.inj hs').symm
          · exact Or.inr ((h.live i0).mpr ⟨c, q', b', hcm, hb0, hs'⟩)
        · exact Or.inr ((h.live i0).mpr ⟨c', q, b', get?_mem hcj, hb', hs'⟩))
    (by
      intro i0 y hi0 hy hgc
      rcases mem_insAt.mp hi0 with e | hold
      · rw [e, core_n] at hy
        rw [← Option.some.inj hy] at hgc ⊢
        exact h.gc i x hi hx hgc
      · by_cases e : i0 = i
        · rw [e, core_i] at hy
          rw [← Option.some.inj hy] at hgc ⊢
          exact h.gc i x hi hx hgc
        · rw [core_other i0 e (by have := h.chain.bound i0 hold; omega)] at hy
          exact h.gc i0 y hold hy hgc)
  exact ⟨key.1, key.2, core_i, core_n, core_other, hlen⟩

/-! ### A split is `YoctoSpec.split` -/

theorem take_unitChars (f : Id → Char) (c : Nat) :
    ∀ (n d k : Nat), d ≤ n → (unitChars f c k n).take d = unitChars f c k d := by
  intro n
  induction n with
  | zero =>
    intro d k hd
    have e : d = 0 := by omega
    rw [e]
    rfl
  | succ n ih =>
    intro d k hd
    cases d with
    | zero => rfl
    | succ d' =>
      show f ⟨c, k⟩ :: (unitChars f c (k + 1) n).take d' = f ⟨c, k⟩ :: unitChars f c (k + 1) d'
      rw [ih d' (k + 1) (by omega)]

theorem drop_unitChars (f : Id → Char) (c : Nat) :
    ∀ (n d k : Nat), d ≤ n → (unitChars f c k n).drop d = unitChars f c (k + d) (n - d) := by
  intro n
  induction n with
  | zero =>
    intro d k hd
    have e : d = 0 := by omega
    rw [e]
    rfl
  | succ n ih =>
    intro d k hd
    cases d with
    | zero => rfl
    | succ d' =>
      show (unitChars f c (k + 1) n).drop d' = unitChars f c (k + (d' + 1)) (n + 1 - (d' + 1))
      rw [ih d' (k + 1) (by omega)]
      have e1 : k + 1 + d' = k + (d' + 1) := by omega
      have e2 : n - d' = n + 1 - (d' + 1) := by omega
      rw [e1, e2]

theorem blockOf_leftPart (f : Id → Char) (x : MItem) {d : Nat} (hd : d ≤ x.len) :
    (blockOf f x).leftPart d = blockOf f { x with len := d } := by
  cases hg : x.gc with
  | true => simp [Block.leftPart, blockOf, hg, Content.take, Nat.min_eq_left hd]
  | false => simp [Block.leftPart, blockOf, hg, Content.take, take_unitChars f _ _ _ _ hd]

theorem blockOf_rightPart (f : Id → Char) (x : MItem) {d : Nat} (hd : d ≤ x.len) :
    (blockOf f x).rightPart d = blockOf f (x.rightHalf d) := by
  cases hg : x.gc with
  | true => simp [Block.rightPart, blockOf, MItem.rightHalf, hg, Content.drop]
  | false =>
    simp [Block.rightPart, blockOf, MItem.rightHalf, hg, Content.drop, drop_unitChars f _ _ _ _ hd]

/-- A block that does not hold `z` strictly inside is not split at `z`. -/
theorem splitBlock_not {z : Id} {B : Block}
    (h : ¬ (z.client = B.id.client ∧ B.id.clock < z.clock ∧ z.clock < B.id.clock + B.len)) :
    splitBlock z B = [B] := by
  unfold splitBlock
  rw [ite_eq_right h]

/-- `split_node` is `YoctoSpec.split` at the first clock of the right half. -/
theorem blocks_splitNode {f : Id → Char} {s : MStore} (h : WF s) {ci p i d : Nat} {c : MClient}
    {b : MBlock} {x : MItem} (hc : s.clients[ci]? = some c) (hb : c.blocks[p]? = some b)
    (hs : b.kind.slot = some i) (hx : coreAt s.items i = some x) (hd0 : 0 < d) (hd : d < x.len) :
    blocks f (splitNode s ci p i d) = YoctoSpec.split (blocks f s) ⟨c.client, b.clock + d⟩ := by
  obtain ⟨k, hk, _, hord, core_i, core_n, core_other, _⟩ := splitNode_spec h hc hb hs hx hd0 hd
  obtain ⟨i', x', e1, e2, e3, _⟩ := h.block_item (get?_mem hc) hb
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei, hx] at e2
  have ex : x' = x := (Option.some.inj e2).symm
  rw [ex] at e3
  have hxc : x.id.client = c.client := by rw [e3]
  have hxk : x.id.clock = b.clock := by rw [e3]
  have hi : i ∈ order s := get?_mem hk
  unfold blocks YoctoSpec.split
  rw [hord, map_insAt_after (blockAt f (splitNode s ci p i d).items) s.items.length (order s) k i
    h.chain.nodup hk, flatMap_map]
  apply flatMap_congr_mem
  intro j hj
  by_cases e : j = i
  · rw [ite_eq_left e, e, blockAt_of_core core_i, blockAt_of_core core_n, blockAt_of_core hx]
    have hcond : (⟨c.client, b.clock + d⟩ : Id).client = (blockOf f x).id.client ∧
        (blockOf f x).id.clock < (⟨c.client, b.clock + d⟩ : Id).clock ∧
        (⟨c.client, b.clock + d⟩ : Id).clock < (blockOf f x).id.clock + (blockOf f x).len := by
      rw [blockOf_len]
      show c.client = x.id.client ∧ x.id.clock < b.clock + d ∧ b.clock + d < x.id.clock + x.len
      exact ⟨hxc.symm, by omega, by omega⟩
    unfold splitBlock
    rw [ite_eq_left hcond]
    have ek : (⟨c.client, b.clock + d⟩ : Id).clock - (blockOf f x).id.clock = d := by
      show b.clock + d - x.id.clock = d
      omega
    rw [ek]
    show _ = [(blockOf f x).leftPart d, (blockOf f x).rightPart d]
    rw [blockOf_leftPart f x (Nat.le_of_lt hd), blockOf_rightPart f x (Nat.le_of_lt hd)]
  · rw [ite_eq_right e]
    have hjn : j ≠ s.items.length := by
      have := h.chain.bound j hj
      omega
    obtain ⟨y, hy⟩ := h.core_of_mem hj
    have hy' : coreAt (splitNode s ci p i d).items j = some y := by
      rw [core_other j e hjn]
      exact hy
    rw [blockAt_of_core hy', blockAt_of_core hy]
    refine (splitBlock_not ?_).symm
    rintro ⟨h1, h2, h3⟩
    rw [blockOf_len] at h3
    have h1' : c.client = y.id.client := h1
    have h2' : y.id.clock < b.clock + d := h2
    have h3' : b.clock + d < y.id.clock + y.len := h3
    exact e (h.slot_unique (z := ⟨c.client, b.clock + d⟩) hj hi hy hx h1' (Nat.le_of_lt h2') h3'
      hxc.symm (by show x.id.clock ≤ b.clock + d; omega)
      (by show b.clock + d < x.id.clock + x.len; omega))

/-- A split where no block holds the clock strictly inside changes nothing. -/
theorem split_blocks_none {f : Id → Char} {s : MStore} (h : WF s) {z : Id}
    (hz : ∀ (i : Nat) (x : MItem), i ∈ order s → coreAt s.items i = some x →
      ¬ (z.client = x.id.client ∧ x.id.clock < z.clock ∧ z.clock < x.id.clock + x.len)) :
    YoctoSpec.split (blocks f s) z = blocks f s := by
  unfold blocks YoctoSpec.split
  rw [flatMap_map, ← flatMap_singleton (blockAt f s.items) (order s)]
  apply flatMap_congr_mem
  intro j hj
  obtain ⟨y, hy⟩ := h.core_of_mem hj
  rw [blockAt_of_core hy]
  apply splitBlock_not
  rw [blockOf_len]
  exact hz j y hj hy

/-! ## Linking a new item -/

/-- `ensure_client` for a client that has no timeline yet. -/
def pushClient (s : MStore) (client : Nat) : MStore :=
  { s with clients := s.clients ++ [⟨client, [], 0⟩] }

theorem pushClient_spec {s : MStore} (h : WF s) {client : Nat}
    (hnew : ∀ c : MClient, c ∈ s.clients → c.client ≠ client) :
    WF (pushClient s client) ∧ order (pushClient s client) = order s := by
  have hmem : ∀ c : MClient, c ∈ (pushClient s client).clients →
      c ∈ s.clients ∨ c = ⟨client, [], 0⟩ := by
    intro c hc
    rcases List.mem_append.mp hc with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by simpa using h1)
  refine WF.of_order (s := pushClient s client) (order s) h.chain ?_ ?_ ?_ ?_ h.gc
  · intro p q a b hpq ha hb
    rcases get?_snoc_cases ha with ⟨_, ha'⟩ | ⟨hp, _⟩
    · rcases get?_snoc_cases hb with ⟨_, hb'⟩ | ⟨_, eb⟩
      · exact h.distinct p q a b hpq ha' hb'
      · rw [eb]
        exact hnew a (get?_mem ha')
    · have := get?_lt hb
      simp only [pushClient, List.length_append, List.length_cons, List.length_nil] at this
      omega
  · intro c hc
    rcases hmem c hc with h1 | h1
    · exact h.timeline c h1
    · rw [h1]
      exact ⟨fun _ _ _ _ _ ha _ => by simp at ha, fun _ _ ha => by simp at ha⟩
  · intro c p b hc hb
    rcases hmem c hc with h1 | h1
    · exact h.block c p b h1 hb
    · rw [h1] at hb
      simp at hb
  · intro i
    rw [h.live i]
    constructor
    · rintro ⟨c, p, b, hc, hb, hs⟩
      exact ⟨c, p, b, List.mem_append_left _ hc, hb, hs⟩
    · rintro ⟨c, p, b, hc, hb, hs⟩
      rcases hmem c hc with h1 | h1
      · exact ⟨c, p, b, h1, hb, hs⟩
      · rw [h1] at hb
        simp at hb

/-- The timeline of a client with one more block at its end. -/
def MClient.appended (c : MClient) (nb : MBlock) (stop : Nat) : MClient :=
  { c with blocks := c.blocks ++ [nb], stop := stop }

/-- `link`: the item `x` takes the next slot, right after `prev` in the
sequence and at the end of the timeline `ci`. -/
def linkNew (s : MStore) (ci : Nat) (prev : Option Nat) (x : MItem) : MStore :=
  { items := linkItems s.items s.start prev x
    start := linkStart s.items s.start prev
    clients := upd s.clients ci (fun c =>
      c.appended ⟨x.id.clock, MKind.item s.items.length⟩ (x.id.clock + x.len)) }

/-- A block that continues a timeline keeps it. -/
theorem TimelineWF.append {blocks : List MBlock} {stop : Nat} (h : TimelineWF blocks stop)
    {nb : MBlock} {stop' : Nat} (hcont : blocks = [] ∨ stop = nb.clock) (hlt : nb.clock < stop') :
    TimelineWF (blocks ++ [nb]) stop' := by
  have old_lt : ∀ (q : Nat) (a : MBlock), blocks[q]? = some a → a.clock < nb.clock := by
    intro q a ha
    rcases hcont with e | e
    · rw [e] at ha
      simp at ha
    · rw [← e]
      exact h.below q a ha
  constructor
  · intro q r a c hqr ha hc
    rcases get?_snoc_cases ha with ⟨_, ha'⟩ | ⟨hq, _⟩
    · rcases get?_snoc_cases hc with ⟨_, hc'⟩ | ⟨_, ec⟩
      · exact h.sorted q r a c hqr ha' hc'
      · rw [ec]
        exact old_lt q a ha'
    · have := get?_lt hc
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega
  · intro q a ha
    rcases get?_snoc_cases ha with ⟨_, ha'⟩ | ⟨_, ea⟩
    · have := old_lt q a ha'
      omega
    · rw [ea]
      exact hlt

theorem endAt_snoc_lt {blocks : List MBlock} {q : Nat} (nb : MBlock) (stop stop' : Nat)
    (h : q + 1 < blocks.length) : endAt (blocks ++ [nb]) stop' q = endAt blocks stop q := by
  unfold endAt
  rw [get?_append_left h]
  obtain ⟨a, ha⟩ := get?_some h
  rw [ha]

theorem endAt_snoc_last {blocks : List MBlock} {q : Nat} (nb : MBlock) (stop' : Nat)
    (h : q + 1 = blocks.length) : endAt (blocks ++ [nb]) stop' q = nb.clock := by
  unfold endAt
  rw [h, get?_snoc_last]

theorem endAt_snoc_new (blocks : List MBlock) (nb : MBlock) (stop' : Nat) :
    endAt (blocks ++ [nb]) stop' blocks.length = stop' := by
  unfold endAt
  rw [get?_none (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]

theorem endAt_last {blocks : List MBlock} {q : Nat} (stop : Nat) (h : q + 1 = blocks.length) :
    endAt blocks stop q = stop := by
  unfold endAt
  rw [get?_none (by omega)]

/-- Linking a new item keeps the invariant: the new slot is at position `k`
of the sequence, and no other item changes. -/
theorem linkNew_spec {s : MStore} (h : WF s) {ci k : Nat} {c : MClient} {x : MItem}
    (hc : s.clients[ci]? = some c) (hcl : c.client = x.id.client)
    (hcont : c.blocks = [] ∨ c.stop = x.id.clock) (hlen : 0 < x.len)
    (hdel : x.deleted = false) (hgc : x.gc = false) (hk : k ≤ (order s).length) :
    WF (linkNew s ci (prevAt (order s) k) x) ∧
      order (linkNew s ci (prevAt (order s) k) x) = insAt (order s) k s.items.length ∧
      coreAt (linkNew s ci (prevAt (order s) k) x).items s.items.length = some x.core ∧
      (∀ j, j ≠ s.items.length →
        coreAt (linkNew s ci (prevAt (order s) k) x).items j = coreAt s.items j) ∧
      (linkNew s ci (prevAt (order s) k) x).items.length = s.items.length + 1 := by
  have hcm : c ∈ s.clients := get?_mem hc
  have htl := h.timeline c hcm
  have core_new : ∀ j, coreAt (linkNew s ci (prevAt (order s) k) x).items j =
      if j = s.items.length then some x.core else coreAt s.items j := fun j => coreAt_linkItems _ _ _ _ j
  have core_n : coreAt (linkNew s ci (prevAt (order s) k) x).items s.items.length = some x.core := by
    rw [core_new, ite_eq_left rfl]
  have core_other : ∀ j, j ≠ s.items.length →
      coreAt (linkNew s ci (prevAt (order s) k) x).items j = coreAt s.items j := by
    intro j hj
    rw [core_new, ite_eq_right hj]
  have hch : Chain (linkNew s ci (prevAt (order s) k) x).items
      (linkNew s ci (prevAt (order s) k) x).start (insAt (order s) k s.items.length) :=
    h.chain.link hk x
  have hcl' : ∀ c', c' ∈ (linkNew s ci (prevAt (order s) k) x).clients →
      c' = c.appended ⟨x.id.clock, MKind.item s.items.length⟩ (x.id.clock + x.len) ∨
      ∃ j, j ≠ ci ∧ s.clients[j]? = some c' := by
    intro c' hc'
    rcases mem_upd hc' with ⟨a, ha, e⟩ | hj
    · rw [hc] at ha
      have ea : c = a := Option.some.inj ha
      rw [← ea] at e
      exact Or.inl e
    · exact Or.inr hj
  have hnew_mem : c.appended ⟨x.id.clock, MKind.item s.items.length⟩ (x.id.clock + x.len) ∈
      (linkNew s ci (prevAt (order s) k) x).clients :=
    upd_mem_self (f := fun c : MClient =>
      c.appended ⟨x.id.clock, MKind.item s.items.length⟩ (x.id.clock + x.len)) hc
  have key := WF.of_order (s := linkNew s ci (prevAt (order s) k) x)
    (insAt (order s) k s.items.length) hch
    (by
      intro p' q' a' b' hpq ha' hb'
      have pre : ∀ (j : Nat) (c' : MClient),
          (linkNew s ci (prevAt (order s) k) x).clients[j]? = some c' →
          ∃ c0, s.clients[j]? = some c0 ∧ c'.client = c0.client := by
        intro j c' hj
        rcases get?_upd_cases hj with ⟨ej, a, ha, e⟩ | ⟨_, hj'⟩
        · exact ⟨a, by rw [ej]; exact ha, by rw [e]; rfl⟩
        · exact ⟨c', hj', rfl⟩
      obtain ⟨a0, ha0, ea⟩ := pre p' a' ha'
      obtain ⟨b0, hb0, eb⟩ := pre q' b' hb'
      rw [ea, eb]
      exact h.distinct p' q' a0 b0 hpq ha0 hb0)
    (by
      intro c' hc'
      rcases hcl' c' hc' with e | ⟨j, _, hj⟩
      · rw [e]
        exact htl.append hcont (by show x.id.clock < x.id.clock + x.len; omega)
      · exact h.timeline c' (get?_mem hj))
    (by
      intro c' q b' hc' hb'
      rcases hcl' c' hc' with e | ⟨j, hj, hcj⟩
      · rw [e] at hb' ⊢
        rcases get?_snoc_cases hb' with ⟨hq, hb0⟩ | ⟨hq, eb⟩
        · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c q b' hcm hb0
          refine ⟨i2, x2, f1, ?_, f3, ?_, f5⟩
          · rw [core_other i2 (by have := coreAt_lt f2; omega)]
            exact f2
          · show x2.len = endAt (c.blocks ++ [_]) (x.id.clock + x.len) q - b'.clock
            by_cases hlast : q + 1 = c.blocks.length
            · rw [endAt_snoc_last _ _ hlast]
              rw [endAt_last c.stop hlast] at f4
              rcases hcont with e0 | e0
              · rw [e0] at hq
                simp at hq
              · show x2.len = x.id.clock - b'.clock
                rw [← e0]
                exact f4
            · rw [endAt_snoc_lt _ c.stop _ (by omega)]
              exact f4
        · rw [hq, eb]
          refine ⟨s.items.length, x.core, rfl, core_n, ?_, ?_, ?_⟩
          · show x.id = ⟨c.client, x.id.clock⟩
            rw [hcl]
          · show x.len = endAt (c.blocks ++ [_]) (x.id.clock + x.len) c.blocks.length - x.id.clock
            rw [endAt_snoc_new]
            omega
          · exact hdel
      · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c' q b' (get?_mem hcj) hb'
        exact ⟨i2, x2, f1, by
          rw [core_other i2 (by have := coreAt_lt f2; omega)]
          exact f2, f3, f4, f5⟩)
    (by
      intro i0
      constructor
      · intro hi0
        rcases mem_insAt.mp hi0 with e | hold
        · rw [e]
          exact ⟨_, c.blocks.length, _, hnew_mem, get?_snoc_last _ _, rfl⟩
        · obtain ⟨c0, q, b0, hc0, hb0, hs0⟩ := (h.live i0).mp hold
          obtain ⟨j, hj⟩ := mem_get? hc0
          by_cases ej : j = ci
          · rw [ej, hc] at hj
            have ec : c = c0 := Option.some.inj hj
            rw [← ec] at hb0
            exact ⟨_, q, b0, hnew_mem, by
              show (c.blocks ++ [_])[q]? = some b0
              rw [get?_append_left (get?_lt hb0)]
              exact hb0, hs0⟩
          · exact ⟨c0, q, b0, upd_mem_other ej hj, hb0, hs0⟩
      · rintro ⟨c', q, b', hc', hb', hs'⟩
        apply mem_insAt.mpr
        rcases hcl' c' hc' with e | ⟨j, _, hcj⟩
        · rw [e] at hb'
          rcases get?_snoc_cases hb' with ⟨_, hb0⟩ | ⟨_, eb⟩
          · exact Or.inr ((h.live i0).mpr ⟨c, q, b', hcm, hb0, hs'⟩)
          · rw [eb] at hs'
            exact Or.inl (Option.some.inj hs').symm
        · exact Or.inr ((h.live i0).mpr ⟨c', q, b', get?_mem hcj, hb', hs'⟩))
    (by
      intro i0 y hi0 hy hg
      rcases mem_insAt.mp hi0 with e | hold
      · rw [e, core_n] at hy
        rw [← Option.some.inj hy] at hg
        have hg' : x.gc = true := hg
        rw [hgc] at hg'
        cases hg'
      · rw [core_other i0 (by have := h.chain.bound i0 hold; omega)] at hy
        exact h.gc i0 y hold hy hg)
  exact ⟨key.1, key.2, core_n, core_other, length_linkItems _ _ _ _⟩

/-! ### Linking is `insertAfterB` -/

theorem get?_blocks (f : Id → Char) (s : MStore) (j : Nat) :
    (blocks f s)[j]? = ((order s)[j]?).map (blockAt f s.items) :=
  get?_map _ _ _

/-- The blocks of the sequence have distinct ids. -/
theorem blocks_id_inj {f : Id → Char} {s : MStore} (h : WF s) {j1 j2 i1 i2 : Nat}
    (h1 : (order s)[j1]? = some i1) (h2 : (order s)[j2]? = some i2)
    (e : (blockAt f s.items i1).id = (blockAt f s.items i2).id) : j1 = j2 := by
  obtain ⟨x1, hx1⟩ := h.core_of_mem (get?_mem h1)
  obtain ⟨x2, hx2⟩ := h.core_of_mem (get?_mem h2)
  rw [blockAt_of_core hx1, blockAt_of_core hx2] at e
  have e' : x1.id = x2.id := e
  obtain ⟨_, _, _, _, _, _, _, _, _, _, l1⟩ := h.item_block (get?_mem h1) hx1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, l2⟩ := h.item_block (get?_mem h2) hx2
  have ei : i1 = i2 := h.slot_unique (z := x1.id) (get?_mem h1) (get?_mem h2) hx1 hx2 rfl
    (Nat.le_refl _) (by omega) (by rw [e']) (by rw [e']; exact Nat.le_refl _) (by rw [e']; omega)
  rw [ei] at h1
  exact h.chain.pos_unique h1 h2

theorem insertAfterBId_eq_insAt {y : Id} (B : Block) :
    ∀ (bs : List Block) (k : Nat) (B0 : Block), bs[k]? = some B0 → B0.id = y →
      (∀ (j : Nat) (Bj : Block), j < k → bs[j]? = some Bj → Bj.id ≠ y) →
      insertAfterBId y B bs = insAt bs (k + 1) B := by
  intro bs
  induction bs with
  | nil =>
    intro k B0 h
    simp at h
  | cons a t ih =>
    intro k B0 hk hy hne
    cases k with
    | zero =>
      have e : a = B0 := by simpa using hk
      rw [insertAfterBId, ite_eq_left (by rw [e]; exact hy)]
      simp [insAt]
    | succ k' =>
      have hk' : t[k']? = some B0 := by simpa using hk
      have ha : ¬ a.id = y := hne 0 a (by omega) (by simp)
      rw [insertAfterBId, ite_eq_right ha,
        ih k' B0 hk' hy (fun j Bj hj hBj => hne (j + 1) Bj (by omega) (by simpa using hBj))]
      simp [insAt]

/-- The id of the item before position `k` of the sequence. -/
def prevId (f : Id → Char) (s : MStore) (k : Nat) : Option Id :=
  (prevAt (order s) k).map (fun i => (blockAt f s.items i).id)

/-- `link` is `insertAfterB`: the block of the new item goes right after the
block of `prev`. -/
theorem blocks_linkNew {f : Id → Char} {s : MStore} (h : WF s) {ci k : Nat} {c : MClient}
    {x : MItem} (hc : s.clients[ci]? = some c) (hcl : c.client = x.id.client)
    (hcont : c.blocks = [] ∨ c.stop = x.id.clock) (hlen : 0 < x.len)
    (hdel : x.deleted = false) (hgc : x.gc = false) (hk : k ≤ (order s).length) :
    blocks f (linkNew s ci (prevAt (order s) k) x) =
      insertAfterB (prevId f s k) (blockOf f x) (blocks f s) := by
  obtain ⟨_, hord, core_n, core_other, _⟩ := linkNew_spec h hc hcl hcont hlen hdel hgc hk
  have hm : (order s).map (blockAt f (linkNew s ci (prevAt (order s) k) x).items) =
      (order s).map (blockAt f s.items) := by
    apply map_congr_mem
    intro j hj
    obtain ⟨y, hy⟩ := h.core_of_mem hj
    have hy' : coreAt (linkNew s ci (prevAt (order s) k) x).items j = some y := by
      rw [core_other j (by have := h.chain.bound j hj; omega)]
      exact hy
    rw [blockAt_of_core hy', blockAt_of_core hy]
  have hmap : blocks f (linkNew s ci (prevAt (order s) k) x) = insAt (blocks f s) k (blockOf f x) := by
    unfold blocks
    rw [hord, map_insAt, blockAt_of_core core_n, blockOf_core, hm]
  rw [hmap]
  cases k with
  | zero => simp [insAt, prevId, prevAt, insertAfterB]
  | succ k' =>
    obtain ⟨i, hi⟩ := get?_some (show k' < (order s).length by omega)
    have hp : prevId f s (k' + 1) = some (blockAt f s.items i).id := by
      show ((order s)[k']?).map _ = _
      rw [hi]
      rfl
    rw [hp]
    show _ = insertAfterBId _ _ _
    symm
    apply insertAfterBId_eq_insAt (blockOf f x) (blocks f s) k' (blockAt f s.items i)
    · rw [get?_blocks, hi]
      rfl
    · rfl
    · intro j Bj hj hBj
      rw [get?_blocks] at hBj
      obtain ⟨i', hi'⟩ := get?_some (show j < (order s).length by omega)
      rw [hi'] at hBj
      have eB : blockAt f s.items i' = Bj := Option.some.inj hBj
      intro e
      rw [← eB] at e
      have := blocks_id_inj h hi' hi e
      omega

/-! ## Lookups -/

theorem ownerB_some_of {z : Id} : ∀ {bs : List Block} {B : Block}, B ∈ bs → B.contains z = true →
    (∀ B', B' ∈ bs → B'.contains z = true → B'.id = B.id) → ownerB bs z = some B.id := by
  intro bs
  induction bs with
  | nil =>
    intro B hB
    cases hB
  | cons a t ih =>
    intro B hB hc hu
    rw [ownerB]
    by_cases ha : a.contains z = true
    · rw [ite_eq_left ha, hu a (List.mem_cons_self ..) ha]
    · rw [ite_eq_right ha]
      rcases List.mem_cons.mp hB with e | hB'
      · rw [e] at hc
        exact absurd hc ha
      · exact ih hB' hc (fun B' hB'' hc' => hu B' (List.mem_cons_of_mem _ hB'') hc')

theorem ownerB_none_of {z : Id} : ∀ {bs : List Block}, (∀ B, B ∈ bs → ¬ B.contains z = true) →
    ownerB bs z = none := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons a t ih =>
    intro hn
    rw [ownerB, ite_eq_right (hn a (List.mem_cons_self ..))]
    exact ih (fun B hB => hn B (List.mem_cons_of_mem _ hB))

theorem blockOf_contains {f : Id → Char} {x : MItem} {z : Id} :
    (blockOf f x).contains z = true ↔
      z.client = x.id.client ∧ x.id.clock ≤ z.clock ∧ z.clock < x.id.clock + x.len := by
  unfold Block.contains
  rw [blockOf_len]
  exact decide_eq_true_iff

/-- `origin_owner` of the block sequence is the lookup on the timelines: the
start of the block that holds the id. -/
theorem ownerB_blocks_at {f : Id → Char} {s : MStore} (h : WF s) {z : Id} {c : MClient} {p : Nat}
    {b : MBlock} (ha : At s z c p b) : ownerB (blocks f s) z = some ⟨z.client, b.clock⟩ := by
  obtain ⟨i, x, _, hx, hid, hl, _, hi, _⟩ := ha.item h
  have hlt := ha.lt
  have hge := ha.ge
  have hxc : x.id.client = z.client := by rw [hid]
  have hxk : x.id.clock = b.clock := by rw [hid]
  have hB : blockOf f x ∈ blocks f s :=
    List.mem_map.mpr ⟨i, hi, blockAt_of_core hx⟩
  have hc : (blockOf f x).contains z = true :=
    blockOf_contains.mpr ⟨hxc.symm, by omega, by omega⟩
  have := ownerB_some_of hB hc (by
    intro B' hB' hc'
    obtain ⟨j, y, hj, hy, e⟩ := mem_blocks h hB'
    rw [e] at hc' ⊢
    obtain ⟨h1, h2, h3⟩ := blockOf_contains.mp hc'
    have ej : j = i := h.slot_unique hj hi hy hx h1 h2 h3 hxc.symm (by omega) (by omega)
    rw [ej, hx] at hy
    rw [← Option.some.inj hy])
  rw [this]
  show some x.id = _
  rw [hid]

theorem ownerB_blocks_none {f : Id → Char} {s : MStore} (h : WF s) {z : Id}
    (hno : ∀ (c : MClient) (p : Nat) (b : MBlock), ¬ At s z c p b) : ownerB (blocks f s) z = none := by
  apply ownerB_none_of
  intro B hB hc
  obtain ⟨j, y, hj, hy, e⟩ := mem_blocks h hB
  rw [e] at hc
  obtain ⟨h1, h2, h3⟩ := blockOf_contains.mp hc
  obtain ⟨c, p, b, ha, _⟩ := h.at_of_contains hj hy h1 h2 h3
  exact hno c p b ha

/-! ## The conflict scan -/

/-- What `scan_step` answers for a candidate. -/
inductive MStep where
  | stop
  | skip
  | take

/-- `scan_step`: the two sets already hold the id of the candidate. -/
def scanStep (owner : Id → Option Id) (thisId : Id) (thisL thisR : Option Id) (cand : MItem)
    (before conflicting : List Id) : MStep :=
  if thisL = cand.originL then
    if cand.id.client < thisId.client then MStep.take
    else if thisR = cand.originR then MStep.stop
    else MStep.skip
  else
    match cand.originL with
    | none => MStep.stop
    | some cl =>
      match owner cl with
      | none => MStep.stop
      | some o =>
        if o ∈ before then
          if o ∈ conflicting then MStep.skip else MStep.take
        else MStep.stop

/-- `find_conflict_left`, branch for branch as `YoctoSpec.findConflictLeft`:
`conflict` is the candidate, `left` the neighbour found so far. -/
def scanLoop (items : List MItem) (owner : Id → Option Id) (thisId : Id) (thisL thisR : Option Id)
    (right : Option Nat) : Nat → Option Nat → Option Nat → List Id → List Id → Option Nat
  | 0, left, _, _, _ => left
  | _ + 1, left, none, _, _ => left
  | fuel + 1, left, some cur, before, conflicting =>
    if right = some cur then left
    else
      if thisL = (itemAt items cur).originL then
        if (itemAt items cur).id.client < thisId.client then
          scanLoop items owner thisId thisL thisR right fuel (some cur) (itemAt items cur).right
            ((itemAt items cur).id :: before) []
        else if thisR = (itemAt items cur).originR then left
        else
          scanLoop items owner thisId thisL thisR right fuel left (itemAt items cur).right
            ((itemAt items cur).id :: before) ((itemAt items cur).id :: conflicting)
      else
        match (itemAt items cur).originL with
        | none => left
        | some cl =>
          match owner cl with
          | none => left
          | some o =>
            if o ∈ (itemAt items cur).id :: before then
              if o ∈ (itemAt items cur).id :: conflicting then
                scanLoop items owner thisId thisL thisR right fuel left (itemAt items cur).right
                  ((itemAt items cur).id :: before) ((itemAt items cur).id :: conflicting)
              else
                scanLoop items owner thisId thisL thisR right fuel (some cur) (itemAt items cur).right
                  ((itemAt items cur).id :: before) []
            else left

/-- The candidate an item is for the scan (`ConflictItem`). -/
def MItem.toItem (x : MItem) : Item := ⟨x.id, x.originL, x.originR⟩

theorem rightOf_itemAt {items : List MItem} {i : Nat} (h : i < items.length) :
    rightOf items i = (itemAt items i).right := by
  unfold rightOf itemAt
  obtain ⟨x, hx⟩ := get?_some h
  rw [hx]
  rfl

/-- One candidate: the scan over slots and `findConflictLeft` take the same
branch. -/
theorem scanLoop_step_eq (items : List MItem) (owner : Id → Option Id) (this : Item)
    (rightS : Option Nat) (rightId : Option Id) (fuel : Nat) (left : Option Nat) (cur : Nat)
    (before conf : List Id) (rest : List Item) (g : Option Nat → Option Id) (c : Item)
    (hid : (itemAt items cur).id = c.id) (hl : (itemAt items cur).originL = c.left)
    (hrt : (itemAt items cur).originR = c.right)
    (hr : rightS = some cur ↔ rightId = some c.id)
    (hrec : ∀ (left' : Option Nat) (before' conf' : List Id),
      g (scanLoop items owner this.id this.left this.right rightS fuel left'
        (itemAt items cur).right before' conf') =
        findConflictLeft this rightId owner rest (g left') before' conf')
    (hg : g (some cur) = some c.id) :
    g (scanLoop items owner this.id this.left this.right rightS (fuel + 1) left (some cur) before
      conf) =
      findConflictLeft this rightId owner (c :: rest) (g left) before conf := by
  rw [scanLoop, findConflictLeft, hid, hl, hrt]
  by_cases h0 : rightS = some cur
  · rw [ite_eq_left h0, ite_eq_left (hr.mp h0)]
  · rw [ite_eq_right h0, ite_eq_right (fun e => h0 (hr.mpr e))]
    by_cases h1 : this.left = c.left
    · rw [ite_eq_left h1, ite_eq_left h1]
      by_cases h2 : c.id.client < this.id.client
      · rw [ite_eq_left h2, ite_eq_left h2, hrec, hg]
      · rw [ite_eq_right h2, ite_eq_right h2]
        by_cases h3 : this.right = c.right
        · rw [ite_eq_left h3, ite_eq_left h3]
        · rw [ite_eq_right h3, ite_eq_right h3]
          exact hrec _ _ _
    · rw [ite_eq_right h1, ite_eq_right h1]
      cases hcl : c.left with
      | none => rfl
      | some cl' =>
        show g (match owner cl' with
          | none => left
          | some o => _) = (match owner cl' with
          | none => g left
          | some o => _)
        cases how : owner cl' with
        | none => rfl
        | some o =>
          show g (if o ∈ c.id :: before then _ else left) = (if o ∈ c.id :: before then _ else g left)
          by_cases h4 : o ∈ c.id :: before
          · rw [ite_eq_left h4, ite_eq_left h4]
            by_cases h5 : o ∈ c.id :: conf
            · rw [ite_eq_left h5, ite_eq_left h5]
              exact hrec _ _ _
            · rw [ite_eq_right h5, ite_eq_right h5, hrec, hg]
          · rw [ite_eq_right h4, ite_eq_right h4]

/-- The scan over slots is `findConflictLeft` over the items of the slots. -/
theorem scanLoop_eq {s : MStore} (h : WF s) (this : Item) (owner : Id → Option Id)
    (rightS : Option Nat) (rightId : Option Id)
    (hright : ∀ i, i ∈ order s → (rightS = some i ↔ rightId = some (itemAt s.items i).id)) :
    ∀ (suf pre : List Nat) (fuel : Nat) (left : Option Nat) (before conf : List Id),
      order s = pre ++ suf → suf.length ≤ fuel →
      (scanLoop s.items owner this.id this.left this.right rightS fuel left suf[0]? before
          conf).map (fun i => (itemAt s.items i).id) =
        findConflictLeft this rightId owner (suf.map (fun i => (itemAt s.items i).toItem))
          (left.map (fun i => (itemAt s.items i).id)) before conf := by
  intro suf
  induction suf with
  | nil =>
    intro pre fuel left before conf _ _
    have e : ([] : List Nat)[0]? = none := by simp
    rw [e]
    cases fuel <;> rfl
  | cons cur t ih =>
    intro pre fuel left before conf he hf
    cases fuel with
    | zero => simp at hf
    | succ fuel' =>
      have hcur : cur ∈ order s := by
        rw [he]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      have hpos : (order s)[pre.length]? = some cur := by
        rw [he]
        simp
      have hnext : (itemAt s.items cur).right = t[0]? := by
        rw [← rightOf_itemAt (h.chain.bound cur hcur), h.chain.right pre.length cur hpos, he]
        have := get?_append_right pre (cur :: t) 1
        simpa using this
      have e0 : (cur :: t)[0]? = some cur := by simp
      rw [e0, List.map_cons]
      apply scanLoop_step_eq s.items owner this rightS rightId fuel' left cur before conf _
        (fun o => o.map (fun i => (itemAt s.items i).id)) (itemAt s.items cur).toItem rfl rfl rfl
        (hright cur hcur)
      · intro left' before' conf'
        rw [hnext]
        exact ih (pre ++ [cur]) fuel' left' before' conf' (by rw [he]; simp)
          (by simp only [List.length_cons] at hf; omega)
      · rfl

/-! ## `split` and `split_after` -/

/-- What an operation that only splits items keeps of the timelines: the
clients in their places, where each timeline ends, and which are empty. -/
structure Frame (s s' : MStore) : Prop where
  len : s'.clients.length = s.clients.length
  client : ∀ (ci : Nat) (c : MClient), s.clients[ci]? = some c →
    ∃ c', s'.clients[ci]? = some c' ∧ c'.client = c.client ∧ c'.stop = c.stop ∧
      (c.blocks = [] ↔ c'.blocks = [])
  items : s.items.length ≤ s'.items.length

theorem Frame.refl (s : MStore) : Frame s s :=
  ⟨rfl, fun _ c hc => ⟨c, hc, rfl, rfl, Iff.rfl⟩, Nat.le_refl _⟩

theorem Frame.trans {s s' s'' : MStore} (h₁ : Frame s s') (h₂ : Frame s' s'') : Frame s s'' := by
  refine ⟨h₂.len.trans h₁.len, ?_, Nat.le_trans h₁.items h₂.items⟩
  intro ci c hc
  obtain ⟨c', hc', e1, e2, e3⟩ := h₁.client ci c hc
  obtain ⟨c'', hc'', f1, f2, f3⟩ := h₂.client ci c' hc'
  exact ⟨c'', hc'', f1.trans e1, f2.trans e2, e3.trans f3⟩

theorem insAt_ne_nil (l : List MBlock) (i : Nat) (a : MBlock) : insAt l i a ≠ [] := by
  intro e
  have := congrArg List.length e
  simp at this

theorem splitNode_frame {s : MStore} {ci p i d : Nat} {c : MClient} {b : MBlock}
    (hc : s.clients[ci]? = some c) (hb : c.blocks[p]? = some b)
    (hlen : (splitNode s ci p i d).items.length = s.items.length + 1) :
    Frame s (splitNode s ci p i d) := by
  refine ⟨length_upd _ _ _, ?_, by omega⟩
  intro cj c0 hc0
  by_cases e : cj = ci
  · rw [e, hc] at hc0
    have ec : c = c0 := Option.some.inj hc0
    refine ⟨_, by rw [e]; show (upd s.clients ci _)[ci]? = _; rw [get?_upd_self, hc]; rfl, ?_, ?_, ?_⟩
    · rw [← ec]
      rfl
    · rw [← ec]
      rfl
    · rw [← ec]
      constructor
      · intro e0
        rw [e0] at hb
        simp at hb
      · intro e0
        exact absurd e0 (insAt_ne_nil _ _ _)
  · exact ⟨c0, by show (upd s.clients ci _)[cj]? = _; rw [get?_upd_ne _ _ e]; exact hc0, rfl, rfl,
      Iff.rfl⟩

/-- What `split` (`split_at_and_get_right`) does for an id the store holds:
the block sequence is split at the id, the slot it returns starts there, and
an item that does not hold the id strictly inside is left as it is. -/
structure SplitOk (s : MStore) (z : Id) (s' : MStore) (slot : Nat) : Prop where
  wf : WF s'
  blocks : ∀ f : Id → Char, blocks f s' = YoctoSpec.split (blocks f s) z
  frame : Frame s s'
  mem : slot ∈ order s'
  starts : ∃ y, coreAt s'.items slot = some y ∧ y.id = z
  keep : ∀ (j : Nat) (x : MItem), j ∈ order s → coreAt s.items j = some x →
    ¬ (z.client = x.id.client ∧ x.id.clock < z.clock ∧ z.clock < x.id.clock + x.len) →
    j ∈ order s' ∧ coreAt s'.items j = some x
  mono : ∀ j : Nat, j ∈ order s → j ∈ order s'

/-- `split` on an id where a block starts changes nothing. -/
theorem splitOk_same {s : MStore} (h : WF s) {z : Id} {c : MClient} {p : Nat} {b : MBlock}
    (ha : At s z c p b) {i : Nat} (hs : b.kind.slot = some i) (hz : z.clock = b.clock) :
    SplitOk s z s i := by
  obtain ⟨i', x, e1, hx, hid, hl, _, hi, _⟩ := ha.item h
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei] at hx hi
  have hxc : x.id.client = z.client := by rw [hid]
  have hxk : x.id.clock = b.clock := by rw [hid]
  refine ⟨h, ?_, Frame.refl s, hi, ⟨x, hx, ?_⟩, fun j y hj hy _ => ⟨hj, hy⟩, fun _ hj => hj⟩
  · intro f
    refine (split_blocks_none h ?_).symm
    rintro j y hj hy ⟨h1, h2, h3⟩
    have ej : j = i := h.slot_unique hj hi hy hx h1 (Nat.le_of_lt h2) h3 hxc.symm (by omega)
      (by have := ha.lt; omega)
    rw [ej, hx] at hy
    rw [← Option.some.inj hy] at h2
    omega
  · rw [hid, ← hz]

/-- `split` on an id inside a block is `split_node`. -/
theorem splitOk_split {s : MStore} (h : WF s) {z : Id} {c : MClient} {p ci : Nat} {b : MBlock}
    (ha : At s z c p b) (hc : s.clients[ci]? = some c) {i : Nat} (hs : b.kind.slot = some i)
    (hz : z.clock ≠ b.clock) :
    SplitOk s z (splitNode s ci p i (z.clock - b.clock)) s.items.length := by
  obtain ⟨i', x, e1, hx, hid, hl, _, hi, _⟩ := ha.item h
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei] at hx hi
  have hxc : x.id.client = z.client := by rw [hid]
  have hxk : x.id.clock = b.clock := by rw [hid]
  have hge := ha.ge
  have hlt := ha.lt
  have hd0 : 0 < z.clock - b.clock := by omega
  have hd : z.clock - b.clock < x.len := by omega
  obtain ⟨k, hk, hwf, hord, core_i, core_n, core_other, hlen⟩ :=
    splitNode_spec h hc ha.block hs hx hd0 hd
  have hzeq : (⟨c.client, b.clock + (z.clock - b.clock)⟩ : Id) = z := by
    have e : b.clock + (z.clock - b.clock) = z.clock := by omega
    rw [e, ha.client]
  refine ⟨hwf, ?_, splitNode_frame hc ha.block hlen, ?_, ⟨_, core_n, ?_⟩, ?_, ?_⟩
  · intro f
    rw [blocks_splitNode h hc ha.block hs hx hd0 hd, hzeq]
  · rw [hord]
    exact mem_insAt.mpr (Or.inl rfl)
  · show (⟨x.id.client, x.id.clock + (z.clock - b.clock)⟩ : Id) = z
    rw [hxc, hxk]
    have e : b.clock + (z.clock - b.clock) = z.clock := by omega
    rw [e]
  · intro j y hj hy hn
    have hji : j ≠ i := by
      intro e
      rw [e, hx] at hy
      rw [← Option.some.inj hy] at hn
      exact hn ⟨hxc.symm, by omega, by omega⟩
    refine ⟨by rw [hord]; exact mem_insAt.mpr (Or.inr hj), ?_⟩
    rw [core_other j hji (by have := h.chain.bound j hj; omega)]
    exact hy
  · intro j hj
    rw [hord]
    exact mem_insAt.mpr (Or.inr hj)

/-- What `split_after` (`split_at_and_get_left`) does for an id the store
holds: the block sequence is split after the id, and the slot it returns ends
there and starts where the block that held the id started. -/
structure SplitAfterOk (s : MStore) (z : Id) (s' : MStore) (slot : Nat) : Prop where
  wf : WF s'
  blocks : ∀ f : Id → Char, blocks f s' = splitAfter (blocks f s) z
  frame : Frame s s'
  mem : slot ∈ order s'
  ends : ∃ (y : MItem) (c : MClient) (p : Nat) (b : MBlock), coreAt s'.items slot = some y ∧
    At s z c p b ∧ y.id.client = z.client ∧ y.id.clock = b.clock ∧ y.id.clock + y.len = z.clock + 1

/-- `split_after` on the last id of a block changes nothing. -/
theorem splitAfterOk_same {s : MStore} (h : WF s) {z : Id} {c : MClient} {p : Nat} {b : MBlock}
    (ha : At s z c p b) {i : Nat} {x : MItem} (hs : b.kind.slot = some i)
    (hx : coreAt s.items i = some x) (hz : ¬ z.clock - b.clock + 1 < x.len) :
    SplitAfterOk s z s i := by
  obtain ⟨i', x', e1, hx', hid, hl, _, hi, _⟩ := ha.item h
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei, hx] at hx'
  have ex : x' = x := (Option.some.inj hx').symm
  rw [ei] at hi
  rw [ex] at hid hl
  have hxc : x.id.client = z.client := by rw [hid]
  have hxk : x.id.clock = b.clock := by rw [hid]
  have hge := ha.ge
  have hlt := ha.lt
  refine ⟨h, ?_, Frame.refl s, hi, ⟨x, c, p, b, hx, ha, hxc, hxk, by omega⟩⟩
  intro f
  unfold splitAfter
  refine (split_blocks_none h ?_).symm
  rintro j y hj hy ⟨h1, h2, h3⟩
  have h1' : z.client = y.id.client := h1
  have h2' : y.id.clock < z.clock + 1 := h2
  have h3' : z.clock + 1 < y.id.clock + y.len := h3
  have ej : j = i := h.slot_unique hj hi hy hx h1' (by omega) (by omega) hxc.symm (by omega)
    (by omega)
  rw [ej, hx] at hy
  rw [← Option.some.inj hy] at h3'
  omega

/-- `split_after` on an id before the end of its block is `split_node`. -/
theorem splitAfterOk_split {s : MStore} (h : WF s) {z : Id} {c : MClient} {p ci : Nat}
    {b : MBlock} (ha : At s z c p b) (hc : s.clients[ci]? = some c) {i : Nat} {x : MItem}
    (hs : b.kind.slot = some i) (hx : coreAt s.items i = some x)
    (hz : z.clock - b.clock + 1 < x.len) :
    SplitAfterOk s z (splitNode s ci p i (z.clock - b.clock + 1)) i := by
  obtain ⟨i', x', e1, hx', hid, hl, _, hi, _⟩ := ha.item h
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei, hx] at hx'
  have ex : x' = x := (Option.some.inj hx').symm
  rw [ei] at hi
  rw [ex] at hid hl
  have hxc : x.id.client = z.client := by rw [hid]
  have hxk : x.id.clock = b.clock := by rw [hid]
  have hge := ha.ge
  obtain ⟨k, hk, hwf, hord, core_i, core_n, core_other, hlen⟩ :=
    splitNode_spec h hc ha.block hs hx (Nat.succ_pos _) hz
  have hzeq : (⟨c.client, b.clock + (z.clock - b.clock + 1)⟩ : Id) = ⟨z.client, z.clock + 1⟩ := by
    have e : b.clock + (z.clock - b.clock + 1) = z.clock + 1 := by omega
    rw [e, ha.client]
  refine ⟨hwf, ?_, splitNode_frame hc ha.block hlen, ?_, ⟨_, c, p, b, core_i, ha, hxc, hxk, ?_⟩⟩
  · intro f
    rw [blocks_splitNode h hc ha.block hs hx (Nat.succ_pos _) hz, hzeq]
    rfl
  · rw [hord]
    exact mem_insAt.mpr (Or.inr hi)
  · show x.id.clock + (z.clock - b.clock + 1) = z.clock + 1
    omega

/-! ## `integrate` -/

/-- `node_id`, the `origin_owner` of the scan: the start of the block that
holds an id. -/
def ownerM (s : MStore) (z : Id) : Option Id := ownerB (blocks (fun _ => 'a') s) z

theorem ownerM_eq {f : Id → Char} {s : MStore} (h : WF s) (z : Id) :
    ownerB (blocks f s) z = ownerM s z := by
  unfold ownerM
  by_cases hex : ∃ (c : MClient) (p : Nat) (b : MBlock), At s z c p b
  · obtain ⟨c, p, b, ha⟩ := hex
    rw [ownerB_blocks_at h ha, ownerB_blocks_at h ha]
  · have hno : ∀ (c : MClient) (p : Nat) (b : MBlock), ¬ At s z c p b :=
      fun c p b ha => hex ⟨c, p, b, ha⟩
    rw [ownerB_blocks_none h hno, ownerB_blocks_none h hno]

theorem ownerM_at {s : MStore} (h : WF s) {z : Id} {c : MClient} {p : Nat} {b : MBlock}
    (ha : At s z c p b) : ownerM s z = some ⟨z.client, b.clock⟩ :=
  ownerB_blocks_at h ha

theorem ownerM_none {s : MStore} (h : WF s) {z : Id}
    (hno : ∀ (c : MClient) (p : Nat) (b : MBlock), ¬ At s z c p b) : ownerM s z = none :=
  ownerB_blocks_none h hno

/-- `needs_scan`. -/
def needsScan (s : MStore) (left right : Option Nat) : Bool :=
  match left with
  | some l => decide (rightOf s.items l ≠ right)
  | none =>
    match right with
    | some r => (leftOf s.items r).isSome
    | none => true

/-- The left neighbour `integrate` links a new item to. -/
def scanM (s : MStore) (thisId : Id) (thisL thisR : Option Id) (left right : Option Nat) :
    Option Nat :=
  if needsScan s left right then
    scanLoop s.items (ownerM s) thisId thisL thisR right s.items.length left
      (nextOf s.items s.start left) [] []
  else left

theorem scanLoop_stop (items : List MItem) (owner : Id → Option Id) (thisId : Id)
    (thisL thisR : Option Id) (right : Option Nat) (fuel : Nat) (left conflict : Option Nat)
    (before conf : List Id) (h : conflict = none ∨ right = conflict) :
    scanLoop items owner thisId thisL thisR right fuel left conflict before conf = left := by
  cases fuel with
  | zero => rfl
  | succ fuel' =>
    cases conflict with
    | none => rfl
    | some cur =>
      rcases h with e | e
      · cases e
      · rw [scanLoop, ite_eq_left e]

/-- Without `needs_scan` the scan would stop at its first candidate. -/
theorem scanM_eq_loop {s : MStore} (h : WF s) (thisId : Id) (thisL thisR : Option Id) {k : Nat}
    (hk : k ≤ (order s).length) {right : Option Nat} (hrmem : ∀ r, right = some r → r ∈ order s) :
    scanM s thisId thisL thisR (prevAt (order s) k) right =
      scanLoop s.items (ownerM s) thisId thisL thisR right s.items.length (prevAt (order s) k)
        (order s)[k]? [] [] := by
  unfold scanM
  rw [h.chain.nextOf_prevAt hk]
  by_cases hn : needsScan s (prevAt (order s) k) right = true
  · rw [ite_eq_left hn]
  · rw [ite_eq_right hn]
    refine (scanLoop_stop _ _ _ _ _ _ _ _ _ _ _ ?_).symm
    cases k with
    | zero =>
      have hn' : ¬ needsScan s none right = true := hn
      cases right with
      | none => exact absurd rfl hn'
      | some r =>
        have hr := hrmem r rfl
        obtain ⟨j, hj⟩ := mem_get? hr
        have hl : leftOf s.items r = none := by
          cases hlo : leftOf s.items r with
          | none => rfl
          | some q =>
            have : needsScan s none (some r) = true := by
              show (leftOf s.items r).isSome = true
              rw [hlo]
              rfl
            exact absurd this hn'
        cases j with
        | zero => exact Or.inr hj.symm
        | succ j' =>
          have := h.chain.left j' r hj
          rw [hl] at this
          have hlt := get?_lt hj
          obtain ⟨q, hq⟩ := get?_some (show j' < (order s).length by omega)
          rw [hq] at this
          cases this
    | succ k' =>
      obtain ⟨l, hl⟩ := get?_some (show k' < (order s).length by omega)
      have e : prevAt (order s) (k' + 1) = some l := hl
      rw [e] at hn
      have hn' : ¬ decide (rightOf s.items l ≠ right) = true := hn
      have heq : rightOf s.items l = right := by
        by_cases e' : rightOf s.items l = right
        · exact e'
        · exact absurd (decide_eq_true e') hn'
      rw [← heq, h.chain.right k' l hl]
      exact Or.inr rfl

/-- The scan only answers slots of the sequence. -/
theorem scanLoop_mem {s : MStore} (h : WF s) (owner : Id → Option Id) (thisId : Id)
    (thisL thisR : Option Id) (right : Option Nat) :
    ∀ (fuel : Nat) (left conflict : Option Nat) (before conf : List Id),
      (∀ i, left = some i → i ∈ order s) → (∀ i, conflict = some i → i ∈ order s) →
      ∀ i, scanLoop s.items owner thisId thisL thisR right fuel left conflict before conf = some i →
        i ∈ order s := by
  intro fuel
  induction fuel with
  | zero =>
    intro left conflict before conf hl _ i hi
    exact hl i hi
  | succ fuel ih =>
    intro left conflict before conf hl hc i hi
    cases conflict with
    | none => exact hl i hi
    | some cur =>
      have hcur := hc cur rfl
      have hnext : ∀ j, (itemAt s.items cur).right = some j → j ∈ order s := by
        intro j hj
        obtain ⟨k, hk⟩ := mem_get? hcur
        have hr := h.chain.right k cur hk
        rw [rightOf_itemAt (h.chain.bound cur hcur), hj] at hr
        exact get?_mem hr.symm
      have hcur' : ∀ j, some cur = some j → j ∈ order s := by
        intro j e
        rw [← Option.some.inj e]
        exact hcur
      rw [scanLoop] at hi
      by_cases h0 : right = some cur
      · rw [ite_eq_left h0] at hi
        exact hl i hi
      · rw [ite_eq_right h0] at hi
        by_cases h1 : thisL = (itemAt s.items cur).originL
        · rw [ite_eq_left h1] at hi
          by_cases h2 : (itemAt s.items cur).id.client < thisId.client
          · rw [ite_eq_left h2] at hi
            exact ih _ _ _ _ hcur' hnext i hi
          · rw [ite_eq_right h2] at hi
            by_cases h3 : thisR = (itemAt s.items cur).originR
            · rw [ite_eq_left h3] at hi
              exact hl i hi
            · rw [ite_eq_right h3] at hi
              exact ih _ _ _ _ hl hnext i hi
        · rw [ite_eq_right h1] at hi
          cases hol : (itemAt s.items cur).originL with
          | none =>
            rw [hol] at hi
            exact hl i hi
          | some cl =>
            rw [hol] at hi
            cases how : owner cl with
            | none =>
              have hi' : left = some i := by
                simpa [how] using hi
              exact hl i hi'
            | some o =>
              have hi' : (if o ∈ (itemAt s.items cur).id :: before then
                  if o ∈ (itemAt s.items cur).id :: conf then
                    scanLoop s.items owner thisId thisL thisR right fuel left
                      (itemAt s.items cur).right ((itemAt s.items cur).id :: before)
                      ((itemAt s.items cur).id :: conf)
                  else
                    scanLoop s.items owner thisId thisL thisR right fuel (some cur)
                      (itemAt s.items cur).right ((itemAt s.items cur).id :: before) []
                else left) = some i := by
                simpa [how] using hi
              by_cases h4 : o ∈ (itemAt s.items cur).id :: before
              · rw [ite_eq_left h4] at hi'
                by_cases h5 : o ∈ (itemAt s.items cur).id :: conf
                · rw [ite_eq_left h5] at hi'
                  exact ih _ _ _ _ hl hnext i hi'
                · rw [ite_eq_right h5] at hi'
                  exact ih _ _ _ _ hcur' hnext i hi'
              · rw [ite_eq_right h4] at hi'
                exact hl i hi'

theorem prevAt_of_mem {order : List Nat} (o : Option Nat) (h : ∀ i, o = some i → i ∈ order) :
    ∃ k, k ≤ order.length ∧ o = prevAt order k := by
  cases o with
  | none => exact ⟨0, Nat.zero_le _, rfl⟩
  | some i =>
    obtain ⟨j, hj⟩ := mem_get? (h i rfl)
    have := get?_lt hj
    exact ⟨j + 1, by omega, hj.symm⟩

theorem afterBId_eq_drop {y : Id} : ∀ (bs : List Block) (k : Nat) (B0 : Block),
    bs[k]? = some B0 → B0.id = y →
    (∀ (j : Nat) (Bj : Block), j < k → bs[j]? = some Bj → Bj.id ≠ y) →
    afterBId y bs = bs.drop (k + 1) := by
  intro bs
  induction bs with
  | nil =>
    intro k B0 h
    simp at h
  | cons a t ih =>
    intro k B0 hk hy hne
    cases k with
    | zero =>
      have e : a = B0 := by simpa using hk
      rw [afterBId, ite_eq_left (by rw [e]; exact hy)]
      simp
    | succ k' =>
      have hk' : t[k']? = some B0 := by simpa using hk
      have ha : ¬ a.id = y := hne 0 a (by omega) (by simp)
      rw [afterBId, ite_eq_right ha,
        ih k' B0 hk' hy (fun j Bj hj hBj => hne (j + 1) Bj (by omega) (by simpa using hBj))]
      simp

/-- The scan of the store is `scanB` of its block sequence. -/
theorem scanM_spec {f : Id → Char} {s : MStore} (h : WF s) (b : Block) {k : Nat}
    (hk : k ≤ (order s).length) {right : Option Nat}
    (hL : b.left.bind (ownerB (blocks f s)) = prevId f s k)
    (hright : ∀ i, i ∈ order s → (right = some i ↔ b.right = some (itemAt s.items i).id))
    (hrmem : ∀ r, right = some r → r ∈ order s) :
    ∃ k', k' ≤ (order s).length ∧
      scanM s b.id b.left b.right (prevAt (order s) k) right = prevAt (order s) k' ∧
      prevId f s k' = scanB (blocks f s) b := by
  have hloop := scanM_eq_loop h b.id b.left b.right hk hrmem
  have hprevmem : ∀ i, prevAt (order s) k = some i → i ∈ order s := by
    intro i hi
    cases k with
    | zero => cases hi
    | succ k' => exact get?_mem hi
  have hmem : ∀ i, scanM s b.id b.left b.right (prevAt (order s) k) right = some i → i ∈ order s := by
    intro i hi
    rw [hloop] at hi
    exact scanLoop_mem h _ _ _ _ _ _ _ _ _ _ hprevmem (fun j hj => get?_mem hj) i hi
  obtain ⟨k', hk', ek'⟩ := prevAt_of_mem _ hmem
  refine ⟨k', hk', ek', ?_⟩
  -- the scan over the slots from `k` on
  have hsplit : order s = (order s).take k ++ (order s).drop k := (List.take_append_drop k _).symm
  have hfuel : ((order s).drop k).length ≤ s.items.length :=
    Nat.le_trans (length_drop_le _ _) (nodup_length_le _ _ h.chain.nodup h.chain.bound)
  have heq := scanLoop_eq h b.toItem (ownerM s) right b.right hright ((order s).drop k)
    ((order s).take k) s.items.length (prevAt (order s) k) [] [] hsplit hfuel
  rw [get?_drop_zero] at heq
  have hown : ownerB (blocks f s) = ownerM s := funext (fun z => ownerM_eq h z)
  -- the candidates of `scanB`
  have hcands : (afterB (b.left.bind (ownerB (blocks f s))) (blocks f s)).map Block.toItem =
      ((order s).drop k).map (fun i => (itemAt s.items i).toItem) := by
    rw [hL]
    have hmap : ((order s).drop k).map (fun i => (itemAt s.items i).toItem) =
        ((blocks f s).drop k).map Block.toItem := by
      unfold blocks
      rw [← map_drop', List.map_map]
      rfl
    rw [hmap]
    cases k with
    | zero => rfl
    | succ k0 =>
      obtain ⟨i, hi⟩ := get?_some (show k0 < (order s).length by omega)
      have hp : prevId f s (k0 + 1) = some (blockAt f s.items i).id := by
        show ((order s)[k0]?).map _ = _
        rw [hi]
        rfl
      rw [hp]
      show (afterBId _ _).map _ = _
      rw [afterBId_eq_drop (blocks f s) k0 (blockAt f s.items i) (by rw [get?_blocks, hi]; rfl) rfl
        (by
          intro j Bj hj hBj
          rw [get?_blocks] at hBj
          obtain ⟨i', hi'⟩ := get?_some (show j < (order s).length by omega)
          rw [hi'] at hBj
          have eB : blockAt f s.items i' = Bj := Option.some.inj hBj
          intro e
          rw [← eB] at e
          have := blocks_id_inj h hi' hi e
          omega)]
  unfold scanB
  rw [hcands, hL, hown]
  have hid : ∀ o : Option Nat, o.map (fun i => (itemAt s.items i).id) =
      o.map (fun i => (blockAt f s.items i).id) := fun _ => rfl
  show (prevAt (order s) k').map (fun i => (blockAt f s.items i).id) = _
  rw [← ek', hloop, ← hid]
  exact heq

/-- The two splits and the scan of an integration: where the store stands
before the new item is linked.

`hL` and `hR` say what `repair` did for the two origins; `hsep` says that the
right origin is not inside the block that ends at the left origin (an item is
created between its origins, so it never is). -/
theorem integrate_scan {s s1 s2 : MStore} (h : WF s) {x : MItem}
    {left right : Option Nat}
    (hL : (x.originL = none ∧ s1 = s ∧ left = none) ∨
      ∃ l i, x.originL = some l ∧ left = some i ∧ SplitAfterOk s l s1 i)
    (hR : (x.originR = none ∧ s2 = s1 ∧ right = none) ∨
      ∃ r i, x.originR = some r ∧ right = some i ∧ SplitOk s1 r s2 i)
    (hsep : ∀ (l r : Id) (c : MClient) (p : Nat) (b : MBlock), x.originL = some l →
      x.originR = some r → At s l c p b →
      ¬ (r.client = l.client ∧ b.clock < r.clock ∧ r.clock ≤ l.clock)) :
    WF s2 ∧
      (∀ f : Id → Char, blocks f s2 = splitRight x.originR (splitLeft x.originL (blocks f s))) ∧
      (∃ k, k ≤ (order s2).length ∧ left = prevAt (order s2) k) ∧
      (∀ r, right = some r → r ∈ order s2) ∧
      ∀ f : Id → Char, ∃ k', k' ≤ (order s2).length ∧
        scanM s2 x.id x.originL x.originR left right = prevAt (order s2) k' ∧
        prevId f s2 k' = scanB (blocks f s2) (blockOf f x) := by
  -- the store after the left split
  have h1 : WF s1 := by
    rcases hL with ⟨_, e, _⟩ | ⟨l, i, _, _, ok⟩
    · rw [e]
      exact h
    · exact ok.wf
  have hb1 : ∀ f : Id → Char, blocks f s1 = splitLeft x.originL (blocks f s) := by
    intro f
    rcases hL with ⟨e0, e, _⟩ | ⟨l, i, e0, _, ok⟩
    · rw [e, e0]
      rfl
    · rw [e0, ok.blocks f]
      rfl
  -- the store after the right split
  have h2 : WF s2 := by
    rcases hR with ⟨_, e, _⟩ | ⟨r, i, _, _, ok⟩
    · rw [e]
      exact h1
    · exact ok.wf
  have hb2 : ∀ f : Id → Char, blocks f s2 = splitRight x.originR (blocks f s1) := by
    intro f
    rcases hR with ⟨e0, e, _⟩ | ⟨r, i, e0, _, ok⟩
    · rw [e, e0]
      rfl
    · rw [e0, ok.blocks f]
      rfl
  -- the left neighbour is in the sequence, where its origin says
  have hleft : ∃ k, k ≤ (order s2).length ∧ left = prevAt (order s2) k ∧
      ∀ f : Id → Char, x.originL.bind (ownerB (blocks f s2)) = prevId f s2 k := by
    rcases hL with ⟨e0, _, el⟩ | ⟨l, i, e0, el, ok⟩
    · exact ⟨0, Nat.zero_le _, el, fun f => by rw [e0]; rfl⟩
    · obtain ⟨y, c0, p0, b0, hy, ha0, hyc, hyk, hyend⟩ := ok.ends
      have hge0 := ha0.ge
      -- the item survives the right split
      have hsurv : i ∈ order s2 ∧ coreAt s2.items i = some y := by
        rcases hR with ⟨_, e, _⟩ | ⟨r, j, er, _, okr⟩
        · rw [e]
          exact ⟨ok.mem, hy⟩
        · refine okr.keep i y ok.mem hy ?_
          rintro ⟨g1, g2, g3⟩
          exact hsep l r c0 p0 b0 e0 er ha0 ⟨by rw [g1, hyc], by omega, by omega⟩
      obtain ⟨j0, hj0⟩ := mem_get? hsurv.1
      have hjl := get?_lt hj0
      refine ⟨j0 + 1, by omega, by rw [el]; exact hj0.symm, ?_⟩
      intro f
      obtain ⟨c', p', b', ha', hs'⟩ := h2.at_of_contains (z := l) hsurv.1 hsurv.2 hyc.symm
        (by omega) (by omega)
      obtain ⟨i', x', e1, e2, e3, _⟩ := ha'.item h2
      have ei : i' = i := Option.some.inj (e1.symm.trans hs')
      rw [ei, hsurv.2] at e2
      have ex : y = x' := Option.some.inj e2
      rw [e0]
      show ownerB (blocks f s2) l = _
      rw [ownerB_blocks_at h2 ha']
      show _ = ((order s2)[j0]?).map (fun i => (blockAt f s2.items i).id)
      rw [hj0]
      show _ = some (blockAt f s2.items i).id
      rw [blockAt_of_core hsurv.2, ← e3, ← ex]
      rfl
  obtain ⟨k, hk, ek, hLid⟩ := hleft
  -- the right neighbour is the item that starts at the right origin
  have hright : ∀ i, i ∈ order s2 → (right = some i ↔ x.originR = some (itemAt s2.items i).id) := by
    intro i hi
    rcases hR with ⟨e0, _, er⟩ | ⟨r, j, e0, er, okr⟩
    · rw [e0, er]
      constructor
      · intro e
        cases e
      · intro e
        cases e
    · obtain ⟨yj, hyj, hyid⟩ := okr.starts
      rw [e0, er]
      constructor
      · intro e
        have eij : j = i := Option.some.inj e
        have hci : (itemAt s2.items j).core.id = yj.id := congrArg MItem.id (itemAt_core hyj)
        have hci' : (itemAt s2.items j).id = yj.id := hci
        rw [← eij, hci', hyid]
      · intro e
        have eid : r = (itemAt s2.items i).id := Option.some.inj e
        obtain ⟨yi, hyi⟩ := h2.core_of_mem hi
        have hci : (itemAt s2.items i).core.id = yi.id := congrArg MItem.id (itemAt_core hyi)
        have hci' : (itemAt s2.items i).id = yi.id := hci
        obtain ⟨_, _, _, _, _, _, _, _, _, _, li⟩ := h2.item_block hi hyi
        obtain ⟨_, _, _, _, _, _, _, _, _, _, lj⟩ := h2.item_block okr.mem hyj
        have hyi_id : yi.id = r := by rw [← hci', ← eid]
        have eji : j = i := h2.slot_unique (z := r) okr.mem hi hyj hyi (by rw [hyid])
          (by rw [hyid]; exact Nat.le_refl _) (by rw [hyid]; omega) (by rw [hyi_id])
          (by rw [hyi_id]; exact Nat.le_refl _) (by rw [hyi_id]; omega)
        rw [eji]
  have hrmem : ∀ r, right = some r → r ∈ order s2 := by
    intro r hr
    rcases hR with ⟨_, _, er⟩ | ⟨r0, j, _, er, okr⟩
    · rw [er] at hr
      cases hr
    · rw [er] at hr
      rw [← Option.some.inj hr]
      exact okr.mem
  -- the scan, then the link
  have hscan : ∀ f : Id → Char, ∃ k', k' ≤ (order s2).length ∧
      scanM s2 x.id x.originL x.originR left right = prevAt (order s2) k' ∧
      prevId f s2 k' = scanB (blocks f s2) (blockOf f x) := by
    intro f
    rw [ek]
    exact scanM_spec h2 (blockOf f x) hk (hLid f) hright hrmem
  exact ⟨h2, fun f => by rw [hb2 f, hb1 f], ⟨k, hk, ek⟩, hrmem, hscan⟩

/-- **Integration.** `integrate` is `integrateBlock`: after the two splits of
`repair` (`s1`, `s2`) and, if the client is new, its empty timeline (`s3`), the
scan and the link are `scanB` and `insertAfterB` on the block sequence. -/
theorem integrate_compose {s s1 s2 s3 : MStore} (h : WF s) {x : MItem} {ci : Nat} {c : MClient}
    {left right : Option Nat} (hlen : 0 < x.len) (hdel : x.deleted = false) (hgc : x.gc = false)
    (hL : (x.originL = none ∧ s1 = s ∧ left = none) ∨
      ∃ l i, x.originL = some l ∧ left = some i ∧ SplitAfterOk s l s1 i)
    (hR : (x.originR = none ∧ s2 = s1 ∧ right = none) ∨
      ∃ r i, x.originR = some r ∧ right = some i ∧ SplitOk s1 r s2 i)
    (hsep : ∀ (l r : Id) (c : MClient) (p : Nat) (b : MBlock), x.originL = some l →
      x.originR = some r → At s l c p b →
      ¬ (r.client = l.client ∧ b.clock < r.clock ∧ r.clock ≤ l.clock))
    (h3 : WF s3) (ho : order s3 = order s2) (hi : s3.items = s2.items)
    (hc : s3.clients[ci]? = some c) (hcl : c.client = x.id.client)
    (hcont : c.blocks = [] ∨ c.stop = x.id.clock) :
    WF (linkNew s3 ci (scanM s2 x.id x.originL x.originR left right) x) ∧
      ∀ f : Id → Char,
        blocks f (linkNew s3 ci (scanM s2 x.id x.originL x.originR left right) x) =
          integrateBlock (blocks f s) (blockOf f x) := by
  obtain ⟨h2, hb, _, _, hscan⟩ := integrate_scan h hL hR hsep
  obtain ⟨k', hk', ek', _⟩ := hscan (fun _ => 'a')
  have hk3 : k' ≤ (order s3).length := by
    rw [ho]
    exact hk'
  rw [ek', ← ho]
  refine ⟨(linkNew_spec h3 hc hcl hcont hlen hdel hgc hk3).1, ?_⟩
  intro f
  obtain ⟨k'', hk'', ek'', hsb⟩ := hscan f
  rw [ek'] at ek''
  have hkk : prevId f s2 k' = prevId f s2 k'' := by
    unfold prevId
    rw [ek'']
  have hb3 : blocks f s3 = blocks f s2 := by
    unfold blocks
    rw [ho, hi]
  have hp3 : prevId f s3 k' = prevId f s2 k' := by
    unfold prevId
    rw [ho, hi]
  rw [blocks_linkNew h3 hc hcl hcont hlen hdel hgc hk3, hb3, hp3, hkk, hsb]
  unfold integrateBlock
  rw [hb f]
  rfl

/-! ## One step of the scan -/

theorem scanLoop_succ (items : List MItem) (owner : Id → Option Id) (thisId : Id)
    (thisL thisR : Option Id) (right : Option Nat) (fuel : Nat) (left : Option Nat) (cur : Nat)
    (before conf : List Id) :
    scanLoop items owner thisId thisL thisR right (fuel + 1) left (some cur) before conf =
      if right = some cur then left
      else
        match scanStep owner thisId thisL thisR (itemAt items cur)
            ((itemAt items cur).id :: before) ((itemAt items cur).id :: conf) with
        | MStep.stop => left
        | MStep.skip =>
          scanLoop items owner thisId thisL thisR right fuel left (itemAt items cur).right
            ((itemAt items cur).id :: before) ((itemAt items cur).id :: conf)
        | MStep.take =>
          scanLoop items owner thisId thisL thisR right fuel (some cur) (itemAt items cur).right
            ((itemAt items cur).id :: before) [] := by
  rw [scanLoop]
  unfold scanStep
  generalize itemAt items cur = c
  by_cases h0 : right = some cur
  · simp [h0]
  · by_cases h1 : thisL = c.originL
    · by_cases h2 : c.id.client < thisId.client
      · simp [h0, h1, h2]
      · by_cases h3 : thisR = c.originR
        · simp [h0, h1, h2, h3]
        · simp [h0, h1, h2, h3]
    · cases hl : c.originL with
      | none =>
        rw [hl] at h1
        simp [h0, h1]
      | some cl =>
        rw [hl] at h1
        cases ho : owner cl with
        | none => simp [h0, h1, ho]
        | some o =>
          by_cases h4 : o = c.id ∨ o ∈ before
          · by_cases h5 : o = c.id ∨ o ∈ conf
            · simp [h0, h1, ho, h4, h5]
            · simp [h0, h1, ho, h4, h5]
          · simp [h0, h1, ho, h4]

theorem scanStep_same_take {owner : Id → Option Id} {thisId : Id} {thisL thisR : Option Id}
    {cand : MItem} {B C : List Id} (h1 : thisL = cand.originL)
    (h2 : cand.id.client < thisId.client) :
    scanStep owner thisId thisL thisR cand B C = MStep.take := by
  unfold scanStep
  simp [h1, h2]

theorem scanStep_same_stop {owner : Id → Option Id} {thisId : Id} {thisL thisR : Option Id}
    {cand : MItem} {B C : List Id} (h1 : thisL = cand.originL)
    (h2 : ¬ cand.id.client < thisId.client) (h3 : thisR = cand.originR) :
    scanStep owner thisId thisL thisR cand B C = MStep.stop := by
  unfold scanStep
  simp [h1, h2, h3]

theorem scanStep_same_skip {owner : Id → Option Id} {thisId : Id} {thisL thisR : Option Id}
    {cand : MItem} {B C : List Id} (h1 : thisL = cand.originL)
    (h2 : ¬ cand.id.client < thisId.client) (h3 : ¬ thisR = cand.originR) :
    scanStep owner thisId thisL thisR cand B C = MStep.skip := by
  unfold scanStep
  simp [h1, h2, h3]

theorem scanStep_none {owner : Id → Option Id} {thisId : Id} {thisL thisR : Option Id}
    {cand : MItem} {B C : List Id} (h1 : ¬ thisL = cand.originL) (h2 : cand.originL = none) :
    scanStep owner thisId thisL thisR cand B C = MStep.stop := by
  unfold scanStep
  rw [h2] at h1
  simp [h1, h2]

theorem scanStep_owner_none {owner : Id → Option Id} {thisId : Id} {thisL thisR : Option Id}
    {cand : MItem} {B C : List Id} {cl : Id} (h1 : ¬ thisL = cand.originL)
    (h2 : cand.originL = some cl) (h3 : owner cl = none) :
    scanStep owner thisId thisL thisR cand B C = MStep.stop := by
  unfold scanStep
  rw [h2] at h1
  simp [h1, h2, h3]

theorem scanStep_owner_skip {owner : Id → Option Id} {thisId : Id} {thisL thisR : Option Id}
    {cand : MItem} {B C : List Id} {cl o : Id} (h1 : ¬ thisL = cand.originL)
    (h2 : cand.originL = some cl) (h3 : owner cl = some o) (h4 : o ∈ B) (h5 : o ∈ C) :
    scanStep owner thisId thisL thisR cand B C = MStep.skip := by
  unfold scanStep
  rw [h2] at h1
  simp [h1, h2, h3, h4, h5]

theorem scanStep_owner_take {owner : Id → Option Id} {thisId : Id} {thisL thisR : Option Id}
    {cand : MItem} {B C : List Id} {cl o : Id} (h1 : ¬ thisL = cand.originL)
    (h2 : cand.originL = some cl) (h3 : owner cl = some o) (h4 : o ∈ B) (h5 : ¬ o ∈ C) :
    scanStep owner thisId thisL thisR cand B C = MStep.take := by
  unfold scanStep
  rw [h2] at h1
  simp [h1, h2, h3, h4, h5]

theorem scanStep_owner_far {owner : Id → Option Id} {thisId : Id} {thisL thisR : Option Id}
    {cand : MItem} {B C : List Id} {cl o : Id} (h1 : ¬ thisL = cand.originL)
    (h2 : cand.originL = some cl) (h3 : owner cl = some o) (h4 : ¬ o ∈ B) :
    scanStep owner thisId thisL thisR cand B C = MStep.stop := by
  unfold scanStep
  rw [h2] at h1
  simp [h1, h2, h3, h4]

theorem scanStep_congr {owner : Id → Option Id} {thisId : Id} {thisL thisR : Option Id}
    {cand : MItem} {B C B' C' : List Id} (hB : ∀ z, z ∈ B ↔ z ∈ B') (hC : ∀ z, z ∈ C ↔ z ∈ C') :
    scanStep owner thisId thisL thisR cand B C = scanStep owner thisId thisL thisR cand B' C' := by
  unfold scanStep
  simp [hB, hC]

/-- The scan answers a position of the sequence. -/
theorem scanM_pos {s : MStore} (h : WF s) (thisId : Id) (thisL thisR : Option Id)
    {left : Option Nat} (right : Option Nat) (hl : ∀ i, left = some i → i ∈ order s) :
    ∃ k', k' ≤ (order s).length ∧
      scanM s thisId thisL thisR left right = prevAt (order s) k' := by
  apply prevAt_of_mem
  intro i hi
  unfold scanM at hi
  by_cases hn : needsScan s left right = true
  · simp only [hn, ↓reduceIte] at hi
    refine scanLoop_mem h (ownerM s) thisId thisL thisR right s.items.length left
      (nextOf s.items s.start left) [] [] hl ?_ i hi
    intro j hj
    obtain ⟨k, hk, ek⟩ := prevAt_of_mem left hl
    rw [ek, h.chain.nextOf_prevAt hk] at hj
    exact get?_mem hj
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hi
    exact hl i hi

/-! ## Content collection -/

/-- `gc_item_content`: a deleted item drops its content. -/
def MItem.collect (x : MItem) : MItem := if x.deleted then { x with gc := true } else x

theorem MItem.collect_right (x : MItem) : x.collect.right = x.right := by
  unfold MItem.collect
  split <;> rfl

theorem MItem.collect_left (x : MItem) : x.collect.left = x.left := by
  unfold MItem.collect
  split <;> rfl

theorem MItem.collect_id (x : MItem) : x.collect.id = x.id := by
  unfold MItem.collect
  split <;> rfl

theorem MItem.collect_len (x : MItem) : x.collect.len = x.len := by
  unfold MItem.collect
  split <;> rfl

theorem MItem.collect_deleted (x : MItem) : x.collect.deleted = x.deleted := by
  unfold MItem.collect
  split <;> rfl

theorem MItem.collect_core (x : MItem) : x.collect.core = x.core.collect := by
  cases hd : x.deleted <;> simp [MItem.collect, MItem.core, hd]

/-- The store after the content of every deleted item is dropped. -/
def gcAll (s : MStore) : MStore := { s with items := s.items.map MItem.collect }

theorem rightOf_collect (items : List MItem) (i : Nat) :
    rightOf (items.map MItem.collect) i = rightOf items i := by
  unfold rightOf
  rw [get?_map]
  cases items[i]? with
  | none => rfl
  | some x => exact x.collect_right

theorem leftOf_collect (items : List MItem) (i : Nat) :
    leftOf (items.map MItem.collect) i = leftOf items i := by
  unfold leftOf
  rw [get?_map]
  cases items[i]? with
  | none => rfl
  | some x => exact x.collect_left

theorem coreAt_collect (items : List MItem) (i : Nat) :
    coreAt (items.map MItem.collect) i = (coreAt items i).map MItem.collect := by
  unfold coreAt
  rw [get?_map]
  cases items[i]? with
  | none => rfl
  | some x =>
    show some x.collect.core = some x.core.collect
    rw [MItem.collect_core]

theorem blockOf_collect (f : Id → Char) (x : MItem) :
    blockOf f x.collect = gcBlock (blockOf f x) := by
  unfold gcBlock
  cases hd : x.deleted with
  | false =>
    have e : x.collect = x := by simp [MItem.collect, hd]
    have e2 : (blockOf f x).deleted = false := hd
    rw [e]
    simp [e2]
  | true =>
    have e : x.collect = { x with gc := true } := by simp [MItem.collect, hd]
    have e2 : (blockOf f x).deleted = true := hd
    rw [e]
    simp only [e2, ↓reduceIte]
    rw [blockOf_len]
    simp [blockOf, hd]

/-- **Content collection is `gcContent`.** -/
theorem gcAll_spec {s : MStore} (h : WF s) :
    WF (gcAll s) ∧ order (gcAll s) = order s ∧
      ∀ f : Id → Char, blocks f (gcAll s) = gcContent (blocks f s) := by
  have hchain : Chain (gcAll s).items (gcAll s).start (order s) :=
    h.chain.congr (List.length_map _) (fun i _ => rightOf_collect s.items i)
      (fun i _ => leftOf_collect s.items i)
  have hb : ∀ (c : MClient) (p : Nat) (b : MBlock), c ∈ (gcAll s).clients →
      c.blocks[p]? = some b → BlockOK (gcAll s).items c p b := by
    intro c p b hc hb
    obtain ⟨i, x, hs, hx, hid, hlen, hdel⟩ := h.block c p b hc hb
    refine ⟨i, x.collect, hs, ?_, ?_, ?_, ?_⟩
    · show coreAt (s.items.map MItem.collect) i = some x.collect
      rw [coreAt_collect, hx]
      rfl
    · rw [MItem.collect_id]
      exact hid
    · rw [MItem.collect_len]
      exact hlen
    · rw [MItem.collect_deleted]
      exact hdel
  have hg : ∀ (i : Nat) (y : MItem), i ∈ order s → coreAt (gcAll s).items i = some y →
      y.gc = true → y.deleted = true := by
    intro i y hi hy hgc
    have hy' : coreAt (s.items.map MItem.collect) i = some y := hy
    rw [coreAt_collect] at hy'
    obtain ⟨x, hx⟩ := h.core_of_mem hi
    rw [hx] at hy'
    have ey : y = x.collect := (Option.some.inj hy').symm
    rw [ey, MItem.collect_deleted]
    rw [ey] at hgc
    by_cases hd : x.deleted = true
    · exact hd
    · have e : x.collect = x := by simp [MItem.collect, hd]
      rw [e] at hgc
      exact h.gc i x hi hx hgc
  have hwo := WF.of_order (s := gcAll s) (order s) hchain h.distinct h.timeline hb h.live hg
  refine ⟨hwo.1, hwo.2, fun f => ?_⟩
  unfold blocks gcContent
  rw [hwo.2, List.map_map]
  apply map_congr_mem
  intro i hi
  obtain ⟨x, hx⟩ := h.core_of_mem hi
  have hx' : coreAt (gcAll s).items i = some x.collect := by
    show coreAt (s.items.map MItem.collect) i = some x.collect
    rw [coreAt_collect, hx]
    rfl
  show blockAt f (gcAll s).items i = gcBlock (blockAt f s.items i)
  rw [blockAt_of_core hx', blockAt_of_core hx, blockOf_collect]

/-! ## The text of the blocks -/

theorem unitChars_eq_units (f : Id → Char) (c : Nat) (right : Option Id) :
    ∀ (n k : Nat) (l : Option Id),
      unitChars f c k n = (unitsFrom c right k l n).map (fun u => f u.id)
  | 0, _, _ => rfl
  | n + 1, k, l => by
    show f ⟨c, k⟩ :: unitChars f c (k + 1) n =
      f ⟨c, k⟩ :: (unitsFrom c right (k + 1) (some ⟨c, k⟩) n).map (fun u => f u.id)
    rw [unitChars_eq_units f c right n (k + 1) (some ⟨c, k⟩)]

/-- The live blocks of a store hold the characters `f` gives their clocks. -/
theorem payload_blocks {f : Id → Char} {s : MStore} (h : WF s) : Payload f (blocks f s) := by
  intro B hB hdel
  obtain ⟨i, x, hi, hx, rfl⟩ := mem_blocks h hB
  have hd : x.deleted = false := hdel
  have hgc : x.gc = false := by
    cases hg : x.gc with
    | false => rfl
    | true =>
      have := h.gc i x hi hx hg
      rw [hd] at this
      cases this
  have hc : (blockOf f x).content = Content.str (unitChars f x.id.client x.id.clock x.len) := by
    unfold blockOf
    simp [hgc]
  have hl : (blockOf f x).len = x.len := blockOf_len f x
  unfold Block.units
  rw [hl, hc]
  exact unitChars_eq_units f _ _ _ _ _

/-! ## Deleting a block -/

/-- `delete_block` on a live block: the item and its block are marked deleted. -/
def markDeleted (s : MStore) (ci p i : Nat) : MStore :=
  { items := upd s.items i (fun x => { x with deleted := true })
    start := s.start
    clients := upd s.clients ci (fun c =>
      { c with blocks := upd c.blocks p (fun b => { b with kind := MKind.deleted i }) }) }

theorem endAt_upd {blocks : List MBlock} {stop p : Nat} {g : MBlock → MBlock}
    (hg : ∀ b, (g b).clock = b.clock) (q : Nat) :
    endAt (upd blocks p g) stop q = endAt blocks stop q := by
  unfold endAt
  rw [get?_upd]
  by_cases e : q + 1 = p
  · rw [ite_eq_left e]
    cases blocks[q + 1]? with
    | none => rfl
    | some b => exact hg b
  · rw [ite_eq_right e]

theorem markDeleted_spec {s : MStore} (h : WF s) {ci p i : Nat} {c : MClient} {b : MBlock}
    {x : MItem} (hc : s.clients[ci]? = some c) (hb : c.blocks[p]? = some b)
    (hs : b.kind.slot = some i) (hx : coreAt s.items i = some x) :
    WF (markDeleted s ci p i) ∧ order (markDeleted s ci p i) = order s ∧
      coreAt (markDeleted s ci p i).items i = some { x with deleted := true } ∧
      (∀ j, j ≠ i → coreAt (markDeleted s ci p i).items j = coreAt s.items j) := by
  have hcm : c ∈ s.clients := get?_mem hc
  obtain ⟨i', x', e1, e2, e3, e4, e5, hi', _⟩ := h.block_item hcm hb
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei] at e2 hi'
  rw [hx] at e2
  have ex : x' = x := (Option.some.inj e2).symm
  rw [ex] at e3 e4 e5
  have hi : i ∈ order s := hi'
  have htl := h.timeline c hcm
  have hgc : ∀ b : MBlock, ({ b with kind := MKind.deleted i } : MBlock).clock = b.clock :=
    fun _ => rfl
  have core_i : coreAt (markDeleted s ci p i).items i = some { x with deleted := true } := by
    show coreAt (upd s.items i (fun x => { x with deleted := true })) i = _
    rw [coreAt_upd, ite_eq_left rfl]
    unfold coreAt at hx
    cases hy : s.items[i]? with
    | none =>
      rw [hy] at hx
      cases hx
    | some y =>
      rw [hy] at hx
      have exy : y.core = x := Option.some.inj hx
      show some ({ y with deleted := true } : MItem).core = some { x with deleted := true }
      rw [← exy]
      rfl
  have core_other : ∀ j, j ≠ i → coreAt (markDeleted s ci p i).items j = coreAt s.items j := by
    intro j hj
    show coreAt (upd s.items i (fun x => { x with deleted := true })) j = _
    rw [coreAt_upd, ite_eq_right hj]
  have hch : Chain (markDeleted s ci p i).items (markDeleted s ci p i).start (order s) :=
    h.chain.congr (length_upd _ _ _) (fun j _ => rightOf_upd_keep _ _ _ (fun _ => rfl))
      (fun j _ => leftOf_upd_keep _ _ _ (fun _ => rfl))
  have hcl : ∀ c', c' ∈ (markDeleted s ci p i).clients →
      c' = { c with blocks := upd c.blocks p (fun b => { b with kind := MKind.deleted i }) } ∨
      ∃ j, j ≠ ci ∧ s.clients[j]? = some c' := by
    intro c' hc'
    rcases mem_upd hc' with ⟨a, ha, e⟩ | hj
    · rw [hc] at ha
      have ea : c = a := Option.some.inj ha
      rw [← ea] at e
      exact Or.inl e
    · exact Or.inr hj
  have hnew_mem : ({ c with blocks := upd c.blocks p (fun b => { b with kind := MKind.deleted i }) } :
      MClient) ∈ (markDeleted s ci p i).clients :=
    upd_mem_self (f := fun c : MClient =>
      { c with blocks := upd c.blocks p (fun b => { b with kind := MKind.deleted i }) }) hc
  have hother : ∀ (j : Nat) (c' : MClient) (q : Nat) (b' : MBlock), j ≠ ci →
      s.clients[j]? = some c' → c'.blocks[q]? = some b' → b'.kind.slot ≠ some i := by
    intro j c' q b' hj hc' hb' hslot
    obtain ⟨i2, x2, f1, f2, f3, _⟩ := h.block c' q b' (get?_mem hc') hb'
    have e2 : i2 = i := Option.some.inj (f1.symm.trans hslot)
    rw [e2, hx] at f2
    have ex2 : x = x2 := Option.some.inj f2
    rw [← ex2, e3] at f3
    have ecl : c.client = c'.client := congrArg Id.client f3
    by_cases hlt : j < ci
    · exact h.distinct j ci c' c hlt hc' hc ecl.symm
    · exact h.distinct ci j c c' (by omega) hc hc' ecl
  have key := WF.of_order (s := markDeleted s ci p i) (order s) hch
    (by
      intro p' q' a' b' hpq ha' hb'
      have pre : ∀ (j : Nat) (c' : MClient), (markDeleted s ci p i).clients[j]? = some c' →
          ∃ c0, s.clients[j]? = some c0 ∧ c'.client = c0.client := by
        intro j c' hj
        rcases get?_upd_cases hj with ⟨ej, a, ha, e⟩ | ⟨_, hj'⟩
        · exact ⟨a, by rw [ej]; exact ha, by rw [e]⟩
        · exact ⟨c', hj', rfl⟩
      obtain ⟨a0, ha0, ea⟩ := pre p' a' ha'
      obtain ⟨b0, hb0, eb⟩ := pre q' b' hb'
      rw [ea, eb]
      exact h.distinct p' q' a0 b0 hpq ha0 hb0)
    (by
      intro c' hc'
      rcases hcl c' hc' with e | ⟨j, _, hj⟩
      · rw [e]
        exact htl.update p (fun b _ => hgc b)
      · exact h.timeline c' (get?_mem hj))
    (by
      intro c' q b' hc' hb'
      rcases hcl c' hc' with e | ⟨j, hj, hcj⟩
      · rw [e] at hb' ⊢
        have hb'' : (upd c.blocks p (fun b => { b with kind := MKind.deleted i }))[q]? = some b' :=
          hb'
        rcases get?_upd_cases hb'' with ⟨eq, a, ha, eb⟩ | ⟨hq, hb0⟩
        · rw [hb] at ha
          have eab : b = a := Option.some.inj ha
          rw [eq, eb, ← eab]
          refine ⟨i, { x with deleted := true }, rfl, core_i, e3, ?_, rfl⟩
          show x.len = endAt (upd c.blocks p (fun b => { b with kind := MKind.deleted i })) c.stop p -
            b.clock
          rw [endAt_upd hgc]
          exact e4
        · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c q b' hcm hb0
          have hne : i2 ≠ i := by
            intro e2
            rw [e2, hx] at f2
            have ex2 : x = x2 := Option.some.inj f2
            rw [← ex2, e3] at f3
            have hck : b.clock = b'.clock := congrArg Id.clock f3
            by_cases hlt : q < p
            · have := htl.sorted q p b' b hlt hb0 hb
              omega
            · have := htl.sorted p q b b' (by omega) hb hb0
              omega
          refine ⟨i2, x2, f1, ?_, f3, ?_, f5⟩
          · rw [core_other i2 hne]
            exact f2
          · show x2.len = endAt (upd c.blocks p (fun b => { b with kind := MKind.deleted i }))
              c.stop q - b'.clock
            rw [endAt_upd hgc]
            exact f4
      · obtain ⟨i2, x2, f1, f2, f3, f4, f5⟩ := h.block c' q b' (get?_mem hcj) hb'
        have hne : i2 ≠ i := fun e2 => hother j c' q b' hj hcj hb' (by rw [f1, e2])
        exact ⟨i2, x2, f1, by
          rw [core_other i2 hne]
          exact f2, f3, f4, f5⟩)
    (by
      intro i0
      constructor
      · intro hi0
        obtain ⟨c0, q, b0, hc0, hb0, hs0⟩ := (h.live i0).mp hi0
        obtain ⟨j, hj⟩ := mem_get? hc0
        by_cases ej : j = ci
        · rw [ej, hc] at hj
          have ec : c = c0 := Option.some.inj hj
          rw [← ec] at hb0
          by_cases hq : q = p
          · rw [hq, hb] at hb0
            have ebb : b = b0 := Option.some.inj hb0
            rw [← ebb, hs] at hs0
            refine ⟨_, p, { b with kind := MKind.deleted i }, hnew_mem, ?_, hs0⟩
            show (upd c.blocks p (fun b => { b with kind := MKind.deleted i }))[p]? = _
            rw [get?_upd_self, hb]
            rfl
          · refine ⟨_, q, b0, hnew_mem, ?_, hs0⟩
            show (upd c.blocks p (fun b => { b with kind := MKind.deleted i }))[q]? = some b0
            rw [get?_upd_ne _ _ hq]
            exact hb0
        · exact ⟨c0, q, b0, upd_mem_other ej hj, hb0, hs0⟩
      · rintro ⟨c', q, b', hc', hb', hs'⟩
        rcases hcl c' hc' with e | ⟨j, _, hcj⟩
        · rw [e] at hb'
          have hb'' : (upd c.blocks p (fun b => { b with kind := MKind.deleted i }))[q]? = some b' :=
            hb'
          rcases get?_upd_cases hb'' with ⟨eq, a, ha, eb⟩ | ⟨hq, hb0⟩
          · rw [eb] at hs'
            have e0 : i = i0 := Option.some.inj hs'
            rw [← e0]
            exact hi
          · exact (h.live i0).mpr ⟨c, q, b', hcm, hb0, hs'⟩
        · exact (h.live i0).mpr ⟨c', q, b', get?_mem hcj, hb', hs'⟩)
    (by
      intro i0 y hi0 hy hgc'
      by_cases e : i0 = i
      · rw [e, core_i] at hy
        rw [← Option.some.inj hy]
      · rw [core_other i0 e] at hy
        exact h.gc i0 y hi0 hy hgc')
  exact ⟨key.1, key.2, core_i, core_other⟩

/-- The store `s'` holds the clocks of `s`, in the same order, and at least
its deletions (I8: a deletion is never undone). -/
structure Grows (s s' : MStore) : Prop where
  flat : ∀ f : Id → Char, flatten (blocks f s') = flatten (blocks f s)
  dels : ∀ (f : Id → Char) (x : Id), x ∈ deletedSet (blocks f s) → x ∈ deletedSet (blocks f s')

theorem Grows.refl (s : MStore) : Grows s s := ⟨fun _ => rfl, fun _ _ h => h⟩

theorem Grows.trans {a b c : MStore} (h1 : Grows a b) (h2 : Grows b c) : Grows a c :=
  ⟨fun f => (h2.flat f).trans (h1.flat f), fun f x hx => h2.dels f x (h1.dels f x hx)⟩

theorem Grows.of_toDoc {s s' : MStore}
    (h : ∀ f : Id → Char, toDoc (blocks f s') = toDoc (blocks f s)) : Grows s s' := by
  constructor
  · intro f
    exact congrArg Doc.items (h f)
  · intro f x hx
    have e : deletedSet (blocks f s') = deletedSet (blocks f s) := congrArg Doc.deleted (h f)
    rw [e]
    exact hx

/-- A split keeps the clocks and the deletions. -/
theorem SplitOk.grows {s s' : MStore} {z : Id} {slot : Nat} (h : SplitOk s z s' slot) :
    Grows s s' :=
  Grows.of_toDoc (fun f => by rw [h.blocks f]; exact toDoc_split _ _)

/-- Deleting a block keeps the clocks and the deletions. -/
theorem markDeleted_grows {s : MStore} (h : WF s) {ci p i : Nat} {c : MClient} {b : MBlock}
    {x : MItem} (hc : s.clients[ci]? = some c) (hb : c.blocks[p]? = some b)
    (hs : b.kind.slot = some i) (hx : coreAt s.items i = some x) :
    Grows s (markDeleted s ci p i) := by
  obtain ⟨_, ho, core_i, core_other⟩ := markDeleted_spec h hc hb hs hx
  have hunits : ∀ (f : Id → Char) (j : Nat), j ∈ order s →
      (blockAt f (markDeleted s ci p i).items j).units = (blockAt f s.items j).units ∧
      ((blockAt f s.items j).deleted = true →
        (blockAt f (markDeleted s ci p i).items j).deleted = true) := by
    intro f j hj
    obtain ⟨y, hy⟩ := h.core_of_mem hj
    by_cases e : j = i
    · rw [e, blockAt_of_core core_i, blockAt_of_core hx]
      exact ⟨rfl, fun _ => rfl⟩
    · rw [blockAt_of_core (by rw [core_other j e]; exact hy), blockAt_of_core hy]
      exact ⟨rfl, fun hd => hd⟩
  constructor
  · intro f
    unfold blocks flatten
    rw [ho, flatMap_map, flatMap_map]
    exact flatMap_congr_mem (fun j hj => (hunits f j hj).1)
  · intro f z hz
    obtain ⟨B, hB, hdel, hzB⟩ := mem_deletedSet.mp hz
    have hB' : B ∈ (order s).map (blockAt f s.items) := hB
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hB'
    apply mem_deletedSet.mpr
    refine ⟨blockAt f (markDeleted s ci p i).items j, ?_, (hunits f j hj).2 hdel, ?_⟩
    · unfold blocks
      rw [ho]
      exact List.mem_map.mpr ⟨j, hj, rfl⟩
    · rw [(hunits f j hj).1]
      exact hzB

/-! ## The origins of an item of the network

`integrate_compose` needs the right origin of the new item not to be inside
the block that ends at its left origin. An item the network creates or
delivers stands between its origins (`CanIntegrate.left_lt_right`), and the
clocks of a block stand in clock order, so it never is. -/

theorem ix_unitsFrom (c : Nat) (right : Option Id) :
    ∀ (n k : Nat) (l : Option Id) (j : Nat), j < n →
      ix (unitsFrom c right k l n) ⟨c, k + j⟩ = j + 1
  | 0, _, _, _, h => by omega
  | n + 1, k, l, 0, _ => by
    show ix (⟨⟨c, k⟩, l, right⟩ :: unitsFrom c right (k + 1) (some ⟨c, k⟩) n) ⟨c, k + 0⟩ = 0 + 1
    exact ix_cons_self _ _
  | n + 1, k, l, j + 1, h => by
    show ix (⟨⟨c, k⟩, l, right⟩ :: unitsFrom c right (k + 1) (some ⟨c, k⟩) n) ⟨c, k + (j + 1)⟩ =
      j + 1 + 1
    have hne : (⟨⟨c, k⟩, l, right⟩ : Item).id ≠ ⟨c, k + (j + 1)⟩ := by
      intro e
      have e' : k = k + (j + 1) := congrArg Id.clock e
      omega
    rw [ix_cons_ne hne]
    have e : k + (j + 1) = (k + 1) + j := by omega
    rw [e, ix_unitsFrom c right n (k + 1) (some ⟨c, k⟩) j (by omega)]

/-- The position of a clock of a block in the unit sequence. -/
theorem ix_flatten_block {pre post : List Block} {B : Block}
    (hn : NodupIds (flatten (pre ++ B :: post))) {j : Nat} (hj : j < B.len) :
    ix (flatten (pre ++ B :: post)) ⟨B.id.client, B.id.clock + j⟩ =
      (flatten pre).length + (j + 1) := by
  have hu : ix B.units ⟨B.id.client, B.id.clock + j⟩ = j + 1 :=
    ix_unitsFrom B.id.client B.right B.len B.id.clock B.left j hj
  have hlen : B.units.length = B.len := length_unitsFrom _ _ _ _ _
  obtain ⟨a, haU, hai⟩ : ∃ a, a ∈ B.units ∧ a.id = ⟨B.id.client, B.id.clock + j⟩ :=
    ix_le_length_iff.mp (by rw [hu, hlen]; omega)
  rw [flatten_append, flatten_cons] at hn ⊢
  have habs : ∀ a', a' ∈ flatten pre → a'.id ≠ ⟨B.id.client, B.id.clock + j⟩ := by
    intro a' ha' e
    have hp := List.pairwise_append.mp hn
    exact hp.2.2 a' ha' a (List.mem_append_left _ haU) (e.trans hai.symm)
  rw [ix_append_right _ (by rw [ix_absent habs]; omega),
    ix_append_left _ (by rw [hu, hlen]; omega), hu]

/-- An item that stands between its origins does not have its right origin
inside the block that ends at its left origin. -/
theorem sep_of_canIntegrate {f : Id → Char} {s : MStore} (h : WF s)
    (hn : NodupIds (flatten (blocks f s))) {u : Item}
    (hci : CanIntegrate (flatten (blocks f s)) u) :
    ∀ (l r : Id) (c : MClient) (p : Nat) (b : MBlock), u.left = some l → u.right = some r →
      At s l c p b → ¬ (r.client = l.client ∧ b.clock < r.clock ∧ r.clock ≤ l.clock) := by
  intro l r c p b hl hr ha ⟨hc, h1, h2⟩
  obtain ⟨i, x, hs, hx, hid, hlen, _, hi, _⟩ := ha.item h
  have hge := ha.ge
  have hlt := ha.lt
  have hB : blockOf f x ∈ blocks f s := by
    unfold blocks
    exact List.mem_map.mpr ⟨i, hi, blockAt_of_core hx⟩
  obtain ⟨pre, post, e⟩ := List.append_of_mem hB
  rw [e] at hn hci
  have hBlen : (blockOf f x).len = x.len := blockOf_len f x
  have hBid : (blockOf f x).id = ⟨l.client, b.clock⟩ := hid
  have el : l = ⟨(blockOf f x).id.client, (blockOf f x).id.clock + (l.clock - b.clock)⟩ := by
    rw [hBid]
    show l = ⟨l.client, b.clock + (l.clock - b.clock)⟩
    have e0 : b.clock + (l.clock - b.clock) = l.clock := by omega
    rw [e0]
  have er : r = ⟨(blockOf f x).id.client, (blockOf f x).id.clock + (r.clock - b.clock)⟩ := by
    rw [hBid]
    show r = ⟨l.client, b.clock + (r.clock - b.clock)⟩
    have e0 : b.clock + (r.clock - b.clock) = r.clock := by omega
    rw [e0, ← hc]
  have hjl : l.clock - b.clock < (blockOf f x).len := by
    rw [hBlen, hlen]
    omega
  have hjr : r.clock - b.clock < (blockOf f x).len := by
    rw [hBlen, hlen]
    omega
  have ixl := ix_flatten_block hn hjl
  have ixr := ix_flatten_block hn hjr
  rw [← el] at ixl
  rw [← er] at ixr
  have hlr := hci.left_lt_right
  rw [hl, hr] at hlr
  have hlr' : ix (flatten (pre ++ blockOf f x :: post)) l <
      ix (flatten (pre ++ blockOf f x :: post)) r := hlr
  rw [ixl, ixr] at hlr'
  omega

/-! ## Deleting a range

`delete_range` on the timelines. `Held` and `Dead` are the clocks of a store
and its deleted clocks as its timelines give them; `Marking` is the state of
the loop that deletes the blocks of a range one after the other. -/

theorem mem_flatten_ids {bs : List Block} {z : Id} :
    z ∈ (flatten bs).map Item.id ↔ ∃ B, B ∈ bs ∧ z ∈ B.units.map Item.id := by
  constructor
  · intro hz
    obtain ⟨u, hu, e⟩ := List.mem_map.mp hz
    have hu' : u ∈ bs.flatMap Block.units := hu
    obtain ⟨B, hB, huB⟩ := List.mem_flatMap.mp hu'
    exact ⟨B, hB, List.mem_map.mpr ⟨u, huB, e⟩⟩
  · rintro ⟨B, hB, hz⟩
    obtain ⟨u, hu, e⟩ := List.mem_map.mp hz
    have hu' : u ∈ bs.flatMap Block.units := List.mem_flatMap.mpr ⟨B, hB, hu⟩
    exact List.mem_map.mpr ⟨u, hu', e⟩

/-- A timeline of the store holds the id `z`. -/
def Held (s : MStore) (z : Id) : Prop := ∃ (c : MClient) (p : Nat) (b : MBlock), At s z c p b

/-- A deleted block of a timeline of the store holds the id `z`. -/
def Dead (s : MStore) (z : Id) : Prop :=
  ∃ (c : MClient) (p : Nat) (b : MBlock), At s z c p b ∧ b.kind.dead = true

/-- A clock of a block of the sequence is in a block of a timeline, deleted
when the block is. -/
theorem at_of_block {f : Id → Char} {s : MStore} (h : WF s) {B : Block} {z : Id}
    (hB : B ∈ blocks f s) (hz : z ∈ B.units.map Item.id) :
    ∃ (c : MClient) (p : Nat) (b : MBlock), At s z c p b ∧ b.kind.dead = B.deleted := by
  obtain ⟨i, x, hi, hx, e⟩ := mem_blocks h hB
  rw [e] at hz ⊢
  obtain ⟨h1, h2, h3⟩ := mem_units_ids.mp hz
  rw [blockOf_len] at h3
  obtain ⟨c, p, b, ha, hs⟩ := h.at_of_contains hi hx h1 h2 h3
  obtain ⟨i', x', e1, e2, _, _, e5, _, _⟩ := ha.item h
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei, hx] at e2
  have ex : x = x' := Option.some.inj e2
  refine ⟨c, p, b, ha, ?_⟩
  rw [← e5, ← ex]
  rfl

/-- A clock of a block of a timeline is in a block of the sequence, deleted
when the block is. -/
theorem block_of_at {f : Id → Char} {s : MStore} (h : WF s) {z : Id} {c : MClient} {p : Nat}
    {b : MBlock} (ha : At s z c p b) :
    ∃ B, B ∈ blocks f s ∧ B.deleted = b.kind.dead ∧ z ∈ B.units.map Item.id := by
  obtain ⟨i, x, _, hx, hid, hl, hdel, hi, _⟩ := ha.item h
  have hlt := ha.lt
  have hge := ha.ge
  have hxc : x.id.client = z.client := by rw [hid]
  have hxk : x.id.clock = b.clock := by rw [hid]
  refine ⟨blockOf f x, List.mem_map.mpr ⟨i, hi, blockAt_of_core hx⟩, hdel, ?_⟩
  apply mem_units_ids.mpr
  rw [blockOf_len]
  exact ⟨hxc.symm, Nat.le_trans (Nat.le_of_eq hxk) hge, by
    show z.clock < x.id.clock + x.len
    omega⟩

/-- The clocks of the block sequence are the clocks of the timelines. -/
theorem held_iff {f : Id → Char} {s : MStore} (h : WF s) (z : Id) :
    z ∈ (flatten (blocks f s)).map Item.id ↔ Held s z := by
  rw [mem_flatten_ids]
  constructor
  · rintro ⟨B, hB, hz⟩
    obtain ⟨c, p, b, ha, _⟩ := at_of_block h hB hz
    exact ⟨c, p, b, ha⟩
  · rintro ⟨c, p, b, ha⟩
    obtain ⟨B, hB, _, hz⟩ := block_of_at (f := f) h ha
    exact ⟨B, hB, hz⟩

/-- The deleted clocks of the block sequence are the clocks of the deleted
blocks of the timelines. -/
theorem dead_iff {f : Id → Char} {s : MStore} (h : WF s) (z : Id) :
    z ∈ deletedSet (blocks f s) ↔ Dead s z := by
  rw [mem_deletedSet]
  constructor
  · rintro ⟨B, hB, hd, hz⟩
    obtain ⟨c, p, b, ha, e⟩ := at_of_block h hB hz
    exact ⟨c, p, b, ha, by rw [e]; exact hd⟩
  · rintro ⟨c, p, b, ha, hd⟩
    obtain ⟨B, hB, e, hz⟩ := block_of_at (f := f) h ha
    exact ⟨B, hB, by rw [e]; exact hd, hz⟩

/-- The timeline `ci` after `markDeleted`. -/
theorem markDeleted_client {s : MStore} {ci : Nat} (p i : Nat) {c : MClient}
    (hc : s.clients[ci]? = some c) :
    (markDeleted s ci p i).clients[ci]? =
      some { c with blocks := upd c.blocks p (fun b => { b with kind := MKind.deleted i }) } := by
  show (upd s.clients ci _)[ci]? = _
  rw [get?_upd_self, hc]
  rfl

/-- Deleting a block keeps the clocks of the store. -/
theorem held_markDeleted {s : MStore} (h : WF s) {ci p i : Nat} {c : MClient} {b : MBlock}
    (hc : s.clients[ci]? = some c) (hb : c.blocks[p]? = some b) (hs : b.kind.slot = some i)
    (z : Id) : Held (markDeleted s ci p i) z ↔ Held s z := by
  obtain ⟨i', x, e1, hx, _⟩ := h.block_item (get?_mem hc) hb
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei] at hx
  obtain ⟨hw, _⟩ := markDeleted_spec h hc hb hs hx
  have hg := markDeleted_grows h hc hb hs hx
  rw [← held_iff (f := fun _ => 'a') hw, ← held_iff (f := fun _ => 'a') h, hg.flat]

/-- Deleting a block deletes its clocks, and no other. -/
theorem dead_markDeleted {s : MStore} (h : WF s) {ci p i : Nat} {c : MClient} {b : MBlock}
    (hc : s.clients[ci]? = some c) (hb : c.blocks[p]? = some b) (hs : b.kind.slot = some i)
    (z : Id) :
    Dead (markDeleted s ci p i) z ↔
      Dead s z ∨
        (z.client = c.client ∧ b.clock ≤ z.clock ∧ z.clock < endAt c.blocks c.stop p) := by
  obtain ⟨i', x, e1, hx, hid, hlen, _, hi', _⟩ := h.block_item (get?_mem hc) hb
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei] at hx hi'
  obtain ⟨hw, ho, core_i, core_other⟩ := markDeleted_spec h hc hb hs hx
  have hg := markDeleted_grows h hc hb hs hx
  have hxc : x.id.client = c.client := by rw [hid]
  have hxk : x.id.clock = b.clock := by rw [hid]
  have hlt := (h.timeline c (get?_mem hc)).lt_end hb
  rw [← dead_iff (f := fun _ => 'a') hw, ← dead_iff (f := fun _ => 'a') h]
  constructor
  · intro hz
    obtain ⟨B, hB, hdel, hzB⟩ := mem_deletedSet.mp hz
    have hB' : B ∈ (order (markDeleted s ci p i)).map
        (blockAt (fun _ => 'a') (markDeleted s ci p i).items) := hB
    rw [ho] at hB'
    obtain ⟨j, hj, ej⟩ := List.mem_map.mp hB'
    rw [← ej] at hdel hzB
    by_cases e : j = i
    · right
      rw [e, blockAt_of_core core_i] at hzB
      obtain ⟨h1, h2, h3⟩ := mem_units_ids.mp hzB
      rw [blockOf_len] at h3
      have h1' : z.client = x.id.client := h1
      have h2' : x.id.clock ≤ z.clock := h2
      have h3' : z.clock < x.id.clock + x.len := h3
      exact ⟨h1'.trans hxc, by omega, by omega⟩
    · left
      obtain ⟨y, hy⟩ := h.core_of_mem hj
      have hy' : coreAt (markDeleted s ci p i).items j = some y := by
        rw [core_other j e]
        exact hy
      rw [blockAt_of_core hy'] at hdel hzB
      exact mem_deletedSet.mpr
        ⟨blockOf (fun _ => 'a') y, List.mem_map.mpr ⟨j, hj, blockAt_of_core hy⟩, hdel, hzB⟩
  · rintro (hz | ⟨h1, h2, h3⟩)
    · exact hg.dels _ z hz
    · apply mem_deletedSet.mpr
      refine ⟨blockAt (fun _ => 'a') (markDeleted s ci p i).items i, ?_, ?_, ?_⟩
      · show _ ∈ (order (markDeleted s ci p i)).map _
        rw [ho]
        exact List.mem_map.mpr ⟨i, hi', rfl⟩
      · rw [blockAt_of_core core_i]
        rfl
      · rw [blockAt_of_core core_i]
        apply mem_units_ids.mpr
        rw [blockOf_len]
        show z.client = x.id.client ∧ x.id.clock ≤ z.clock ∧ z.clock < x.id.clock + x.len
        exact ⟨h1.trans hxc.symm, by omega, by omega⟩

/-- No live block of the timeline `ci` holds the clock `z` after its first
clock: `z` is a block boundary, or in a deleted block, or not there. -/
def NoStraddle (s : MStore) (ci z : Nat) : Prop :=
  ∀ (c : MClient) (p : Nat) (b : MBlock), s.clients[ci]? = some c → c.blocks[p]? = some b →
    b.kind.dead = false → b.clock < z → endAt c.blocks c.stop p ≤ z

theorem noStraddle_none {s : MStore} {ci z : Nat} {c : MClient} (hc : s.clients[ci]? = some c)
    (hno : ∀ p, ¬ Holds c.blocks c.stop p z) : NoStraddle s ci z := by
  intro c' q a hc' ha _ hlt
  rw [hc] at hc'
  have ec : c = c' := Option.some.inj hc'
  subst ec
  by_cases hz : z < endAt c.blocks c.stop q
  · exact absurd ⟨a, ha, Nat.le_of_lt hlt, hz⟩ (hno q)
  · omega

theorem noStraddle_at {s : MStore} {ci z p : Nat} {c : MClient} {b : MBlock}
    (hc : s.clients[ci]? = some c) (ht : TimelineWF c.blocks c.stop)
    (hp : Holds c.blocks c.stop p z) (hb : c.blocks[p]? = some b)
    (hk : b.kind.dead = true ∨ b.clock = z) : NoStraddle s ci z := by
  intro c' q a hc' ha hlive hlt
  rw [hc] at hc'
  have ec : c = c' := Option.some.inj hc'
  subst ec
  by_cases hz : z < endAt c.blocks c.stop q
  · have e : q = p := ht.holds_unique ⟨a, ha, Nat.le_of_lt hlt, hz⟩ hp
    rw [e, hb] at ha
    have eb : b = a := Option.some.inj ha
    rw [← eb] at hlive hlt
    rcases hk with hd | he
    · rw [hlive] at hd
      cases hd
    · omega
  · omega

theorem NoStraddle.markDeleted {s : MStore} {ci z : Nat} (p i : Nat) {c : MClient}
    (hc : s.clients[ci]? = some c) (hn : NoStraddle s ci z) :
    NoStraddle (markDeleted s ci p i) ci z := by
  intro c' q a hc' ha hlive hlt
  rw [markDeleted_client p i hc] at hc'
  have ec := Option.some.inj hc'
  subst ec
  have ha' : (upd c.blocks p (fun b => { b with kind := MKind.deleted i }))[q]? = some a := ha
  show endAt (upd c.blocks p (fun b => { b with kind := MKind.deleted i })) c.stop q ≤ z
  rw [endAt_upd (g := fun b => { b with kind := MKind.deleted i }) (fun _ => rfl) q]
  rcases get?_upd_cases ha' with ⟨_, a', _, ea⟩ | ⟨_, ha''⟩
  · rw [ea] at hlive
    have hf : (true : Bool) = false := hlive
    cases hf
  · exact hn c q a hc ha'' hlive hlt

/-- The timeline `ci` after `splitNode` of its block `b`. -/
theorem splitNode_client {s : MStore} (h : WF s) {ci p i d : Nat} {c : MClient} {b : MBlock}
    {x : MItem} (hc : s.clients[ci]? = some c) (hb : c.blocks[p]? = some b)
    (hs : b.kind.slot = some i) (hx : coreAt s.items i = some x) :
    (splitNode s ci p i d).clients[ci]? =
      some (c.withBlock (p + 1) ⟨b.clock + d, b.kind.reslot s.items.length⟩) := by
  obtain ⟨i', x', e1, e2, e3, _⟩ := h.block_item (get?_mem hc) hb
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei, hx] at e2
  have ex : x = x' := Option.some.inj e2
  rw [← ex] at e3
  have hyclock : (itemAt s.items i).id.clock = b.clock := by
    have e : (itemAt s.items i).core.id = x.id := congrArg MItem.id (itemAt_core hx)
    have e' : (itemAt s.items i).id = x.id := e
    rw [e', e3]
  show (upd s.clients ci _)[ci]? = _
  rw [get?_upd_self, hc]
  show some (c.withBlock (p + 1) ⟨(itemAt s.items i).id.clock + d,
    ((c.blocks[p]?).getD default).kind.reslot s.items.length⟩) = _
  rw [hyclock, hb]
  rfl

/-- A split makes the clock it splits at a block boundary, and keeps the
boundaries there were. -/
theorem splitNode_noStraddle {s : MStore} (h : WF s) {ci p i d : Nat} {c : MClient} {b : MBlock}
    {x : MItem} (hc : s.clients[ci]? = some c) (hb : c.blocks[p]? = some b)
    (hs : b.kind.slot = some i) (hx : coreAt s.items i = some x) (hd : d < x.len) :
    NoStraddle (splitNode s ci p i d) ci (b.clock + d) ∧
      ∀ z, NoStraddle s ci z → NoStraddle (splitNode s ci p i d) ci z := by
  have hcm := get?_mem hc
  obtain ⟨i', x', e1, e2, _, e4, _⟩ := h.block_item hcm hb
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei, hx] at e2
  have ex : x = x' := Option.some.inj e2
  rw [← ex] at e4
  have htl := h.timeline c hcm
  have hpl := get?_lt hb
  have hle : p + 1 ≤ c.blocks.length := by omega
  have hlt := htl.lt_end hb
  have hcl := splitNode_client (d := d) h hc hb hs hx
  have hnd : (b.kind.reslot s.items.length).dead = b.kind.dead := MKind.dead_reslot _ _
  constructor
  · intro c' q a hc' ha _ hlt'
    rw [hcl] at hc'
    have ec := Option.some.inj hc'
    subst ec
    have ha' : (insAt c.blocks (p + 1) ⟨b.clock + d, b.kind.reslot s.items.length⟩)[q]? =
        some a := ha
    show endAt (insAt c.blocks (p + 1) ⟨b.clock + d, b.kind.reslot s.items.length⟩) c.stop q ≤
      _
    rcases get?_insAt_cases hle ha' with ⟨hq, ha''⟩ | ⟨_, ea⟩ | ⟨q', eq, hq', ha''⟩
    · by_cases e : q = p
      · rw [endAt_insAt_eq (q := q) _ (by omega) hle]
        exact Nat.le_refl _
      · rw [endAt_insAt_lt (q := q) _ (by omega) hle]
        have := htl.end_le (show q < p by omega) hb
        omega
    · rw [ea] at hlt'
      exact absurd hlt' (Nat.lt_irrefl _)
    · have := htl.end_le (show p < q' by omega) ha''
      omega
  · intro z hn c' q a hc' ha hlive hlt'
    rw [hcl] at hc'
    have ec := Option.some.inj hc'
    subst ec
    have ha' : (insAt c.blocks (p + 1) ⟨b.clock + d, b.kind.reslot s.items.length⟩)[q]? =
        some a := ha
    show endAt (insAt c.blocks (p + 1) ⟨b.clock + d, b.kind.reslot s.items.length⟩) c.stop q ≤
      z
    rcases get?_insAt_cases hle ha' with ⟨hq, ha''⟩ | ⟨eq, ea⟩ | ⟨q', eq, hq', ha''⟩
    · by_cases e : q = p
      · rw [endAt_insAt_eq (q := q) _ (by omega) hle]
        rw [e, hb] at ha''
        have eb : b = a := Option.some.inj ha''
        rw [← eb] at hlive hlt'
        have := hn c p b hc hb hlive hlt'
        show b.clock + d ≤ z
        omega
      · rw [endAt_insAt_lt (q := q) _ (by omega) hle]
        exact hn c q a hc ha'' hlive hlt'
    · rw [eq, endAt_insAt_self]
      rw [ea] at hlive hlt'
      have hlive' : b.kind.dead = false := by rw [← hnd]; exact hlive
      have hlt'' : b.clock + d < z := hlt'
      exact hn c p b hc hb hlive' (by omega)
    · rw [eq, endAt_insAt_gt _ hq']
      exact hn c q' a hc ha'' hlive hlt'

/-- A block that keeps its start holds the clocks it held. -/
theorem Holds.upd {blocks : List MBlock} {stop p x : Nat} (i : Nat) {g : MBlock → MBlock}
    (hg : ∀ b, (g b).clock = b.clock) (h : Holds blocks stop p x) :
    Holds (ListAux.upd blocks i g) stop p x := by
  obtain ⟨a, ha, h1, h2⟩ := h
  have h2' : x < endAt (ListAux.upd blocks i g) stop p := by
    rw [endAt_upd hg]
    exact h2
  by_cases e : p = i
  · refine ⟨g a, ?_, by rw [hg]; exact h1, h2'⟩
    rw [e, get?_upd_self, ← e, ha]
    rfl
  · exact ⟨a, by rw [get?_upd_ne _ _ e]; exact ha, h1, h2'⟩

/-- The state of `delete_range` while it deletes the blocks of the timeline
`ci` from the block `pos0`, which holds `start`, on: `m` is the store it
started from, `t` the store when it is done with the blocks before `pos`. -/
structure Marking (m t : MStore) (ci client start stop pos0 pos : Nat) : Prop where
  wf : WF t
  flat : ∀ f : Id → Char, flatten (blocks f t) = flatten (blocks f m)
  held : ∀ z, Held t z ↔ Held m z
  sub : ∀ z, Dead t z →
    Dead m z ∨ (Held m z ∧ z.client = client ∧ start ≤ z.clock ∧ z.clock < stop)
  sup : ∀ z, Dead m z → Dead t z
  timeline : ∃ c, t.clients[ci]? = some c ∧ c.client = client ∧
    Holds c.blocks c.stop pos0 start ∧
    ∀ (q : Nat) (b : MBlock), pos0 ≤ q → q < pos → c.blocks[q]? = some b →
      b.kind.dead = true
  first : NoStraddle t ci start
  last : NoStraddle t ci stop
  le : pos0 ≤ pos

theorem Marking.init {m : MStore} {ci client start stop pos0 : Nat} {c : MClient} (h : WF m)
    (hc : m.clients[ci]? = some c) (hcl : c.client = client)
    (hp : Holds c.blocks c.stop pos0 start) (h1 : NoStraddle m ci start)
    (h2 : NoStraddle m ci stop) : Marking m m ci client start stop pos0 pos0 :=
  { wf := h
    flat := fun _ => rfl
    held := fun _ => Iff.rfl
    sub := fun _ hz => Or.inl hz
    sup := fun _ hz => hz
    timeline := ⟨c, hc, hcl, hp, fun _ _ h1 h2 _ => absurd h2 (Nat.not_lt.mpr h1)⟩
    first := h1
    last := h2
    le := Nat.le_refl _ }

/-- A block that is deleted already is passed over. -/
theorem Marking.skip {m t : MStore} {ci client start stop pos0 pos : Nat} {c : MClient}
    {b : MBlock} (h : Marking m t ci client start stop pos0 pos) (hc : t.clients[ci]? = some c)
    (hb : c.blocks[pos]? = some b) (hd : b.kind.dead = true) :
    Marking m t ci client start stop pos0 (pos + 1) := by
  obtain ⟨c0, hc0, hcl, hp0, hdone⟩ := h.timeline
  rw [hc] at hc0
  have ec : c = c0 := Option.some.inj hc0
  subst ec
  refine { h with timeline := ⟨c, hc, hcl, hp0, ?_⟩, le := Nat.le_succ_of_le h.le }
  intro q a hq1 hq2 ha
  by_cases e : q = pos
  · rw [e, hb] at ha
    rw [← Option.some.inj ha]
    exact hd
  · exact hdone q a hq1 (by omega) ha

/-- A live block that starts before `stop` is deleted: it lies in the range. -/
theorem Marking.mark {m t : MStore} {ci client start stop pos0 pos i : Nat} {c : MClient}
    {b : MBlock} (h : Marking m t ci client start stop pos0 pos) (hc : t.clients[ci]? = some c)
    (hb : c.blocks[pos]? = some b) (hk : b.kind = MKind.item i) (hlt : b.clock < stop) :
    Marking m (markDeleted t ci pos i) ci client start stop pos0 (pos + 1) := by
  obtain ⟨c0, hc0, hcl, hp0, hdone⟩ := h.timeline
  rw [hc] at hc0
  have ec : c = c0 := Option.some.inj hc0
  subst ec
  have hs : b.kind.slot = some i := by rw [hk]; rfl
  have hlive : b.kind.dead = false := by rw [hk]; rfl
  obtain ⟨i', x, e1, hx, _⟩ := h.wf.block_item (get?_mem hc) hb
  have ei : i' = i := Option.some.inj (e1.symm.trans hs)
  rw [ei] at hx
  obtain ⟨hw, _⟩ := markDeleted_spec h.wf hc hb hs hx
  have hg := markDeleted_grows h.wf hc hb hs hx
  have htl := h.wf.timeline c (get?_mem hc)
  have hge : start ≤ b.clock := by
    obtain ⟨a, ha, _, ha2⟩ := hp0
    by_cases e : pos = pos0
    · by_cases hl : b.clock < start
      · have := h.first c pos b hc hb hlive hl
        rw [e] at this
        omega
      · omega
    · have := htl.end_le (show pos0 < pos by have := h.le; omega) hb
      omega
  have hend : endAt c.blocks c.stop pos ≤ stop := h.last c pos b hc hb hlive hlt
  refine
    { wf := hw
      flat := fun f => (hg.flat f).trans (h.flat f)
      held := fun z => (held_markDeleted h.wf hc hb hs z).trans (h.held z)
      sub := ?_
      sup := fun z hz => (dead_markDeleted h.wf hc hb hs z).mpr (Or.inl (h.sup z hz))
      timeline := ⟨_, markDeleted_client pos i hc, hcl,
        hp0.upd pos (g := fun b => { b with kind := MKind.deleted i }) (fun _ => rfl), ?_⟩
      first := h.first.markDeleted pos i hc
      last := h.last.markDeleted pos i hc
      le := Nat.le_succ_of_le h.le }
  · intro z hz
    rcases (dead_markDeleted h.wf hc hb hs z).mp hz with hz' | ⟨h1, h2, h3⟩
    · exact h.sub z hz'
    · right
      refine ⟨(h.held z).mp ⟨c, pos, b, ⟨get?_mem hc, h1.symm, hb, h2, h3⟩⟩, h1.trans hcl,
        ?_, ?_⟩
      · omega
      · omega
  · intro q a hq1 hq2 ha
    have ha' : (upd c.blocks pos (fun b => { b with kind := MKind.deleted i }))[q]? = some a := ha
    rcases get?_upd_cases ha' with ⟨_, a', _, ea⟩ | ⟨hne, ha''⟩
    · rw [ea]
      rfl
    · exact hdone q a hq1 (by omega) ha''

/-- **What the loop has deleted when it stops**: the deletions there were,
and the clocks of the client in `start..stop` the store holds. -/
theorem Marking.final {m t : MStore} {ci client start stop pos0 pos : Nat}
    (h : Marking m t ci client start stop pos0 pos)
    (hexit : ∀ (c : MClient) (b : MBlock), t.clients[ci]? = some c → c.blocks[pos]? = some b →
      stop ≤ b.clock) (z : Id) :
    Dead t z ↔
      Dead m z ∨ (Held m z ∧ z.client = client ∧ start ≤ z.clock ∧ z.clock < stop) := by
  constructor
  · exact h.sub z
  · rintro (hz | ⟨hh, h1, h2, h3⟩)
    · exact h.sup z hz
    · obtain ⟨c', q, b, ha⟩ := (h.held z).mpr hh
      obtain ⟨c, hc, hcl, ⟨a, ha0, ha1, _⟩, hdone⟩ := h.timeline
      have ec : c' = c :=
        h.wf.client_unique ha.mem (get?_mem hc) (by rw [ha.client, h1, hcl])
      rw [ec] at ha
      have htl := h.wf.timeline c (get?_mem hc)
      have hlt := ha.lt
      have hge := ha.ge
      refine ⟨c, q, b, ha, hdone q b ?_ ?_ ha.block⟩
      · by_cases hq : q < pos0
        · have := htl.end_le hq ha0
          omega
        · omega
      · by_cases hq : q < pos
        · exact hq
        · exfalso
          have hql := get?_lt ha.block
          obtain ⟨bp, hbp⟩ := get?_some (show pos < c.blocks.length by omega)
          have h5 := hexit c bp hc hbp
          have h6 : bp.clock ≤ b.clock := by
            by_cases e : pos = q
            · rw [e, ha.block] at hbp
              rw [← Option.some.inj hbp]
              exact Nat.le_refl _
            · exact Nat.le_of_lt (htl.sorted pos q bp b (by omega) hbp ha.block)
          omega

end YoctoCore.Properties.YataModel
