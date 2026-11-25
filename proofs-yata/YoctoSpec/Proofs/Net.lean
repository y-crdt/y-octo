/-
Strong eventual consistency of the unit-level model.

`Net` is a set of replicas (one per client id) that create items between two
adjacent items of their own state, and receive the items of the others in any
order that respects their dependencies: the origins of an item and the earlier
items of its client. `sec` shows that replicas that integrated the same items
hold the same sequence.
-/
import YoctoSpec.Proofs.Order

namespace YoctoSpec

/-! ### Local insertion -/

theorem lt_nextClock {s : List Item} {a : Item} {c : Nat} (ha : a ∈ s) (hc : a.id.client = c) :
    a.id.clock < nextClock s c := by
  induction s with
  | nil => cases ha
  | cons b t ih =>
    rw [nextClock]
    rcases List.mem_cons.mp ha with e | h
    · rw [← e, ite_eq_left hc]
      omega
    · have := ih h
      by_cases hb : b.id.client = c
      · rw [ite_eq_left hb]
        omega
      · rw [ite_eq_right hb]
        exact this

theorem idAt_zero (s : List Item) : idAt s 0 = none := by
  cases s <;> simp [idAt]

theorem idAt_mem {s : List Item} {j : Nat} {x : Id} (h : idAt s j = some x) :
    ∃ a, a ∈ s ∧ a.id = x := by
  induction s generalizing j with
  | nil => cases j <;> simp [idAt] at h
  | cons a t ih =>
    cases j with
    | zero => simp [idAt] at h
    | succ j =>
      rw [idAt] at h
      by_cases hj : j = 0
      · rw [ite_eq_left hj] at h
        exact ⟨a, List.mem_cons_self .., Option.some.inj h⟩
      · rw [ite_eq_right hj] at h
        obtain ⟨b, hb, e⟩ := ih h
        exact ⟨b, List.mem_cons_of_mem _ hb, e⟩

theorem ix_idAt {s : List Item} (hn : NodupIds s) {j : Nat} (h₁ : 1 ≤ j) (h₂ : j ≤ s.length) :
    ∃ a, a ∈ s ∧ idAt s j = some a.id ∧ ix s a.id = j := by
  induction s generalizing j with
  | nil =>
    rw [List.length_nil] at h₂
    omega
  | cons a t ih =>
    have hn' := List.pairwise_cons.mp hn
    cases j with
    | zero => omega
    | succ j =>
      by_cases hj : j = 0
      · refine ⟨a, List.mem_cons_self .., ?_, ?_⟩
        · rw [idAt, ite_eq_left hj]
        · rw [ix_cons_self]
          omega
      · rw [List.length_cons] at h₂
        obtain ⟨b, hb, e₁, e₂⟩ := ih hn'.2 (j := j) (by omega) (by omega)
        refine ⟨b, List.mem_cons_of_mem _ hb, ?_, ?_⟩
        · rw [idAt, ite_eq_right hj]
          exact e₁
        · rw [ix_cons_ne (hn'.1 b hb), e₂]

theorem idAt_none_of_gt {s : List Item} {j : Nat} (h : s.length < j) : idAt s j = none := by
  induction s generalizing j with
  | nil => cases j <;> simp [idAt]
  | cons a t ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [List.length_cons] at h
      rw [idAt, ite_eq_right (by omega), ih (by omega)]

theorem ixL_idAt {s : List Item} (hn : NodupIds s) {k : Nat} (hk : k ≤ s.length) :
    ixL s (idAt s k) = k := by
  by_cases h0 : k = 0
  · rw [h0, idAt_zero, ixL_none]
  · obtain ⟨a, _, e₁, e₂⟩ := ix_idAt hn (by omega) hk
    rw [e₁, ixL_some, e₂]

theorem ixR_idAt {s : List Item} (hn : NodupIds s) {j : Nat} (h₁ : 1 ≤ j)
    (h₂ : j ≤ s.length + 1) : ixR s (idAt s j) = j := by
  by_cases h : j ≤ s.length
  · obtain ⟨a, _, e₁, e₂⟩ := ix_idAt hn h₁ h
    rw [e₁, ixR_some, e₂]
  · rw [idAt_none_of_gt (by omega), ixR_none]
    omega

theorem present_idAt (s : List Item) (j : Nat) : Present s (idAt s j) := by
  intro x hx
  exact ix_le_length_iff.mpr (idAt_mem hx)

/-- The item was created between two adjacent items of `s₀`. -/
structure Adj (s₀ : List Item) (i : Item) : Prop where
  left_mem : Present s₀ i.left
  right_mem : Present s₀ i.right
  adj : ixR s₀ i.right = ixL s₀ i.left + 1

theorem mkItem_adj {s : List Item} (hs : Legal s) (c : Nat) {k : Nat} (hk : k ≤ s.length) :
    Adj s (mkItem s c k) where
  left_mem := present_idAt s k
  right_mem := present_idAt s (k + 1)
  adj := by
    have eL : ixL s (mkItem s c k).left = k := ixL_idAt hs.nodup hk
    have eR : ixR s (mkItem s c k).right = k + 1 := ixR_idAt hs.nodup (by omega) (by omega)
    rw [eL, eR]

/-- A locally created item can be integrated where it was created. -/
theorem mkItem_canIntegrate {s : List Item} (hs : Legal s) (c : Nat) {k : Nat}
    (hk : k ≤ s.length) : CanIntegrate s (mkItem s c k) := by
  have eL : ixL s (mkItem s c k).left = k := ixL_idAt hs.nodup hk
  have eR : ixR s (mkItem s c k).right = k + 1 := ixR_idAt hs.nodup (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha e
    have hcl : a.id.client = c := congrArg Id.client e
    have hck : a.id.clock = nextClock s c := congrArg Id.clock e
    have := lt_nextClock ha hcl
    omega
  · exact present_idAt s k
  · exact present_idAt s (k + 1)
  · rw [eL, eR]
    omega
  · intro y hy hr
    have := hs.left_lt y hy
    rw [hr, ixR_some] at eR
    rw [eL]
    omega
  · intro y hy _
    rw [eL, eR]
    omega

/-- An item with a new id can be integrated between the two adjacent items it
was created between. -/
theorem canIntegrate_of_adj {s : List Item} {i : Item} (hs : Legal s) (hadj : Adj s i)
    (hfresh : ∀ a, a ∈ s → a.id ≠ i.id) : CanIntegrate s i := by
  have e := hadj.adj
  refine ⟨hfresh, hadj.left_mem, hadj.right_mem, by omega, ?_, ?_⟩
  · intro y hy hr
    have := hs.left_lt y hy
    rw [hr, ixR_some] at e
    omega
  · intro y hy _
    omega

/-! ### Remote delivery -/

/-- What a replica needs to integrate a created item: the item is new to it,
its origins are integrated, and every item of its client the replica holds has
a smaller clock (the items of one client are delivered in clock order). -/
structure Ready (s : List Item) (i : Item) : Prop where
  fresh : ∀ a, a ∈ s → a.id ≠ i.id
  left_mem : Present s i.left
  right_mem : Present s i.right
  clock : ∀ a, a ∈ s → a.id.client = i.id.client → a.id.clock < i.id.clock

/-- An item created between adjacent items of a legal sequence `s₀` can be
integrated into any legal sequence that is ready for it. -/
theorem canIntegrate_of_witness {s s₀ : List Item} {i : Item} (hs : Legal s) (h0 : Legal s₀)
    (hc : Compat s₀ s) (hadj : Adj s₀ i) (hr : Ready s i)
    (hcl : ∀ y, y ∈ s → y.id.client = i.id.client → y ∈ s₀) : CanIntegrate s i := by
  have hadj' := hadj.adj
  -- an origin of `i`, as an item of both sequences
  have common : ∀ x, ix s₀ x ≤ s₀.length → ix s x ≤ s.length →
      ∃ u, u ∈ s₀ ∧ u ∈ s ∧ u.id = x := fun x h₁ h₂ => common_of_present hc h₁ h₂
  have xfer : ∀ u v, u ∈ s₀ → u ∈ s → v ∈ s₀ → v ∈ s → ix s₀ u.id ≤ ix s₀ v.id →
      ix s u.id ≤ ix s v.id := fun u v h₁ h₂ h₃ h₄ h => stable_le h0 hs hc h₁ h₂ h₃ h₄ h
  refine ⟨hr.fresh, hr.left_mem, hr.right_mem, ?_, ?_, ?_⟩
  · -- left origin before right origin
    cases hl : i.left with
    | none =>
      rw [ixL_none]
      have := ixR_pos s i.right
      omega
    | some x =>
      cases hrr : i.right with
      | none =>
        rw [ixL_some, ixR_none]
        have := hr.left_mem x hl
        omega
      | some y =>
        rw [ixL_some, ixR_some]
        rw [hl, hrr, ixL_some, ixR_some] at hadj'
        obtain ⟨u, hu0, hus, eu⟩ := common x (hadj.left_mem x hl) (hr.left_mem x hl)
        obtain ⟨v, hv0, hvs, ev⟩ := common y (hadj.right_mem y hrr) (hr.right_mem y hrr)
        rw [← eu, ← ev] at hadj' ⊢
        exact stable h0 hs hc u v hu0 hus hv0 hvs (by omega)
  · -- the left origin of the right origin
    intro y hy hry
    obtain ⟨w, hw0, hws, ew⟩ := common y.id (hadj.right_mem y.id hry) (ix_mem hy)
    have hwy : w = y := hs.nodup.eq_of_id hws hy ew
    rw [hwy] at hw0
    have h₁ := h0.left_lt y hw0
    rw [hry, ixR_some] at hadj'
    cases hyl : y.left with
    | none =>
      rw [ixL_none]
      exact Nat.zero_le _
    | some x =>
      rw [hyl, ixL_some] at h₁
      have hx0 : ix s₀ x ≤ s₀.length := h0.left_present hw0 x hyl
      have hxs : ix s x ≤ s.length := hs.left_present hy x hyl
      obtain ⟨u, hu0, hus, eu⟩ := common x hx0 hxs
      cases hl : i.left with
      | none =>
        rw [hl, ixL_none] at hadj'
        have := ix_pos s₀ x
        omega
      | some z =>
        rw [hl, ixL_some] at hadj'
        obtain ⟨v, hv0, hvs, ev⟩ := common z (hadj.left_mem z hl) (hr.left_mem z hl)
        rw [ixL_some, ixL_some]
        rw [← eu] at h₁ ⊢
        rw [← ev] at hadj' ⊢
        exact xfer u v hu0 hus hv0 hvs (by omega)
  · -- items of the same client
    intro y hy hyc
    have hy0 := hcl y hy hyc
    have hy0n := ix_mem hy0
    by_cases hside : ix s₀ y.id ≤ ixL s₀ i.left
    · left
      cases hl : i.left with
      | none =>
        rw [hl, ixL_none] at hside
        have := ix_pos s₀ y.id
        omega
      | some z =>
        rw [hl, ixL_some] at hside
        obtain ⟨v, hv0, hvs, ev⟩ := common z (hadj.left_mem z hl) (hr.left_mem z hl)
        rw [ixL_some]
        rw [← ev] at hside ⊢
        exact xfer y v hy0 hy hv0 hvs hside
    · right
      cases hrr : i.right with
      | none =>
        rw [hrr, ixR_none] at hadj'
        omega
      | some z =>
        rw [hrr, ixR_some] at hadj'
        obtain ⟨v, hv0, hvs, ev⟩ := common z (hadj.right_mem z hrr) (hr.right_mem z hrr)
        rw [ixR_some]
        rw [← ev] at hadj' ⊢
        exact xfer v y hv0 hvs hy0 hy (by omega)

/-! ### The network -/

/-- Replica states, every insertion created so far and every deletion created
so far. The replica `r` is the only one that creates items of client `r`. -/
structure Net where
  st : Nat → Doc
  ops : List Item
  dels : List Id

def Net.init : Net := { st := fun _ => Doc.empty, ops := [], dels := [] }

def Net.set (n : Net) (r : Nat) (d : Doc) : Nat → Doc :=
  fun r' => if r' = r then d else n.st r'

/-- Replica `r` creates the item `i` and integrates it. -/
def Net.gen (n : Net) (r : Nat) (i : Item) : Net :=
  { st := n.set r ((n.st r).integrate i), ops := i :: n.ops, dels := n.dels }

/-- Replica `r` integrates the item `i` created elsewhere. -/
def Net.deliver (n : Net) (r : Nat) (i : Item) : Net :=
  { st := n.set r ((n.st r).integrate i), ops := n.ops, dels := n.dels }

/-- Replica `r` deletes `x`. -/
def Net.delete (n : Net) (r : Nat) (x : Id) : Net :=
  { st := n.set r ((n.st r).delete x), ops := n.ops, dels := x :: n.dels }

/-- Replica `r` applies the deletion of `x` created elsewhere. -/
def Net.deliverDelete (n : Net) (r : Nat) (x : Id) : Net :=
  { st := n.set r ((n.st r).delete x), ops := n.ops, dels := n.dels }

inductive Step : Net → Net → Prop
  /-- replica `r` creates an item with its next clock between two adjacent
  items of its own sequence -/
  | gen (n : Net) (r : Nat) (i : Item) (hid : i.id = ⟨r, nextClock (n.st r).items r⟩)
      (hadj : Adj (n.st r).items i) : Step n (n.gen r i)
  | deliver (n : Net) (r : Nat) (i : Item) (hi : i ∈ n.ops) (hr : Ready (n.st r).items i) :
      Step n (n.deliver r i)
  | delete (n : Net) (r : Nat) (x : Id) : Step n (n.delete r x)
  | deliverDelete (n : Net) (r : Nat) (x : Id) (hx : x ∈ n.dels) : Step n (n.deliverDelete r x)

inductive Reachable : Net → Prop
  | init : Reachable Net.init
  | step {n n' : Net} : Reachable n → Step n n' → Reachable n'

theorem Net.set_same (n : Net) (r : Nat) (d : Doc) : n.set r d r = d := by
  unfold Net.set
  exact ite_eq_left rfl

theorem Net.set_ne (n : Net) {r r' : Nat} (d : Doc) (h : r' ≠ r) : n.set r d r' = n.st r' := by
  unfold Net.set
  exact ite_eq_right h

/-- Invariant of the network. -/
structure Inv (n : Net) : Prop where
  legal : ∀ r, Legal (n.st r).items
  /-- replicas hold created items only -/
  sub : ∀ r a, a ∈ (n.st r).items → a ∈ n.ops
  uniq : ∀ a, a ∈ n.ops → ∀ b, b ∈ n.ops → a.id = b.id → a = b
  /-- a replica holds everything it created -/
  own : ∀ a, a ∈ n.ops → a ∈ (n.st a.id.client).items
  /-- every item was created between adjacent items of a legal sequence that
  held the earlier items of its client -/
  wit : ∀ i, i ∈ n.ops → ∃ s₀, Legal s₀ ∧ (∀ a, a ∈ s₀ → a ∈ n.ops) ∧ Adj s₀ i ∧
    (∀ j, j ∈ n.ops → j.id.client = i.id.client → j.id.clock < i.id.clock → j ∈ s₀)

theorem inv_init : Inv Net.init where
  legal := fun _ => legal_nil
  sub := by
    intro r a ha
    have ha' : a ∈ ([] : List Item) := ha
    cases ha'
  uniq := by
    intro a ha
    have ha' : a ∈ ([] : List Item) := ha
    cases ha'
  own := by
    intro a ha
    have ha' : a ∈ ([] : List Item) := ha
    cases ha'
  wit := by
    intro i hi
    have hi' : i ∈ ([] : List Item) := hi
    cases hi'

/-- A newly created item can be integrated by its creator. -/
theorem canIntegrate_gen {s : List Item} (hs : Legal s) {r : Nat} {i : Item}
    (hid : i.id = ⟨r, nextClock s r⟩) (hadj : Adj s i) : CanIntegrate s i := by
  have hcl : i.id.client = r := by rw [hid]
  have hck : i.id.clock = nextClock s r := by rw [hid]
  apply canIntegrate_of_adj hs hadj
  intro a ha e
  have h₁ : a.id.client = r := by rw [e, hcl]
  have h₂ := lt_nextClock ha h₁
  rw [e, hck] at h₂
  omega

theorem Inv.gen {n : Net} (h : Inv n) (r : Nat) {i : Item}
    (hid : i.id = ⟨r, nextClock (n.st r).items r⟩) (hadj : Adj (n.st r).items i) :
    Inv (n.gen r i) := by
  have hs := h.legal r
  have hcl : i.id.client = r := by rw [hid]
  have hck : i.id.clock = nextClock (n.st r).items r := by rw [hid]
  have hci : CanIntegrate (n.st r).items i := canIntegrate_gen hs hid hadj
  have F1 : (n.gen r i).ops = i :: n.ops := rfl
  have F2 : ((n.gen r i).st r).items = integrate (n.st r).items i := by
    show (n.set r _ r).items = _
    rw [Net.set_same]
    rfl
  have F3 : ∀ r', r' ≠ r → (n.gen r i).st r' = n.st r' := fun r' e => Net.set_ne n _ e
  -- an older item of client `r` is in the state of `r`, hence has a smaller clock
  have older : ∀ a, a ∈ n.ops → a.id.client = r →
      a ∈ (n.st r).items ∧ a.id.clock < i.id.clock := by
    intro a ha e
    have hm := h.own a ha
    rw [e] at hm
    have := lt_nextClock hm e
    exact ⟨hm, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r'
    by_cases e : r' = r
    · rw [e, F2]
      exact legal_integrate hs hci
    · rw [F3 r' e]
      exact h.legal r'
  · intro r' a ha
    rw [F1]
    by_cases e : r' = r
    · rw [e, F2] at ha
      rcases mem_integrate.mp ha with e' | h'
      · rw [e']
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (h.sub r a h')
    · rw [F3 r' e] at ha
      exact List.mem_cons_of_mem _ (h.sub r' a ha)
  · intro a ha b hb e
    rw [F1] at ha hb
    rcases List.mem_cons.mp ha with ea | ha'
    · rcases List.mem_cons.mp hb with eb | hb'
      · rw [ea, eb]
      · exfalso
        rw [ea] at e
        have hbr : b.id.client = r := by rw [← e, hcl]
        exact hci.fresh b (older b hb' hbr).1 e.symm
    · rcases List.mem_cons.mp hb with eb | hb'
      · exfalso
        rw [eb] at e
        have har : a.id.client = r := by rw [e, hcl]
        exact hci.fresh a (older a ha' har).1 e
      · exact h.uniq a ha' b hb' e
  · intro a ha
    rw [F1] at ha
    rcases List.mem_cons.mp ha with ea | ha'
    · rw [ea, hcl, F2]
      exact mem_integrate.mpr (Or.inl rfl)
    · by_cases e : a.id.client = r
      · rw [e, F2]
        exact mem_integrate.mpr (Or.inr (older a ha' e).1)
      · rw [F3 _ e]
        exact h.own a ha'
  · intro j hj
    rw [F1] at hj ⊢
    rcases List.mem_cons.mp hj with ej | hj'
    · refine ⟨(n.st r).items, hs, ?_, ?_, ?_⟩
      · intro a ha
        exact List.mem_cons_of_mem _ (h.sub r a ha)
      · rw [ej]
        exact hadj
      · intro j' hj' e₁ e₂
        rw [ej] at e₁ e₂
        rcases List.mem_cons.mp hj' with e' | h'
        · rw [e'] at e₂
          omega
        · exact (older j' h' (by rw [e₁, hcl])).1
    · obtain ⟨s₀, l0, sub0, adj0, own0⟩ := h.wit j hj'
      refine ⟨s₀, l0, ?_, adj0, ?_⟩
      · intro a ha
        exact List.mem_cons_of_mem _ (sub0 a ha)
      · intro j' hj'' e₁ e₂
        rcases List.mem_cons.mp hj'' with e' | h'
        · exfalso
          rw [e'] at e₁ e₂
          have := (older j hj' (by rw [← e₁, hcl])).2
          omega
        · exact own0 j' h' e₁ e₂

/-- A created item can be integrated by every replica that is ready for it. -/
theorem Inv.canIntegrate {n : Net} (h : Inv n) (r : Nat) {i : Item} (hi : i ∈ n.ops)
    (hr : Ready (n.st r).items i) : CanIntegrate (n.st r).items i := by
  obtain ⟨s₀, l0, sub0, adj0, own0⟩ := h.wit i hi
  apply canIntegrate_of_witness (h.legal r) l0 _ adj0 hr
  · intro y hy e
    exact own0 y (h.sub r y hy) e (hr.clock y hy e)
  · intro a ha b hb e
    exact h.uniq a (sub0 a ha) b (h.sub r b hb) e

theorem Inv.deliver {n : Net} (h : Inv n) (r : Nat) {i : Item} (hi : i ∈ n.ops)
    (hr : Ready (n.st r).items i) : Inv (n.deliver r i) := by
  have hs := h.legal r
  have hci := h.canIntegrate r hi hr
  have F1 : (n.deliver r i).ops = n.ops := rfl
  have F2 : ((n.deliver r i).st r).items = integrate (n.st r).items i := by
    show (n.set r _ r).items = _
    rw [Net.set_same]
    rfl
  have F3 : ∀ r', r' ≠ r → (n.deliver r i).st r' = n.st r' := fun r' e => Net.set_ne n _ e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r'
    by_cases e : r' = r
    · rw [e, F2]
      exact legal_integrate hs hci
    · rw [F3 r' e]
      exact h.legal r'
  · intro r' a ha
    rw [F1]
    by_cases e : r' = r
    · rw [e, F2] at ha
      rcases mem_integrate.mp ha with e' | h'
      · rw [e']
        exact hi
      · exact h.sub r a h'
    · rw [F3 r' e] at ha
      exact h.sub r' a ha
  · rw [F1]
    exact h.uniq
  · intro a ha
    rw [F1] at ha
    by_cases e : a.id.client = r
    · have hm := h.own a ha
      rw [e] at hm
      rw [e, F2]
      exact mem_integrate.mpr (Or.inr hm)
    · rw [F3 _ e]
      exact h.own a ha
  · rw [F1]
    exact h.wit

/-- A step that leaves the sequences and the created items alone. -/
theorem Inv.of_items {n n' : Net} (h : Inv n) (hst : ∀ r, (n'.st r).items = (n.st r).items)
    (hops : n'.ops = n.ops) : Inv n' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    rw [hst]
    exact h.legal r
  · intro r a ha
    rw [hst] at ha
    rw [hops]
    exact h.sub r a ha
  · rw [hops]
    exact h.uniq
  · intro a ha
    rw [hops] at ha
    rw [hst]
    exact h.own a ha
  · rw [hops]
    exact h.wit

theorem Net.delete_items (n : Net) (r : Nat) (x : Id) (r' : Nat) :
    (n.set r ((n.st r).delete x) r').items = (n.st r').items := by
  by_cases e : r' = r
  · rw [e, Net.set_same]
    rfl
  · rw [Net.set_ne n _ e]

theorem Inv.step {n n' : Net} (h : Inv n) (hstep : Step n n') : Inv n' := by
  cases hstep with
  | gen r i hid hadj => exact h.gen r hid hadj
  | deliver r i hi hr => exact h.deliver r hi hr
  | delete r x => exact h.of_items (n.delete_items r x) rfl
  | deliverDelete r x hx => exact h.of_items (n.delete_items r x) rfl

/-- Inserting at gap `k` of the own sequence is a step of the network. -/
theorem Step.genAt {n : Net} (h : Inv n) (r : Nat) {k : Nat} (hk : k ≤ (n.st r).items.length) :
    Step n (n.gen r (mkItem (n.st r).items r k)) :=
  Step.gen n r _ rfl (mkItem_adj (h.legal r) r hk)

theorem Reachable.inv {n : Net} (h : Reachable n) : Inv n := by
  induction h with
  | init => exact inv_init
  | step _ hstep ih => exact ih.step hstep

/-- **Strong eventual consistency (sequence).** Two replicas that integrated the
same items hold the same sequence, whatever the delivery orders were. -/
theorem sec {n : Net} (h : Reachable n) (r₁ r₂ : Nat)
    (hm : ∀ a, a ∈ (n.st r₁).items ↔ a ∈ (n.st r₂).items) :
    (n.st r₁).items = (n.st r₂).items := by
  have hi := h.inv
  apply legal_unique (hi.legal r₁) (hi.legal r₂) _ hm
  intro a ha b hb e
  exact hi.uniq a (hi.sub r₁ a ha) b (hi.sub r₂ b hb) e

/-- The same, from the integrated ids alone. -/
theorem sec_ids {n : Net} (h : Reachable n) (r₁ r₂ : Nat)
    (hm : ∀ x, x ∈ (n.st r₁).items.map Item.id ↔ x ∈ (n.st r₂).items.map Item.id) :
    (n.st r₁).items = (n.st r₂).items := by
  have hi := h.inv
  apply sec h
  have key : ∀ r r', (∀ x, x ∈ (n.st r).items.map Item.id → x ∈ (n.st r').items.map Item.id) →
      ∀ a, a ∈ (n.st r).items → a ∈ (n.st r').items := by
    intro r r' hsub a ha
    obtain ⟨b, hb, e⟩ := List.mem_map.mp (hsub a.id (List.mem_map.mpr ⟨a, ha, rfl⟩))
    have hab : b = a := hi.uniq b (hi.sub r' b hb) a (hi.sub r a ha) e
    rw [← hab]
    exact hb
  intro a
  exact ⟨key r₁ r₂ (fun x => (hm x).mp) a, key r₂ r₁ (fun x => (hm x).mpr) a⟩

/-- **Strong eventual consistency (document).** Replicas that integrated the
same items and applied the same deletions are in the same state, and show the
same content. -/
theorem sec_doc {n : Net} (h : Reachable n) (r₁ r₂ : Nat)
    (hm : ∀ a, a ∈ (n.st r₁).items ↔ a ∈ (n.st r₂).items)
    (hd : ∀ x, x ∈ (n.st r₁).deleted ↔ x ∈ (n.st r₂).deleted) : n.st r₁ = n.st r₂ := by
  have e₁ := sec h r₁ r₂ hm
  have e₂ : (n.st r₁).deleted = (n.st r₂).deleted := DeleteSet.ext hd
  cases h₁ : n.st r₁ with
  | mk i₁ d₁ =>
    cases h₂ : n.st r₂ with
    | mk i₂ d₂ =>
      rw [h₁, h₂] at e₁ e₂
      simp only at e₁ e₂
      rw [e₁, e₂]

theorem sec_visible {n : Net} (h : Reachable n) (r₁ r₂ : Nat)
    (hm : ∀ a, a ∈ (n.st r₁).items ↔ a ∈ (n.st r₂).items)
    (hd : ∀ x, x ∈ (n.st r₁).deleted ↔ x ∈ (n.st r₂).deleted) :
    (n.st r₁).visible = (n.st r₂).visible := by
  rw [sec_doc h r₁ r₂ hm hd]

end YoctoSpec
