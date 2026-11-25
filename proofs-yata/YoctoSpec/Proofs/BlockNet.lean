/-
Block-level strong eventual consistency.

`BRun bn n` pairs the block sequences `bn` of the replicas with a run `n` of
the unit-level network: every struct a replica integrates is a run of clocks
that the network creates at that replica or delivers to it (`UnitRun`), and
replicas may delete clock ranges, split, merge and collect at any time.
`brun_sound` shows that every block sequence stands for the unit-level state
of its replica, so the unit-level theorem applies: replicas with the same
clocks and the same deletions hold the same document (`bsec`).
-/
import YoctoSpec.Proofs.Pending

namespace YoctoSpec

/-! ## The delete set of a block sequence -/

theorem mem_deletedSet {bs : List Block} {x : Id} :
    x ∈ deletedSet bs ↔ ∃ b, b ∈ bs ∧ b.deleted = true ∧ x ∈ b.units.map Item.id := by
  unfold deletedSet
  rw [DeleteSet.mem_foldl_insert]
  constructor
  · rintro (h | h)
    · exact absurd h (DeleteSet.not_mem_empty x)
    · obtain ⟨b, hb, hx⟩ := List.mem_flatMap.mp h
      unfold Block.deletedIds at hx
      by_cases hd : b.deleted = true
      · rw [ite_eq_left hd] at hx
        exact ⟨b, hb, hd, hx⟩
      · rw [ite_eq_right hd] at hx
        cases hx
  · rintro ⟨b, hb, hd, hx⟩
    right
    apply List.mem_flatMap.mpr
    refine ⟨b, hb, ?_⟩
    unfold Block.deletedIds
    rw [ite_eq_left hd]
    exact hx

theorem deletedSet_congr {p q : List Block}
    (h : p.flatMap Block.deletedIds = q.flatMap Block.deletedIds) :
    deletedSet p = deletedSet q := by
  unfold deletedSet
  rw [h]

theorem toDoc_ext {p : List Block} {d : Doc} (h₁ : flatten p = d.items)
    (h₂ : deletedSet p = d.deleted) : toDoc p = d :=
  Doc.ext' h₁ h₂

/-! ## Deleting a clock range -/

theorem units_markBlock (c lo hi : Nat) (b : Block) : (markBlock c lo hi b).units = b.units := by
  unfold markBlock
  by_cases h : b.id.client = c ∧ lo ≤ b.id.clock ∧ b.id.clock + b.len ≤ hi
  · rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h]

theorem flatten_markRange (c lo hi : Nat) (bs : List Block) :
    flatten (markRange c lo hi bs) = flatten bs := by
  unfold markRange
  induction bs with
  | nil => rfl
  | cons b t ih => rw [List.map_cons, flatten_cons, flatten_cons, units_markBlock, ih]

theorem flatten_deleteRange (bs : List Block) (c lo hi : Nat) :
    flatten (deleteRange bs c lo hi) = flatten bs := by
  unfold deleteRange
  rw [flatten_markRange, flatten_split, flatten_split]

theorem blockWF_markRange {bs : List Block} (hw : BlockWF bs) (c lo hi : Nat) :
    BlockWF (markRange c lo hi bs) := by
  intro b hb
  unfold markRange at hb
  obtain ⟨a, ha, e⟩ := List.mem_map.mp hb
  rw [← e, len_markBlock]
  exact hw a ha

theorem blockWF_deleteRange {bs : List Block} (hw : BlockWF bs) (c lo hi : Nat) :
    BlockWF (deleteRange bs c lo hi) :=
  blockWF_markRange (blockWF_split (blockWF_split hw _) _) c lo hi

/-- **`delete_range` deletes exactly the integrated clocks of the range.** -/
theorem mem_deletedSet_deleteRange (bs : List Block) (c lo hi : Nat) (x : Id) :
    x ∈ deletedSet (deleteRange bs c lo hi) ↔
      x ∈ deletedSet bs ∨
        (x ∈ (flatten bs).map Item.id ∧ x.client = c ∧ lo ≤ x.clock ∧ x.clock < hi) := by
  have hsame : SameUnits (split (split bs ⟨c, lo⟩) ⟨c, hi⟩) bs :=
    (sameUnits_split _ _).trans (sameUnits_split _ _)
  have hds : deletedSet (split (split bs ⟨c, lo⟩) ⟨c, hi⟩) = deletedSet bs :=
    deletedSet_congr hsame.deleted
  have hlo : Aligned ⟨c, lo⟩ (split (split bs ⟨c, lo⟩) ⟨c, hi⟩) :=
    aligned_split_of_aligned (aligned_split bs _) _
  have hhi : Aligned ⟨c, hi⟩ (split (split bs ⟨c, lo⟩) ⟨c, hi⟩) := aligned_split _ _
  unfold deleteRange
  generalize split (split bs ⟨c, lo⟩) ⟨c, hi⟩ = bs₂ at hsame hds hlo hhi ⊢
  rw [← hds, ← hsame.units, mem_deletedSet, mem_deletedSet]
  constructor
  · rintro ⟨b', hb', hd', hx'⟩
    unfold markRange at hb'
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hb'
    rw [← e, units_markBlock] at hx'
    by_cases hcond : b.id.client = c ∧ lo ≤ b.id.clock ∧ b.id.clock + b.len ≤ hi
    · right
      have hx := mem_units_ids.mp hx'
      refine ⟨ids_subset_flatten hb hx', ?_, ?_, ?_⟩
      · rw [hx.1]
        exact hcond.1
      · omega
      · omega
    · left
      rw [← e] at hd'
      unfold markBlock at hd'
      rw [ite_eq_right hcond] at hd'
      exact ⟨b, hb, hd', hx'⟩
  · rintro (⟨b, hb, hd, hx⟩ | ⟨hpres, hxc, hxlo, hxhi⟩)
    · refine ⟨markBlock c lo hi b, ?_, ?_, ?_⟩
      · unfold markRange
        exact List.mem_map.mpr ⟨b, hb, rfl⟩
      · unfold markBlock
        by_cases hcond : b.id.client = c ∧ lo ≤ b.id.clock ∧ b.id.clock + b.len ≤ hi
        · rw [ite_eq_left hcond]
        · rw [ite_eq_right hcond]
          exact hd
      · rw [units_markBlock]
        exact hx
    · obtain ⟨u, hu, eu⟩ := List.mem_map.mp hpres
      obtain ⟨b, hb, hub⟩ := mem_flatten.mp hu
      have hxb : x ∈ b.units.map Item.id := List.mem_map.mpr ⟨u, hub, eu⟩
      have hx := mem_units_ids.mp hxb
      have h₁ := hlo b hb
      have h₂ := hhi b hb
      have h₁' : ¬ (c = b.id.client ∧ b.id.clock < lo ∧ lo < b.id.clock + b.len) := h₁
      have h₂' : ¬ (c = b.id.client ∧ b.id.clock < hi ∧ hi < b.id.clock + b.len) := h₂
      have hbc : b.id.client = c := by rw [← hx.1, hxc]
      have hcond : b.id.client = c ∧ lo ≤ b.id.clock ∧ b.id.clock + b.len ≤ hi := by
        refine ⟨hbc, ?_, ?_⟩
        · omega
        · omega
      refine ⟨markBlock c lo hi b, ?_, ?_, ?_⟩
      · unfold markRange
        exact List.mem_map.mpr ⟨b, hb, rfl⟩
      · unfold markBlock
        rw [ite_eq_left hcond]
      · rw [units_markBlock]
        exact hxb

/-- The integrated clocks of client `c` in `[lo, hi)`. -/
def presentRange (bs : List Block) (c lo hi : Nat) : List Id :=
  ((flatten bs).map Item.id).filter (fun x => decide (x.client = c ∧ lo ≤ x.clock ∧ x.clock < hi))

theorem mem_presentRange {bs : List Block} {c lo hi : Nat} {x : Id} :
    x ∈ presentRange bs c lo hi ↔
      x ∈ (flatten bs).map Item.id ∧ x.client = c ∧ lo ≤ x.clock ∧ x.clock < hi := by
  unfold presentRange
  rw [List.mem_filter, decide_eq_true_iff]

/-! ## Well-formedness of the other operations -/

theorem blockWF_cons {a : Block} {t : List Block} :
    BlockWF (a :: t) ↔ 0 < a.len ∧ BlockWF t := by
  constructor
  · intro h
    exact ⟨h a (List.mem_cons_self ..), fun c hc => h c (List.mem_cons_of_mem _ hc)⟩
  · rintro ⟨h₁, h₂⟩ c hc
    rcases List.mem_cons.mp hc with e | h
    · rw [e]
      exact h₁
    · exact h₂ c h

theorem len_mergeBlocks {a b : Block} (h : canMerge a b = true) :
    (mergeBlocks a b).len = a.len + b.len :=
  Content.len_append (canMerge_spec h).2.2.2.2.2.2

theorem blockWF_mergeAt : ∀ (n : Nat) (bs : List Block), BlockWF bs → BlockWF (mergeAt n bs) := by
  intro n
  induction n with
  | zero =>
    intro bs hw
    match bs with
    | [] => exact hw
    | [a] => exact hw
    | a :: b :: t =>
      rw [mergeAt]
      by_cases h : canMerge a b = true
      · rw [ite_eq_left h]
        have h₁ := blockWF_cons.mp hw
        have h₂ := blockWF_cons.mp h₁.2
        refine blockWF_cons.mpr ⟨?_, h₂.2⟩
        rw [len_mergeBlocks h]
        omega
      · rw [ite_eq_right h]
        exact hw
  | succ n ih =>
    intro bs hw
    match bs with
    | [] => exact hw
    | [a] => exact hw
    | a :: b :: t =>
      rw [mergeAt]
      have h₁ := blockWF_cons.mp hw
      exact blockWF_cons.mpr ⟨h₁.1, ih (b :: t) h₁.2⟩

theorem blockWF_mergeAll : ∀ (bs : List Block), BlockWF bs → BlockWF (mergeAll bs) := by
  intro bs
  induction bs with
  | nil =>
    intro hw
    exact hw
  | cons a t ih =>
    intro hw
    have h₁ := blockWF_cons.mp hw
    have iht := ih h₁.2
    rw [mergeAll]
    cases hm : mergeAll t with
    | nil => exact blockWF_cons.mpr ⟨h₁.1, fun c hc => by cases hc⟩
    | cons b t' =>
      rw [hm] at iht
      have h₂ := blockWF_cons.mp iht
      simp only
      by_cases h : canMerge a b = true
      · rw [ite_eq_left h]
        refine blockWF_cons.mpr ⟨?_, h₂.2⟩
        rw [len_mergeBlocks h]
        omega
      · rw [ite_eq_right h]
        exact blockWF_cons.mpr ⟨h₁.1, iht⟩

theorem len_gcBlock (b : Block) : (gcBlock b).len = b.len := by
  unfold gcBlock
  by_cases h : b.deleted = true
  · rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h]

theorem blockWF_gcContent {bs : List Block} (hw : BlockWF bs) : BlockWF (gcContent bs) := by
  intro b hb
  unfold gcContent at hb
  obtain ⟨a, ha, e⟩ := List.mem_map.mp hb
  rw [← e, len_gcBlock]
  exact hw a ha

theorem mem_insertAfterBId {x : Id} {n c : Block} :
    ∀ {l : List Block}, c ∈ insertAfterBId x n l → c = n ∨ c ∈ l := by
  intro l
  induction l with
  | nil =>
    intro h
    rw [insertAfterBId] at h
    rcases List.mem_cons.mp h with e | h'
    · exact Or.inl e
    · cases h'
  | cons b t ih =>
    intro h
    rw [insertAfterBId] at h
    by_cases hb : b.id = x
    · rw [ite_eq_left hb] at h
      rcases List.mem_cons.mp h with e | h'
      · exact Or.inr (by rw [e]; exact List.mem_cons_self ..)
      · rcases List.mem_cons.mp h' with e | h''
        · exact Or.inl e
        · exact Or.inr (List.mem_cons_of_mem _ h'')
    · rw [ite_eq_right hb] at h
      rcases List.mem_cons.mp h with e | h'
      · exact Or.inr (by rw [e]; exact List.mem_cons_self ..)
      · rcases ih h' with e | h''
        · exact Or.inl e
        · exact Or.inr (List.mem_cons_of_mem _ h'')

theorem blockWF_integrateBlock {bs : List Block} {b : Block} (hw : BlockWF bs) (hb : 0 < b.len) :
    BlockWF (integrateBlock bs b) := by
  have hw₂ := blockWF_splitRight (blockWF_splitLeft hw b.left) b.right
  intro c hc
  unfold integrateBlock at hc
  cases hres : scanB (splitRight b.right (splitLeft b.left bs)) b with
  | none =>
    rw [hres] at hc
    rcases List.mem_cons.mp hc with e | h
    · rw [e]
      exact hb
    · exact hw₂ c h
  | some x =>
    rw [hres] at hc
    rcases mem_insertAfterBId hc with e | h
    · rw [e]
      exact hb
    · exact hw₂ c h

theorem flatMap_insertAfterBId {β : Type} (f : Block → List β) {n : Block} (hn : f n = [])
    (x : Id) : ∀ (l : List Block), (insertAfterBId x n l).flatMap f = l.flatMap f := by
  intro l
  induction l with
  | nil =>
    rw [insertAfterBId]
    simp only [List.flatMap_cons, hn, List.nil_append]
  | cons b t ih =>
    rw [insertAfterBId]
    by_cases hb : b.id = x
    · rw [ite_eq_left hb]
      simp only [List.flatMap_cons, hn, List.nil_append]
    · rw [ite_eq_right hb]
      simp only [List.flatMap_cons, ih]

theorem sameUnits_splitLeft (o : Option Id) (bs : List Block) : SameUnits (splitLeft o bs) bs := by
  cases o with
  | none => exact SameUnits.refl _
  | some l => exact sameUnits_split bs _

theorem sameUnits_splitRight (o : Option Id) (bs : List Block) :
    SameUnits (splitRight o bs) bs := by
  cases o with
  | none => exact SameUnits.refl _
  | some r => exact sameUnits_split bs _

/-- Integrating a block that is not deleted leaves the delete set alone. -/
theorem deletedSet_integrateBlock {bs : List Block} {b : Block} (hb : b.deleted = false) :
    deletedSet (integrateBlock bs b) = deletedSet bs := by
  apply deletedSet_congr
  have hn : b.deletedIds = [] := by
    simp [Block.deletedIds, hb]
  have h₂ := ((sameUnits_splitRight b.right _).trans (sameUnits_splitLeft b.left bs)).deleted
  unfold integrateBlock
  cases scanB (splitRight b.right (splitLeft b.left bs)) b with
  | none =>
    show (b :: splitRight b.right (splitLeft b.left bs)).flatMap Block.deletedIds = _
    rw [List.flatMap_cons, hn, List.nil_append, h₂]
  | some x =>
    show (insertAfterBId x b (splitRight b.right (splitLeft b.left bs))).flatMap
      Block.deletedIds = _
    rw [flatMap_insertAfterBId _ hn, h₂]

/-! ## The unit-level run of a struct -/

/-- The network creates at `r`, or delivers to `r`, the items `us` one after
the other. -/
inductive UnitRun (r : Nat) : Net → List Item → Net → Prop
  | nil (n : Net) : UnitRun r n [] n
  | gen {n n' : Net} {u : Item} {us : List Item}
      (hid : u.id = ⟨r, nextClock (n.st r).items r⟩) (hadj : Adj (n.st r).items u)
      (h : UnitRun r (n.gen r u) us n') : UnitRun r n (u :: us) n'
  | deliver {n n' : Net} {u : Item} {us : List Item} (hu : u ∈ n.ops)
      (hr : Ready (n.st r).items u) (h : UnitRun r (n.deliver r u) us n') :
      UnitRun r n (u :: us) n'

theorem UnitRun.reachable {r : Nat} {n n' : Net} {us : List Item} (h : UnitRun r n us n') :
    Reachable n → Reachable n' := by
  induction h with
  | nil n => exact fun hn => hn
  | gen hid hadj _ ih => exact fun hn => ih (Reachable.step hn (Step.gen _ r _ hid hadj))
  | deliver hu hr _ ih => exact fun hn => ih (Reachable.step hn (Step.deliver _ r _ hu hr))

theorem UnitRun.st {r : Nat} {n n' : Net} {us : List Item} (h : UnitRun r n us n') :
    (n'.st r).items = us.foldl integrate (n.st r).items ∧
      (n'.st r).deleted = (n.st r).deleted ∧ ∀ r', r' ≠ r → n'.st r' = n.st r' := by
  induction h with
  | nil n => exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | @gen n n' u us hid hadj _ ih =>
    have e : (n.gen r u).st r = (n.st r).integrate u := Net.set_same n r _
    obtain ⟨h₁, h₂, h₃⟩ := ih
    rw [e] at h₁ h₂
    refine ⟨h₁, h₂, ?_⟩
    intro r' hr'
    rw [h₃ r' hr']
    exact Net.set_ne n _ hr'
  | @deliver n n' u us hu hr _ ih =>
    have e : (n.deliver r u).st r = (n.st r).integrate u := Net.set_same n r _
    obtain ⟨h₁, h₂, h₃⟩ := ih
    rw [e] at h₁ h₂
    refine ⟨h₁, h₂, ?_⟩
    intro r' hr'
    rw [h₃ r' hr']
    exact Net.set_ne n _ hr'

/-- The first item of a run can be integrated, and its replica holds no later
clock of its client. -/
theorem UnitRun.head {r : Nat} {n n' : Net} {u : Item} {us : List Item}
    (h : UnitRun r n (u :: us) n') (hn : Reachable n) :
    CanIntegrate (n.st r).items u ∧
      ∀ a, a ∈ (n.st r).items → a.id.client = u.id.client → a.id.clock < u.id.clock := by
  cases h with
  | gen hid hadj _ =>
    refine ⟨canIntegrate_gen (hn.inv.legal r) hid hadj, ?_⟩
    intro a ha e
    have hc : a.id.client = r := e.trans (congrArg Id.client hid)
    have hlt := lt_nextClock ha hc
    have hk : u.id.clock = nextClock (n.st r).items r := congrArg Id.clock hid
    omega
  | deliver hu hr _ => exact ⟨hn.inv.canIntegrate r hu hr, hr.clock⟩

/-! ## Deletions at the unit level -/

/-- Replica `r` deletes the ids one after the other. -/
def Net.deletes (n : Net) (r : Nat) (ids : List Id) : Net :=
  ids.foldl (fun n x => n.delete r x) n

theorem Net.deletes_spec (r : Nat) : ∀ (ids : List Id) (n : Net), Reachable n →
    Reachable (n.deletes r ids) ∧ ((n.deletes r ids).st r).items = (n.st r).items ∧
      ((n.deletes r ids).st r).deleted = ids.foldl DeleteSet.insert (n.st r).deleted ∧
      ∀ r', r' ≠ r → (n.deletes r ids).st r' = n.st r' := by
  intro ids
  induction ids with
  | nil =>
    intro n hn
    exact ⟨hn, rfl, rfl, fun _ _ => rfl⟩
  | cons x t ih =>
    intro n hn
    have e : (n.delete r x).st r = (n.st r).delete x := Net.set_same n r _
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih (n.delete r x) (Reachable.step hn (Step.delete n r x))
    rw [e] at h₂ h₃
    refine ⟨h₁, h₂, h₃, ?_⟩
    intro r' hr'
    have h := h₄ r' hr'
    have e' : (n.delete r x).st r' = n.st r' := Net.set_ne n _ hr'
    rw [e'] at h
    exact h

/-! ## Block-level runs -/

def upd (bn : Nat → List Block) (r : Nat) (bs : List Block) : Nat → List Block :=
  fun r' => if r' = r then bs else bn r'

theorem upd_same (bn : Nat → List Block) (r : Nat) (bs : List Block) : upd bn r bs r = bs := by
  unfold upd
  exact ite_eq_left rfl

theorem upd_ne (bn : Nat → List Block) {r r' : Nat} (bs : List Block) (h : r' ≠ r) :
    upd bn r bs r' = bn r' := by
  unfold upd
  exact ite_eq_right h

/-- Block sequences of the replicas, next to the unit-level run they
implement. -/
inductive BRun : (Nat → List Block) → Net → Prop
  | init : BRun (fun _ => []) Net.init
  /-- replica `r` integrates the struct `b`: every clock of `b` is created at
  `r` or delivered to `r` at the unit level, in clock order -/
  | integrate {bn : Nat → List Block} {n n' : Net} (r : Nat) (b : Block) :
      BRun bn n → 0 < b.len → b.deleted = false → UnitRun r n b.units n' →
      BRun (upd bn r (integrateBlock (bn r) b)) n'
  /-- replica `r` deletes the clocks of client `c` in `[lo, hi)` it holds -/
  | delete {bn : Nat → List Block} {n : Net} (r c lo hi : Nat) :
      BRun bn n →
      BRun (upd bn r (deleteRange (bn r) c lo hi)) (n.deletes r (presentRange (bn r) c lo hi))
  | split {bn : Nat → List Block} {n : Net} (r : Nat) (x : Id) :
      BRun bn n → BRun (upd bn r (split (bn r) x)) n
  | mergeAt {bn : Nat → List Block} {n : Net} (r idx : Nat) :
      BRun bn n → BRun (upd bn r (mergeAt idx (bn r))) n
  | mergeAll {bn : Nat → List Block} {n : Net} (r : Nat) :
      BRun bn n → BRun (upd bn r (mergeAll (bn r))) n
  | gcContent {bn : Nat → List Block} {n : Net} (r : Nat) :
      BRun bn n → BRun (upd bn r (gcContent (bn r))) n

/-- Every block sequence stands for the unit-level state of its replica. -/
structure BInv (bn : Nat → List Block) (n : Net) : Prop where
  reach : Reachable n
  doc : ∀ r, toDoc (bn r) = n.st r
  wf : ∀ r, BlockWF (bn r)

theorem BInv.same {bn : Nat → List Block} {n : Net} (h : BInv bn n) (r : Nat)
    {bs' : List Block} (hdoc : toDoc bs' = toDoc (bn r)) (hwf : BlockWF bs') :
    BInv (upd bn r bs') n := by
  refine ⟨h.reach, ?_, ?_⟩
  · intro r'
    by_cases e : r' = r
    · rw [e, upd_same, hdoc]
      exact h.doc r
    · rw [upd_ne _ _ e]
      exact h.doc r'
  · intro r'
    by_cases e : r' = r
    · rw [e, upd_same]
      exact hwf
    · rw [upd_ne _ _ e]
      exact h.wf r'

/-- A replica that integrates a struct the network creates at it or delivers
to it keeps standing for its unit-level state. -/
theorem BInv.integrate {bn : Nat → List Block} {n n' : Net} (ih : BInv bn n) (r : Nat)
    (b : Block) (hlen : 0 < b.len) (hdel : b.deleted = false) (hrun : UnitRun r n b.units n') :
    BInv (upd bn r (integrateBlock (bn r) b)) n' := by
  have hitems : flatten (bn r) = (n.st r).items := congrArg Doc.items (ih.doc r)
  have hdels : deletedSet (bn r) = (n.st r).deleted := congrArg Doc.deleted (ih.doc r)
  have hrun' := hrun
  rw [units_eq_cons' hlen] at hrun'
  obtain ⟨hci, hclk⟩ := hrun'.head ih.reach
  rw [← hitems] at hci hclk
  have hlegal : Legal (flatten (bn r)) := by
    rw [hitems]
    exact ih.reach.inv.legal r
  have hfresh : ∀ a, a ∈ flatten (bn r) → ∀ j, b.id.clock ≤ j →
      a.id ≠ ⟨b.id.client, j⟩ := by
    intro a ha j hj e
    have h₁ : a.id.client = b.id.client := by rw [e]
    have h₂ : a.id.clock = j := by rw [e]
    have h₃ : a.id.clock < b.id.clock := hclk a ha h₁
    omega
  have hfl := flatten_integrateBlock (ih.wf r) hlegal hlen hci hfresh
  obtain ⟨st₁, st₂, st₃⟩ := hrun.st
  refine ⟨hrun.reachable ih.reach, ?_, ?_⟩
  · intro r'
    by_cases e : r' = r
    · rw [e, upd_same]
      apply toDoc_ext
      · rw [hfl, hitems, st₁]
      · rw [deletedSet_integrateBlock hdel, hdels, st₂]
    · rw [upd_ne _ _ e, st₃ r' e]
      exact ih.doc r'
  · intro r'
    by_cases e : r' = r
    · rw [e, upd_same]
      exact blockWF_integrateBlock (ih.wf r) hlen
    · rw [upd_ne _ _ e]
      exact ih.wf r'

/-- A replica whose block sequence keeps its clocks and gains the deletions
`ids` stands for its state in the network where it deleted them. -/
theorem BInv.deletes {bn : Nat → List Block} {n : Net} (ih : BInv bn n) (r : Nat)
    {bs' : List Block} (ids : List Id) (hfl : flatten bs' = flatten (bn r))
    (hdel : ∀ x, x ∈ deletedSet bs' ↔ x ∈ deletedSet (bn r) ∨ x ∈ ids) (hwf : BlockWF bs') :
    BInv (upd bn r bs') (n.deletes r ids) := by
  have hitems : flatten (bn r) = (n.st r).items := congrArg Doc.items (ih.doc r)
  have hdels : deletedSet (bn r) = (n.st r).deleted := congrArg Doc.deleted (ih.doc r)
  obtain ⟨d₁, d₂, d₃, d₄⟩ := Net.deletes_spec r ids n ih.reach
  refine ⟨d₁, ?_, ?_⟩
  · intro r'
    by_cases e : r' = r
    · rw [e, upd_same]
      apply toDoc_ext
      · rw [hfl, hitems, d₂]
      · apply DeleteSet.ext
        intro x
        rw [d₃, DeleteSet.mem_foldl_insert, hdel x, hdels]
    · rw [upd_ne _ _ e, d₄ r' e]
      exact ih.doc r'
  · intro r'
    by_cases e : r' = r
    · rw [e, upd_same]
      exact hwf
    · rw [upd_ne _ _ e]
      exact ih.wf r'

/-- **Refinement.** In a block-level run every replica holds a block sequence
that stands for its state in a reachable unit-level network. -/
theorem brun_sound {bn : Nat → List Block} {n : Net} (h : BRun bn n) : BInv bn n := by
  induction h with
  | init =>
    exact ⟨Reachable.init, fun _ => rfl, fun _ c hc => by cases hc⟩
  | @integrate bn n n' r b _ hlen hdel hrun ih => exact ih.integrate r b hlen hdel hrun
  | @delete bn n r c lo hi _ ih =>
    have hitems : flatten (bn r) = (n.st r).items := congrArg Doc.items (ih.doc r)
    have hdels : deletedSet (bn r) = (n.st r).deleted := congrArg Doc.deleted (ih.doc r)
    obtain ⟨d₁, d₂, d₃, d₄⟩ := Net.deletes_spec r (presentRange (bn r) c lo hi) n ih.reach
    refine ⟨d₁, ?_, ?_⟩
    · intro r'
      by_cases e : r' = r
      · rw [e, upd_same]
        apply toDoc_ext
        · rw [flatten_deleteRange, hitems, d₂]
        · apply DeleteSet.ext
          intro x
          rw [d₃, DeleteSet.mem_foldl_insert, mem_deletedSet_deleteRange, hdels,
            mem_presentRange]
      · rw [upd_ne _ _ e, d₄ r' e]
        exact ih.doc r'
    · intro r'
      by_cases e : r' = r
      · rw [e, upd_same]
        exact blockWF_deleteRange (ih.wf r) c lo hi
      · rw [upd_ne _ _ e]
        exact ih.wf r'
  | @split bn n r x _ ih => exact ih.same r (toDoc_split _ x) (blockWF_split (ih.wf r) x)
  | @mergeAt bn n r idx _ ih =>
    exact ih.same r (toDoc_mergeAt idx _) (blockWF_mergeAt idx _ (ih.wf r))
  | @mergeAll bn n r _ ih => exact ih.same r (toDoc_mergeAll _) (blockWF_mergeAll _ (ih.wf r))
  | @gcContent bn n r _ ih => exact ih.same r (toDoc_gcContent _) (blockWF_gcContent (ih.wf r))

/-- Replicas that stand for the states of a reachable network, hold the same
clocks and the same deletions, stand for the same document. -/
theorem BInv.sec {bn : Nat → List Block} {n : Net} (hinv : BInv bn n) (r₁ r₂ : Nat)
    (hu : ∀ u, u ∈ flatten (bn r₁) ↔ u ∈ flatten (bn r₂))
    (hd : ∀ x, x ∈ deletedSet (bn r₁) ↔ x ∈ deletedSet (bn r₂)) :
    toDoc (bn r₁) = toDoc (bn r₂) := by
  rw [hinv.doc r₁, hinv.doc r₂]
  apply sec_doc hinv.reach r₁ r₂
  · intro a
    have e₁ : (n.st r₁).items = flatten (bn r₁) := (congrArg Doc.items (hinv.doc r₁)).symm
    have e₂ : (n.st r₂).items = flatten (bn r₂) := (congrArg Doc.items (hinv.doc r₂)).symm
    rw [e₁, e₂]
    exact hu a
  · intro x
    have e₁ : (n.st r₁).deleted = deletedSet (bn r₁) := (congrArg Doc.deleted (hinv.doc r₁)).symm
    have e₂ : (n.st r₂).deleted = deletedSet (bn r₂) := (congrArg Doc.deleted (hinv.doc r₂)).symm
    rw [e₁, e₂]
    exact hd x

/-- The same, comparing the clocks the two replicas hold by id only. -/
theorem BInv.sec_ids {bn : Nat → List Block} {n : Net} (hinv : BInv bn n) (r₁ r₂ : Nat)
    (hu : ∀ x, x ∈ (flatten (bn r₁)).map Item.id ↔ x ∈ (flatten (bn r₂)).map Item.id)
    (hd : ∀ x, x ∈ deletedSet (bn r₁) ↔ x ∈ deletedSet (bn r₂)) :
    toDoc (bn r₁) = toDoc (bn r₂) := by
  have e₁ : flatten (bn r₁) = (n.st r₁).items := congrArg Doc.items (hinv.doc r₁)
  have e₂ : flatten (bn r₂) = (n.st r₂).items := congrArg Doc.items (hinv.doc r₂)
  have hitems : flatten (bn r₁) = flatten (bn r₂) := by
    rw [e₁, e₂]
    apply YoctoSpec.sec_ids hinv.reach
    intro x
    rw [← e₁, ← e₂]
    exact hu x
  exact Doc.ext' hitems (DeleteSet.ext hd)

/-- **Block-level strong eventual consistency.** After any block-level run
(structs integrated in any causal order, deletions, splits, merges and content
GC interleaved at will), two replicas that hold the same clocks and the same
deletions stand for the same document: the same sequence of clocks with the
same origins, and the same delete set. -/
theorem bsec {bn : Nat → List Block} {n : Net} (h : BRun bn n) (r₁ r₂ : Nat)
    (hu : ∀ u, u ∈ flatten (bn r₁) ↔ u ∈ flatten (bn r₂))
    (hd : ∀ x, x ∈ deletedSet (bn r₁) ↔ x ∈ deletedSet (bn r₂)) :
    toDoc (bn r₁) = toDoc (bn r₂) :=
  (brun_sound h).sec r₁ r₂ hu hd

/-- The same, comparing the clocks the two replicas hold by id only. -/
theorem bsec_ids {bn : Nat → List Block} {n : Net} (h : BRun bn n) (r₁ r₂ : Nat)
    (hu : ∀ x, x ∈ (flatten (bn r₁)).map Item.id ↔ x ∈ (flatten (bn r₂)).map Item.id)
    (hd : ∀ x, x ∈ deletedSet (bn r₁) ↔ x ∈ deletedSet (bn r₂)) :
    toDoc (bn r₁) = toDoc (bn r₂) :=
  (brun_sound h).sec_ids r₁ r₂ hu hd

/-- The visible clocks of the two replicas are the same sequence. -/
theorem bsec_visible_ids {bn : Nat → List Block} {n : Net} (h : BRun bn n) (r₁ r₂ : Nat)
    (hu : ∀ u, u ∈ flatten (bn r₁) ↔ u ∈ flatten (bn r₂))
    (hd : ∀ x, x ∈ deletedSet (bn r₁) ↔ x ∈ deletedSet (bn r₂)) :
    (toDoc (bn r₁)).visible = (toDoc (bn r₂)).visible := by
  rw [bsec h r₁ r₂ hu hd]

/-! ## The visible text -/

/-- The blocks that are not deleted hold, for each of their clocks, the
character `f` assigns to it. -/
def Payload (f : Id → Char) (bs : List Block) : Prop :=
  ∀ b, b ∈ bs → b.deleted = false → b.content.chars = b.units.map (fun u => f u.id)

theorem filter_all_false {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ a, a ∈ l → p a = false) → l.filter p = [] := by
  intro l
  induction l with
  | nil => exact fun _ => rfl
  | cons a t ih =>
    intro h
    rw [filter_cons_false (h a (List.mem_cons_self ..))]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem filter_all_true {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ a, a ∈ l → p a = true) → l.filter p = l := by
  intro l
  induction l with
  | nil => exact fun _ => rfl
  | cons a t ih =>
    intro h
    rw [filter_cons_true (h a (List.mem_cons_self ..)),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The visible text is the text of the visible clocks of the document. -/
theorem visible_eq_map {f : Id → Char} {bs : List Block} (hn : NodupIds (flatten bs))
    (hp : Payload f bs) : visible bs = (toDoc bs).visible.map f := by
  have hall : ∀ b, b ∈ bs → ∀ u, u ∈ b.units → (u.id ∈ deletedSet bs ↔ b.deleted = true) := by
    intro b hb u hu
    have hub : u.id ∈ b.units.map Item.id := List.mem_map.mpr ⟨u, hu, rfl⟩
    constructor
    · intro h
      obtain ⟨d, hd, hdel, hx⟩ := mem_deletedSet.mp h
      rw [← block_unique hn hd hb hx hub]
      exact hdel
    · intro h
      exact mem_deletedSet.mpr ⟨b, hb, h, hub⟩
  have key : ∀ t : List Block, (∀ b, b ∈ t → b ∈ bs) →
      visible t =
        (((flatten t).filter (fun a => decide (¬ a.id ∈ deletedSet bs))).map Item.id).map f := by
    intro t
    induction t with
    | nil => exact fun _ => rfl
    | cons b t ih =>
      intro ht
      have hb : b ∈ bs := ht b (List.mem_cons_self ..)
      rw [visible_cons, flatten_cons, List.filter_append, List.map_append, List.map_append,
        ih (fun x hx => ht x (List.mem_cons_of_mem _ hx))]
      congr 1
      by_cases hd : b.deleted = true
      · have e : b.units.filter (fun a => decide (¬ a.id ∈ deletedSet bs)) = [] :=
          filter_all_false (fun u hu =>
            decide_eq_false (fun hnot => hnot ((hall b hb u hu).mpr hd)))
        rw [ite_eq_left hd, e, List.map_nil, List.map_nil]
      · have hd' : b.deleted = false := by
          cases hbd : b.deleted with
          | false => rfl
          | true => exact absurd hbd hd
        have e : b.units.filter (fun a => decide (¬ a.id ∈ deletedSet bs)) = b.units :=
          filter_all_true (fun u hu =>
            decide_eq_true (fun hin => hd ((hall b hb u hu).mp hin)))
        rw [ite_eq_right hd, e, hp b hb hd']
        exact List.map_map.symm
  exact key bs (fun _ h => h)

/-- The visible texts of replicas that stand for the states of a reachable
network, with the same clocks and deletions, agree. -/
theorem BInv.sec_visible {bn : Nat → List Block} {n : Net} (hinv : BInv bn n) (r₁ r₂ : Nat)
    (hu : ∀ u, u ∈ flatten (bn r₁) ↔ u ∈ flatten (bn r₂))
    (hd : ∀ x, x ∈ deletedSet (bn r₁) ↔ x ∈ deletedSet (bn r₂)) {f : Id → Char}
    (hp₁ : Payload f (bn r₁)) (hp₂ : Payload f (bn r₂)) : visible (bn r₁) = visible (bn r₂) := by
  have hn : ∀ r, NodupIds (flatten (bn r)) := by
    intro r
    have e : flatten (bn r) = (n.st r).items := congrArg Doc.items (hinv.doc r)
    rw [e]
    exact (hinv.reach.inv.legal r).nodup
  rw [visible_eq_map (hn r₁) hp₁, visible_eq_map (hn r₂) hp₂, hinv.sec r₁ r₂ hu hd]

/-- **The visible texts agree.** Two replicas of a block-level run with the
same clocks and deletions, whose live blocks hold the text `f` assigns to
their clocks, show the same text. -/
theorem bsec_visible {bn : Nat → List Block} {n : Net} (h : BRun bn n) (r₁ r₂ : Nat)
    (hu : ∀ u, u ∈ flatten (bn r₁) ↔ u ∈ flatten (bn r₂))
    (hd : ∀ x, x ∈ deletedSet (bn r₁) ↔ x ∈ deletedSet (bn r₂)) {f : Id → Char}
    (hp₁ : Payload f (bn r₁)) (hp₂ : Payload f (bn r₂)) : visible (bn r₁) = visible (bn r₂) :=
  (brun_sound h).sec_visible r₁ r₂ hu hd hp₁ hp₂

end YoctoSpec
