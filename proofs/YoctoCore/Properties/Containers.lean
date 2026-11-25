/-
The lists of a document, on the extracted store: a list of a parent type, and
the list of the values of a map key.

`DocStore` keeps one YATA list for every parent type and, under a map, for
every key. Each is a sequence as `YataStoreCore` keeps one, and `Refinement`
proves the strong eventual consistency of that store. This file reads its
theorems for the two kinds of list:

* a list of a parent type shows the clocks that are not deleted, in order
  (`containers_sec`: `YoctoSpec.visible`);
* the list of a map key shows its last clock, when that is not deleted
  (`keyValue`, last writer wins).

`map_sec` is `core_sec` for a key: replicas that hold the same clocks and the
same deletions read the same value. `map_sec_lww` asks less: last writer wins
deletes every value but the last one of a key (`DocKernel.Lww`, which
`decide_integrate_link` keeps: `DocKernel.keyRun_lww`), so replicas that hold
the same clocks need to agree on the last one only, and then hold the same
deletions too. `containers_sec` is both, for every list of a document at once.

What is assumed, and tested: that the lists of `DocStore` are such stores,
kept apart by `same_container` and linked as `decide_integrate_link` says
(`proofs/TRUSTED.md`).
-/
import Aeneas
import YoctoSpec
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.DocKernel
import YoctoCore.Properties.YataStore
import YoctoCore.Properties.Refinement

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open YoctoCore.Code
open YoctoCore.Properties.ListAux
open YoctoCore.Properties.YataStore YoctoCore.Properties.Refinement
open YoctoCore.Properties.DocKernel (Lww winner lww_determined)

set_option maxHeartbeats 400000
set_option autoImplicit false

namespace YoctoCore.Properties.Containers

/-! ## The list of a map key -/

/-- The clocks of a document in order, each with whether it is deleted. -/
def chainOf (d : YoctoSpec.Doc) : List (YoctoSpec.Id × Bool) :=
  d.items.map (fun u => (u.id, decide (u.id ∈ d.deleted)))

/-- The list of a map key a store holds: its clocks in order, each with
whether it is deleted. -/
def keyChain (f : YoctoSpec.Id → Char) (s : yata_store.YataStoreCore) :
    List (YoctoSpec.Id × Bool) :=
  chainOf (YoctoSpec.toDoc (YataStore.abs f s))

/-- The value of a map key whose list a store holds: its last clock, unless
that is deleted. -/
def keyValue (f : YoctoSpec.Id → Char) (s : yata_store.YataStoreCore) : Option YoctoSpec.Id :=
  winner (keyChain f s)

theorem chainOf_fst (d : YoctoSpec.Doc) :
    (chainOf d).map Prod.fst = d.items.map YoctoSpec.Item.id := by
  unfold chainOf
  rw [List.map_map]
  rfl

/-- A deleted clock of a block sequence is a clock of it. -/
theorem deleted_is_clock {bs : List YoctoSpec.Block} {x : YoctoSpec.Id}
    (h : x ∈ YoctoSpec.deletedSet bs) : ∃ u, u ∈ YoctoSpec.flatten bs ∧ u.id = x := by
  obtain ⟨b, hb, _, hx⟩ := YoctoSpec.mem_deletedSet.mp h
  obtain ⟨u, hu, e⟩ := List.mem_map.mp hx
  exact ⟨u, List.mem_flatMap.mpr ⟨b, hb, hu⟩, e⟩

/-- The deletions of a document are read off its list. -/
theorem deleted_of_chain {bs₁ bs₂ : List YoctoSpec.Block}
    (e : chainOf (YoctoSpec.toDoc bs₁) = chainOf (YoctoSpec.toDoc bs₂)) {x : YoctoSpec.Id}
    (h : x ∈ YoctoSpec.deletedSet bs₁) : x ∈ YoctoSpec.deletedSet bs₂ := by
  obtain ⟨u, hu, ex⟩ := deleted_is_clock h
  have hmem : (x, true) ∈ chainOf (YoctoSpec.toDoc bs₁) := by
    unfold chainOf
    refine List.mem_map.mpr ⟨u, hu, ?_⟩
    rw [ex]
    have hd : x ∈ (YoctoSpec.toDoc bs₁).deleted := h
    rw [decide_eq_true hd]
  rw [e] at hmem
  unfold chainOf at hmem
  obtain ⟨u', _, e'⟩ := List.mem_map.mp hmem
  have e1 : u'.id = x := congrArg Prod.fst e'
  have e2 : decide (u'.id ∈ (YoctoSpec.toDoc bs₂).deleted) = true := congrArg Prod.snd e'
  rw [← e1]
  exact of_decide_eq_true e2

/-- **Replicas that hold the same clocks and the same deletions under a map
key read the same value**, whatever order the values came in: `core_sec`,
for the list of a key. -/
theorem map_sec {f : YoctoSpec.Id → Char} {sn : Nat → yata_store.YataStoreCore}
    {n : YoctoSpec.Net} (h : CoreRun f sn n) (r₁ r₂ : Nat)
    (hu : ∀ u, u ∈ YoctoSpec.flatten (YataStore.abs f (sn r₁)) ↔
      u ∈ YoctoSpec.flatten (YataStore.abs f (sn r₂)))
    (hd : ∀ x, x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₁)) ↔
      x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₂))) :
    keyChain f (sn r₁) = keyChain f (sn r₂) ∧ keyValue f (sn r₁) = keyValue f (sn r₂) := by
  have e : keyChain f (sn r₁) = keyChain f (sn r₂) :=
    congrArg chainOf (core_sec h r₁ r₂ hu hd)
  refine ⟨e, ?_⟩
  unfold keyValue
  rw [e]

/-- **Last writer wins converges from the clocks alone.** Two replicas that
hold the same clocks under a map key, each with every value but the last one
deleted (`DocKernel.Lww`: what linking values as `decide_integrate_link` says
keeps, `DocKernel.keyRun_lww`), and that agree on whether the last one is
deleted, stand for the same document under that key: the same clocks in the
same order, the same deletions (the ones last writer wins made included,
which no replica was told), and the same value. -/
theorem map_sec_lww {f : YoctoSpec.Id → Char} {sn : Nat → yata_store.YataStoreCore}
    {n : YoctoSpec.Net} (h : CoreRun f sn n) (r₁ r₂ : Nat)
    (hu : ∀ x, x ∈ (YoctoSpec.flatten (YataStore.abs f (sn r₁))).map YoctoSpec.Item.id ↔
      x ∈ (YoctoSpec.flatten (YataStore.abs f (sn r₂))).map YoctoSpec.Item.id)
    (h₁ : Lww (keyChain f (sn r₁))) (h₂ : Lww (keyChain f (sn r₂)))
    (hlast : ∀ e₁ e₂, (keyChain f (sn r₁)).getLast? = some e₁ →
      (keyChain f (sn r₂)).getLast? = some e₂ → e₁.2 = e₂.2) :
    YoctoSpec.toDoc (YataStore.abs f (sn r₁)) = YoctoSpec.toDoc (YataStore.abs f (sn r₂)) ∧
      keyValue f (sn r₁) = keyValue f (sn r₂) := by
  have hb := (coreRun_sound h).2
  -- the clocks are in the same order: the conflict scan, whatever was deleted
  have hi₁ : YoctoSpec.flatten (YataStore.abs f (sn r₁)) = (n.st r₁).items :=
    congrArg YoctoSpec.Doc.items (hb.doc r₁)
  have hi₂ : YoctoSpec.flatten (YataStore.abs f (sn r₂)) = (n.st r₂).items :=
    congrArg YoctoSpec.Doc.items (hb.doc r₂)
  have hitems : YoctoSpec.flatten (YataStore.abs f (sn r₁)) =
      YoctoSpec.flatten (YataStore.abs f (sn r₂)) := by
    rw [hi₁, hi₂]
    apply YoctoSpec.sec_ids hb.reach r₁ r₂
    intro x
    rw [← hi₁, ← hi₂]
    exact hu x
  -- so the lists of the key hold the same values, and are the same list
  have hvals : (keyChain f (sn r₁)).map Prod.fst = (keyChain f (sn r₂)).map Prod.fst := by
    unfold keyChain
    rw [chainOf_fst, chainOf_fst]
    show (YoctoSpec.flatten (YataStore.abs f (sn r₁))).map YoctoSpec.Item.id =
      (YoctoSpec.flatten (YataStore.abs f (sn r₂))).map YoctoSpec.Item.id
    rw [hitems]
  have e : keyChain f (sn r₁) = keyChain f (sn r₂) := lww_determined h₁ h₂ hvals hlast
  have hdel : YoctoSpec.deletedSet (YataStore.abs f (sn r₁)) =
      YoctoSpec.deletedSet (YataStore.abs f (sn r₂)) :=
    YoctoSpec.DeleteSet.ext (fun x => ⟨deleted_of_chain e, deleted_of_chain e.symm⟩)
  refine ⟨YoctoSpec.toDoc_ext hitems hdel, ?_⟩
  unfold keyValue
  rw [e]

/-! ## Every list of a document -/

/-- **Strong eventual consistency, list by list.** A document is its lists,
one store each (`c` names a list: a parent type and, under a map, a key), and
a run of the document is a run of each. Two replicas that hold the same
clocks and the same deletions in every list stand for the same document in
every list: the same visible text in a list of a parent type, and the same
value under a map key. -/
theorem containers_sec {κ : Type} {f : YoctoSpec.Id → Char}
    {sn : κ → Nat → yata_store.YataStoreCore} {n : κ → YoctoSpec.Net}
    (h : ∀ c, CoreRun f (sn c) (n c)) (r₁ r₂ : Nat)
    (hu : ∀ c u, u ∈ YoctoSpec.flatten (YataStore.abs f (sn c r₁)) ↔
      u ∈ YoctoSpec.flatten (YataStore.abs f (sn c r₂)))
    (hd : ∀ c x, x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn c r₁)) ↔
      x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn c r₂))) (c : κ) :
    YoctoSpec.toDoc (YataStore.abs f (sn c r₁)) = YoctoSpec.toDoc (YataStore.abs f (sn c r₂)) ∧
      YoctoSpec.visible (YataStore.abs f (sn c r₁)) =
        YoctoSpec.visible (YataStore.abs f (sn c r₂)) ∧
      keyValue f (sn c r₁) = keyValue f (sn c r₂) :=
  ⟨core_sec (h c) r₁ r₂ (hu c) (hd c), core_sec_visible (h c) r₁ r₂ (hu c) (hd c),
    (map_sec (h c) r₁ r₂ (hu c) (hd c)).2⟩

end YoctoCore.Properties.Containers
