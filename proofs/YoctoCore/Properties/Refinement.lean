/-
L3: the extracted `YataStoreCore` refines `YoctoSpec`.

`abs f s` (`YataStore.abs`) is the block sequence of `YoctoSpec` a store stands
for. The theorems of `YataStore` say, function by function, what a call does to
it. This file puts them together: in a run of replicas that hold extracted
stores (`CoreRun`: every step is a call of an extracted function that
returned) every replica stands for its state in a reachable unit-level network
of `YoctoSpec` (`coreRun_sound`), so the strong eventual consistency
`YoctoSpec` proves for its model holds for the extracted Rust (`core_sec`,
`core_sec_ids`, `core_sec_visible`, and `core_sec_visible_ids` for what the
extracted `visible_ids` answers). `core_witness` is such a run, with two
replicas that insert concurrently.
-/
import Aeneas
import YoctoSpec
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.YataModel
import YoctoCore.Properties.YataMerge
import YoctoCore.Properties.YataStore
import YoctoCore.Properties.YataStoreMerge

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open YoctoCore.Code
open YoctoCore.Properties.YataModel YoctoCore.Properties.YataStore

set_option autoImplicit false

namespace YoctoCore.Properties.Refinement

/-- What a triple says about a call that returned. -/
theorem of_spec {α : Type} {m : Result α} {P : α → Prop} {x : α} (h : m ⦃ P ⦄) (e : m = ok x) :
    P x := by
  rw [e] at h
  simp only [spec_ok] at h
  exact h

/-- A call that meets a specification returned: the specifications of this
development are total. -/
theorem ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    ∃ x, m = ok x ∧ P x := by
  cases m with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact ((spec_vis i k).mp h).elim
  | div => exact (spec_div.mp h).elim

/-! ## The replicas -/

/-- The stores of the replicas after replica `r` moved to `s`. -/
def updS (sn : Nat → yata_store.YataStoreCore) (r : Nat) (s : yata_store.YataStoreCore) :
    Nat → yata_store.YataStoreCore :=
  fun r' => if r' = r then s else sn r'

theorem abs_updS (f : YoctoSpec.Id → Char) (sn : Nat → yata_store.YataStoreCore) (r : Nat)
    (s : yata_store.YataStoreCore) :
    (fun r' => YataStore.abs f (updS sn r s r')) =
      YoctoSpec.upd (fun r' => YataStore.abs f (sn r')) r (YataStore.abs f s) := by
  funext r'
  unfold updS YoctoSpec.upd
  by_cases e : r' = r
  · simp [e]
  · simp [e]

theorem inv_updS {sn : Nat → yata_store.YataStoreCore} (h : ∀ r, Inv (sn r)) (r : Nat)
    {s : yata_store.YataStoreCore} (hs : Inv s) : ∀ r', Inv (updS sn r s r') := by
  intro r'
  unfold updS
  by_cases e : r' = r
  · simp only [e, ↓reduceIte]
    exact hs
  · simp only [e, ↓reduceIte]
    exact h r'

theorem updS_same (sn : Nat → yata_store.YataStoreCore) (r : Nat)
    (s : yata_store.YataStoreCore) : updS sn r s r = s := by
  unfold updS
  simp

theorem updS_ne (sn : Nat → yata_store.YataStoreCore) {r r' : Nat}
    (s : yata_store.YataStoreCore) (h : r' ≠ r) : updS sn r s r' = sn r' := by
  unfold updS
  simp [h]

theorem upd_self (bn : Nat → List YoctoSpec.Block) (r : Nat) : YoctoSpec.upd bn r (bn r) = bn := by
  funext r'
  unfold YoctoSpec.upd
  by_cases e : r' = r
  · simp [e]
  · simp [e]

/-- Splits change neither the clocks nor the deletions of a block sequence. -/
theorem toDoc_splits : ∀ (zs : List YoctoSpec.Id) (bs : List YoctoSpec.Block),
    YoctoSpec.toDoc (zs.foldl YoctoSpec.split bs) = YoctoSpec.toDoc bs
  | [], _ => rfl
  | z :: t, bs => by
    show YoctoSpec.toDoc (t.foldl YoctoSpec.split (YoctoSpec.split bs z)) = YoctoSpec.toDoc bs
    rw [toDoc_splits t, YoctoSpec.toDoc_split]

/-! ## Runs of the extracted store -/

/-- A run of replicas that hold extracted stores, next to the unit-level
network of `YoctoSpec` it implements. Every step is a call of an extracted
function that returned (`= ok …`), whatever it answered: `new` or `with_key`
(under any key, one for each replica), `integrate`, `split`,
`merge_adjacent`, `gc` and `delete_range`.

A struct a replica integrates is created at the replica or delivered to it,
clock by clock, in the unit-level network (`UnitRun`, the hypothesis of
`YoctoSpec.BRun.integrate`). -/
inductive CoreRun (f : YoctoSpec.Id → Char) :
    (Nat → yata_store.YataStoreCore) → YoctoSpec.Net → Prop
  | init {s0 : yata_store.YataStoreCore} :
      yata_store.YataStoreCore.new = ok s0 → CoreRun f (fun _ => s0) YoctoSpec.Net.init
  /-- every replica starts from the store of `with_key`, each under a key of
  its own: the key is where the conflict scans of a store look ids up, and
  no two replicas need the same one -/
  | initKeyed {sn : Nat → yata_store.YataStoreCore} :
      (∀ r, ∃ k0 k1 : Std.U64, yata_store.YataStoreCore.with_key k0 k1 = ok (sn r)) →
      CoreRun f sn YoctoSpec.Net.init
  | integrate {sn : Nat → yata_store.YataStoreCore} {n n' : YoctoSpec.Net} (r : Nat)
      (id : yata_store.IdCore) (len : Std.U64) (ol or_ : Option yata_store.IdCore)
      (res : core.result.Result Std.U32 client_blocks.StoreError)
      (s' : yata_store.YataStoreCore) :
      CoreRun f sn n →
      yata_store.YataStoreCore.integrate (sn r) id len ol or_ = ok (res, s') →
      (∀ idx, res = core.result.Result.Ok idx →
        YoctoSpec.UnitRun r n (blockOf f (newItem id len ol or_)).units n') →
      (∀ e, res = core.result.Result.Err e → n' = n) →
      CoreRun f (updS sn r s') n'
  | split {sn : Nat → yata_store.YataStoreCore} {n : YoctoSpec.Net} (r : Nat)
      (id : yata_store.IdCore)
      (res : core.result.Result (Option Std.U32) client_blocks.StoreError)
      (s' : yata_store.YataStoreCore) :
      CoreRun f sn n → yata_store.YataStoreCore.split (sn r) id = ok (res, s') →
      CoreRun f (updS sn r s') n
  /-- replica `r` asks for the struct that holds `id` and its successor on
  the timeline to become one item: whatever the call answers (it merged
  them, it did not, or the store does not hold `id`), nothing changes in the
  network -/
  | merge {sn : Nat → yata_store.YataStoreCore} {n : YoctoSpec.Net} (r : Nat)
      (id : yata_store.IdCore)
      (res : core.result.Result Bool client_blocks.StoreError)
      (s' : yata_store.YataStoreCore) :
      CoreRun f sn n → yata_store.YataStoreCore.merge_adjacent (sn r) id = ok (res, s') →
      CoreRun f (updS sn r s') n
  | gc {sn : Nat → yata_store.YataStoreCore} {n : YoctoSpec.Net} (r : Nat)
      (s' : yata_store.YataStoreCore) :
      CoreRun f sn n → yata_store.YataStoreCore.gc (sn r) = ok s' → CoreRun f (updS sn r s') n
  /-- replica `r` deletes the clocks `start..stop` of `client`, its store
  holds `start`, the range is not empty and the call accepts: in the network
  the replica deletes the clocks of the range it held before the call
  (`YoctoSpec.presentRange`, the step of `YoctoSpec.BRun.delete`) -/
  | delete {sn : Nat → yata_store.YataStoreCore} {n : YoctoSpec.Net} (r : Nat)
      (client start stop : Std.U64) (s' : yata_store.YataStoreCore) :
      CoreRun f sn n →
      yata_store.YataStoreCore.delete_range (sn r) client start stop =
        ok (core.result.Result.Ok (), s') →
      (⟨client.val, start.val⟩ : YoctoSpec.Id) ∈
        (YoctoSpec.flatten (YataStore.abs f (sn r))).map YoctoSpec.Item.id →
      start.val < stop.val →
      CoreRun f (updS sn r s')
        (n.deletes r (YoctoSpec.presentRange (YataStore.abs f (sn r)) client.val start.val
          stop.val))
  /-- any other call of `delete_range` that returned (it failed, the store
  does not hold `start`, or the range is empty): nothing is deleted in the
  network -/
  | deleteNone {sn : Nat → yata_store.YataStoreCore} {n : YoctoSpec.Net} (r : Nat)
      (client start stop : Std.U64)
      (res : core.result.Result Unit client_blocks.StoreError)
      (s' : yata_store.YataStoreCore) :
      CoreRun f sn n →
      yata_store.YataStoreCore.delete_range (sn r) client start stop = ok (res, s') →
      ¬ (res = core.result.Result.Ok () ∧
        (⟨client.val, start.val⟩ : YoctoSpec.Id) ∈
          (YoctoSpec.flatten (YataStore.abs f (sn r))).map YoctoSpec.Item.id ∧
        start.val < stop.val) →
      CoreRun f (updS sn r s') n

/-- **Refinement.** In a run of the extracted store every replica keeps the
invariant, and the block sequence it stands for is its state in a reachable
unit-level network of `YoctoSpec` (`YoctoSpec.BInv`, what `YoctoSpec.brun_sound`
gives for the block-level runs of the model). -/
theorem coreRun_sound {f : YoctoSpec.Id → Char} {sn : Nat → yata_store.YataStoreCore}
    {n : YoctoSpec.Net} (h : CoreRun f sn n) :
    (∀ r, Inv (sn r)) ∧ YoctoSpec.BInv (fun r => YataStore.abs f (sn r)) n := by
  induction h with
  | @init s0 h0 =>
    obtain ⟨hm, hinv⟩ := of_spec YataStore.new_spec h0
    refine ⟨fun _ => hinv, ?_⟩
    have e : (fun _ : Nat => YataStore.abs f s0) = fun _ => [] := by
      funext _
      unfold YataStore.abs
      rw [hm]
      rfl
    rw [e]
    exact YoctoSpec.brun_sound YoctoSpec.BRun.init
  | @initKeyed sn h0 =>
    have hm : ∀ r, toM (sn r) = ⟨[], none, []⟩ ∧ Inv (sn r) := by
      intro r
      obtain ⟨k0, k1, e⟩ := h0 r
      obtain ⟨hm, hinv, _, _⟩ := of_spec (YataStore.with_key_spec k0 k1) e
      exact ⟨hm, hinv⟩
    refine ⟨fun r => (hm r).2, ?_⟩
    have e : (fun r : Nat => YataStore.abs f (sn r)) = fun _ => [] := by
      funext r
      unfold YataStore.abs
      rw [(hm r).1]
      rfl
    rw [e]
    exact YoctoSpec.brun_sound YoctoSpec.BRun.init
  | @integrate sn n n' r id len ol or_ res s' _ hcall hok herr ih =>
    obtain ⟨hinv, hb⟩ := ih
    have hp0 := of_spec (integrate_spec (sn r) id len ol or_ (hinv r)) hcall
    have hp : IntegratePost (sn r) id len ol or_ res s' := hp0
    refine ⟨inv_updS hinv r hp.inv, ?_⟩
    rw [abs_updS]
    cases res with
    | Err e =>
      rw [herr e rfl]
      obtain ⟨zs, hzs⟩ := hp.err e rfl
      refine hb.same r ?_ (blocks_wf hp.inv)
      rw [hzs f]
      exact toDoc_splits zs _
    | Ok idx =>
      have hunits := hok idx rfl
      obtain ⟨hpos, hint⟩ := hp.done idx rfl
      have hblen : 0 < (blockOf f (newItem id len ol or_)).len := by
        rw [blockOf_len]
        exact hpos
      -- the struct stands between its origins in the network, so `Sep` holds
      have hrun' := hunits
      rw [YoctoSpec.units_eq_cons' hblen] at hrun'
      obtain ⟨hci, _⟩ := hrun'.head hb.reach
      have hitems : YoctoSpec.flatten (YataStore.abs f (sn r)) = (n.st r).items :=
        congrArg YoctoSpec.Doc.items (hb.doc r)
      rw [← hitems] at hci
      have hnod : YoctoSpec.NodupIds (YoctoSpec.flatten (YataStore.abs f (sn r))) := by
        rw [hitems]
        exact (hb.reach.inv.legal r).nodup
      have hsep : Sep (toM (sn r)) (ol.map toId) (or_.map toId) :=
        sep_of_canIntegrate (hinv r) hnod hci
      rw [hint hsep f]
      exact hb.integrate r _ hblen rfl hunits
  | @split sn n r id res s' _ hcall ih =>
    obtain ⟨hinv, hb⟩ := ih
    have hp0 := of_spec (split_spec (sn r) id (hinv r)) hcall
    have hp : SplitPost (sn r) (toId id) SplitOk res s' := hp0
    cases res with
    | Err e =>
      have es : s' = sn r := hp.err e rfl
      refine ⟨inv_updS hinv r (by rw [es]; exact hinv r), ?_⟩
      rw [abs_updS, es, upd_self]
      exact hb
    | Ok slot =>
      cases slot with
      | none => exact absurd rfl hp.gone
      | some i =>
        have ok := hp.found i rfl
        refine ⟨inv_updS hinv r ok.wf, ?_⟩
        rw [abs_updS]
        refine hb.same r ?_ (blocks_wf ok.wf)
        have e : YataStore.abs f s' = YoctoSpec.split (YataStore.abs f (sn r)) (toId id) :=
          ok.blocks f
        rw [e]
        exact YoctoSpec.toDoc_split _ _
  | @merge sn n r id res s' _ hcall ih =>
    obtain ⟨hinv, hb⟩ := ih
    have hp0 := of_spec (merge_adjacent_spec (sn r) id (hinv r)) hcall
    have hp : MergeAdjacentPost (sn r) id res s' := hp0
    refine ⟨inv_updS hinv r hp.inv, ?_⟩
    rw [abs_updS]
    exact hb.same r (hp.doc f) (blocks_wf hp.inv)
  | @gc sn n r s' _ hcall ih =>
    obtain ⟨hinv, hb⟩ := ih
    obtain ⟨hinv', habs⟩ := of_spec (gc_spec (sn r) (hinv r)) hcall
    refine ⟨inv_updS hinv r hinv', ?_⟩
    rw [abs_updS]
    refine hb.same r ?_ (blocks_wf hinv')
    rw [habs f]
    exact YoctoSpec.toDoc_gcContent _
  | @delete sn n r client start stop s' _ hcall hheld hlt ih =>
    obtain ⟨hinv, hb⟩ := ih
    have hp0 := of_spec (delete_range_spec (sn r) client start stop (hinv r)) hcall
    have hp : DeletePost (sn r) client start stop (core.result.Result.Ok ()) s' := hp0
    have hh : Held (toM (sn r)) ⟨client.val, start.val⟩ :=
      (held_iff (s := toM (sn r)) (f := f) (hinv r) _).mp hheld
    obtain ⟨hflat, hdel⟩ := hp.done rfl hh hlt f
    refine ⟨inv_updS hinv r hp.inv, ?_⟩
    rw [abs_updS]
    exact hb.deletes r _ hflat hdel (blocks_wf hp.inv)
  | @deleteNone sn n r client start stop res s' _ hcall hnot ih =>
    obtain ⟨hinv, hb⟩ := ih
    have hp0 := of_spec (delete_range_spec (sn r) client start stop (hinv r)) hcall
    have hp : DeletePost (sn r) client start stop res s' := hp0
    refine ⟨inv_updS hinv r hp.inv, ?_⟩
    rw [abs_updS]
    refine hb.same r ?_ (blocks_wf hp.inv)
    cases res with
    | Err e => exact hp.err e rfl f
    | Ok u =>
      have es : s' = sn r := hp.idle rfl (fun hno => hnot
        ⟨rfl, (held_iff (s := toM (sn r)) (f := f) (hinv r) _).mpr hno.1, hno.2⟩)
      rw [es]

/-! ## Strong eventual consistency of the extracted store -/

/-- **SEC, on the extracted Rust.** After any run of the extracted store
(structs integrated in any causal order, deletions, splits, merges and
content collection interleaved at will), two replicas that hold the same clocks and the same
deletions stand for the same document: the same sequence of clocks with the
same origins, and the same delete set. -/
theorem core_sec {f : YoctoSpec.Id → Char} {sn : Nat → yata_store.YataStoreCore}
    {n : YoctoSpec.Net} (h : CoreRun f sn n) (r₁ r₂ : Nat)
    (hu : ∀ u, u ∈ YoctoSpec.flatten (YataStore.abs f (sn r₁)) ↔
      u ∈ YoctoSpec.flatten (YataStore.abs f (sn r₂)))
    (hd : ∀ x, x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₁)) ↔
      x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₂))) :
    YoctoSpec.toDoc (YataStore.abs f (sn r₁)) = YoctoSpec.toDoc (YataStore.abs f (sn r₂)) :=
  (coreRun_sound h).2.sec r₁ r₂ hu hd

/-- The same, comparing the clocks the two replicas hold by id only
(`YoctoSpec.bsec_ids`). -/
theorem core_sec_ids {f : YoctoSpec.Id → Char} {sn : Nat → yata_store.YataStoreCore}
    {n : YoctoSpec.Net} (h : CoreRun f sn n) (r₁ r₂ : Nat)
    (hu : ∀ x, x ∈ (YoctoSpec.flatten (YataStore.abs f (sn r₁))).map YoctoSpec.Item.id ↔
      x ∈ (YoctoSpec.flatten (YataStore.abs f (sn r₂))).map YoctoSpec.Item.id)
    (hd : ∀ x, x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₁)) ↔
      x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₂))) :
    YoctoSpec.toDoc (YataStore.abs f (sn r₁)) = YoctoSpec.toDoc (YataStore.abs f (sn r₂)) :=
  (coreRun_sound h).2.sec_ids r₁ r₂ hu hd

/-- **The visible texts agree, on the extracted Rust.** -/
theorem core_sec_visible {f : YoctoSpec.Id → Char} {sn : Nat → yata_store.YataStoreCore}
    {n : YoctoSpec.Net} (h : CoreRun f sn n) (r₁ r₂ : Nat)
    (hu : ∀ u, u ∈ YoctoSpec.flatten (YataStore.abs f (sn r₁)) ↔
      u ∈ YoctoSpec.flatten (YataStore.abs f (sn r₂)))
    (hd : ∀ x, x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₁)) ↔
      x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₂))) :
    YoctoSpec.visible (YataStore.abs f (sn r₁)) = YoctoSpec.visible (YataStore.abs f (sn r₂)) :=
  (coreRun_sound h).2.sec_visible r₁ r₂ hu hd
    (payload_blocks ((coreRun_sound h).1 r₁)) (payload_blocks ((coreRun_sound h).1 r₂))

/-- **What `visible_ids` answers agrees, on the extracted Rust.** After any
run of the extracted store, the extracted `visible_ids` returns on two
replicas that hold the same clocks and the same deletions, and its two
answers stand, clock by clock, for the same sequence of ids: the visible ids
of the document both replicas stand for. The blocks may differ (one replica
may have split or merged where the other did not); their clocks do not. -/
theorem core_sec_visible_ids {f : YoctoSpec.Id → Char} {sn : Nat → yata_store.YataStoreCore}
    {n : YoctoSpec.Net} (h : CoreRun f sn n) (r₁ r₂ : Nat)
    (hu : ∀ u, u ∈ YoctoSpec.flatten (YataStore.abs f (sn r₁)) ↔
      u ∈ YoctoSpec.flatten (YataStore.abs f (sn r₂)))
    (hd : ∀ x, x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₁)) ↔
      x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn r₂))) :
    ∃ v₁ v₂, yata_store.YataStoreCore.visible_ids (sn r₁) = ok v₁ ∧
      yata_store.YataStoreCore.visible_ids (sn r₂) = ok v₂ ∧
      expandIds (v₁.val.map toPair) = expandIds (v₂.val.map toPair) ∧
      expandIds (v₁.val.map toPair) = (YoctoSpec.toDoc (YataStore.abs f (sn r₁))).visible := by
  have hinv := (coreRun_sound h).1
  obtain ⟨v₁, e₁, hv₁⟩ := ok_of_spec (visible_ids_spec (sn r₁) (hinv r₁))
  obtain ⟨v₂, e₂, hv₂⟩ := ok_of_spec (visible_ids_spec (sn r₂) (hinv r₂))
  have h₁ : expandIds (v₁.val.map toPair) =
      (YoctoSpec.toDoc (YataStore.abs f (sn r₁))).visible := by
    rw [hv₁]
    exact expand_visM (hinv r₁)
  have h₂ : expandIds (v₂.val.map toPair) =
      (YoctoSpec.toDoc (YataStore.abs f (sn r₂))).visible := by
    rw [hv₂]
    exact expand_visM (hinv r₂)
  refine ⟨v₁, v₂, e₁, e₂, ?_, h₁⟩
  rw [h₁, h₂, core_sec h r₁ r₂ hu hd]

/-! ## A run that inserts

`CoreRun` and the hypotheses of `core_sec` are not empty: two replicas start
from the store of `new`, each integrates a struct of its own at the start of
the sequence, then the struct of the other. Every step is a call of the
extracted `integrate` that accepted (`YataStore.integrate_root_spec`), and
the two replicas end with the same two clocks in the same order. -/

/-- A struct without origins, in a store with room for it, is accepted, and
the store keeps the invariant. -/
theorem root_step (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (len : Std.U64)
    (h : Inv s) (hr : Room s id len) :
    ∃ (idx : Std.U32) (s' : yata_store.YataStoreCore),
      yata_store.YataStoreCore.integrate s id len none none =
        ok (core.result.Result.Ok idx, s') ∧
      Inv s' ∧ RootPost s id (core.result.Result.Ok idx) s' := by
  obtain ⟨⟨r, s'⟩, hcall, hp0⟩ := ok_of_spec (integrate_root_spec s id len h hr)
  have hp : RootPost s id r s' := hp0
  obtain ⟨idx, rfl⟩ := hp.ok
  have hq0 := of_spec (integrate_spec s id len none none h) hcall
  have hq : IntegratePost s id len none none (core.result.Result.Ok idx) s' := hq0
  exact ⟨idx, s', hcall, hq.inv, hp⟩

/-- An empty store has room for a first struct of one clock. -/
theorem room_empty {s : yata_store.YataStoreCore} (hi : s.items.val = [])
    (hc : s.clients.val = []) (id : yata_store.IdCore) (len : Std.U64) (hl : len.val = 1)
    (hk : id.clock.val = 0) : Room s id len :=
  { pos := by omega
    fits := by scalar_tac
    items := by rw [hi]; decide
    clients := by rw [hc]; decide
    cont := fun c hcm _ => by rw [hc] at hcm; cases hcm }

/-- After a first struct, there is room for the first struct of another
client. -/
theorem room_next {s s' : yata_store.YataStoreCore} {id id' : yata_store.IdCore}
    {r : core.result.Result Std.U32 client_blocks.StoreError} (hp : RootPost s id r s')
    (hi : s.items.val = []) (hc : s.clients.val = []) (len : Std.U64) (hl : len.val = 1)
    (hk : id'.clock.val = 0) (hne : id.client ≠ id'.client) : Room s' id' len :=
  { pos := by omega
    fits := by scalar_tac
    items := by rw [hp.items, hi]; decide
    clients := by
      have h := hp.clients
      rw [hc] at h
      exact Nat.lt_of_le_of_lt h (by decide)
    cont := fun c hcm he => by
      rcases hp.owner c hcm with e | e
      · exact absurd (e.symm.trans he) hne
      · rw [hc] at e
        cases e }

/-- The units of a struct of one clock without origins. -/
theorem units_root (f : YoctoSpec.Id → Char) (id : yata_store.IdCore) (len : Std.U64)
    (h1 : len.val = 1) :
    (blockOf f (newItem id len none none)).units = [⟨toId id, none, none⟩] := by
  unfold YoctoSpec.Block.units
  rw [blockOf_len]
  show YoctoSpec.unitsFrom (toId id).client none (toId id).clock none len.val = _
  rw [h1]
  rfl

namespace Witness

/-- The clock `0` of client `1`, and the one of client `2`: no origins. -/
def u1 : YoctoSpec.Item := ⟨⟨1, 0⟩, none, none⟩

def u2 : YoctoSpec.Item := ⟨⟨2, 0⟩, none, none⟩

/-- The network: replica `1` creates `u1`, replica `2` creates `u2`, then
each receives the item of the other. -/
def n1 : YoctoSpec.Net := YoctoSpec.Net.init.gen 1 u1

def n2 : YoctoSpec.Net := n1.gen 2 u2

def n3 : YoctoSpec.Net := n2.deliver 1 u2

def n4 : YoctoSpec.Net := n3.deliver 2 u1

theorem run1 : YoctoSpec.UnitRun 1 YoctoSpec.Net.init [u1] n1 :=
  YoctoSpec.UnitRun.gen rfl ⟨YoctoSpec.present_none _, YoctoSpec.present_none _, rfl⟩
    (YoctoSpec.UnitRun.nil _)

theorem run2 : YoctoSpec.UnitRun 2 n1 [u2] n2 :=
  YoctoSpec.UnitRun.gen rfl ⟨YoctoSpec.present_none _, YoctoSpec.present_none _, rfl⟩
    (YoctoSpec.UnitRun.nil _)

theorem ready3 : YoctoSpec.Ready (n2.st 1).items u2 := by
  have hitems : (n2.st 1).items = [u1] := rfl
  rw [hitems]
  refine ⟨?_, YoctoSpec.present_none _, YoctoSpec.present_none _, ?_⟩
  · intro a ha
    rw [List.mem_singleton.mp ha]
    decide
  · intro a ha hc
    rw [List.mem_singleton.mp ha] at hc
    exact absurd hc (by decide)

theorem run3 : YoctoSpec.UnitRun 1 n2 [u2] n3 :=
  YoctoSpec.UnitRun.deliver (by decide) ready3 (YoctoSpec.UnitRun.nil _)

theorem ready4 : YoctoSpec.Ready (n3.st 2).items u1 := by
  have hitems : (n3.st 2).items = [u2] := rfl
  rw [hitems]
  refine ⟨?_, YoctoSpec.present_none _, YoctoSpec.present_none _, ?_⟩
  · intro a ha
    rw [List.mem_singleton.mp ha]
    decide
  · intro a ha hc
    rw [List.mem_singleton.mp ha] at hc
    exact absurd hc (by decide)

theorem run4 : YoctoSpec.UnitRun 2 n3 [u1] n4 :=
  YoctoSpec.UnitRun.deliver (by decide) ready4 (YoctoSpec.UnitRun.nil _)

/-- Both replicas hold `u1` before `u2`: the item of the smaller client first. -/
theorem items1 : (n4.st 1).items = [u1, u2] := rfl

theorem items2 : (n4.st 2).items = [u1, u2] := rfl

theorem deleted1 : (n4.st 1).deleted = YoctoSpec.DeleteSet.empty := rfl

theorem deleted2 : (n4.st 2).deleted = YoctoSpec.DeleteSet.empty := rfl

end Witness

/-- **`CoreRun` holds a run that inserts.** From the store of `new`, replica
`1` integrates the clock `0` of client `1` and replica `2` the clock `0` of
client `2`, both at the start of the sequence; then each integrates the
struct of the other. The four calls of the extracted `integrate` return and
accept, and both replicas stand for the two clocks, the one of client `1`
first, with nothing deleted. -/
theorem core_witness (f : YoctoSpec.Id → Char) :
    ∃ (sn : Nat → yata_store.YataStoreCore) (n : YoctoSpec.Net), CoreRun f sn n ∧
      YoctoSpec.flatten (YataStore.abs f (sn 1)) =
        [⟨⟨1, 0⟩, none, none⟩, ⟨⟨2, 0⟩, none, none⟩] ∧
      YoctoSpec.flatten (YataStore.abs f (sn 2)) =
        [⟨⟨1, 0⟩, none, none⟩, ⟨⟨2, 0⟩, none, none⟩] ∧
      YoctoSpec.deletedSet (YataStore.abs f (sn 1)) = YoctoSpec.DeleteSet.empty ∧
      YoctoSpec.deletedSet (YataStore.abs f (sn 2)) = YoctoSpec.DeleteSet.empty := by
  -- the two structs: one clock each, no origins
  obtain ⟨one, hone⟩ : ∃ l : Std.U64, l.val = 1 :=
    ⟨1#u64, rfl⟩
  obtain ⟨id1, hid1⟩ : ∃ id : yata_store.IdCore, toId id = ⟨1, 0⟩ :=
    ⟨⟨1#u64, 0#u64⟩, rfl⟩
  obtain ⟨id2, hid2⟩ : ∃ id : yata_store.IdCore, toId id = ⟨2, 0⟩ :=
    ⟨⟨2#u64, 0#u64⟩, rfl⟩
  have hc1 : id1.client.val = 1 := congrArg YoctoSpec.Id.client hid1
  have hk1 : id1.clock.val = 0 := congrArg YoctoSpec.Id.clock hid1
  have hc2 : id2.client.val = 2 := congrArg YoctoSpec.Id.client hid2
  have hk2 : id2.clock.val = 0 := congrArg YoctoSpec.Id.clock hid2
  have hne : id1.client ≠ id2.client := by
    intro e
    rw [e] at hc1
    omega
  have hu1 := units_root f id1 one hone
  rw [hid1] at hu1
  have hu2 := units_root f id2 one hone
  rw [hid2] at hu2
  -- the empty store
  obtain ⟨s0, hnew, hm0, hinv0⟩ := ok_of_spec YataStore.new_spec
  have hi0 : s0.items.val = [] := List.map_eq_nil_iff.mp (congrArg MStore.items hm0)
  have hcl0 : s0.clients.val = [] := List.map_eq_nil_iff.mp (congrArg MStore.clients hm0)
  -- the four calls
  obtain ⟨iA, sA, hA, hinvA, hpA⟩ :=
    root_step s0 id1 one hinv0 (room_empty hi0 hcl0 id1 one hone hk1)
  obtain ⟨iB, sB, hB, hinvB, hpB⟩ :=
    root_step s0 id2 one hinv0 (room_empty hi0 hcl0 id2 one hone hk2)
  obtain ⟨iC, sC, hC, _, _⟩ :=
    root_step sA id2 one hinvA (room_next hpA hi0 hcl0 one hone hk2 hne)
  obtain ⟨iD, sD, hD, _, _⟩ :=
    root_step sB id1 one hinvB (room_next hpB hi0 hcl0 one hone hk1 (Ne.symm hne))
  -- the run
  have r0 : CoreRun f (fun _ => s0) YoctoSpec.Net.init := CoreRun.init hnew
  have r1 : CoreRun f (updS (fun _ => s0) 1 sA) Witness.n1 :=
    CoreRun.integrate 1 id1 one none none (core.result.Result.Ok iA) sA r0 hA
      (fun _ _ => by rw [hu1]; exact Witness.run1) (fun _ he => nomatch he)
  have e2 : updS (fun _ => s0) 1 sA 2 = s0 :=
    updS_ne (r := 1) (r' := 2) (fun _ => s0) sA (by decide)
  have r2 : CoreRun f (updS (updS (fun _ => s0) 1 sA) 2 sB) Witness.n2 :=
    CoreRun.integrate 2 id2 one none none (core.result.Result.Ok iB) sB r1
      (by rw [e2]; exact hB) (fun _ _ => by rw [hu2]; exact Witness.run2)
      (fun _ he => nomatch he)
  have e3 : updS (updS (fun _ => s0) 1 sA) 2 sB 1 = sA :=
    (updS_ne (r := 2) (r' := 1) (updS (fun _ => s0) 1 sA) sB (by decide)).trans
      (updS_same (fun _ => s0) 1 sA)
  have r3 : CoreRun f (updS (updS (updS (fun _ => s0) 1 sA) 2 sB) 1 sC) Witness.n3 :=
    CoreRun.integrate 1 id2 one none none (core.result.Result.Ok iC) sC r2
      (by rw [e3]; exact hC) (fun _ _ => by rw [hu2]; exact Witness.run3)
      (fun _ he => nomatch he)
  have e4 : updS (updS (updS (fun _ => s0) 1 sA) 2 sB) 1 sC 2 = sB :=
    (updS_ne (r := 1) (r' := 2) (updS (updS (fun _ => s0) 1 sA) 2 sB) sC (by decide)).trans
      (updS_same (updS (fun _ => s0) 1 sA) 2 sB)
  have r4 :
      CoreRun f (updS (updS (updS (updS (fun _ => s0) 1 sA) 2 sB) 1 sC) 2 sD) Witness.n4 :=
    CoreRun.integrate 2 id1 one none none (core.result.Result.Ok iD) sD r3
      (by rw [e4]; exact hD) (fun _ _ => by rw [hu1]; exact Witness.run4)
      (fun _ he => nomatch he)
  -- every replica stands for its state in the network
  have hb := (coreRun_sound r4).2
  have d1 := hb.doc 1
  have d2 := hb.doc 2
  exact ⟨_, _, r4, (congrArg YoctoSpec.Doc.items d1).trans Witness.items1,
    (congrArg YoctoSpec.Doc.items d2).trans Witness.items2,
    (congrArg YoctoSpec.Doc.deleted d1).trans Witness.deleted1,
    (congrArg YoctoSpec.Doc.deleted d2).trans Witness.deleted2⟩

/-- **`core_sec` and `core_sec_visible` on that run**: their hypotheses hold
for two replicas that are not empty, so the two stand for the same document
and show the same text. -/
theorem core_witness_sec (f : YoctoSpec.Id → Char) :
    ∃ (sn : Nat → yata_store.YataStoreCore) (n : YoctoSpec.Net), CoreRun f sn n ∧
      YoctoSpec.flatten (YataStore.abs f (sn 1)) ≠ [] ∧
      YoctoSpec.toDoc (YataStore.abs f (sn 1)) = YoctoSpec.toDoc (YataStore.abs f (sn 2)) ∧
      YoctoSpec.visible (YataStore.abs f (sn 1)) =
        YoctoSpec.visible (YataStore.abs f (sn 2)) := by
  obtain ⟨sn, n, h, h1, h2, d1, d2⟩ := core_witness f
  have hu : ∀ u, u ∈ YoctoSpec.flatten (YataStore.abs f (sn 1)) ↔
      u ∈ YoctoSpec.flatten (YataStore.abs f (sn 2)) := by
    intro u
    rw [h1, h2]
  have hd : ∀ x, x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn 1)) ↔
      x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn 2)) := by
    intro x
    rw [d1, d2]
  refine ⟨sn, n, h, ?_, core_sec h 1 2 hu hd, core_sec_visible h 1 2 hu hd⟩
  rw [h1]
  exact List.cons_ne_nil _ _

/-- **`core_sec_visible_ids` on that run**: the extracted `visible_ids`
returns on both replicas, and both answers stand for the clock `0` of client
`1` and then the clock `0` of client `2`. -/
theorem core_witness_visible_ids (f : YoctoSpec.Id → Char) :
    ∃ (sn : Nat → yata_store.YataStoreCore) (n : YoctoSpec.Net)
      (v₁ v₂ : alloc.vec.Vec (yata_store.IdCore × Std.U64)), CoreRun f sn n ∧
      yata_store.YataStoreCore.visible_ids (sn 1) = ok v₁ ∧
      yata_store.YataStoreCore.visible_ids (sn 2) = ok v₂ ∧
      expandIds (v₁.val.map toPair) = [⟨1, 0⟩, ⟨2, 0⟩] ∧
      expandIds (v₂.val.map toPair) = [⟨1, 0⟩, ⟨2, 0⟩] := by
  obtain ⟨sn, n, h, h1, h2, d1, d2⟩ := core_witness f
  have hu : ∀ u, u ∈ YoctoSpec.flatten (YataStore.abs f (sn 1)) ↔
      u ∈ YoctoSpec.flatten (YataStore.abs f (sn 2)) := by
    intro u
    rw [h1, h2]
  have hd : ∀ x, x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn 1)) ↔
      x ∈ YoctoSpec.deletedSet (YataStore.abs f (sn 2)) := by
    intro x
    rw [d1, d2]
  obtain ⟨v₁, v₂, e₁, e₂, heq, hvis⟩ := core_sec_visible_ids h 1 2 hu hd
  have hdoc : (YoctoSpec.toDoc (YataStore.abs f (sn 1))).visible = [⟨1, 0⟩, ⟨2, 0⟩] := by
    show ((YoctoSpec.flatten (YataStore.abs f (sn 1))).filter
      (fun a => decide (¬ a.id ∈ YoctoSpec.deletedSet (YataStore.abs f (sn 1))))).map
        YoctoSpec.Item.id = _
    rw [h1, d1]
    rfl
  refine ⟨sn, n, v₁, v₂, h, e₁, e₂, ?_, ?_⟩
  · rw [hvis, hdoc]
  · rw [← heq, hvis, hdoc]

end YoctoCore.Properties.Refinement
