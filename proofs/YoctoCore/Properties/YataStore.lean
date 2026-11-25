/-
`y_octo_core::yata_store`: the sequence store of the post-S3 `DocStore`.

`toM` reads the extracted store as the pure model of `YataModel`; `Inv` is the
invariant of the model on it. Every function below is total on every store
that satisfies `Inv` (no panic, no overflow, no index out of bounds), keeps
`Inv`, and does on `toM` what the model operation of the same name does.

`merge_adjacent` (with `continues`) and `visible_ids` have no theorem here
yet: see `proofs/TRUSTED.md`.
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.YataModel
import YoctoCore.Properties.ClientBlocks

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties
open YoctoCore.Properties.ListAux YoctoCore.Properties.YataModel
open YoctoCore.Properties.ClientBlocks (toKind toBlock toBlocks kindSlot kindSlot_val
  toBlocks_get? toBlocks_length get?_of_getElem)

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace YoctoCore.Properties.YataStore

/-! ## The model of a store -/

def toId (i : yata_store.IdCore) : YoctoSpec.Id := ⟨i.client.val, i.clock.val⟩

def toSlot (o : Option Std.U32) : Option Nat := o.map (fun i => i.val)

def toItem (x : yata_store.ItemCore) : MItem :=
  { id := toId x.id
    len := x.len.val
    originL := x.origin_left.map toId
    originR := x.origin_right.map toId
    left := toSlot x.left
    right := toSlot x.right
    deleted := x.deleted
    gc := x.gc }

def toClient (c : yata_store.ClientEntryCore) : MClient :=
  ⟨c.client.val, toBlocks c.blocks, c.blocks.end_clock.val⟩

def toM (s : yata_store.YataStoreCore) : MStore :=
  ⟨s.items.val.map toItem, toSlot s.start, s.clients.val.map toClient⟩

/-- The invariant of a store: the one of its model (I1, I2, I3, I5, I8). -/
def Inv (s : yata_store.YataStoreCore) : Prop := YataModel.WF (toM s)

/-- The abstraction function: the block sequence of `YoctoSpec` the store
stands for, `f` giving the character of every clock. -/
def abs (f : YoctoSpec.Id → Char) (s : yata_store.YataStoreCore) : List YoctoSpec.Block :=
  blocks f (toM s)

theorem toId_eq_iff (a b : yata_store.IdCore) :
    toId a = toId b ↔ a.client = b.client ∧ a.clock = b.clock := by
  constructor
  · intro h
    exact ⟨UScalar.eq_of_val_eq (congrArg YoctoSpec.Id.client h),
      UScalar.eq_of_val_eq (congrArg YoctoSpec.Id.clock h)⟩
  · rintro ⟨h1, h2⟩
    unfold toId
    rw [h1, h2]

theorem toId_inj {a b : yata_store.IdCore} (h : toId a = toId b) : a = b := by
  obtain ⟨h1, h2⟩ := (toId_eq_iff a b).mp h
  cases a
  cases b
  simp only at h1 h2
  rw [h1, h2]

theorem u32_val_inj {x y : Std.U32} : x.val = y.val ↔ x = y :=
  ⟨UScalar.eq_of_val_eq, fun h => by rw [h]⟩

theorem toSlot_some_iff {o : Option Std.U32} {i : Std.U32} : toSlot o = some i.val ↔ o = some i := by
  cases o with
  | none => simp [toSlot]
  | some j => simp [toSlot, u32_val_inj]

theorem toM_items_get? (s : yata_store.YataStoreCore) (i : Nat) :
    (toM s).items[i]? = (s.items.val[i]?).map toItem :=
  get?_map _ _ _

theorem toM_clients_get? (s : yata_store.YataStoreCore) (i : Nat) :
    (toM s).clients[i]? = (s.clients.val[i]?).map toClient :=
  get?_map _ _ _

theorem toM_items_length (s : yata_store.YataStoreCore) :
    (toM s).items.length = s.items.val.length := by
  simp [toM]

theorem mem_toM_clients {s : yata_store.YataStoreCore} {c : yata_store.ClientEntryCore}
    (h : c ∈ s.clients.val) : toClient c ∈ (toM s).clients :=
  List.mem_map.mpr ⟨c, h, rfl⟩

/-! ## Comparisons -/

@[step]
theorem id_eq_spec (a b : yata_store.IdCore) :
    yata_store.id_eq a b ⦃ r => (r = true ↔ toId a = toId b) ⦄ := by
  unfold yata_store.id_eq
  rw [toId_eq_iff]
  by_cases h : a.client = b.client
  · have h' : (a.client = b.client) = True := eq_true h
    simp only [h', ↓reduceIte, spec_ok]
    simp
  · simp only [h, ↓reduceIte, spec_ok]
    simp

@[step]
theorem opt_id_eq_spec (a b : Option yata_store.IdCore) :
    yata_store.opt_id_eq a b ⦃ r => (r = true ↔ a.map toId = b.map toId) ⦄ := by
  unfold yata_store.opt_id_eq
  cases a with
  | none => cases b <;> simp [spec_ok]
  | some x =>
    cases b with
    | none => simp [spec_ok]
    | some y =>
      refine spec_mono (id_eq_spec x y) ?_
      intro r hr
      simp [hr]

@[step]
theorem opt_slot_eq_spec (a b : Option Std.U32) :
    yata_store.opt_slot_eq a b ⦃ r => (r = true ↔ toSlot a = toSlot b) ⦄ := by
  unfold yata_store.opt_slot_eq
  cases a <;> cases b <;> simp [spec_ok, toSlot, u32_val_inj]

@[step]
theorem slot_is_spec (a : Option Std.U32) (b : Std.U32) :
    yata_store.slot_is a b ⦃ r => (r = true ↔ toSlot a = some b.val) ⦄ := by
  unfold yata_store.slot_is
  cases a <;> simp [spec_ok, toSlot, u32_val_inj]

@[step]
theorem check_origin_spec (id : yata_store.IdCore) (origin : Option yata_store.IdCore) :
    yata_store.check_origin id origin ⦃ _ => True ⦄ := by
  unfold yata_store.check_origin
  cases origin with
  | none => simp [spec_ok]
  | some o =>
    dsimp only
    split_ifs <;> simp [spec_ok]

/-! ## `ids_contain` -/

theorem ids_contain_loop_spec (ids : Slice yata_store.IdCore) (id : yata_store.IdCore)
    (i : Std.Usize)
    (hinv : ∀ (j : Nat) (x : yata_store.IdCore), j < i.val → ids.val[j]? = some x →
      toId x ≠ toId id) :
    yata_store.ids_contain_loop ids id i ⦃ r => (r = true ↔ toId id ∈ ids.val.map toId) ⦄ := by
  unfold yata_store.ids_contain_loop
  refine loop.spec_decr_nat
    (fun (k : Std.Usize) => ids.val.length - k.val)
    (fun (k : Std.Usize) => ∀ (j : Nat) (x : yata_store.IdCore), j < k.val →
      ids.val[j]? = some x → toId x ≠ toId id)
    (fun (r : Bool) => (r = true ↔ toId id ∈ ids.val.map toId))
    _ i ?_ hinv
  intro k hk
  unfold yata_store.ids_contain_loop.body
  simp only
  by_cases hlt : k < Slice.len ids
  · simp only [hlt, ↓reduceIte]
    have hkl : k.val < ids.val.length := by scalar_tac
    step as ⟨ic, hic⟩
    have hx := get?_of_getElem hkl hic
    step as ⟨b, hb⟩
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte, spec_ok]
      have hmem : toId id ∈ ids.val.map toId := by
        rw [← hb.mp hbt]
        exact List.mem_map.mpr ⟨ic, get?_mem hx, rfl⟩
      simp [hmem]
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
      step as ⟨k1, hk1⟩
      refine ⟨?_, by scalar_tac⟩
      intro j x hj hjx
      by_cases e : j = k.val
      · rw [e, hx] at hjx
        cases hjx
        intro heq
        exact hbt (hb.mpr heq)
      · exact hk j x (by scalar_tac) hjx
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : ids.val.length ≤ k.val := by scalar_tac
    constructor
    · intro h
      cases h
    · intro hmem
      exfalso
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmem
      obtain ⟨j, hj⟩ := mem_get? hx
      exact hk j x (by have := get?_lt hj; omega) hj hxe

@[step]
theorem ids_contain_spec (ids : Slice yata_store.IdCore) (id : yata_store.IdCore) :
    yata_store.ids_contain ids id ⦃ r => (r = true ↔ toId id ∈ ids.val.map toId) ⦄ := by
  unfold yata_store.ids_contain
  exact ids_contain_loop_spec ids id 0#usize (by
    intro j x hj
    exfalso
    scalar_tac)

/-! ## `new`, `client_index`, `get_state` -/

@[step]
theorem new_spec : yata_store.YataStoreCore.new ⦃ s => toM s = ⟨[], none, []⟩ ∧ Inv s ⦄ := by
  unfold yata_store.YataStoreCore.new
  simp only [spec_ok]
  have key : ∀ s' : yata_store.YataStoreCore, toM s' = ⟨[], none, []⟩ →
      toM s' = ⟨[], none, []⟩ ∧ Inv s' := by
    intro s' e
    refine ⟨e, ?_⟩
    unfold Inv
    rw [e]
    exact WF.empty
  apply key
  simp [toM, toSlot]

theorem client_index_loop_spec (s : yata_store.YataStoreCore) (client : Std.U64) (i : Std.Usize)
    (hinv : ∀ (j : Nat) (c : yata_store.ClientEntryCore), j < i.val →
      s.clients.val[j]? = some c → c.client ≠ client) :
    yata_store.YataStoreCore.client_index_loop s client i ⦃ o =>
      (o = none ∧ ∀ (j : Nat) (c : yata_store.ClientEntryCore), s.clients.val[j]? = some c →
        c.client ≠ client) ∨
      ∃ (ci : Std.Usize) (c : yata_store.ClientEntryCore), o = some ci ∧
        s.clients.val[ci.val]? = some c ∧ c.client = client ⦄ := by
  unfold yata_store.YataStoreCore.client_index_loop
  refine loop.spec_decr_nat
    (fun (k : Std.Usize) => s.clients.val.length - k.val)
    (fun (k : Std.Usize) => ∀ (j : Nat) (c : yata_store.ClientEntryCore), j < k.val →
      s.clients.val[j]? = some c → c.client ≠ client)
    (fun (o : Option Std.Usize) =>
      (o = none ∧ ∀ (j : Nat) (c : yata_store.ClientEntryCore), s.clients.val[j]? = some c →
        c.client ≠ client) ∨
      ∃ (ci : Std.Usize) (c : yata_store.ClientEntryCore), o = some ci ∧
        s.clients.val[ci.val]? = some c ∧ c.client = client)
    _ i ?_ hinv
  intro k hk
  unfold yata_store.YataStoreCore.client_index_loop.body
  simp only
  by_cases hlt : k < alloc.vec.Vec.len s.clients
  · simp only [hlt, ↓reduceIte]
    have hkl : k.val < s.clients.val.length := by scalar_tac
    step as ⟨cec, hcec⟩
    have hx := get?_of_getElem hkl hcec
    by_cases hc : cec.client = client
    · have hc' : (cec.client = client) = True := eq_true hc
      simp only [hc', ↓reduceIte, spec_ok]
      right
      exact ⟨k, cec, rfl, hx, hc⟩
    · simp only [hc, ↓reduceIte]
      step as ⟨k1, hk1⟩
      refine ⟨?_, by scalar_tac⟩
      intro j c hj hjc
      by_cases e : j = k.val
      · rw [e, hx] at hjc
        cases hjc
        exact hc
      · exact hk j c (by scalar_tac) hjc
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : s.clients.val.length ≤ k.val := by scalar_tac
    left
    refine ⟨trivial, ?_⟩
    intro j c hj
    exact hk j c (by have := get?_lt hj; omega) hj

@[step]
theorem client_index_spec (s : yata_store.YataStoreCore) (client : Std.U64) :
    yata_store.YataStoreCore.client_index s client ⦃ o =>
      (o = none ∧ ∀ (j : Nat) (c : yata_store.ClientEntryCore), s.clients.val[j]? = some c →
        c.client ≠ client) ∨
      ∃ (ci : Std.Usize) (c : yata_store.ClientEntryCore), o = some ci ∧
        s.clients.val[ci.val]? = some c ∧ c.client = client ⦄ := by
  unfold yata_store.YataStoreCore.client_index
  exact client_index_loop_spec s client 0#usize (by
    intro j c hj
    exfalso
    scalar_tac)

/-- The clock the next struct of `client` has to start at; `0` for a client
the store does not know. -/
@[step]
theorem get_state_spec (s : yata_store.YataStoreCore) (client : Std.U64) :
    yata_store.YataStoreCore.get_state s client ⦃ r =>
      (r.val = 0 ∧ ∀ (j : Nat) (c : yata_store.ClientEntryCore), s.clients.val[j]? = some c →
        c.client ≠ client) ∨
      ∃ (j : Nat) (c : yata_store.ClientEntryCore), s.clients.val[j]? = some c ∧
        c.client = client ∧ r = c.blocks.end_clock ⦄ := by
  unfold yata_store.YataStoreCore.get_state
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hno⟩ | ⟨ci, c, rfl, hc, hcl⟩
  · simp only [spec_ok]
    left
    exact ⟨by simp, hno⟩
  · simp only []
    have hlt := get?_lt hc
    step as ⟨cec, hcec⟩
    have hx := get?_of_getElem hlt hcec
    rw [hc] at hx
    cases hx
    right
    exact ⟨ci.val, c, hc, hcl, rfl⟩

/-! ## `locate` and `node_id` -/

/-- `locate` answers the timeline and the block that hold a clock. -/
@[step]
theorem locate_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (h : Inv s) :
    yata_store.YataStoreCore.locate s id ⦃ o =>
      (o = none ∧ ∀ (c : MClient) (p : Nat) (b : MBlock), ¬ At (toM s) (toId id) c p b) ∨
      ∃ (ci pos : Std.Usize) (c : yata_store.ClientEntryCore) (b : client_blocks.BlockRefCore),
        o = some (ci, pos) ∧ s.clients.val[ci.val]? = some c ∧
        c.blocks.blocks.val[pos.val]? = some b ∧
        At (toM s) (toId id) (toClient c) pos.val (toBlock b) ⦄ := by
  unfold yata_store.YataStoreCore.locate
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hno⟩ | ⟨ci, c, rfl, hc, hcl⟩
  · simp only [spec_ok]
    left
    refine ⟨trivial, ?_⟩
    intro c' p b ha
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp ha.mem
    obtain ⟨j, hj⟩ := mem_get? hc0
    apply hno j c0 hj
    exact UScalar.eq_of_val_eq ha.client
  · simp only []
    have hlt := get?_lt hc
    step as ⟨cec, hcec⟩
    have hx := get?_of_getElem hlt hcec
    rw [hc] at hx
    cases hx
    have hmem : toClient c ∈ (toM s).clients := mem_toM_clients (get?_mem hc)
    have hwf : ClientBlocks.WF c.blocks := ⟨YataModel.WF.timeline h (toClient c) hmem⟩
    have hclient : (toClient c).client = (toId id).client := by
      show c.client.val = id.client.val
      rw [hcl]
    step with ClientBlocks.find_spec c.blocks id.clock hwf as ⟨o1, ho1⟩
    rcases ho1 with ⟨rfl, hnone⟩ | ⟨pos, rfl, hholds⟩
    · simp only [spec_ok]
      left
      refine ⟨trivial, ?_⟩
      intro c' p b ha
      have ec : c' = toClient c := YataModel.WF.client_unique h ha.mem hmem (ha.client.trans hclient.symm)
      subst ec
      exact hnone p ⟨b, ha.block, ha.ge, ha.lt⟩
    · simp only [spec_ok]
      right
      obtain ⟨a, ha, hge, hlt'⟩ := hholds
      rw [toBlocks_get?] at ha
      cases hb : c.blocks.blocks.val[pos.val]? with
      | none =>
        rw [hb] at ha
        cases ha
      | some b =>
        rw [hb] at ha
        cases ha
        refine ⟨ci, pos, c, b, by rfl, hc, by trivial, ?_⟩
        exact ⟨hmem, hclient, by show (toBlocks c.blocks)[pos.val]? = some (toBlock b); rw [toBlocks_get?, hb]; rfl, hge, hlt'⟩

/-- `node_id` answers the first clock of the block that holds a clock: the
owner of the clock in the block sequence. -/
@[step]
theorem node_id_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (h : Inv s) :
    yata_store.YataStoreCore.node_id s id ⦃ o => o.map toId = ownerM (toM s) (toId id) ⦄ := by
  unfold yata_store.YataStoreCore.node_id
  step with locate_spec s id h as ⟨o, ho⟩
  rcases ho with ⟨rfl, hno⟩ | ⟨ci, pos, c, b, rfl, hc, hb, hat⟩
  · simp only [spec_ok]
    rw [ownerM_none h hno]
    rfl
  · simp only []
    have hlt := get?_lt hc
    step as ⟨cec, hcec⟩
    have hx := get?_of_getElem hlt hcec
    rw [hc] at hx
    cases hx
    have hlt2 := get?_lt hb
    step as ⟨brc, hbrc⟩
    have hy := get?_of_getElem hlt2 hbrc
    rw [hb] at hy
    cases hy
    rw [ownerM_at h hat]
    rfl

/-! ## Links -/

theorem toM_set_item {s : yata_store.YataStoreCore} {i : Std.Usize} {x : yata_store.ItemCore}
    (g : yata_store.ItemCore → yata_store.ItemCore) (g' : MItem → MItem)
    (hx : s.items.val[i.val]? = some x) (hg : ∀ a, toItem (g a) = g' (toItem a)) :
    toM { s with items := s.items.set i (g x) } =
      { toM s with items := upd (toM s).items i.val g' } := by
  unfold toM
  simp only [alloc.vec.Vec.set_val_eq, set_eq_upd_get hx g, map_upd toItem _ _ g g' hg]

@[step]
theorem set_left_spec (s : yata_store.YataStoreCore) (slot : Option Std.U32) (value : Std.U32)
    (hb : ∀ i, slot = some i → i.val < s.items.val.length) :
    yata_store.YataStoreCore.set_left s slot value ⦃ s' =>
      toM s' = { toM s with items := setLeft value.val (toSlot slot) (toM s).items } ∧
        s'.items.val.length = s.items.val.length ∧ s'.clients = s.clients ⦄ := by
  unfold yata_store.YataStoreCore.set_left
  cases slot with
  | none => simp [spec_ok, setLeft, toSlot]
  | some idx =>
    have hlt := hb idx rfl
    simp only []
    step as ⟨i, hi⟩
    have hilt : i.val < s.items.val.length := by scalar_tac
    step as ⟨ic, back, h1, h2⟩
    have hx := get?_of_getElem hilt h1
    subst h2
    have hiv : i.val = idx.val := by scalar_tac
    have e := toM_set_item (s := s) (i := i) (fun a => { a with left := some value })
      (fun a => { a with left := some value.val }) hx (fun _ => rfl)
    rw [hiv] at e
    refine ⟨e, ?_⟩
    simp

/-- The first item of the sequence after linking `n` after `slot`. -/
def startAfter (slot : Option Nat) (n : Nat) (start : Option Nat) : Option Nat :=
  match slot with
  | none => some n
  | some _ => start

@[step]
theorem set_next_spec (s : yata_store.YataStoreCore) (slot : Option Std.U32) (value : Std.U32)
    (hb : ∀ i, slot = some i → i.val < s.items.val.length) :
    yata_store.YataStoreCore.set_next s slot value ⦃ s' =>
      toM s' = { items := setRight value.val (toSlot slot) (toM s).items
                 start := startAfter (toSlot slot) value.val (toM s).start
                 clients := (toM s).clients } ∧
        s'.items.val.length = s.items.val.length ∧ s'.clients = s.clients ⦄ := by
  unfold yata_store.YataStoreCore.set_next
  cases slot with
  | none => simp [spec_ok, setRight, toSlot, toM, startAfter]
  | some idx =>
    have hlt := hb idx rfl
    simp only []
    step as ⟨i, hi⟩
    have hilt : i.val < s.items.val.length := by scalar_tac
    step as ⟨ic, back, h1, h2⟩
    have hx := get?_of_getElem hilt h1
    subst h2
    have hiv : i.val = idx.val := by scalar_tac
    have e := toM_set_item (s := s) (i := i) (fun a => { a with right := some value })
      (fun a => { a with right := some value.val }) hx (fun _ => rfl)
    rw [hiv] at e
    refine ⟨e, ?_⟩
    simp

@[step]
theorem next_of_spec (s : yata_store.YataStoreCore) (left : Option Std.U32)
    (hb : ∀ i, left = some i → i.val < s.items.val.length) :
    yata_store.YataStoreCore.next_of s left ⦃ r =>
      toSlot r = nextOf (toM s).items (toM s).start (toSlot left) ⦄ := by
  unfold yata_store.YataStoreCore.next_of
  cases left with
  | none => simp [spec_ok, nextOf, toSlot, toM]
  | some idx =>
    have hlt := hb idx rfl
    simp only []
    step as ⟨i, hi⟩
    have hilt : i.val < s.items.val.length := by scalar_tac
    step as ⟨ic, hic⟩
    have hx := get?_of_getElem hilt hic
    have hiv : i.val = idx.val := by scalar_tac
    rw [hiv] at hx
    simp [nextOf, rightOf, toSlot, toM_items_get?, hx, toItem]

/-! ## `split_node`, `split`, `split_after` -/

theorem toItem_right_half (item : yata_store.ItemCore) (clock i3 i4 diff : Std.U64)
    (idx : Std.U32) (hclock : clock.val = item.id.clock.val + diff.val)
    (hi3 : i3.val = item.len.val - diff.val) (hi4 : i4.val = clock.val - 1) :
    toItem { item with
        id := { item.id with clock := clock }
        len := i3
        origin_left := some { item.id with clock := i4 }
        left := some idx } =
      { (toItem item).rightHalf diff.val with
        left := some idx.val
        right := (toItem item).right } := by
  simp [toItem, toId, toSlot, MItem.rightHalf, hclock, hi3, hi4]

theorem coreAt_toM {s : yata_store.YataStoreCore} {i : Nat} {item : yata_store.ItemCore}
    (h : s.items.val[i]? = some item) : coreAt (toM s).items i = some (toItem item).core := by
  unfold coreAt
  rw [toM_items_get?, h]
  rfl

theorem itemAt_toM {s : yata_store.YataStoreCore} {i : Nat} {item : yata_store.ItemCore}
    (h : s.items.val[i]? = some item) : itemAt (toM s).items i = toItem item := by
  unfold itemAt
  rw [toM_items_get?, h]
  rfl

theorem toM_clients_at {s : yata_store.YataStoreCore} {i : Nat} {c : yata_store.ClientEntryCore}
    (h : s.clients.val[i]? = some c) : (toM s).clients[i]? = some (toClient c) := by
  rw [toM_clients_get?, h]
  rfl

theorem toClient_block {c : yata_store.ClientEntryCore} {p : Nat}
    {b : client_blocks.BlockRefCore} (h : c.blocks.blocks.val[p]? = some b) :
    (toClient c).blocks[p]? = some (toBlock b) := by
  show (toBlocks c.blocks)[p]? = some (toBlock b)
  rw [toBlocks_get?, h]
  rfl

/-- The store `split_node` builds is the split of the model. -/
theorem toM_split_node {s : yata_store.YataStoreCore} {ci pos i5 : Std.Usize}
    {c : yata_store.ClientEntryCore} {b : client_blocks.BlockRefCore} {idx right_idx : Std.U32}
    {item : yata_store.ItemCore} {diff clock i3 i4 : Std.U64}
    {kind : client_blocks.BlockKindCore} {cbc : client_blocks.ClientBlocksCore}
    {v1 : alloc.vec.Vec yata_store.ItemCore}
    (hc : s.clients.val[ci.val]? = some c) (hb : c.blocks.blocks.val[pos.val]? = some b)
    (hit : s.items.val[idx.val]? = some item) (hi5 : i5.val = idx.val)
    (hriv : right_idx.val = s.items.val.length)
    (hclock : clock.val = item.id.clock.val + diff.val)
    (hi3 : i3.val = item.len.val - diff.val) (hi4 : i4.val = clock.val - 1)
    (hkind : toKind kind = (toKind b.kind).reslot s.items.val.length)
    (hbl : cbc.blocks.val = insAt c.blocks.blocks.val (pos.val + 1)
      ({ clock := clock, kind := kind } : client_blocks.BlockRefCore))
    (hend : cbc.end_clock = c.blocks.end_clock)
    (hv1 : v1.val = (s.items.set i5 { item with len := diff }).val ++
      [{ item with
          id := { item.id with clock := clock }
          len := i3
          origin_left := some { item.id with clock := i4 }
          left := some idx }]) :
    (MStore.mk
      (setLeft right_idx.val (toSlot item.right)
        (setRight right_idx.val (some idx.val) (v1.val.map toItem)))
      (toSlot s.start)
      ((s.clients.set ci { c with blocks := cbc }).val.map toClient)) =
      splitNode (toM s) ci.val pos.val idx.val diff.val := by
  have hMi : (toM s).items[idx.val]? = some (toItem item) := by
    rw [toM_items_get?, hit]
    rfl
  have hitemAt := itemAt_toM hit
  have hset : (s.items.set i5 { item with len := diff }).val.map toItem =
      upd (toM s).items idx.val (fun y => { y with len := diff.val }) := by
    rw [alloc.vec.Vec.set_val_eq, hi5]
    exact map_set_get toItem hit _ _ rfl
  have hnext : nextOf (upd (toM s).items idx.val (fun y => { y with len := diff.val }))
      (toM s).start (some idx.val) = toSlot item.right := by
    simp [nextOf, rightOf, get?_upd_self, hMi, toItem]
  unfold splitNode linkItems
  rw [MStore.mk.injEq]
  refine ⟨?_, rfl, ?_⟩
  · simp only [hriv, hv1, List.map_append, List.map_cons, List.map_nil, hset, hitemAt, length_upd,
      toM_items_length, hnext, toItem_right_half item clock i3 i4 diff idx hclock hi3 hi4]
    rfl
  · rw [alloc.vec.Vec.set_val_eq]
    refine map_set_get toClient hc _ _ ?_
    simp only [toClient, MClient.withBlock, ClientBlocks.toBlocks_of_insAt hbl, hend, hitemAt,
      toBlocks_get?, hb, toM_items_length]
    simp [toBlock, hclock, hkind, toItem, toId]

structure SplitNodePost (s : yata_store.YataStoreCore) (ci pos : Std.Usize) (diff : Std.U64)
    (b : client_blocks.BlockRefCore)
    (r : core.result.Result (Std.U32 × Std.U32) client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → s' = s
  ok : ∀ l rt, r = core.result.Result.Ok (l, rt) →
    kindSlot b.kind = some l ∧ rt.val = s.items.val.length ∧
      toM s' = splitNode (toM s) ci.val pos.val l.val diff.val

theorem split_node_spec (s : yata_store.YataStoreCore) (ci pos : Std.Usize) (diff : Std.U64)
    (h : Inv s) {c : yata_store.ClientEntryCore} {b : client_blocks.BlockRefCore}
    (hc : s.clients.val[ci.val]? = some c) (hb : c.blocks.blocks.val[pos.val]? = some b)
    (hd : ∀ (i : Nat) (x : MItem), (toKind b.kind).slot = some i →
      coreAt (toM s).items i = some x → 0 < diff.val ∧ diff.val < x.len) :
    yata_store.YataStoreCore.split_node s ci pos diff ⦃ r s' =>
      SplitNodePost s ci pos diff b r s' ⦄ := by
  unfold yata_store.YataStoreCore.split_node
  have hclt := get?_lt hc
  step as ⟨cec, hcec⟩
  have hx := get?_of_getElem hclt hcec
  rw [hc] at hx
  cases hx
  have hblt := get?_lt hb
  step as ⟨block, hblock⟩
  have hy := get?_of_getElem hblt hblock
  rw [hb] at hy
  cases hy
  step as ⟨o, ho⟩
  subst ho
  cases hk : kindSlot b.kind with
  | none =>
    simp only [spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun _ _ h => nomatch h)⟩
  | some idx =>
    simp only []
    by_cases hcap : alloc.vec.Vec.len s.items >= yata_store.MAX_ITEMS
    · simp only [hcap, ↓reduceIte, spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun _ _ h => nomatch h)⟩
    · simp only [hcap, ↓reduceIte]
      have hcap' : s.items.val.length < 4294967295 := by
        simp [yata_store.MAX_ITEMS] at hcap
        scalar_tac
      have hmem : toClient c ∈ (toM s).clients := mem_toM_clients (get?_mem hc)
      have hbm := toClient_block hb
      have hslot : (toBlock b).kind.slot = some idx.val := by
        show (toKind b.kind).slot = some idx.val
        rw [← kindSlot_val, hk]
        rfl
      obtain ⟨i0, x, hs0, hx0, hxid, hxlen, hxdel, hiord, hxpos⟩ :=
        YataModel.WF.block_item h hmem hbm
      rw [hslot] at hs0
      cases hs0
      have hidx : idx.val < s.items.val.length := by
        have := h.chain.bound _ hiord
        rw [toM_items_length] at this
        exact this
      obtain ⟨hd0, hd1⟩ := hd idx.val x hslot hx0
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = idx.val := by scalar_tac
      have hi1lt : i1.val < s.items.val.length := by omega
      step as ⟨item, hitem⟩
      have hit := get?_of_getElem hi1lt hitem
      rw [hi1v] at hit
      have hxitem : x = (toItem item).core := by
        rw [coreAt_toM hit] at hx0
        exact (Option.some.inj hx0).symm
      have hlen : x.len = item.len.val := by
        rw [hxitem]
        rfl
      have hidc : item.id.clock.val = b.clock.val := by
        have := congrArg YoctoSpec.Id.clock hxid
        rw [hxitem] at this
        exact this
      have hE : endAt (toBlocks c.blocks) c.blocks.end_clock.val pos.val ≤ c.blocks.end_clock.val :=
        (YataModel.WF.timeline h _ hmem).end_le_stop pos.val
      have hxlen' : item.len.val =
          endAt (toBlocks c.blocks) c.blocks.end_clock.val pos.val - b.clock.val := by
        rw [← hlen]
        exact hxlen
      rw [hlen] at hd1
      have hright : ∀ i, item.right = some i → i.val < s.items.val.length := by
        intro i hi
        obtain ⟨k, hk'⟩ := mem_get? hiord
        have hr := h.chain.right k idx.val hk'
        have e : rightOf (toM s).items idx.val = some i.val := by
          simp [rightOf, toM_items_get?, hit, toItem, toSlot, hi]
        rw [e] at hr
        have := h.chain.bound i.val (get?_mem hr.symm)
        rw [toM_items_length] at this
        exact this
      have hu32 : (alloc.vec.Vec.len s.items).val ≤ UScalar.max UScalarTy.U32 := by
        scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.U32 (alloc.vec.Vec.len s.items) hu32
        as ⟨right_idx, hri⟩
      have hriv : right_idx.val = s.items.val.length := by
        rw [hri]
        simp
      have hsum : item.id.clock.val + diff.val < c.blocks.end_clock.val := by omega
      step as ⟨clock, hclock⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨dead, hdead⟩
      have hkindspec :
          (if dead = true then ok (client_blocks.BlockKindCore.DeletedItem right_idx)
            else ok (client_blocks.BlockKindCore.Item right_idx)) ⦃ k =>
              toKind k = (toKind b.kind).reslot s.items.val.length ⦄ := by
        by_cases hdd : dead = true
        · simp only [hdd, ↓reduceIte, spec_ok]
          have hd' : (toKind b.kind).dead = true := by
            rw [← hdead]
            exact hdd
          show MKind.deleted right_idx.val = MKind.reslot (toKind b.kind) s.items.val.length
          unfold MKind.reslot
          rw [hd', hriv]
          rfl
        · simp only [hdd, Bool.false_eq_true, ↓reduceIte, spec_ok]
          have hd' : (toKind b.kind).dead = false := by
            rw [← hdead]
            simpa using hdd
          show MKind.item right_idx.val = MKind.reslot (toKind b.kind) s.items.val.length
          unfold MKind.reslot
          rw [hd', hriv]
          rfl
      step with hkindspec as ⟨kind, hkind⟩
      step as ⟨cec1, back, hcec1, hback⟩
      have hc1 := get?_of_getElem hclt hcec1
      rw [hc] at hc1
      cases hc1
      subst hback
      step as ⟨r, cbc, hpost⟩
      cases r with
      | Err error =>
        have hcb := hpost.err error rfl
        subst hcb
        simp only [spec_ok, uncurry'_pair]
        refine ⟨fun _ _ => ?_, (fun _ _ h => nomatch h)⟩
        have e : s.clients.set ci { c with blocks := c.blocks } = s.clients := by
          apply alloc.vec.Vec.ext
          rw [alloc.vec.Vec.set_val_eq]
          exact set_eq_self hc
        show ({ s with clients := s.clients.set ci { c with blocks := c.blocks } } :
          yata_store.YataStoreCore) = s
        rw [e]
      | Ok u =>
        obtain ⟨b', hb', hg1, hg2, hbl, hend⟩ := hpost.ok rfl
        simp only []
        step as ⟨i5, hi5⟩
        have hi5v : i5.val = idx.val := by scalar_tac
        have hi5lt : i5.val < s.items.val.length := by omega
        step as ⟨ic, back1, hic, hback1⟩
        have hic' := get?_of_getElem hi5lt hic
        rw [hi5v, hit] at hic'
        cases hic'
        subst hback1
        step as ⟨v1, hv1⟩
        have hv1len : v1.val.length = s.items.val.length + 1 := by
          have := congrArg List.length hv1
          simpa using this
        have hpre1 : ∀ i, some idx = some i →
            i.val < ({ s with items := v1, clients := s.clients.set ci { c with blocks := cbc } } :
              yata_store.YataStoreCore).items.val.length := by
          intro i hi
          cases hi
          show idx.val < v1.val.length
          omega
        step with set_next_spec _ (some idx) right_idx hpre1 as ⟨self1, hself1, hlen1, hcl1⟩
        have hpre2 : ∀ i, item.right = some i → i.val < self1.items.val.length := by
          intro i hi
          have := hright i hi
          rw [hlen1]
          show i.val < v1.val.length
          omega
        step with set_left_spec self1 item.right right_idx hpre2 as ⟨self2, hself2, hlen2, hcl2⟩
        refine ⟨(fun _ h => nomatch h), fun l rt hEq => ?_⟩
        cases hEq
        refine ⟨hk, hriv, ?_⟩
        rw [hself2, hself1]
        exact toM_split_node hc hb hit hi5v hriv (by scalar_tac) (by scalar_tac) (by scalar_tac)
          hkind hbl hend hv1

structure SplitPost (s : yata_store.YataStoreCore) (z : YoctoSpec.Id)
    (ok : MStore → YoctoSpec.Id → MStore → Nat → Prop)
    (r : core.result.Result (Option Std.U32) client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → s' = s
  gone : r ≠ core.result.Result.Ok none
  found : ∀ i, r = core.result.Result.Ok (some i) → ok (toM s) z (toM s') i.val

/-- `split` makes the clock the first clock of its block (`YoctoSpec.split`). -/
theorem split_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (h : Inv s) :
    yata_store.YataStoreCore.split s id ⦃ r s' => SplitPost s (toId id) SplitOk r s' ⦄ := by
  unfold yata_store.YataStoreCore.split
  step with locate_spec s id h as ⟨o, ho⟩
  rcases ho with ⟨rfl, hno⟩ | ⟨ci, pos, c, b, rfl, hc, hb, hat⟩
  · simp only [spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun h => nomatch h), (fun _ h => nomatch h)⟩
  · simp only []
    have hclt := get?_lt hc
    step as ⟨cec, hcec⟩
    have hx := get?_of_getElem hclt hcec
    rw [hc] at hx
    cases hx
    have hblt := get?_lt hb
    step as ⟨block, hblock⟩
    have hy := get?_of_getElem hblt hblock
    rw [hb] at hy
    cases hy
    step as ⟨o1, ho1⟩
    subst ho1
    cases hk : kindSlot b.kind with
    | none =>
      exfalso
      obtain ⟨i', x', hs', _⟩ := At.item h hat
      have hnone : (toBlock b).kind.slot = none := by
        show (toKind b.kind).slot = none
        rw [← kindSlot_val, hk]
        rfl
      rw [hnone] at hs'
      cases hs'
    | some idx =>
      simp only []
      have hslot : (toBlock b).kind.slot = some idx.val := by
        show (toKind b.kind).slot = some idx.val
        rw [← kindSlot_val, hk]
        rfl
      by_cases heq : id.clock = b.clock
      · have heq' : (id.clock = b.clock) = True := eq_true heq
        simp only [heq', ↓reduceIte, spec_ok, uncurry'_pair]
        refine ⟨(fun _ h => nomatch h), (fun h => nomatch h), fun i hi => ?_⟩
        cases hi
        exact splitOk_same h hat hslot (by show id.clock.val = b.clock.val; rw [heq])
      · simp only [heq, ↓reduceIte]
        have hge : b.clock.val ≤ id.clock.val := hat.ge
        have hne : id.clock.val ≠ b.clock.val := by
          intro e
          exact heq (UScalar.eq_of_val_eq e)
        step as ⟨i, hi⟩
        have hiv : i.val = id.clock.val - b.clock.val := by scalar_tac
        have hd : ∀ (j : Nat) (x : MItem), (toKind b.kind).slot = some j →
            coreAt (toM s).items j = some x → 0 < i.val ∧ i.val < x.len := by
          intro j x hj hx
          obtain ⟨j', x', hs', hx', _, hxlen, _, _, _⟩ := At.item h hat
          rw [hslot] at hs'
          have hjj : (toBlock b).kind.slot = some j := hj
          rw [hslot] at hjj
          cases hs'
          cases hjj
          rw [hx] at hx'
          cases hx'
          have hlt : id.clock.val < endAt (toClient c).blocks (toClient c).stop pos.val := hat.lt
          have hb' : (toBlock b).clock = b.clock.val := rfl
          omega
        step with split_node_spec s ci pos i h hc hb hd as ⟨r, s1, hpost⟩
        cases r with
        | Err error =>
          simp only [spec_ok, uncurry'_pair]
          exact ⟨fun _ _ => hpost.err error rfl, (fun h => nomatch h), (fun _ h => nomatch h)⟩
        | Ok p =>
          obtain ⟨l, rt⟩ := p
          obtain ⟨hl, hrt, hm⟩ := hpost.ok l rt rfl
          show spec (ok _) _
          simp only [spec_ok, uncurry'_pair]
          refine ⟨(fun _ h => nomatch h), (fun h => nomatch h), fun j hj => ?_⟩
          cases hj
          rw [hk] at hl
          cases hl
          rw [hm, hrt, hiv, ← toM_items_length]
          exact splitOk_split h hat (toM_clients_at hc) hslot hne

/-- `split_after` makes the clock the last clock of its block
(`YoctoSpec.splitAfter`). -/
theorem split_after_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (h : Inv s) :
    yata_store.YataStoreCore.split_after s id ⦃ r s' =>
      SplitPost s (toId id) SplitAfterOk r s' ⦄ := by
  unfold yata_store.YataStoreCore.split_after
  step with locate_spec s id h as ⟨o, ho⟩
  rcases ho with ⟨rfl, hno⟩ | ⟨ci, pos, c, b, rfl, hc, hb, hat⟩
  · simp only [spec_ok, uncurry'_pair]
    exact ⟨fun _ _ => rfl, (fun h => nomatch h), (fun _ h => nomatch h)⟩
  · simp only []
    have hclt := get?_lt hc
    step as ⟨cec, hcec⟩
    have hx := get?_of_getElem hclt hcec
    rw [hc] at hx
    cases hx
    have hblt := get?_lt hb
    step as ⟨block, hblock⟩
    have hy := get?_of_getElem hblt hblock
    rw [hb] at hy
    cases hy
    step as ⟨o1, ho1⟩
    subst ho1
    cases hk : kindSlot b.kind with
    | none =>
      exfalso
      obtain ⟨i', x', hs', _⟩ := At.item h hat
      have hnone : (toBlock b).kind.slot = none := by
        show (toKind b.kind).slot = none
        rw [← kindSlot_val, hk]
        rfl
      rw [hnone] at hs'
      cases hs'
    | some idx =>
      simp only []
      have hslot : (toBlock b).kind.slot = some idx.val := by
        show (toKind b.kind).slot = some idx.val
        rw [← kindSlot_val, hk]
        rfl
      have hmem : toClient c ∈ (toM s).clients := mem_toM_clients (get?_mem hc)
      obtain ⟨j', x, hs', hx', _, hxlen, _, hiord, _⟩ := At.item h hat
      rw [hslot] at hs'
      cases hs'
      have hidx : idx.val < s.items.val.length := by
        have := h.chain.bound _ hiord
        rw [toM_items_length] at this
        exact this
      have hge : b.clock.val ≤ id.clock.val := hat.ge
      have hlt : id.clock.val < endAt (toBlocks c.blocks) c.blocks.end_clock.val pos.val := hat.lt
      have hE : endAt (toBlocks c.blocks) c.blocks.end_clock.val pos.val ≤ c.blocks.end_clock.val :=
        (YataModel.WF.timeline h _ hmem).end_le_stop pos.val
      step as ⟨i, hi⟩
      have hiv : i.val = id.clock.val - b.clock.val := by scalar_tac
      step as ⟨cut, hcut⟩
      have hcutv : cut.val = id.clock.val - b.clock.val + 1 := by scalar_tac
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = idx.val := by scalar_tac
      have hi1lt : i1.val < s.items.val.length := by omega
      step as ⟨ic, hic⟩
      have hit := get?_of_getElem hi1lt hic
      rw [hi1v] at hit
      have hxic : x = (toItem ic).core := by
        rw [coreAt_toM hit] at hx'
        exact (Option.some.inj hx').symm
      have hlen : x.len = ic.len.val := by
        rw [hxic]
        rfl
      by_cases hfull : cut >= ic.len
      · simp only [hfull, ↓reduceIte, spec_ok, uncurry'_pair]
        refine ⟨(fun _ h => nomatch h), (fun h => nomatch h), fun j hj => ?_⟩
        cases hj
        refine splitAfterOk_same h hat hslot hx' ?_
        show ¬ id.clock.val - b.clock.val + 1 < x.len
        have : ic.len.val ≤ cut.val := by scalar_tac
        omega
      · simp only [hfull, ↓reduceIte]
        have hcutlt : cut.val < ic.len.val := by scalar_tac
        have hd : ∀ (j : Nat) (y : MItem), (toKind b.kind).slot = some j →
            coreAt (toM s).items j = some y → 0 < cut.val ∧ cut.val < y.len := by
          intro j y hj hy
          have hjj : (toBlock b).kind.slot = some j := hj
          rw [hslot] at hjj
          cases hjj
          rw [hx'] at hy
          cases hy
          omega
        step with split_node_spec s ci pos cut h hc hb hd as ⟨r, s1, hpost⟩
        cases r with
        | Err error =>
          simp only [spec_ok, uncurry'_pair]
          exact ⟨fun _ _ => hpost.err error rfl, (fun h => nomatch h), (fun _ h => nomatch h)⟩
        | Ok p =>
          obtain ⟨l, rt⟩ := p
          obtain ⟨hl, hrt, hm⟩ := hpost.ok l rt rfl
          show spec (ok _) _
          simp only [spec_ok, uncurry'_pair]
          refine ⟨(fun _ h => nomatch h), (fun h => nomatch h), fun j hj => ?_⟩
          cases hj
          rw [hk] at hl
          cases hl
          rw [hm, hcutv]
          refine splitAfterOk_split h hat (toM_clients_at hc) hslot hx' ?_
          show id.clock.val - b.clock.val + 1 < x.len
          omega

/-! ## The conflict scan -/

def toStep : yata_store.ScanStep → MStep
  | .Stop => MStep.stop
  | .Skip => MStep.skip
  | .Take => MStep.take

/-- One step of the scan is `scanStep` of the model. -/
@[step]
theorem scan_step_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore)
    (ol or_ : Option yata_store.IdCore) (cand : yata_store.ItemCore)
    (before conflicting : Slice yata_store.IdCore) (h : Inv s) :
    yata_store.YataStoreCore.scan_step s id ol or_ cand before conflicting ⦃ r =>
      toStep r = scanStep (ownerM (toM s)) (toId id) (ol.map toId) (or_.map toId) (toItem cand)
        (before.val.map toId) (conflicting.val.map toId) ⦄ := by
  unfold yata_store.YataStoreCore.scan_step
  step as ⟨b, hb⟩
  by_cases hbt : b = true
  · simp only [hbt, ↓reduceIte]
    have h1 : ol.map toId = (toItem cand).originL := hb.mp hbt
    by_cases hlt : cand.id.client < id.client
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hlt' : (toItem cand).id.client < (toId id).client := by
        show cand.id.client.val < id.client.val
        scalar_tac
      rw [scanStep_same_take h1 hlt']
      rfl
    · simp only [hlt, ↓reduceIte]
      have hlt' : ¬ (toItem cand).id.client < (toId id).client := by
        show ¬ cand.id.client.val < id.client.val
        scalar_tac
      step as ⟨b1, hb1⟩
      by_cases hb1t : b1 = true
      · simp only [hb1t, ↓reduceIte, spec_ok]
        have h3 : or_.map toId = (toItem cand).originR := hb1.mp hb1t
        rw [scanStep_same_stop h1 hlt' h3]
        rfl
      · simp only [hb1t, Bool.false_eq_true, ↓reduceIte, spec_ok]
        have h3 : ¬ or_.map toId = (toItem cand).originR := fun e => hb1t (hb1.mpr e)
        rw [scanStep_same_skip h1 hlt' h3]
        rfl
  · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
    have h1 : ¬ ol.map toId = (toItem cand).originL := fun e => hbt (hb.mpr e)
    cases hcl : cand.origin_left with
    | none =>
      simp only [spec_ok]
      have h2 : (toItem cand).originL = none := by
        show cand.origin_left.map toId = none
        rw [hcl]
        rfl
      rw [scanStep_none h1 h2]
      rfl
    | some origin =>
      simp only []
      have h2 : (toItem cand).originL = some (toId origin) := by
        show cand.origin_left.map toId = some (toId origin)
        rw [hcl]
        rfl
      step with node_id_spec s origin h as ⟨o, ho⟩
      cases o with
      | none =>
        simp only [spec_ok]
        rw [scanStep_owner_none h1 h2 ho.symm]
        rfl
      | some owner =>
        have h3 : ownerM (toM s) (toId origin) = some (toId owner) := ho.symm
        simp only []
        step as ⟨b1, hb1⟩
        by_cases hb1t : b1 = true
        · simp only [hb1t, ↓reduceIte]
          step as ⟨b2, hb2⟩
          by_cases hb2t : b2 = true
          · simp only [hb2t, ↓reduceIte, spec_ok]
            rw [scanStep_owner_skip h1 h2 h3 (hb1.mp hb1t) (hb2.mp hb2t)]
            rfl
          · simp only [hb2t, Bool.false_eq_true, ↓reduceIte, spec_ok]
            rw [scanStep_owner_take h1 h2 h3 (hb1.mp hb1t) (fun e => hb2t (hb2.mpr e))]
            rfl
        · simp only [hb1t, Bool.false_eq_true, ↓reduceIte, spec_ok]
          rw [scanStep_owner_far h1 h2 h3 (fun e => hb1t (hb1.mpr e))]
          rfl

theorem mem_push_ids {B : List YoctoSpec.Id} {l l1 : List yata_store.IdCore}
    {x : yata_store.IdCore} (hB : ∀ z, z ∈ B ↔ z ∈ l.map toId) (hl : l1 = l ++ [x]) :
    ∀ z, z ∈ toId x :: B ↔ z ∈ l1.map toId := by
  intro z
  rw [hl, List.map_append, List.mem_append, List.mem_cons, hB z]
  show z = toId x ∨ z ∈ l.map toId ↔ z ∈ l.map toId ∨ z ∈ [toId x]
  rw [List.mem_singleton]
  exact Or.comm

theorem order_le_items {s : yata_store.YataStoreCore} (h : Inv s) :
    (order (toM s)).length ≤ s.items.val.length := by
  have := nodup_length_le (toM s).items.length (order (toM s)) h.chain.nodup h.chain.bound
  rw [toM_items_length] at this
  exact this

theorem order_bound {s : yata_store.YataStoreCore} (h : Inv s) {i : Nat}
    (hi : i ∈ order (toM s)) : i < s.items.val.length := by
  have := h.chain.bound i hi
  rw [toM_items_length] at this
  exact this

theorem rightOf_toM {s : yata_store.YataStoreCore} {i : Nat} {item : yata_store.ItemCore}
    (h : s.items.val[i]? = some item) : rightOf (toM s).items i = toSlot item.right := by
  simp [rightOf, toM_items_get?, h, toItem]

theorem leftOf_toM {s : yata_store.YataStoreCore} {i : Nat} {item : yata_store.ItemCore}
    (h : s.items.val[i]? = some item) : leftOf (toM s).items i = toSlot item.left := by
  simp [leftOf, toM_items_get?, h, toItem]

/-- The loop of the scan is `scanLoop` of the model, with any fuel that
covers the rest of the sequence. -/
theorem find_conflict_left_loop_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore)
    (ol or_ : Option yata_store.IdCore) (right conflict left : Option Std.U32)
    (conflicting before : alloc.vec.Vec yata_store.IdCore) (h : Inv s)
    (k : Nat) (B C : List YoctoSpec.Id) (fuel : Nat)
    (hk : k ≤ (order (toM s)).length) (hcur : toSlot conflict = (order (toM s))[k]?)
    (hB : ∀ z, z ∈ B ↔ z ∈ before.val.map toId)
    (hC : ∀ z, z ∈ C ↔ z ∈ conflicting.val.map toId)
    (hbl : before.val.length ≤ k) (hcl : conflicting.val.length ≤ k)
    (hfuel : (order (toM s)).length - k ≤ fuel) :
    yata_store.YataStoreCore.find_conflict_left_loop conflict s id ol or_ right left conflicting
        before ⦃ r =>
      toSlot r = scanLoop (toM s).items (ownerM (toM s)) (toId id) (ol.map toId) (or_.map toId)
        (toSlot right) fuel (toSlot left) (toSlot conflict) B C ⦄ := by
  obtain ⟨R, hR⟩ : ∃ R, scanLoop (toM s).items (ownerM (toM s)) (toId id) (ol.map toId)
      (or_.map toId) (toSlot right) fuel (toSlot left) (toSlot conflict) B C = R := ⟨_, rfl⟩
  rw [hR]
  unfold yata_store.YataStoreCore.find_conflict_left_loop
  refine loop.spec_decr_nat
    (fun ((_, _, _, bv) : Option Std.U32 × Option Std.U32 × alloc.vec.Vec yata_store.IdCore ×
      alloc.vec.Vec yata_store.IdCore) => Std.Usize.max - bv.val.length)
    (fun ((cf, lf, cv, bv) : Option Std.U32 × Option Std.U32 ×
      alloc.vec.Vec yata_store.IdCore × alloc.vec.Vec yata_store.IdCore) =>
      ∃ (k' : Nat) (B' C' : List YoctoSpec.Id) (fuel' : Nat),
        k' ≤ (order (toM s)).length ∧ toSlot cf = (order (toM s))[k']? ∧
        (∀ z, z ∈ B' ↔ z ∈ bv.val.map toId) ∧ (∀ z, z ∈ C' ↔ z ∈ cv.val.map toId) ∧
        bv.val.length ≤ k' ∧ cv.val.length ≤ k' ∧ (order (toM s)).length - k' ≤ fuel' ∧
        scanLoop (toM s).items (ownerM (toM s)) (toId id) (ol.map toId) (or_.map toId)
          (toSlot right) fuel' (toSlot lf) (toSlot cf) B' C' = R)
    (fun (r : Option Std.U32) => toSlot r = R)
    _ (conflict, left, conflicting, before) ?_ ⟨k, B, C, fuel, hk, hcur, hB, hC, hbl, hcl, hfuel, hR⟩
  intro ⟨cf, lf, cv, bv⟩ ⟨k', B', C', fuel', hk', hcur', hB', hC', hbl', hcl', hfuel', hinv⟩
  unfold yata_store.YataStoreCore.find_conflict_left_loop.body
  simp only
  cases cf with
  | none =>
    simp only [spec_ok]
    rw [← hinv]
    exact (scanLoop_stop _ _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)).symm
  | some current =>
    simp only []
    have hcur'' : (order (toM s))[k']? = some current.val := hcur'.symm
    have hklt : k' < (order (toM s)).length := get?_lt hcur''
    have hmem : current.val ∈ order (toM s) := get?_mem hcur''
    have hcb : current.val < s.items.val.length := order_bound h hmem
    have hol := order_le_items h
    step as ⟨b, hb⟩
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte, spec_ok]
      rw [← hinv]
      exact (scanLoop_stop _ _ _ _ _ _ _ _ _ _ _ (Or.inr (hb.mp hbt))).symm
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
      have hne : ¬ toSlot right = some current.val := fun e => hbt (hb.mpr e)
      step as ⟨i, hi⟩
      have hiv : i.val = current.val := by scalar_tac
      have hilt : i.val < s.items.val.length := by omega
      step as ⟨cand, hcand⟩
      have hit := get?_of_getElem hilt hcand
      rw [hiv] at hit
      have hbv : bv.val.length < Std.Usize.max := by scalar_tac
      have hcv : cv.val.length < Std.Usize.max := by scalar_tac
      step as ⟨bv1, hbv1⟩
      step as ⟨cv1, hcv1⟩
      have hB1 := mem_push_ids hB' hbv1
      have hC1 := mem_push_ids hC' hcv1
      have hd1 : (alloc.vec.Vec.deref bv1).val = bv1.val := by
        simp [alloc.vec.Vec.deref]
      have hd2 : (alloc.vec.Vec.deref cv1).val = cv1.val := by
        simp [alloc.vec.Vec.deref]
      step with scan_step_spec s id ol or_ cand (alloc.vec.Vec.deref bv1)
        (alloc.vec.Vec.deref cv1) h as ⟨ss, hss⟩
      rw [hd1, hd2] at hss
      have hstep : toStep ss = scanStep (ownerM (toM s)) (toId id) (ol.map toId) (or_.map toId)
          (toItem cand) (toId cand.id :: B') (toId cand.id :: C') := by
        rw [hss]
        exact (scanStep_congr hB1 hC1).symm
      obtain ⟨fuel'', hfe⟩ : ∃ f'' : Nat, fuel' = f'' + 1 := ⟨fuel' - 1, by omega⟩
      have hinv' : (match toStep ss with
          | MStep.stop => toSlot lf
          | MStep.skip =>
            scanLoop (toM s).items (ownerM (toM s)) (toId id) (ol.map toId) (or_.map toId)
              (toSlot right) fuel'' (toSlot lf) (toSlot cand.right) (toId cand.id :: B')
              (toId cand.id :: C')
          | MStep.take =>
            scanLoop (toM s).items (ownerM (toM s)) (toId id) (ol.map toId) (or_.map toId)
              (toSlot right) fuel'' (some current.val) (toSlot cand.right) (toId cand.id :: B')
              []) = R := by
        rw [← hinv, hfe]
        show _ = scanLoop (toM s).items (ownerM (toM s)) (toId id) (ol.map toId) (or_.map toId)
          (toSlot right) (fuel'' + 1) (toSlot lf) (some current.val) B' C'
        rw [scanLoop_succ, itemAt_toM hit, hstep]
        simp only [hne, ↓reduceIte]
        rfl
      have hnext : toSlot cand.right = (order (toM s))[k' + 1]? := by
        rw [← rightOf_toM hit]
        exact h.chain.right k' _ hcur''
      have hbl1 : bv1.val.length ≤ k' + 1 := by
        rw [hbv1, List.length_append, List.length_singleton]
        omega
      have hmeas : Std.Usize.max - bv1.val.length < Std.Usize.max - bv.val.length := by
        rw [hbv1, List.length_append, List.length_singleton]
        omega
      cases ss with
      | Stop =>
        simp only [spec_ok]
        exact hinv'
      | Skip =>
        simp only [spec_ok]
        have hcl1 : cv1.val.length ≤ k' + 1 := by
          rw [hcv1, List.length_append, List.length_singleton]
          omega
        exact ⟨⟨k' + 1, toId cand.id :: B', toId cand.id :: C', fuel'', by omega, hnext, hB1,
          hC1, hbl1, hcl1, by omega, hinv'⟩, hmeas⟩
      | Take =>
        simp only [spec_ok]
        refine ⟨⟨k' + 1, toId cand.id :: B', [], fuel'', by omega, hnext, hB1, ?_, hbl1, ?_,
          by omega, hinv'⟩, hmeas⟩
        · intro z
          simp
        · simp

/-- Whether the scan has to look at anything: `needsScan` of the model. -/
theorem needs_scan_spec (s : yata_store.YataStoreCore) (left right : Option Std.U32)
    (hl : ∀ i, left = some i → i.val < s.items.val.length)
    (hr : ∀ i, right = some i → i.val < s.items.val.length) :
    yata_store.YataStoreCore.needs_scan s left right ⦃ b =>
      b = needsScan (toM s) (toSlot left) (toSlot right) ⦄ := by
  unfold yata_store.YataStoreCore.needs_scan
  cases left with
  | none =>
    cases right with
    | none => simp [spec_ok, needsScan, toSlot]
    | some idx =>
      have hlt := hr idx rfl
      simp only []
      step as ⟨i, hi⟩
      have hiv : i.val = idx.val := by scalar_tac
      have hilt : i.val < s.items.val.length := by omega
      step as ⟨ic, hic⟩
      have hit := get?_of_getElem hilt hic
      rw [hiv] at hit
      have hlo := leftOf_toM hit
      cases hleft : ic.left with
      | none =>
        simp only [spec_ok]
        show false = (leftOf (toM s).items idx.val).isSome
        rw [hlo, hleft]
        rfl
      | some j =>
        simp only [spec_ok]
        show true = (leftOf (toM s).items idx.val).isSome
        rw [hlo, hleft]
        rfl
  | some idx =>
    have hlt := hl idx rfl
    simp only []
    step as ⟨i, hi⟩
    have hiv : i.val = idx.val := by scalar_tac
    have hilt : i.val < s.items.val.length := by omega
    step as ⟨ic, hic⟩
    have hit := get?_of_getElem hilt hic
    rw [hiv] at hit
    have hro := rightOf_toM hit
    step as ⟨b, hb⟩
    show _ = decide (rightOf (toM s).items idx.val ≠ toSlot right)
    rw [hro]
    by_cases e : toSlot ic.right = toSlot right
    · have hbt : b = true := hb.mpr e
      simp [hbt, e]
    · have hbf : b = false := by
        cases hbb : b with
        | false => rfl
        | true => exact absurd (hb.mp hbb) e
      simp [hbf, e]

/-- The left neighbour `integrate` links after: `scanM` of the model. -/
theorem conflict_left_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore)
    (ol or_ : Option yata_store.IdCore) (left right : Option Std.U32) (h : Inv s) {k : Nat}
    (hk : k ≤ (order (toM s)).length) (hleft : toSlot left = prevAt (order (toM s)) k)
    (hrmem : ∀ r, toSlot right = some r → r ∈ order (toM s)) :
    yata_store.YataStoreCore.conflict_left s id ol or_ left right ⦃ r =>
      toSlot r = scanM (toM s) (toId id) (ol.map toId) (or_.map toId) (toSlot left)
        (toSlot right) ⦄ := by
  unfold yata_store.YataStoreCore.conflict_left
  have hlb : ∀ i, left = some i → i.val < s.items.val.length := by
    intro i hi
    rw [hi] at hleft
    cases k with
    | zero => cases hleft
    | succ j => exact order_bound h (get?_mem hleft.symm)
  have hrb : ∀ i, right = some i → i.val < s.items.val.length := by
    intro i hi
    exact order_bound h (hrmem i.val (by rw [hi]; rfl))
  step with needs_scan_spec s left right hlb hrb as ⟨b, hb⟩
  by_cases hbt : b = true
  · simp only [hbt, ↓reduceIte]
    step with next_of_spec s left hlb as ⟨o, ho⟩
    have hcur : toSlot o = (order (toM s))[k]? := by
      rw [ho, hleft]
      exact h.chain.nextOf_prevAt hk
    have hol := order_le_items h
    unfold yata_store.YataStoreCore.find_conflict_left
    refine spec_mono (find_conflict_left_loop_spec s id ol or_ right o left
      (alloc.vec.Vec.new yata_store.IdCore) (alloc.vec.Vec.new yata_store.IdCore) h k [] []
      (toM s).items.length hk hcur (by intro z; simp) (by intro z; simp) (by simp) (by simp)
      (by rw [toM_items_length]; omega)) ?_
    intro r hr
    rw [hr]
    unfold scanM
    rw [← hb, hbt, ← ho]
    simp
  · simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
    unfold scanM
    rw [← hb]
    simp [hbt]

/-! ## `check_append`, `ensure_client`, `repair` -/

@[step]
theorem check_append_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore)
    (len : Std.U64) : yata_store.YataStoreCore.check_append s id len ⦃ _ => True ⦄ := by
  unfold yata_store.YataStoreCore.check_append
  have hMax : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
  have hle : id.clock.val ≤ (core.num.U64.MAX : Std.U64).val := by
    rw [hMax]
    scalar_tac
  have tail : ∀ cont : Bool,
      (if cont = true then do
          let i ← core.num.U64.MAX - id.clock
          if len > i then ok (core.result.Result.Err client_blocks.StoreError.ClockOverflow)
          else ok (core.result.Result.Ok ())
        else ok (core.result.Result.Err client_blocks.StoreError.ClockMismatch)) ⦃ _ => True ⦄ := by
    intro cont
    by_cases hc : cont = true
    · simp only [hc, ↓reduceIte]
      step as ⟨i, hi⟩
      split_ifs <;> simp [spec_ok]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, spec_ok]
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, _⟩ | ⟨ci, c, rfl, hc, _⟩
  · have hinner0 : (ok true : Result Bool) ⦃ _ => True ⦄ := by simp [spec_ok]
    exact spec_bind hinner0 (fun cont _ => tail cont)
  · have hlt := get?_lt hc
    have hinner :
        (do
          let cec ← alloc.vec.Vec.index_usize s.clients ci
          client_blocks.ClientBlocksCore.continues cec.blocks id.clock) ⦃ _ => True ⦄ := by
      step as ⟨cec, hcec⟩
      exact spec_mono (ClientBlocks.continues_spec _ _) (fun _ _ => trivial)
    exact spec_bind hinner (fun cont _ => tail cont)

structure EnsurePost (s : yata_store.YataStoreCore) (client : Std.U64)
    (r : core.result.Result Std.Usize client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → s' = s
  done : ∀ ci, r = core.result.Result.Ok ci →
    ∃ c, s'.clients.val[ci.val]? = some c ∧ c.client = client ∧ s'.items = s.items ∧
      s'.start = s.start ∧ Inv s' ∧ order (toM s') = order (toM s) ∧
      (toM s').items = (toM s).items
  /-- it accepts while there is room for a timeline -/
  accepts : s.clients.val.length < 4294967295 → ∃ ci, r = core.result.Result.Ok ci
  /-- the timeline it answers is one the store had, or a new empty one -/
  fresh : ∀ ci c, r = core.result.Result.Ok ci → s'.clients.val[ci.val]? = some c →
    s' = s ∨ (c.blocks.blocks.val = [] ∧ s'.clients.val = s.clients.val ++ [c])

/-- `ensure_client` finds the timeline of a client, or adds an empty one. -/
theorem ensure_client_spec (s : yata_store.YataStoreCore) (client : Std.U64) (h : Inv s) :
    yata_store.YataStoreCore.ensure_client s client ⦃ r s' => EnsurePost s client r s' ⦄ := by
  unfold yata_store.YataStoreCore.ensure_client
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hno⟩ | ⟨ci, c, rfl, hc, hcl⟩
  · simp only []
    by_cases hcap : alloc.vec.Vec.len s.clients >= yata_store.MAX_ITEMS
    · have hfull : ¬ s.clients.val.length < 4294967295 := by
        intro hlt
        simp [yata_store.MAX_ITEMS] at hcap
        scalar_tac
      simp only [hcap, ↓reduceIte, spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => rfl, (fun _ hh => nomatch hh), fun hlt => absurd hlt hfull,
        (fun _ _ hh => nomatch hh)⟩
    · simp only [hcap, ↓reduceIte]
      have hcap' : s.clients.val.length < Std.Usize.max := by
        simp [yata_store.MAX_ITEMS] at hcap
        scalar_tac
      step as ⟨cbc, hcbc1, hcbc2, hcbc3⟩
      step as ⟨v, hv⟩
      refine ⟨(fun _ hh => nomatch hh), fun ci hci => ?_, fun _ => ⟨_, rfl⟩,
        fun ci c hci hc => ?_⟩
      swap
      · cases hci
        right
        have hc' : v.val[(alloc.vec.Vec.len s.clients).val]? = some c := hc
        rw [hv] at hc'
        simp at hc'
        rw [← hc']
        exact ⟨hcbc1, hv⟩
      cases hci
      have hm : toM ({ s with clients := v }) = pushClient (toM s) client.val := by
        unfold toM pushClient
        simp [hv, toClient, toBlocks, hcbc1, hcbc2]
      have hnew : ∀ c : MClient, c ∈ (toM s).clients → c.client ≠ client.val := by
        intro c' hc' e
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc'
        obtain ⟨j, hj⟩ := mem_get? hc0
        exact hno j c0 hj (UScalar.eq_of_val_eq e)
      obtain ⟨hw, ho⟩ := pushClient_spec h hnew
      refine ⟨{ client := client, blocks := cbc }, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
      · show v.val[(alloc.vec.Vec.len s.clients).val]? = some _
        rw [hv]
        simp
      · unfold Inv
        rw [hm]
        exact hw
      · rw [hm]
        exact ho
  · simp only [spec_ok, uncurry'_pair]
    refine ⟨(fun _ hh => nomatch hh), fun j hj => ?_, fun _ => ⟨_, rfl⟩,
      fun _ _ _ _ => Or.inl rfl⟩
    cases hj
    exact ⟨c, hc, hcl, rfl, rfl, h, rfl, rfl⟩

structure RepairPost (s : yata_store.YataStoreCore) (origin : Option yata_store.IdCore)
    (P : MStore → YoctoSpec.Id → MStore → Nat → Prop)
    (r : core.result.Result (Option Std.U32 × Option yata_store.IdCore)
      client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e → s' = s
  done : ∀ slot o, r = core.result.Result.Ok (slot, o) → o = origin ∧
    ((origin = none ∧ slot = none ∧ s' = s) ∨
      ∃ l i, origin = some l ∧ slot = some i ∧ P (toM s) (toId l) (toM s') i.val)

/-- `repair` for the left origin: the block that ends at the origin. -/
theorem repair_left_spec (s : yata_store.YataStoreCore) (origin : Option yata_store.IdCore)
    (h : Inv s) :
    yata_store.YataStoreCore.repair_left s origin ⦃ r s' =>
      RepairPost s origin SplitAfterOk r s' ⦄ := by
  unfold yata_store.YataStoreCore.repair_left
  cases origin with
  | none =>
    simp only [spec_ok, uncurry'_pair]
    refine ⟨(fun _ hh => nomatch hh), fun slot o hEq => ?_⟩
    cases hEq
    exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | some l =>
    simp only []
    step with split_after_spec s l h as ⟨r, s1, hpost⟩
    cases r with
    | Err e =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => hpost.err e rfl, (fun _ _ hh => nomatch hh)⟩
    | Ok slot =>
      cases slot with
      | none => exact absurd rfl hpost.gone
      | some idx =>
        have hok := hpost.found idx rfl
        obtain ⟨y, c0, p0, b0, hy, ha0, hyc, hyk, hyend⟩ := hok.ends
        have hidx : idx.val < s1.items.val.length := order_bound hok.wf hok.mem
        simp only []
        step as ⟨i, hi⟩
        have hiv : i.val = idx.val := by scalar_tac
        have hilt : i.val < s1.items.val.length := by omega
        step as ⟨item, hitem⟩
        have hit := get?_of_getElem hilt hitem
        rw [hiv] at hit
        have hyitem : y = (toItem item).core := by
          rw [coreAt_toM hit] at hy
          exact (Option.some.inj hy).symm
        have hcl : item.id.client.val = l.client.val := by
          have := hyc
          rw [hyitem] at this
          exact this
        have hck : item.id.clock.val + item.len.val = l.clock.val + 1 := by
          have := hyend
          rw [hyitem] at this
          exact this
        have hkb : item.id.clock.val = b0.clock := by
          have := hyk
          rw [hyitem] at this
          exact this
        have hge0 : b0.clock ≤ l.clock.val := ha0.ge
        step as ⟨i1, hi1⟩
        step as ⟨i2, hi2⟩
        refine ⟨(fun _ hh => nomatch hh), fun slot o hEq => ?_⟩
        cases hEq
        have e : ({ item.id with clock := i2 } : yata_store.IdCore) = l := by
          apply toId_inj
          show (⟨item.id.client.val, i2.val⟩ : YoctoSpec.Id) = ⟨l.client.val, l.clock.val⟩
          have hi2v : i2.val = l.clock.val := by scalar_tac
          rw [hcl, hi2v]
        rw [e]
        exact ⟨rfl, Or.inr ⟨l, idx, rfl, rfl, hok⟩⟩

/-- `repair` for the right origin: the block that starts at the origin. -/
theorem repair_right_spec (s : yata_store.YataStoreCore) (origin : Option yata_store.IdCore)
    (h : Inv s) :
    yata_store.YataStoreCore.repair_right s origin ⦃ r s' =>
      RepairPost s origin SplitOk r s' ⦄ := by
  unfold yata_store.YataStoreCore.repair_right
  cases origin with
  | none =>
    simp only [spec_ok, uncurry'_pair]
    refine ⟨(fun _ hh => nomatch hh), fun slot o hEq => ?_⟩
    cases hEq
    exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | some l =>
    simp only []
    step with split_spec s l h as ⟨r, s1, hpost⟩
    cases r with
    | Err e =>
      simp only [spec_ok, uncurry'_pair]
      exact ⟨fun _ _ => hpost.err e rfl, (fun _ _ hh => nomatch hh)⟩
    | Ok slot =>
      cases slot with
      | none => exact absurd rfl hpost.gone
      | some idx =>
        have hok := hpost.found idx rfl
        obtain ⟨y, hy, hyid⟩ := hok.starts
        have hidx : idx.val < s1.items.val.length := order_bound hok.wf hok.mem
        simp only []
        step as ⟨i, hi⟩
        have hiv : i.val = idx.val := by scalar_tac
        have hilt : i.val < s1.items.val.length := by omega
        step as ⟨ic, hic⟩
        have hit := get?_of_getElem hilt hic
        rw [hiv] at hit
        have hyic : y = (toItem ic).core := by
          rw [coreAt_toM hit] at hy
          exact (Option.some.inj hy).symm
        have e : ic.id = l := by
          apply toId_inj
          have := hyid
          rw [hyic] at this
          exact this
        refine ⟨(fun _ hh => nomatch hh), fun slot o hEq => ?_⟩
        cases hEq
        rw [e]
        exact ⟨rfl, Or.inr ⟨l, idx, rfl, rfl, hok⟩⟩

/-! ## `link` and `integrate` -/

/-- The model of the item `integrate` adds. -/
def newItem (id : yata_store.IdCore) (len : Std.U64) (ol or_ : Option yata_store.IdCore) :
    MItem :=
  { id := toId id
    len := len.val
    originL := ol.map toId
    originR := or_.map toId
    left := none
    right := none
    deleted := false
    gc := false }

/-- The store `link` builds is `linkNew` of the model. -/
theorem toM_link {s1 : yata_store.YataStoreCore} {ci : Std.Usize}
    {c : yata_store.ClientEntryCore} {idx : Std.U32} {id : yata_store.IdCore} {len : Std.U64}
    {ol or_ : Option yata_store.IdCore} {left next : Option Std.U32}
    {cbc : client_blocks.ClientBlocksCore} {v : alloc.vec.Vec yata_store.ItemCore}
    (hc : s1.clients.val[ci.val]? = some c) (hidx : idx.val = s1.items.val.length)
    (hnext : toSlot next = nextOf (toM s1).items (toM s1).start (toSlot left))
    (hbl : cbc.blocks.val = c.blocks.blocks.val ++
      [({ clock := id.clock, kind := client_blocks.BlockKindCore.Item idx } :
        client_blocks.BlockRefCore)])
    (hend : cbc.end_clock.val = id.clock.val + len.val)
    (hv : v.val = s1.items.val ++
      [({ id := id, len := len, origin_left := ol, origin_right := or_, left := left,
          right := next, deleted := false, gc := false } : yata_store.ItemCore)]) :
    (MStore.mk
      (setLeft idx.val (toSlot next) (setRight idx.val (toSlot left) (v.val.map toItem)))
      (startAfter (toSlot left) idx.val (toSlot s1.start))
      ((s1.clients.set ci { c with blocks := cbc }).val.map toClient)) =
      linkNew (toM s1) ci.val (toSlot left) (newItem id len ol or_) := by
  unfold linkNew linkItems
  rw [MStore.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv, List.map_append, List.map_cons, List.map_nil, ← hnext, toM_items_length,
      ← hidx]
    rfl
  · cases left with
    | none =>
      show some idx.val = some (toM s1).items.length
      rw [toM_items_length, hidx]
    | some l => rfl
  · rw [alloc.vec.Vec.set_val_eq]
    refine map_set_get toClient hc _ _ ?_
    simp [toClient, MClient.appended, toBlocks, hbl, hend, newItem, toBlock, toKind, toId,
      toM_items_length, hidx]

/-- There is room for a struct of `len` clocks at `id` that continues the
timeline of its client: what `integrate` checks besides the origins. -/
structure Room (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (len : Std.U64) :
    Prop where
  pos : 0 < len.val
  fits : id.clock.val + len.val ≤ Std.U64.max
  items : s.items.val.length + 3 < 4294967295
  clients : s.clients.val.length < 4294967295
  cont : ∀ c, c ∈ s.clients.val → c.client = id.client →
    (c.blocks.blocks.val = [] ∨ id.clock = c.blocks.end_clock) ∧
      c.blocks.blocks.val.length < 4294967295

/-- A struct was accepted: the store has one more item, at most one more
timeline, and every new or changed timeline is the one of the struct. -/
structure RootPost (s : yata_store.YataStoreCore) (id : yata_store.IdCore)
    (r : core.result.Result Std.U32 client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  ok : ∃ idx, r = core.result.Result.Ok idx
  items : s'.items.val.length = s.items.val.length + 1
  clients : s'.clients.val.length ≤ s.clients.val.length + 1
  owner : ∀ c, c ∈ s'.clients.val → c.client = id.client ∨ c ∈ s.clients.val

structure LinkPost (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (len : Std.U64)
    (ol or_ : Option yata_store.IdCore) (left : Option Std.U32)
    (r : core.result.Result Std.U32 client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  err : ∀ e, r = core.result.Result.Err e →
    Inv s' ∧ order (toM s') = order (toM s) ∧ (toM s').items = (toM s).items
  done : ∀ idx, r = core.result.Result.Ok idx →
    ∃ (ci : Nat) (c : MClient) (m : MStore), YataModel.WF m ∧ order m = order (toM s) ∧
      m.items = (toM s).items ∧ m.clients[ci]? = some c ∧ c.client = id.client.val ∧
      (c.blocks = [] ∨ c.stop = id.clock.val) ∧ 0 < len.val ∧
      toM s' = linkNew m ci (toSlot left) (newItem id len ol or_)
  /-- `link` accepts when there is room -/
  room : Room s id len → RootPost s id r s'

/-- `link` appends the block to the timeline of its client and links the
item after `left`: `linkNew` of the model. -/
theorem link_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (len : Std.U64)
    (ol or_ : Option yata_store.IdCore) (left : Option Std.U32) (h : Inv s) {k : Nat}
    (hk : k ≤ (order (toM s)).length) (hleft : toSlot left = prevAt (order (toM s)) k) :
    yata_store.YataStoreCore.link s id len ol or_ left ⦃ r s' =>
      LinkPost s id len ol or_ left r s' ⦄ := by
  unfold yata_store.YataStoreCore.link
  have same : ∀ e, ¬ Room s id len → LinkPost s id len ol or_ left (core.result.Result.Err e) s :=
    fun e hno => ⟨fun _ _ => ⟨h, rfl, rfl⟩, (fun _ hh => nomatch hh), fun hr => absurd hr hno⟩
  have hlb : ∀ i, left = some i → i.val < s.items.val.length := by
    intro i hi
    rw [hi] at hleft
    cases k with
    | zero => cases hleft
    | succ j => exact order_bound h (get?_mem hleft.symm)
  by_cases hcap : alloc.vec.Vec.len s.items >= yata_store.MAX_ITEMS
  · have hfull : ¬ Room s id len := by
      intro hr
      have := hr.items
      simp [yata_store.MAX_ITEMS] at hcap
      scalar_tac
    simp only [hcap, ↓reduceIte, spec_ok, uncurry'_pair]
    exact same _ hfull
  · simp only [hcap, ↓reduceIte]
    have hcap' : s.items.val.length < 4294967295 := by
      simp [yata_store.MAX_ITEMS] at hcap
      scalar_tac
    step with next_of_spec s left hlb as ⟨next, hnext⟩
    have hnb : ∀ i, next = some i → i.val < s.items.val.length := by
      intro i hi
      rw [hi, hleft, h.chain.nextOf_prevAt hk] at hnext
      exact order_bound h (get?_mem hnext.symm)
    step with ensure_client_spec s id.client h as ⟨r, s1, hens⟩
    cases r with
    | Err e =>
      simp only [spec_ok, uncurry'_pair]
      rw [hens.err e rfl]
      refine same _ (fun hr => ?_)
      obtain ⟨ci, hci⟩ := hens.accepts hr.clients
      cases hci
    | Ok ci =>
      obtain ⟨c, hc, hcl, hitems, hstart, hinv1, hord1, hmi⟩ := hens.done ci rfl
      have hfresh := hens.fresh ci c rfl hc
      have hroom : Room s id len →
          (c.blocks.blocks.val = [] ∨ id.clock = c.blocks.end_clock) ∧
            c.blocks.blocks.val.length < 4294967295 := by
        intro hr
        rcases hfresh with e | ⟨he, _⟩
        · rw [e] at hc
          exact hr.cont c (get?_mem hc) hcl
        · rw [he]
          exact ⟨Or.inl rfl, by decide⟩
      simp only []
      have hs1len : s1.items.val.length = s.items.val.length := by rw [hitems]
      have hu32 : (alloc.vec.Vec.len s1.items).val ≤ UScalar.max UScalarTy.U32 := by
        scalar_tac
      step with UScalar.cast_inBounds_spec UScalarTy.U32 (alloc.vec.Vec.len s1.items) hu32
        as ⟨idx, hidx⟩
      have hidxv : idx.val = s1.items.val.length := by
        rw [hidx]
        simp
      have hclt := get?_lt hc
      step as ⟨cec, back, hcec, hback⟩
      have hc1 := get?_of_getElem hclt hcec
      rw [hc] at hc1
      cases hc1
      subst hback
      step as ⟨r1, cbc, hpost⟩
      cases r1 with
      | Err e =>
        have hcb := hpost.err e rfl
        subst hcb
        simp only [spec_ok, uncurry'_pair]
        have e1 : s1.clients.set ci { c with blocks := c.blocks } = s1.clients := by
          apply alloc.vec.Vec.ext
          rw [alloc.vec.Vec.set_val_eq]
          exact set_eq_self hc
        show LinkPost s id len ol or_ left (core.result.Result.Err e)
          ({ s1 with clients := s1.clients.set ci { c with blocks := c.blocks } })
        rw [e1]
        refine ⟨fun _ _ => ⟨hinv1, hord1, hmi⟩, (fun _ hh => nomatch hh), fun hr => ?_⟩
        obtain ⟨h1, h2⟩ := hroom hr
        have hok := hpost.accepts hr.pos h1 hr.fits h2
        cases hok
      | Ok u =>
        obtain ⟨hpos, hcont, hbl, hend⟩ := hpost.ok rfl
        simp only []
        step as ⟨v, hv⟩
        have hvlen : v.val.length = s.items.val.length + 1 := by
          rw [hv, List.length_append, List.length_singleton, hs1len]
        have hpre1 : ∀ i, left = some i →
            i.val < ({ s1 with items := v, clients := s1.clients.set ci { c with blocks := cbc } } :
              yata_store.YataStoreCore).items.val.length := by
          intro i hi
          have := hlb i hi
          show i.val < v.val.length
          omega
        step with set_next_spec _ left idx hpre1 as ⟨self2, hself2, hlen2, hcl2⟩
        have hpre2 : ∀ i, next = some i → i.val < self2.items.val.length := by
          intro i hi
          have := hnb i hi
          rw [hlen2]
          show i.val < v.val.length
          omega
        step with set_left_spec self2 next idx hpre2 as ⟨self3, hself3, hlen3, hcl3⟩
        refine ⟨(fun _ hh => nomatch hh), fun j hj => ?_, fun _ => ?_⟩
        swap
        · have hcls : self3.clients.val = s1.clients.val.set ci.val { c with blocks := cbc } := by
            rw [hcl3, hcl2]
            exact alloc.vec.Vec.set_val_eq _ _ _
          refine ⟨⟨idx, rfl⟩, ?_, ?_, ?_⟩
          · rw [hlen3, hlen2]
            exact hvlen
          · rw [hcls, List.length_set]
            rcases hfresh with e | ⟨_, e⟩
            · rw [e]
              exact Nat.le_succ _
            · rw [e, List.length_append]
              exact Nat.le_refl _
          · intro c' hc'
            rw [hcls] at hc'
            rcases List.mem_or_eq_of_mem_set hc' with hm | hm
            · rcases hfresh with e | ⟨_, e⟩
              · rw [e] at hm
                exact Or.inr hm
              · rw [e] at hm
                rcases List.mem_append.mp hm with hm' | hm'
                · exact Or.inr hm'
                · rw [List.mem_singleton.mp hm']
                  exact Or.inl hcl
            · rw [hm]
              exact Or.inl hcl
        cases hj
        have hst : (toM s1).start = (toM s).start := by
          show toSlot s1.start = toSlot s.start
          rw [hstart]
        refine ⟨ci.val, toClient c, toM s1, hinv1, hord1, hmi, toM_clients_at hc, ?_, ?_, hpos, ?_⟩
        · show c.client.val = id.client.val
          rw [hcl]
        · rcases hcont with e | e
          · left
            show toBlocks c.blocks = []
            simp [toBlocks, e]
          · right
            show c.blocks.end_clock.val = id.clock.val
            rw [← e]
        · rw [hself3, hself2]
          exact toM_link hc hidxv (by rw [hmi, hst]; exact hnext) hbl hend hv

/-- The right origin is not inside the block that ends at the left origin.
An item is created between its origins, so in a run of the network it never
is (`YataModel.sep_of_canIntegrate`, from `YoctoSpec.CanIntegrate`). -/
def Sep (m : MStore) (ol or_ : Option YoctoSpec.Id) : Prop :=
  ∀ (l r : YoctoSpec.Id) (c : MClient) (p : Nat) (b : MBlock), ol = some l → or_ = some r →
    At m l c p b → ¬ (r.client = l.client ∧ b.clock < r.clock ∧ r.clock ≤ l.clock)

/-- What `integrate` guarantees on every input: the invariant; when it
refuses the struct, a store that stands for the same blocks up to the splits
`repair` made; when it accepts it, `YoctoSpec.integrateBlock`. -/
structure IntegratePost (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (len : Std.U64)
    (ol or_ : Option yata_store.IdCore)
    (r : core.result.Result Std.U32 client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  inv : Inv s'
  err : ∀ e, r = core.result.Result.Err e →
    ∃ zs : List YoctoSpec.Id, ∀ f, abs f s' = zs.foldl YoctoSpec.split (abs f s)
  done : ∀ idx, r = core.result.Result.Ok idx → 0 < len.val ∧
    (Sep (toM s) (ol.map toId) (or_.map toId) →
      ∀ f, abs f s' = YoctoSpec.integrateBlock (abs f s) (blockOf f (newItem id len ol or_)))

/-- **`integrate` refines `YoctoSpec.integrateBlock`.** -/
theorem integrate_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore) (len : Std.U64)
    (ol or_ : Option yata_store.IdCore) (h : Inv s) :
    yata_store.YataStoreCore.integrate s id len ol or_ ⦃ r s' =>
      IntegratePost s id len ol or_ r s' ⦄ := by
  unfold yata_store.YataStoreCore.integrate
  have same : ∀ e, IntegratePost s id len ol or_ (core.result.Result.Err e) s :=
    fun e => ⟨h, fun _ _ => ⟨[], fun _ => rfl⟩, (fun _ hh => nomatch hh)⟩
  by_cases hz : len = 0#u64
  · have hz' : (len = 0#u64) = True := eq_true hz
    simp only [hz', ↓reduceIte, spec_ok, uncurry'_pair]
    exact same _
  · simp only [hz, ↓reduceIte]
    have hpos : 0 < len.val := by scalar_tac
    step as ⟨r0⟩
    cases r0 with
    | Err e =>
      simp only [spec_ok, uncurry'_pair]
      exact same _
    | Ok u0 =>
      simp only []
      step as ⟨r1⟩
      cases r1 with
      | Err e =>
        simp only [spec_ok, uncurry'_pair]
        exact same _
      | Ok u1 =>
        simp only []
        step as ⟨r2⟩
        cases r2 with
        | Err e =>
          simp only [spec_ok, uncurry'_pair]
          exact same _
        | Ok u2 =>
          simp only []
          have hmax3 : 3 ≤ (yata_store.MAX_ITEMS).val := by
            simp [yata_store.MAX_ITEMS]
          step as ⟨i1, hi1⟩
          by_cases hcap : alloc.vec.Vec.len s.items > i1
          · simp only [hcap, ↓reduceIte, spec_ok, uncurry'_pair]
            exact same _
          · simp only [hcap, ↓reduceIte]
            step with repair_left_spec s ol h as ⟨r3, s1, hp3⟩
            cases r3 with
            | Err e =>
              simp only [spec_ok, uncurry'_pair]
              rw [hp3.err e rfl]
              exact same _
            | Ok found =>
              obtain ⟨left, tl⟩ := found
              obtain ⟨htl, hL⟩ := hp3.done left tl rfl
              subst htl
              have hLm : ((newItem id len tl or_).originL = none ∧ toM s1 = toM s ∧
                  toSlot left = none) ∨
                  ∃ l i, (newItem id len tl or_).originL = some l ∧ toSlot left = some i ∧
                    SplitAfterOk (toM s) l (toM s1) i := by
                rcases hL with ⟨e1, e2, e3⟩ | ⟨l, i, e1, e2, ok⟩
                · left
                  refine ⟨?_, by rw [e3], by rw [e2]; rfl⟩
                  show tl.map toId = none
                  rw [e1]
                  rfl
                · right
                  refine ⟨toId l, i.val, ?_, by rw [e2]; rfl, ok⟩
                  show tl.map toId = some (toId l)
                  rw [e1]
                  rfl
              have h1 : Inv s1 := by
                rcases hLm with ⟨_, e, _⟩ | ⟨_, _, _, _, ok⟩
                · unfold Inv
                  rw [e]
                  exact h
                · exact ok.wf
              have hz1 : ∃ zs : List YoctoSpec.Id,
                  ∀ f, abs f s1 = zs.foldl YoctoSpec.split (abs f s) := by
                rcases hLm with ⟨_, e, _⟩ | ⟨l, _, _, _, ok⟩
                · exact ⟨[], fun f => by unfold abs; rw [e]; rfl⟩
                · exact ⟨[⟨l.client, l.clock + 1⟩], fun f => ok.blocks f⟩
              show spec (Bind.bind _ _) _
              step with repair_right_spec s1 or_ h1 as ⟨r4, s2, hp4⟩
              cases r4 with
              | Err e =>
                simp only [spec_ok, uncurry'_pair]
                rw [hp4.err e rfl]
                exact ⟨h1, fun _ _ => hz1, (fun _ hh => nomatch hh)⟩
              | Ok found1 =>
                obtain ⟨right, tr⟩ := found1
                obtain ⟨htr, hR⟩ := hp4.done right tr rfl
                subst htr
                have hRm : ((newItem id len tl tr).originR = none ∧ toM s2 = toM s1 ∧
                    toSlot right = none) ∨
                    ∃ r i, (newItem id len tl tr).originR = some r ∧ toSlot right = some i ∧
                      SplitOk (toM s1) r (toM s2) i := by
                  rcases hR with ⟨e1, e2, e3⟩ | ⟨l, i, e1, e2, ok⟩
                  · left
                    refine ⟨?_, by rw [e3], by rw [e2]; rfl⟩
                    show tr.map toId = none
                    rw [e1]
                    rfl
                  · right
                    refine ⟨toId l, i.val, ?_, by rw [e2]; rfl, ok⟩
                    show tr.map toId = some (toId l)
                    rw [e1]
                    rfl
                have h2 : Inv s2 := by
                  rcases hRm with ⟨_, e, _⟩ | ⟨_, _, _, _, ok⟩
                  · unfold Inv
                    rw [e]
                    exact h1
                  · exact ok.wf
                have hz2 : ∃ zs : List YoctoSpec.Id,
                    ∀ f, abs f s2 = zs.foldl YoctoSpec.split (abs f s) := by
                  obtain ⟨zs, hzs⟩ := hz1
                  rcases hRm with ⟨_, e, _⟩ | ⟨r, _, _, _, ok⟩
                  · exact ⟨zs, fun f => by rw [← hzs f]; unfold abs; rw [e]⟩
                  · refine ⟨zs ++ [r], fun f => ?_⟩
                    rw [List.foldl_append, ← hzs f]
                    exact ok.blocks f
                have hlmem : ∀ i, toSlot left = some i → i ∈ order (toM s2) := by
                  intro i hi
                  have hi1 : i ∈ order (toM s1) := by
                    rcases hLm with ⟨_, _, e⟩ | ⟨_, j, _, e, ok⟩
                    · rw [e] at hi
                      cases hi
                    · rw [e] at hi
                      cases hi
                      exact ok.mem
                  rcases hRm with ⟨_, e, _⟩ | ⟨_, _, _, _, ok⟩
                  · rw [e]
                    exact hi1
                  · exact ok.mono i hi1
                have hrmem : ∀ r, toSlot right = some r → r ∈ order (toM s2) := by
                  intro r hr
                  rcases hRm with ⟨_, _, e⟩ | ⟨_, j, _, e, ok⟩
                  · rw [e] at hr
                    cases hr
                  · rw [e] at hr
                    cases hr
                    exact ok.mem
                obtain ⟨k, hk, ek⟩ := prevAt_of_mem (toSlot left) hlmem
                show spec (Bind.bind _ _) _
                step with conflict_left_spec s2 id tl tr left right h2 hk ek hrmem
                  as ⟨left1, hleft1⟩
                obtain ⟨k', hk', ek'⟩ := scanM_pos h2 (toId id) (tl.map toId) (tr.map toId)
                  (toSlot right) hlmem
                refine spec_mono
                  (link_spec s2 id len tl tr left1 h2 hk' (hleft1.trans ek')) ?_
                rintro ⟨r5, s3⟩ hpost
                have hpost' : LinkPost s2 id len tl tr left1 r5 s3 := hpost
                show IntegratePost s id len tl tr r5 s3
                refine ⟨?_, ?_, ?_⟩
                · cases r5 with
                  | Err e => exact (hpost'.err e rfl).1
                  | Ok idx =>
                    obtain ⟨ci, c, m3, hw3, ho3, hi3, hc3, hcl3, hcont3, hlen3, hm⟩ :=
                      hpost'.done idx rfl
                    unfold Inv
                    rw [hm, hleft1, ek', ← ho3]
                    exact (linkNew_spec hw3 hc3 hcl3 hcont3 hlen3 rfl rfl
                      (by rw [ho3]; exact hk')).1
                · intro e he
                  subst he
                  obtain ⟨_, ho, hi⟩ := hpost'.err e rfl
                  obtain ⟨zs, hzs⟩ := hz2
                  refine ⟨zs, fun f => ?_⟩
                  rw [← hzs f]
                  unfold abs blocks
                  rw [ho, hi]
                · intro idx he
                  subst he
                  refine ⟨hpos, fun hsep f => ?_⟩
                  obtain ⟨ci, c, m3, hw3, ho3, hi3, hc3, hcl3, hcont3, hlen3, hm⟩ :=
                    hpost'.done idx rfl
                  have key := (integrate_compose (x := newItem id len tl tr) h hlen3 rfl rfl hLm
                    hRm hsep hw3 ho3 hi3 hc3 hcl3 hcont3).2 f
                  unfold abs
                  rw [hm, hleft1]
                  exact key

/-! ## `gc` -/

/-- `gc_item_content` on an item of the arena. -/
def collectC (x : yata_store.ItemCore) : yata_store.ItemCore :=
  if x.deleted then { x with gc := true } else x

theorem toItem_collectC (x : yata_store.ItemCore) : toItem (collectC x) = (toItem x).collect := by
  cases hd : x.deleted <;> simp [collectC, MItem.collect, toItem, hd]

theorem get?_take_map_append {α : Type} (g : α → α) (l : List α) (k : Nat) (h : k ≤ l.length) :
    ((l.take k).map g ++ l.drop k)[k]? = l[k]? := by
  have hl : ((l.take k).map g).length = k := by
    rw [List.length_map, List.length_take]
    omega
  have e := get?_append_right ((l.take k).map g) (l.drop k) 0
  rw [hl, Nat.add_zero] at e
  rw [e, get?_drop_zero]

theorem set_take_map_append {α : Type} (g : α → α) (l : List α) (k : Nat) {x : α}
    (h : l[k]? = some x) :
    ((l.take k).map g ++ l.drop k).set k (g x) = (l.take (k + 1)).map g ++ l.drop (k + 1) := by
  have hk := get?_lt h
  have hl : ((l.take k).map g).length = k := by
    rw [List.length_map, List.length_take]
    omega
  rw [drop_eq_cons_get h, take_succ_get h, List.map_append, List.append_assoc]
  have e := set_append_length ((l.take k).map g) x (g x) (l.drop (k + 1))
  rw [hl] at e
  rw [e]
  rfl

theorem gc_loop_spec (s0 s : yata_store.YataStoreCore) (i : Std.Usize)
    (hinv : i.val ≤ s0.items.val.length ∧ s.start = s0.start ∧ s.clients = s0.clients ∧
      s.items.val = (s0.items.val.take i.val).map collectC ++ s0.items.val.drop i.val) :
    yata_store.YataStoreCore.gc_loop s i ⦃ r =>
      r.1.val = s0.items.val.map collectC ∧ r.2.1 = s0.start ∧ r.2.2 = s0.clients ⦄ := by
  unfold yata_store.YataStoreCore.gc_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : yata_store.YataStoreCore × Std.Usize) => s0.items.val.length - k.val)
    (fun ((t, k) : yata_store.YataStoreCore × Std.Usize) =>
      k.val ≤ s0.items.val.length ∧ t.start = s0.start ∧ t.clients = s0.clients ∧
        t.items.val = (s0.items.val.take k.val).map collectC ++ s0.items.val.drop k.val)
    (fun (r : alloc.vec.Vec yata_store.ItemCore × Option Std.U32 ×
        alloc.vec.Vec yata_store.ClientEntryCore) =>
      r.1.val = s0.items.val.map collectC ∧ r.2.1 = s0.start ∧ r.2.2 = s0.clients)
    _ (s, i) ?_ hinv
  intro ⟨t, k⟩ ⟨hk, hst, hcl, hit⟩
  unfold yata_store.YataStoreCore.gc_loop.body
  simp only
  have hlen : t.items.val.length = s0.items.val.length := by
    have := congrArg List.length hit
    rw [List.length_append, List.length_map, List.length_take, List.length_drop] at this
    omega
  by_cases hlt : k < alloc.vec.Vec.len t.items
  · simp only [hlt, ↓reduceIte]
    have hkl : k.val < t.items.val.length := by scalar_tac
    have hkl0 : k.val < s0.items.val.length := by omega
    step as ⟨ic, hic⟩
    have hx := get?_of_getElem hkl hic
    obtain ⟨x0, hx0⟩ := get?_some hkl0
    have hicx : ic = x0 := by
      have e : t.items.val[k.val]? = some x0 := by
        rw [hit, get?_take_map_append collectC _ _ hk, hx0]
      rw [hx] at e
      exact Option.some.inj e
    subst hicx
    by_cases hd : ic.deleted = true
    · simp only [hd, ↓reduceIte]
      step as ⟨p, hp1, hp2⟩
      obtain ⟨ic1, back⟩ := p
      have h1 : ic1 = t.items.val[k.val] := hp1
      have h2 : back = t.items.set k := hp2
      have hx1 := get?_of_getElem hkl h1
      rw [hx] at hx1
      cases hx1
      subst h2
      show spec (Bind.bind (ok _) _) _
      simp only [bind_tc_ok]
      step as ⟨k1, hk1⟩
      refine ⟨by scalar_tac, hst, hcl, ?_, by scalar_tac⟩
      rw [hk1]
      have e : collectC ic = { ic with gc := true } := by simp [collectC, hd]
      show (t.items.set k { ic with gc := true }).val = _
      rw [alloc.vec.Vec.set_val_eq, hit, ← e]
      exact set_take_map_append collectC _ _ hx0
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      step as ⟨k1, hk1⟩
      refine ⟨by scalar_tac, hst, hcl, ?_, by scalar_tac⟩
      rw [hk1]
      have e : collectC ic = ic := by simp [collectC, hd]
      show t.items.val = _
      rw [hit]
      have hs := set_take_map_append collectC _ _ hx0
      rw [e] at hs
      rw [← hs]
      refine (set_eq_self ?_).symm
      rw [get?_take_map_append collectC _ _ hk, hx0]
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : s0.items.val.length ≤ k.val := by scalar_tac
    refine ⟨?_, hst, hcl⟩
    rw [hit, List.take_of_length_le hge, List.drop_eq_nil_of_le hge, List.append_nil]

/-- **`gc` refines `YoctoSpec.gcContent`.** -/
theorem gc_spec (s : yata_store.YataStoreCore) (h : Inv s) :
    yata_store.YataStoreCore.gc s ⦃ s' =>
      Inv s' ∧ ∀ f, abs f s' = YoctoSpec.gcContent (abs f s) ⦄ := by
  unfold yata_store.YataStoreCore.gc
  have hinit : (0#usize).val ≤ s.items.val.length ∧ s.start = s.start ∧ s.clients = s.clients ∧
      s.items.val = (s.items.val.take (0#usize).val).map collectC ++
        s.items.val.drop (0#usize).val := by
    refine ⟨by scalar_tac, rfl, rfl, ?_⟩
    simp
  step with gc_loop_spec s s 0#usize hinit as ⟨v, o, v1, hr1, hr2, hr3⟩
  have hm : toM { items := v, start := o, clients := v1 } = gcAll (toM s) := by
    have e1 : v.val = s.items.val.map collectC := hr1
    have e2 : o = s.start := hr2
    have e3 : v1 = s.clients := hr3
    unfold toM gcAll
    rw [e1, e2, e3, List.map_map, List.map_map]
    have : toItem ∘ collectC = MItem.collect ∘ toItem := by
      funext x
      exact toItem_collectC x
    rw [this]
  obtain ⟨hw, _, hb⟩ := gcAll_spec h
  refine ⟨?_, fun f => ?_⟩
  · unfold Inv
    rw [hm]
    exact hw
  · unfold abs
    rw [hm]
    exact hb f

/-! ## `delete_range` -/

/-- A program that starts by returning a value goes on with it. -/
theorem spec_bind_ok {α β : Type} {x : α} {f : α → Result β} {P : β → Prop}
    (h : spec (f x) P) : spec (Bind.bind (ok x) f) P := by
  rw [bind_tc_ok]
  exact h

theorem toKind_inj {a b : client_blocks.BlockKindCore} (h : toKind a = toKind b) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | (exfalso; exact MKind.noConfusion h)
    | (have e := MKind.item.inj h; rw [UScalar.eq_of_val_eq e])
    | (have e := MKind.deleted.inj h; rw [UScalar.eq_of_val_eq e])

theorem clients_of_toM {s : yata_store.YataStoreCore} {ci : Nat} {mc : MClient}
    (h : (toM s).clients[ci]? = some mc) :
    ∃ c, s.clients.val[ci]? = some c ∧ toClient c = mc := by
  rw [toM_clients_get?] at h
  cases hc : s.clients.val[ci]? with
  | none =>
    rw [hc] at h
    cases h
  | some c =>
    rw [hc] at h
    exact ⟨c, rfl, Option.some.inj h⟩

theorem block_of_toClient {c : yata_store.ClientEntryCore} {p : Nat} {mb : MBlock}
    (h : (toClient c).blocks[p]? = some mb) :
    ∃ b, c.blocks.blocks.val[p]? = some b ∧ toBlock b = mb := by
  have h' : (toBlocks c.blocks)[p]? = some mb := h
  rw [toBlocks_get?] at h'
  cases hb : c.blocks.blocks.val[p]? with
  | none =>
    rw [hb] at h'
    cases h'
  | some b =>
    rw [hb] at h'
    exact ⟨b, rfl, Option.some.inj h'⟩

theorem toM_clients_length (s : yata_store.YataStoreCore) :
    (toM s).clients.length = s.clients.val.length := by
  simp [toM]

/-- What `split_inside` does: the store stands for the same document, and no
live block of the timeline holds the clock after its first clock any more. -/
structure SplitInsidePost (s : yata_store.YataStoreCore) (ci : Std.Usize) (clock : Std.U64)
    (r : core.result.Result Unit client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  inv : Inv s'
  doc : ∀ f, YoctoSpec.toDoc (abs f s') = YoctoSpec.toDoc (abs f s)
  client : ∀ c, s.clients.val[ci.val]? = some c →
    ∃ c', s'.clients.val[ci.val]? = some c' ∧ c'.client = c.client
  cut : ∀ u, r = core.result.Result.Ok u → NoStraddle (toM s') ci.val clock.val
  keep : ∀ z, NoStraddle (toM s) ci.val z → NoStraddle (toM s') ci.val z

/-- `split_inside` makes a clock inside a live block a block boundary. -/
theorem split_inside_spec (s : yata_store.YataStoreCore) (ci : Std.Usize) (clock : Std.U64)
    (h : Inv s) {c : yata_store.ClientEntryCore} (hc : s.clients.val[ci.val]? = some c) :
    yata_store.YataStoreCore.split_inside s ci clock ⦃ r s' =>
      SplitInsidePost s ci clock r s' ⦄ := by
  unfold yata_store.YataStoreCore.split_inside
  have hcm := toM_clients_at hc
  have hmem : toClient c ∈ (toM s).clients := mem_toM_clients (get?_mem hc)
  have htl := YataModel.WF.timeline h (toClient c) hmem
  have same : ∀ r, NoStraddle (toM s) ci.val clock.val → SplitInsidePost s ci clock r s :=
    fun _ hn => ⟨h, fun _ => rfl, fun c' hc' => ⟨c', hc', rfl⟩, fun _ _ => hn, fun _ hz => hz⟩
  have hclt := get?_lt hc
  step as ⟨cec, hcec⟩
  have hx := get?_of_getElem hclt hcec
  rw [hc] at hx
  cases hx
  step with ClientBlocks.find_spec c.blocks clock ⟨htl⟩ as ⟨o, ho⟩
  rcases ho with ⟨rfl, hno⟩ | ⟨pos, rfl, hholds⟩
  · simp only [spec_ok, uncurry'_pair]
    exact same _ (noStraddle_none hcm hno)
  · simp only []
    have hp : Holds (toClient c).blocks (toClient c).stop pos.val clock.val := hholds
    obtain ⟨a, ha, hge, hlt⟩ := hholds
    obtain ⟨b, hb, eb⟩ := block_of_toClient (c := c) ha
    have hbm := toClient_block hb
    have hbc : (toBlock b).clock = b.clock.val := rfl
    rw [← eb, hbc] at hge
    have hlt' : clock.val < endAt (toClient c).blocks (toClient c).stop pos.val := hlt
    have hblt := get?_lt hb
    step as ⟨brc, hbrc⟩
    have hy := get?_of_getElem hblt hbrc
    rw [hb] at hy
    cases hy
    step as ⟨brc1, hbrc1⟩
    have hy1 := get?_of_getElem hblt hbrc1
    rw [hb] at hy1
    cases hy1
    cases hk : b.kind with
    | Item idx =>
      refine spec_bind_ok ?_
      simp only [↓reduceIte]
      by_cases h1 : b.clock < clock
      · simp only [h1, ↓reduceIte]
        have hslot : (toBlock b).kind.slot = some idx.val := by
          show (toKind b.kind).slot = some idx.val
          rw [hk]
          rfl
        obtain ⟨j', x, hs', hx', _, hxlen, _, _, _⟩ := YataModel.WF.block_item h hmem hbm
        rw [hslot] at hs'
        cases hs'
        step as ⟨i, hi⟩
        have hlt1 : b.clock.val < clock.val := by scalar_tac
        have hiv : i.val = clock.val - b.clock.val := by scalar_tac
        have hd0 : 0 < i.val := by omega
        have hd1 : i.val < x.len := by omega
        have hd : ∀ (j : Nat) (y : MItem), (toKind b.kind).slot = some j →
            coreAt (toM s).items j = some y → 0 < i.val ∧ i.val < y.len := by
          intro j y hj hy
          have hjj : (toBlock b).kind.slot = some j := hj
          rw [hslot] at hjj
          cases hjj
          rw [hx'] at hy
          cases hy
          exact ⟨hd0, hd1⟩
        step with split_node_spec s ci pos i h hc hb hd as ⟨r, s1, hpost⟩
        cases r with
        | Err err =>
          simp only [spec_ok, uncurry'_pair]
          rw [hpost.err err rfl]
          exact ⟨h, fun _ => rfl, fun c' hc' => ⟨c', hc', rfl⟩, (fun _ hh => nomatch hh),
            fun _ hz => hz⟩
        | Ok p =>
          obtain ⟨l, rt⟩ := p
          obtain ⟨hl, hrt, hm⟩ := hpost.ok l rt rfl
          have hl' : (toBlock b).kind.slot = some l.val := by
            show (toKind b.kind).slot = some l.val
            rw [← kindSlot_val, hl]
            rfl
          rw [hslot] at hl'
          have hli : l.val = idx.val := (Option.some.inj hl').symm
          rw [hli] at hm
          obtain ⟨k, _, hwf, _⟩ := splitNode_spec h hcm hbm hslot hx' hd0 hd1
          obtain ⟨hcut, hkeep⟩ := splitNode_noStraddle (d := i.val) h hcm hbm hslot hx' hd1
          have hcl := splitNode_client (d := i.val) h hcm hbm hslot hx'
          have hinv1 : Inv s1 := by
            unfold Inv
            rw [hm]
            exact hwf
          have hcut' : NoStraddle (toM s1) ci.val clock.val := by
            rw [hm]
            have e : clock.val = (toBlock b).clock + i.val := by
              rw [hbc]
              omega
            rw [e]
            exact hcut
          have hkeep' : ∀ z, NoStraddle (toM s) ci.val z → NoStraddle (toM s1) ci.val z := by
            intro z hz
            rw [hm]
            exact hkeep z hz
          have hci : (toM s1).clients[ci.val]? = some ((toClient c).withBlock (pos.val + 1)
              ⟨(toBlock b).clock + i.val, (toBlock b).kind.reslot (toM s).items.length⟩) := by
            rw [hm]
            exact hcl
          obtain ⟨c1, hc1, ec1⟩ := clients_of_toM hci
          have hc1c : c1.client = c.client :=
            UScalar.eq_of_val_eq (congrArg MClient.client ec1)
          show spec (ok _) _
          simp only [spec_ok, uncurry'_pair]
          refine ⟨hinv1, fun f => ?_, fun c' hc' => ?_, fun _ _ => hcut', hkeep'⟩
          · show YoctoSpec.toDoc (blocks f (toM s1)) = YoctoSpec.toDoc (blocks f (toM s))
            rw [hm, blocks_splitNode h hcm hbm hslot hx' hd0 hd1]
            exact YoctoSpec.toDoc_split _ _
          · rw [hc] at hc'
            rw [← Option.some.inj hc']
            exact ⟨c1, hc1, hc1c⟩
      · simp only [h1, ↓reduceIte, spec_ok, uncurry'_pair]
        refine same _ (noStraddle_at hcm htl hp hbm (Or.inr ?_))
        rw [hbc]
        have : ¬ b.clock.val < clock.val := by scalar_tac
        omega
    | DeletedItem idx =>
      refine spec_bind_ok ?_
      simp only [Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
      refine same _ (noStraddle_at hcm htl hp hbm (Or.inl ?_))
      show (toKind b.kind).dead = true
      rw [hk]
      rfl
    | Gc =>
      refine spec_bind_ok ?_
      simp only [Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
      refine same _ (noStraddle_at hcm htl hp hbm (Or.inl ?_))
      show (toKind b.kind).dead = true
      rw [hk]
      rfl
    | Skip =>
      refine spec_bind_ok ?_
      simp only [Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
      refine same _ (noStraddle_at hcm htl hp hbm (Or.inl ?_))
      show (toKind b.kind).dead = true
      rw [hk]
      rfl

/-- The store `delete_block` builds is `markDeleted` of the model. -/
theorem toM_mark_deleted {s1 : yata_store.YataStoreCore} {ci pos i : Std.Usize}
    {c1 : yata_store.ClientEntryCore} {b1 : client_blocks.BlockRefCore} {idx : Std.U32}
    {ic : yata_store.ItemCore} {cbc : client_blocks.ClientBlocksCore}
    (hc1 : s1.clients.val[ci.val]? = some c1) (hb1 : c1.blocks.blocks.val[pos.val]? = some b1)
    (hit : s1.items.val[idx.val]? = some ic) (hi : i.val = idx.val)
    (hbl : cbc.blocks.val = c1.blocks.blocks.val.set pos.val
      ({ clock := b1.clock, kind := client_blocks.BlockKindCore.DeletedItem idx } :
        client_blocks.BlockRefCore))
    (hend : cbc.end_clock = c1.blocks.end_clock) :
    (MStore.mk ((s1.items.set i { ic with deleted := true }).val.map toItem) (toSlot s1.start)
      ((s1.clients.set ci { c1 with blocks := cbc }).val.map toClient)) =
      markDeleted (toM s1) ci.val pos.val idx.val := by
  unfold markDeleted
  rw [MStore.mk.injEq]
  refine ⟨?_, rfl, ?_⟩
  · rw [alloc.vec.Vec.set_val_eq, hi]
    exact map_set_get toItem hit _ _ rfl
  · rw [alloc.vec.Vec.set_val_eq]
    refine map_set_get toClient hc1 _ _ ?_
    show (⟨c1.client.val, toBlocks cbc, cbc.end_clock.val⟩ : MClient) =
      ⟨c1.client.val, upd (toBlocks c1.blocks) pos.val _, c1.blocks.end_clock.val⟩
    rw [hend]
    unfold toBlocks
    rw [hbl, map_set_get toBlock hb1 _ (fun b => { b with kind := MKind.deleted idx.val }) rfl]

/-- What `delete_block` does to the block `b`: it accepts; a block that is
deleted already stays as it is, a live one is `markDeleted` of the model. -/
structure DeleteBlockPost (s : yata_store.YataStoreCore) (ci pos : Std.Usize)
    (b : client_blocks.BlockRefCore) (r : core.result.Result Unit client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  ok : r = core.result.Result.Ok ()
  state : ((toBlock b).kind.dead = true ∧ s' = s) ∨
    ∃ i, (toBlock b).kind = MKind.item i ∧ toM s' = markDeleted (toM s) ci.val pos.val i

theorem delete_block_spec (s : yata_store.YataStoreCore) (ci pos : Std.Usize) (h : Inv s)
    {c : yata_store.ClientEntryCore} {b : client_blocks.BlockRefCore}
    (hc : s.clients.val[ci.val]? = some c) (hb : c.blocks.blocks.val[pos.val]? = some b) :
    yata_store.YataStoreCore.delete_block s ci pos ⦃ r s' =>
      DeleteBlockPost s ci pos b r s' ⦄ := by
  unfold yata_store.YataStoreCore.delete_block
  have hclt := get?_lt hc
  step as ⟨cec, hcec⟩
  have hx := get?_of_getElem hclt hcec
  rw [hc] at hx
  cases hx
  have hblt := get?_lt hb
  step as ⟨brc, hbrc⟩
  have hy := get?_of_getElem hblt hbrc
  rw [hb] at hy
  cases hy
  have dead : (toKind b.kind).dead = true →
      DeleteBlockPost s ci pos b (core.result.Result.Ok ()) s :=
    fun hd => ⟨rfl, Or.inl ⟨hd, rfl⟩⟩
  cases hk : b.kind with
  | Item idx =>
    refine spec_bind_ok ?_
    simp only []
    step as ⟨cec1, back, hcec1, hback⟩
    have hx1 := get?_of_getElem hclt hcec1
    rw [hc] at hx1
    cases hx1
    subst hback
    step as ⟨r1, cbc, hmd⟩
    cases r1 with
    | Err err =>
      exfalso
      have hno := hmd.accepts b err hb rfl
      rw [hk] at hno
      have hno' : (some idx : Option Std.U32) = none := hno
      cases hno'
    | Ok u1 =>
      obtain ⟨b2, i2, hb2, hslot2, hbl, hend⟩ := hmd.ok rfl
      rw [hb] at hb2
      cases hb2
      have hi2 : i2 = idx := by
        rw [hk] at hslot2
        exact (Option.some.inj hslot2).symm
      subst hi2
      have hcm := toM_clients_at hc
      have hbm := toClient_block hb
      have hkind : (toBlock b).kind = MKind.item i2.val := by
        show toKind b.kind = MKind.item i2.val
        rw [hk]
        rfl
      have hslot : (toBlock b).kind.slot = some i2.val := by
        rw [hkind]
        rfl
      obtain ⟨j', x, hs', hx', _, _, _, hiord, _⟩ :=
        YataModel.WF.block_item h (get?_mem hcm) hbm
      rw [hslot] at hs'
      cases hs'
      have hidx : i2.val < s.items.val.length := order_bound h hiord
      simp only []
      step as ⟨i, hi⟩
      have hiv : i.val = i2.val := by scalar_tac
      have hilt : i.val < s.items.val.length := by omega
      step as ⟨ic, back1, hic, hback1⟩
      have hit := get?_of_getElem hilt hic
      rw [hiv] at hit
      subst hback1
      have hm := toM_mark_deleted hc hb hit hiv hbl hend
      exact ⟨rfl, Or.inr ⟨i2.val, hkind, hm⟩⟩
  | DeletedItem idx =>
    refine spec_bind_ok ?_
    simp only [spec_ok, uncurry'_pair]
    exact dead (by rw [hk]; rfl)
  | Gc =>
    refine spec_bind_ok ?_
    simp only [spec_ok, uncurry'_pair]
    exact dead (by rw [hk]; rfl)
  | Skip =>
    refine spec_bind_ok ?_
    simp only [spec_ok, uncurry'_pair]
    exact dead (by rw [hk]; rfl)

/-- The loop of `delete_range`, when it is done with the blocks before `pos`
of the timeline `ci`, which has `len` blocks. -/
structure DelLoop (m : MStore) (t : yata_store.YataStoreCore)
    (ci client start stop pos0 pos len : Nat) : Prop where
  mark : Marking m (toM t) ci client start stop pos0 pos
  len : ∀ c, (toM t).clients[ci]? = some c → c.blocks.length = len

/-- The loop of `delete_range` when it stops: it never fails, and the block
it stops at, if there is one, starts at `stop` or after. -/
structure DelDone (m : MStore) (ci client start stop pos0 : Nat)
    (r : core.result.Result Unit client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  ok : r = core.result.Result.Ok ()
  fin : ∃ pos, Marking m (toM s') ci client start stop pos0 pos ∧
    ∀ (c : MClient) (b : MBlock), (toM s').clients[ci]? = some c → c.blocks[pos]? = some b →
      stop ≤ b.clock

theorem delete_range_loop_spec (m : MStore) (s : yata_store.YataStoreCore) (stop : Std.U64)
    (ci pos0 : Std.Usize) (client start : Nat)
    (hmk : Marking m (toM s) ci.val client start stop.val pos0.val pos0.val) :
    yata_store.YataStoreCore.delete_range_loop s stop ci pos0 ⦃ r s' =>
      DelDone m ci.val client start stop.val pos0.val r s' ⦄ := by
  unfold yata_store.YataStoreCore.delete_range_loop
  obtain ⟨c0, hc0, _⟩ := hmk.timeline
  have hinit : DelLoop m s ci.val client start stop.val pos0.val pos0.val c0.blocks.length :=
    ⟨hmk, fun c hc => by rw [hc0] at hc; rw [← Option.some.inj hc]⟩
  refine loop.spec_decr_nat
    (fun ((_, k) : yata_store.YataStoreCore × Std.Usize) => c0.blocks.length - k.val)
    (fun ((t, k) : yata_store.YataStoreCore × Std.Usize) =>
      DelLoop m t ci.val client start stop.val pos0.val k.val c0.blocks.length)
    (fun (r : core.result.Result Unit client_blocks.StoreError × yata_store.YataStoreCore) =>
      DelDone m ci.val client start stop.val pos0.val r.1 r.2)
    _ (s, pos0) ?_ hinit
  intro ⟨t, k⟩ hinv0
  have hinv : DelLoop m t ci.val client start stop.val pos0.val k.val c0.blocks.length := hinv0
  unfold yata_store.YataStoreCore.delete_range_loop.body
  simp only
  have hmk' := hinv.mark
  obtain ⟨mc, hmc, _⟩ := hmk'.timeline
  obtain ⟨c, hc, ec⟩ := clients_of_toM hmc
  rw [← ec] at hmc
  have hlen := hinv.len _ hmc
  have hclt := get?_lt hc
  step as ⟨cec, hcec⟩
  have hx := get?_of_getElem hclt hcec
  rw [hc] at hx
  cases hx
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hle⟩ | ⟨b, e, rfl, hb, he⟩
  · simp only [spec_ok]
    refine ⟨rfl, k.val, hmk', ?_⟩
    intro c' b' hc' hb'
    have hc'' : (toM t).clients[ci.val]? = some c' := hc'
    rw [hmc] at hc''
    rw [← Option.some.inj hc''] at hb'
    have h1 := get?_lt hb'
    have h2 : (toClient c).blocks.length = c.blocks.blocks.val.length := toBlocks_length c.blocks
    omega
  · have hbm := toClient_block hb
    show (if b.clock >= stop then _ else _) ⦃ _ ⦄
    by_cases hge : b.clock >= stop
    · simp only [hge, ↓reduceIte, spec_ok]
      refine ⟨rfl, k.val, hmk', ?_⟩
      intro c' b' hc' hb'
      have hc'' : (toM t).clients[ci.val]? = some c' := hc'
      rw [hmc] at hc''
      rw [← Option.some.inj hc'', hbm] at hb'
      rw [← Option.some.inj hb']
      show stop.val ≤ b.clock.val
      scalar_tac
    · simp only [hge, ↓reduceIte]
      have hinvt : Inv t := hmk'.wf
      have hkl := get?_lt hb
      have hbnd := c.blocks.blocks.property
      step with delete_block_spec t ci k hinvt hc hb as ⟨r, t1, hdb⟩
      have hr := hdb.ok
      have hpost := hdb.state
      subst hr
      simp only []
      step as ⟨k1, hk1⟩
      have ek1 : k1.val = k.val + 1 := by scalar_tac
      have hlt : (toBlock b).clock < stop.val := by
        show b.clock.val < stop.val
        scalar_tac
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [ek1]
        rcases hpost with ⟨hd, e1⟩ | ⟨i, hki, hm⟩
        · rw [e1]
          exact hmk'.skip hmc hbm hd
        · rw [hm]
          exact hmk'.mark hmc hbm hki hlt
      · intro c' hc'
        rcases hpost with ⟨_, e1⟩ | ⟨i, _, hm⟩
        · rw [e1] at hc'
          exact hinv.len c' hc'
        · rw [hm, markDeleted_client k.val i hmc] at hc'
          rw [← Option.some.inj hc']
          show (upd (toClient c).blocks k.val _).length = _
          rw [length_upd]
          exact hlen
      · have h1 : k.val < (toClient c).blocks.length := get?_lt hbm
        omega

/-- What `delete_range` does, by its answer. -/
structure DeletePost (s : yata_store.YataStoreCore) (client start stop : Std.U64)
    (r : core.result.Result Unit client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  inv : Inv s'
  /-- an error deletes nothing -/
  err : ∀ e, r = core.result.Result.Err e →
    ∀ f, YoctoSpec.toDoc (abs f s') = YoctoSpec.toDoc (abs f s)
  /-- the store does not hold `start`, or the range is empty: nothing is done -/
  idle : r = core.result.Result.Ok () →
    ¬ (Held (toM s) ⟨client.val, start.val⟩ ∧ start.val < stop.val) → s' = s
  /-- otherwise the clocks and their order stay, and the deleted clocks are
  the ones there were and the clocks of `client` in `start..stop` the store
  holds -/
  done : r = core.result.Result.Ok () → Held (toM s) ⟨client.val, start.val⟩ →
    start.val < stop.val →
    ∀ f, YoctoSpec.flatten (abs f s') = YoctoSpec.flatten (abs f s) ∧
      ∀ x, x ∈ YoctoSpec.deletedSet (abs f s') ↔
        x ∈ YoctoSpec.deletedSet (abs f s) ∨
          x ∈ YoctoSpec.presentRange (abs f s) client.val start.val stop.val

/-- **`delete_range` deletes exactly the range.** It is total and keeps the
invariant. When it accepts, the store holds `start` and `start < stop`, the
clocks of the store and their order stay and its deleted clocks are the ones
it had and the clocks of `client` in `start..stop` it holds (`presentRange`,
what `YoctoSpec.deleteRange` deletes); when it accepts otherwise the store is
unchanged; when it fails the store stands for the same document: no clock is
deleted. -/
theorem delete_range_spec (s : yata_store.YataStoreCore) (client start stop : Std.U64)
    (h : Inv s) :
    yata_store.YataStoreCore.delete_range s client start stop ⦃ r s' =>
      DeletePost s client start stop r s' ⦄ := by
  unfold yata_store.YataStoreCore.delete_range
  have idle : ¬ (Held (toM s) ⟨client.val, start.val⟩ ∧ start.val < stop.val) →
      DeletePost s client start stop (core.result.Result.Ok ()) s :=
    fun hno => ⟨h, (fun _ hh => nomatch hh), fun _ _ => rfl, fun _ hh hl => absurd ⟨hh, hl⟩ hno⟩
  have full : ∀ e, DeletePost s client start stop (core.result.Result.Err e) s :=
    fun _ => ⟨h, fun _ _ _ => rfl, (fun hh => nomatch hh), (fun hh => nomatch hh)⟩
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, hnone⟩ | ⟨ci, c, rfl, hc, hcl⟩
  · simp only [spec_ok, uncurry'_pair]
    refine idle ?_
    rintro ⟨⟨c', p, b, ha⟩, _⟩
    obtain ⟨c0, hc0, e0⟩ := List.mem_map.mp ha.mem
    obtain ⟨j, hj⟩ := mem_get? hc0
    apply hnone j c0 hj
    apply UScalar.eq_of_val_eq
    have e1 : c'.client = client.val := ha.client
    rw [← e0] at e1
    exact e1
  · simp only []
    have hclt := get?_lt hc
    step as ⟨cec, hcec⟩
    have hx := get?_of_getElem hclt hcec
    rw [hc] at hx
    cases hx
    have hcm := toM_clients_at hc
    have hmem : toClient c ∈ (toM s).clients := mem_toM_clients (get?_mem hc)
    have htl := YataModel.WF.timeline h (toClient c) hmem
    have hclv : (toClient c).client = client.val := by
      show c.client.val = client.val
      rw [hcl]
    step with ClientBlocks.find_spec c.blocks start ⟨htl⟩ as ⟨o1, ho1⟩
    rcases ho1 with ⟨rfl, hno⟩ | ⟨pos, rfl, hholds⟩
    · simp only [spec_ok, uncurry'_pair]
      refine idle ?_
      rintro ⟨⟨c', p, b, ha⟩, _⟩
      have ec : c' = toClient c :=
        YataModel.WF.client_unique h ha.mem hmem (ha.client.trans hclv.symm)
      rw [ec] at ha
      exact hno p ⟨b, ha.block, ha.ge, ha.lt⟩
    · simp only []
      obtain ⟨a, ha, hage, halt⟩ := hholds
      have hheld0 : Held (toM s) ⟨client.val, start.val⟩ :=
        ⟨toClient c, pos.val, a, ⟨hmem, hclv, ha, hage, halt⟩⟩
      by_cases hse : start >= stop
      · simp only [hse, ↓reduceIte, spec_ok, uncurry'_pair]
        refine idle ?_
        rintro ⟨_, hl⟩
        scalar_tac
      · simp only [hse, ↓reduceIte]
        have hsl : start.val < stop.val := by scalar_tac
        have hmax2 : 2 ≤ (yata_store.MAX_ITEMS).val := by
          simp [yata_store.MAX_ITEMS]
        step as ⟨i1, hi1⟩
        by_cases hcap : alloc.vec.Vec.len s.items > i1
        · simp only [hcap, ↓reduceIte, spec_ok, uncurry'_pair]
          exact full _
        · simp only [hcap, ↓reduceIte]
          step as ⟨i2, hi2⟩
          have hmaxb : 2 ≤ (client_blocks.MAX_BLOCKS).val := by
            simp [client_blocks.MAX_BLOCKS]
          step as ⟨i3, hi3⟩
          by_cases hcapb : i2 > i3
          · simp only [hcapb, ↓reduceIte, spec_ok, uncurry'_pair]
            exact full _
          · simp only [hcapb, ↓reduceIte]
            step with split_inside_spec s ci start h hc as ⟨r, s1, hs1⟩
            cases r with
            | Err err =>
              simp only [spec_ok, uncurry'_pair]
              exact ⟨hs1.inv, fun _ _ f => hs1.doc f, (fun hh => nomatch hh),
                (fun hh => nomatch hh)⟩
            | Ok u =>
              simp only []
              obtain ⟨c1, hc1, hcl1⟩ := hs1.client c hc
              step with split_inside_spec s1 ci stop hs1.inv hc1 as ⟨r1, s2, hs2⟩
              have hdoc : ∀ f, YoctoSpec.toDoc (abs f s2) = YoctoSpec.toDoc (abs f s) :=
                fun f => (hs2.doc f).trans (hs1.doc f)
              cases r1 with
              | Err err =>
                simp only [spec_ok, uncurry'_pair]
                exact ⟨hs2.inv, fun _ _ f => hdoc f, (fun hh => nomatch hh),
                  (fun hh => nomatch hh)⟩
              | Ok u1 =>
                simp only []
                obtain ⟨c2, hc2, hcl2⟩ := hs2.client c1 hc1
                have hc2lt := get?_lt hc2
                step as ⟨cec1, hcec1⟩
                have hx2 := get?_of_getElem hc2lt hcec1
                rw [hc2] at hx2
                cases hx2
                have hc2m := toM_clients_at hc2
                have hmem2 : toClient c2 ∈ (toM s2).clients :=
                  mem_toM_clients (get?_mem hc2)
                have htl2 := YataModel.WF.timeline hs2.inv (toClient c2) hmem2
                have hclv2 : (toClient c2).client = client.val := by
                  show c2.client.val = client.val
                  rw [hcl2, hcl1, hcl]
                have hheld : ∀ z, Held (toM s2) z ↔ Held (toM s) z := by
                  intro z
                  have e : YoctoSpec.flatten (abs (fun _ => 'a') s2) =
                      YoctoSpec.flatten (abs (fun _ => 'a') s) :=
                    congrArg YoctoSpec.Doc.items (hdoc (fun _ => 'a'))
                  have e2 := held_iff (s := toM s2) (f := fun _ => 'a') hs2.inv z
                  have e0 := held_iff (s := toM s) (f := fun _ => 'a') h z
                  unfold abs at e
                  rw [e] at e2
                  exact e2.symm.trans e0
                step with ClientBlocks.find_spec c2.blocks start ⟨htl2⟩ as ⟨o2, ho2⟩
                rcases ho2 with ⟨rfl, hno2⟩ | ⟨pos2, rfl, hholds2⟩
                · simp only [spec_ok, uncurry'_pair]
                  exfalso
                  obtain ⟨c', p, b, ha2⟩ := (hheld _).mpr hheld0
                  have ec : c' = toClient c2 :=
                    YataModel.WF.client_unique hs2.inv ha2.mem hmem2 (ha2.client.trans hclv2.symm)
                  rw [ec] at ha2
                  exact hno2 p ⟨b, ha2.block, ha2.ge, ha2.lt⟩
                · simp only []
                  have hfirst : NoStraddle (toM s2) ci.val start.val :=
                    hs2.keep _ (hs1.cut u rfl)
                  have hlast : NoStraddle (toM s2) ci.val stop.val := hs2.cut u1 rfl
                  have hmk : Marking (toM s2) (toM s2) ci.val client.val start.val stop.val
                      pos2.val pos2.val :=
                    Marking.init hs2.inv hc2m hclv2 hholds2 hfirst hlast
                  refine spec_mono
                    (delete_range_loop_spec (toM s2) s2 stop ci pos2 client.val start.val hmk) ?_
                  rintro ⟨r2, s3⟩ hpost
                  have hdn : DelDone (toM s2) ci.val client.val start.val stop.val pos2.val r2 s3 :=
                    hpost
                  obtain ⟨posf, hmf, hexit⟩ := hdn.fin
                  show DeletePost s client start stop r2 s3
                  refine ⟨hmf.wf, ?_, fun _ hnh => absurd ⟨hheld0, hsl⟩ hnh, fun _ _ _ f => ?_⟩
                  · intro e he
                    rw [hdn.ok] at he
                    cases he
                  · have eflat : YoctoSpec.flatten (abs f s2) = YoctoSpec.flatten (abs f s) :=
                      congrArg YoctoSpec.Doc.items (hdoc f)
                    have edel : YoctoSpec.deletedSet (abs f s2) = YoctoSpec.deletedSet (abs f s) :=
                      congrArg YoctoSpec.Doc.deleted (hdoc f)
                    refine ⟨(hmf.flat f).trans eflat, fun x => ?_⟩
                    have e1 : x ∈ YoctoSpec.deletedSet (abs f s3) ↔ Dead (toM s3) x :=
                      dead_iff hmf.wf x
                    have e2 : x ∈ YoctoSpec.deletedSet (abs f s) ↔ Dead (toM s2) x := by
                      rw [← edel]
                      exact dead_iff (s := toM s2) hs2.inv x
                    have e3 : x ∈ (YoctoSpec.flatten (abs f s)).map YoctoSpec.Item.id ↔
                        Held (toM s2) x := by
                      rw [← eflat]
                      exact held_iff (s := toM s2) hs2.inv x
                    rw [e1, e2, YoctoSpec.mem_presentRange, e3]
                    exact hmf.final hexit x

/-! ## A struct without origins is accepted

`integrate_spec` says what `integrate` does when it accepts. That it accepts
is shown here for a struct without origins that continues the timeline of
its client, in a store with room for it (`Room`): what a run that only
inserts at the start of the sequence needs (`Refinement.core_witness`). -/

/-- `check_append` accepts a struct that continues the timeline of its
client and whose clocks do not overflow. -/
theorem check_append_accepts (s : yata_store.YataStoreCore) (id : yata_store.IdCore)
    (len : Std.U64) (hr : Room s id len) :
    yata_store.YataStoreCore.check_append s id len ⦃ r => r = core.result.Result.Ok () ⦄ := by
  unfold yata_store.YataStoreCore.check_append
  have hMax : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide
  have hle : id.clock.val ≤ (core.num.U64.MAX : Std.U64).val := by
    rw [hMax]
    scalar_tac
  have hfit := hr.fits
  have tail : ∀ cont : Bool, cont = true →
      (if cont = true then do
          let i ← core.num.U64.MAX - id.clock
          if len > i then ok (core.result.Result.Err client_blocks.StoreError.ClockOverflow)
          else ok (core.result.Result.Ok ())
        else ok (core.result.Result.Err client_blocks.StoreError.ClockMismatch)) ⦃ r =>
          r = core.result.Result.Ok () ⦄ := by
    intro cont hc
    simp only [hc, ↓reduceIte]
    step as ⟨i, hi⟩
    have hni : ¬ len > i := by scalar_tac
    simp only [hni, ↓reduceIte, spec_ok]
  step as ⟨o, ho⟩
  rcases ho with ⟨rfl, _⟩ | ⟨ci, c, rfl, hc, hcl⟩
  · have hinner0 : (ok true : Result Bool) ⦃ b => b = true ⦄ := by simp [spec_ok]
    exact spec_bind hinner0 (fun cont hcont => tail cont hcont)
  · have hlt := get?_lt hc
    have hinner :
        (do
          let cec ← alloc.vec.Vec.index_usize s.clients ci
          client_blocks.ClientBlocksCore.continues cec.blocks id.clock) ⦃ b => b = true ⦄ := by
      step as ⟨cec, hcec⟩
      have hx := get?_of_getElem hlt hcec
      rw [hc] at hx
      cases hx
      refine spec_mono (ClientBlocks.continues_spec _ _) ?_
      intro b hb
      exact hb.mpr (hr.cont c (get?_mem hc) hcl).1
    exact spec_bind hinner (fun cont hcont => tail cont hcont)

/-- **`integrate` accepts a struct without origins when there is room for
it**, and the store grows by one item and at most one timeline. -/
theorem integrate_root_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore)
    (len : Std.U64) (h : Inv s) (hr : Room s id len) :
    yata_store.YataStoreCore.integrate s id len none none ⦃ r s' => RootPost s id r s' ⦄ := by
  unfold yata_store.YataStoreCore.integrate
  have hpos := hr.pos
  have hz : ¬ len = 0#u64 := by scalar_tac
  simp only [hz, ↓reduceIte]
  have hco : yata_store.check_origin id none = ok (core.result.Result.Ok ()) := by
    unfold yata_store.check_origin
    rfl
  simp only [hco]
  step with check_append_accepts s id len hr as ⟨r2, hr2⟩
  subst hr2
  simp only []
  have hmax3 : 3 ≤ (yata_store.MAX_ITEMS).val := by
    simp [yata_store.MAX_ITEMS]
  have hmv : (yata_store.MAX_ITEMS).val = 4294967295 := by
    simp [yata_store.MAX_ITEMS]
  step as ⟨i1, hi1⟩
  have hcap : ¬ alloc.vec.Vec.len s.items > i1 := by
    have := hr.items
    scalar_tac
  simp only [hcap, ↓reduceIte]
  have hrl : yata_store.YataStoreCore.repair_left s none =
      ok (core.result.Result.Ok (none, none), s) := by
    unfold yata_store.YataStoreCore.repair_left
    rfl
  have hrr : yata_store.YataStoreCore.repair_right s none =
      ok (core.result.Result.Ok (none, none), s) := by
    unfold yata_store.YataStoreCore.repair_right
    rfl
  rw [hrl]
  refine spec_bind_ok ?_
  show spec (Bind.bind _ _) _
  rw [hrr]
  refine spec_bind_ok ?_
  show spec (Bind.bind _ _) _
  have hnone : toSlot (none : Option Std.U32) = none := rfl
  have hlmem : ∀ i, toSlot (none : Option Std.U32) = some i → i ∈ order (toM s) := by
    intro i hi
    rw [hnone] at hi
    cases hi
  step with conflict_left_spec s id none none none none h (Nat.zero_le _) rfl hlmem
    as ⟨left1, hleft1⟩
  obtain ⟨k', hk', ek'⟩ := scanM_pos h (toId id) none none (toSlot (none : Option Std.U32)) hlmem
  refine spec_mono (link_spec s id len none none left1 h hk' (hleft1.trans ek')) ?_
  rintro ⟨r5, s3⟩ hpost
  have hpost' : LinkPost s id len none none left1 r5 s3 := hpost
  exact hpost'.room hr

end YoctoCore.Properties.YataStore
