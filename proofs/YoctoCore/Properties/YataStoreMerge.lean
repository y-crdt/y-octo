/-
`merge_adjacent` (with `continues`) and `visible_ids` of
`y_octo_core::yata_store`, on the extracted code.

`merge_adjacent` is total on every store that satisfies `Inv` and keeps it.
When it answers `Ok true` it merged the block that holds the id it was given
with the next block of the sequence: the two can merge, the block sequence
the store stands for is `YoctoSpec.mergeAt` of the one before at the place
of that block, and it is one block shorter. On any other answer the store is
as it was. Either way the store stands for the same document
(`MergeAdjacentPost`).

`visible_ids` is total on every store that satisfies `Inv`: it answers the
first id and the length of every block that is not deleted, in the order of
the sequence (`visible_ids_spec`, `visible_ids_abs`), which are, clock by
clock, the visible ids of the document the store stands for.

`items`, `start` and `clients` read the private fields of a store
(`items_spec`, `start_spec`, `clients_spec`).
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.YataModel
import YoctoCore.Properties.YataMerge
import YoctoCore.Properties.ClientBlocks
import YoctoCore.Properties.YataStore

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties
open YoctoCore.Properties.ListAux YoctoCore.Properties.YataModel
open YoctoCore.Properties.ClientBlocks (toKind toBlock toBlocks kindSlot kindSlot_val
  toBlocks_get? toBlocks_length get?_of_getElem)

open YoctoCore.Properties.Ring (blocksOf length_blocksOf length_blocksOf_le)

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace YoctoCore.Properties.YataStore

/-! ## `continues` -/

/-- What `can_merge_items` reads of an item of the store. -/
def sideOf (item : yata_store.ItemCore) : doc_kernel.MergeSide :=
  { id := item.id
    len := item.len
    origin_left := item.origin_left
    origin_right := item.origin_right
    left := item.left
    right := item.right }

theorem merge_side_eq (item : yata_store.ItemCore) :
    yata_store.merge_side item = ok (sideOf item) := by
  unfold yata_store.merge_side sideOf
  rfl

theorem optId_inj {a b : Option yata_store.IdCore} (h : a.map toId = b.map toId) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => cases h
  | some x =>
    cases b with
    | none => cases h
    | some y =>
      have e : toId x = toId y := Option.some.inj h
      rw [toId_inj e]

/-- `continues`: the right item follows the left one in the sequence, was
typed right after its last clock with the same right origin, both hold the
same kind of content, and (`can_merge_items`, the conditions
`DocStore::merge_items` merges on) its first clock is the next clock of the
same client. It is total on every pair of items: the clocks of a left item
that has none, or whose clocks do not fit a `u64`, are not computed. -/
theorem continues_spec (left right : yata_store.ItemCore) (l r : Std.U32) :
    yata_store.continues left l right r ⦃ b =>
      (b = true ↔
        toSlot left.right = some r.val ∧ toSlot right.left = some l.val ∧
        right.origin_left.map toId =
          some ⟨left.id.client.val, left.id.clock.val + left.len.val - 1⟩ ∧
        left.origin_right.map toId = right.origin_right.map toId ∧ left.gc = right.gc ∧
        left.id.client = right.id.client ∧ 0 < left.len.val ∧
        left.id.clock.val + left.len.val ≤ Std.U64.max ∧
        left.id.clock.val + left.len.val = right.id.clock.val) ⦄ := by
  unfold yata_store.continues
  simp only [merge_side_eq, bind_ok]
  step with DocKernel.can_merge_items_spec (sideOf left) l (sideOf right) r true as ⟨b, hb⟩
  -- the conditions of the kernel, on the model
  have fwd : DocKernel.CanMerge (sideOf left) l (sideOf right) r →
      toSlot left.right = some r.val ∧ toSlot right.left = some l.val ∧
        right.origin_left.map toId =
          some ⟨left.id.client.val, left.id.clock.val + left.len.val - 1⟩ ∧
        left.origin_right.map toId = right.origin_right.map toId := by
    intro hc
    have h1 : left.right = some r := hc.right_of
    have h2 : right.left = some l := hc.left_of
    have h4 : left.origin_right = right.origin_right := hc.origin
    obtain ⟨o, e1, e2, e3⟩ := hc.typed
    have e1' : right.origin_left = some o := e1
    have e2' : o.client = left.id.client := e2
    have e3' : o.clock.val = left.id.clock.val + left.len.val - 1 := e3
    refine ⟨toSlot_some_iff.mpr h1, toSlot_some_iff.mpr h2, ?_, by rw [h4]⟩
    rw [e1']
    show some (toId o) = some _
    unfold toId
    rw [e2', e3']
  have bwd : toSlot left.right = some r.val → toSlot right.left = some l.val →
      right.origin_left.map toId =
        some ⟨left.id.client.val, left.id.clock.val + left.len.val - 1⟩ →
      left.origin_right.map toId = right.origin_right.map toId →
      left.id.client = right.id.client → 0 < left.len.val →
      left.id.clock.val + left.len.val ≤ Std.U64.max →
      left.id.clock.val + left.len.val = right.id.clock.val →
      DocKernel.CanMerge (sideOf left) l (sideOf right) r := by
    intro h1 h2 h3 h4 h5 h6 h7 h8
    refine ⟨toSlot_some_iff.mp h1, toSlot_some_iff.mp h2, h5, h6, h7, h8, ?_, optId_inj h4⟩
    cases hro : right.origin_left with
    | none =>
      rw [hro] at h3
      cases h3
    | some o =>
      rw [hro] at h3
      have e : toId o = ⟨left.id.client.val, left.id.clock.val + left.len.val - 1⟩ :=
        Option.some.inj h3
      refine ⟨o, hro, UScalar.eq_of_val_eq (congrArg YoctoSpec.Id.client e), ?_⟩
      exact congrArg YoctoSpec.Id.clock e
  have hmpr : DocKernel.CanMerge (sideOf left) l (sideOf right) r → b = true := hb.mpr
  by_cases hbt : b = true
  · simp only [hbt, ↓reduceIte, spec_ok, decide_eq_true_eq]
    have hc : DocKernel.CanMerge (sideOf left) l (sideOf right) r := hb.mp hbt
    obtain ⟨h1, h2, h3, h4⟩ := fwd hc
    constructor
    · intro hg
      exact ⟨h1, h2, h3, h4, hg, hc.client, hc.pos, hc.fits, hc.next⟩
    · intro hh
      exact hh.2.2.2.2.1
  · simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
    constructor
    · intro e
      cases e
    · rintro ⟨h1, h2, h3, h4, _, h5, h6, h7, h8⟩
      exact absurd (hmpr (bwd h1 h2 h3 h4 h5 h6 h7 h8)) hbt

/-! ## `merge_adjacent` -/

/-- The store `merge_adjacent` builds is `mergeNode` of the model. -/
theorem toM_merge {s : yata_store.YataStoreCore} {ci pos i4 i5 : Std.Usize}
    {c : yata_store.ClientEntryCore} {idx idx1 : Std.U32} {left right : yata_store.ItemCore}
    {i3 : Std.U64} {cbc : client_blocks.ClientBlocksCore}
    (hc : s.clients.val[ci.val]? = some c) (hitl : s.items.val[idx.val]? = some left)
    (hitr : s.items.val[idx1.val]? = some right) (hi4 : i4.val = idx.val)
    (hi5 : i5.val = idx.val) (hi3 : i3.val = left.len.val + right.len.val)
    (hbl : (blocksOf cbc) = delAt (blocksOf c.blocks) (pos.val + 1))
    (hend : cbc.end_clock = c.blocks.end_clock) :
    (MStore.mk
      (setLeft idx.val (toSlot right.right)
        (((s.items.set i4 { left with len := i3 }).set i5
          { left with len := i3, right := right.right }).val.map toItem))
      (toSlot s.start)
      ((s.clients.set ci { c with blocks := cbc }).val.map toClient)) =
      mergeNode (toM s) ci.val pos.val idx.val idx1.val := by
  have hset : ((s.items.set i4 { left with len := i3 }).set i5
      { left with len := i3, right := right.right }).val =
      s.items.val.set idx.val { left with len := i3, right := right.right } := by
    rw [alloc.vec.Vec.set_val_eq, alloc.vec.Vec.set_val_eq, hi4, hi5]
    apply ext_get?
    intro j
    rw [set_eq_upd, set_eq_upd, set_eq_upd, get?_upd, get?_upd, get?_upd]
    by_cases e : j = idx.val
    · rw [ite_eq_left e, ite_eq_left e, ite_eq_left e, e, hitl]
      rfl
    · rw [ite_eq_right e, ite_eq_right e, ite_eq_right e]
  unfold mergeNode
  rw [MStore.mk.injEq]
  refine ⟨?_, rfl, ?_⟩
  · rw [hset, rightOf_toM hitr, itemAt_toM hitr]
    congr 1
    refine map_set_get toItem hitl _ _ ?_
    simp [toItem, toId, toSlot, hi3]
  · rw [alloc.vec.Vec.set_val_eq]
    refine map_set_get toClient hc _ _ ?_
    show (⟨c.client.val, toBlocks cbc, cbc.end_clock.val⟩ : MClient) =
      ⟨c.client.val, delAt (toBlocks c.blocks) (pos.val + 1), c.blocks.end_clock.val⟩
    rw [hend, ClientBlocks.toBlocks_of_delAt hbl]

/-- What `merge_adjacent s id` does, by its answer.

`Ok true` is exactly a merge of the block that holds `id` with the block
after it. `YoctoSpec.mergeAt k` returns its list where `k` is past the last
pair or the two blocks cannot merge, so the equation `abs f s' = mergeAt k
(abs f s)` alone would also hold of a call that merged nothing: `merged`
pins `k` to the block that holds `id`, says that it and its right neighbour
can merge, and that the sequence lost one block.

Any other answer leaves the store as it was. The theorem does not say when
the answer is `Ok false` rather than `Ok true`: that the two blocks could
not merge, or that the block has no successor, is not stated (the tests
cover the answers). -/
structure MergeAdjacentPost (s : yata_store.YataStoreCore) (id : yata_store.IdCore)
    (r : core.result.Result Bool client_blocks.StoreError)
    (s' : yata_store.YataStoreCore) : Prop where
  inv : Inv s'
  /-- it merged: the block `a` at `k` holds `id`, the block `b` at `k + 1`
  can merge with it, the blocks are `YoctoSpec.mergeAt k` of the ones there
  were, and there is one block less -/
  merged : r = core.result.Result.Ok true →
    ∃ k : Nat, ∀ f : YoctoSpec.Id → Char, ∃ a b : YoctoSpec.Block,
      (abs f s)[k]? = some a ∧ (abs f s)[k + 1]? = some b ∧
      (a.id.client = id.client.val ∧ a.id.clock ≤ id.clock.val ∧
        id.clock.val < a.id.clock + a.len) ∧
      YoctoSpec.canMerge a b = true ∧
      abs f s' = YoctoSpec.mergeAt k (abs f s) ∧
      (abs f s').length + 1 = (abs f s).length
  /-- any other answer (it did not merge, or the store does not hold the
  id): the store is as it was -/
  same : r ≠ core.result.Result.Ok true → s' = s

/-- Whatever `merge_adjacent` answers, the store stands for the same
document: the same clocks in the same order, and the same deletions. -/
theorem MergeAdjacentPost.doc {s s' : yata_store.YataStoreCore} {id : yata_store.IdCore}
    {r : core.result.Result Bool client_blocks.StoreError} (h : MergeAdjacentPost s id r s')
    (f : YoctoSpec.Id → Char) :
    YoctoSpec.toDoc (abs f s') = YoctoSpec.toDoc (abs f s) := by
  by_cases e : r = core.result.Result.Ok true
  · obtain ⟨k, hk⟩ := h.merged e
    obtain ⟨_, _, _, _, _, _, hm, _⟩ := hk f
    rw [hm]
    exact YoctoSpec.toDoc_mergeAt k _
  · rw [h.same e]

theorem sameKind_dead {a b : client_blocks.BlockKindCore}
    (h : ClientBlocks.sameKind a b = true) : (toKind a).dead = (toKind b).dead := by
  revert h
  cases a <;> cases b <;> simp [ClientBlocks.sameKind, toKind, MKind.dead]

/-- **`merge_adjacent` refines `YoctoSpec.mergeAt`**, at the block that holds
the id it is given. -/
theorem merge_adjacent_spec (s : yata_store.YataStoreCore) (id : yata_store.IdCore)
    (h : Inv s) :
    yata_store.YataStoreCore.merge_adjacent s id ⦃ r s' => MergeAdjacentPost s id r s' ⦄ := by
  unfold yata_store.YataStoreCore.merge_adjacent
  have same : ∀ r : core.result.Result Bool client_blocks.StoreError,
      r ≠ core.result.Result.Ok true → MergeAdjacentPost s id r s :=
    fun r hr => ⟨h, fun e => absurd e hr, fun _ => rfl⟩
  have hfalse : (core.result.Result.Ok false :
      core.result.Result Bool client_blocks.StoreError) ≠ core.result.Result.Ok true := by
    intro e
    cases e
  step with locate_spec s id h as ⟨o, ho⟩
  rcases ho with ⟨rfl, hno⟩ | ⟨ci, pos, c, b, rfl, hc, hb, hat⟩
  · simp only [spec_ok, uncurry'_pair]
    exact same _ (fun e => nomatch e)
  · simp only []
    have hposlt := get?_lt hb
    have hbnd := length_blocksOf_le c.blocks
    step as ⟨next_pos, hnext⟩
    have hnv : next_pos.val = pos.val + 1 := by scalar_tac
    have hclt := get?_lt hc
    step as ⟨cec, hcec⟩
    have hx := get?_of_getElem hclt hcec
    rw [hc] at hx
    cases hx
    step as ⟨n, hn⟩
    by_cases hlast : next_pos >= n
    · simp only [hlast, ↓reduceIte, spec_ok, uncurry'_pair]
      exact same _ hfalse
    · simp only [hlast, ↓reduceIte]
      have hnlt : next_pos.val < (blocksOf c.blocks).length := by scalar_tac
      step as ⟨brc, hbrc⟩
      have hy := get?_of_getElem hposlt hbrc
      rw [hb] at hy
      cases hy
      step as ⟨b1, hbrc1⟩
      have hb1 := get?_of_getElem hnlt hbrc1
      rw [hnv] at hb1
      step as ⟨sk, hsk⟩
      by_cases hskt : sk = true
      · simp only [hskt, ↓reduceIte]
        have hsame : ClientBlocks.sameKind b.kind b1.kind = true := by
          rw [← hsk]
          exact hskt
        step as ⟨o1, ho1⟩
        subst ho1
        cases hk : kindSlot b.kind with
        | none =>
          simp only [spec_ok, uncurry'_pair]
          exact same _ hfalse
        | some idx =>
          simp only []
          step as ⟨o2, ho2⟩
          subst ho2
          cases hk1 : kindSlot b1.kind with
          | none =>
            simp only [spec_ok, uncurry'_pair]
            exact same _ hfalse
          | some idx1 =>
            simp only []
            have hmem : toClient c ∈ (toM s).clients := mem_toM_clients (get?_mem hc)
            have hcm := toM_clients_at hc
            have hbm := toClient_block hb
            have hbm1 := toClient_block hb1
            have hslot : (toBlock b).kind.slot = some idx.val := by
              show (toKind b.kind).slot = some idx.val
              rw [← kindSlot_val, hk]
              rfl
            have hslot1 : (toBlock b1).kind.slot = some idx1.val := by
              show (toKind b1.kind).slot = some idx1.val
              rw [← kindSlot_val, hk1]
              rfl
            obtain ⟨j0, x, hs0, hx0, hxid, hxlen, _, hiord, hxpos⟩ :=
              YataModel.WF.block_item h hmem hbm
            rw [hslot] at hs0
            cases hs0
            obtain ⟨j1, y, hs1, hy0, _, hylen, _, hiord1, _⟩ :=
              YataModel.WF.block_item h hmem hbm1
            rw [hslot1] at hs1
            cases hs1
            have hidx : idx.val < s.items.val.length := order_bound h hiord
            have hidx1 : idx1.val < s.items.val.length := order_bound h hiord1
            step as ⟨i1, hi1⟩
            have hi1v : i1.val = idx.val := by scalar_tac
            have hi1lt : i1.val < s.items.val.length := by omega
            step as ⟨left, hleft⟩
            have hitl := get?_of_getElem hi1lt hleft
            rw [hi1v] at hitl
            step as ⟨i2, hi2⟩
            have hi2v : i2.val = idx1.val := by scalar_tac
            have hi2lt : i2.val < s.items.val.length := by omega
            step as ⟨right, hright⟩
            have hitr := get?_of_getElem hi2lt hright
            rw [hi2v] at hitr
            have hxl : x = (toItem left).core := by
              rw [coreAt_toM hitl] at hx0
              exact (Option.some.inj hx0).symm
            have hyr : y = (toItem right).core := by
              rw [coreAt_toM hitr] at hy0
              exact (Option.some.inj hy0).symm
            -- the clocks of the two blocks: no subtraction or addition overflows
            have htl := YataModel.WF.timeline h (toClient c) hmem
            have hE := htl.end_le_stop (pos.val + 1)
            have hEp : endAt (toClient c).blocks (toClient c).stop pos.val =
                (toBlock b1).clock := by
              unfold endAt
              rw [hbm1]
            have hab : (toBlock b).clock < (toBlock b1).clock :=
              htl.sorted pos.val (pos.val + 1) _ _ (by omega) hbm hbm1
            have hbE := htl.lt_end hbm1
            have hllen : left.len.val = (toBlock b1).clock - (toBlock b).clock := by
              have e := hxlen
              rw [hxl, hEp] at e
              exact e
            have hlclk : left.id.clock.val = (toBlock b).clock := by
              have e := congrArg YoctoSpec.Id.clock hxid
              rw [hxl] at e
              exact e
            have hrlen : right.len.val =
                endAt (toClient c).blocks (toClient c).stop (pos.val + 1) -
                  (toBlock b1).clock := by
              have e := hylen
              rw [hyr] at e
              exact e
            have hstop : (toClient c).stop ≤ Std.U64.max := by
              show c.blocks.end_clock.val ≤ Std.U64.max
              scalar_tac
            have hsum : left.len.val + right.len.val ≤ Std.U64.max := by omega
            step with continues_spec left right idx idx1 as ⟨cont, hcont⟩
            by_cases hct : cont = true
            · simp only [hct, ↓reduceIte]
              obtain ⟨hlr, _, hol, hor, hgc, _⟩ := hcont.mp hct
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
                have e : s.clients.set ci { c with blocks := c.blocks } = s.clients := by
                  apply alloc.vec.Vec.ext
                  rw [alloc.vec.Vec.set_val_eq]
                  exact set_eq_self hc
                show MergeAdjacentPost s id (core.result.Result.Err error)
                  ({ s with clients := s.clients.set ci { c with blocks := c.blocks } })
                rw [e]
                exact same _ (fun e => nomatch e)
              | Ok u =>
                obtain ⟨_, _, _, _, _, hbl, hend⟩ := hpost.ok rfl
                simp only []
                step as ⟨i3, hi3⟩
                have hi3v : i3.val = left.len.val + right.len.val := by scalar_tac
                step as ⟨i4, hi4⟩
                have hi4v : i4.val = idx.val := by scalar_tac
                have hi4lt : i4.val < s.items.val.length := by omega
                step as ⟨ic, back1, hic, hback1⟩
                have hic' := get?_of_getElem hi4lt hic
                rw [hi4v, hitl] at hic'
                cases hic'
                subst hback1
                step as ⟨i5, hi5⟩
                have hi5v : i5.val = idx.val := by scalar_tac
                have hlen5 : (s.items.set i4 { left with len := i3 }).val.length =
                    s.items.val.length := by
                  rw [alloc.vec.Vec.set_val_eq, List.length_set]
                have hi5lt : i5.val < (s.items.set i4 { left with len := i3 }).val.length := by
                  rw [hlen5]
                  omega
                step as ⟨ic1, back2, hic1, hback2⟩
                have hic1' := get?_of_getElem hi5lt hic1
                rw [alloc.vec.Vec.set_val_eq, hi5v, hi4v, set_eq_upd, get?_upd_self, hitl]
                  at hic1'
                have eic1 : ic1 = { left with len := i3 } := (Option.some.inj hic1').symm
                subst eic1
                subst hback2
                have hrr : ∀ i, right.right = some i → i.val < s.items.val.length := by
                  intro i hi
                  obtain ⟨k, hk'⟩ := mem_get? hiord1
                  have hr := h.chain.right k idx1.val hk'
                  have e : rightOf (toM s).items idx1.val = some i.val := by
                    rw [rightOf_toM hitr, hi]
                    rfl
                  rw [e] at hr
                  exact order_bound h (get?_mem hr.symm)
                have hpre : ∀ i, right.right = some i →
                    i.val < ({ s with
                      items := (s.items.set i4 { left with len := i3 }).set i5
                        { left with len := i3, right := right.right }
                      clients := s.clients.set ci { c with blocks := cbc } } :
                        yata_store.YataStoreCore).items.val.length := by
                  intro i hi
                  show i.val < ((s.items.set i4 { left with len := i3 }).set i5
                    { left with len := i3, right := right.right }).val.length
                  rw [alloc.vec.Vec.set_val_eq, List.length_set, hlen5]
                  exact hrr i hi
                step with set_left_spec _ right.right idx hpre as ⟨self1, hself1, _, _⟩
                have hm : toM self1 = mergeNode (toM s) ci.val pos.val idx.val idx1.val := by
                  rw [hself1]
                  exact toM_merge hc hitl hitr hi4v hi5v hi3v hbl hend
                have hlrM : rightOf (toM s).items idx.val = some idx1.val := by
                  rw [rightOf_toM hitl]
                  exact hlr
                have holM : y.originL = some ⟨x.id.client, x.id.clock + x.len - 1⟩ := by
                  rw [hyr, hxl]
                  exact hol
                have horM : x.originR = y.originR := by
                  rw [hxl, hyr]
                  exact hor
                have hgcM : x.gc = y.gc := by
                  rw [hxl, hyr]
                  exact hgc
                have hdelM : (toBlock b).kind.dead = (toBlock b1).kind.dead :=
                  sameKind_dead hsame
                obtain ⟨k, _, _, hwf, _⟩ :=
                  mergeNode_spec h hcm hbm hbm1 hslot hslot1 hx0 hy0 hlrM
                obtain ⟨k2, _, hblocks⟩ :=
                  blocks_mergeNode h hcm hbm hbm1 hslot hslot1 hx0 hy0 hlrM holM horM hdelM
                    hgcM
                refine ⟨?_, fun _ => ⟨k2, fun f => ?_⟩, fun hne => absurd rfl hne⟩
                · unfold Inv
                  rw [hm]
                  exact hwf
                · obtain ⟨hA, hB, hcan, hmerge, hshort⟩ := hblocks f
                  -- the block that holds `id` is the one of the left item
                  have hge : (toBlock b).clock ≤ id.clock.val := hat.ge
                  have hlt : id.clock.val <
                      endAt (toClient c).blocks (toClient c).stop pos.val := hat.lt
                  have hxclk : x.id.clock = (toBlock b).clock :=
                    congrArg YoctoSpec.Id.clock hxid
                  have hxcl : x.id.client = id.client.val :=
                    (congrArg YoctoSpec.Id.client hxid).trans hat.client
                  refine ⟨blockOf f x, blockOf f y, hA, hB, ⟨hxcl, ?_, ?_⟩, hcan, ?_, ?_⟩
                  · show x.id.clock ≤ id.clock.val
                    rw [hxclk]
                    exact hge
                  · show id.clock.val < x.id.clock + (blockOf f x).len
                    rw [blockOf_len, hxclk, hxlen]
                    omega
                  · unfold abs
                    rw [hm]
                    exact hmerge
                  · unfold abs
                    rw [hm]
                    exact hshort
            · simp only [hct, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
              exact same _ hfalse
      · simp only [hskt, Bool.false_eq_true, ↓reduceIte, spec_ok, uncurry'_pair]
        exact same _ hfalse

/-! ## `visible_ids` -/

/-- A pair of `visible_ids` on the model: the id, and the length as a number. -/
def toPair (e : yata_store.IdCore × Std.U64) : YoctoSpec.Id × Nat := (toId e.1, e.2.val)

theorem filterMap_snoc_none {α β : Type} (g : α → Option β) (l : List α) (a : α)
    (h : g a = none) : (l ++ [a]).filterMap g = l.filterMap g := by
  rw [List.filterMap_append]
  simp [h]

theorem filterMap_snoc_some {α β : Type} (g : α → Option β) (l : List α) (a : α) (b : β)
    (h : g a = some b) : (l ++ [a]).filterMap g = l.filterMap g ++ [b] := by
  rw [List.filterMap_append]
  simp [h]

/-- The loop of `visible_ids` at position `k` of the sequence. -/
structure Visiting (s : yata_store.YataStoreCore) (cursor : Option Std.U32)
    (out : List (yata_store.IdCore × Std.U64)) (k : Nat) : Prop where
  bound : k ≤ (order (toM s)).length
  here : toSlot cursor = (order (toM s))[k]?
  answer : out.map toPair =
    ((order (toM s)).take k).filterMap (fun i => visOf (itemAt (toM s).items i))
  short : out.length ≤ k

theorem visible_ids_loop_spec (s : yata_store.YataStoreCore) (h : Inv s)
    (cursor : Option Std.U32) (out : alloc.vec.Vec (yata_store.IdCore × Std.U64)) (k : Nat)
    (hinv : Visiting s cursor out.val k) :
    yata_store.YataStoreCore.visible_ids_loop cursor s.items out ⦃ r =>
      r.val.map toPair = visM (toM s) ⦄ := by
  unfold yata_store.YataStoreCore.visible_ids_loop
  refine loop.spec_decr_nat
    (fun ((cf, _) : Option Std.U32 × alloc.vec.Vec (yata_store.IdCore × Std.U64)) =>
      restOf (order (toM s)) cf)
    (fun ((cf, ov) : Option Std.U32 × alloc.vec.Vec (yata_store.IdCore × Std.U64)) =>
      ∃ k', Visiting s cf ov.val k')
    (fun (r : alloc.vec.Vec (yata_store.IdCore × Std.U64)) =>
      r.val.map toPair = visM (toM s))
    _ (cursor, out) ?_ ⟨k, hinv⟩
  intro ⟨cf, ov⟩ ⟨k', hV⟩
  unfold yata_store.YataStoreCore.visible_ids_loop.body
  simp only
  cases cf with
  | none =>
    simp only [spec_ok]
    have hnone : (order (toM s))[k']? = none := hV.here.symm
    have hge : (order (toM s)).length ≤ k' := get?_none_le hnone
    rw [hV.answer, List.take_of_length_le hge]
    rfl
  | some current =>
    simp only []
    have hcur : (order (toM s))[k']? = some current.val := hV.here.symm
    have hklt : k' < (order (toM s)).length := get?_lt hcur
    have hmem : current.val ∈ order (toM s) := get?_mem hcur
    have hcb : current.val < s.items.val.length := order_bound h hmem
    have hol := order_le_items h
    step as ⟨i, hi⟩
    have hiv : i.val = current.val := by scalar_tac
    have hilt : i.val < s.items.val.length := by omega
    step as ⟨item, hitem⟩
    have hit := get?_of_getElem hilt hitem
    rw [hiv] at hit
    have hnext : toSlot item.right = (order (toM s))[k' + 1]? := by
      rw [← rightOf_toM hit]
      exact h.chain.right k' _ hcur
    have htake : (order (toM s)).take (k' + 1) = (order (toM s)).take k' ++ [current.val] :=
      take_succ_get hcur
    have hmeas : restOf (order (toM s)) item.right < restOf (order (toM s)) (some current) :=
      restOf_next h hcur hit
    by_cases hd : item.deleted = true
    · simp only [hd, ↓reduceIte, spec_ok]
      have hvis : visOf (itemAt (toM s).items current.val) = none := by
        rw [itemAt_toM hit]
        show (if item.deleted = true then none else _) = none
        rw [ite_eq_left hd]
      refine ⟨⟨k' + 1, by omega, hnext, ?_, by have := hV.short; omega⟩, hmeas⟩
      rw [htake, filterMap_snoc_none (fun i => visOf (itemAt (toM s).items i)) _ _ hvis]
      exact hV.answer
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      have hshort := hV.short
      have hov : ov.val.length < Std.Usize.max := by scalar_tac
      step as ⟨out1, hout1⟩
      have hvis : visOf (itemAt (toM s).items current.val) =
          some (toPair (item.id, item.len)) := by
        rw [itemAt_toM hit]
        show (if item.deleted = true then none else _) = some _
        rw [ite_eq_right hd]
        rfl
      refine ⟨⟨k' + 1, by omega, hnext, ?_, ?_⟩, hmeas⟩
      · rw [hout1, htake,
          filterMap_snoc_some (fun i => visOf (itemAt (toM s).items i)) _ _ _ hvis,
          List.map_append, hV.answer]
        rfl
      · rw [hout1, List.length_append, List.length_singleton]
        omega

/-- **`visible_ids` answers the visible items of the sequence**: the first id
and the length of every item that is not deleted, in order. -/
theorem visible_ids_spec (s : yata_store.YataStoreCore) (h : Inv s) :
    yata_store.YataStoreCore.visible_ids s ⦃ v => v.val.map toPair = visM (toM s) ⦄ := by
  unfold yata_store.YataStoreCore.visible_ids
  refine visible_ids_loop_spec s h s.start _ 0 ⟨Nat.zero_le _, h.chain.head, ?_, ?_⟩
  · simp
  · simp

/-- The same on the block sequence the store stands for: the answer names the
blocks that are not deleted, and, clock by clock, the visible ids of the
document. -/
theorem visible_ids_abs (s : yata_store.YataStoreCore) (h : Inv s) :
    yata_store.YataStoreCore.visible_ids s ⦃ v => ∀ f : YoctoSpec.Id → Char,
      v.val.map toPair =
        ((abs f s).filter (fun B => !B.deleted)).map (fun B => (B.id, B.len)) ∧
      expandIds (v.val.map toPair) = (YoctoSpec.toDoc (abs f s)).visible ⦄ := by
  refine spec_mono (visible_ids_spec s h) ?_
  intro v hv f
  rw [hv]
  exact ⟨visM_blocks f (toM s), expand_visM h⟩

/-! ## The read accessors

The fields of `YataStoreCore` are private in Rust; `items`, `start` and
`clients` read them. They are total on every store and answer the field as it
is: nothing of a store can be changed through them. -/

/-- `items` answers the arena. -/
theorem items_spec (s : yata_store.YataStoreCore) :
    yata_store.YataStoreCore.impl.items s ⦃ v => v.val = s.items.val ⦄ := by
  unfold yata_store.YataStoreCore.impl.items
  simp [spec_ok, alloc.vec.Vec.deref]

/-- `start` answers the first item of the sequence. -/
theorem start_spec (s : yata_store.YataStoreCore) :
    yata_store.YataStoreCore.impl.start s ⦃ o => o = s.start ⦄ := by
  unfold yata_store.YataStoreCore.impl.start
  simp [spec_ok]

/-- `clients` answers the timelines. -/
theorem clients_spec (s : yata_store.YataStoreCore) :
    yata_store.YataStoreCore.impl.clients s ⦃ v => v.val = s.clients.val ⦄ := by
  unfold yata_store.YataStoreCore.impl.clients
  simp [spec_ok, alloc.vec.Vec.deref]

end YoctoCore.Properties.YataStore
