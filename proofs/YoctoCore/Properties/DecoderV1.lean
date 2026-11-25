import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.Varint
import YoctoCore.Properties.DeleteSet
import YoctoCore.Properties.StateVector
import YoctoCore.Properties.Utf16

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 2000000

namespace YoctoCore.Properties.DecoderV1

section Helpers

open Lean Elab Tactic Meta in
private def casesFirstHyp (pred : Expr → Bool) : TacticM Unit := do
  withMainContext do
    for ldecl in (← getLCtx) do
      if !ldecl.isImplementationDetail then
        let ty ← instantiateMVars ldecl.type
        if pred ty then
          let g ← getMainGoal
          let subgoals ← g.cases ldecl.fvarId
          replaceMainGoal (subgoals.map (·.mvarId)).toList
          return
    throwError "no matching hypothesis"

open Lean Elab Tactic Meta in
elab "cases_result_err" : tactic =>
  casesFirstHyp fun t => t.isAppOfArity ``core.result.Result 2

open Lean Elab Tactic Meta in
elab "cases_prod_hyp" : tactic =>
  casesFirstHyp fun t => t.isAppOfArity ``Prod 2

private theorem ite_wp_split {α : Type _} (c : Prop) [Decidable c]
    (t e : Result α) (P : α → Prop)
    (ht : c → t ⦃ P ⦄) (he : ¬c → e ⦃ P ⦄) :
    (if c then t else e) ⦃ P ⦄ := by
  split_ifs with h <;> [exact ht h; exact he h]

end Helpers

private theorem core_ops_try_branch_ok {α ε : Type _} (x : α) :
    core.result.Result.Insts.CoreOpsTry.branch
      (core.result.Result.Ok x : core.result.Result α ε) =
      ok (core.ops.control_flow.ControlFlow.Continue x) := rfl

private theorem core_ops_try_branch_err {α ε : Type _} (e : ε) :
    core.result.Result.Insts.CoreOpsTry.branch
      (core.result.Result.Err e : core.result.Result α ε) =
      ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e)) := rfl

private theorem core_ops_try_from_residual_err {α ε : Type _} (e : ε) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual α
      (core.convert.FromSame ε) (core.result.Result.Err e) =
      ok (core.result.Result.Err e) := by
  unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
  simp [core.convert.FromSame]

private theorem is_none_eq_true_iff {α : Type _} (o : Option α) :
    core.option.Option.is_none o = true ↔ o = none := by
  cases o <;> simp [core.option.Option.is_none]

private def errFlag (err : Option CodecError) : Nat :=
  if err.isNone then 1 else 0

private def stepFlag (done1 : Bool) (err : Option CodecError) : Nat :=
  if done1 || !err.isNone then 0 else 1

@[simp] private theorem errFlag_none : errFlag none = 1 := rfl
@[simp] private theorem errFlag_some (e : CodecError) : errFlag (some e) = 0 := rfl
@[simp] private theorem stepFlag_false_none : stepFlag false none = 1 := rfl
@[simp] private theorem stepFlag_some (b : Bool) (e : CodecError) : stepFlag b (some e) = 0 := by
  cases b <;> rfl

@[local step]
theorem checked_usize_from_u64_total (v : Std.U64) :
    decoder_v1.checked_usize_from_u64 v ⦃ _ => True ⦄ := by
  unfold decoder_v1.checked_usize_from_u64
  step*

theorem check_fits_total (remaining count : Std.Usize) (min_bytes : Std.U64)
    (hMin : 0 < min_bytes.val) :
    decoder_v1.check_fits remaining count min_bytes ⦃ _ => True ⦄ := by
  unfold decoder_v1.check_fits
  step*

@[local step]
private theorem check_fits_2_total (remaining count : Std.Usize) :
    decoder_v1.check_fits remaining count 2#u64 ⦃ _ => True ⦄ :=
  check_fits_total remaining count 2#u64 (by decide)

@[local step]
private theorem check_fits_min_client_total (remaining count : Std.Usize) :
    decoder_v1.check_fits remaining count decoder_v1.MIN_CLIENT_BYTES ⦃ _ => True ⦄ :=
  check_fits_total remaining count decoder_v1.MIN_CLIENT_BYTES
    (by simp [decoder_v1.MIN_CLIENT_BYTES])

@[local step]
private theorem check_fits_min_struct_total (remaining count : Std.Usize) :
    decoder_v1.check_fits remaining count decoder_v1.MIN_STRUCT_BYTES ⦃ _ => True ⦄ :=
  check_fits_total remaining count decoder_v1.MIN_STRUCT_BYTES
    (by simp [decoder_v1.MIN_STRUCT_BYTES])

@[local step]
private theorem check_fits_min_delete_client_total (remaining count : Std.Usize) :
    decoder_v1.check_fits remaining count decoder_v1.MIN_DELETE_CLIENT_BYTES ⦃ _ => True ⦄ :=
  check_fits_total remaining count decoder_v1.MIN_DELETE_CLIENT_BYTES
    (by simp [decoder_v1.MIN_DELETE_CLIENT_BYTES])

@[local step]
private theorem check_fits_min_delete_range_total (remaining count : Std.Usize) :
    decoder_v1.check_fits remaining count decoder_v1.MIN_DELETE_RANGE_BYTES ⦃ _ => True ⦄ :=
  check_fits_total remaining count decoder_v1.MIN_DELETE_RANGE_BYTES
    (by simp [decoder_v1.MIN_DELETE_RANGE_BYTES])

@[local step]
private theorem check_fits_min_entry_total (remaining count : Std.Usize) :
    decoder_v1.check_fits remaining count decoder_v1.MIN_ENTRY_BYTES ⦃ _ => True ⦄ :=
  check_fits_total remaining count decoder_v1.MIN_ENTRY_BYTES
    (by simp [decoder_v1.MIN_ENTRY_BYTES])

@[local step]
private theorem check_fits_min_obj_entry_total (remaining count : Std.Usize) :
    decoder_v1.check_fits remaining count decoder_v1.MIN_OBJECT_ENTRY_BYTES ⦃ _ => True ⦄ :=
  check_fits_total remaining count decoder_v1.MIN_OBJECT_ENTRY_BYTES
    (by simp [decoder_v1.MIN_OBJECT_ENTRY_BYTES])

@[local step]
theorem checked_add_usize_total (a b : Std.Usize) :
    decoder_v1.checked_add_usize a b ⦃ r =>
      match r with
      | .Ok s => s.val = a.val + b.val
      | .Err _ => True ⦄ := by
  unfold decoder_v1.checked_add_usize
  step* <;> try simp [spec_ok]
  try scalar_tac

@[local step]
theorem read_u8_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_u8_at input pos ⦃ r =>
      match r with
      | .Ok (_, nxt) => pos.val < nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_u8_at
  step* <;> try simp [spec_ok]
  try exact ⟨by scalar_tac, by scalar_tac⟩

@[local step]
theorem read_var_u64_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_var_u64_at input pos ⦃ r =>
      match r with
      | .Ok (_, nxt) => nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_var_u64_at
  dsimp only
  split_ifs with hgt
  · simp [spec_ok]
  · step as ⟨s, hs⟩
    step with Varint.decode_var_u64_total s as ⟨r⟩
    cases r with
    | Ok val =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val with ⟨val1, used⟩
      step as ⟨i2, hi2⟩
      split_ifs with hof
      · simp [spec_ok]
      · step as ⟨i3, hi3⟩
        simp [spec_ok]
        scalar_tac
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem read_var_i32_with_sign_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_var_i32_with_sign_at input pos ⦃ _ => True ⦄ := by
  unfold decoder_v1.read_var_i32_with_sign_at
  dsimp only
  split_ifs with hgt
  · simp [spec_ok]
  · step as ⟨s, hs⟩
    step with Varint.decode_var_i32_with_sign_total s as ⟨r⟩
    cases r with
    | Ok val =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val with ⟨v, used⟩
      step*
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem read_bytes_slice_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_bytes_slice_at input pos ⦃ r =>
      match r with
      | .Ok (s, e) => s.val ≤ e.val ∧ e.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_bytes_slice_at
  step with read_var_u64_at_total input pos as ⟨r, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨len_u64, next⟩
    dsimp only at hr ⊢
    step with checked_usize_from_u64_total len_u64 as ⟨r1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      step as ⟨i1, hi1⟩
      split_ifs with hgt
      · simp [spec_ok]
      · step as ⟨i2, hi2⟩
        simp [spec_ok]
        exact ⟨by scalar_tac, by scalar_tac⟩
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem read_str_slice_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_str_slice_at input pos ⦃ r =>
      match r with
      | .Ok (s, e) => s.val ≤ e.val ∧ e.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_str_slice_at
  step with read_bytes_slice_at_total input pos as ⟨r, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨start, «end»⟩
    dsimp only at hr ⊢
    step as ⟨s, hs⟩
    step with Utf16.is_valid_utf8_total s as ⟨b⟩
    split_ifs <;> simp [spec_ok]
    exact ⟨by scalar_tac, by scalar_tac⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem skip_fixed_at_total (input : Slice Std.U8) (pos width : Std.Usize) :
    decoder_v1.skip_fixed_at input pos width ⦃ _ => True ⦄ := by
  unfold decoder_v1.skip_fixed_at
  step*

@[local step]
theorem advance_clock_total (clock len : Std.U64) :
    decoder_v1.advance_clock clock len ⦃ _ => True ⦄ := by
  unfold decoder_v1.advance_clock
  split_ifs with hz
  · simp [spec_ok]
  · have hMax : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, Std.U64.numBits]
    have hCoreMax : core.num.U64.MAX.val = 2 ^ 64 - 1 := by decide
    have hClkLe : clock.val ≤ core.num.U64.MAX.val := by
      have := clock.hBounds
      have hnb : UScalarTy.U64.numBits = 64 := rfl
      rw [hnb] at this
      omega
    step as ⟨i, hi⟩
    split_ifs <;> step*

@[local step]
theorem contains_u64_total (items : Slice Std.U64) (target : Std.U64) :
    decoder_v1.contains_u64 items target ⦃ _ => True ⦄ := by
  unfold decoder_v1.contains_u64
  unfold decoder_v1.contains_u64_loop
  refine loop.spec_decr_nat
    (fun i => items.length - i.val) (fun i => i.val ≤ items.length)
    (fun _ => True) _ 0#usize ?_ (by scalar_tac)
  intro i hi
  unfold decoder_v1.contains_u64_loop.body
  dsimp only
  split_ifs with hlt
  · step* <;> simp [spec_ok] <;> scalar_tac
  · simp [spec_ok]

@[local step]
theorem read_sv_entry_total (input : Slice Std.U8) (cur : Std.Usize) :
    decoder_v1.read_sv_entry input cur ⦃ _ => True ⦄ := by
  unfold decoder_v1.read_sv_entry
  step with read_var_u64_at_total input cur as ⟨r⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨client, p1⟩
    step with read_var_u64_at_total input p1 as ⟨r1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val1 with ⟨clock, p2⟩
      simp [spec_ok]
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem read_state_vector_v1_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_state_vector_v1 input pos ⦃ _ => True ⦄ := by
  unfold decoder_v1.read_state_vector_v1
  dsimp only
  split_ifs with hgt
  · simp [spec_ok]
  · step with read_var_u64_at_total input pos as ⟨r, hr⟩
    cases r with
    | Ok val =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val with ⟨count_u64, cur⟩
      dsimp only at hr
      step with checked_usize_from_u64_total count_u64 as ⟨r1⟩
      cases r1 with
      | Ok val1 =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        step as ⟨i2, hi2⟩
        step with check_fits_2_total i2 val1 as ⟨r2⟩
        cases r2 with
        | Ok _ =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          step with StateVector.new_spec as ⟨sv, hsvCan, hsvLen, _⟩
          have hLoop :
              decoder_v1.read_state_vector_v1_loop input cur val1 sv none 0#usize ⦃ _ => True ⦄ := by
            unfold decoder_v1.read_state_vector_v1_loop
            let inv : Std.Usize × state_vector.StateVectorCore × Option CodecError × Std.Usize → Prop :=
              fun (_, sv1, _, i) =>
                StateVector.Canonical sv1 ∧ i.val ≤ val1.val ∧ sv1.entries.length ≤ i.val
            refine loop.spec_decr_nat
              (fun (_, _, err, i) => errFlag err + (val1.val - i.val))
              inv (fun _ => True) _ (cur, sv, none, 0#usize) ?_
              ⟨hsvCan, by scalar_tac, by omega⟩
            intro ⟨cur1, sv1, err1, i1⟩ ⟨hCan1, hiLe, hLen1⟩
            unfold decoder_v1.read_state_vector_v1_loop.body
            dsimp only
            split_ifs with hlt hnone
            · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
              subst herr
              step with read_sv_entry_total input cur1 as ⟨r3⟩
              cases r3 with
              | Ok t =>
                rcases t with ⟨client, clock, _⟩
                dsimp only
                have hCap : sv1.entries.length < Std.Usize.max := by scalar_tac
                step with StateVector.set_spec sv1 client clock hCan1 hCap as ⟨sv2, hsv2Can, hsv2Len, _, _⟩
                step as ⟨i3, hi3⟩
                try simp only [spec_ok]
                exact ⟨⟨hsv2Can, by scalar_tac, by omega⟩, by simp [hi3]; scalar_tac⟩
              | Err e =>
                try simp only [spec_ok]
                exact ⟨⟨hCan1, hiLe, hLen1⟩, by simp⟩
            · simp [spec_ok]
            · simp [spec_ok]
          step with hLoop as ⟨cur1, sv1, err⟩
          cases err <;> simp [spec_ok]
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

theorem decode_state_vector_v1_total (input : Slice Std.U8) :
    decoder_v1.decode_state_vector_v1 input ⦃ _ => True ⦄ := by
  unfold decoder_v1.decode_state_vector_v1
  step with read_state_vector_v1_total input 0#usize as ⟨r⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]
    rcases val with ⟨sv, «end»⟩
    simp only [Aeneas.Std.uncurry]
    split_ifs <;> simp [spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem read_one_delete_range_total (input : Slice Std.U8) (cur : Std.Usize) :
    decoder_v1.read_one_delete_range input cur ⦃ _ => True ⦄ := by
  unfold decoder_v1.read_one_delete_range
  step with read_var_u64_at_total input cur as ⟨r⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨start, q1⟩
    step with read_var_u64_at_total input q1 as ⟨r1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val1 with ⟨len, q2⟩
      have hMax : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, Std.U64.numBits]
      have hCoreMax : core.num.U64.MAX.val = 2 ^ 64 - 1 := by decide
      have hStLe : start.val ≤ core.num.U64.MAX.val := by
        have := start.hBounds
        have hnb : UScalarTy.U64.numBits = 64 := rfl
        rw [hnb] at this
        omega
      step as ⟨i, hi⟩
      split_ifs <;> step*
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

theorem read_delete_ranges_for_client_spec
    (input : Slice Std.U8) (start_pos : Std.Usize) (client : Std.U64)
    (range_count : Std.Usize) (ds : delete_set.DeleteSetCore)
    (hCan : DeleteSet.Canonical ds)
    (hCap : DeleteSet.totalRanges ds + range_count.val ≤ Std.Usize.max) :
    decoder_v1.read_delete_ranges_for_client input start_pos client range_count ds ⦃ (_, ds1) =>
      DeleteSet.Canonical ds1 ∧
      DeleteSet.totalRanges ds1 ≤ DeleteSet.totalRanges ds + range_count.val ⦄ := by
  unfold decoder_v1.read_delete_ranges_for_client
  let inv : delete_set.DeleteSetCore × Std.Usize × Std.Usize × Option CodecError → Prop :=
    fun (ds1, _, rIdx, _) =>
      DeleteSet.Canonical ds1 ∧ rIdx.val ≤ range_count.val ∧
      DeleteSet.totalRanges ds1 ≤ DeleteSet.totalRanges ds + rIdx.val
  have hLoop :
      decoder_v1.read_delete_ranges_for_client_loop input client range_count ds start_pos 0#usize none ⦃ (ds1, _, _) =>
        DeleteSet.Canonical ds1 ∧
        DeleteSet.totalRanges ds1 ≤ DeleteSet.totalRanges ds + range_count.val ⦄ := by
    unfold decoder_v1.read_delete_ranges_for_client_loop
    refine loop.spec_decr_nat
      (fun (_, _, rIdx, err) => errFlag err + (range_count.val - rIdx.val))
      inv _ _ (ds, start_pos, 0#usize, none) ?_ ⟨hCan, by scalar_tac, by scalar_tac⟩
    intro ⟨ds1, cur1, rIdx, err1⟩ ⟨hCan1, hrLe, hTot1⟩
    unfold decoder_v1.read_delete_ranges_for_client_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with read_one_delete_range_total input cur1 as ⟨r⟩
      cases r with
      | Ok t =>
        rcases t with ⟨start, «end», q2⟩
        dsimp only
        have hDs1 :
            (if start != «end»
             then delete_set.DeleteSetCore.insert ds1 client start «end»
             else ok ds1)
              ⦃ ds2 => DeleteSet.Canonical ds2 ∧ DeleteSet.totalRanges ds2 ≤ DeleteSet.totalRanges ds1 + 1 ⦄ := by
          split_ifs with hne
          · have hCapStep : DeleteSet.totalRanges ds1 < Std.Usize.max := by scalar_tac
            step with DeleteSet.insert_spec ds1 client start «end» hCan1 hCapStep as ⟨ds2, hDs2Can, hDs2Tot, _⟩
            exact ⟨hDs2Can, hDs2Tot⟩
          · simp only [spec_ok]; exact ⟨hCan1, by omega⟩
        step with hDs1 as ⟨ds2, hDs2Can, hDs2Tot⟩
        step as ⟨rIdx1, hrIdx1⟩
        try simp only [spec_ok]
        refine ⟨⟨hDs2Can, by scalar_tac, by omega⟩, ?_⟩
        simp [hrIdx1]; scalar_tac
      | Err e =>
        try simp only [spec_ok]
        exact ⟨⟨hCan1, hrLe, hTot1⟩, by simp⟩
    · simp only [spec_ok]; exact ⟨hCan1, by omega⟩
    · simp only [spec_ok]; exact ⟨hCan1, by omega⟩
  step with hLoop as ⟨ds1, cur, err, hCan1, hTot1⟩
  cases err <;> simp [spec_ok] <;> exact ⟨hCan1, hTot1⟩

@[local step]
theorem read_delete_client_header_total
    (input : Slice Std.U8) (cur : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (total_entries : Std.Usize) :
    decoder_v1.read_delete_client_header input cur limits total_entries ⦃ r =>
      match r with
      | .Ok (_, rc, nxtEnt, _) =>
        nxtEnt.val = total_entries.val + rc.val ∧
        nxtEnt.val ≤ limits.max_collection_entries.val
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_delete_client_header
  step with read_var_u64_at_total input cur as ⟨r, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨client, p1⟩
    step with read_var_u64_at_total input p1 as ⟨r1, hr1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val1 with ⟨ranges_u64, p2⟩
      dsimp only at hr1
      step with checked_usize_from_u64_total ranges_u64 as ⟨r2⟩
      cases r2 with
      | Ok val2 =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        step with checked_add_usize_total total_entries val2 as ⟨r3, hr3⟩
        cases r3 with
        | Ok val3 =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          dsimp only at hr3
          split_ifs with hlim
          · simp [spec_ok]
          · step as ⟨i1, hi1⟩
            step with check_fits_min_delete_range_total i1 val2 as ⟨r4⟩
            cases r4 with
            | Ok _ =>
              simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
              simp [spec_ok]; exact ⟨hr3, by scalar_tac⟩
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem read_delete_set_v1_total
    (input : Slice Std.U8) (pos : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc : Std.Usize) :
    decoder_v1.read_delete_set_v1 input pos limits entries_acc ⦃ _ => True ⦄ := by
  unfold decoder_v1.read_delete_set_v1
  dsimp only
  split_ifs with hgt
  · simp [spec_ok]
  · step with read_var_u64_at_total input pos as ⟨r, hr⟩
    cases r with
    | Ok val =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val with ⟨clients_u64, cur⟩
      dsimp only at hr
      step with checked_usize_from_u64_total clients_u64 as ⟨r1⟩
      cases r1 with
      | Ok val1 =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        split_ifs with hlim
        · simp [spec_ok]
        · step as ⟨i2, hi2⟩
          step with check_fits_min_delete_client_total i2 val1 as ⟨r2⟩
          cases r2 with
          | Ok _ =>
            simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
            step with DeleteSet.new_spec as ⟨ds, hdsCan, _, hdsTot, _⟩
            have hLoop :
                decoder_v1.read_delete_set_v1_loop input limits.max_structs limits.max_clients
                  limits.max_collection_entries limits.max_any_depth limits.max_content_bytes
                  cur val1 ds entries_acc 0#usize 0#usize none ⦃ _ => True ⦄ := by
              unfold decoder_v1.read_delete_set_v1_loop
              let inv : Std.Usize × delete_set.DeleteSetCore × Std.Usize × Std.Usize × Std.Usize × Option CodecError → Prop :=
                fun (_, ds1, totEnt, _, cIdx, _) =>
                  DeleteSet.Canonical ds1 ∧ cIdx.val ≤ val1.val ∧ DeleteSet.totalRanges ds1 ≤ totEnt.val
              refine loop.spec_decr_nat
                (fun (_, _, _, _, cIdx, err) => errFlag err + (val1.val - cIdx.val))
                inv (fun _ => True) _ (cur, ds, entries_acc, 0#usize, 0#usize, none) ?_
                ⟨hdsCan, by scalar_tac, by omega⟩
              intro ⟨cur1, ds1, totEnt, totRng, cIdx, err1⟩ ⟨hCan1, hcLe, hTot1⟩
              unfold decoder_v1.read_delete_set_v1_loop.body
              dsimp only
              split_ifs with hlt hnone
              · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
                subst herr
                step with read_delete_client_header_total input cur1
                  { limits with } totEnt as ⟨r3, hr3⟩
                cases r3 with
                | Ok t =>
                  rcases t with ⟨client, rc, nxtEnt, next_cur⟩
                  dsimp only at hr3 ⊢
                  have hNxtLe : nxtEnt.val ≤ Std.Usize.max := by scalar_tac
                  have hCapStep : DeleteSet.totalRanges ds1 + rc.val ≤ Std.Usize.max := by omega
                  step with read_delete_ranges_for_client_spec input next_cur client rc ds1 hCan1 hCapStep
                    as ⟨r4, ds2, hDs2Can, hDs2Tot⟩
                  cases r4 with
                  | Ok next_cur2 =>
                    step with checked_add_usize_total totRng rc as ⟨r5⟩
                    cases r5 with
                    | Ok next_ranges =>
                      step as ⟨cIdx1, hcIdx1⟩
                      try simp only [spec_ok]
                      exact ⟨⟨hDs2Can, by scalar_tac, by omega⟩, by simp [hcIdx1]; scalar_tac⟩
                    | Err e =>
                      try simp only [spec_ok]
                      exact ⟨⟨hDs2Can, hcLe, by omega⟩, by simp⟩
                  | Err e =>
                    try simp only [spec_ok]
                    exact ⟨⟨hDs2Can, hcLe, by omega⟩, by simp⟩
                | Err e =>
                  try simp only [spec_ok]
                  exact ⟨⟨hCan1, hcLe, hTot1⟩, by simp⟩
              · simp [spec_ok]
              · simp [spec_ok]
            step with hLoop as ⟨cur1, ds1, totRng, err⟩
            cases err <;> simp [spec_ok]
          | Err e =>
            simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem pop_open_stack_spec («open» : Slice (Std.Usize × Bool))
    (hPos : 0 < «open».length) :
    decoder_v1.pop_open_stack «open» ⦃ next_open => next_open.length = «open».length - 1 ⦄ := by
  unfold decoder_v1.pop_open_stack
  step as ⟨target, htarget⟩
  have hTargetEq : target.val = «open».length - 1 := by scalar_tac
  have hLoop :
      decoder_v1.pop_open_stack_loop «open» (alloc.vec.Vec.new (Std.Usize × Bool)) 0#usize target
        ⦃ next_open => next_open.length = «open».length - 1 ⦄ := by
    unfold decoder_v1.pop_open_stack_loop
    let inv : alloc.vec.Vec (Std.Usize × Bool) × Std.Usize → Prop := fun (v, k) =>
      k.val ≤ target.val ∧ v.length = k.val
    refine loop.spec_decr_nat
      (fun (_, k) => target.val - k.val) inv
      (fun (v : alloc.vec.Vec (Std.Usize × Bool)) => v.length = «open».length - 1) _
      (alloc.vec.Vec.new (Std.Usize × Bool), 0#usize) ?_
      ⟨by scalar_tac, by simp [alloc.vec.Vec.new, alloc.vec.Vec.length]⟩
    intro ⟨v, k⟩ ⟨hkLe, hvLen⟩
    unfold decoder_v1.pop_open_stack_loop.body
    dsimp only
    split_ifs with hlt
    · have hCap : v.length < Std.Usize.max := by scalar_tac
      step*
      try simp only [spec_ok]
      exact ⟨⟨by scalar_tac, by scalar_tac⟩, by scalar_tac⟩
    · simp only [spec_ok]; scalar_tac
  exact hLoop

private theorem min_bytes_any_total (tag : Std.U8) :
    (if tag = 9#u8 then ok decoder_v1.MIN_OBJECT_ENTRY_BYTES
     else ok decoder_v1.MIN_ENTRY_BYTES) ⦃ mb => 0 < mb.val ⦄ := by
  split_ifs <;> simp [spec_ok, decoder_v1.MIN_OBJECT_ENTRY_BYTES, decoder_v1.MIN_ENTRY_BYTES]

private theorem step_any_atom_branches
    (input : Slice Std.U8) (pos : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc : Std.Usize)
    («open» : alloc.vec.Vec (Std.Usize × Bool))
    (hCap : «open».length < Std.Usize.max) :
    decoder_v1.skip_any_atom input pos limits entries_acc «open» ⦃ (_, open1) =>
      open1.length ≤ «open».length + 1 ⦄ := by
  unfold decoder_v1.skip_any_atom
  dsimp only
  by_cases hgt : alloc.vec.Vec.len «open» > limits.max_any_depth
  · simp [hgt, spec_ok]
  · simp only [hgt, ite_false]
    step with read_u8_at_total input pos as ⟨r⟩
    cases r with
    | Ok val =>
      simp only [core_ops_try_branch_ok, bind_ok]
      rcases val with ⟨raw_tag, cur⟩
      step as ⟨tag, htag⟩
      try dsimp only; try simp only [Aeneas.Std.uncurry]
      repeat (any_goals (
        first
        | (simp only [spec_ok, Aeneas.Std.uncurry]; try dsimp only; first | done | (scalar_tac; done) | (omega; done))
        | (apply ite_wp_split <;> intro _)
        | (split_ifs <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
        | (cases_prod_hyp <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
        | (cases_result_err <;>
            simp only [core_ops_try_branch_ok, core_ops_try_branch_err, bind_ok,
              core_ops_try_from_residual_err, Aeneas.Std.uncurry] <;>
            try dsimp only)
        | (step with min_bytes_any_total)
        | (step with check_fits_total _ _ _ (by assumption))
        | step
      ))
      all_goals try simp only [spec_ok, Aeneas.Std.uncurry]
      all_goals try dsimp only
      all_goals try scalar_tac
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
      try dsimp only
      omega

@[local step]
theorem skip_any_atom_spec
    (input : Slice Std.U8) (pos : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc : Std.Usize)
    («open» : alloc.vec.Vec (Std.Usize × Bool))
    (hCap : «open».length < Std.Usize.max) :
    decoder_v1.skip_any_atom input pos limits entries_acc «open» ⦃ (_, open1) =>
      open1.length ≤ «open».length + 1 ⦄ :=
  step_any_atom_branches input pos limits entries_acc «open» hCap

theorem skip_any_step_spec
    (input : Slice Std.U8) (cur : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc : Std.Usize)
    («open» : alloc.vec.Vec (Std.Usize × Bool))
    (hCap : «open».length < Std.Usize.max) :
    decoder_v1.skip_any_step input cur limits entries_acc «open» ⦃ (_, open1) =>
      open1.length ≤ «open».length + 1 ⦄ := by
  unfold decoder_v1.skip_any_step
  simp only [alloc.vec.Vec.len]
  split_ifs with hpos
  · have hOpenPos : 0 < «open».length := by scalar_tac
    step as ⟨i, hi⟩
    step as ⟨pair, hpair⟩
    split_ifs with hzero hb
    · have hDerefPos : 0 < (alloc.vec.Vec.deref «open»).length := by
        simp [alloc.vec.Vec.deref, alloc.vec.Vec.length, Slice.length]; exact hOpenPos
      step with pop_open_stack_spec _ hDerefPos as ⟨open1, hopen1⟩
      step as ⟨b1, hb1⟩
      simp only [alloc.vec.Vec.deref, alloc.vec.Vec.length, Slice.length] at hopen1
      simp only [spec_ok, alloc.vec.Vec.length]
      try simp at hopen1 ⊢
      omega
    · step as ⟨i2, hi2⟩
      step as ⟨v2, b1, back, hpair2, hback⟩
      try simp only [Aeneas.Std.uncurry]
      step with read_str_slice_at_total input cur as ⟨r⟩
      cases r with
      | Ok val =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        rcases val with ⟨_, end_k⟩
        have hLenOpen : (back (i2, b1)).length = «open».length := by
          rw [hback]; simp [alloc.vec.Vec.set, alloc.vec.Vec.length]
        step with skip_any_atom_spec input end_k limits entries_acc (back (i2, b1)) (by omega) as ⟨r1, open1, hopen1⟩
        try simp only [spec_ok, Aeneas.Std.uncurry]; try dsimp only
        all_goals omega
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err]
        try dsimp only
        have hLenOpen : (back (i2, b1)).length = «open».length := by
          rw [hback]; simp [alloc.vec.Vec.set, alloc.vec.Vec.length]
        try simp only [spec_ok, Aeneas.Std.uncurry]; try dsimp only
        try rw [hLenOpen]
        omega
    · step as ⟨i2, hi2⟩
      step as ⟨v2, b1, back, hpair2, hback⟩
      try simp only [Aeneas.Std.uncurry]
      have hLenOpen : (back (i2, b1)).length = «open».length := by
        rw [hback]; simp [alloc.vec.Vec.set, alloc.vec.Vec.length]
      step with skip_any_atom_spec input cur limits entries_acc (back (i2, b1)) (by omega) as ⟨r1, open1, hopen1⟩
      try simp only [spec_ok, Aeneas.Std.uncurry]; try dsimp only
      all_goals omega
  · exact skip_any_atom_spec input cur limits entries_acc «open» hCap

@[local step]
theorem skip_any_v1_total
    (input : Slice Std.U8) (start_pos : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc : Std.Usize) :
    decoder_v1.skip_any_v1 input start_pos limits entries_acc ⦃ _ => True ⦄ := by
  unfold decoder_v1.skip_any_v1
  dsimp only
  have hUsizeMax : core.num.Usize.MAX.val = Std.Usize.max := by
    simp [core.num.Usize.MAX]
  have hRemSpec :
      (if Slice.len input >= start_pos
       then let i1 := Slice.len input; i1 - start_pos
       else ok 0#usize) ⦃ _ => True ⦄ := by
    split_ifs
    · dsimp only; step*
    · simp [spec_ok]
  step with hRemSpec as ⟨rem⟩
  step as ⟨i1, hi1⟩
  have hRem2Spec :
      (if rem <= i1 then rem * 2#usize else ok core.num.Usize.MAX) ⦃ _ => True ⦄ := by
    split_ifs with hle
    · have : rem.val * 2 ≤ Std.Usize.max := by scalar_tac
      step*
    · simp [spec_ok]
  step with hRem2Spec as ⟨rem2⟩
  have hRem2Le : rem2.val ≤ core.num.Usize.MAX.val := by
    have := rem2.hBounds; scalar_tac
  step as ⟨i2, hi2⟩
  have hRemDSpec :
      (if limits.max_any_depth <= i2 then rem2 + limits.max_any_depth else ok core.num.Usize.MAX)
        ⦃ _ => True ⦄ := by
    split_ifs with hle
    · have : rem2.val + limits.max_any_depth.val ≤ Std.Usize.max := by scalar_tac
      step*
    · simp [spec_ok]
  step with hRemDSpec as ⟨rem_d⟩
  have hRemDLe : rem_d.val ≤ core.num.Usize.MAX.val := by
    have := rem_d.hBounds; scalar_tac
  step as ⟨i3, hi3⟩
  have hMaxStepsSpec :
      (if 2#usize <= i3 then rem_d + 2#usize else ok core.num.Usize.MAX) ⦃ _ => True ⦄ := by
    split_ifs with hle
    · have : rem_d.val + 2 ≤ Std.Usize.max := by scalar_tac
      step*
    · simp [spec_ok]
  step with hMaxStepsSpec as ⟨max_steps⟩
  have hLoop :
      decoder_v1.skip_any_v1_loop input limits.max_structs limits.max_clients
        limits.max_collection_entries limits.max_any_depth limits.max_content_bytes
        start_pos entries_acc (alloc.vec.Vec.new (Std.Usize × Bool)) max_steps 0#usize false none
        ⦃ _ => True ⦄ := by
    unfold decoder_v1.skip_any_v1_loop
    let inv : Std.Usize × Std.Usize × alloc.vec.Vec (Std.Usize × Bool) × Std.Usize × Bool × Option CodecError → Prop :=
      fun (_, _, open1, step1, _, _) =>
        step1.val ≤ max_steps.val ∧ open1.length ≤ step1.val
    refine loop.spec_decr_nat
      (fun (_, _, _, step1, done1, err1) =>
        stepFlag done1 err1 + (max_steps.val - step1.val))
      inv (fun _ => True) _
      (start_pos, entries_acc, alloc.vec.Vec.new (Std.Usize × Bool), 0#usize, false, none) ?_
      ⟨by scalar_tac, by simp [alloc.vec.Vec.new, alloc.vec.Vec.length]⟩
    intro ⟨cur1, tot1, open1, step1, done1, err1⟩ ⟨hStep, hOpenLen⟩
    unfold decoder_v1.skip_any_v1_loop.body
    dsimp only
    split_ifs with hlt hdone hnone
    · simp [spec_ok]
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      have hCapStep : open1.length < Std.Usize.max := by scalar_tac
      step as ⟨step2, hStep2⟩
      step with skip_any_step_spec input cur1
        ⟨limits.max_structs, limits.max_clients, limits.max_collection_entries,
          limits.max_any_depth, limits.max_content_bytes⟩
        tot1 open1 hCapStep as ⟨r, open2, hOpen2⟩
      cases r with
      | Ok t =>
        rcases t with ⟨nc, ne, b⟩
        dsimp only
        try simp only [Aeneas.Std.uncurry]
        try simp only [spec_ok]
        refine ⟨⟨by scalar_tac, by omega⟩, ?_⟩
        by_cases hb : b <;> simp [stepFlag, hb, hStep2] <;> scalar_tac
      | Err e =>
        dsimp only
        try simp only [Aeneas.Std.uncurry]
        try simp only [spec_ok]
        refine ⟨⟨by scalar_tac, by omega⟩, ?_⟩
        simp [stepFlag, hStep2]; scalar_tac
    · simp [spec_ok]
    · simp [spec_ok]
  step with hLoop as ⟨cur, tot, done1, err⟩
  cases err with
  | none => split_ifs <;> simp [spec_ok]
  | some e => simp [spec_ok]

@[local step]
theorem skip_id_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.skip_id_at input pos ⦃ _ => True ⦄ := by
  unfold decoder_v1.skip_id_at
  step with read_var_u64_at_total input pos as ⟨r⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨_, p1⟩
    step with read_var_u64_at_total input p1 as ⟨r1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val1 with ⟨_, p2⟩
      simp [spec_ok]
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem read_json_entries_total (input : Slice Std.U8) (start_pos count : Std.Usize) :
    decoder_v1.read_json_entries input start_pos count ⦃ _ => True ⦄ := by
  unfold decoder_v1.read_json_entries
  have hLoop :
      decoder_v1.read_json_entries_loop input count start_pos 0#usize none ⦃ _ => True ⦄ := by
    unfold decoder_v1.read_json_entries_loop
    refine loop.spec_decr_nat
      (fun (_, i, err) => errFlag err + (count.val - i.val))
      (fun (_, i, _) => i.val ≤ count.val)
      (fun _ => True) _ (start_pos, 0#usize, none) ?_ (by scalar_tac)
    intro ⟨cur1, i1, err1⟩ hi
    unfold decoder_v1.read_json_entries_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with read_str_slice_at_total input cur1 as ⟨r⟩
      cases r with
      | Ok p =>
        rcases p with ⟨_, end_j⟩
        dsimp
        step as ⟨i2, hi2⟩
        try simp only [spec_ok]
        exact ⟨by scalar_tac, by simp [hi2]; scalar_tac⟩
      | Err e =>
        simp only [spec_ok]
        exact ⟨hi, by simp⟩
    · simp [spec_ok]
    · simp [spec_ok]
  step with hLoop as ⟨cur, err⟩
  cases err <;> simp [spec_ok]

@[local step]
theorem read_any_entries_total
    (input : Slice Std.U8) (start_pos count : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc : Std.Usize) :
    decoder_v1.read_any_entries input start_pos count limits entries_acc ⦃ _ => True ⦄ := by
  unfold decoder_v1.read_any_entries
  have hLoop :
      decoder_v1.read_any_entries_loop input count limits start_pos entries_acc 0#usize none ⦃ _ => True ⦄ := by
    unfold decoder_v1.read_any_entries_loop
    refine loop.spec_decr_nat
      (fun (_, _, i, err) => errFlag err + (count.val - i.val))
      (fun (_, _, i, _) => i.val ≤ count.val)
      (fun _ => True) _ (start_pos, entries_acc, 0#usize, none) ?_ (by scalar_tac)
    intro ⟨cur1, ent1, i1, err1⟩ hi
    unfold decoder_v1.read_any_entries_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with skip_any_v1_total input cur1 limits ent1 as ⟨r⟩
      cases r with
      | Ok p =>
        rcases p with ⟨_, end_j⟩
        dsimp
        step as ⟨i2, hi2⟩
        try simp only [spec_ok]
        exact ⟨by scalar_tac, by simp [hi2]; scalar_tac⟩
      | Err e =>
        simp only [spec_ok]
        exact ⟨hi, by simp⟩
    · simp [spec_ok]
    · simp [spec_ok]
  step with hLoop as ⟨cur, entries, err⟩
  cases err <;> simp [spec_ok]

@[local step]
theorem skip_item_header_total (input : Slice Std.U8) (start_pos : Std.Usize) (info : Std.U8) :
    decoder_v1.skip_item_header input start_pos info ⦃ _ => True ⦄ := by
  unfold decoder_v1.skip_item_header
  repeat (any_goals (
    first
    | (simp only [spec_ok, Aeneas.Std.uncurry]; try dsimp only; first | done | (scalar_tac; done) | (omega; done))
    | (apply ite_wp_split <;> intro _)
    | (split_ifs <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
    | (cases_prod_hyp <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
    | (cases_result_err <;>
        simp only [core_ops_try_branch_ok, core_ops_try_branch_err, bind_ok,
          core_ops_try_from_residual_err, Aeneas.Std.uncurry] <;>
        try dsimp only)
    | step
  ))
  all_goals try simp only [spec_ok, Aeneas.Std.uncurry]

@[local step]
theorem skip_item_content_total
    (input : Slice Std.U8) (cur : Std.Usize) (tag : Std.U8)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc : Std.Usize) :
    decoder_v1.skip_item_content input cur tag limits entries_acc ⦃ _ => True ⦄ := by
  unfold decoder_v1.skip_item_content
  try dsimp only; try simp only [Aeneas.Std.uncurry]
  repeat (
    first
    | (simp only [spec_ok, Aeneas.Std.uncurry]; try dsimp only; first | done | (scalar_tac; done) | (omega; done))
    | (apply ite_wp_split <;> intro _)
    | (split_ifs <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
    | (cases_prod_hyp <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
    | (cases_result_err <;>
        simp only [core_ops_try_branch_ok, core_ops_try_branch_err, bind_ok,
          core_ops_try_from_residual_err, Aeneas.Std.uncurry] <;>
        try dsimp only)
    | (step with Utf16.utf16_len_total)
    | step
  )
  all_goals try simp only [spec_ok, Aeneas.Std.uncurry]

private theorem sat_sub_usize_total (a b : Std.Usize) :
    (if a >= b then a - b else ok 0#usize) ⦃ _ => True ⦄ := by
  split_ifs <;> step*

@[local step]
theorem read_struct_frame_total
    (input : Slice Std.U8) (pos : Std.Usize) (clock : Std.U64)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc content_bytes_acc : Std.Usize) :
    decoder_v1.read_struct_frame input pos clock limits entries_acc content_bytes_acc ⦃ _ => True ⦄ := by
  unfold decoder_v1.read_struct_frame
  try dsimp only; try simp only [Aeneas.Std.uncurry]
  repeat (
    first
    | (simp only [spec_ok, Aeneas.Std.uncurry]; try dsimp only; first | done | (scalar_tac; done) | (omega; done))
    | (apply ite_wp_split <;> intro _)
    | (split_ifs <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
    | (cases_prod_hyp <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
    | (cases_result_err <;>
        simp only [core_ops_try_branch_ok, core_ops_try_branch_err, bind_ok,
          core_ops_try_from_residual_err, Aeneas.Std.uncurry] <;>
        try dsimp only)
    | (step with sat_sub_usize_total)
    | step
  )
  all_goals try simp only [spec_ok, Aeneas.Std.uncurry]

@[local step]
theorem read_client_structs_total
    (input : Slice Std.U8) (start_pos : Std.Usize) (start_clock : Std.U64)
    (count : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (entries_acc content_bytes_acc : Std.Usize) :
    decoder_v1.read_client_structs input start_pos start_clock count limits entries_acc content_bytes_acc ⦃ _ => True ⦄ := by
  unfold decoder_v1.read_client_structs
  have hLoop :
      decoder_v1.read_client_structs_loop input count limits start_pos start_clock
        entries_acc content_bytes_acc 0#usize none ⦃ _ => True ⦄ := by
    unfold decoder_v1.read_client_structs_loop
    refine loop.spec_decr_nat
      (fun (_, _, _, _, sIdx, err) => errFlag err + (count.val - sIdx.val))
      (fun (_, _, _, _, sIdx, _) => sIdx.val ≤ count.val)
      (fun _ => True) _ (start_pos, start_clock, entries_acc, content_bytes_acc, 0#usize, none) ?_
      (by scalar_tac)
    intro ⟨cur1, clk1, ent1, bytes1, sIdx, err1⟩ hs
    unfold decoder_v1.read_client_structs_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with read_struct_frame_total input cur1 clk1 limits ent1 bytes1 as ⟨r⟩
      cases r with
      | Ok t =>
        rcases t with ⟨nc, nk, ne, nb⟩
        dsimp
        step as ⟨sIdx1, hsIdx1⟩
        try simp only [spec_ok]
        exact ⟨by scalar_tac, by simp [hsIdx1]; scalar_tac⟩
      | Err e =>
        try simp only [spec_ok]
        exact ⟨hs, by simp⟩
    · simp [spec_ok]
    · simp [spec_ok]
  step with hLoop as ⟨cur, entries, content_bytes, err⟩
  cases err <;> simp [spec_ok]

@[local step]
theorem decode_one_client_block_total
    (input : Slice Std.U8) (cur : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (seen_clients : alloc.vec.Vec Std.U64)
    (total_structs total_entries total_content_bytes : Std.Usize)
    (hCap : seen_clients.length < Std.Usize.max) :
    decoder_v1.decode_one_client_block input cur limits seen_clients
      total_structs total_entries total_content_bytes ⦃ (_, seen1) =>
        seen1.length ≤ seen_clients.length + 1 ⦄ := by
  unfold decoder_v1.decode_one_client_block
  try dsimp only; try simp only [Aeneas.Std.uncurry]
  repeat (any_goals (
    first
    | (simp only [spec_ok, Aeneas.Std.uncurry]; try dsimp only; first | done | (scalar_tac; done) | (omega; done))
    | (apply ite_wp_split <;> intro _)
    | (split_ifs <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
    | (cases_prod_hyp <;> try dsimp only <;> try simp only [Aeneas.Std.uncurry])
    | (cases_result_err <;>
        simp only [core_ops_try_branch_ok, core_ops_try_branch_err, bind_ok,
          core_ops_try_from_residual_err, Aeneas.Std.uncurry] <;>
        try dsimp only)
    | step
  ))
  all_goals try simp only [spec_ok, Aeneas.Std.uncurry]
  all_goals try dsimp only
  all_goals try scalar_tac

theorem decode_update_v1_frame_total
    (input : Slice Std.U8) (limits : decoder_v1.DecodeLimitsCore) :
    decoder_v1.decode_update_v1_frame input limits ⦃ _ => True ⦄ := by
  unfold decoder_v1.decode_update_v1_frame
  step with read_var_u64_at_total input 0#usize as ⟨r, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨clients_u64, cur⟩
    dsimp only at hr
    step with checked_usize_from_u64_total clients_u64 as ⟨r1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      split_ifs with hlim
      · simp [spec_ok]
      · step as ⟨i1, hi1⟩
        step with check_fits_min_client_total i1 val1 as ⟨r2⟩
        cases r2 with
        | Ok _ =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          have hLoop :
              decoder_v1.decode_update_v1_frame_loop input limits.max_structs limits.max_clients
                limits.max_collection_entries limits.max_any_depth limits.max_content_bytes
                cur val1 (alloc.vec.Vec.new Std.U64) 0#usize 0#usize 0#usize 0#usize none ⦃ _ => True ⦄ := by
            unfold decoder_v1.decode_update_v1_frame_loop
            let inv : Std.Usize × alloc.vec.Vec Std.U64 × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Option CodecError → Prop :=
              fun (_, seen, _, _, _, cIdx, err) =>
                cIdx.val ≤ val1.val ∧ seen.length ≤ cIdx.val + (1 - errFlag err)
            refine loop.spec_decr_nat
              (fun (_, _, _, _, _, cIdx, err) => errFlag err + (val1.val - cIdx.val))
              inv (fun _ => True) _
              (cur, alloc.vec.Vec.new Std.U64, 0#usize, 0#usize, 0#usize, 0#usize, none) ?_
              ⟨by scalar_tac, by simp [alloc.vec.Vec.new, alloc.vec.Vec.length]⟩
            intro ⟨cur1, seen1, structs1, ent1, bytes1, cIdx, err1⟩ ⟨hcLe, hSeenLen⟩
            unfold decoder_v1.decode_update_v1_frame_loop.body
            dsimp only
            split_ifs with hlt hnone
            · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
              subst herr
              simp only [errFlag_none, Nat.sub_self, Nat.add_zero] at hSeenLen
              have hCapStep : seen1.length < Std.Usize.max := by scalar_tac
              step with decode_one_client_block_total input cur1
                ⟨limits.max_structs, limits.max_clients, limits.max_collection_entries,
                  limits.max_any_depth, limits.max_content_bytes⟩
                seen1 structs1 ent1 bytes1 hCapStep as ⟨rBlock, seen2, hSeen2⟩
              cases rBlock with
              | Ok t =>
                rcases t with ⟨nc, ns, ne, nb⟩
                dsimp only
                step as ⟨cIdx1, hcIdx1⟩
                try simp only [spec_ok]
                exact ⟨⟨by scalar_tac, by simp only [errFlag_none, hcIdx1]; omega⟩, by simp only [errFlag_none, hcIdx1]; scalar_tac⟩
              | Err e =>
                try simp only [spec_ok]
                exact ⟨⟨hcLe, by simp only [errFlag_some]; omega⟩, by simp⟩
            · simp [spec_ok]
            · simp [spec_ok]
          step with hLoop as ⟨cur1, total_structs, total_entries, err⟩
          cases err with
          | none =>
            step with read_delete_set_v1_total input cur1 limits total_entries as ⟨r3⟩
            cases r3 with
            | Ok val2 =>
              simp only [core_ops_try_branch_ok, bind_ok]
              rcases val2 with ⟨ds, end_d⟩
              try simp only [Aeneas.Std.uncurry]
              split_ifs <;> simp [spec_ok]
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          | some e =>
            simp [spec_ok]
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

end YoctoCore.Properties.DecoderV1
