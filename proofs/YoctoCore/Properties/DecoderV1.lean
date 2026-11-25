import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.Varint
import YoctoCore.Properties.DeleteSet
import YoctoCore.Properties.StateVector
import YoctoCore.Properties.Utf16

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code

set_option maxHeartbeats 4000000

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

open Lean Elab Tactic Meta in
elab "cases_and_hyp" : tactic =>
  casesFirstHyp fun t => t.isAppOfArity ``And 2

macro "cases_and_hyps" : tactic => `(tactic| repeat cases_and_hyp)

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

/-- Span validity predicate: a byte range `[start, end)` within `input`. -/
def SpanOk (input : Slice Std.U8) (sp : decoder_v1.Span) : Prop :=
  sp.start.val ≤ sp.«end».val ∧ sp.«end».val ≤ input.length

def WireParentOk (input : Slice Std.U8) : decoder_v1.WireParentCore → Prop
  | .Root sp => SpanOk input sp
  | .Item _ => True
  | .Inherit => True

def OptSpanOk (input : Slice Std.U8) : Option decoder_v1.Span → Prop
  | none => True
  | some sp => SpanOk input sp

def ItemMetaOk (input : Slice Std.U8) (m : decoder_v1.ItemMetaCore) : Prop :=
  WireParentOk input m.parent ∧ OptSpanOk input m.parent_sub ∧ SpanOk input m.raw_range

/-- Totality contract for `SvSink` preserving a caller invariant `Inv`. -/
structure SvSinkTotal {S : Type _} (V : decoder_v1.SvSink S) (Inv : S → Prop) : Prop where
  on_sv_len : ∀ s count, Inv s → V.on_sv_len s count ⦃ (_, s') => Inv s' ⦄
  on_sv_entry : ∀ s client clock, Inv s → V.on_sv_entry s client clock ⦃ (_, s') => Inv s' ⦄

/-- Totality & span-safety contract for `V1Sink`: `Span`-receiving callbacks
    may assume `SpanOk input` on their emitted spans and `ItemMetaOk input` on `on_item`. -/
structure V1SinkSpanSafe {S : Type _}
    (input : Slice Std.U8) (V : decoder_v1.V1Sink S) (Inv : S → Prop) : Prop where
  core_validates_utf8 : ∀ s, V.core_validates_utf8 s ⦃ _ => True ⦄
  validate_utf8_early : ∀ s slot sp, Inv s → SpanOk input sp →
    V.validate_utf8_early s slot sp ⦃ (_, s') => Inv s' ⦄
  on_decode_error : ∀ s err a b, Inv s → V.on_decode_error s err a b ⦃ s' => Inv s' ⦄
  record_client : ∀ s client, Inv s → V.record_client s client ⦃ (_, s') => Inv s' ⦄
  begin_client : ∀ s client count, Inv s → V.begin_client s client count ⦃ (_, s') => Inv s' ⦄
  on_gc : ∀ s id len, Inv s → V.on_gc s id len ⦃ (_, s') => Inv s' ⦄
  on_skip : ∀ s id len, Inv s → V.on_skip s id len ⦃ (_, s') => Inv s' ⦄
  on_item : ∀ s id len m, Inv s → ItemMetaOk input m →
    V.on_item s id len m ⦃ (_, s') => Inv s' ⦄
  on_skipped_zero_origin : ∀ s ol, Inv s → V.on_skipped_zero_origin s ol ⦃ s' => Inv s' ⦄
  on_deleted : ∀ s len, Inv s → V.on_deleted s len ⦃ (_, s') => Inv s' ⦄
  on_json_start : ∀ s count, Inv s → V.on_json_start s count ⦃ (_, s') => Inv s' ⦄
  on_json_value : ∀ s sp, Inv s → SpanOk input sp →
    V.on_json_value s sp ⦃ (_, s') => Inv s' ⦄
  on_json_finish : ∀ s, Inv s → V.on_json_finish s ⦃ (_, s') => Inv s' ⦄
  on_binary : ∀ s sp, Inv s → SpanOk input sp → V.on_binary s sp ⦃ (_, s') => Inv s' ⦄
  on_string : ∀ s sp, Inv s → SpanOk input sp → V.on_string s sp ⦃ (_, s') => Inv s' ⦄
  on_embed : ∀ s sp, Inv s → SpanOk input sp → V.on_embed s sp ⦃ (_, s') => Inv s' ⦄
  on_format : ∀ s k v, Inv s → SpanOk input k → SpanOk input v →
    V.on_format s k v ⦃ (_, s') => Inv s' ⦄
  on_type : ∀ s kind tag, Inv s → OptSpanOk input tag →
    V.on_type s kind tag ⦃ (_, s') => Inv s' ⦄
  on_any_content_start : ∀ s count, Inv s → V.on_any_content_start s count ⦃ (_, s') => Inv s' ⦄
  on_any_content_value : ∀ s, Inv s → V.on_any_content_value s ⦃ (_, s') => Inv s' ⦄
  on_any_content_finish : ∀ s, Inv s → V.on_any_content_finish s ⦃ (_, s') => Inv s' ⦄
  on_doc : ∀ s guid, Inv s → SpanOk input guid → V.on_doc s guid ⦃ (_, s') => Inv s' ⦄
  on_any_start : ∀ s, Inv s → V.on_any_start s ⦃ (_, s') => Inv s' ⦄
  on_any_undefined : ∀ s, Inv s → V.on_any_undefined s ⦃ (_, s') => Inv s' ⦄
  on_any_null : ∀ s, Inv s → V.on_any_null s ⦃ (_, s') => Inv s' ⦄
  on_any_i32 : ∀ s v, Inv s → V.on_any_i32 s v ⦃ (_, s') => Inv s' ⦄
  on_any_f32_bits : ∀ s bits, Inv s → V.on_any_f32_bits s bits ⦃ (_, s') => Inv s' ⦄
  on_any_f64_bits : ∀ s bits, Inv s → V.on_any_f64_bits s bits ⦃ (_, s') => Inv s' ⦄
  on_any_i64_bits : ∀ s bits, Inv s → V.on_any_i64_bits s bits ⦃ (_, s') => Inv s' ⦄
  on_any_bool : ∀ s v, Inv s → V.on_any_bool s v ⦃ (_, s') => Inv s' ⦄
  on_any_str : ∀ s sp, Inv s → SpanOk input sp → V.on_any_str s sp ⦃ (_, s') => Inv s' ⦄
  on_any_bytes : ∀ s sp, Inv s → SpanOk input sp → V.on_any_bytes s sp ⦃ (_, s') => Inv s' ⦄
  on_any_begin_object : ∀ s count, Inv s → V.on_any_begin_object s count ⦃ (_, s') => Inv s' ⦄
  on_any_object_key : ∀ s sp, Inv s → SpanOk input sp →
    V.on_any_object_key s sp ⦃ (_, s') => Inv s' ⦄
  on_any_begin_array : ∀ s count, Inv s → V.on_any_begin_array s count ⦃ (_, s') => Inv s' ⦄
  on_any_end_container : ∀ s, Inv s → V.on_any_end_container s ⦃ (_, s') => Inv s' ⦄
  on_any_finish : ∀ s sp, Inv s → SpanOk input sp → V.on_any_finish s sp ⦃ (_, s') => Inv s' ⦄
  begin_delete_client : ∀ s client count, Inv s →
    V.begin_delete_client s client count ⦃ (_, s') => Inv s' ⦄
  on_delete_range : ∀ s client start «end», Inv s →
    V.on_delete_range s client start «end» ⦃ (_, s') => Inv s' ⦄

/-- Unconditional totality contract for `V1Sink` preserving `Inv`. -/
structure V1SinkTotal {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop) : Prop where
  core_validates_utf8 : ∀ s, V.core_validates_utf8 s ⦃ _ => True ⦄
  validate_utf8_early : ∀ s slot sp, Inv s → V.validate_utf8_early s slot sp ⦃ (_, s') => Inv s' ⦄
  on_decode_error : ∀ s err a b, Inv s → V.on_decode_error s err a b ⦃ s' => Inv s' ⦄
  record_client : ∀ s client, Inv s → V.record_client s client ⦃ (_, s') => Inv s' ⦄
  begin_client : ∀ s client count, Inv s → V.begin_client s client count ⦃ (_, s') => Inv s' ⦄
  on_gc : ∀ s id len, Inv s → V.on_gc s id len ⦃ (_, s') => Inv s' ⦄
  on_skip : ∀ s id len, Inv s → V.on_skip s id len ⦃ (_, s') => Inv s' ⦄
  on_item : ∀ s id len m, Inv s → V.on_item s id len m ⦃ (_, s') => Inv s' ⦄
  on_skipped_zero_origin : ∀ s ol, Inv s → V.on_skipped_zero_origin s ol ⦃ s' => Inv s' ⦄
  on_deleted : ∀ s len, Inv s → V.on_deleted s len ⦃ (_, s') => Inv s' ⦄
  on_json_start : ∀ s count, Inv s → V.on_json_start s count ⦃ (_, s') => Inv s' ⦄
  on_json_value : ∀ s sp, Inv s → V.on_json_value s sp ⦃ (_, s') => Inv s' ⦄
  on_json_finish : ∀ s, Inv s → V.on_json_finish s ⦃ (_, s') => Inv s' ⦄
  on_binary : ∀ s sp, Inv s → V.on_binary s sp ⦃ (_, s') => Inv s' ⦄
  on_string : ∀ s sp, Inv s → V.on_string s sp ⦃ (_, s') => Inv s' ⦄
  on_embed : ∀ s sp, Inv s → V.on_embed s sp ⦃ (_, s') => Inv s' ⦄
  on_format : ∀ s k v, Inv s → V.on_format s k v ⦃ (_, s') => Inv s' ⦄
  on_type : ∀ s kind tag, Inv s → V.on_type s kind tag ⦃ (_, s') => Inv s' ⦄
  on_any_content_start : ∀ s count, Inv s → V.on_any_content_start s count ⦃ (_, s') => Inv s' ⦄
  on_any_content_value : ∀ s, Inv s → V.on_any_content_value s ⦃ (_, s') => Inv s' ⦄
  on_any_content_finish : ∀ s, Inv s → V.on_any_content_finish s ⦃ (_, s') => Inv s' ⦄
  on_doc : ∀ s guid, Inv s → V.on_doc s guid ⦃ (_, s') => Inv s' ⦄
  on_any_start : ∀ s, Inv s → V.on_any_start s ⦃ (_, s') => Inv s' ⦄
  on_any_undefined : ∀ s, Inv s → V.on_any_undefined s ⦃ (_, s') => Inv s' ⦄
  on_any_null : ∀ s, Inv s → V.on_any_null s ⦃ (_, s') => Inv s' ⦄
  on_any_i32 : ∀ s v, Inv s → V.on_any_i32 s v ⦃ (_, s') => Inv s' ⦄
  on_any_f32_bits : ∀ s bits, Inv s → V.on_any_f32_bits s bits ⦃ (_, s') => Inv s' ⦄
  on_any_f64_bits : ∀ s bits, Inv s → V.on_any_f64_bits s bits ⦃ (_, s') => Inv s' ⦄
  on_any_i64_bits : ∀ s bits, Inv s → V.on_any_i64_bits s bits ⦃ (_, s') => Inv s' ⦄
  on_any_bool : ∀ s v, Inv s → V.on_any_bool s v ⦃ (_, s') => Inv s' ⦄
  on_any_str : ∀ s sp, Inv s → V.on_any_str s sp ⦃ (_, s') => Inv s' ⦄
  on_any_bytes : ∀ s sp, Inv s → V.on_any_bytes s sp ⦃ (_, s') => Inv s' ⦄
  on_any_begin_object : ∀ s count, Inv s → V.on_any_begin_object s count ⦃ (_, s') => Inv s' ⦄
  on_any_object_key : ∀ s sp, Inv s → V.on_any_object_key s sp ⦃ (_, s') => Inv s' ⦄
  on_any_begin_array : ∀ s count, Inv s → V.on_any_begin_array s count ⦃ (_, s') => Inv s' ⦄
  on_any_end_container : ∀ s, Inv s → V.on_any_end_container s ⦃ (_, s') => Inv s' ⦄
  on_any_finish : ∀ s sp, Inv s → V.on_any_finish s sp ⦃ (_, s') => Inv s' ⦄
  begin_delete_client : ∀ s client count, Inv s →
    V.begin_delete_client s client count ⦃ (_, s') => Inv s' ⦄
  on_delete_range : ∀ s client start «end», Inv s →
    V.on_delete_range s client start «end» ⦃ (_, s') => Inv s' ⦄

theorem V1SinkTotal.toSpanSafe {S : Type _} {V : decoder_v1.V1Sink S} {Inv : S → Prop}
    (input : Slice Std.U8) (h : V1SinkTotal V Inv) : V1SinkSpanSafe input V Inv :=
  { core_validates_utf8 := h.core_validates_utf8
    validate_utf8_early := fun s slot sp hs _ => h.validate_utf8_early s slot sp hs
    on_decode_error := h.on_decode_error
    record_client := h.record_client
    begin_client := h.begin_client
    on_gc := h.on_gc
    on_skip := h.on_skip
    on_item := fun s id len m hs _ => h.on_item s id len m hs
    on_skipped_zero_origin := h.on_skipped_zero_origin
    on_deleted := h.on_deleted
    on_json_start := h.on_json_start
    on_json_value := fun s sp hs _ => h.on_json_value s sp hs
    on_json_finish := h.on_json_finish
    on_binary := fun s sp hs _ => h.on_binary s sp hs
    on_string := fun s sp hs _ => h.on_string s sp hs
    on_embed := fun s sp hs _ => h.on_embed s sp hs
    on_format := fun s k v hs _ _ => h.on_format s k v hs
    on_type := fun s kind tag hs _ => h.on_type s kind tag hs
    on_any_content_start := h.on_any_content_start
    on_any_content_value := h.on_any_content_value
    on_any_content_finish := h.on_any_content_finish
    on_doc := fun s guid hs _ => h.on_doc s guid hs
    on_any_start := h.on_any_start
    on_any_undefined := h.on_any_undefined
    on_any_null := h.on_any_null
    on_any_i32 := h.on_any_i32
    on_any_f32_bits := h.on_any_f32_bits
    on_any_f64_bits := h.on_any_f64_bits
    on_any_i64_bits := h.on_any_i64_bits
    on_any_bool := h.on_any_bool
    on_any_str := fun s sp hs _ => h.on_any_str s sp hs
    on_any_bytes := fun s sp hs _ => h.on_any_bytes s sp hs
    on_any_begin_object := h.on_any_begin_object
    on_any_object_key := fun s sp hs _ => h.on_any_object_key s sp hs
    on_any_begin_array := h.on_any_begin_array
    on_any_end_container := h.on_any_end_container
    on_any_finish := fun s sp hs _ => h.on_any_finish s sp hs
    begin_delete_client := h.begin_delete_client
    on_delete_range := h.on_delete_range }

@[local step]
theorem checked_usize_from_u64_total (v : Std.U64) :
    decoder_v1.checked_usize_from_u64 v ⦃ _ => True ⦄ := by
  unfold decoder_v1.checked_usize_from_u64
  step*

@[local step]
theorem checked_usize_limit_total (v : Std.U64) (kind : LimitKind) :
    decoder_v1.checked_usize_limit v kind ⦃ _ => True ⦄ := by
  unfold decoder_v1.checked_usize_limit
  step*

theorem check_fits_total (remaining count : Std.Usize) (min_bytes : Std.U64)
    (hMin : 0 < min_bytes.val) :
    decoder_v1.check_fits remaining count min_bytes ⦃ _ => True ⦄ := by
  unfold decoder_v1.check_fits
  step*

theorem check_fits_kind_total (remaining count : Std.Usize) (min_bytes : Std.U64)
    (kind : LimitKind) (hMin : 0 < min_bytes.val) :
    decoder_v1.check_fits_kind remaining count min_bytes kind ⦃ _ => True ⦄ := by
  unfold decoder_v1.check_fits_kind
  step*

theorem fail_with_spec {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (sink : S) (err : CodecError) (a : Std.Usize) (b : Std.U64) (hSink : Inv sink) :
    decoder_v1.fail_with V sink err a b ⦃ (_, sink') => Inv sink' ⦄ := by
  unfold decoder_v1.fail_with
  step with hV.on_decode_error sink err a b hSink as ⟨sink1, hInv1⟩
  simp [spec_ok, hInv1]

theorem check_fits_kind_sink_spec {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (remaining count : Std.Usize) (min_bytes : Std.U64) (kind : LimitKind) (sink : S)
    (hMin : 0 < min_bytes.val) (hSink : Inv sink) :
    decoder_v1.check_fits_kind_sink V remaining count min_bytes kind sink
      ⦃ (_, sink') => Inv sink' ⦄ := by
  unfold decoder_v1.check_fits_kind_sink
  step as ⟨i, _⟩
  step as ⟨available, _⟩
  step as ⟨i1, _⟩
  split_ifs
  · step with fail_with_spec V Inv input hV sink (CodecError.CountTooLarge kind) count available hSink
      as ⟨ce, sink1, hInv1⟩
    simp [spec_ok, hInv1]
  · simp [spec_ok, hSink]

@[local step]
private theorem check_fits_2_total (remaining count : Std.Usize) :
    decoder_v1.check_fits remaining count 2#u64 ⦃ _ => True ⦄ :=
  check_fits_total remaining count 2#u64 (by decide)

@[local step]
private theorem check_fits_kind_min_client_total (remaining count : Std.Usize) (kind : LimitKind) :
    decoder_v1.check_fits_kind remaining count decoder_v1.MIN_CLIENT_BYTES kind ⦃ _ => True ⦄ :=
  check_fits_kind_total remaining count decoder_v1.MIN_CLIENT_BYTES kind
    (by simp [decoder_v1.MIN_CLIENT_BYTES])

@[local step]
private theorem check_fits_kind_min_struct_total (remaining count : Std.Usize) (kind : LimitKind) :
    decoder_v1.check_fits_kind remaining count decoder_v1.MIN_STRUCT_BYTES kind ⦃ _ => True ⦄ :=
  check_fits_kind_total remaining count decoder_v1.MIN_STRUCT_BYTES kind
    (by simp [decoder_v1.MIN_STRUCT_BYTES])

@[local step]
private theorem check_fits_kind_min_delete_client_total (remaining count : Std.Usize) (kind : LimitKind) :
    decoder_v1.check_fits_kind remaining count decoder_v1.MIN_DELETE_CLIENT_BYTES kind ⦃ _ => True ⦄ :=
  check_fits_kind_total remaining count decoder_v1.MIN_DELETE_CLIENT_BYTES kind
    (by simp [decoder_v1.MIN_DELETE_CLIENT_BYTES])

@[local step]
private theorem check_fits_kind_min_delete_range_total (remaining count : Std.Usize) (kind : LimitKind) :
    decoder_v1.check_fits_kind remaining count decoder_v1.MIN_DELETE_RANGE_BYTES kind ⦃ _ => True ⦄ :=
  check_fits_kind_total remaining count decoder_v1.MIN_DELETE_RANGE_BYTES kind
    (by simp [decoder_v1.MIN_DELETE_RANGE_BYTES])

@[local step]
private theorem check_fits_kind_min_entry_total (remaining count : Std.Usize) (kind : LimitKind) :
    decoder_v1.check_fits_kind remaining count decoder_v1.MIN_ENTRY_BYTES kind ⦃ _ => True ⦄ :=
  check_fits_kind_total remaining count decoder_v1.MIN_ENTRY_BYTES kind
    (by simp [decoder_v1.MIN_ENTRY_BYTES])

@[local step]
private theorem check_fits_kind_min_obj_entry_total (remaining count : Std.Usize) (kind : LimitKind) :
    decoder_v1.check_fits_kind remaining count decoder_v1.MIN_OBJECT_ENTRY_BYTES kind ⦃ _ => True ⦄ :=
  check_fits_kind_total remaining count decoder_v1.MIN_OBJECT_ENTRY_BYTES kind
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
theorem checked_add_limit_total (a b : Std.Usize) (kind : LimitKind) :
    decoder_v1.checked_add_limit a b kind ⦃ r =>
      match r with
      | .Ok s => s.val = a.val + b.val
      | .Err _ => True ⦄ := by
  unfold decoder_v1.checked_add_limit
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
theorem read_u32_be_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_u32_be_at input pos ⦃ r =>
      match r with
      | .Ok (_, nxt) => pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_u32_be_at
  step* <;> try simp [spec_ok]
  try exact ⟨by scalar_tac, by scalar_tac⟩

@[local step]
theorem read_u64_be_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_u64_be_at input pos ⦃ r =>
      match r with
      | .Ok (_, nxt) => pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_u64_be_at
  step* <;> try simp [spec_ok]
  try exact ⟨by scalar_tac, by scalar_tac⟩

@[local step]
theorem read_var_u64_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_var_u64_at input pos ⦃ r =>
      match r with
      | .Ok (_, nxt) => pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_var_u64_at
  dsimp only
  split_ifs with hgt
  · simp [spec_ok]
  · step as ⟨first, _⟩
    split_ifs with hfast
    · step as ⟨i1, _⟩
      step as ⟨i2, hi2⟩
      simp [spec_ok]
      exact ⟨by scalar_tac, by scalar_tac⟩
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
          exact ⟨by scalar_tac, by scalar_tac⟩
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem read_var_i32_with_sign_at_total (input : Slice Std.U8) (pos : Std.Usize) :
    decoder_v1.read_var_i32_with_sign_at input pos ⦃ r =>
      match r with
      | .Ok (_, nxt) => pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
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
      step as ⟨i2, hi2⟩
      split_ifs with hof
      · simp [spec_ok]
      · step as ⟨i3, hi3⟩
        simp [spec_ok]
        exact ⟨by scalar_tac, by scalar_tac⟩
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

theorem read_var_u64_sink_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos : Std.Usize) (sink : S) (hSink : Inv sink) :
    decoder_v1.read_var_u64_sink V input pos sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok (_, nxt) => pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_var_u64_sink
  step with read_var_u64_at_total input pos as ⟨r, hr⟩
  cases r with
  | Ok val =>
    simp only [spec_ok]
    exact ⟨hSink, hr⟩
  | Err e =>
    dsimp only
    split_ifs with hle
    · step as ⟨i1, hi1⟩
      step with fail_with_spec V Inv input hV sink e i1 0#u64 hSink as ⟨ce, sink1, hInv1⟩
      simp [spec_ok, hInv1]
    · step with fail_with_spec V Inv input hV sink e 0#usize 0#u64 hSink as ⟨ce, sink1, hInv1⟩
      simp [spec_ok, hInv1]

theorem read_var_i32_with_sign_sink_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos : Std.Usize) (sink : S) (hSink : Inv sink) :
    decoder_v1.read_var_i32_with_sign_sink V input pos sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok (_, nxt) => pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_var_i32_with_sign_sink
  step with read_var_i32_with_sign_at_total input pos as ⟨r, hr⟩
  cases r with
  | Ok val =>
    simp only [spec_ok]
    exact ⟨hSink, hr⟩
  | Err e =>
    dsimp only
    split_ifs with hle
    · step as ⟨i1, hi1⟩
      step with fail_with_spec V Inv input hV sink e i1 0#u64 hSink as ⟨ce, sink1, hInv1⟩
      simp [spec_ok, hInv1]
    · step with fail_with_spec V Inv input hV sink e 0#usize 0#u64 hSink as ⟨ce, sink1, hInv1⟩
      simp [spec_ok, hInv1]

theorem read_bytes_slice_at_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos : Std.Usize) (sink : S) (hSink : Inv sink) :
    decoder_v1.read_bytes_slice_at V input pos sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok sp => pos.val ≤ sp.start.val ∧ SpanOk input sp
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_bytes_slice_at
  step with read_var_u64_sink_spec V Inv input hV pos sink hSink as ⟨r, sink1, hInv1, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨len_u64, next⟩
    dsimp only at hr ⊢
    step as ⟨i, hi⟩
    split_ifs with hof
    · simp [spec_ok, hInv1]
    · step as ⟨len, hlen⟩
      step as ⟨i1, hi1⟩
      split_ifs with hlo
      · simp [spec_ok, hInv1]
      · step as ⟨i3, hi3⟩
        split_ifs with hgt
        · simp [spec_ok, hInv1]
        · step as ⟨i4, hi4⟩
          simp [spec_ok, SpanOk]
          exact ⟨hInv1, by scalar_tac, by scalar_tac, by scalar_tac⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    exact ⟨hInv1, trivial⟩

theorem read_str_slice_at_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos : Std.Usize) (sink : S) (hSink : Inv sink) :
    decoder_v1.read_str_slice_at V input pos sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok sp => pos.val ≤ sp.start.val ∧ SpanOk input sp
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_str_slice_at
  step with read_bytes_slice_at_spec V Inv input hV pos sink hSink as ⟨r, sink1, hInv1, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    dsimp only [SpanOk] at hr ⊢
    step with hV.core_validates_utf8 sink1 as ⟨b⟩
    split_ifs
    · step as ⟨s, hs⟩
      step with Utf16.is_valid_utf8_total s as ⟨b1⟩
      split_ifs <;> simp [spec_ok, SpanOk, hInv1]
      exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
    · simp [spec_ok, SpanOk, hInv1]
      exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    exact ⟨hInv1, trivial⟩

theorem read_early_str_slice_at_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos : Std.Usize) (slot : Std.U8) (sink : S) (hSink : Inv sink) :
    decoder_v1.read_early_str_slice_at V input pos slot sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok sp => pos.val ≤ sp.start.val ∧ SpanOk input sp
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_early_str_slice_at
  step with read_bytes_slice_at_spec V Inv input hV pos sink hSink as ⟨r, sink1, hInv1, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    dsimp only [SpanOk] at hr ⊢
    step with hV.core_validates_utf8 sink1 as ⟨b⟩
    split_ifs
    · step as ⟨s, hs⟩
      step with Utf16.is_valid_utf8_total s as ⟨b1⟩
      split_ifs <;> simp [spec_ok, SpanOk, hInv1]
      exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
    · step with hV.validate_utf8_early sink1 slot val hInv1 hr.2 as ⟨r1, sink2, hInv2⟩
      cases r1 with
      | Ok _ =>
        simp only [core_ops_try_branch_ok, bind_ok, spec_ok, SpanOk]
        try dsimp only
        exact ⟨hInv2, by scalar_tac, by scalar_tac, by scalar_tac⟩
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
        try dsimp only
        exact ⟨hInv2, trivial⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    exact ⟨hInv1, trivial⟩

theorem read_wire_id_at_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos : Std.Usize) (sink : S) (hSink : Inv sink) :
    decoder_v1.read_wire_id_at V input pos sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok (_, nxt) => pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_wire_id_at
  step with read_var_u64_sink_spec V Inv input hV pos sink hSink as ⟨r, sink1, hInv1, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨client, p1⟩
    dsimp only at hr
    step with read_var_u64_sink_spec V Inv input hV p1 sink1 hInv1 as ⟨r1, sink2, hInv2, hr1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val1 with ⟨clock, p2⟩
      dsimp only at hr1 ⊢
      simp [spec_ok]
      exact ⟨hInv2, by omega, hr1.2⟩
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      exact ⟨hInv2, trivial⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    exact ⟨hInv1, trivial⟩

theorem advance_clock_sink_spec {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (clock len : Std.U64) (sink : S) (hSink : Inv sink) :
    decoder_v1.advance_clock_sink V clock len sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok nc => 0 < len.val ∧ nc.val = clock.val + len.val
      | .Err _ => True ⦄ := by
  unfold decoder_v1.advance_clock_sink
  split_ifs with hz
  · simp [spec_ok, hSink]
  · have hMax : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, Std.U64.numBits]
    have hCoreMax : core.num.U64.MAX.val = 2 ^ 64 - 1 := by decide
    have hClkLe : clock.val ≤ core.num.U64.MAX.val := by
      have := clock.hBounds
      have hnb : UScalarTy.U64.numBits = 64 := rfl
      rw [hnb] at this
      omega
    step as ⟨i, hi⟩
    split_ifs with hgt
    · step with fail_with_spec V Inv input hV sink CodecError.ClockOverflow 0#usize clock hSink
        as ⟨ce, sink1, hInv1⟩
      try simp [spec_ok, hInv1]
    · step as ⟨nc, hnc⟩
      try simp only [spec_ok]
      exact ⟨hSink, by scalar_tac, by omega⟩

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

theorem read_state_vector_v1_with_total
    {S : Type _} (V : decoder_v1.SvSink S) (Inv : S → Prop) (hV : SvSinkTotal V Inv)
    (input : Slice Std.U8) (pos : Std.Usize) (sink : S) (hSink : Inv sink) :
    decoder_v1.read_state_vector_v1_with V input pos sink ⦃ (_, sink') => Inv sink' ⦄ := by
  unfold decoder_v1.read_state_vector_v1_with
  dsimp only
  split_ifs with hgt
  · simp [spec_ok, hSink]
  · step with read_var_u64_at_total input pos as ⟨r, hr⟩
    cases r with
    | Ok val =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val with ⟨count_u64, cur⟩
      dsimp only at hr
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      split_ifs with hcnt
      · simp [spec_ok, hSink]
      · step with checked_usize_limit_total count_u64 LimitKind.Clients as ⟨r1⟩
        cases r1 with
        | Ok val1 =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          step with hV.on_sv_len sink val1 hSink as ⟨r2, sink1, hSink1⟩
          cases r2 with
          | Ok _ =>
            simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
            have hLoop :
                decoder_v1.read_state_vector_v1_with_loop V input sink1 cur val1 none 0#usize
                  ⦃ (sink2, _, _) => Inv sink2 ⦄ := by
              unfold decoder_v1.read_state_vector_v1_with_loop
              let inv : S × Std.Usize × Option CodecError × Std.Usize → Prop :=
                fun (sinkk, _, _, i) => Inv sinkk ∧ i.val ≤ val1.val
              refine loop.spec_decr_nat
                (fun (_, _, err, i) => errFlag err + (val1.val - i.val))
                inv _ _ (sink1, cur, none, 0#usize) ?_
                ⟨hSink1, by scalar_tac⟩
              intro ⟨sinkk, cur1, err1, i1⟩ ⟨hInvK, hiLe⟩
              unfold decoder_v1.read_state_vector_v1_with_loop.body
              dsimp only
              split_ifs with hlt hnone
              · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
                subst herr
                step with read_sv_entry_total input cur1 as ⟨r3⟩
                cases r3 with
                | Ok t =>
                  rcases t with ⟨client, clock, p2⟩
                  dsimp only
                  step with hV.on_sv_entry sinkk client clock hInvK as ⟨r4, sinkNext, hInvNext⟩
                  cases r4 with
                  | Ok _ =>
                    step as ⟨iNext, hiNext⟩
                    try simp only [spec_ok]
                    exact ⟨⟨hInvNext, by scalar_tac⟩, by simp [hiNext]; scalar_tac⟩
                  | Err e =>
                    try simp only [spec_ok]
                    exact ⟨⟨hInvNext, hiLe⟩, by simp⟩
                | Err e =>
                  try simp only [spec_ok]
                  exact ⟨⟨hInvK, hiLe⟩, by simp⟩
              · simp [spec_ok, hInvK]
              · simp [spec_ok, hInvK]
            step with hLoop as ⟨sink2, cur1, err, hSink2⟩
            cases err <;> simp [spec_ok, hSink2]
          | Err e =>
            simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
            exact hSink1
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact hSink
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      exact hSink

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
    decoder_v1.read_one_delete_range input cur ⦃ r =>
      match r with
      | .Ok (_, _, q2) => q2.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.read_one_delete_range
  step with read_var_u64_at_total input cur as ⟨r⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨start, q1⟩
    step with read_var_u64_at_total input q1 as ⟨r1, hr1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val1 with ⟨len, q2⟩
      dsimp only at hr1
      have hMax : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, Std.U64.numBits]
      have hCoreMax : core.num.U64.MAX.val = 2 ^ 64 - 1 := by decide
      have hStLe : start.val ≤ core.num.U64.MAX.val := by
        have := start.hBounds
        have hnb : UScalarTy.U64.numBits = 64 := rfl
        rw [hnb] at this
        omega
      step as ⟨i, hi⟩
      split_ifs <;> (try simp only [spec_ok]) <;> (try exact hr1.2) <;> step*
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

theorem read_one_delete_range_sink_spec {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (cur : Std.Usize) (sink : S) (hSink : Inv sink) :
    decoder_v1.read_one_delete_range_sink V input cur sink ⦃ (r, sink') =>
      Inv sink' ∧ match r with | .Ok (_, _, q2) => q2.val ≤ input.length | .Err _ => True ⦄ := by
  unfold decoder_v1.read_one_delete_range_sink
  step with read_var_u64_sink_spec V Inv input hV cur sink hSink as ⟨r, sink1, hInv1, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨start, q1⟩
    step with read_var_u64_sink_spec V Inv input hV q1 sink1 hInv1 as ⟨r1, sink2, hInv2, hr1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val1 with ⟨len, q2⟩
      dsimp only at hr1
      have hMax : Std.U64.max = 2 ^ 64 - 1 := by simp [Std.U64.max, Std.U64.numBits]
      have hCoreMax : core.num.U64.MAX.val = 2 ^ 64 - 1 := by decide
      have hStLe : start.val ≤ core.num.U64.MAX.val := by
        have := start.hBounds
        have hnb : UScalarTy.U64.numBits = 64 := rfl
        rw [hnb] at this
        omega
      step as ⟨i, hi⟩
      split_ifs with hgt
      · step with fail_with_spec V Inv input hV sink2 CodecError.ClockOverflow 0#usize start hInv2
          as ⟨ce, sink3, hInv3⟩
        simp [spec_ok, hInv3]
      · step as ⟨s1, _⟩
        simp [spec_ok, hInv2, hr1.2]
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      exact ⟨hInv2, trivial⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    exact ⟨hInv1, trivial⟩

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
            (if start != «end» then do
               let (status, ds2) ← delete_set.DeleteSetCore.try_insert ds1 client start «end»
               let err ← match status with
                         | .Ok _ => ok none
                         | .Err e => ok (some e)
               ok (ds2, err)
             else ok (ds1, none))
              ⦃ (ds2, _) => DeleteSet.Canonical ds2 ∧
                DeleteSet.totalRanges ds2 ≤ DeleteSet.totalRanges ds1 + 1 ⦄ := by
          split_ifs
          · have hCapStep : DeleteSet.totalRanges ds1 < Std.Usize.max := by scalar_tac
            step with DeleteSet.try_insert_spec ds1 client start «end» hCan1 hCapStep as
              ⟨status, ds2, hc, ht, _⟩
            cases status <;> simpa [bind_ok, spec_ok] using And.intro hc ht
          · simp only [spec_ok]; exact ⟨hCan1, by omega⟩
        step with hDs1 as ⟨ds2, err2, hDs2Can, hDs2Tot⟩
        step as ⟨rIdx1, hrIdx1⟩
        try simp only [spec_ok]
        refine ⟨⟨hDs2Can, by scalar_tac, by omega⟩, ?_⟩
        cases err2 <;> simp [errFlag, hrIdx1] <;> scalar_tac
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
      | .Ok (_, rc, nxtEnt, nxtCur) =>
        nxtEnt.val = total_entries.val + rc.val ∧
        nxtEnt.val ≤ limits.max_collection_entries.val ∧
        nxtCur.val ≤ input.length
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
      step with checked_usize_limit_total ranges_u64 LimitKind.DeleteRanges as ⟨r2⟩
      cases r2 with
      | Ok val2 =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        step with checked_add_limit_total total_entries val2 LimitKind.CollectionEntries as ⟨r3, hr3⟩
        cases r3 with
        | Ok val3 =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          dsimp only at hr3
          split_ifs with hlim
          · simp [spec_ok]
          · simp [spec_ok]
            exact ⟨hr3, by scalar_tac, hr1.2⟩
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
      step with checked_usize_limit_total clients_u64 LimitKind.DeleteClients as ⟨r1⟩
      cases r1 with
      | Ok val1 =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        split_ifs with hlim
        · simp [spec_ok]
        · step as ⟨i2, hi2⟩
          step with check_fits_kind_min_delete_client_total i2 val1 LimitKind.DeleteClients as ⟨r2⟩
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
                  step as ⟨i5, _⟩
                  step with check_fits_kind_min_delete_range_total i5 rc LimitKind.DeleteRanges as ⟨rFit⟩
                  cases rFit with
                  | Ok _ =>
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
theorem wire_id_lt_total (a b : decoder_v1.WireId) :
    decoder_v1.wire_id_lt a b ⦃ _ => True ⦄ := by
  unfold decoder_v1.wire_id_lt
  repeat (first | simp [spec_ok] | split_ifs)

@[local step]
theorem find_wire_id_lower_bound_total
    (items : Slice decoder_v1.WireId) (target : decoder_v1.WireId) :
    decoder_v1.find_wire_id_lower_bound items target ⦃ _ => True ⦄ := by
  unfold decoder_v1.find_wire_id_lower_bound decoder_v1.find_wire_id_lower_bound_loop
  refine loop.spec_decr_nat
    (fun (low, high) => high.val - low.val)
    (fun (low, high) => low.val ≤ high.val ∧ high.val ≤ items.length)
    (fun _ => True)
    _ (0#usize, Slice.len items) ?_ ⟨by scalar_tac, by scalar_tac⟩
  intro ⟨low, high⟩ ⟨hLoHi, hHiLen⟩
  unfold decoder_v1.find_wire_id_lower_bound_loop.body
  dsimp only
  by_cases hlt : low < high
  · rw [if_pos hlt]
    step as ⟨d, hd⟩
    step as ⟨half, hhalf⟩
    step as ⟨mid, hmid⟩
    have hMidLt : mid.val < items.length := by scalar_tac
    step as ⟨wi, _⟩
    step with wire_id_lt_total wi target as ⟨b⟩
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      step as ⟨low1, hlow1⟩
      try simp only [spec_ok]
      exact ⟨by scalar_tac, hHiLen, by scalar_tac⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      try simp only [spec_ok]
      exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
  · rw [if_neg hlt]
    simp [spec_ok]

@[local step]
theorem mark_zero_strings_covered_total
    (pending : Slice decoder_v1.WireId) (max_hi : Slice Std.Usize)
    (client start «end» : Std.U64) :
    decoder_v1.mark_zero_strings_covered pending max_hi client start «end» ⦃ _ => True ⦄ := by
  unfold decoder_v1.mark_zero_strings_covered
  dsimp only
  by_cases hle : «end» ≤ start
  · rw [if_pos hle]
    simp [spec_ok]
  · rw [if_neg hle]
    step as ⟨i, hi⟩
    by_cases hlt2 : i < 2#u64
    · rw [if_pos hlt2]
      simp [spec_ok]
    · rw [if_neg hlt2]
      have hStartMax : start.val + 1 ≤ Std.U64.max := by scalar_tac
      step as ⟨i1, hi1⟩
      step with find_wire_id_lower_bound_total pending { client, clock := i1 } as ⟨lo⟩
      step with find_wire_id_lower_bound_total pending { client, clock := «end» } as ⟨hiBound⟩
      by_cases hlohi : lo < hiBound
      · rw [if_pos hlohi]
        by_cases hloLen : lo < Slice.len max_hi
        · rw [if_pos hloLen]
          have hLoLt : lo.val < max_hi.length := by scalar_tac
          step as ⟨i3, _⟩
          by_cases hgt : hiBound > i3
          · rw [if_pos hgt]
            step*
          · rw [if_neg hgt]
            simp [spec_ok]
        · rw [if_neg hloLen]
          simp [spec_ok]
      · rw [if_neg hlohi]
        simp [spec_ok]

theorem decode_delete_ranges_for_client_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos : Std.Usize) (client : Std.U64) (range_count : Std.Usize)
    (sink : S) (hSink : Inv sink)
    (hStart : start_pos.val ≤ input.length) :
    decoder_v1.decode_delete_ranges_for_client V input start_pos client range_count sink
      ⦃ (r, sink') => Inv sink' ∧ match r with | .Ok nxt => nxt.val ≤ input.length | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_delete_ranges_for_client
  let inv : S × Std.Usize × Std.Usize × Option CodecError → Prop :=
    fun (sink1, cur1, rIdx, _) => Inv sink1 ∧ rIdx.val ≤ range_count.val ∧ cur1.val ≤ input.length
  have hLoop :
      decoder_v1.decode_delete_ranges_for_client_loop V input client range_count sink start_pos 0#usize none
        ⦃ (sink1, cur1, _) => Inv sink1 ∧ cur1.val ≤ input.length ⦄ := by
    unfold decoder_v1.decode_delete_ranges_for_client_loop
    refine loop.spec_decr_nat
      (fun (_, _, rIdx, err) => errFlag err + (range_count.val - rIdx.val))
      inv _ _ (sink, start_pos, 0#usize, none) ?_
      ⟨hSink, by scalar_tac, hStart⟩
    intro ⟨sink1, cur1, rIdx, err1⟩ ⟨hInv1, hrLe, hCur1⟩
    unfold decoder_v1.decode_delete_ranges_for_client_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with read_one_delete_range_sink_spec V Inv input hV cur1 sink1 hInv1 as ⟨r, sink1', hInv1', hr⟩
      cases r with
      | Ok t =>
        rcases t with ⟨start, «end», q2⟩
        dsimp only [uncurry] at hr ⊢
        split_ifs with hne
        · step with hV.on_delete_range sink1' client start «end» hInv1' as ⟨r1, sink2, hInv2⟩
          cases r1 with
          | Ok _ =>
            step as ⟨rIdx1, hrIdx1⟩
            try simp only [spec_ok]
            exact ⟨⟨hInv2, by scalar_tac, hr⟩, by simp [hrIdx1]; scalar_tac⟩
          | Err e =>
            try simp only [spec_ok]
            exact ⟨⟨hInv2, hrLe, hCur1⟩, by simp⟩
        · step as ⟨rIdx1, hrIdx1⟩
          try simp only [spec_ok]
          exact ⟨⟨hInv1', by scalar_tac, hr⟩, by simp [hrIdx1]; scalar_tac⟩
      | Err e =>
        try simp only [spec_ok]
        exact ⟨⟨hInv1', hrLe, hCur1⟩, by simp⟩
    · simp only [spec_ok]; exact ⟨hInv1, hCur1⟩
    · simp only [spec_ok]; exact ⟨hInv1, hCur1⟩
  step with hLoop as ⟨sink1, cur, err, hInv1, hCur⟩
  cases err <;> simp [spec_ok]
  · exact ⟨hInv1, hCur⟩
  · exact hInv1

theorem decode_delete_client_header_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (cur : Std.Usize) (limits : decoder_v1.DecodeLimitsCore) (total_entries : Std.Usize)
    (sink : S) (hSink : Inv sink) :
    decoder_v1.decode_delete_client_header V input cur limits total_entries sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok (_, rc, nxtEnt, nxtCur) =>
        nxtEnt.val = total_entries.val + rc.val ∧
        nxtEnt.val ≤ limits.max_collection_entries.val ∧
        nxtCur.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_delete_client_header
  step with read_var_u64_sink_spec V Inv input hV cur sink hSink as ⟨r, sink1, hInv1, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨client, p1⟩
    step with read_var_u64_sink_spec V Inv input hV p1 sink1 hInv1 as ⟨r1, sink2, hInv2, hr1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val1 with ⟨ranges_u64, p2⟩
      dsimp only at hr1
      step with checked_usize_limit_total ranges_u64 LimitKind.DeleteRanges as ⟨r2⟩
      cases r2 with
      | Ok val2 =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        step with checked_add_limit_total total_entries val2 LimitKind.CollectionEntries as ⟨r3, hr3⟩
        cases r3 with
        | Ok val3 =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          dsimp only at hr3
          split_ifs with hlim
          · simp [spec_ok, hInv2]
          · simp [spec_ok, hInv2]
            exact ⟨hr3, by scalar_tac, hr1.2⟩
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact ⟨hInv2, trivial⟩
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
        exact ⟨hInv2, trivial⟩
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      exact ⟨hInv2, trivial⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    exact ⟨hInv1, trivial⟩

theorem decode_delete_set_v1_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (entries_acc : Std.Usize)
    (sink : S) (hSink : Inv sink) :
    decoder_v1.decode_delete_set_v1 V input pos limits entries_acc sink
      ⦃ (r, sink') => Inv sink' ∧ match r with | .Ok nxt => nxt.val ≤ input.length | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_delete_set_v1
  dsimp only
  split_ifs with hgt
  · step with fail_with_spec V Inv input hV sink CodecError.UnexpectedEof 0#usize 0#u64 hSink
      as ⟨ce, sink0, hSink0⟩
    simp [spec_ok, hSink0]
  · step with read_var_u64_sink_spec V Inv input hV pos sink hSink as ⟨r, sink_v, hSink_v, hr⟩
    cases r with
    | Ok val =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val with ⟨clients_u64, cur⟩
      dsimp only at hr
      step with checked_usize_limit_total clients_u64 LimitKind.DeleteClients as ⟨r1⟩
      cases r1 with
      | Ok val1 =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        split_ifs with hlim
        · simp [spec_ok, hSink_v]
        · step as ⟨i2, hi2⟩
          step with check_fits_kind_sink_spec V Inv input hV i2 val1
            decoder_v1.MIN_DELETE_CLIENT_BYTES LimitKind.DeleteClients sink_v
            (by simp [decoder_v1.MIN_DELETE_CLIENT_BYTES]) hSink_v as ⟨r2, sink0, hSink0⟩
          cases r2 with
          | Ok _ =>
            simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
            have hLoop :
                decoder_v1.decode_delete_set_v1_loop V input limits.max_structs limits.max_clients
                  limits.max_collection_entries limits.max_any_depth limits.max_content_bytes
                  sink0 cur val1 entries_acc 0#usize none
                  ⦃ (sink1, cur1, _) => Inv sink1 ∧ cur1.val ≤ input.length ⦄ := by
              unfold decoder_v1.decode_delete_set_v1_loop
              let inv : S × Std.Usize × Std.Usize × Std.Usize × Option CodecError → Prop :=
                fun (sink1, cur1, _, cIdx, _) => Inv sink1 ∧ cIdx.val ≤ val1.val ∧ cur1.val ≤ input.length
              refine loop.spec_decr_nat
                (fun (_, _, _, cIdx, err) => errFlag err + (val1.val - cIdx.val))
                inv _ _ (sink0, cur, entries_acc, 0#usize, none) ?_
                ⟨hSink0, by scalar_tac, hr.2⟩
              intro ⟨sink1, cur1, totEnt, cIdx, err1⟩ ⟨hInv1, hcLe, hCur1⟩
              unfold decoder_v1.decode_delete_set_v1_loop.body
              dsimp only
              split_ifs with hlt hnone
              · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
                subst herr
                step with decode_delete_client_header_spec V Inv input hV cur1
                  { limits with } totEnt sink1 hInv1 as ⟨r3, sink1a, hInv1a, hr3⟩
                cases r3 with
                | Ok t =>
                  rcases t with ⟨client, rc, nxtEnt, next_cur⟩
                  dsimp only at hr3 ⊢
                  step as ⟨i5, _⟩
                  step with check_fits_kind_sink_spec V Inv input hV i5 rc
                    decoder_v1.MIN_DELETE_RANGE_BYTES LimitKind.DeleteRanges sink1a
                    (by simp [decoder_v1.MIN_DELETE_RANGE_BYTES]) hInv1a as ⟨rFit, sink1', hInv1'⟩
                  cases rFit with
                  | Ok _ =>
                    step with hV.begin_delete_client sink1' client rc hInv1' as ⟨r4, sink2, hInv2⟩
                    cases r4 with
                    | Ok _ =>
                      step with decode_delete_ranges_for_client_spec V Inv input hV next_cur client rc
                        sink2 hInv2 hr3.2.2 as ⟨r5, sink3, hInv3, hNxt5⟩
                      cases r5 with
                      | Ok next_cur2 =>
                        step as ⟨cIdx1, hcIdx1⟩
                        try simp only [spec_ok]
                        exact ⟨⟨hInv3, by scalar_tac, hNxt5⟩, by simp [hcIdx1]; scalar_tac⟩
                      | Err e =>
                        try simp only [spec_ok]
                        exact ⟨⟨hInv3, hcLe, hCur1⟩, by simp⟩
                    | Err e =>
                      try simp only [spec_ok]
                      exact ⟨⟨hInv2, hcLe, hCur1⟩, by simp⟩
                  | Err e =>
                    try simp only [spec_ok]
                    exact ⟨⟨hInv1', hcLe, hCur1⟩, by simp⟩
                | Err e =>
                  try simp only [spec_ok]
                  exact ⟨⟨hInv1a, hcLe, hCur1⟩, by simp⟩
              · simp [spec_ok, hInv1, hCur1]
              · simp [spec_ok, hInv1, hCur1]
            step with hLoop as ⟨sink1, cur1, err, hInv1, hCur1⟩
            cases err <;> simp [spec_ok]
            · exact ⟨hInv1, hCur1⟩
            · exact hInv1
          | Err e =>
            simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
            (try dsimp); exact ⟨hSink0, trivial⟩
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
        (try dsimp); exact ⟨hSink_v, trivial⟩
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
      (try dsimp); exact ⟨hSink_v, trivial⟩

theorem decode_delete_set_v1_total
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkTotal V Inv)
    (pos : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (entries_acc : Std.Usize)
    (sink : S) (hSink : Inv sink) :
    decoder_v1.decode_delete_set_v1 V input pos limits entries_acc sink
      ⦃ (_, sink') => Inv sink' ⦄ := by
  step with decode_delete_set_v1_spec V Inv input (hV.toSpanSafe input) pos limits entries_acc sink hSink
    as ⟨_, sink', hInv, _⟩
  exact hInv

private theorem min_bytes_any_total (tag : Std.U8) :
    (if tag = 9#u8 then ok decoder_v1.MIN_OBJECT_ENTRY_BYTES
     else ok decoder_v1.MIN_ENTRY_BYTES) ⦃ mb => 0 < mb.val ⦄ := by
  split_ifs <;> simp [spec_ok, decoder_v1.MIN_OBJECT_ENTRY_BYTES, decoder_v1.MIN_ENTRY_BYTES]

private theorem kind_any_total (tag : Std.U8) :
    (if tag = 9#u8 then ok LimitKind.AnyObjectEntries
     else ok LimitKind.AnyArrayEntries) ⦃ _ => True ⦄ := by
  split_ifs <;> simp [spec_ok]

private theorem sat_sub_usize_total (a b : Std.Usize) :
    (if a >= b then a - b else ok 0#usize) ⦃ _ => True ⦄ := by
  split_ifs <;> step*

theorem decode_any_scalar_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos : Std.Usize) (tag : Std.U8) (cur : Std.Usize) (sink : S)
    (hSink : Inv sink) (hCur : start_pos.val ≤ cur.val ∧ cur.val ≤ input.length) :
    decoder_v1.decode_any_scalar V input tag cur sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok nxt => start_pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_any_scalar
  try dsimp only; try simp only [Aeneas.Std.uncurry]
  repeat (any_goals (
    first
    | (simp only [spec_ok, Aeneas.Std.uncurry]; (try dsimp only at *); (try simp only [SpanOk] at *);
        (first
        | done
        | (exact ⟨by assumption, by omega, by omega⟩)
        | (exact ⟨by assumption, trivial⟩)
        | (scalar_tac; done)
        | (omega; done)))
    | (apply ite_wp_split <;> intro _)
    | (split_ifs <;> try dsimp only at * <;> try simp only [Aeneas.Std.uncurry])
    | (cases_prod_hyp <;> try dsimp only at * <;> try simp only [Aeneas.Std.uncurry])
    | (cases_result_err <;>
        simp only [core_ops_try_branch_ok, core_ops_try_branch_err, bind_ok,
          core_ops_try_from_residual_err, Aeneas.Std.uncurry] <;>
        try dsimp only at *)
    | (step with (hV.on_any_undefined))
    | (step with (hV.on_any_null))
    | (step with (hV.on_any_i32))
    | (step with (hV.on_any_f32_bits))
    | (step with (hV.on_any_f64_bits))
    | (step with (hV.on_any_i64_bits))
    | (step with (hV.on_any_bool))
    | (step with (hV.on_any_str))
    | (step with (hV.on_any_bytes))
    | (step with (read_var_i32_with_sign_sink_spec V Inv input hV))
    | (step with (read_str_slice_at_spec V Inv input hV))
    | (step with (read_bytes_slice_at_spec V Inv input hV))
    | step
    | ((try simp only [SpanOk, Slice.length] at *);
        cases_and_hyps;
        (first
        | done
        | (assumption; done)
        | (exact ⟨by omega, by omega⟩; done)
        | (omega; done)))
  ))
  all_goals try simp only [spec_ok, Aeneas.Std.uncurry]
  all_goals try (simp only [SpanOk] at *; exact ⟨by assumption, by omega, by omega⟩)
  all_goals try exact ⟨by assumption, trivial⟩

private theorem set_or_push_open_spec
    («open» : alloc.vec.Vec (Std.Usize × Bool)) (depth val1 : Std.Usize) (is_obj : Bool)
    (hDepth : depth.val ≤ «open».length) (hDepMax : depth.val < Std.Usize.max) :
    (if depth < «open».len
     then do
       let (_, index_mut_back) ← «open».index_mut_usize depth
       ok (index_mut_back (val1, is_obj))
     else «open».push (val1, is_obj))
      ⦃ open1 => depth.val + 1 ≤ open1.length ⦄ := by
  split_ifs with hlt
  · have hLt : depth.val < «open».length := by scalar_tac
    step as ⟨_, back, _, hback⟩
    have hLen : (back (val1, is_obj)).length = «open».length := by
      rw [hback]; simp [alloc.vec.Vec.set, alloc.vec.Vec.length]
    omega
  · have hGe : «open».length ≤ depth.val := by scalar_tac
    have hPushCap : «open».length + 1 ≤ Std.Usize.max := by omega
    step as ⟨open1, hOpen1⟩
    simp [hOpen1, alloc.vec.Vec.push, alloc.vec.Vec.length]
    omega

theorem open_any_container_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos : Std.Usize) (is_obj : Bool) (cur : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore)
    (entries depth : Std.Usize) («open» : alloc.vec.Vec (Std.Usize × Bool)) (sink : S)
    (hSink : Inv sink) (hDepth : depth.val ≤ «open».length)
    (hCur : start_pos.val ≤ cur.val ∧ cur.val ≤ input.length) :
    decoder_v1.open_any_container V input is_obj cur limits entries depth «open» sink
      ⦃ (r, open1, sink1) =>
        Inv sink1 ∧
        match r with
        | .Ok (nxt_cur, _, nxt_depth, empty) =>
          nxt_depth.val ≤ open1.length ∧
          (empty = true → 0 < nxt_depth.val) ∧
          start_pos.val ≤ nxt_cur.val ∧ nxt_cur.val ≤ input.length
        | .Err _ => True ⦄ := by
  unfold decoder_v1.open_any_container
  dsimp only
  have hKind :
      (if is_obj then ok LimitKind.AnyObjectEntries else ok LimitKind.AnyArrayEntries) ⦃ _ => True ⦄ := by
    cases is_obj <;> simp [spec_ok]
  have hMinSpec :
      (if is_obj then ok decoder_v1.MIN_OBJECT_ENTRY_BYTES else ok decoder_v1.MIN_ENTRY_BYTES)
        ⦃ mb => 0 < mb.val ⦄ := by
    cases is_obj <;> simp [spec_ok, decoder_v1.MIN_OBJECT_ENTRY_BYTES, decoder_v1.MIN_ENTRY_BYTES]
  step with hKind as ⟨kind⟩
  step with hMinSpec as ⟨min_bytes, hMinPos⟩
  step with read_var_u64_sink_spec V Inv input hV cur sink hSink as ⟨r, sink1, hInv1, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨cnt_u64, p⟩
    dsimp only at hr
    step with checked_usize_limit_total cnt_u64 kind as ⟨r1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      step with checked_add_limit_total entries val1 LimitKind.CollectionEntries as ⟨r2⟩
      cases r2 with
      | Ok val2 =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        by_cases hlim : val2 > limits.max_collection_entries
        · simp only [hlim, ↓reduceIte, spec_ok]
          exact ⟨hInv1, trivial⟩
        · simp only [hlim, ↓reduceIte]
          step as ⟨i1, hi1⟩
          step with check_fits_kind_sink_spec V Inv input hV i1 val1 min_bytes kind sink1
            hMinPos hInv1 as ⟨r3, sink2, hInv2⟩
          cases r3 with
          | Ok _ =>
            simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
            have hUsizeMax : core.num.Usize.MAX.val = Std.Usize.max := by
              simp [core.num.Usize.MAX]
            by_cases hmaxd : depth = core.num.Usize.MAX
            · simp only [hmaxd, ↓reduceIte, spec_ok]
              exact ⟨hInv2, trivial⟩
            · simp only [hmaxd, ↓reduceIte]
              have hDepMax : depth.val < Std.Usize.max := by
                have hNe : depth.val ≠ Std.Usize.max := fun hEq => hmaxd (by scalar_tac)
                scalar_tac
              cases is_obj with
              | true =>
                simp only [↓reduceIte]
                step with hV.on_any_begin_object sink2 val1 hInv2 as ⟨r4, sink3, hInv3⟩
                cases r4 with
                | Ok _ =>
                  simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
                  step with set_or_push_open_spec «open» depth val1 true hDepth hDepMax as ⟨open1, hOpen1⟩
                  step as ⟨i3, hi3⟩
                  exact ⟨hInv3, by omega, fun _ => by omega, by omega, hr.2⟩
                | Err e =>
                  simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                  exact ⟨hInv3, trivial⟩
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                step with hV.on_any_begin_array sink2 val1 hInv2 as ⟨r4, sink3, hInv3⟩
                cases r4 with
                | Ok _ =>
                  simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
                  step with set_or_push_open_spec «open» depth val1 false hDepth hDepMax as ⟨open1, hOpen1⟩
                  step as ⟨i3, hi3⟩
                  exact ⟨hInv3, by omega, fun _ => by omega, by omega, hr.2⟩
                | Err e =>
                  simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                  exact ⟨hInv3, trivial⟩
          | Err e =>
            simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
            exact ⟨hInv2, trivial⟩
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
        exact ⟨hInv1, trivial⟩
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      exact ⟨hInv1, trivial⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    exact ⟨hInv1, trivial⟩

theorem close_finished_containers_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    («open» : Slice (Std.Usize × Bool)) (start_depth : Std.Usize) (sink : S)
    (hSink : Inv sink) (hStartDepth : start_depth.val ≤ «open».length) :
    decoder_v1.close_finished_containers V «open» start_depth sink
      ⦃ (r, sink') =>
        Inv sink' ∧
        match r with
        | .Ok d => d.val ≤ «open».length
        | .Err _ => True ⦄ := by
  unfold decoder_v1.close_finished_containers
  let inv : S × Std.Usize × Bool × Option CodecError → Prop :=
    fun (sinkk, depthk, _, _) => Inv sinkk ∧ depthk.val ≤ «open».length
  have hLoop :
      decoder_v1.close_finished_containers_loop V «open» sink start_depth false none
        ⦃ (sink1, depth1, _) => Inv sink1 ∧ depth1.val ≤ «open».length ⦄ := by
    unfold decoder_v1.close_finished_containers_loop
    refine loop.spec_decr_nat
      (fun (_, depthk, stopk, errk) => stepFlag stopk errk + depthk.val)
      inv _ _ (sink, start_depth, false, none) ?_ ⟨hSink, hStartDepth⟩
    intro ⟨sinkk, depthk, stopk, errk⟩ ⟨hInvK, hDepK⟩
    unfold decoder_v1.close_finished_containers_loop.body
    dsimp only
    split_ifs with hgt hstop hnone
    · simp [spec_ok, hInvK, hDepK]
    · have herr : errk = none := (is_none_eq_true_iff errk).1 hnone
      subst herr
      step as ⟨i, hi⟩
      step as ⟨p, hp⟩
      split_ifs with hzero
      · step with hV.on_any_end_container sinkk hInvK as ⟨r, sink1, hInv1⟩
        cases r with
        | Ok _ =>
          try simp only [spec_ok]
          exact ⟨⟨hInv1, by omega⟩, by simp [stepFlag, hstop]; omega⟩
        | Err e =>
          try simp only [spec_ok]
          exact ⟨⟨hInv1, hDepK⟩, by simp [stepFlag, hstop]⟩
      · try simp only [spec_ok]
        exact ⟨⟨hInvK, hDepK⟩, by simp [stepFlag, hstop]⟩
    · simp [spec_ok, hInvK, hDepK]
    · simp [spec_ok, hInvK, hDepK]
  step with hLoop as ⟨sink1, depth1, err, hInv1, hDep1⟩
  cases err <;> simp [spec_ok, hInv1, hDep1]

theorem decode_any_step_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos start_cur : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (entries depth : Std.Usize) («open» : alloc.vec.Vec (Std.Usize × Bool)) (sink : S)
    (hSink : Inv sink) (hDepthPos : 0 < depth.val) (hDepth : depth.val ≤ «open».length)
    (hCur : start_pos.val ≤ start_cur.val ∧ start_cur.val ≤ input.length) :
    decoder_v1.decode_any_step V input start_cur limits entries depth «open» sink
      ⦃ (r, open1, sink1) =>
        Inv sink1 ∧
        match r with
        | .Ok (next_cur, _, next_depth) =>
          next_depth.val ≤ open1.length ∧
          start_pos.val ≤ next_cur.val ∧ next_cur.val ≤ input.length
        | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_any_step
  dsimp only
  step as ⟨i, hi⟩
  step as ⟨p, hp⟩
  by_cases hzero : p = 0#usize
  · simp only [hzero, ↓reduceIte]
    step with hV.on_any_end_container sink hSink as ⟨r, sink1, hSink1⟩
    cases r with
    | Ok _ =>
      simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
      exact ⟨hSink1, by omega, hCur.1, hCur.2⟩
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      exact ⟨hSink1, trivial⟩
  · simp only [hzero, ↓reduceIte]
    step as ⟨i2, hi2⟩
    step as ⟨v2, b1, back, hpair2, hback⟩
    try simp only [Aeneas.Std.uncurry]
    have hLenOpen : (back (i2, b1)).length = «open».length := by
      rw [hback]; simp [alloc.vec.Vec.set, alloc.vec.Vec.length]
    cases hp with
    | true =>
      simp only [↓reduceIte]
      step with read_str_slice_at_spec V Inv input hV start_cur sink hSink as ⟨r, sink1, hSink1, hr⟩
      cases r with
      | Ok val =>
        simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
        dsimp only [SpanOk] at hr
        step with hV.on_any_object_key sink1 val hSink1 hr.2 as ⟨r1, sink2, hSink2⟩
        cases r1 with
        | Ok _ =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          split_ifs with hdep
          · simp [spec_ok, hSink2]
          · step with read_u8_at_total input val.«end» as ⟨r2, hr2⟩
            cases r2 with
            | Ok val1 =>
              simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
              rcases val1 with ⟨raw_tag, after_tag⟩
              dsimp only at hr2
              step as ⟨tag, htag⟩
              have hDepthBack : depth.val ≤ (back (i2, b1)).length := by omega
              have hAfterCur : start_pos.val ≤ after_tag.val ∧ after_tag.val ≤ input.length :=
                ⟨by omega, hr2.2⟩
              split_ifs with h9 h10
              · step with open_any_container_spec V Inv input hV start_pos (decide (tag = 9#u8)) after_tag
                  limits entries depth (back (i2, b1)) sink2 hSink2 hDepthBack hAfterCur
                  as ⟨r3, open2, sink3, hSink3, hRes3⟩
                cases r3 with
                | Ok val2 =>
                  simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
                  rcases val2 with ⟨next_cur, next_entries, next_depth, empty⟩
                  dsimp only at hRes3
                  split_ifs with hemp
                  · have hStartDep : next_depth.val ≤ (alloc.vec.Vec.deref open2).length := by
                      simpa [alloc.vec.Vec.deref, Slice.length] using hRes3.1
                    step with close_finished_containers_spec V Inv input hV (alloc.vec.Vec.deref open2)
                      next_depth sink3 hSink3 hStartDep as ⟨r4, sink4, hSink4, hRes4⟩
                    cases r4 with
                    | Ok val3 =>
                      simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
                      have hV3 : val3.val ≤ open2.length := by
                        simpa [alloc.vec.Vec.deref, Slice.length] using hRes4
                      exact ⟨hSink4, hV3, hRes3.2.2.1, hRes3.2.2.2⟩
                    | Err e =>
                      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                      exact ⟨hSink4, trivial⟩
                  · simp only [spec_ok]
                    exact ⟨hSink3, hRes3.1, hRes3.2.2.1, hRes3.2.2.2⟩
                | Err e =>
                  simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                  exact ⟨hSink3, trivial⟩
              · step with open_any_container_spec V Inv input hV start_pos (decide (tag = 9#u8)) after_tag
                  limits entries depth (back (i2, b1)) sink2 hSink2 hDepthBack hAfterCur
                  as ⟨r3, open2, sink3, hSink3, hRes3⟩
                cases r3 with
                | Ok val2 =>
                  simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
                  rcases val2 with ⟨next_cur, next_entries, next_depth, empty⟩
                  dsimp only at hRes3
                  split_ifs with hemp
                  · have hStartDep : next_depth.val ≤ (alloc.vec.Vec.deref open2).length := by
                      simpa [alloc.vec.Vec.deref, Slice.length] using hRes3.1
                    step with close_finished_containers_spec V Inv input hV (alloc.vec.Vec.deref open2)
                      next_depth sink3 hSink3 hStartDep as ⟨r4, sink4, hSink4, hRes4⟩
                    cases r4 with
                    | Ok val3 =>
                      simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
                      have hV3 : val3.val ≤ open2.length := by
                        simpa [alloc.vec.Vec.deref, Slice.length] using hRes4
                      exact ⟨hSink4, hV3, hRes3.2.2.1, hRes3.2.2.2⟩
                    | Err e =>
                      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                      exact ⟨hSink4, trivial⟩
                  · simp only [spec_ok]
                    exact ⟨hSink3, hRes3.1, hRes3.2.2.1, hRes3.2.2.2⟩
                | Err e =>
                  simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                  exact ⟨hSink3, trivial⟩
              · step with decode_any_scalar_spec V Inv input hV start_pos tag after_tag sink2
                  hSink2 hAfterCur as ⟨r3, sink3, hSink3, hRes3⟩
                cases r3 with
                | Ok val2 =>
                  simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
                  step as ⟨p3, hp3⟩
                  split_ifs with hz3
                  · have hStartDep : depth.val ≤ (alloc.vec.Vec.deref (back (i2, b1))).length := by
                      simpa [alloc.vec.Vec.deref, Slice.length, hLenOpen] using hDepth
                    step with close_finished_containers_spec V Inv input hV
                      (alloc.vec.Vec.deref (back (i2, b1))) depth sink3
                      hSink3 hStartDep as ⟨r4, sink4, hSink4, hRes4⟩
                    cases r4 with
                    | Ok val3 =>
                      simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
                      have hV3 : val3.val ≤ (back (i2, b1)).length := by
                        simpa [alloc.vec.Vec.deref, Slice.length] using hRes4
                      exact ⟨hSink4, hV3, hRes3.1, hRes3.2⟩
                    | Err e =>
                      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                      exact ⟨hSink4, trivial⟩
                  · simp only [spec_ok]
                    exact ⟨hSink3, by omega, hRes3.1, hRes3.2⟩
                | Err e =>
                  simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                  exact ⟨hSink3, trivial⟩
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
              exact ⟨hSink2, trivial⟩
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact ⟨hSink2, trivial⟩
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
        exact ⟨hSink1, trivial⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hdep : depth > limits.max_any_depth
      · simp only [hdep, ↓reduceIte, spec_ok]
        exact ⟨hSink, trivial⟩
      · simp only [hdep, ↓reduceIte]
        step with read_u8_at_total input start_cur as ⟨r, hr⟩
        cases r with
        | Ok val =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          rcases val with ⟨raw_tag, after_tag⟩
          dsimp only at hr
          step as ⟨tag, htag⟩
          have hDepthBack : depth.val ≤ (back (i2, b1)).length := by omega
          have hAfterCur : start_pos.val ≤ after_tag.val ∧ after_tag.val ≤ input.length :=
            ⟨by omega, hr.2⟩
          split_ifs with h9 h10
          · step with open_any_container_spec V Inv input hV start_pos (decide (tag = 9#u8)) after_tag
              limits entries depth (back (i2, b1)) sink hSink hDepthBack hAfterCur
              as ⟨r1, open2, sink1, hSink1, hRes1⟩
            cases r1 with
            | Ok val1 =>
              simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
              rcases val1 with ⟨next_cur, next_entries, next_depth, empty⟩
              dsimp only at hRes1
              split_ifs with hemp
              · have hStartDep : next_depth.val ≤ (alloc.vec.Vec.deref open2).length := by
                  simpa [alloc.vec.Vec.deref, Slice.length] using hRes1.1
                step with close_finished_containers_spec V Inv input hV (alloc.vec.Vec.deref open2)
                  next_depth sink1 hSink1 hStartDep as ⟨r2, sink2, hSink2, hRes2⟩
                cases r2 with
                | Ok val2 =>
                  simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
                  have hV2 : val2.val ≤ open2.length := by
                    simpa [alloc.vec.Vec.deref, Slice.length] using hRes2
                  exact ⟨hSink2, hV2, hRes1.2.2.1, hRes1.2.2.2⟩
                | Err e =>
                  simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                  exact ⟨hSink2, trivial⟩
              · simp only [spec_ok]
                exact ⟨hSink1, hRes1.1, hRes1.2.2.1, hRes1.2.2.2⟩
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
              exact ⟨hSink1, trivial⟩
          · step with open_any_container_spec V Inv input hV start_pos (decide (tag = 9#u8)) after_tag
              limits entries depth (back (i2, b1)) sink hSink hDepthBack hAfterCur
              as ⟨r1, open2, sink1, hSink1, hRes1⟩
            cases r1 with
            | Ok val1 =>
              simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
              rcases val1 with ⟨next_cur, next_entries, next_depth, empty⟩
              dsimp only at hRes1
              split_ifs with hemp
              · have hStartDep : next_depth.val ≤ (alloc.vec.Vec.deref open2).length := by
                  simpa [alloc.vec.Vec.deref, Slice.length] using hRes1.1
                step with close_finished_containers_spec V Inv input hV (alloc.vec.Vec.deref open2)
                  next_depth sink1 hSink1 hStartDep as ⟨r2, sink2, hSink2, hRes2⟩
                cases r2 with
                | Ok val2 =>
                  simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
                  have hV2 : val2.val ≤ open2.length := by
                    simpa [alloc.vec.Vec.deref, Slice.length] using hRes2
                  exact ⟨hSink2, hV2, hRes1.2.2.1, hRes1.2.2.2⟩
                | Err e =>
                  simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                  exact ⟨hSink2, trivial⟩
              · simp only [spec_ok]
                exact ⟨hSink1, hRes1.1, hRes1.2.2.1, hRes1.2.2.2⟩
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
              exact ⟨hSink1, trivial⟩
          · step with decode_any_scalar_spec V Inv input hV start_pos tag after_tag sink
              hSink hAfterCur as ⟨r1, sink1, hSink1, hRes1⟩
            cases r1 with
            | Ok val1 =>
              simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
              step as ⟨p3, hp3⟩
              split_ifs with hz3
              · have hStartDep : depth.val ≤ (alloc.vec.Vec.deref (back (i2, b1))).length := by
                  simpa [alloc.vec.Vec.deref, Slice.length, hLenOpen] using hDepth
                step with close_finished_containers_spec V Inv input hV
                  (alloc.vec.Vec.deref (back (i2, b1))) depth sink1
                  hSink1 hStartDep as ⟨r2, sink2, hSink2, hRes2⟩
                cases r2 with
                | Ok val2 =>
                  simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
                  have hV2 : val2.val ≤ (back (i2, b1)).length := by
                    simpa [alloc.vec.Vec.deref, Slice.length] using hRes2
                  exact ⟨hSink2, hV2, hRes1.1, hRes1.2⟩
                | Err e =>
                  simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                  exact ⟨hSink2, trivial⟩
              · simp only [spec_ok]
                exact ⟨hSink1, by omega, hRes1.1, hRes1.2⟩
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
              exact ⟨hSink1, trivial⟩
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact ⟨hSink, trivial⟩

private theorem decode_any_max_steps_cont_total {α : Type _}
    (input : Slice Std.U8) (cur max_any_depth : Std.Usize)
    (k : Std.Usize → Result α) (P : α → Prop)
    (hk : ∀ max_steps, k max_steps ⦃ P ⦄) :
    (do
      let i := Slice.len input
      let rem ←
        if i >= cur then
          let i1 := Slice.len input
          i1 - cur
        else ok 0#usize
      let i1 ← core.num.Usize.MAX / 2#usize
      let rem2 ← if rem <= i1 then rem * 2#usize else ok core.num.Usize.MAX
      let i2 ← core.num.Usize.MAX - rem2
      let rem_d ← if max_any_depth <= i2 then rem2 + max_any_depth else ok core.num.Usize.MAX
      let i3 ← core.num.Usize.MAX - rem_d
      let max_steps ← if 2#usize <= i3 then rem_d + 2#usize else ok core.num.Usize.MAX
      k max_steps) ⦃ P ⦄ := by
  have hUsizeMax : core.num.Usize.MAX.val = Std.Usize.max := by
    simp [core.num.Usize.MAX]
  have hRemSpec :
      (if Slice.len input >= cur then let i1 := Slice.len input; i1 - cur else ok 0#usize)
        ⦃ _ => True ⦄ := by
    split_ifs
    · dsimp only; step*
    · simp [spec_ok]
  step with hRemSpec as ⟨rem⟩
  step as ⟨i1, hi1⟩
  have hRem2Spec : (if rem <= i1 then rem * 2#usize else ok core.num.Usize.MAX) ⦃ _ => True ⦄ := by
    split_ifs with hle
    · have : rem.val * 2 ≤ Std.Usize.max := by scalar_tac
      step*
    · simp [spec_ok]
  step with hRem2Spec as ⟨rem2⟩
  have hRem2Le : rem2.val ≤ core.num.Usize.MAX.val := by
    have := rem2.hBounds; scalar_tac
  step as ⟨i2, hi2⟩
  have hRemDSpec :
      (if max_any_depth <= i2 then rem2 + max_any_depth else ok core.num.Usize.MAX) ⦃ _ => True ⦄ := by
    split_ifs with hle
    · have : rem2.val + max_any_depth.val ≤ Std.Usize.max := by scalar_tac
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
  exact hk max_steps

private theorem decode_any_v1_loop_body_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos : Std.Usize) (limits : decoder_v1.DecodeLimitsCore) (max_steps : Std.Usize)
    (sinkk : S) (openk : alloc.vec.Vec (Std.Usize × Bool))
    (curk entk depthk stepk : Std.Usize) (errk : Option CodecError)
    (hState : Inv sinkk ∧ stepk.val ≤ max_steps.val ∧
      (errk = none → depthk.val ≤ openk.length) ∧ start_pos.val ≤ curk.val ∧ curk.val ≤ input.length) :
    (if stepk < max_steps then
      if depthk > 0#usize then
        if errk.isNone = true then do
          let step1 ← stepk + 1#usize
          let (r, open1, sink1) ← decoder_v1.decode_any_step V input curk limits entk depthk openk sinkk
          match r with
          | .Ok t =>
            let (next_cur, next_entries, next_depth) := t
            ok (cont (sink1, open1, next_cur, next_entries, next_depth, step1, errk))
          | .Err e =>
            ok (cont (sink1, open1, curk, entk, depthk, step1, some e))
        else ok (done (sinkk, curk, entk, depthk, errk))
      else ok (done (sinkk, curk, entk, depthk, errk))
    else ok (done (sinkk, curk, entk, depthk, errk)))
      ⦃ cf =>
        match cf with
        | .cont (sink2, open2, cur2, _, depth2, step2, err2) =>
          (Inv sink2 ∧ step2.val ≤ max_steps.val ∧
            (err2 = none → depth2.val ≤ open2.length) ∧ start_pos.val ≤ cur2.val ∧ cur2.val ≤ input.length) ∧
          (errFlag err2 + (max_steps.val - step2.val)) <
            (errFlag errk + (max_steps.val - stepk.val))
        | .done (sink2, cur2, _, _, _) =>
          Inv sink2 ∧ start_pos.val ≤ cur2.val ∧ cur2.val ≤ input.length ⦄ := by
  rcases hState with ⟨hInvK, hStep, hDepthK, hCurLo, hCurHi⟩
  split_ifs with hlt hdep hnone
  · have herr : errk = none := by cases errk <;> simp_all
    subst herr
    have hDepthPos : 0 < depthk.val := by scalar_tac
    step as ⟨step2, hStep2⟩
    step with decode_any_step_spec V Inv input hV start_pos curk limits entk depthk openk sinkk
      hInvK hDepthPos (hDepthK rfl) ⟨hCurLo, hCurHi⟩ as ⟨r1, open2, sink2, hInv2, hRes2⟩
    cases r1 with
    | Ok t =>
      rcases t with ⟨next_cur, next_entries, next_depth⟩
      simp [spec_ok]
      refine ⟨hInv2, by scalar_tac, hRes2.1, hRes2.2.1, hRes2.2.2, ?_⟩
      simp [hStep2]; scalar_tac
    | Err e =>
      simp [spec_ok]
      refine ⟨hInv2, by scalar_tac, hCurLo, hCurHi, ?_⟩
      simp [hStep2]; scalar_tac
  · simp [spec_ok, hInvK, hCurLo, hCurHi]
  · simp [spec_ok, hInvK, hCurLo, hCurHi]
  · simp [spec_ok, hInvK, hCurLo, hCurHi]

theorem decode_any_v1_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (entries_acc : Std.Usize) (sink : S) (hSink : Inv sink)
    (hStart : start_pos.val ≤ input.length) :
    decoder_v1.decode_any_v1 V input start_pos limits entries_acc sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok (nxt, _) => start_pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_any_v1
  dsimp only
  step with hV.on_any_start sink hSink as ⟨r, sink1, hSink1⟩
  cases r with
  | Ok _ =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    step with read_u8_at_total input start_pos as ⟨r1, hr1⟩
    cases r1 with
    | Ok val =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      rcases val with ⟨raw_tag, after_tag⟩
      dsimp only at hr1
      step as ⟨first_tag, _⟩
      have hAfter : start_pos.val ≤ after_tag.val ∧ after_tag.val ≤ input.length := ⟨by omega, hr1.2⟩
      split_ifs with hnot9 hnot10
      · step with decode_any_scalar_spec V Inv input hV start_pos first_tag after_tag sink1
          hSink1 hAfter as ⟨r2, sink2, hSink2, hRes2⟩
        cases r2 with
        | Ok val1 =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          step with hV.on_any_finish sink2 { start := start_pos, «end» := val1 } hSink2
            hRes2 as ⟨r3, sink3, hSink3⟩
          cases r3 with
          | Ok _ =>
            simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
            exact ⟨hSink3, hRes2⟩
          | Err e =>
            simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
            exact ⟨hSink3, trivial⟩
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact ⟨hSink2, trivial⟩
      · step with open_any_container_spec V Inv input hV start_pos (decide (first_tag = 9#u8)) after_tag
          limits entries_acc 0#usize (alloc.vec.Vec.new (Std.Usize × Bool)) sink1 hSink1
          (by simp [alloc.vec.Vec.new, alloc.vec.Vec.length]) hAfter as ⟨r2, «open», sink2, hSink2, hOpen2⟩
        cases r2 with
        | Ok val1 =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          rcases val1 with ⟨cur, entries, depth, empty⟩
          try dsimp only at hOpen2
          try simp only [Aeneas.Std.uncurry]
          try dsimp only
          by_cases hemp : empty = true
          · simp only [hemp, ↓reduceIte]
            have hStartDep : depth.val ≤ (alloc.vec.Vec.deref «open»).length := by
              simpa [alloc.vec.Vec.deref, Slice.length] using hOpen2.1
            step with close_finished_containers_spec V Inv input hV (alloc.vec.Vec.deref «open»)
              depth sink2 hSink2 hStartDep as ⟨r3, sink3, hSink3, hClose3⟩
            cases r3 with
            | Ok val2 =>
              simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
              refine decode_any_max_steps_cont_total input cur limits.max_any_depth _ _ (fun max_steps => ?_)
              have hDepVal2 : val2.val ≤ «open».length := by
                simpa [alloc.vec.Vec.deref, Slice.length] using hClose3
              have hLoop :
                  decoder_v1.decode_any_v1_loop0 V input limits.max_structs limits.max_clients
                    limits.max_collection_entries limits.max_any_depth limits.max_content_bytes
                    sink3 «open» cur entries val2 max_steps 0#usize none
                    ⦃ (sink4, cur1, _, _, _) =>
                      Inv sink4 ∧ start_pos.val ≤ cur1.val ∧ cur1.val ≤ input.length ⦄ := by
                unfold decoder_v1.decode_any_v1_loop0
                let inv : S × alloc.vec.Vec (Std.Usize × Bool) × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Option CodecError → Prop :=
                  fun (sinkk, openk, curk, _, depthk, stepk, errk) =>
                    Inv sinkk ∧ stepk.val ≤ max_steps.val ∧ (errk = none → depthk.val ≤ openk.length) ∧
                    start_pos.val ≤ curk.val ∧ curk.val ≤ input.length
                refine loop.spec_decr_nat
                  (fun (_, _, _, _, _, stepk, errk) => errFlag errk + (max_steps.val - stepk.val))
                  inv _ _ (sink3, «open», cur, entries, val2, 0#usize, none) ?_
                  ⟨hSink3, by scalar_tac, fun _ => hDepVal2, hOpen2.2.2.1, hOpen2.2.2.2⟩
                intro ⟨sinkk, openk, curk, entk, depthk, stepk, errk⟩ hInvK
                unfold decoder_v1.decode_any_v1_loop0.body
                dsimp only [inv]
                try simp only [letFun]
                refine spec_mono (decode_any_v1_loop_body_spec V Inv input hV start_pos
                  ⟨limits.max_structs, limits.max_clients, limits.max_collection_entries,
                    limits.max_any_depth, limits.max_content_bytes⟩
                  max_steps sinkk openk curk entk depthk stepk errk hInvK) (fun cf hcf => ?_)
                cases cf with
                | cont x =>
                  rcases x with ⟨_, _, _, _, _, _, _⟩
                  dsimp only at hcf ⊢
                  exact hcf
                | done y =>
                  rcases y with ⟨_, _, _, _, _⟩
                  dsimp only at hcf ⊢
                  exact hcf
              step with hLoop as ⟨sink4, cur1, entries1, depth1, err, hSink4, hLo4, hHi4⟩
              cases err with
              | none =>
                split_ifs with hnz
                · simp [spec_ok, hSink4]
                · step with hV.on_any_finish sink4 { start := start_pos, «end» := cur1 } hSink4
                    ⟨hLo4, hHi4⟩ as ⟨r4, sink5, hSink5⟩
                  cases r4 with
                  | Ok _ => simp only [core_ops_try_branch_ok, bind_ok, spec_ok]; exact ⟨hSink5, hLo4, hHi4⟩
                  | Err e => simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]; exact ⟨hSink5, trivial⟩
              | some e => simp [spec_ok, hSink4]
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
              exact ⟨hSink3, trivial⟩
          · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
            refine decode_any_max_steps_cont_total input cur limits.max_any_depth _ _ (fun max_steps => ?_)
            have hLoop :
                decoder_v1.decode_any_v1_loop1 V input limits.max_structs limits.max_clients
                  limits.max_collection_entries limits.max_any_depth limits.max_content_bytes
                  sink2 «open» cur entries depth max_steps 0#usize none
                  ⦃ (sink3, cur1, _, _, _) =>
                    Inv sink3 ∧ start_pos.val ≤ cur1.val ∧ cur1.val ≤ input.length ⦄ := by
              unfold decoder_v1.decode_any_v1_loop1
              let inv : S × alloc.vec.Vec (Std.Usize × Bool) × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Option CodecError → Prop :=
                fun (sinkk, openk, curk, _, depthk, stepk, errk) =>
                  Inv sinkk ∧ stepk.val ≤ max_steps.val ∧ (errk = none → depthk.val ≤ openk.length) ∧
                  start_pos.val ≤ curk.val ∧ curk.val ≤ input.length
              refine loop.spec_decr_nat
                (fun (_, _, _, _, _, stepk, errk) => errFlag errk + (max_steps.val - stepk.val))
                inv _ _ (sink2, «open», cur, entries, depth, 0#usize, none) ?_
                ⟨hSink2, by scalar_tac, fun _ => hOpen2.1, hOpen2.2.2.1, hOpen2.2.2.2⟩
              intro ⟨sinkk, openk, curk, entk, depthk, stepk, errk⟩ hInvK
              unfold decoder_v1.decode_any_v1_loop1.body
              dsimp only [inv]
              try simp only [letFun]
              refine spec_mono (decode_any_v1_loop_body_spec V Inv input hV start_pos
                ⟨limits.max_structs, limits.max_clients, limits.max_collection_entries,
                  limits.max_any_depth, limits.max_content_bytes⟩
                max_steps sinkk openk curk entk depthk stepk errk hInvK) (fun cf hcf => ?_)
              cases cf with
              | cont x =>
                rcases x with ⟨_, _, _, _, _, _, _⟩
                dsimp only at hcf ⊢
                exact hcf
              | done y =>
                rcases y with ⟨_, _, _, _, _⟩
                dsimp only at hcf ⊢
                exact hcf
            step with hLoop as ⟨sink3, cur1, entries1, depth1, err, hSink3, hLo3, hHi3⟩
            cases err with
            | none =>
              split_ifs with hnz
              · simp [spec_ok, hSink3]
              · step with hV.on_any_finish sink3 { start := start_pos, «end» := cur1 } hSink3
                  ⟨hLo3, hHi3⟩ as ⟨r3, sink4, hSink4⟩
                cases r3 with
                | Ok _ => simp only [core_ops_try_branch_ok, bind_ok, spec_ok]; exact ⟨hSink4, hLo3, hHi3⟩
                | Err e => simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]; exact ⟨hSink4, trivial⟩
            | some e => simp [spec_ok, hSink3]
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact ⟨hSink2, trivial⟩
      · step with open_any_container_spec V Inv input hV start_pos (decide (first_tag = 9#u8)) after_tag
          limits entries_acc 0#usize (alloc.vec.Vec.new (Std.Usize × Bool)) sink1 hSink1
          (by simp [alloc.vec.Vec.new, alloc.vec.Vec.length]) hAfter as ⟨r2, «open», sink2, hSink2, hOpen2⟩
        cases r2 with
        | Ok val1 =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          rcases val1 with ⟨cur, entries, depth, empty⟩
          try dsimp only at hOpen2
          try simp only [Aeneas.Std.uncurry]
          try dsimp only
          by_cases hemp : empty = true
          · simp only [hemp, ↓reduceIte]
            have hStartDep : depth.val ≤ (alloc.vec.Vec.deref «open»).length := by
              simpa [alloc.vec.Vec.deref, Slice.length] using hOpen2.1
            step with close_finished_containers_spec V Inv input hV (alloc.vec.Vec.deref «open»)
              depth sink2 hSink2 hStartDep as ⟨r3, sink3, hSink3, hClose3⟩
            cases r3 with
            | Ok val2 =>
              simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
              refine decode_any_max_steps_cont_total input cur limits.max_any_depth _ _ (fun max_steps => ?_)
              have hDepVal2 : val2.val ≤ «open».length := by
                simpa [alloc.vec.Vec.deref, Slice.length] using hClose3
              have hLoop :
                  decoder_v1.decode_any_v1_loop2 V input limits.max_structs limits.max_clients
                    limits.max_collection_entries limits.max_any_depth limits.max_content_bytes
                    sink3 «open» cur entries val2 max_steps 0#usize none
                    ⦃ (sink4, cur1, _, _, _) =>
                      Inv sink4 ∧ start_pos.val ≤ cur1.val ∧ cur1.val ≤ input.length ⦄ := by
                unfold decoder_v1.decode_any_v1_loop2
                let inv : S × alloc.vec.Vec (Std.Usize × Bool) × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Option CodecError → Prop :=
                  fun (sinkk, openk, curk, _, depthk, stepk, errk) =>
                    Inv sinkk ∧ stepk.val ≤ max_steps.val ∧ (errk = none → depthk.val ≤ openk.length) ∧
                    start_pos.val ≤ curk.val ∧ curk.val ≤ input.length
                refine loop.spec_decr_nat
                  (fun (_, _, _, _, _, stepk, errk) => errFlag errk + (max_steps.val - stepk.val))
                  inv _ _ (sink3, «open», cur, entries, val2, 0#usize, none) ?_
                  ⟨hSink3, by scalar_tac, fun _ => hDepVal2, hOpen2.2.2.1, hOpen2.2.2.2⟩
                intro ⟨sinkk, openk, curk, entk, depthk, stepk, errk⟩ hInvK
                unfold decoder_v1.decode_any_v1_loop2.body
                dsimp only [inv]
                try simp only [letFun]
                refine spec_mono (decode_any_v1_loop_body_spec V Inv input hV start_pos
                  ⟨limits.max_structs, limits.max_clients, limits.max_collection_entries,
                    limits.max_any_depth, limits.max_content_bytes⟩
                  max_steps sinkk openk curk entk depthk stepk errk hInvK) (fun cf hcf => ?_)
                cases cf with
                | cont x =>
                  rcases x with ⟨_, _, _, _, _, _, _⟩
                  dsimp only at hcf ⊢
                  exact hcf
                | done y =>
                  rcases y with ⟨_, _, _, _, _⟩
                  dsimp only at hcf ⊢
                  exact hcf
              step with hLoop as ⟨sink4, cur1, entries1, depth1, err, hSink4, hLo4, hHi4⟩
              cases err with
              | none =>
                split_ifs with hnz
                · simp [spec_ok, hSink4]
                · step with hV.on_any_finish sink4 { start := start_pos, «end» := cur1 } hSink4
                    ⟨hLo4, hHi4⟩ as ⟨r4, sink5, hSink5⟩
                  cases r4 with
                  | Ok _ => simp only [core_ops_try_branch_ok, bind_ok, spec_ok]; exact ⟨hSink5, hLo4, hHi4⟩
                  | Err e => simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]; exact ⟨hSink5, trivial⟩
              | some e => simp [spec_ok, hSink4]
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
              exact ⟨hSink3, trivial⟩
          · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
            refine decode_any_max_steps_cont_total input cur limits.max_any_depth _ _ (fun max_steps => ?_)
            have hLoop :
                decoder_v1.decode_any_v1_loop3 V input limits.max_structs limits.max_clients
                  limits.max_collection_entries limits.max_any_depth limits.max_content_bytes
                  sink2 «open» cur entries depth max_steps 0#usize none
                  ⦃ (sink3, cur1, _, _, _) =>
                    Inv sink3 ∧ start_pos.val ≤ cur1.val ∧ cur1.val ≤ input.length ⦄ := by
              unfold decoder_v1.decode_any_v1_loop3
              let inv : S × alloc.vec.Vec (Std.Usize × Bool) × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Option CodecError → Prop :=
                fun (sinkk, openk, curk, _, depthk, stepk, errk) =>
                  Inv sinkk ∧ stepk.val ≤ max_steps.val ∧ (errk = none → depthk.val ≤ openk.length) ∧
                  start_pos.val ≤ curk.val ∧ curk.val ≤ input.length
              refine loop.spec_decr_nat
                (fun (_, _, _, _, _, stepk, errk) => errFlag errk + (max_steps.val - stepk.val))
                inv _ _ (sink2, «open», cur, entries, depth, 0#usize, none) ?_
                ⟨hSink2, by scalar_tac, fun _ => hOpen2.1, hOpen2.2.2.1, hOpen2.2.2.2⟩
              intro ⟨sinkk, openk, curk, entk, depthk, stepk, errk⟩ hInvK
              unfold decoder_v1.decode_any_v1_loop3.body
              dsimp only [inv]
              try simp only [letFun]
              refine spec_mono (decode_any_v1_loop_body_spec V Inv input hV start_pos
                ⟨limits.max_structs, limits.max_clients, limits.max_collection_entries,
                  limits.max_any_depth, limits.max_content_bytes⟩
                max_steps sinkk openk curk entk depthk stepk errk hInvK) (fun cf hcf => ?_)
              cases cf with
              | cont x =>
                rcases x with ⟨_, _, _, _, _, _, _⟩
                dsimp only at hcf ⊢
                exact hcf
              | done y =>
                rcases y with ⟨_, _, _, _, _⟩
                dsimp only at hcf ⊢
                exact hcf
            step with hLoop as ⟨sink3, cur1, entries1, depth1, err, hSink3, hLo3, hHi3⟩
            cases err with
            | none =>
              split_ifs with hnz
              · simp [spec_ok, hSink3]
              · step with hV.on_any_finish sink3 { start := start_pos, «end» := cur1 } hSink3
                  ⟨hLo3, hHi3⟩ as ⟨r3, sink4, hSink4⟩
                cases r3 with
                | Ok _ => simp only [core_ops_try_branch_ok, bind_ok, spec_ok]; exact ⟨hSink4, hLo3, hHi3⟩
                | Err e => simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]; exact ⟨hSink4, trivial⟩
            | some e => simp [spec_ok, hSink3]
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact ⟨hSink2, trivial⟩
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      exact ⟨hSink1, trivial⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    exact ⟨hSink1, trivial⟩

theorem decode_any_v1_total
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkTotal V Inv)
    (start_pos : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (entries_acc : Std.Usize) (sink : S) (hSink : Inv sink)
    (hStart : start_pos.val ≤ input.length) :
    decoder_v1.decode_any_v1 V input start_pos limits entries_acc sink
      ⦃ (_, sink') => Inv sink' ⦄ := by
  step with decode_any_v1_spec V Inv input (hV.toSpanSafe input) start_pos limits entries_acc sink
    hSink hStart as ⟨_, sink', hInv, _⟩
  exact hInv

theorem decode_json_entries_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos count : Std.Usize) (sink : S) (hSink : Inv sink)
    (hStart : start_pos.val ≤ input.length) :
    decoder_v1.decode_json_entries V input start_pos count sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok nxt => start_pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_json_entries
  let inv : S × Std.Usize × Std.Usize × Option CodecError → Prop :=
    fun (sink1, cur1, i1, _) =>
      Inv sink1 ∧ i1.val ≤ count.val ∧ start_pos.val ≤ cur1.val ∧ cur1.val ≤ input.length
  have hLoop :
      decoder_v1.decode_json_entries_loop V input count sink start_pos 0#usize none
        ⦃ (sink1, cur1, _) =>
          Inv sink1 ∧ start_pos.val ≤ cur1.val ∧ cur1.val ≤ input.length ⦄ := by
    unfold decoder_v1.decode_json_entries_loop
    refine loop.spec_decr_nat
      (fun (_, _, i, err) => errFlag err + (count.val - i.val))
      inv _ _
      (sink, start_pos, 0#usize, none) ?_ ⟨hSink, by scalar_tac, le_rfl, hStart⟩
    intro ⟨sink1, cur1, i1, err1⟩ ⟨hInv1, hi, hLo, hHi⟩
    unfold decoder_v1.decode_json_entries_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with read_str_slice_at_spec V Inv input hV cur1 sink1 hInv1 as ⟨r, sink1', hInv1', hr⟩
      cases r with
      | Ok sp =>
        dsimp only [SpanOk] at hr
        step with hV.on_json_value sink1' sp hInv1' hr.2 as ⟨r1, sink2, hInv2⟩
        cases r1 with
        | Ok _ =>
          step as ⟨i2, hi2⟩
          try simp only [spec_ok]
          exact ⟨⟨hInv2, by scalar_tac, by omega, by omega⟩, by simp [hi2]; scalar_tac⟩
        | Err e =>
          try simp only [spec_ok]
          exact ⟨⟨hInv2, hi, hLo, hHi⟩, by simp⟩
      | Err e =>
        try simp only [spec_ok]
        exact ⟨⟨hInv1', hi, hLo, hHi⟩, by simp⟩
    · simp only [spec_ok]; exact ⟨hInv1, hLo, hHi⟩
    · simp only [spec_ok]; exact ⟨hInv1, hLo, hHi⟩
  step with hLoop as ⟨sink1, cur, err, hInv1, hLo, hHi⟩
  cases err <;> simp [spec_ok]
  · exact ⟨hInv1, hLo, hHi⟩
  · exact hInv1

theorem decode_any_entries_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos count : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc : Std.Usize)
    (sink : S) (hSink : Inv sink) (hStart : start_pos.val ≤ input.length) :
    decoder_v1.decode_any_entries V input start_pos count limits entries_acc sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok (nxt, _) => start_pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_any_entries
  let inv : S × Std.Usize × Std.Usize × Std.Usize × Option CodecError → Prop :=
    fun (sink1, cur1, _, i1, _) =>
      Inv sink1 ∧ i1.val ≤ count.val ∧ start_pos.val ≤ cur1.val ∧ cur1.val ≤ input.length
  have hLoop :
      decoder_v1.decode_any_entries_loop V input count limits sink start_pos entries_acc 0#usize none
        ⦃ (sink1, cur1, _, _) =>
          Inv sink1 ∧ start_pos.val ≤ cur1.val ∧ cur1.val ≤ input.length ⦄ := by
    unfold decoder_v1.decode_any_entries_loop
    refine loop.spec_decr_nat
      (fun (_, _, _, i, err) => errFlag err + (count.val - i.val))
      inv _ _
      (sink, start_pos, entries_acc, 0#usize, none) ?_ ⟨hSink, by scalar_tac, le_rfl, hStart⟩
    intro ⟨sink1, cur1, ent1, i1, err1⟩ ⟨hInv1, hi, hLo, hHi⟩
    unfold decoder_v1.decode_any_entries_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with decode_any_v1_spec V Inv input hV cur1 limits ent1 sink1 hInv1 hHi
        as ⟨r, sink2, hInv2, hRes⟩
      cases r with
      | Ok p =>
        rcases p with ⟨next_c, next_e⟩
        dsimp only at hRes
        step with hV.on_any_content_value sink2 hInv2 as ⟨r1, sink3, hInv3⟩
        cases r1 with
        | Ok _ =>
          step as ⟨i2, hi2⟩
          try simp only [spec_ok]
          exact ⟨⟨hInv3, by scalar_tac, by omega, hRes.2⟩, by simp [hi2]; scalar_tac⟩
        | Err e =>
          try simp only [spec_ok]
          exact ⟨⟨hInv3, hi, hLo, hHi⟩, by simp⟩
      | Err e =>
        try simp only [spec_ok]
        exact ⟨⟨hInv2, hi, hLo, hHi⟩, by simp⟩
    · simp only [spec_ok]; exact ⟨hInv1, hLo, hHi⟩
    · simp only [spec_ok]; exact ⟨hInv1, hLo, hHi⟩
  step with hLoop as ⟨sink1, cur, entries, err, hInv1, hLo, hHi⟩
  cases err <;> simp [spec_ok]
  · exact ⟨hInv1, hLo, hHi⟩
  · exact hInv1

theorem decode_item_header_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos : Std.Usize) (info : Std.U8) (sink : S) (hSink : Inv sink)
    (hStart : start_pos.val ≤ input.length) :
    decoder_v1.decode_item_header V input start_pos info sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok (hdr, nxt) =>
        start_pos.val ≤ nxt.val ∧ nxt.val ≤ input.length ∧
        WireParentOk input hdr.parent ∧ OptSpanOk input hdr.parent_sub
      | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_item_header
  repeat (any_goals (
    first
    | (simp only [spec_ok, Aeneas.Std.uncurry]; (try dsimp only at *); (try simp only [SpanOk] at *);
        (first
        | done
        | (exact ⟨by assumption, by omega, by omega, trivial, trivial⟩)
        | (exact ⟨by assumption, trivial⟩)
        | (refine ⟨by assumption, by omega, by omega, ?_, ?_⟩ <;>
            (simp only [WireParentOk, OptSpanOk, SpanOk] <;>
             first | trivial | exact ⟨by omega, by omega⟩))
        | (scalar_tac; done)
        | (omega; done)))
    | (apply ite_wp_split <;> intro _)
    | (split_ifs <;> try dsimp only at * <;> try simp only [Aeneas.Std.uncurry])
    | (cases_prod_hyp <;> try dsimp only at * <;> try simp only [Aeneas.Std.uncurry])
    | (cases_result_err <;>
        simp only [core_ops_try_branch_ok, core_ops_try_branch_err, bind_ok,
          core_ops_try_from_residual_err, Aeneas.Std.uncurry] <;>
        try dsimp only at *)
    | (step with (read_var_u64_sink_spec V Inv input hV))
    | (step with (read_wire_id_at_spec V Inv input hV))
    | (step with (read_early_str_slice_at_spec V Inv input hV))
    | step
  ))
  all_goals try simp only [spec_ok, Aeneas.Std.uncurry]
  all_goals try exact ⟨by assumption, trivial⟩

theorem decode_item_content_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (cur : Std.Usize) (tag : Std.U8)
    (limits : decoder_v1.DecodeLimitsCore) (entries_acc : Std.Usize)
    (sink : S) (hSink : Inv sink) (hCur : cur.val ≤ input.length) :
    decoder_v1.decode_item_content V input cur tag limits entries_acc sink ⦃ (r, sink') =>
      Inv sink' ∧
      match r with
      | .Ok (_, nxt, _) => cur.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_item_content
  try dsimp only; try simp only [Aeneas.Std.uncurry]
  repeat (any_goals (
    first
    | (simp only [spec_ok, Aeneas.Std.uncurry]; (try dsimp only at *); (try simp only [SpanOk] at *);
        (first
        | done
        | (exact ⟨by assumption, by omega, by omega⟩)
        | (exact ⟨by assumption, trivial⟩)
        | (scalar_tac; done)
        | (omega; done)))
    | (apply ite_wp_split <;> intro _)
    | (split_ifs <;> try dsimp only at * <;> try simp only [Aeneas.Std.uncurry])
    | (cases_prod_hyp <;> try dsimp only at * <;> try simp only [Aeneas.Std.uncurry])
    | (cases_result_err <;>
        simp only [core_ops_try_branch_ok, core_ops_try_branch_err, bind_ok,
          core_ops_try_from_residual_err, Aeneas.Std.uncurry] <;>
        try dsimp only at *)
    | (step with (Utf16.utf16_len_total))
    | (step with (read_bytes_slice_at_spec V Inv input hV))
    | (step with (read_str_slice_at_spec V Inv input hV))
    | (step with (read_var_u64_sink_spec V Inv input hV))
    | (step with (read_wire_id_at_spec V Inv input hV))
    | (step with (read_early_str_slice_at_spec V Inv input hV))
    | (step with (check_fits_kind_sink_spec V Inv input hV))
    | (step with (fail_with_spec V Inv input hV))
    | (step with (decode_json_entries_spec V Inv input hV))
    | (step with (decode_any_entries_spec V Inv input hV))
    | (step with (decode_any_v1_spec V Inv input hV))
    | (step with (hV.on_deleted))
    | (step with (hV.on_json_start))
    | (step with (hV.on_json_finish))
    | (step with (hV.on_binary))
    | (step with (hV.on_string))
    | (step with (hV.on_embed))
    | (step with (hV.on_format))
    | (step with (hV.on_type))
    | (step with (hV.on_any_content_start))
    | (step with (hV.on_any_content_finish))
    | (step with (hV.on_doc))
    | step
    | ((try dsimp only at *); (try simp only [ItemMetaOk, WireParentOk, OptSpanOk, SpanOk] at *);
        (try dsimp);
        (first
        | done
        | (assumption; done)
        | (trivial; done)
        | (simp [decoder_v1.MIN_ENTRY_BYTES]; done)
        | (exact ⟨by omega, by omega⟩; done)
        | (exact ⟨by assumption, by assumption, by omega, by omega⟩; done)
        | (tauto; done)
        | (omega; done)))
  ))
  all_goals try simp only [spec_ok, Aeneas.Std.uncurry]
  all_goals try (simp only [SpanOk] at *; exact ⟨by assumption, by omega, by omega⟩)
  all_goals try exact ⟨by assumption, trivial⟩

@[local step]
theorem seq_ranges_find_total
    (ranges : Slice order_range.ClockRange) (clock : Std.U64) :
    decoder_v1.seq_ranges_find ranges clock ⦃ _ => True ⦄ := by
  unfold decoder_v1.seq_ranges_find
  dsimp only
  split_ifs with h0
  · simp [spec_ok]
  · step as ⟨i, hi⟩
    have hiLt : i.val < ranges.length := by scalar_tac
    step as ⟨last, hlast⟩
    split_ifs with hge hltLast
    · simp [spec_ok]
    · simp [spec_ok]
    · unfold decoder_v1.seq_ranges_find_loop
      refine loop.spec_decr_nat
        (fun (low, high) => high.val - low.val)
        (fun (low, high) => low.val ≤ high.val ∧ high.val ≤ ranges.length)
        (fun _ => True)
        _ (0#usize, i) ?_ ⟨by scalar_tac, by scalar_tac⟩
      intro ⟨low, high⟩ ⟨hLoHi, hHiLen⟩
      unfold decoder_v1.seq_ranges_find_loop.body
      dsimp only
      split_ifs with hlt
      · step as ⟨d, hd⟩
        step as ⟨half, hhalf⟩
        step as ⟨mid, hmid⟩
        have hMidLt : mid.val < ranges.length := by scalar_tac
        step as ⟨r, hr⟩
        split_ifs with hclt hcge
        · simp only [spec_ok]
          exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
        · step as ⟨low1, hlow1⟩
          try simp only [spec_ok]
          exact ⟨by scalar_tac, hHiLen, by scalar_tac⟩
        · simp [spec_ok]
      · simp [spec_ok]

@[local step]
theorem seq_ranges_push_total
    (ranges : alloc.vec.Vec order_range.ClockRange) (start «end» : Std.U64) :
    decoder_v1.seq_ranges_push ranges start «end» ⦃ _ => True ⦄ := by
  unfold decoder_v1.seq_ranges_push
  dsimp only
  have hUsizeMax : core.num.Usize.MAX.val = Std.Usize.max := by
    simp [core.num.Usize.MAX]
  by_cases hpos : alloc.vec.Vec.len ranges > 0#usize
  · rw [if_pos hpos]
    step as ⟨i, hi⟩
    have hiLt : i.val < ranges.length := by
      simp only [alloc.vec.Vec.len] at hpos
      scalar_tac
    step as ⟨last, hlast⟩
    by_cases heq : last.end = start
    · rw [if_pos heq]
      step*
    · rw [if_neg heq]
      by_cases hmax : alloc.vec.Vec.len ranges < core.num.Usize.MAX
      · rw [if_pos hmax]
        have hCap : ranges.length < Std.Usize.max := by
          simp only [alloc.vec.Vec.len] at hmax
          scalar_tac
        step*
      · rw [if_neg hmax]
        simp [spec_ok]
  · rw [if_neg hpos]
    by_cases hmax : alloc.vec.Vec.len ranges < core.num.Usize.MAX
    · rw [if_pos hmax]
      have hCap : ranges.length < Std.Usize.max := by
        simp only [alloc.vec.Vec.len] at hmax
        scalar_tac
      step*
    · rw [if_neg hmax]
      simp [spec_ok]

@[local step]
theorem is_ytext_content_total
    (input : Slice Std.U8) (start «end» : Std.Usize) (tag : Std.U8) :
    decoder_v1.is_ytext_content input start «end» tag ⦃ _ => True ⦄ := by
  unfold decoder_v1.is_ytext_content
  dsimp only
  by_cases htag : tag = 7#u8
  · rw [if_pos htag]
    by_cases hlt : start < «end»
    · rw [if_pos hlt]
      by_cases hle : «end» ≤ Slice.len input
      · rw [if_pos hle]
        have hStartLt : start.val < input.length := by scalar_tac
        step*
      · rw [if_neg hle]
        simp [spec_ok]
    · rw [if_neg hlt]
      simp [spec_ok]
  · rw [if_neg htag]
    simp [spec_ok]

@[local step]
theorem same_wire_id_opt_total (a b : Option decoder_v1.WireId) :
    decoder_v1.same_wire_id_opt a b ⦃ _ => True ⦄ := by
  unfold decoder_v1.same_wire_id_opt
  cases a <;> cases b <;> repeat (first | simp [spec_ok] | split_ifs)

@[local step]
theorem lookup_ytext_parent_total
    (id : decoder_v1.WireId) (parent : decoder_v1.WireParentCore)
    (ytext_types : Slice order_range.ClockRange) :
    decoder_v1.lookup_ytext_parent id parent ytext_types ⦃ _ => True ⦄ := by
  unfold decoder_v1.lookup_ytext_parent
  cases parent with
  | Root _ => simp [spec_ok]
  | Inherit => simp [spec_ok]
  | Item p =>
    dsimp only
    by_cases hc : p.client = id.client
    · rw [if_pos hc]
      by_cases hlt : p.clock < id.clock
      · rw [if_pos hlt]
        step with seq_ranges_find_total ytext_types p.clock as ⟨o⟩
      · rw [if_neg hlt]
        simp [spec_ok]
    · rw [if_neg hc]
      simp [spec_ok]

@[local step]
theorem lookup_proven_origin_total
    (id : decoder_v1.WireId) (origin : Option decoder_v1.WireId)
    (seq_ranges : Slice order_range.ClockRange) :
    decoder_v1.lookup_proven_origin id origin seq_ranges ⦃ _ => True ⦄ := by
  unfold decoder_v1.lookup_proven_origin
  cases origin with
  | none => simp [spec_ok]
  | some o =>
    dsimp only
    split_ifs <;> try simp [spec_ok]
    exact seq_ranges_find_total seq_ranges o.clock

@[local step]
theorem origin_left_at_range_end_total
    (id : decoder_v1.WireId) (origin : Option decoder_v1.WireId)
    (range : Option order_range.ClockRange) :
    decoder_v1.origin_left_at_range_end id origin range ⦃ _ => True ⦄ := by
  unfold decoder_v1.origin_left_at_range_end
  cases origin with
  | none => simp [spec_ok]
  | some o =>
    cases range with
    | none => simp [spec_ok]
    | some r =>
      dsimp only
      split_ifs with hlt
      · step as ⟨i, _⟩
        split_ifs <;> simp [spec_ok]
      · simp [spec_ok]

@[local step]
theorem should_skip_zero_len_item_total
    (tag : Std.U8) (len : Std.U64)
    (has_parent_sub_bit or_none ol_boundary : Bool) :
    decoder_v1.should_skip_zero_len_item tag len has_parent_sub_bit or_none ol_boundary
      ⦃ _ => True ⦄ := by
  unfold decoder_v1.should_skip_zero_len_item
  repeat (first | simp [spec_ok] | split_ifs)

@[local step]
theorem is_item_proven_seq_total
    (has_parent_sub_bit ol_none or_none ol_proven or_proven wire_parent_sub_none parent_is_ytext : Bool) :
    decoder_v1.is_item_proven_seq has_parent_sub_bit ol_none or_none ol_proven or_proven wire_parent_sub_none parent_is_ytext
      ⦃ _ => True ⦄ := by
  unfold decoder_v1.is_item_proven_seq
  repeat (first | simp [spec_ok] | split_ifs)

@[local step]
theorem classify_item_seq_provenance_total
    (id : decoder_v1.WireId) (info tag : Std.U8) (len : Std.U64)
    (hdr : decoder_v1.ItemHeader)
    (ytext_types seq_ranges : Slice order_range.ClockRange) :
    decoder_v1.classify_item_seq_provenance id info tag len hdr ytext_types seq_ranges ⦃ _ => True ⦄ := by
  unfold decoder_v1.classify_item_seq_provenance
  step*

@[local step]
theorem push_wire_id_total
    (dst : alloc.vec.Vec decoder_v1.WireId) (id : decoder_v1.WireId) :
    decoder_v1.push_wire_id dst id ⦃ _ => True ⦄ := by
  unfold decoder_v1.push_wire_id
  dsimp only
  have hUsizeMax : core.num.Usize.MAX.val = Std.Usize.max := by
    simp [core.num.Usize.MAX]
  by_cases hmax : alloc.vec.Vec.len dst < core.num.Usize.MAX
  · rw [if_pos hmax]
    have hCap : dst.length < Std.Usize.max := by
      simp only [alloc.vec.Vec.len] at hmax
      scalar_tac
    step*
  · rw [if_neg hmax]
    simp [spec_ok]

@[local step]
theorem extend_wire_ids_total
    (dst : alloc.vec.Vec decoder_v1.WireId) (src : Slice decoder_v1.WireId) :
    decoder_v1.extend_wire_ids dst src ⦃ _ => True ⦄ := by
  unfold decoder_v1.extend_wire_ids decoder_v1.extend_wire_ids_loop
  let inv : alloc.vec.Vec decoder_v1.WireId × Std.Usize → Prop :=
    fun (_, i) => i.val ≤ src.length
  refine loop.spec_decr_nat
    (fun (_, i) => src.length - i.val)
    inv (fun _ => True) _ (dst, 0#usize) ?_ (by scalar_tac)
  intro ⟨dst1, i⟩ hiLe
  unfold decoder_v1.extend_wire_ids_loop.body
  dsimp only
  by_cases hlt : i < Slice.len src
  · rw [if_pos hlt]
    have hiLt : i.val < src.length := by scalar_tac
    step as ⟨wi, _⟩
    step with push_wire_id_total dst1 wi as ⟨dst2⟩
    step as ⟨i2, hi2⟩
    try simp only [spec_ok]
    exact ⟨by scalar_tac, by scalar_tac⟩
  · rw [if_neg hlt]
    simp [spec_ok]

private theorem slice_set_length {α : Type _} (s : Slice α) (i : Std.Usize) (x : α) :
    (s.set i x).length = s.length := by
  simp [Slice.length, Slice.set_val_eq]

@[local step]
theorem sift_down_wire_ids_total
    (items : Slice decoder_v1.WireId) (start «end» : Std.Usize)
    (hEnd : «end».val ≤ items.length) :
    decoder_v1.sift_down_wire_ids items start «end» ⦃ items' => items'.length = items.length ⦄ := by
  unfold decoder_v1.sift_down_wire_ids
  step as ⟨half, hhalf⟩
  unfold decoder_v1.sift_down_wire_ids_loop
  let inv : (Slice decoder_v1.WireId) × Std.Usize → Prop :=
    fun (items1, _) => items1.length = items.length
  refine loop.spec_decr_nat
    (fun (_, root) => half.val - root.val)
    inv (fun (items1 : Slice decoder_v1.WireId) => items1.length = items.length) _ (items, start) ?_ rfl
  intro ⟨items1, root⟩ hLen1
  unfold decoder_v1.sift_down_wire_ids_loop.body
  dsimp only
  by_cases hlt : root < half
  · rw [if_pos hlt]
    have hMul : root.val * 2 ≤ Std.Usize.max := by scalar_tac
    step as ⟨i, hi⟩
    have hLeftMax : i.val + 1 ≤ Std.Usize.max := by scalar_tac
    step as ⟨left, hleft⟩
    have hRootLt : root.val < items1.length := by scalar_tac
    have hLeftLt : left.val < items1.length := by scalar_tac
    step as ⟨wi, _⟩
    step as ⟨wi1, _⟩
    step with wire_id_lt_total wi wi1 as ⟨b⟩
    have hSwap0 :
        (if b = true then ok left else ok root)
        ⦃ s0 => s0.val < items1.length ∧ (s0 = root ∨ root.val < s0.val) ⦄ := by
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte, spec_ok]
        exact ⟨hLeftLt, Or.inr (by scalar_tac)⟩
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact ⟨hRootLt, Or.inl trivial⟩
    step with hSwap0 as ⟨swap_idx, hSwapLt, hSwapRel⟩
    have hI1Max : left.val + 1 ≤ Std.Usize.max := by scalar_tac
    step as ⟨i1, hi1⟩
    have hSwap1 :
        (if i1 < «end» then do
          let wi2 ← Slice.index_usize items1 swap_idx
          let wi3 ← Slice.index_usize items1 i1
          let b1 ← decoder_v1.wire_id_lt wi2 wi3
          if b1 = true then ok i1 else ok swap_idx
         else ok swap_idx)
        ⦃ s1 => s1.val < items1.length ∧ (s1 = root ∨ root.val < s1.val) ⦄ := by
      by_cases hRight : i1 < «end»
      · rw [if_pos hRight]
        have hI1Lt : i1.val < items1.length := by scalar_tac
        step as ⟨wi2, _⟩
        step as ⟨wi3, _⟩
        step with wire_id_lt_total wi2 wi3 as ⟨b1⟩
        by_cases hb1 : b1 = true
        · simp only [hb1, ↓reduceIte, spec_ok]
          exact ⟨hI1Lt, Or.inr (by scalar_tac)⟩
        · simp only [hb1, Bool.false_eq_true, ↓reduceIte, spec_ok]
          exact ⟨hSwapLt, hSwapRel⟩
      · rw [if_neg hRight]
        simp only [spec_ok]
        exact ⟨hSwapLt, hSwapRel⟩
    step with hSwap1 as ⟨swap_idx1, hSwap1Lt, hSwap1Rel⟩
    by_cases heq : swap_idx1 = root
    · rw [if_pos heq]
      simp only [spec_ok]
      exact ⟨hLen1, by scalar_tac⟩
    · rw [if_neg heq]
      have hGtRoot : root.val < swap_idx1.val := by
        rcases hSwap1Rel with h | h
        · exact False.elim (heq h)
        · exact h
      step as ⟨wi2, _⟩
      step as ⟨items2, hLen2⟩
      have hSwap1Lt2 : swap_idx1.val < items2.length := by
        rw [hLen2, slice_set_length]; exact hSwap1Lt
      step as ⟨s, hLenS⟩
      try simp only [spec_ok]
      dsimp only [inv]
      exact ⟨by rw [hLenS, slice_set_length, hLen2, slice_set_length, hLen1], by scalar_tac⟩
  · rw [if_neg hlt]
    dsimp only [inv] at hLen1
    simp [spec_ok, hLen1]

@[local step]
theorem sort_wire_ids_total (items : Slice decoder_v1.WireId) :
    decoder_v1.sort_wire_ids items ⦃ _ => True ⦄ := by
  unfold decoder_v1.sort_wire_ids
  dsimp only
  by_cases hle : Slice.len items ≤ 1#usize
  · rw [if_pos hle]
    simp [spec_ok]
  · rw [if_neg hle]
    step as ⟨start, hstart⟩
    have hLoop0 :
        decoder_v1.sort_wire_ids_loop0 items (Slice.len items) start
          ⦃ items1 => items1.length = items.length ⦄ := by
      unfold decoder_v1.sort_wire_ids_loop0
      let inv0 : (Slice decoder_v1.WireId) × Std.Usize → Prop :=
        fun (items1, _) => items1.length = items.length
      refine loop.spec_decr_nat
        (fun (_, s) => s.val)
        inv0
        (fun (items1 : Slice decoder_v1.WireId) => items1.length = items.length)
        _ (items, start) ?_ rfl
      intro ⟨items1, s⟩ hLen1
      unfold decoder_v1.sort_wire_ids_loop0.body
      dsimp only
      by_cases hpos : s > 0#usize
      · rw [if_pos hpos]
        step as ⟨s1, hs1⟩
        step with sift_down_wire_ids_total items1 s1 (Slice.len items) (by rw [hLen1]; scalar_tac)
          as ⟨items2, hLen2⟩
        try simp only [spec_ok]
        dsimp only [inv0]
        exact ⟨by rw [hLen2, hLen1], by scalar_tac⟩
      · rw [if_neg hpos]
        dsimp only [inv0] at hLen1
        simp [spec_ok, hLen1]
    step with hLoop0 as ⟨items1, hLen1⟩
    unfold decoder_v1.sort_wire_ids_loop1
    let inv1 : (Slice decoder_v1.WireId) × Std.Usize → Prop :=
      fun (items2, e) => items2.length = items.length ∧ e.val ≤ items.length
    refine loop.spec_decr_nat
      (fun (_, e) => e.val)
      inv1 (fun _ => True) _ (items1, Slice.len items) ?_ ⟨hLen1, by scalar_tac⟩
    intro ⟨items2, e⟩ ⟨hLen2, hELe⟩
    unfold decoder_v1.sort_wire_ids_loop1.body
    dsimp only
    by_cases hgt : e > 1#usize
    · rw [if_pos hgt]
      step as ⟨e1, he1⟩
      have h0Lt : (0#usize).val < items2.length := by scalar_tac
      have hE1Lt : e1.val < items2.length := by scalar_tac
      step as ⟨tmp, _⟩
      step as ⟨wi, _⟩
      step as ⟨items3, hLen3⟩
      have hE1Lt3 : e1.val < items3.length := by
        rw [hLen3, slice_set_length]; exact hE1Lt
      step as ⟨items4, hLen4⟩
      have hLen4Eq : items4.length = items.length := by
        rw [hLen4, slice_set_length, hLen3, slice_set_length, hLen2]
      step with sift_down_wire_ids_total items4 0#usize e1 (by rw [hLen4Eq]; scalar_tac)
        as ⟨items5, hLen5⟩
      try simp only [spec_ok]
      dsimp only [inv1]
      exact ⟨⟨by rw [hLen5, hLen4Eq], by scalar_tac⟩, by scalar_tac⟩
    · rw [if_neg hgt]
      simp [spec_ok]

@[local step]
theorem alloc_zero_max_hi_total (len : Std.Usize) :
    decoder_v1.alloc_zero_max_hi len ⦃ _ => True ⦄ := by
  unfold decoder_v1.alloc_zero_max_hi decoder_v1.alloc_zero_max_hi_loop
  let inv : (alloc.vec.Vec Std.Usize) × Std.Usize → Prop :=
    fun (_, i) => i.val ≤ len.val
  refine loop.spec_decr_nat
    (fun (_, i) => len.val - i.val)
    inv (fun _ => True) _ (alloc.vec.Vec.new Std.Usize, 0#usize) ?_ (by scalar_tac)
  intro ⟨out1, i⟩ hiLe
  unfold decoder_v1.alloc_zero_max_hi_loop.body
  dsimp only
  have hUsizeMax : core.num.Usize.MAX.val = Std.Usize.max := by
    simp [core.num.Usize.MAX]
  by_cases hlt : i < len
  · rw [if_pos hlt]
    by_cases hmax : alloc.vec.Vec.len out1 < core.num.Usize.MAX
    · rw [if_pos hmax]
      have hCap : out1.length < Std.Usize.max := by
        simp only [alloc.vec.Vec.len] at hmax
        scalar_tac
      step as ⟨out2, _⟩
      step as ⟨i2, hi2⟩
      try simp only [spec_ok]
      exact ⟨by scalar_tac, by scalar_tac⟩
    · rw [if_neg hmax]
      simp [spec_ok]
  · rw [if_neg hlt]
    simp [spec_ok]

@[local step]
theorem all_zero_strings_covered_total (max_hi : Slice Std.Usize) :
    decoder_v1.all_zero_strings_covered max_hi ⦃ _ => True ⦄ := by
  unfold decoder_v1.all_zero_strings_covered decoder_v1.all_zero_strings_covered_loop
  let inv : Std.Usize × Std.Usize → Prop :=
    fun (_, i) => i.val ≤ max_hi.length
  refine loop.spec_decr_nat
    (fun (_, i) => max_hi.length - i.val)
    inv (fun _ => True) _ (0#usize, 0#usize) ?_ (by scalar_tac)
  intro ⟨reach, i⟩ hiLe
  unfold decoder_v1.all_zero_strings_covered_loop.body
  dsimp only
  by_cases hlt : i < Slice.len max_hi
  · rw [if_pos hlt]
    have hiLt : i.val < max_hi.length := by scalar_tac
    step as ⟨i2, _⟩
    have hReach : (if i2 > reach then ok i2 else ok reach) ⦃ _ => True ⦄ := by
      split_ifs <;> simp [spec_ok]
    step with hReach as ⟨reach1⟩
    by_cases hle : reach1 ≤ i
    · rw [if_pos hle]
      simp [spec_ok]
    · rw [if_neg hle]
      step as ⟨i3, hi3⟩
      try simp only [spec_ok]
      exact ⟨by scalar_tac, by scalar_tac⟩
  · rw [if_neg hlt]
    simp [spec_ok]

@[local step]
theorem contains_wire_id_sorted_total
    (items : Slice decoder_v1.WireId) (target : decoder_v1.WireId) :
    decoder_v1.contains_wire_id_sorted items target ⦃ _ => True ⦄ := by
  unfold decoder_v1.contains_wire_id_sorted
  step with find_wire_id_lower_bound_total items target as ⟨idx⟩
  by_cases hlt : idx < Slice.len items
  · rw [if_pos hlt]
    have hLt : idx.val < items.length := by scalar_tac
    step as ⟨found, _⟩
    split_ifs <;> simp [spec_ok]
  · rw [if_neg hlt]
    simp [spec_ok]

@[local step]
theorem opt_wire_id_in_sorted_total
    (items : Slice decoder_v1.WireId) (opt : Option decoder_v1.WireId) :
    decoder_v1.opt_wire_id_in_sorted items opt ⦃ _ => True ⦄ := by
  unfold decoder_v1.opt_wire_id_in_sorted
  cases opt with
  | none => simp [spec_ok]
  | some w => exact contains_wire_id_sorted_total items w

@[local step]
theorem parent_item_in_sorted_total
    (items : Slice decoder_v1.WireId) (parent : decoder_v1.WireParentCore) :
    decoder_v1.parent_item_in_sorted items parent ⦃ _ => True ⦄ := by
  unfold decoder_v1.parent_item_in_sorted
  cases parent with
  | Root _ => simp [spec_ok]
  | Inherit => simp [spec_ok]
  | Item w => exact contains_wire_id_sorted_total items w

@[local step]
theorem mark_point_ids_covered_total
    (pending : Slice decoder_v1.WireId) (max_hi : Slice Std.Usize)
    (client start «end» : Std.U64) :
    decoder_v1.mark_point_ids_covered pending max_hi client start «end» ⦃ _ => True ⦄ := by
  unfold decoder_v1.mark_point_ids_covered
  dsimp only
  by_cases hle : «end» ≤ start
  · rw [if_pos hle]
    simp [spec_ok]
  · rw [if_neg hle]
    step with find_wire_id_lower_bound_total pending { client, clock := start } as ⟨lo⟩
    step with find_wire_id_lower_bound_total pending { client, clock := «end» } as ⟨hiBound⟩
    by_cases hlohi : lo < hiBound
    · rw [if_pos hlohi]
      by_cases hloLen : lo < Slice.len max_hi
      · rw [if_pos hloLen]
        have hLoLt : lo.val < max_hi.length := by scalar_tac
        step as ⟨i1, _⟩
        by_cases hgt : hiBound > i1
        · rw [if_pos hgt]
          step*
        · rw [if_neg hgt]
          simp [spec_ok]
      · rw [if_neg hloLen]
        simp [spec_ok]
    · rw [if_neg hlohi]
      simp [spec_ok]

theorem noop_sink_v1sink_total :
    V1SinkTotal decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink (fun _ => True) :=
  { core_validates_utf8 := by
      intro s; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.core_validates_utf8, spec_ok]
    validate_utf8_early := by
      intro s _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.validate_utf8_early, spec_ok]
    on_decode_error := by
      intro s _ _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_decode_error, spec_ok]
    record_client := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.record_client, spec_ok]
    begin_client := by
      intro s _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.begin_client, spec_ok]
    on_gc := by
      intro s _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_gc, spec_ok]
    on_skip := by
      intro s _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_skip, spec_ok]
    on_item := by
      intro s _ _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_item, spec_ok]
    on_skipped_zero_origin := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_skipped_zero_origin, spec_ok]
    on_deleted := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_deleted, spec_ok]
    on_json_start := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_json_start, spec_ok]
    on_json_value := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_json_value, spec_ok]
    on_json_finish := by
      intro s _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_json_finish, spec_ok]
    on_binary := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_binary, spec_ok]
    on_string := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_string, spec_ok]
    on_embed := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_embed, spec_ok]
    on_format := by
      intro s _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_format, spec_ok]
    on_type := by
      intro s _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_type, spec_ok]
    on_any_content_start := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_content_start, spec_ok]
    on_any_content_value := by
      intro s _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_content_value, spec_ok]
    on_any_content_finish := by
      intro s _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_content_finish, spec_ok]
    on_doc := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_doc, spec_ok]
    on_any_start := by
      intro s _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_start, spec_ok]
    on_any_undefined := by
      intro s _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_undefined, spec_ok]
    on_any_null := by
      intro s _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_null, spec_ok]
    on_any_i32 := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_i32, spec_ok]
    on_any_f32_bits := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_f32_bits, spec_ok]
    on_any_f64_bits := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_f64_bits, spec_ok]
    on_any_i64_bits := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_i64_bits, spec_ok]
    on_any_bool := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_bool, spec_ok]
    on_any_str := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_str, spec_ok]
    on_any_bytes := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_bytes, spec_ok]
    on_any_begin_object := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_begin_object, spec_ok]
    on_any_object_key := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_object_key, spec_ok]
    on_any_begin_array := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_begin_array, spec_ok]
    on_any_end_container := by
      intro s _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_end_container, spec_ok]
    on_any_finish := by
      intro s _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_finish, spec_ok]
    begin_delete_client := by
      intro s _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.begin_delete_client, spec_ok]
    on_delete_range := by
      intro s _ _ _ _; simp [decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.NoopSink.Insts.Y_octo_coreDecoder_v1V1Sink.on_delete_range, spec_ok] }

@[local step]
theorem replay_client_seq_state_total
    (input : Slice Std.U8) (start_pos : Std.Usize) (start_id : decoder_v1.WireId)
    (target_idx : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (state : decoder_v1.ClientSeqState) :
    decoder_v1.replay_client_seq_state input start_pos start_id target_idx limits state
      ⦃ _ => True ⦄ := by
  unfold decoder_v1.replay_client_seq_state
  have hNoop := noop_sink_v1sink_total.toSpanSafe input
  have hLoop :
      decoder_v1.replay_client_seq_state_loop input start_id.client target_idx limits state ()
        start_pos start_id.clock 0#usize none ⦃ _ => True ⦄ := by
    unfold decoder_v1.replay_client_seq_state_loop
    let inv : decoder_v1.ClientSeqState × decoder_v1.NoopSink × Std.Usize × Std.U64 ×
        Std.Usize × Option CodecError → Prop :=
      fun (_, _, _, _, idx, _) => idx.val ≤ target_idx.val
    refine loop.spec_decr_nat
      (fun (_, _, _, _, idx, err) => errFlag err + (target_idx.val - idx.val))
      inv (fun _ => True) _ (state, (), start_pos, start_id.clock, 0#usize, none) ?_ (by scalar_tac)
    intro ⟨st1, noop1, cur1, clk1, idx1, err1⟩ hIdxLe
    unfold decoder_v1.replay_client_seq_state_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with read_u8_at_total input cur1 as ⟨r, _⟩
      cases r with
      | Ok p =>
        rcases p with ⟨info, after_info⟩
        step as ⟨tag, _⟩
        split_ifs with h0 h10
        · step with read_var_u64_sink_spec _ (fun _ => True) input hNoop after_info noop1 trivial as ⟨r1, _⟩
          cases r1 with
          | Ok p1 =>
            rcases p1 with ⟨len, next_cur⟩
            step with advance_clock_sink_spec _ (fun _ => True) input hNoop clk1 len () trivial as ⟨r2, _⟩
            cases r2 with
            | Ok next_clk =>
              step as ⟨idx2, hidx2⟩
              try simp only [spec_ok]
              exact ⟨by scalar_tac, by simp [hidx2]; scalar_tac⟩
            | Err e => try simp only [spec_ok]; exact ⟨hIdxLe, by simp⟩
          | Err e => try simp only [spec_ok]; exact ⟨hIdxLe, by simp⟩
        · step with read_var_u64_sink_spec _ (fun _ => True) input hNoop after_info noop1 trivial as ⟨r1, _⟩
          cases r1 with
          | Ok p1 =>
            rcases p1 with ⟨len, next_cur⟩
            step with advance_clock_sink_spec _ (fun _ => True) input hNoop clk1 len () trivial as ⟨r2, _⟩
            cases r2 with
            | Ok next_clk =>
              step as ⟨idx2, hidx2⟩
              try simp only [spec_ok]
              exact ⟨by scalar_tac, by simp [hidx2]; scalar_tac⟩
            | Err e => try simp only [spec_ok]; exact ⟨hIdxLe, by simp⟩
          | Err e => try simp only [spec_ok]; exact ⟨hIdxLe, by simp⟩
        · step with decode_item_header_spec _ (fun _ => True) input hNoop after_info info noop1 trivial as ⟨r1, _⟩
          cases r1 with
          | Ok p1 =>
            rcases p1 with ⟨hdr, content_start⟩
            step with decode_item_content_spec _ (fun _ => True) input hNoop content_start tag limits 0#usize () trivial
              as ⟨r2, _⟩
            cases r2 with
            | Ok t =>
              rcases t with ⟨len, content_end, _⟩
              step with advance_clock_sink_spec _ (fun _ => True) input hNoop clk1 len () trivial as ⟨r3, _⟩
              cases r3 with
              | Ok next_clk =>
                step with classify_item_seq_provenance_total { client := start_id.client, clock := clk1 } info tag len hdr
                  (alloc.vec.Vec.deref st1.ytext_types) (alloc.vec.Vec.deref st1.seq_ranges) as ⟨_, is_proven_seq⟩
                step with is_ytext_content_total input content_start content_end tag as ⟨b1⟩
                have hV0 :
                    (if b1 = true then decoder_v1.seq_ranges_push st1.ytext_types clk1 next_clk else ok st1.ytext_types)
                    ⦃ _ => True ⦄ := by
                  by_cases hb1 : b1 = true
                  · simp only [hb1, ↓reduceIte]; exact seq_ranges_push_total st1.ytext_types clk1 next_clk
                  · simp only [hb1, Bool.false_eq_true, ↓reduceIte, spec_ok]
                step with hV0 as ⟨v0⟩
                have hV1 :
                    (if is_proven_seq = true then decoder_v1.seq_ranges_push st1.seq_ranges clk1 next_clk else ok st1.seq_ranges)
                    ⦃ _ => True ⦄ := by
                  by_cases hp : is_proven_seq = true
                  · simp only [hp, ↓reduceIte]; exact seq_ranges_push_total st1.seq_ranges clk1 next_clk
                  · simp only [hp, Bool.false_eq_true, ↓reduceIte, spec_ok]
                step with hV1 as ⟨v1⟩
                step as ⟨idx2, hidx2⟩
                try simp only [spec_ok]
                exact ⟨by scalar_tac, by simp [hidx2]; scalar_tac⟩
              | Err e => try simp only [spec_ok]; exact ⟨hIdxLe, by simp⟩
            | Err e => try simp only [spec_ok]; exact ⟨hIdxLe, by simp⟩
          | Err e => try simp only [spec_ok]; exact ⟨hIdxLe, by simp⟩
      | Err e => try simp only [spec_ok]; exact ⟨hIdxLe, by simp⟩
    · simp [spec_ok]
    · simp [spec_ok]
  step with hLoop as ⟨st1, err⟩
  cases err <;> simp [spec_ok]

theorem emit_tracked_item_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos : Std.Usize) (id : decoder_v1.WireId) (tag : Std.U8)
    (hdr : decoder_v1.ItemHeader) (content_start : Std.Usize) (len : Std.U64)
    (content_end entries content_bytes : Std.Usize)
    (acc : decoder_v1.DecodeAcc) (is_proven_seq : Bool)
    (state : decoder_v1.ClientSeqState) (sink : S) (hSink : Inv sink)
    (hPos : pos.val ≤ content_end.val ∧ content_end.val ≤ input.length)
    (hHdr : WireParentOk input hdr.parent ∧ OptSpanOk input hdr.parent_sub) :
    decoder_v1.emit_tracked_item V input pos id tag hdr content_start len content_end
      entries content_bytes acc is_proven_seq state sink
      ⦃ (r, _, sink') =>
        Inv sink' ∧
        match r with
        | .Ok (nc, nxt, _, _, _) => id.clock.val ≤ nc.val ∧ pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
        | .Err _ => True ⦄ := by
  unfold decoder_v1.emit_tracked_item
  step with same_wire_id_opt_total state.just_skipped_ol hdr.origin_left as ⟨b⟩
  by_cases hb : b = true
  · simp only [hb, ↓reduceIte]
    step with fail_with_spec V Inv input hV sink CodecError.ZeroLengthStruct 0#usize 0#u64 hSink
      as ⟨ce, sink1, hInv1⟩
    simp [spec_ok, hInv1]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    step with advance_clock_sink_spec V Inv input hV id.clock len sink hSink as ⟨r, sink1, hInv1, hr⟩
    cases r with
    | Ok val =>
      simp only [core_ops_try_branch_ok, bind_ok]
      dsimp only at hr
      have hMeta : ItemMetaOk input
          { origin_left := hdr.origin_left,
            origin_right := hdr.origin_right,
            parent := hdr.parent,
            parent_sub := hdr.parent_sub,
            raw_range := { start := pos, «end» := content_end } } :=
        ⟨hHdr.1, hHdr.2, hPos.1, hPos.2⟩
      step with hV.on_item sink1 id len _ hInv1 hMeta as ⟨r1, sink2, hInv2⟩
      cases r1 with
      | Ok _ =>
        simp only [core_ops_try_branch_ok, bind_ok]
        step with is_ytext_content_total input content_start content_end tag as ⟨b1⟩
        have hV0 :
            (if b1 = true then decoder_v1.seq_ranges_push state.ytext_types id.clock val
             else ok state.ytext_types) ⦃ _ => True ⦄ := by
          by_cases hb1 : b1 = true
          · simp only [hb1, ↓reduceIte]; exact seq_ranges_push_total state.ytext_types id.clock val
          · simp only [hb1, Bool.false_eq_true, ↓reduceIte, spec_ok]
        step with hV0 as ⟨v⟩
        by_cases hp : is_proven_seq = true
        · simp only [hp, ↓reduceIte]
          step with seq_ranges_push_total state.seq_ranges id.clock val as ⟨v1⟩
          exact ⟨hInv2, by omega, hPos.1, hPos.2⟩
        · simp only [hp, Bool.false_eq_true, ↓reduceIte, spec_ok]
          exact ⟨hInv2, by omega, hPos.1, hPos.2⟩
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
        exact ⟨hInv2, trivial⟩
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      exact ⟨hInv1, trivial⟩

theorem decode_struct_frame_tracked_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos : Std.Usize) (id : decoder_v1.WireId) (info tag : Std.U8)
    (hdr : decoder_v1.ItemHeader) (content_start : Std.Usize) (len : Std.U64)
    (content_end entries content_bytes : Std.Usize)
    (acc : decoder_v1.DecodeAcc)
    (state : decoder_v1.ClientSeqState) (sink : S) (hSink : Inv sink)
    (hPos : pos.val ≤ content_end.val ∧ content_end.val ≤ input.length)
    (hHdr : WireParentOk input hdr.parent ∧ OptSpanOk input hdr.parent_sub) :
    decoder_v1.decode_struct_frame_tracked V input pos id info tag hdr content_start len
      content_end entries content_bytes acc state sink
      ⦃ (r, _, sink') =>
        Inv sink' ∧
        match r with
        | .Ok (nc, nxt, _, _, _) => id.clock.val ≤ nc.val ∧ pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
        | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_struct_frame_tracked
  step with classify_item_seq_provenance_total id info tag len hdr
    (alloc.vec.Vec.deref state.ytext_types) (alloc.vec.Vec.deref state.seq_ranges)
    as ⟨skip_zero, is_proven_seq⟩
  apply ite_wp_split <;> intro _
  · apply ite_wp_split <;> intro _
    · simp only [spec_ok]
      exact ⟨hSink, Nat.le_refl _, hPos.1, hPos.2⟩
    · exact emit_tracked_item_spec V Inv input hV pos id tag hdr content_start len content_end
        entries content_bytes acc is_proven_seq state sink hSink hPos hHdr
  · exact emit_tracked_item_spec V Inv input hV pos id tag hdr content_start len content_end
      entries content_bytes acc is_proven_seq state sink hSink hPos hHdr

theorem decode_struct_frame_slow_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos client_start_pos : Std.Usize) (client_start_clock : Std.U64)
    (s_idx : Std.Usize) (id : decoder_v1.WireId) (info tag : Std.U8)
    (hdr : decoder_v1.ItemHeader) (content_start : Std.Usize) (len : Std.U64)
    (content_end entries content_bytes : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (acc : decoder_v1.DecodeAcc)
    (state : decoder_v1.ClientSeqState) (sink : S) (hSink : Inv sink)
    (hPos : pos.val ≤ content_end.val ∧ content_end.val ≤ input.length)
    (hHdr : WireParentOk input hdr.parent ∧ OptSpanOk input hdr.parent_sub) :
    decoder_v1.decode_struct_frame_slow V input pos client_start_pos client_start_clock s_idx id
      info tag hdr content_start len content_end entries content_bytes limits acc state sink
      ⦃ (r, _, sink') =>
        Inv sink' ∧
        match r with
        | .Ok (nc, nxt, _, _, _) => id.clock.val ≤ nc.val ∧ pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
        | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_struct_frame_slow
  by_cases hact : state.active = true
  · simp only [hact, ↓reduceIte]
    exact decode_struct_frame_tracked_spec V Inv input hV pos id info tag hdr content_start len
      content_end entries content_bytes acc state sink hSink hPos hHdr
  · simp only [hact, Bool.false_eq_true, ↓reduceIte]
    step with replay_client_seq_state_total input client_start_pos
      { id with clock := client_start_clock } s_idx limits state as ⟨r, state1⟩
    cases r with
    | Ok _ =>
      simp only [core_ops_try_branch_ok, bind_ok]
      exact decode_struct_frame_tracked_spec V Inv input hV pos id info tag hdr content_start len
        content_end entries content_bytes acc state1 sink hSink hPos hHdr
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
      exact ⟨hSink, trivial⟩

@[local step]
theorem collect_colliding_in_client_total
    (input : Slice Std.U8) (start_pos : Std.Usize) (start_id : decoder_v1.WireId)
    (count : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (skipped_ols : Slice decoder_v1.WireId)
    (colliding_ids pending_colliding : alloc.vec.Vec decoder_v1.WireId) :
    decoder_v1.collect_colliding_in_client input start_pos start_id count limits
      skipped_ols colliding_ids pending_colliding ⦃ _ => True ⦄ := by
  unfold decoder_v1.collect_colliding_in_client
  have hNoop := noop_sink_v1sink_total.toSpanSafe input
  have hLoop :
      decoder_v1.collect_colliding_in_client_loop input start_id.client count limits skipped_ols
        colliding_ids pending_colliding () start_pos start_id.clock 0#usize none ⦃ _ => True ⦄ := by
    unfold decoder_v1.collect_colliding_in_client_loop
    let inv : (alloc.vec.Vec decoder_v1.WireId) × (alloc.vec.Vec decoder_v1.WireId) ×
        decoder_v1.NoopSink × Std.Usize × Std.U64 × Std.Usize × Option CodecError → Prop :=
      fun (_, _, _, _, _, sIdx, _) => sIdx.val ≤ count.val
    refine loop.spec_decr_nat
      (fun (_, _, _, _, _, sIdx, err) => errFlag err + (count.val - sIdx.val))
      inv (fun _ => True) _ (colliding_ids, pending_colliding, (), start_pos, start_id.clock, 0#usize, none)
      ?_ (by scalar_tac)
    intro ⟨cids1, pcoll1, noop1, cur1, clk1, sIdx, err1⟩ hsLe
    unfold decoder_v1.collect_colliding_in_client_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with read_u8_at_total input cur1 as ⟨r, _⟩
      cases r with
      | Ok p =>
        rcases p with ⟨info, after_info⟩
        step as ⟨tag, _⟩
        apply ite_wp_split <;> intro _
        · step with read_var_u64_sink_spec _ (fun _ => True) input hNoop after_info noop1 trivial as ⟨r1, _⟩
          cases r1 with
          | Ok p1 =>
            rcases p1 with ⟨len, next_cur⟩
            step with advance_clock_sink_spec _ (fun _ => True) input hNoop clk1 len () trivial as ⟨r2, _⟩
            cases r2 with
            | Ok next_clk =>
              step as ⟨sIdx1, hsIdx1⟩
              try simp only [spec_ok]
              exact ⟨by scalar_tac, by simp [hsIdx1]; scalar_tac⟩
            | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp⟩
          | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp⟩
        · apply ite_wp_split <;> intro _
          · step with read_var_u64_sink_spec _ (fun _ => True) input hNoop after_info noop1 trivial as ⟨r1, _⟩
            cases r1 with
            | Ok p1 =>
              rcases p1 with ⟨len, next_cur⟩
              step with advance_clock_sink_spec _ (fun _ => True) input hNoop clk1 len () trivial as ⟨r2, _⟩
              cases r2 with
              | Ok next_clk =>
                step as ⟨sIdx1, hsIdx1⟩
                try simp only [spec_ok]
                exact ⟨by scalar_tac, by simp [hsIdx1]; scalar_tac⟩
              | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp⟩
            | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp⟩
          · step with decode_item_header_spec _ (fun _ => True) input hNoop after_info info noop1 trivial as ⟨r1, _⟩
            cases r1 with
            | Ok p1 =>
              rcases p1 with ⟨hdr, content_start⟩
              step with decode_item_content_spec _ (fun _ => True) input hNoop content_start tag limits 0#usize () trivial
                as ⟨r2, _⟩
              cases r2 with
              | Ok t =>
                rcases t with ⟨len, content_end, _⟩
                apply ite_wp_split <;> intro _
                · step as ⟨sIdx1, hsIdx1⟩
                  try simp only [spec_ok]
                  exact ⟨by scalar_tac, by simp [hsIdx1]; scalar_tac⟩
                · step with advance_clock_sink_spec _ (fun _ => True) input hNoop clk1 len () trivial as ⟨r3, _⟩
                  cases r3 with
                  | Ok next_clk =>
                    step with opt_wire_id_in_sorted_total skipped_ols hdr.origin_left as ⟨b1⟩
                    have hUpd :
                        (if b1 = true then
                          if (len != 1#u64) = true then ok (cids1, pcoll1, some CodecError.ZeroLengthStruct, ())
                          else do
                            let cids2 ← decoder_v1.push_wire_id cids1 { client := start_id.client, clock := clk1 }
                            let v ← if (tag != 1#u8) = true then decoder_v1.push_wire_id pcoll1 { client := start_id.client, clock := clk1 } else ok pcoll1
                            ok (cids2, v, none, ())
                         else ok (cids1, pcoll1, none, ())) ⦃ _ => True ⦄ := by
                      apply ite_wp_split <;> intro _
                      · apply ite_wp_split <;> intro _
                        · simp [spec_ok]
                        · step with push_wire_id_total cids1 { client := start_id.client, clock := clk1 } as ⟨cids2⟩
                          have hP :
                              (if (tag != 1#u8) = true then decoder_v1.push_wire_id pcoll1 { client := start_id.client, clock := clk1 }
                               else ok pcoll1) ⦃ _ => True ⦄ := by
                            apply ite_wp_split <;> intro _
                            · exact push_wire_id_total pcoll1 { client := start_id.client, clock := clk1 }
                            · simp [spec_ok]
                          step with hP as ⟨v⟩
                      · simp [spec_ok]
                    step with hUpd as ⟨cids2, pcoll2, err2⟩
                    step as ⟨sIdx1, hsIdx1⟩
                    try simp only [spec_ok]
                    have hLt : (sIdx : Nat) < (count : Nat) := by scalar_tac
                    have hErr2 : errFlag err2 ≤ 1 := by cases err2 <;> simp
                    exact ⟨by scalar_tac, by simp [hsIdx1]; omega⟩
                  | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp⟩
              | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp⟩
            | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp⟩
      | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp⟩
    · simp [spec_ok]
    · simp [spec_ok]
  step with hLoop as ⟨cids, pcoll, cur, err⟩
  cases err <;> simp [spec_ok]

@[local step]
theorem collect_colliding_origin_items_total
    (input : Slice Std.U8) (clients_start clients : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (skipped_ols : Slice decoder_v1.WireId) :
    decoder_v1.collect_colliding_origin_items input clients_start clients limits skipped_ols
      ⦃ _ => True ⦄ := by
  unfold decoder_v1.collect_colliding_origin_items
  have hNoop := noop_sink_v1sink_total.toSpanSafe input
  have hLoop :
      decoder_v1.collect_colliding_origin_items_loop input clients limits skipped_ols ()
        clients_start (alloc.vec.Vec.new decoder_v1.WireId) (alloc.vec.Vec.new decoder_v1.WireId)
        0#usize none ⦃ _ => True ⦄ := by
    unfold decoder_v1.collect_colliding_origin_items_loop
    let inv : decoder_v1.NoopSink × Std.Usize × (alloc.vec.Vec decoder_v1.WireId) ×
        (alloc.vec.Vec decoder_v1.WireId) × Std.Usize × Option CodecError → Prop :=
      fun (_, _, _, _, cIdx, _) => cIdx.val ≤ clients.val
    refine loop.spec_decr_nat
      (fun (_, _, _, _, cIdx, err) => errFlag err + (clients.val - cIdx.val))
      inv (fun _ => True) _
      ((), clients_start, alloc.vec.Vec.new decoder_v1.WireId, alloc.vec.Vec.new decoder_v1.WireId, 0#usize, none)
      ?_ (by scalar_tac)
    intro ⟨noop1, cur1, cids1, pcoll1, cIdx, err1⟩ hcLe
    unfold decoder_v1.collect_colliding_origin_items_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with read_var_u64_sink_spec _ (fun _ => True) input hNoop cur1 noop1 trivial as ⟨r, _⟩
      cases r with
      | Ok p =>
        rcases p with ⟨count_u64, p1⟩
        step with checked_usize_limit_total count_u64 LimitKind.Structs as ⟨r1⟩
        cases r1 with
        | Ok cnt =>
          step with read_var_u64_sink_spec _ (fun _ => True) input hNoop p1 () trivial as ⟨r2, _⟩
          cases r2 with
          | Ok p2 =>
            rcases p2 with ⟨client, p21⟩
            step with read_var_u64_sink_spec _ (fun _ => True) input hNoop p21 () trivial as ⟨r3, _⟩
            cases r3 with
            | Ok p3 =>
              rcases p3 with ⟨clock, p31⟩
              step with collect_colliding_in_client_total input p31 { client, clock } cnt limits
                skipped_ols cids1 pcoll1 as ⟨r4, cids2, pcoll2⟩
              cases r4 with
              | Ok next_cur =>
                step as ⟨cIdx1, hcIdx1⟩
                try simp only [spec_ok]
                exact ⟨by scalar_tac, by simp [hcIdx1]; scalar_tac⟩
              | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp⟩
            | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp⟩
          | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp⟩
        | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp⟩
      | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp⟩
    · simp [spec_ok]
    · simp [spec_ok]
  step with hLoop as ⟨cids, pcoll, err⟩
  cases err <;> simp [spec_ok]

@[local step]
theorem client_has_origin_in_total
    (input : Slice Std.U8) (start_pos count : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (target_ids : Slice decoder_v1.WireId) :
    decoder_v1.client_has_origin_in input start_pos count limits target_ids ⦃ _ => True ⦄ := by
  unfold decoder_v1.client_has_origin_in
  have hNoop := noop_sink_v1sink_total.toSpanSafe input
  have hLoop :
      decoder_v1.client_has_origin_in_loop input count limits target_ids () start_pos 0#usize false none
        ⦃ _ => True ⦄ := by
    unfold decoder_v1.client_has_origin_in_loop
    let inv : decoder_v1.NoopSink × Std.Usize × Std.Usize × Bool × Option CodecError → Prop :=
      fun (_, _, sIdx, _, _) => sIdx.val ≤ count.val
    refine loop.spec_decr_nat
      (fun (_, _, sIdx, found, err) => errFlag err + (if found = true then 0 else 1) + (count.val - sIdx.val))
      inv (fun _ => True) _ ((), start_pos, 0#usize, false, none) ?_ (by scalar_tac)
    intro ⟨noop1, cur1, sIdx, found1, err1⟩ hsLe
    unfold decoder_v1.client_has_origin_in_loop.body
    dsimp only
    by_cases hlt : sIdx < count
    · rw [if_pos hlt]
      by_cases hfound : found1 = true
      · simp only [hfound, ↓reduceIte, spec_ok]
      · simp only [hfound, Bool.false_eq_true, ↓reduceIte]
        by_cases hnone : core.option.Option.is_none err1 = true
        · simp only [hnone, ↓reduceIte]
          have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
          subst herr
          step with read_u8_at_total input cur1 as ⟨r, _⟩
          cases r with
          | Ok p =>
            rcases p with ⟨info, after_info⟩
            step as ⟨tag, _⟩
            split_ifs with h0 h10
            · step with read_var_u64_sink_spec _ (fun _ => True) input hNoop after_info noop1 trivial as ⟨r1, _⟩
              cases r1 with
              | Ok p1 =>
                rcases p1 with ⟨_, next_cur⟩
                step as ⟨sIdx1, hsIdx1⟩
                try simp only [spec_ok]
                exact ⟨by scalar_tac, by simp [hsIdx1, hfound]; scalar_tac⟩
              | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp [hfound]⟩
            · step with read_var_u64_sink_spec _ (fun _ => True) input hNoop after_info noop1 trivial as ⟨r1, _⟩
              cases r1 with
              | Ok p1 =>
                rcases p1 with ⟨_, next_cur⟩
                step as ⟨sIdx1, hsIdx1⟩
                try simp only [spec_ok]
                exact ⟨by scalar_tac, by simp [hsIdx1, hfound]; scalar_tac⟩
              | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp [hfound]⟩
            · step with decode_item_header_spec _ (fun _ => True) input hNoop after_info info noop1 trivial as ⟨r1, _⟩
              cases r1 with
              | Ok p1 =>
                rcases p1 with ⟨hdr, content_start⟩
                step with opt_wire_id_in_sorted_total target_ids hdr.origin_left as ⟨b1⟩
                by_cases hb1 : b1 = true
                · simp only [hb1, ↓reduceIte, spec_ok]
                  exact ⟨hsLe, by simp [hfound]⟩
                · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
                  step with opt_wire_id_in_sorted_total target_ids hdr.origin_right as ⟨b2⟩
                  by_cases hb2 : b2 = true
                  · simp only [hb2, ↓reduceIte, spec_ok]
                    exact ⟨hsLe, by simp [hfound]⟩
                  · simp only [hb2, Bool.false_eq_true, ↓reduceIte]
                    step with parent_item_in_sorted_total target_ids hdr.parent as ⟨b3⟩
                    by_cases hb3 : b3 = true
                    · simp only [hb3, ↓reduceIte, spec_ok]
                      exact ⟨hsLe, by simp [hfound]⟩
                    · simp only [hb3, Bool.false_eq_true, ↓reduceIte]
                      step with decode_item_content_spec _ (fun _ => True) input hNoop content_start tag limits 0#usize () trivial
                        as ⟨r2, _⟩
                      cases r2 with
                      | Ok t =>
                        rcases t with ⟨_, content_end, _⟩
                        step as ⟨sIdx1, hsIdx1⟩
                        try simp only [spec_ok]
                        exact ⟨by scalar_tac, by simp [hsIdx1, hfound]; scalar_tac⟩
                      | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp [hfound]⟩
              | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp [hfound]⟩
          | Err e => try simp only [spec_ok]; exact ⟨hsLe, by simp [hfound]⟩
        · simp only [hnone, Bool.false_eq_true, ↓reduceIte, spec_ok]
    · rw [if_neg hlt]
      simp [spec_ok]
  step with hLoop as ⟨cur, found, err⟩
  cases err <;> simp [spec_ok]

@[local step]
theorem has_origin_referencing_total
    (input : Slice Std.U8) (clients_start clients : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (target_ids : Slice decoder_v1.WireId) :
    decoder_v1.has_origin_referencing input clients_start clients limits target_ids ⦃ _ => True ⦄ := by
  unfold decoder_v1.has_origin_referencing
  have hNoop := noop_sink_v1sink_total.toSpanSafe input
  have hLoop :
      decoder_v1.has_origin_referencing_loop input clients limits target_ids () clients_start 0#usize false none
        ⦃ _ => True ⦄ := by
    unfold decoder_v1.has_origin_referencing_loop
    let inv : decoder_v1.NoopSink × Std.Usize × Std.Usize × Bool × Option CodecError → Prop :=
      fun (_, _, cIdx, _, _) => cIdx.val ≤ clients.val
    refine loop.spec_decr_nat
      (fun (_, _, cIdx, found, err) => errFlag err + (if found = true then 0 else 1) + (clients.val - cIdx.val))
      inv (fun _ => True) _ ((), clients_start, 0#usize, false, none) ?_ (by scalar_tac)
    intro ⟨noop1, cur1, cIdx, found1, err1⟩ hcLe
    unfold decoder_v1.has_origin_referencing_loop.body
    dsimp only
    by_cases hlt : cIdx < clients
    · rw [if_pos hlt]
      by_cases hfound : found1 = true
      · simp only [hfound, ↓reduceIte, spec_ok]
      · simp only [hfound, Bool.false_eq_true, ↓reduceIte]
        by_cases hnone : core.option.Option.is_none err1 = true
        · simp only [hnone, ↓reduceIte]
          have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
          subst herr
          step with read_var_u64_sink_spec _ (fun _ => True) input hNoop cur1 noop1 trivial as ⟨r, _⟩
          cases r with
          | Ok p =>
            rcases p with ⟨count_u64, p1⟩
            step with checked_usize_limit_total count_u64 LimitKind.Structs as ⟨r1⟩
            cases r1 with
            | Ok cnt =>
              step with read_var_u64_sink_spec _ (fun _ => True) input hNoop p1 () trivial as ⟨r2, _⟩
              cases r2 with
              | Ok p2 =>
                rcases p2 with ⟨_, p21⟩
                step with read_var_u64_sink_spec _ (fun _ => True) input hNoop p21 () trivial as ⟨r3, _⟩
                cases r3 with
                | Ok p3 =>
                  rcases p3 with ⟨_, p31⟩
                  step with client_has_origin_in_total input p31 cnt limits target_ids as ⟨r4⟩
                  cases r4 with
                  | Ok p4 =>
                    rcases p4 with ⟨next_cur, hit⟩
                    step as ⟨cIdx1, hcIdx1⟩
                    try simp only [spec_ok]
                    refine ⟨by scalar_tac, ?_⟩
                    cases hit <;> simp [hcIdx1, hfound] <;> scalar_tac
                  | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp [hfound]⟩
                | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp [hfound]⟩
              | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp [hfound]⟩
            | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp [hfound]⟩
          | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp [hfound]⟩
        · simp only [hnone, Bool.false_eq_true, ↓reduceIte, spec_ok]
    · rw [if_neg hlt]
      simp [spec_ok]
  step with hLoop as ⟨found, err⟩
  cases err <;> simp [spec_ok]

@[local step]
theorem scan_delete_ranges_coverage_total
    (input : Slice Std.U8) (start_pos : Std.Usize) (client : Std.U64) (range_count : Std.Usize)
    (pending_zeros : Slice decoder_v1.WireId) (zero_max_hi : Slice Std.Usize)
    (pending_colliding : Slice decoder_v1.WireId) (coll_max_hi : Slice Std.Usize) :
    decoder_v1.scan_delete_ranges_coverage input start_pos client range_count
      pending_zeros zero_max_hi pending_colliding coll_max_hi ⦃ _ => True ⦄ := by
  unfold decoder_v1.scan_delete_ranges_coverage
  have hNoop := noop_sink_v1sink_total.toSpanSafe input
  have hLoop :
      decoder_v1.scan_delete_ranges_coverage_loop input client range_count
        pending_zeros zero_max_hi pending_colliding coll_max_hi () start_pos 0#usize none
        ⦃ _ => True ⦄ := by
    unfold decoder_v1.scan_delete_ranges_coverage_loop
    let inv : (Slice Std.Usize) × (Slice Std.Usize) × decoder_v1.NoopSink ×
        Std.Usize × Std.Usize × Option CodecError → Prop :=
      fun (_, _, _, _, rIdx, _) => rIdx.val ≤ range_count.val
    refine loop.spec_decr_nat
      (fun (_, _, _, _, rIdx, err) => errFlag err + (range_count.val - rIdx.val))
      inv (fun _ => True) _ (zero_max_hi, coll_max_hi, (), start_pos, 0#usize, none) ?_ (by scalar_tac)
    intro ⟨zmh1, cmh1, noop1, cur1, rIdx, err1⟩ hrLe
    unfold decoder_v1.scan_delete_ranges_coverage_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with read_one_delete_range_sink_spec _ (fun _ => True) input hNoop cur1 noop1 trivial as ⟨r, _⟩
      cases r with
      | Ok t =>
        rcases t with ⟨start, «end», q2⟩
        have hUpd :
            (if (start != «end») = true then do
              let b1 ← core.slice.Slice.is_empty pending_zeros
              let zmh2 ← if b1 = true then ok zmh1 else decoder_v1.mark_zero_strings_covered pending_zeros zmh1 client start «end»
              let b2 ← core.slice.Slice.is_empty pending_colliding
              let s ← if b2 = true then ok cmh1 else decoder_v1.mark_point_ids_covered pending_colliding cmh1 client start «end»
              ok (zmh2, s, ())
             else ok (zmh1, cmh1, ())) ⦃ _ => True ⦄ := by
          by_cases hne : (start != «end») = true
          · simp only [hne, ↓reduceIte, core.slice.Slice.is_empty, bind_ok]
            have hM1 :
                (if decide (pending_zeros.length = 0) = true then ok zmh1
                 else decoder_v1.mark_zero_strings_covered pending_zeros zmh1 client start «end») ⦃ _ => True ⦄ := by
              by_cases hz : pending_zeros.length = 0
              · simp [hz, spec_ok]
              · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte]
                exact mark_zero_strings_covered_total pending_zeros zmh1 client start «end»
            step with hM1 as ⟨zmh2⟩
            have hM2 :
                (if decide (pending_colliding.length = 0) = true then ok cmh1
                 else decoder_v1.mark_point_ids_covered pending_colliding cmh1 client start «end») ⦃ _ => True ⦄ := by
              by_cases hc : pending_colliding.length = 0
              · simp [hc, spec_ok]
              · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
                exact mark_point_ids_covered_total pending_colliding cmh1 client start «end»
            step with hM2 as ⟨cmh2⟩
          · simp only [hne, Bool.false_eq_true, ↓reduceIte, spec_ok]
        step with hUpd as ⟨zmh2, cmh2⟩
        step as ⟨rIdx1, hrIdx1⟩
        try simp only [spec_ok]
        exact ⟨by scalar_tac, by simp [hrIdx1]; scalar_tac⟩
      | Err e => try simp only [spec_ok]; exact ⟨hrLe, by simp⟩
    · simp [spec_ok]
    · simp [spec_ok]
  step with hLoop as ⟨zmh, cmh, cur, err⟩
  cases err <;> simp [spec_ok]

@[local step]
theorem scan_delete_set_coverage_total
    (input : Slice Std.U8) (ds_start : Std.Usize)
    (pending_zeros : Slice decoder_v1.WireId) (zero_max_hi : Slice Std.Usize)
    (pending_colliding : Slice decoder_v1.WireId) (coll_max_hi : Slice Std.Usize) :
    decoder_v1.scan_delete_set_coverage input ds_start
      pending_zeros zero_max_hi pending_colliding coll_max_hi ⦃ _ => True ⦄ := by
  unfold decoder_v1.scan_delete_set_coverage
  have hNoop := noop_sink_v1sink_total.toSpanSafe input
  step with read_var_u64_sink_spec _ (fun _ => True) input hNoop ds_start () trivial as ⟨r, _⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨clients_u64, cur⟩
    step with checked_usize_limit_total clients_u64 LimitKind.DeleteClients as ⟨r1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      have hLoop :
          decoder_v1.scan_delete_set_coverage_loop input pending_zeros zero_max_hi
            pending_colliding coll_max_hi () cur val1 0#usize none ⦃ _ => True ⦄ := by
        unfold decoder_v1.scan_delete_set_coverage_loop
        let inv : (Slice Std.Usize) × (Slice Std.Usize) × decoder_v1.NoopSink ×
            Std.Usize × Std.Usize × Option CodecError → Prop :=
          fun (_, _, _, _, cIdx, _) => cIdx.val ≤ val1.val
        refine loop.spec_decr_nat
          (fun (_, _, _, _, cIdx, err) => errFlag err + (val1.val - cIdx.val))
          inv (fun _ => True) _ (zero_max_hi, coll_max_hi, (), cur, 0#usize, none) ?_ (by scalar_tac)
        intro ⟨zmh1, cmh1, noop2, cur1, cIdx, err1⟩ hcLe
        unfold decoder_v1.scan_delete_set_coverage_loop.body
        dsimp only
        split_ifs with hlt hnone
        · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
          subst herr
          step with read_var_u64_sink_spec _ (fun _ => True) input hNoop cur1 noop2 trivial as ⟨r2, _⟩
          cases r2 with
          | Ok p =>
            rcases p with ⟨client, p1⟩
            step with read_var_u64_sink_spec _ (fun _ => True) input hNoop p1 () trivial as ⟨r3, _⟩
            cases r3 with
            | Ok p2 =>
              rcases p2 with ⟨ranges_u64, p21⟩
              step with checked_usize_limit_total ranges_u64 LimitKind.DeleteRanges as ⟨r4⟩
              cases r4 with
              | Ok rc =>
                step with scan_delete_ranges_coverage_total input p21 client rc
                  pending_zeros zmh1 pending_colliding cmh1 as ⟨r5, zmh2, cmh2⟩
                cases r5 with
                | Ok next_cur =>
                  step as ⟨cIdx1, hcIdx1⟩
                  try simp only [spec_ok]
                  exact ⟨by scalar_tac, by simp [hcIdx1]; scalar_tac⟩
                | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp⟩
              | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp⟩
            | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp⟩
          | Err e => try simp only [spec_ok]; exact ⟨hcLe, by simp⟩
        · simp [spec_ok]
        · simp [spec_ok]
      step with hLoop as ⟨zmh, cmh, err⟩
      cases err <;> simp [spec_ok]
    | Err e => simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  | Err e => simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

private theorem finish_coverage_check_total
    (pz pc : Slice decoder_v1.WireId)
    (s2 s3 : Slice Std.Usize)
    (backZ backC : Slice Std.Usize → alloc.vec.Vec Std.Usize) :
    (do
      let b2 ← core.slice.Slice.is_empty pz
      if b2 = true then
        let b3 ← core.slice.Slice.is_empty pc
        if b3 = true then ok (core.result.Result.Ok (), pz, pc)
        else
          let coll_max_hi1 := backC s3
          let s4 := alloc.vec.Vec.deref coll_max_hi1
          let b4 ← decoder_v1.all_zero_strings_covered s4
          if b4 = true then ok (core.result.Result.Ok (), pz, pc)
          else ok (core.result.Result.Err CodecError.ZeroLengthStruct, pz, pc)
      else
        let zero_max_hi1 := backZ s2
        let s4 := alloc.vec.Vec.deref zero_max_hi1
        let b3 ← decoder_v1.all_zero_strings_covered s4
        if b3 = true then
          let b4 ← core.slice.Slice.is_empty pc
          if b4 = true then ok (core.result.Result.Ok (), pz, pc)
          else
            let coll_max_hi1 := backC s3
            let s5 := alloc.vec.Vec.deref coll_max_hi1
            let b5 ← decoder_v1.all_zero_strings_covered s5
            if b5 = true then ok (core.result.Result.Ok (), pz, pc)
            else ok (core.result.Result.Err CodecError.ZeroLengthStruct, pz, pc)
        else ok (core.result.Result.Err CodecError.ZeroLengthStruct, pz, pc)) ⦃ _ => True ⦄ := by
  step as ⟨b2, _⟩
  by_cases hb2 : b2 = true
  · simp only [hb2, ↓reduceIte]
    step as ⟨b3, _⟩
    by_cases hb3 : b3 = true
    · simp only [hb3, ↓reduceIte, spec_ok]
    · simp only [hb3, Bool.false_eq_true, ↓reduceIte]
      step with all_zero_strings_covered_total (alloc.vec.Vec.deref (backC s3)) as ⟨b4⟩
      split_ifs <;> simp [spec_ok]
  · simp only [hb2, Bool.false_eq_true, ↓reduceIte]
    step with all_zero_strings_covered_total (alloc.vec.Vec.deref (backZ s2)) as ⟨b3⟩
    by_cases hb3 : b3 = true
    · simp only [hb3, ↓reduceIte]
      step as ⟨b4, _⟩
      by_cases hb4 : b4 = true
      · simp only [hb4, ↓reduceIte, spec_ok]
      · simp only [hb4, Bool.false_eq_true, ↓reduceIte]
        step with all_zero_strings_covered_total (alloc.vec.Vec.deref (backC s3)) as ⟨b5⟩
        split_ifs <;> simp [spec_ok]
    · simp only [hb3, Bool.false_eq_true, ↓reduceIte, spec_ok]

@[local step]
theorem verify_delete_set_coverage_total
    (input : Slice Std.U8) (ds_start : Std.Usize)
    (pending_zero_strings pending_colliding : Slice decoder_v1.WireId) :
    decoder_v1.verify_delete_set_coverage input ds_start pending_zero_strings pending_colliding
      ⦃ _ => True ⦄ := by
  unfold decoder_v1.verify_delete_set_coverage
  step as ⟨b, _⟩
  by_cases hb : b = true
  · simp only [hb, ↓reduceIte]
    step as ⟨b1, _⟩
    by_cases hb1 : b1 = true
    · simp only [hb1, ↓reduceIte, spec_ok]
    · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
      step with sort_wire_ids_total pending_colliding as ⟨pc1⟩
      step with alloc_zero_max_hi_total (Slice.len pc1) as ⟨cmh⟩
      simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
      step with scan_delete_set_coverage_total input ds_start pending_zero_strings _ pc1 _ as ⟨r, s2, s3⟩
      cases r with
      | Ok _ =>
        simp only [core_ops_try_branch_ok, bind_ok]
        exact finish_coverage_check_total pending_zero_strings pc1 s2 s3 _ _
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    step with sort_wire_ids_total pending_zero_strings as ⟨pz1⟩
    step with alloc_zero_max_hi_total (Slice.len pz1) as ⟨zmh⟩
    step as ⟨b1, _⟩
    have hPrepC :
        (if b1 = true then ok (pending_colliding, alloc.vec.Vec.new Std.Usize)
         else do
           let pending_colliding2 ← decoder_v1.sort_wire_ids pending_colliding
           let i := Slice.len pending_colliding2
           let coll_max_hi1 ← decoder_v1.alloc_zero_max_hi i
           ok (pending_colliding2, coll_max_hi1)) ⦃ _ => True ⦄ := by
      by_cases hb1 : b1 = true
      · simp only [hb1, ↓reduceIte, spec_ok]
      · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
        step with sort_wire_ids_total pending_colliding as ⟨pc2⟩
        step with alloc_zero_max_hi_total (Slice.len pc2) as ⟨cmh2⟩
    step with hPrepC as ⟨pc1, cmh⟩
    simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
    step with scan_delete_set_coverage_total input ds_start pz1 _ pc1 _ as ⟨r, s2, s3⟩
    cases r with
    | Ok _ =>
      simp only [core_ops_try_branch_ok, bind_ok]
      exact finish_coverage_check_total pz1 pc1 s2 s3 _ _
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

@[local step]
theorem verify_skipped_zero_items_total
    (input : Slice Std.U8) (clients_start clients ds_start : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore)
    (skipped_ols pending_zero_strings : Slice decoder_v1.WireId) :
    decoder_v1.verify_skipped_zero_items input clients_start clients ds_start limits
      skipped_ols pending_zero_strings ⦃ _ => True ⦄ := by
  unfold decoder_v1.verify_skipped_zero_items
  step with sort_wire_ids_total skipped_ols as ⟨skipped_ols1⟩
  step with collect_colliding_origin_items_total input clients_start clients limits skipped_ols1 as ⟨r⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]
    rcases val with ⟨colliding_ids, pending_colliding⟩
    step as ⟨b, _⟩
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte, lift, bind_ok, alloc.vec.Vec.deref_mut]
      step with verify_delete_set_coverage_total input ds_start pending_zero_strings _ as ⟨r1, pz1, _⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, lift, bind_ok, alloc.vec.Vec.deref_mut]
      step with sort_wire_ids_total _ as ⟨s1⟩
      step with has_origin_referencing_total input clients_start clients limits _ as ⟨r1⟩
      cases r1 with
      | Ok val1 =>
        simp only [core_ops_try_branch_ok, bind_ok]
        by_cases hv : val1 = true
        · simp only [hv, ↓reduceIte, spec_ok]
        · simp only [hv, Bool.false_eq_true, ↓reduceIte, lift, bind_ok, alloc.vec.Vec.deref_mut]
          step with verify_delete_set_coverage_total input ds_start pending_zero_strings _ as ⟨r2, pz1, _⟩
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

theorem decode_struct_frame_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (pos client_start_pos : Std.Usize) (client_start_clock : Std.U64)
    (s_idx : Std.Usize) (id : decoder_v1.WireId)
    (limits : decoder_v1.DecodeLimitsCore) (acc : decoder_v1.DecodeAcc)
    (state : decoder_v1.ClientSeqState)
    (sink : S) (hSink : Inv sink) :
    decoder_v1.decode_struct_frame V input pos client_start_pos client_start_clock s_idx id limits acc state sink ⦃ (r, _, sink') =>
      Inv sink' ∧
      match r with
      | .Ok (nc, nxt, _, _, _) => id.clock.val ≤ nc.val ∧ pos.val ≤ nxt.val ∧ nxt.val ≤ input.length
      | .Err _ => True ⦄ := by
  unfold decoder_v1.decode_struct_frame
  step with read_u8_at_total input pos as ⟨r, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]
    rcases val with ⟨info, cur⟩
    dsimp only at hr
    step as ⟨tag, _⟩
    by_cases h0 : tag = 0#u8
    · simp only [h0, ↓reduceIte]
      step with read_var_u64_sink_spec V Inv input hV cur sink hSink as ⟨r1, sink1, hInv1, hr1⟩
      cases r1 with
      | Ok val1 =>
        simp only [core_ops_try_branch_ok, bind_ok]
        rcases val1 with ⟨len, p⟩
        dsimp only at hr1
        step with advance_clock_sink_spec V Inv input hV id.clock len sink1 hInv1 as ⟨r2, sink2, hInv2, hr2⟩
        cases r2 with
        | Ok val2 =>
          simp only [core_ops_try_branch_ok, bind_ok]
          dsimp only at hr2
          step with hV.on_gc sink2 id len hInv2 as ⟨r3, sink3, hInv3⟩
          cases r3 with
          | Ok _ =>
            simp only [core_ops_try_branch_ok, bind_ok]
            split_ifs <;> (simp only [spec_ok]; exact ⟨hInv3, by omega, by omega, hr1.2⟩)
          | Err e =>
            simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
            exact ⟨hInv3, trivial⟩
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact ⟨hInv2, trivial⟩
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
        exact ⟨hInv1, trivial⟩
    · simp only [h0, ↓reduceIte]
      by_cases h10 : tag = 10#u8
      · simp only [h10, ↓reduceIte]
        step with read_var_u64_sink_spec V Inv input hV cur sink hSink as ⟨r1, sink1, hInv1, hr1⟩
        cases r1 with
        | Ok val1 =>
          simp only [core_ops_try_branch_ok, bind_ok]
          rcases val1 with ⟨len, p⟩
          dsimp only at hr1
          step with advance_clock_sink_spec V Inv input hV id.clock len sink1 hInv1 as ⟨r2, sink2, hInv2, hr2⟩
          cases r2 with
          | Ok val2 =>
            simp only [core_ops_try_branch_ok, bind_ok]
            dsimp only at hr2
            step with hV.on_skip sink2 id len hInv2 as ⟨r3, sink3, hInv3⟩
            cases r3 with
            | Ok _ =>
              simp only [core_ops_try_branch_ok, bind_ok]
              split_ifs <;> (simp only [spec_ok]; exact ⟨hInv3, by omega, by omega, hr1.2⟩)
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
              exact ⟨hInv3, trivial⟩
          | Err e =>
            simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
            exact ⟨hInv2, trivial⟩
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact ⟨hInv1, trivial⟩
      · simp only [h10, ↓reduceIte]
        step with decode_item_header_spec V Inv input hV cur info sink hSink as ⟨r1, sink1, hInv1, hr1⟩
        cases r1 with
        | Ok val1 =>
          simp only [core_ops_try_branch_ok, bind_ok]
          rcases val1 with ⟨hdr, content_start⟩
          dsimp only at hr1
          step with decode_item_content_spec V Inv input hV content_start tag limits acc.entries sink1 hInv1
            as ⟨r2, sink2, hInv2, hr2⟩
          cases r2 with
          | Ok val2 =>
            simp only [core_ops_try_branch_ok, bind_ok]
            rcases val2 with ⟨len, content_end, entries⟩
            dsimp only at hr2
            have hDelta :
                (if content_end ≥ content_start then content_end - content_start else ok 0#usize)
                ⦃ _ => True ⦄ := by
              by_cases hge : content_end ≥ content_start
              · rw [if_pos hge]; step*
              · rw [if_neg hge]; simp [spec_ok]
            step with hDelta as ⟨delta⟩
            step with checked_add_limit_total acc.content_bytes delta LimitKind.ContentBytes as ⟨r3⟩
            cases r3 with
            | Ok val3 =>
              simp only [core_ops_try_branch_ok, bind_ok]
              by_cases hlim : val3 > limits.max_content_bytes
              · rw [if_pos hlim]; simp [spec_ok, hInv2]
              · rw [if_neg hlim]
                have hPosCe : pos.val ≤ content_end.val ∧ content_end.val ≤ input.length :=
                  ⟨by omega, hr2.2⟩
                have hHdrOk : WireParentOk input hdr.parent ∧ OptSpanOk input hdr.parent_sub :=
                  ⟨hr1.2.2.1, hr1.2.2.2⟩
                by_cases hzero : len = 0#u64
                · rw [if_pos hzero]
                  exact decode_struct_frame_slow_spec V Inv input hV pos client_start_pos client_start_clock
                    s_idx id info tag hdr content_start len content_end entries val3 limits acc state sink2
                    hInv2 hPosCe hHdrOk
                · rw [if_neg hzero]
                  by_cases hact : state.active = true
                  · simp only [hact, ↓reduceIte]
                    exact decode_struct_frame_slow_spec V Inv input hV pos client_start_pos client_start_clock
                      s_idx id info tag hdr content_start len content_end entries val3 limits acc state sink2
                      hInv2 hPosCe hHdrOk
                  · simp only [hact, Bool.false_eq_true, ↓reduceIte]
                    step with advance_clock_sink_spec V Inv input hV id.clock len sink2 hInv2
                      as ⟨r4, sink3, hInv3, hr4⟩
                    cases r4 with
                    | Ok val4 =>
                      simp only [core_ops_try_branch_ok, bind_ok]
                      dsimp only at hr4
                      have hMeta : ItemMetaOk input
                          { origin_left := hdr.origin_left,
                            origin_right := hdr.origin_right,
                            parent := hdr.parent,
                            parent_sub := hdr.parent_sub,
                            raw_range := { start := pos, «end» := content_end } } :=
                        ⟨hHdrOk.1, hHdrOk.2, hPosCe.1, hPosCe.2⟩
                      step with hV.on_item sink3 id len _ hInv3 hMeta as ⟨r5, sink4, hInv4⟩
                      cases r5 with
                      | Ok _ =>
                        simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
                        exact ⟨hInv4, by omega, hPosCe.1, hPosCe.2⟩
                      | Err e =>
                        simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                        exact ⟨hInv4, trivial⟩
                    | Err e =>
                      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
                      exact ⟨hInv3, trivial⟩
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
              exact ⟨hInv2, trivial⟩
          | Err e =>
            simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
            exact ⟨hInv2, trivial⟩
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
          exact ⟨hInv1, trivial⟩
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
    exact ⟨hSink, trivial⟩

theorem decode_struct_frame_total
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkTotal V Inv)
    (pos client_start_pos : Std.Usize) (client_start_clock : Std.U64)
    (s_idx : Std.Usize) (id : decoder_v1.WireId)
    (limits : decoder_v1.DecodeLimitsCore) (acc : decoder_v1.DecodeAcc)
    (state : decoder_v1.ClientSeqState)
    (sink : S) (hSink : Inv sink) :
    decoder_v1.decode_struct_frame V input pos client_start_pos client_start_clock s_idx id limits acc state sink ⦃ (_, _, sink') => Inv sink' ⦄ := by
  step with decode_struct_frame_spec V Inv input (hV.toSpanSafe input) pos client_start_pos client_start_clock s_idx id limits acc state sink hSink
    as ⟨_, _, sink', hInv, _⟩
  exact hInv

theorem decode_client_structs_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (start_pos : Std.Usize) (start_id : decoder_v1.WireId) (count : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (start_acc : decoder_v1.DecodeAcc)
    (sink : S) (hSink : Inv sink) :
    decoder_v1.decode_client_structs V input start_pos start_id count limits start_acc sink
      ⦃ (_, sink') => Inv sink' ⦄ := by
  unfold decoder_v1.decode_client_structs
  let inv : S × Std.Usize × Std.U64 × decoder_v1.DecodeAcc ×
      decoder_v1.ClientSeqState × alloc.vec.Vec decoder_v1.WireId ×
      alloc.vec.Vec decoder_v1.WireId × Std.Usize × Option CodecError → Prop :=
    fun (sink1, _, _, _, _, _, _, sIdx, _) => Inv sink1 ∧ sIdx.val ≤ count.val
  have hLoop :
      decoder_v1.decode_client_structs_loop V input start_pos start_id.client start_id.clock count limits sink
        start_pos start_id.clock start_acc
        { active := false,
          ytext_types := alloc.vec.Vec.new order_range.ClockRange,
          seq_ranges := alloc.vec.Vec.new order_range.ClockRange,
          just_skipped_ol := none }
        (alloc.vec.Vec.new decoder_v1.WireId) (alloc.vec.Vec.new decoder_v1.WireId) 0#usize none
        ⦃ (sink1, _, _, _, _, _) => Inv sink1 ⦄ := by
    unfold decoder_v1.decode_client_structs_loop
    refine loop.spec_decr_nat
      (fun (_, _, _, _, _, _, _, sIdx, err) => errFlag err + (count.val - sIdx.val))
      inv _ _
      (sink, start_pos, start_id.clock, start_acc,
        { active := false,
          ytext_types := alloc.vec.Vec.new order_range.ClockRange,
          seq_ranges := alloc.vec.Vec.new order_range.ClockRange,
          just_skipped_ol := none },
        alloc.vec.Vec.new decoder_v1.WireId, alloc.vec.Vec.new decoder_v1.WireId, 0#usize, none) ?_
      ⟨hSink, by scalar_tac⟩
    intro ⟨sink1, cur1, clk1, acc1, state1, skippedOls1, pendingZeros1, sIdx, err1⟩ ⟨hInv1, hs⟩
    unfold decoder_v1.decode_client_structs_loop.body
    dsimp only
    split_ifs with hlt hnone
    · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
      subst herr
      step with decode_struct_frame_spec V Inv input hV cur1 start_pos start_id.clock sIdx
        { client := start_id.client, clock := clk1 } limits acc1 state1 sink1 hInv1
        as ⟨r, state2, sink2, hInv2, _⟩
      cases r with
      | Ok t =>
        rcases t with ⟨next_clk, next_cur, next_acc, skipped_ol, needs_del⟩
        dsimp only
        have hPush :
            (if needs_del = true then decoder_v1.push_wire_id pendingZeros1 { client := start_id.client, clock := clk1 }
             else ok pendingZeros1) ⦃ _ => True ⦄ := by
          by_cases hdel : needs_del = true
          · simp only [hdel, ↓reduceIte]
            exact push_wire_id_total pendingZeros1 { client := start_id.client, clock := clk1 }
          · simp only [hdel, Bool.false_eq_true, ↓reduceIte, spec_ok]
        cases skipped_ol with
        | none =>
          step with hPush as ⟨pz2⟩
          step as ⟨sIdx1, hsIdx1⟩
          try simp only [spec_ok]
          exact ⟨⟨hInv2, by scalar_tac⟩, by simp [hsIdx1]; scalar_tac⟩
        | some ol =>
          step with hV.on_skipped_zero_origin sink2 ol hInv2 as ⟨sink3, hInv3⟩
          step with push_wire_id_total skippedOls1 ol as ⟨ols2⟩
          step with hPush as ⟨pz2⟩
          step as ⟨sIdx1, hsIdx1⟩
          try simp only [spec_ok]
          exact ⟨⟨hInv3, by scalar_tac⟩, by simp [hsIdx1]; scalar_tac⟩
      | Err e =>
        try simp only [spec_ok]
        exact ⟨⟨hInv2, hs⟩, by simp⟩
    · simp [spec_ok, hInv1]
    · simp [spec_ok, hInv1]
  step with hLoop as ⟨sink1, cur, acc, ols, pz, err, hInv1⟩
  cases err <;> simp [spec_ok, hInv1]

theorem decode_client_structs_total
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkTotal V Inv)
    (start_pos : Std.Usize) (start_id : decoder_v1.WireId) (count : Std.Usize)
    (limits : decoder_v1.DecodeLimitsCore) (start_acc : decoder_v1.DecodeAcc)
    (sink : S) (hSink : Inv sink) :
    decoder_v1.decode_client_structs V input start_pos start_id count limits start_acc sink
      ⦃ (_, sink') => Inv sink' ⦄ :=
  decode_client_structs_spec V Inv input (hV.toSpanSafe input) start_pos start_id count limits
    start_acc sink hSink

theorem decode_one_client_block_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (cur : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (acc : decoder_v1.DecodeAcc) (sink : S) (hSink : Inv sink) :
    decoder_v1.decode_one_client_block V input cur limits acc sink
      ⦃ (_, sink') => Inv sink' ⦄ := by
  unfold decoder_v1.decode_one_client_block
  step with read_var_u64_sink_spec V Inv input hV cur sink hSink as ⟨r, sink_a, hSink_a, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; (try dsimp)
    rcases val with ⟨count_u64, p1⟩
    dsimp only at hr
    step with checked_usize_limit_total count_u64 LimitKind.Structs as ⟨r1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; (try dsimp)
      step with checked_add_limit_total acc.structs val1 LimitKind.Structs as ⟨r2⟩
      cases r2 with
      | Ok val2 =>
        simp only [core_ops_try_branch_ok, bind_ok]; (try dsimp)
        split_ifs with hmaxs
        · simp [spec_ok, hSink_a]
        · step with checked_add_limit_total acc.entries val1 LimitKind.CollectionEntries as ⟨r3⟩
          cases r3 with
          | Ok val3 =>
            simp only [core_ops_try_branch_ok, bind_ok]; (try dsimp)
            split_ifs with hmaxe
            · simp [spec_ok, hSink_a]
            · step as ⟨i1, hi1⟩
              step with check_fits_kind_sink_spec V Inv input hV i1 val1
                decoder_v1.MIN_STRUCT_BYTES LimitKind.Structs sink_a
                (by simp [decoder_v1.MIN_STRUCT_BYTES]) hSink_a as ⟨r4, sink0, hSink0⟩
              cases r4 with
              | Ok _ =>
                simp only [core_ops_try_branch_ok, bind_ok]; (try dsimp)
                step with read_var_u64_sink_spec V Inv input hV p1 sink0 hSink0 as ⟨r5, sink_b, hSink_b, hr5⟩
                cases r5 with
                | Ok val4 =>
                  simp only [core_ops_try_branch_ok, bind_ok]; (try dsimp)
                  rcases val4 with ⟨client, p2⟩
                  dsimp only at hr5
                  step with hV.record_client sink_b client hSink_b as ⟨r6, sink1, hSink1⟩
                  cases r6 with
                  | Ok val5 =>
                    simp only [core_ops_try_branch_ok, bind_ok]; (try dsimp)
                    split_ifs with hrec
                    · step with read_var_u64_sink_spec V Inv input hV p2 sink1 hSink1 as ⟨r7, sink_c, hSink_c, hr7⟩
                      cases r7 with
                      | Ok val6 =>
                        simp only [core_ops_try_branch_ok, bind_ok]; (try dsimp)
                        rcases val6 with ⟨clock, p3⟩
                        dsimp only at hr7
                        step with hV.begin_client sink_c client val1 hSink_c as ⟨r8, sink2, hSink2⟩
                        cases r8 with
                        | Ok _ =>
                          simp only [core_ops_try_branch_ok, bind_ok]; (try dsimp)
                          exact decode_client_structs_spec V Inv input hV p3
                            { client, clock } val1 limits
                            { acc with structs := val2, entries := val3 } sink2 hSink2
                        | Err e =>
                          simp only [core_ops_try_branch_err, bind_ok,
                            core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
                          (try dsimp); exact hSink2
                      | Err e =>
                        simp only [core_ops_try_branch_err, bind_ok,
                          core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
                        (try dsimp); exact hSink_c
                    · simp [spec_ok, hSink1]
                  | Err e =>
                    simp only [core_ops_try_branch_err, bind_ok,
                      core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
                    (try dsimp); exact hSink1
                | Err e =>
                  simp only [core_ops_try_branch_err, bind_ok,
                    core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
                  (try dsimp); exact hSink_b
              | Err e =>
                simp only [core_ops_try_branch_err, bind_ok,
                  core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
                (try dsimp); exact hSink0
          | Err e =>
            simp only [core_ops_try_branch_err, bind_ok,
              core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
            (try dsimp); exact hSink_a
      | Err e =>
        simp only [core_ops_try_branch_err, bind_ok,
          core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
        (try dsimp); exact hSink_a
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok,
        core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
      (try dsimp); exact hSink_a
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok,
      core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
    (try dsimp); exact hSink_a

theorem decode_one_client_block_total
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkTotal V Inv)
    (cur : Std.Usize) (limits : decoder_v1.DecodeLimitsCore)
    (acc : decoder_v1.DecodeAcc) (sink : S) (hSink : Inv sink) :
    decoder_v1.decode_one_client_block V input cur limits acc sink
      ⦃ (_, sink') => Inv sink' ⦄ :=
  decode_one_client_block_spec V Inv input (hV.toSpanSafe input) cur limits acc sink hSink

theorem decode_update_v1_spec
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkSpanSafe input V Inv)
    (sink : S) (hSink : Inv sink) (limits : decoder_v1.DecodeLimitsCore) :
    decoder_v1.decode_update_v1 V input sink limits ⦃ (_, sink') => Inv sink' ⦄ := by
  unfold decoder_v1.decode_update_v1
  step with read_var_u64_sink_spec V Inv input hV 0#usize sink hSink as ⟨r, sink_a, hSink_a, hr⟩
  cases r with
  | Ok val =>
    simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
    rcases val with ⟨clients_u64, clients_start⟩
    dsimp only at hr
    step with checked_usize_limit_total clients_u64 LimitKind.Clients as ⟨r1⟩
    cases r1 with
    | Ok val1 =>
      simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
      split_ifs with hlim
      · simp [spec_ok, hSink_a]
      · step as ⟨i1, hi1⟩
        step with check_fits_kind_sink_spec V Inv input hV i1 val1
          decoder_v1.MIN_CLIENT_BYTES LimitKind.Clients sink_a
          (by simp [decoder_v1.MIN_CLIENT_BYTES]) hSink_a as ⟨r2, sink0, hSink0⟩
        cases r2 with
        | Ok _ =>
          simp only [core_ops_try_branch_ok, bind_ok]; try dsimp only
          have hLoop :
              decoder_v1.decode_update_v1_loop V input sink0 limits.max_structs limits.max_clients
                limits.max_collection_entries limits.max_any_depth limits.max_content_bytes
                clients_start val1 { structs := 0#usize, entries := 0#usize, content_bytes := 0#usize }
                (alloc.vec.Vec.new decoder_v1.WireId) (alloc.vec.Vec.new decoder_v1.WireId) 0#usize none
                ⦃ (sink1, _, _, _, _, _) => Inv sink1 ⦄ := by
            unfold decoder_v1.decode_update_v1_loop
            let inv : S × Std.Usize × decoder_v1.DecodeAcc × alloc.vec.Vec decoder_v1.WireId ×
                alloc.vec.Vec decoder_v1.WireId × Std.Usize × Option CodecError → Prop :=
              fun (sink1, _, _, _, _, cIdx, _) => Inv sink1 ∧ cIdx.val ≤ val1.val
            refine loop.spec_decr_nat
              (fun (_, _, _, _, _, cIdx, err) => errFlag err + (val1.val - cIdx.val))
              inv _ _
              (sink0, clients_start, { structs := 0#usize, entries := 0#usize, content_bytes := 0#usize },
                alloc.vec.Vec.new decoder_v1.WireId, alloc.vec.Vec.new decoder_v1.WireId, 0#usize, none) ?_
              ⟨hSink0, by scalar_tac⟩
            intro ⟨sink1, cur1, acc1, skippedOls1, pendingZeros1, cIdx, err1⟩ ⟨hInv1, hcLe⟩
            unfold decoder_v1.decode_update_v1_loop.body
            dsimp only
            split_ifs with hlt hnone
            · have herr : err1 = none := (is_none_eq_true_iff err1).1 hnone
              subst herr
              step with decode_one_client_block_spec V Inv input hV cur1
                ⟨limits.max_structs, limits.max_clients, limits.max_collection_entries,
                  limits.max_any_depth, limits.max_content_bytes⟩
                acc1 sink1 hInv1 as ⟨rBlock, sink2, hInv2⟩
              cases rBlock with
              | Ok p =>
                rcases p with ⟨nc, na, cols, cz⟩
                dsimp only
                step as ⟨b1, _⟩
                have hExt1 :
                    (if b1 = true then ok skippedOls1
                     else decoder_v1.extend_wire_ids skippedOls1 (alloc.vec.Vec.deref cols)) ⦃ _ => True ⦄ := by
                  by_cases hb1 : b1 = true
                  · simp only [hb1, ↓reduceIte, spec_ok]
                  · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
                    exact extend_wire_ids_total skippedOls1 (alloc.vec.Vec.deref cols)
                step with hExt1 as ⟨ols2⟩
                step as ⟨b2, _⟩
                have hExt2 :
                    (if b2 = true then ok pendingZeros1
                     else decoder_v1.extend_wire_ids pendingZeros1 (alloc.vec.Vec.deref cz)) ⦃ _ => True ⦄ := by
                  by_cases hb2 : b2 = true
                  · simp only [hb2, ↓reduceIte, spec_ok]
                  · simp only [hb2, Bool.false_eq_true, ↓reduceIte]
                    exact extend_wire_ids_total pendingZeros1 (alloc.vec.Vec.deref cz)
                step with hExt2 as ⟨pz2⟩
                step as ⟨cIdx1, hcIdx1⟩
                try simp only [spec_ok]
                exact ⟨⟨hInv2, by scalar_tac⟩, by simp [hcIdx1]; scalar_tac⟩
              | Err e =>
                try simp only [spec_ok]
                exact ⟨⟨hInv2, hcLe⟩, by simp⟩
            · simp [spec_ok, hInv1]
            · simp [spec_ok, hInv1]
          step with hLoop as ⟨sink1, ds_start, acc1, skippedOls, pendingZeros, err, hInv1⟩
          cases err with
          | none =>
            step with decode_delete_set_v1_spec V Inv input hV ds_start limits acc1.entries sink1 hInv1
              as ⟨r3, sink2, hInv2, hNxt2⟩
            cases r3 with
            | Ok val2 =>
              simp only [core_ops_try_branch_ok, bind_ok]
              dsimp only at hNxt2
              split_ifs
              · step as ⟨rem, _⟩
                step with fail_with_spec V Inv input hV sink2 CodecError.TrailingBytes rem 0#u64 hInv2
                  as ⟨ce, sink3, hInv3⟩
                simp [spec_ok, hInv3]
              · step as ⟨b, _⟩
                by_cases hb : b = true
                · simp only [hb, ↓reduceIte, spec_ok]
                  exact hInv2
                · simp only [hb, Bool.false_eq_true, ↓reduceIte, lift, bind_ok, alloc.vec.Vec.deref_mut]
                  step with verify_skipped_zero_items_total input clients_start val1 ds_start limits _ _ as ⟨r4, _, _⟩
                  cases r4 with
                  | Ok _ =>
                    simp [spec_ok, hInv2]
                  | Err e =>
                    step with fail_with_spec V Inv input hV sink2 e 0#usize 0#u64 hInv2
                      as ⟨ce, sink3, hInv3⟩
                    simp [spec_ok, hInv3]
            | Err e =>
              simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]
              exact hInv2
          | some e =>
            simp [spec_ok, hInv1]
        | Err e =>
          simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
          (try dsimp); exact hSink0
    | Err e =>
      simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
      (try dsimp); exact hSink_a
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
    (try dsimp); exact hSink_a

theorem decode_update_v1_total
    {S : Type _} (V : decoder_v1.V1Sink S) (Inv : S → Prop)
    (input : Slice Std.U8) (hV : V1SinkTotal V Inv)
    (sink : S) (hSink : Inv sink) (limits : decoder_v1.DecodeLimitsCore) :
    decoder_v1.decode_update_v1 V input sink limits ⦃ (_, sink') => Inv sink' ⦄ :=
  decode_update_v1_spec V Inv input (hV.toSpanSafe input) sink hSink limits

@[local step]
theorem find_u64_index_spec (items : Slice Std.U64) (target : Std.U64) :
    decoder_v1.find_u64_index items target ⦃ p =>
      p.2.val ≤ items.length ∧ (p.1 = true → p.2.val < items.length) ⦄ := by
  unfold decoder_v1.find_u64_index
  unfold decoder_v1.find_u64_index_loop
  refine loop.spec_decr_nat
    (fun (low, high) => high.val - low.val)
    (fun (low, high) => low.val ≤ high.val ∧ high.val ≤ items.length)
    (fun (p : Bool × Std.Usize) => p.2.val ≤ items.length ∧ (p.1 = true → p.2.val < items.length))
    _ (0#usize, Slice.len items) ?_ ⟨by scalar_tac, by scalar_tac⟩
  intro ⟨low, high⟩ ⟨hLoHi, hHiLen⟩
  unfold decoder_v1.find_u64_index_loop.body
  dsimp only
  split_ifs with hlt
  · step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    step as ⟨mid, hmid⟩
    have hMidLt : mid.val < items.length := by scalar_tac
    step as ⟨c, hc⟩
    split_ifs with heq hclt
    · simp only [spec_ok]
      exact ⟨by omega, fun _ => hMidLt⟩
    · step as ⟨low1, hlow1⟩
      try simp only [spec_ok]
      exact ⟨by scalar_tac, hHiLen, by scalar_tac⟩
    · try simp only [spec_ok]
      exact ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
  · simp only [spec_ok]
    exact ⟨by omega, fun h => by contradiction⟩

@[local step]
theorem insert_u64_sorted_spec
    (items : alloc.vec.Vec Std.U64) (target : Std.U64)
    (hCap : items.length < Std.Usize.max) :
    decoder_v1.insert_u64_sorted items target ⦃ _ => True ⦄ := by
  unfold decoder_v1.insert_u64_sorted
  step with find_u64_index_spec (alloc.vec.Vec.deref items) target as ⟨found, idx, hIdxLe, hFound⟩
  simp only [alloc.vec.Vec.deref, Slice.length] at hIdxLe hFound
  split_ifs with hf heq
  · simp [spec_ok]
  · step*
  · step*

theorem summary_sink_v1sink_total :
    V1SinkTotal decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink (fun _ => True) :=
  { core_validates_utf8 := by
      intro s
      simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink,
        decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.core_validates_utf8, spec_ok]
    validate_utf8_early := by
      intro s _ _ _
      simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink,
        decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.validate_utf8_early, spec_ok]
    on_decode_error := by
      intro s _ _ _ _
      simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink,
        decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_decode_error, spec_ok]
    record_client := by
      intro s client _
      simp only [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink]
      unfold decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.record_client
      dsimp only
      split_ifs with hmax
      · simp [spec_ok]
      · have hCap : s.seen_clients.length < Std.Usize.max := by
          simp only [alloc.vec.Vec.len] at hmax
          scalar_tac
        step with insert_u64_sorted_spec s.seen_clients client hCap as ⟨b, v⟩
    begin_client := by
      intro s _ _ _
      simp only [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink]
      unfold decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.begin_client
      dsimp only; split_ifs <;> step*
    on_gc := by
      intro s _ _ _
      simp only [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink]
      unfold decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_gc
      dsimp only; split_ifs <;> step*
    on_skip := by
      intro s _ _ _
      simp only [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink]
      unfold decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_skip
      dsimp only; split_ifs <;> step*
    on_item := by
      intro s _ _ _ _
      simp only [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink]
      unfold decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_item
      dsimp only; split_ifs <;> step*
    on_skipped_zero_origin := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_skipped_zero_origin, spec_ok]
    on_deleted := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_deleted, spec_ok]
    on_json_start := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_json_start, spec_ok]
    on_json_value := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_json_value, spec_ok]
    on_json_finish := by
      intro s _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_json_finish, spec_ok]
    on_binary := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_binary, spec_ok]
    on_string := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_string, spec_ok]
    on_embed := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_embed, spec_ok]
    on_format := by
      intro s _ _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_format, spec_ok]
    on_type := by
      intro s _ _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_type, spec_ok]
    on_any_content_start := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_content_start, spec_ok]
    on_any_content_value := by
      intro s _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_content_value, spec_ok]
    on_any_content_finish := by
      intro s _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_content_finish, spec_ok]
    on_doc := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_doc, spec_ok]
    on_any_start := by
      intro s _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_start, spec_ok]
    on_any_undefined := by
      intro s _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_undefined, spec_ok]
    on_any_null := by
      intro s _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_null, spec_ok]
    on_any_i32 := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_i32, spec_ok]
    on_any_f32_bits := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_f32_bits, spec_ok]
    on_any_f64_bits := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_f64_bits, spec_ok]
    on_any_i64_bits := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_i64_bits, spec_ok]
    on_any_bool := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_bool, spec_ok]
    on_any_str := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_str, spec_ok]
    on_any_bytes := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_bytes, spec_ok]
    on_any_begin_object := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_begin_object, spec_ok]
    on_any_object_key := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_object_key, spec_ok]
    on_any_begin_array := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_begin_array, spec_ok]
    on_any_end_container := by
      intro s _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_end_container, spec_ok]
    on_any_finish := by
      intro s _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_any_finish, spec_ok]
    begin_delete_client := by
      intro s _ count _
      simp only [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink]
      unfold decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.begin_delete_client
      dsimp only
      split_ifs with hmax
      · simp [spec_ok]
      · step as ⟨i, hi⟩
        step with checked_add_usize_total s.summary.delete_ranges count as ⟨r⟩
        cases r with
        | Ok _ => simp only [core_ops_try_branch_ok, bind_ok, spec_ok, Aeneas.Std.uncurry]
        | Err _ => simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok, Aeneas.Std.uncurry]
    on_delete_range := by
      intro s _ _ _ _; simp [decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink, decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink.on_delete_range, spec_ok] }

theorem decode_update_v1_frame_total
    (input : Slice Std.U8) (limits : decoder_v1.DecodeLimitsCore) :
    decoder_v1.decode_update_v1_frame input limits ⦃ _ => True ⦄ := by
  unfold decoder_v1.decode_update_v1_frame
  unfold decoder_v1.SummarySink.new
  step*
  step with decode_update_v1_total decoder_v1.SummarySink.Insts.Y_octo_coreDecoder_v1V1Sink
    (fun _ => True) input summary_sink_v1sink_total _ trivial limits as ⟨r, sink1⟩
  cases r with
  | Ok _ =>
    simp only [core_ops_try_branch_ok, bind_ok, spec_ok]
  | Err e =>
    simp only [core_ops_try_branch_err, bind_ok, core_ops_try_from_residual_err, spec_ok]

end YoctoCore.Properties.DecoderV1
