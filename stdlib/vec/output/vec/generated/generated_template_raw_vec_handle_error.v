From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.cmp.generated Require Export generated_specs_cmp.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.index.index.generated Require Export generated_specs_index.
From rrstd.iterator.iterator.generated Require Export generated_specs_iterator.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.vec.theories Require Export allocation vec.
From rrstd.vec.vec Require Export generated_code_vec generated_specs_vec.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition raw_vec_handle_error_lemma (π : thread_id) : Prop :=
  ∀ (errors_TryReserveError_kind_loc : loc) (handle_alloc_error_loc : loc) (raw_vec_capacity_overflow_loc : loc) (errors_TryReserveError_kind_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (handle_alloc_error_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (raw_vec_capacity_overflow_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_els : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_AllocError_sls : syn_type)) →
  errors_TryReserveError_kind_loc ◁ᵥ{π, MetaNone} errors_TryReserveError_kind_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_errors_TryReserveError_kind (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (errors_TryReserveError_kind_loc_linking -[late_lft_0] -[] π)))%I) -∗
  handle_alloc_error_loc ◁ᵥ{π, MetaNone} handle_alloc_error_loc @ function_ptr [(layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_handle_alloc_error (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (handle_alloc_error_loc_linking -[] -[] π)))%I) -∗
  raw_vec_capacity_overflow_loc ◁ᵥ{π, MetaNone} raw_vec_capacity_overflow_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_capacity_overflow (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (raw_vec_capacity_overflow_loc_linking -[] -[] π)))%I) -∗
  typed_function π (raw_vec_handle_error_def errors_TryReserveError_kind_loc  handle_alloc_error_loc  raw_vec_capacity_overflow_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_handle_error -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_raw_vec_handle_error-[] -[]) π)
  ∗ (□ (∀ (late_lft_0 : lft), errors_TryReserveError_kind_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (handle_alloc_error_loc_linking -[] -[] π))
  ∗ (□ (raw_vec_capacity_overflow_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_handle_error_prelude :=
  unfold raw_vec_handle_error_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_handle_error");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let e := fresh "e" in
  start_function "raw_vec_handle_error" ϝ fid ( [] ) ( [] ) (  e ) ( e );
  intros arg_e;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
