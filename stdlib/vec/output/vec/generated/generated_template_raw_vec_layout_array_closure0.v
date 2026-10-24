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
Definition raw_vec_layout_array_closure0_lemma (π : thread_id) : Prop :=
  ∀ (Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc : loc) , 
  syn_type_is_layoutable ((layout_LayoutError_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_els : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_CapacityOverflow_sls : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls ((layout_LayoutError_sls : syn_type))) : syn_type)) →
  Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc ◁ᵥ{π, MetaNone} Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc @ function_ptr [(errors_TryReserveErrorKind_els : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let realization := (Tasconvert_IntoU_realization (((errors_TryReserveErrorKind_rt))) (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveErrorKind_els : syn_type) (errors_TryReserveError_sls : syn_type) errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_spec_attrs (trait_spec_realization_instantiate (errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_realization) -[] -[]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in fn_spec_add_late_pre ((convert_Into_into_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[(errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[(errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))%I) -∗
  typed_function π (raw_vec_layout_array_closure0_def Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_layout_array_closure0 -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_raw_vec_layout_array_closure0-[] -[]) π)
  ∗ ((introduce_direct ((let realization := (Tasconvert_IntoU_realization (((errors_TryReserveErrorKind_rt))) (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveErrorKind_els : syn_type) (errors_TryReserveError_sls : syn_type) errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_spec_attrs (trait_spec_realization_instantiate (errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_realization) -[] -[]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in realization.(trait_ctx_wf) -[] -[(errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π)))))).
End proof.

Ltac raw_vec_layout_array_closure0_prelude :=
  unfold raw_vec_layout_array_closure0_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_layout_array_closure0");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let _arg_0 := fresh "_arg_0" in
  start_function "raw_vec_layout_array_closure0" ϝ fid ( [] ) ( [] ) (  _arg_0 ) ( _arg_0 );
  intros arg___1 arg___2;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
