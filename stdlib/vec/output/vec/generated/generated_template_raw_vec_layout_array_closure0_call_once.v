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
Definition raw_vec_layout_array_closure0_call_once_lemma (π : thread_id) : Prop :=
  ∀ (raw_vec_layout_array_closure0_loc : loc) (raw_vec_layout_array_closure0_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (UnitSynType) →
  syn_type_is_layoutable (((tuple1_sls ((layout_LayoutError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  raw_vec_layout_array_closure0_loc ◁ᵥ{π, MetaNone} raw_vec_layout_array_closure0_loc @ function_ptr [UnitSynType; (layout_LayoutError_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_layout_array_closure0 (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (raw_vec_layout_array_closure0_loc_linking -[] -[] π)))%I) -∗
  typed_function π (raw_vec_layout_array_closure0_call_once_code raw_vec_layout_array_closure0_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (raw_vec_layout_array_closure0_call_once_spec -[] -[]) (λ π, (True)
  ∗ ((raw_vec_layout_array_closure0_call_once_trait_req_incl-[] -[]) π)
  ∗ (□ (raw_vec_layout_array_closure0_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_layout_array_closure0_call_once_prelude :=
  unfold raw_vec_layout_array_closure0_call_once_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_layout_array_closure0_call_once");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  start_function "raw_vec_layout_array_closure0_call_once" ϝ fid ( [] ) ( [] ) ( ? );
  intros arg_self arg_args;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
