From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.theories Require Export errors layout shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.result.result.generated Require Export generated_specs_result.
From rrstd.alloc.alloc Require Export generated_code_alloc generated_specs_alloc.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable ((layout_LayoutError_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_els : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_CapacityOverflow_sls : syn_type)) →
  ⊢ typed_function π (errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from-[] -[]) π))).
End proof.

Ltac errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from_prelude :=
  unfold errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from_lemma;
  set (FN_NAME := FUNCTION_NAME "errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  start_function "errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from" ϝ fid ( [] ) ( [] ) ( ? );
  intros arg___1;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
