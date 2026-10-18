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
Definition layout_Layoutasstd_clone_Clone_clone_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  ⊢ typed_function π (layout_Layoutasstd_clone_Clone_clone_def ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layoutasstd_clone_Clone_clone -[ulft_1] -[]) (λ π, (True)
  ∗ ((trait_incl_of_layout_Layoutasstd_clone_Clone_clone-[ulft_1] -[]) π))).
End proof.

Ltac layout_Layoutasstd_clone_Clone_clone_prelude :=
  unfold layout_Layoutasstd_clone_Clone_clone_lemma;
  set (FN_NAME := FUNCTION_NAME "layout_Layoutasstd_clone_Clone_clone");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  start_function "layout_Layoutasstd_clone_Clone_clone" ϝ fid ( [ulft_1 [] ] ) ( [] ) ( ? );
  intros arg_self;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
