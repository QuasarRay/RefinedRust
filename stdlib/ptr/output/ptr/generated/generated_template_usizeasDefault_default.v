From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.theories Require Export alignment shims specs.
From rrstd.ptr.ptr Require Export generated_code_ptr generated_specs_ptr.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition usizeasDefault_default_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (usizeasDefault_default_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_usizeasDefault_default -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_usizeasDefault_default-[] -[]) π))).
End proof.

Ltac usizeasDefault_default_prelude :=
  unfold usizeasDefault_default_lemma;
  set (FN_NAME := FUNCTION_NAME "usizeasDefault_default");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  start_function "usizeasDefault_default" ϝ fid ( [] ) ( [] ) ( ? );
  intros;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
