From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.closures.closures.generated Require Export generated_specs_closures.
From rrstd.cmp.theories Require Export ordering.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.cmp.cmp Require Export generated_code_cmp generated_specs_cmp.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition u16asOrd_max_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (u16asOrd_max_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u16asOrd_max -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_u16asOrd_max-[] -[]) π))).
End proof.

Ltac u16asOrd_max_prelude :=
  unfold u16asOrd_max_lemma;
  set (FN_NAME := FUNCTION_NAME "u16asOrd_max");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  start_function "u16asOrd_max" ϝ fid ( [] ) ( [] ) ( ? );
  intros arg_self arg_other;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl.
