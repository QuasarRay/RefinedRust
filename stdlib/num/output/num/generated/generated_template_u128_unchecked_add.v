From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.num.num Require Export generated_code_num generated_specs_num.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition u128_unchecked_add_lemma (π : thread_id) : Prop :=
  ⊢ typed_function π (u128_unchecked_add_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u128_unchecked_add -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_u128_unchecked_add-[] -[]) π))).
End proof.

Ltac u128_unchecked_add_prelude :=
  unfold u128_unchecked_add_lemma;
  set (FN_NAME := FUNCTION_NAME "u128_unchecked_add");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let x := fresh "x" in
  let rhs := fresh "rhs" in
  start_function "u128_unchecked_add" ϝ fid ( [] ) ( [] ) ( [  x rhs ] ) ( x rhs );
  intros arg_x arg_rhs;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
