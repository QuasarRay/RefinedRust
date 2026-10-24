From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.num.num Require Export generated_code_num generated_specs_num.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition usize_checked_mul_lemma (π : thread_id) : Prop :=
  syn_type_is_layoutable (((Option_els ((IntSynType USize))) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls ((IntSynType USize))) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls ((IntSynType USize))) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) →
  ⊢ typed_function π (usize_checked_mul_def ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_usize_checked_mul -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_usize_checked_mul-[] -[]) π))).
End proof.

Ltac usize_checked_mul_prelude :=
  unfold usize_checked_mul_lemma;
  set (FN_NAME := FUNCTION_NAME "usize_checked_mul");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let x := fresh "x" in
  let rhs := fresh "rhs" in
  start_function "usize_checked_mul" ϝ fid ( [] ) ( [] ) ( [  x rhs ] ) ( x rhs );
  intros arg_x arg_rhs;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
