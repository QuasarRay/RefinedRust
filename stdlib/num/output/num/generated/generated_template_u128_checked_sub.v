From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.num.num Require Export generated_code_num generated_specs_num.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition u128_checked_sub_lemma (π : thread_id) : Prop :=
  ∀ (u128_unchecked_sub_loc : loc) (u128_unchecked_sub_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (((Option_els ((IntSynType U128))) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls ((IntSynType U128))) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls ((IntSynType U128))) : syn_type)) →
  u128_unchecked_sub_loc ◁ᵥ{π, MetaNone} u128_unchecked_sub_loc @ function_ptr [(IntSynType U128); (IntSynType U128)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u128_unchecked_sub (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (u128_unchecked_sub_loc_linking -[] -[] π)))%I) -∗
  typed_function π (u128_checked_sub_def u128_unchecked_sub_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u128_checked_sub -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_u128_checked_sub-[] -[]) π)
  ∗ (□ (u128_unchecked_sub_loc_linking -[] -[] π)))).
End proof.

Ltac u128_checked_sub_prelude :=
  unfold u128_checked_sub_lemma;
  set (FN_NAME := FUNCTION_NAME "u128_checked_sub");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let x := fresh "x" in
  let rhs := fresh "rhs" in
  start_function "u128_checked_sub" ϝ fid ( [] ) ( [] ) ( [  x rhs ] ) ( x rhs );
  intros arg_x arg_rhs;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
