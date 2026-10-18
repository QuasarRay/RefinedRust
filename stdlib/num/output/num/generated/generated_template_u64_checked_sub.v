From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.num.num Require Export generated_code_num generated_specs_num.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.
Definition u64_checked_sub_lemma (π : thread_id) : Prop :=
  ∀ (u64_unchecked_sub_loc : loc) (u64_unchecked_sub_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (((Option_els ((IntSynType U64))) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls ((IntSynType U64))) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls ((IntSynType U64))) : syn_type)) →
  u64_unchecked_sub_loc ◁ᵥ{π, MetaNone} u64_unchecked_sub_loc @ function_ptr [(IntSynType U64); (IntSynType U64)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u64_unchecked_sub (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (u64_unchecked_sub_loc_linking -[] -[] π)))%I) -∗
  typed_function π (u64_checked_sub_def u64_unchecked_sub_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_u64_checked_sub -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_u64_checked_sub-[] -[]) π)
  ∗ (□ (u64_unchecked_sub_loc_linking -[] -[] π)))).
End proof.

Ltac u64_checked_sub_prelude :=
  unfold u64_checked_sub_lemma;
  set (FN_NAME := FUNCTION_NAME "u64_checked_sub");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let x := fresh "x" in
  let rhs := fresh "rhs" in
  start_function "u64_checked_sub" ϝ fid ( [] ) ( [] ) ( [  x rhs ] ) ( x rhs );
  intros arg_x arg_rhs;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
