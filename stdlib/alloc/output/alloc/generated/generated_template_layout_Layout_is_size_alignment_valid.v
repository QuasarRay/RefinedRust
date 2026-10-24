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
Definition layout_Layout_is_size_alignment_valid_lemma (π : thread_id) : Prop :=
  ∀ (layout_Layout_max_size_for_alignment_loc : loc) (layout_Layout_max_size_for_alignment_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable ((alignment_Alignment_sls : syn_type)) →
  layout_Layout_max_size_for_alignment_loc ◁ᵥ{π, MetaNone} layout_Layout_max_size_for_alignment_loc @ function_ptr [(alignment_Alignment_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_max_size_for_alignment (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (layout_Layout_max_size_for_alignment_loc_linking -[] -[] π)))%I) -∗
  typed_function π (layout_Layout_is_size_alignment_valid_def layout_Layout_max_size_for_alignment_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_is_size_alignment_valid -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_layout_Layout_is_size_alignment_valid-[] -[]) π)
  ∗ (□ (layout_Layout_max_size_for_alignment_loc_linking -[] -[] π)))).
End proof.

Ltac layout_Layout_is_size_alignment_valid_prelude :=
  unfold layout_Layout_is_size_alignment_valid_lemma;
  set (FN_NAME := FUNCTION_NAME "layout_Layout_is_size_alignment_valid");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let size := fresh "size" in
  let alignment := fresh "alignment" in
  start_function "layout_Layout_is_size_alignment_valid" ϝ fid ( [] ) ( [] ) ( [  size alignment ] ) ( size alignment );
  intros arg_size arg_alignment;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
