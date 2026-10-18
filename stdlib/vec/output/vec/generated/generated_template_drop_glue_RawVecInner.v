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
Definition drop_glue_RawVecInner_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_A_drop_glue_loc : loc) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (((RawVecInner_sls (A_st)) : syn_type)) →
  DropGlue_A_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_A_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I)) -∗
  typed_function π (drop_glue_RawVecInner_def DropGlue_A_drop_glue_loc  A_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_RawVecInner A_rt A_st Allocator_A_spec_attrs DropGlue_A_spec_attrs -[] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_drop_glue_RawVecInner (A_rt) (A_st) (Allocator_A_spec_attrs) (Allocator_A_realization) (DropGlue_A_spec_attrs) (DropGlue_A_realization))-[] -[A_ty]) π))).
End proof.

Ltac drop_glue_RawVecInner_prelude :=
  unfold drop_glue_RawVecInner_lemma;
  set (FN_NAME := FUNCTION_NAME "drop_glue_RawVecInner");
  intros A_rt A_st Allocator_A_spec_attrs Allocator_A_realization DropGlue_A_spec_attrs DropGlue_A_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let A_ty := fresh "A_ty" in
  start_function "drop_glue_RawVecInner" ϝ fid ( [] ) ( [A_ty [] ] ) ( ? );
  intros arg_ptr;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
