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
Definition drop_glue_RawVec_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (RawVecTAasstd_ops_Drop_drop_T_A_loc : loc) (drop_glue_RawVecInner_A_loc : loc) (RawVecTAasstd_ops_Drop_drop_T_A_loc_linking : spec_with 1 [T_rt; A_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (((RawVec_sls (T_st) (A_st)) : syn_type)) →
  RawVecTAasstd_ops_Drop_drop_T_A_loc ◁ᵥ{π, MetaNone} RawVecTAasstd_ops_Drop_drop_T_A_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), fn_spec_add_late_pre (type_of_RawVecTAasstd_ops_Drop_drop (RRGS:=RRGS) ((T_rt)) ((A_rt)) (T_st) (A_st) Allocator_A_spec_attrs DropGlue_T_spec_attrs DropGlue_A_spec_attrs -[late_lft_0] -[T_ty; A_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (RawVecTAasstd_ops_Drop_drop_T_A_loc_linking -[late_lft_0] -[T_ty; A_ty] π)))%I) -∗
  drop_glue_RawVecInner_A_loc ◁ᵥ{π, MetaNone} drop_glue_RawVecInner_A_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), let realization := (drop_glue_RawVecInner_realization (A_rt) A_st Allocator_A_spec_attrs Allocator_A_realization DropGlue_A_spec_attrs DropGlue_A_realization) in fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[A_ty] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[A_ty] π))%I) -∗
  typed_function π (drop_glue_RawVec_def RawVecTAasstd_ops_Drop_drop_T_A_loc  drop_glue_RawVecInner_A_loc  T_st  A_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), fn_spec_add_late_pre (type_of_drop_glue_RawVec T_rt A_rt T_st A_st Allocator_A_spec_attrs DropGlue_T_spec_attrs DropGlue_A_spec_attrs -[] -[T_ty; A_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_drop_glue_RawVec (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs) (Allocator_A_realization) (DropGlue_T_spec_attrs) (DropGlue_T_realization) (DropGlue_A_spec_attrs) (DropGlue_A_realization))-[] -[T_ty; A_ty]) π)
  ∗ ((introduce_direct ((let realization := (drop_glue_RawVecInner_realization (A_rt) A_st Allocator_A_spec_attrs Allocator_A_realization DropGlue_A_spec_attrs DropGlue_A_realization) in realization.(trait_ctx_wf) -[] -[A_ty] π))))
  ∗ (□ (∀ (late_lft_0 : lft), RawVecTAasstd_ops_Drop_drop_T_A_loc_linking -[late_lft_0] -[T_ty; A_ty] π)))).
End proof.

Ltac drop_glue_RawVec_prelude :=
  unfold drop_glue_RawVec_lemma;
  set (FN_NAME := FUNCTION_NAME "drop_glue_RawVec");
  intros T_rt A_rt T_st A_st Allocator_A_spec_attrs Allocator_A_realization DropGlue_T_spec_attrs DropGlue_T_realization DropGlue_A_spec_attrs DropGlue_A_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let A_ty := fresh "A_ty" in
  start_function "drop_glue_RawVec" ϝ fid ( [] ) ( [T_ty [A_ty [] ] ] ) ( ? );
  intros arg_ptr;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl.
