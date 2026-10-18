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
Definition raw_vec_implRawVecTA_from_nonnull_in_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_A_drop_glue_loc : loc) (nonnull_NonNull_T_cast_T_u8_loc : loc) (raw_vec_implRawVecInnerA_from_nonnull_in_A_loc : loc) (raw_vec_new_cap_T_loc : loc) (nonnull_NonNull_T_cast_T_u8_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_from_nonnull_in_A_loc_linking : spec_with 0 [A_rt] (thread_id → iProp Σ)) (raw_vec_new_cap_T_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (((core_marker_PhantomData_sls (T_st)) : syn_type)) →
  syn_type_is_layoutable (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) →
  syn_type_is_layoutable (((nonnull_NonNull_sls (T_st)) : syn_type)) →
  syn_type_is_layoutable (((RawVec_sls (T_st) (A_st)) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls (A_st)) : syn_type)) →
  DropGlue_A_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_A_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I)) -∗
  nonnull_NonNull_T_cast_T_u8_loc ◁ᵥ{π, MetaNone} nonnull_NonNull_T_cast_T_u8_loc @ function_ptr [((nonnull_NonNull_sls (T_st)) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_nonnull_NonNull_T_cast (RRGS:=RRGS) ((T_rt)) (Z) (T_st) ((IntSynType U8)) DropGlue_T_spec_attrs (drop_glue_trivial_spec_attrs (Z)) -[] -[T_ty; (int U8)]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (nonnull_NonNull_T_cast_T_u8_loc_linking -[] -[T_ty] π)))%I) -∗
  raw_vec_implRawVecInnerA_from_nonnull_in_A_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_from_nonnull_in_A_loc @ function_ptr [((nonnull_NonNull_sls ((IntSynType U8))) : syn_type); (IntSynType USize); A_st] (<tag_type> spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_from_nonnull_in (RRGS:=RRGS) ((A_rt)) (A_st) DropGlue_A_spec_attrs Allocator_A_spec_attrs -[] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (raw_vec_implRawVecInnerA_from_nonnull_in_A_loc_linking -[] -[A_ty] π)))%I) -∗
  raw_vec_new_cap_T_loc ◁ᵥ{π, MetaNone} raw_vec_new_cap_T_loc @ function_ptr [(IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_new_cap (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (raw_vec_new_cap_T_loc_linking -[] -[T_ty] π)))%I) -∗
  typed_function π (raw_vec_implRawVecTA_from_nonnull_in_def DropGlue_A_drop_glue_loc  nonnull_NonNull_T_cast_T_u8_loc  raw_vec_implRawVecInnerA_from_nonnull_in_A_loc  raw_vec_new_cap_T_loc  T_st  A_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecTA_from_nonnull_in T_rt A_rt T_st A_st DropGlue_T_spec_attrs DropGlue_A_spec_attrs Allocator_A_spec_attrs -[] -[T_ty; A_ty]) (λ π, ((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_raw_vec_implRawVecTA_from_nonnull_in (T_rt) (A_rt) (T_st) (A_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (Allocator_A_spec_attrs) (Allocator_A_realization))-[] -[T_ty; A_ty]) π)
  ∗ (□ (nonnull_NonNull_T_cast_T_u8_loc_linking -[] -[T_ty] π))
  ∗ (□ (raw_vec_implRawVecInnerA_from_nonnull_in_A_loc_linking -[] -[A_ty] π))
  ∗ (□ (raw_vec_new_cap_T_loc_linking -[] -[T_ty] π)))).
End proof.

Ltac raw_vec_implRawVecTA_from_nonnull_in_prelude :=
  unfold raw_vec_implRawVecTA_from_nonnull_in_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecTA_from_nonnull_in");
  intros T_rt A_rt T_st A_st DropGlue_T_spec_attrs DropGlue_T_realization DropGlue_A_spec_attrs DropGlue_A_realization Allocator_A_spec_attrs Allocator_A_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let A_ty := fresh "A_ty" in
  let els := fresh "els" in
  let ptr := fresh "ptr" in
  let capacity := fresh "capacity" in
  let alloc := fresh "alloc" in
  start_function "raw_vec_implRawVecTA_from_nonnull_in" ϝ fid ( [] ) ( [T_ty [A_ty [] ] ] ) ( [ [ [  els ptr ] capacity ] alloc ] ) ( els ptr capacity alloc );
  intros arg_ptr arg_capacity arg_alloc;
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
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
