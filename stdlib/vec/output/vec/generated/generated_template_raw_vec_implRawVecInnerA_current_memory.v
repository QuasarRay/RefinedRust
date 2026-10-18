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
Definition raw_vec_implRawVecInnerA_current_memory_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(A_st : !syn_type) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (Tasconvert_IntoU_into_std_ptr_Uniqueu8_std_ptr_NonNullu8_loc : loc) (layout_Layout_align_loc : loc) (layout_Layout_from_size_align_unchecked_loc : loc) (layout_Layout_size_loc : loc) (usize_unchecked_mul_loc : loc) (layout_Layout_align_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (layout_Layout_from_size_align_unchecked_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (layout_Layout_size_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (usize_unchecked_mul_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable (((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Option_None_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) →
  syn_type_is_layoutable (((unique_Unique_sls ((IntSynType U8))) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls (A_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)) →
  Tasconvert_IntoU_into_std_ptr_Uniqueu8_std_ptr_NonNullu8_loc ◁ᵥ{π, MetaNone} Tasconvert_IntoU_into_std_ptr_Uniqueu8_std_ptr_NonNullu8_loc @ function_ptr [((unique_Unique_sls ((IntSynType U8))) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let realization := (Tasconvert_IntoU_realization ((((unique_Unique_inv_t_rt)) (Z))) ((((nonnull_NonNull_inv_t_rt)) (Z))) ((unique_Unique_sls ((IntSynType U8))) : syn_type) ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) (nonnull_NonNullTasstd_convert_Fromunique_UniqueT_spec_attrs (Z) ((drop_glue_trivial_spec_attrs (Z)))) (trait_spec_realization_instantiate (nonnull_NonNullTasstd_convert_Fromunique_UniqueT_realization Z (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (trait_spec_realization_instantiate (drop_glue_trivial_realization Z (IntSynType U8)) -[] -[(int U8)])) -[] -[(int U8)]) (drop_glue_trivial_spec_attrs (((((unique_Unique_inv_t_rt)) (Z))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization ((((unique_Unique_inv_t_rt)) (Z))) ((unique_Unique_sls ((IntSynType U8))) : syn_type)) -[] -[(unique_Unique_inv_t (Z) -[] -[(int U8)])]) (drop_glue_trivial_spec_attrs (((((nonnull_NonNull_inv_t_rt)) (Z))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization ((((nonnull_NonNull_inv_t_rt)) (Z))) ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) -[] -[(nonnull_NonNull_inv_t (Z) -[] -[(int U8)])])) in fn_spec_add_late_pre ((convert_Into_into_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[(unique_Unique_inv_t (Z) -[] -[(int U8)]); (nonnull_NonNull_inv_t (Z) -[] -[(int U8)])] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[(unique_Unique_inv_t (Z) -[] -[(int U8)]); (nonnull_NonNull_inv_t (Z) -[] -[(int U8)])] π))%I) -∗
  layout_Layout_align_loc ◁ᵥ{π, MetaNone} layout_Layout_align_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_align (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_align_loc_linking -[late_lft_0] -[] π)))%I) -∗
  layout_Layout_from_size_align_unchecked_loc ◁ᵥ{π, MetaNone} layout_Layout_from_size_align_unchecked_loc @ function_ptr [(IntSynType USize); (IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_from_size_align_unchecked (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (layout_Layout_from_size_align_unchecked_loc_linking -[] -[] π)))%I) -∗
  layout_Layout_size_loc ◁ᵥ{π, MetaNone} layout_Layout_size_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_size (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_size_loc_linking -[late_lft_0] -[] π)))%I) -∗
  usize_unchecked_mul_loc ◁ᵥ{π, MetaNone} usize_unchecked_mul_loc @ function_ptr [(IntSynType USize); (IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_usize_unchecked_mul (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (usize_unchecked_mul_loc_linking -[] -[] π)))%I) -∗
  typed_function π (raw_vec_implRawVecInnerA_current_memory_def Tasconvert_IntoU_into_std_ptr_Uniqueu8_std_ptr_NonNullu8_loc  layout_Layout_align_loc  layout_Layout_from_size_align_unchecked_loc  layout_Layout_size_loc  usize_unchecked_mul_loc  A_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_current_memory A_rt A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs -[ulft_1] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_raw_vec_implRawVecInnerA_current_memory (A_rt) (A_st) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (Allocator_A_spec_attrs) (Allocator_A_realization))-[ulft_1] -[A_ty]) π)
  ∗ ((introduce_direct ((let realization := (Tasconvert_IntoU_realization ((((unique_Unique_inv_t_rt)) (Z))) ((((nonnull_NonNull_inv_t_rt)) (Z))) ((unique_Unique_sls ((IntSynType U8))) : syn_type) ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) (nonnull_NonNullTasstd_convert_Fromunique_UniqueT_spec_attrs (Z) ((drop_glue_trivial_spec_attrs (Z)))) (trait_spec_realization_instantiate (nonnull_NonNullTasstd_convert_Fromunique_UniqueT_realization Z (IntSynType U8) (drop_glue_trivial_spec_attrs (Z)) (trait_spec_realization_instantiate (drop_glue_trivial_realization Z (IntSynType U8)) -[] -[(int U8)])) -[] -[(int U8)]) (drop_glue_trivial_spec_attrs (((((unique_Unique_inv_t_rt)) (Z))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization ((((unique_Unique_inv_t_rt)) (Z))) ((unique_Unique_sls ((IntSynType U8))) : syn_type)) -[] -[(unique_Unique_inv_t (Z) -[] -[(int U8)])]) (drop_glue_trivial_spec_attrs (((((nonnull_NonNull_inv_t_rt)) (Z))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization ((((nonnull_NonNull_inv_t_rt)) (Z))) ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) -[] -[(nonnull_NonNull_inv_t (Z) -[] -[(int U8)])])) in realization.(trait_ctx_wf) -[] -[(unique_Unique_inv_t (Z) -[] -[(int U8)]); (nonnull_NonNull_inv_t (Z) -[] -[(int U8)])] π))))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_align_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (layout_Layout_from_size_align_unchecked_loc_linking -[] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_size_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (usize_unchecked_mul_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_implRawVecInnerA_current_memory_prelude :=
  unfold raw_vec_implRawVecInnerA_current_memory_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecInnerA_current_memory");
  intros A_rt A_st DropGlue_A_spec_attrs DropGlue_A_realization Allocator_A_spec_attrs Allocator_A_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let A_ty := fresh "A_ty" in
  let self := fresh "self" in
  let elem_layout := fresh "elem_layout" in
  start_function "raw_vec_implRawVecInnerA_current_memory" ϝ fid ( [ulft_1 [] ] ) ( [A_ty [] ] ) ( [  self elem_layout ] ) ( self elem_layout );
  intros arg_self arg_elem_layout;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("ulft_1", ulft_1) :: ("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
