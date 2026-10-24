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
Definition raw_vec_implRawVecInnerA_shrink_unchecked_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(A_st : !syn_type) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveErrorKind_closuresrcraw_vecrs7182571828_loc : loc) (allocation_deallocate_raw_A_loc : loc) (allocation_shrink_raw_A_loc : loc) (layout_Layout_align_loc : loc) (layout_Layout_from_size_align_unchecked_loc : loc) (layout_Layout_size_loc : loc) (raw_vec_implRawVecInnerA_current_memory_A_loc : loc) (raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc : loc) (std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveErrorKind_loc : loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc : loc) (unique_Unique_T_new_unchecked_u8_loc : loc) (usize_unchecked_mul_loc : loc) (without_provenance_mut_u8_loc : loc) (Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveErrorKind_closuresrcraw_vecrs7182571828_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (allocation_deallocate_raw_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (allocation_shrink_raw_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (layout_Layout_align_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (layout_Layout_from_size_align_unchecked_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (layout_Layout_size_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_current_memory_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (unique_Unique_T_new_unchecked_u8_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (usize_unchecked_mul_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (without_provenance_mut_u8_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable ((errors_AllocError_sls : syn_type)) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_els : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType)) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType)) : syn_type)) →
  syn_type_is_layoutable (((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) →
  syn_type_is_layoutable (((unique_Unique_sls ((IntSynType U8))) : syn_type)) →
  syn_type_is_layoutable (((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els (PtrSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls (A_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple1_sls (RefSynType)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)) →
  Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveErrorKind_closuresrcraw_vecrs7182571828_loc ◁ᵥ{π, MetaNone} Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveErrorKind_closuresrcraw_vecrs7182571828_loc @ function_ptr [((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type); ((tuple1_sls (RefSynType)) : syn_type)] (<tag_type> spec! ( *[vlft13]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_Result_TE_map_err (RRGS:=RRGS) (loc) ((((errors_AllocError_inv_t_rt)))) ((((errors_TryReserveErrorKind_rt)))) ((((tuple1_rt) ((place_rfnRT (((layout_Layout_inv_t_rt)))))))) (PtrSynType) ((errors_AllocError_sls : syn_type)) ((errors_TryReserveErrorKind_els : syn_type)) (((tuple1_sls (RefSynType)) : syn_type)) (drop_glue_trivial_spec_attrs (loc)) (drop_glue_trivial_spec_attrs ((((errors_AllocError_inv_t_rt))))) (raw_vec_implRawVecInnerA_shrink_unchecked_closure0_FnOnce_spec_attrs ((A_rt)) (Allocator_A_spec_attrs) (DropGlue_A_spec_attrs)) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (drop_glue_tuple1_spec_attrs ((place_rfnRT (((layout_Layout_inv_t_rt))))) ((drop_glue_trivial_spec_attrs ((place_rfnRT (((layout_Layout_inv_t_rt)))))))) -[] -[alias_ptr_t; (errors_AllocError_inv_t  -[] -[]); (errors_TryReserveErrorKind_ty  -[] -[]); (tuple1_ty ((place_rfnRT (((layout_Layout_inv_t_rt))))) -[] -[(shr_ref vlft13 (layout_Layout_inv_t  -[] -[]))])]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveErrorKind_closuresrcraw_vecrs7182571828_loc_linking -[vlft13] -[A_ty] π)))%I) -∗
  allocation_deallocate_raw_A_loc ◁ᵥ{π, MetaNone} allocation_deallocate_raw_A_loc @ function_ptr [RefSynType; ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type); (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_allocation_deallocate_raw (RRGS:=RRGS) ((A_rt)) (A_st) Allocator_A_spec_attrs DropGlue_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (allocation_deallocate_raw_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  allocation_shrink_raw_A_loc ◁ᵥ{π, MetaNone} allocation_shrink_raw_A_loc @ function_ptr [RefSynType; ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type); (layout_Layout_sls : syn_type); (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_allocation_shrink_raw (RRGS:=RRGS) ((A_rt)) (A_st) Allocator_A_spec_attrs DropGlue_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (allocation_shrink_raw_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  layout_Layout_align_loc ◁ᵥ{π, MetaNone} layout_Layout_align_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_align (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_align_loc_linking -[late_lft_0] -[] π)))%I) -∗
  layout_Layout_from_size_align_unchecked_loc ◁ᵥ{π, MetaNone} layout_Layout_from_size_align_unchecked_loc @ function_ptr [(IntSynType USize); (IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_from_size_align_unchecked (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (layout_Layout_from_size_align_unchecked_loc_linking -[] -[] π)))%I) -∗
  layout_Layout_size_loc ◁ᵥ{π, MetaNone} layout_Layout_size_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_size (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_size_loc_linking -[late_lft_0] -[] π)))%I) -∗
  raw_vec_implRawVecInnerA_current_memory_A_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_current_memory_A_loc @ function_ptr [RefSynType; (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_current_memory (RRGS:=RRGS) ((A_rt)) (A_st) DropGlue_A_spec_attrs Allocator_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (raw_vec_implRawVecInnerA_current_memory_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc @ function_ptr [RefSynType; PtrSynType; (IntSynType USize)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_set_ptr_and_cap (RRGS:=RRGS) ((A_rt)) (A_st) DropGlue_A_spec_attrs Allocator_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveErrorKind_loc ◁ᵥ{π, MetaNone} std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveErrorKind_loc @ function_ptr [((Result_els (PtrSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let realization := (std_result_ResultTEasTry_realization loc (((errors_TryReserveErrorKind_rt))) PtrSynType (errors_TryReserveErrorKind_els : syn_type) (drop_glue_trivial_spec_attrs (loc)) (trait_spec_realization_instantiate (drop_glue_trivial_realization loc PtrSynType) -[] -[alias_ptr_t]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])])) in fn_spec_add_late_pre ((Try_branch_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[alias_ptr_t; (errors_TryReserveErrorKind_ty  -[] -[])] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[alias_ptr_t; (errors_TryReserveErrorKind_ty  -[] -[])] π))%I) -∗
  std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc ◁ᵥ{π, MetaNone} std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc @ function_ptr [((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let realization := (std_result_ResultTFasFromResidualstd_result_ResultE_realization unit (((errors_TryReserveErrorKind_rt))) (((errors_TryReserveError_inv_t_rt))) UnitSynType (errors_TryReserveErrorKind_els : syn_type) (errors_TryReserveError_sls : syn_type) errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_spec_attrs (trait_spec_realization_instantiate (errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_realization) -[] -[]) (drop_glue_trivial_spec_attrs (unit)) (trait_spec_realization_instantiate (drop_glue_trivial_realization unit UnitSynType) -[] -[unit_t]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in fn_spec_add_late_pre ((FromResidual_from_residual_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[unit_t; (errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[unit_t; (errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))%I) -∗
  unique_Unique_T_new_unchecked_u8_loc ◁ᵥ{π, MetaNone} unique_Unique_T_new_unchecked_u8_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_unique_Unique_T_new_unchecked (RRGS:=RRGS) (Z) ((IntSynType U8)) (drop_glue_trivial_spec_attrs (Z)) -[] -[(int U8)]) (λ π, (from_assumption_hint (unique_Unique_T_new_unchecked_u8_loc_linking -[] -[] π)))%I) -∗
  usize_unchecked_mul_loc ◁ᵥ{π, MetaNone} usize_unchecked_mul_loc @ function_ptr [(IntSynType USize); (IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_usize_unchecked_mul (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (usize_unchecked_mul_loc_linking -[] -[] π)))%I) -∗
  without_provenance_mut_u8_loc ◁ᵥ{π, MetaNone} without_provenance_mut_u8_loc @ function_ptr [(IntSynType USize)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_without_provenance_mut (RRGS:=RRGS) (Z) ((IntSynType U8)) (drop_glue_trivial_spec_attrs (Z)) -[] -[(int U8)]) (λ π, (from_assumption_hint (without_provenance_mut_u8_loc_linking -[] -[] π)))%I) -∗
  typed_function π (raw_vec_implRawVecInnerA_shrink_unchecked_def Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveErrorKind_closuresrcraw_vecrs7182571828_loc  allocation_deallocate_raw_A_loc  allocation_shrink_raw_A_loc  layout_Layout_align_loc  layout_Layout_from_size_align_unchecked_loc  layout_Layout_size_loc  raw_vec_implRawVecInnerA_current_memory_A_loc  raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc  std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveErrorKind_loc  std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc  unique_Unique_T_new_unchecked_u8_loc  usize_unchecked_mul_loc  without_provenance_mut_u8_loc  A_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_shrink_unchecked A_rt A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs -[ulft_1] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_raw_vec_implRawVecInnerA_shrink_unchecked (A_rt) (A_st) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (Allocator_A_spec_attrs) (Allocator_A_realization))-[ulft_1] -[A_ty]) π)
  ∗ ((introduce_direct ((let realization := (std_result_ResultTEasTry_realization loc (((errors_TryReserveErrorKind_rt))) PtrSynType (errors_TryReserveErrorKind_els : syn_type) (drop_glue_trivial_spec_attrs (loc)) (trait_spec_realization_instantiate (drop_glue_trivial_realization loc PtrSynType) -[] -[alias_ptr_t]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])])) in realization.(trait_ctx_wf) -[] -[alias_ptr_t; (errors_TryReserveErrorKind_ty  -[] -[])] π))))
  ∗ ((introduce_direct ((let realization := (std_result_ResultTFasFromResidualstd_result_ResultE_realization unit (((errors_TryReserveErrorKind_rt))) (((errors_TryReserveError_inv_t_rt))) UnitSynType (errors_TryReserveErrorKind_els : syn_type) (errors_TryReserveError_sls : syn_type) errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_spec_attrs (trait_spec_realization_instantiate (errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_realization) -[] -[]) (drop_glue_trivial_spec_attrs (unit)) (trait_spec_realization_instantiate (drop_glue_trivial_realization unit UnitSynType) -[] -[unit_t]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in realization.(trait_ctx_wf) -[] -[unit_t; (errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))))
  ∗ (□ (∀ (vlft13 : lft), Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveErrorKind_closuresrcraw_vecrs7182571828_loc_linking -[vlft13] -[A_ty] π))
  ∗ (□ (∀ (late_lft_0 : lft), allocation_deallocate_raw_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (∀ (late_lft_0 : lft), allocation_shrink_raw_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_align_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (layout_Layout_from_size_align_unchecked_loc_linking -[] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_size_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), raw_vec_implRawVecInnerA_current_memory_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (∀ (late_lft_0 : lft), raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (unique_Unique_T_new_unchecked_u8_loc_linking -[] -[] π))
  ∗ (□ (usize_unchecked_mul_loc_linking -[] -[] π))
  ∗ (□ (without_provenance_mut_u8_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_implRawVecInnerA_shrink_unchecked_prelude :=
  unfold raw_vec_implRawVecInnerA_shrink_unchecked_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecInnerA_shrink_unchecked");
  intros A_rt A_st DropGlue_A_spec_attrs DropGlue_A_realization Allocator_A_spec_attrs Allocator_A_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let A_ty := fresh "A_ty" in
  let v := fresh "v" in
  let self := fresh "self" in
  let cap := fresh "cap" in
  let elem_layout := fresh "elem_layout" in
  start_function "raw_vec_implRawVecInnerA_shrink_unchecked" ϝ fid ( [ulft_1 [] ] ) ( [A_ty [] ] ) ( [ [ [  v self ] cap ] elem_layout ] ) ( v self cap elem_layout );
  intros arg_self arg_cap arg_elem_layout;
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
