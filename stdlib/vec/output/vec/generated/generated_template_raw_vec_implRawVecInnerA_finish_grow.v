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
Definition raw_vec_implRawVecInnerA_finish_grow_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(A_st : !syn_type) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc : loc) (allocation_allocate_raw_A_loc : loc) (allocation_grow_raw_A_loc : loc) (layout_Layout_align_loc : loc) (panic_shim_loc : loc) (raw_vec_assert_unchecked_loc : loc) (raw_vec_implRawVecInnerA_current_memory_A_loc : loc) (raw_vec_layout_array_loc : loc) (std_result_ResultTEasTry_branch_std_alloc_Layout_std_collections_TryReserveError_loc : loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_mutu8_std_collections_TryReserveError_std_collections_TryReserveError_loc : loc) (allocation_allocate_raw_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (allocation_grow_raw_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (layout_Layout_align_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (panic_shim_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (raw_vec_assert_unchecked_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_current_memory_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (raw_vec_layout_array_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable ((errors_AllocError_sls : syn_type)) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_els : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_AllocError_sls : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_Err_sls (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) →
  syn_type_is_layoutable (((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls (A_st)) : syn_type)) →
  syn_type_is_layoutable (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)) →
  Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc ◁ᵥ{π, MetaNone} Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc @ function_ptr [(errors_TryReserveErrorKind_els : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let realization := (Tasconvert_IntoU_realization (((errors_TryReserveErrorKind_rt))) (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveErrorKind_els : syn_type) (errors_TryReserveError_sls : syn_type) errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_spec_attrs (trait_spec_realization_instantiate (errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_realization) -[] -[]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in fn_spec_add_late_pre ((convert_Into_into_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[(errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[(errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))%I) -∗
  allocation_allocate_raw_A_loc ◁ᵥ{π, MetaNone} allocation_allocate_raw_A_loc @ function_ptr [RefSynType; (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_allocation_allocate_raw (RRGS:=RRGS) ((A_rt)) (A_st) Allocator_A_spec_attrs DropGlue_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (allocation_allocate_raw_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  allocation_grow_raw_A_loc ◁ᵥ{π, MetaNone} allocation_grow_raw_A_loc @ function_ptr [RefSynType; ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type); (layout_Layout_sls : syn_type); (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_allocation_grow_raw (RRGS:=RRGS) ((A_rt)) (A_st) Allocator_A_spec_attrs DropGlue_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (allocation_grow_raw_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  layout_Layout_align_loc ◁ᵥ{π, MetaNone} layout_Layout_align_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_align (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_align_loc_linking -[late_lft_0] -[] π)))%I) -∗
  panic_shim_loc ◁ᵥ{π, MetaNone} panic_shim_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_panic_shim (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (panic_shim_loc_linking -[] -[] π)))%I) -∗
  raw_vec_assert_unchecked_loc ◁ᵥ{π, MetaNone} raw_vec_assert_unchecked_loc @ function_ptr [BoolSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_assert_unchecked (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (raw_vec_assert_unchecked_loc_linking -[] -[] π)))%I) -∗
  raw_vec_implRawVecInnerA_current_memory_A_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_current_memory_A_loc @ function_ptr [RefSynType; (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_current_memory (RRGS:=RRGS) ((A_rt)) (A_st) DropGlue_A_spec_attrs Allocator_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (raw_vec_implRawVecInnerA_current_memory_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  raw_vec_layout_array_loc ◁ᵥ{π, MetaNone} raw_vec_layout_array_loc @ function_ptr [(IntSynType USize); (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_layout_array (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (raw_vec_layout_array_loc_linking -[] -[] π)))%I) -∗
  std_result_ResultTEasTry_branch_std_alloc_Layout_std_collections_TryReserveError_loc ◁ᵥ{π, MetaNone} std_result_ResultTEasTry_branch_std_alloc_Layout_std_collections_TryReserveError_loc @ function_ptr [((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let realization := (std_result_ResultTEasTry_realization (((layout_Layout_inv_t_rt))) (((errors_TryReserveError_inv_t_rt))) (layout_Layout_sls : syn_type) (errors_TryReserveError_sls : syn_type) (drop_glue_trivial_spec_attrs ((((layout_Layout_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((layout_Layout_inv_t_rt))) (layout_Layout_sls : syn_type)) -[] -[(layout_Layout_inv_t  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in fn_spec_add_late_pre ((Try_branch_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[(layout_Layout_inv_t  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[(layout_Layout_inv_t  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))%I) -∗
  std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_mutu8_std_collections_TryReserveError_std_collections_TryReserveError_loc ◁ᵥ{π, MetaNone} std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_mutu8_std_collections_TryReserveError_std_collections_TryReserveError_loc @ function_ptr [((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let realization := (std_result_ResultTFasFromResidualstd_result_ResultE_realization loc (((errors_TryReserveError_inv_t_rt))) (((errors_TryReserveError_inv_t_rt))) PtrSynType (errors_TryReserveError_sls : syn_type) (errors_TryReserveError_sls : syn_type) (Tasconvert_FromT_spec_attrs ((((errors_TryReserveError_inv_t_rt)))) ((drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))))) (trait_spec_realization_instantiate (Tasconvert_FromT_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) -[] -[(errors_TryReserveError_inv_t  -[] -[])]) (drop_glue_trivial_spec_attrs (loc)) (trait_spec_realization_instantiate (drop_glue_trivial_realization loc PtrSynType) -[] -[alias_ptr_t]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in fn_spec_add_late_pre ((FromResidual_from_residual_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[alias_ptr_t; (errors_TryReserveError_inv_t  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[alias_ptr_t; (errors_TryReserveError_inv_t  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))%I) -∗
  typed_function π (raw_vec_implRawVecInnerA_finish_grow_def Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc  allocation_allocate_raw_A_loc  allocation_grow_raw_A_loc  layout_Layout_align_loc  panic_shim_loc  raw_vec_assert_unchecked_loc  raw_vec_implRawVecInnerA_current_memory_A_loc  raw_vec_layout_array_loc  std_result_ResultTEasTry_branch_std_alloc_Layout_std_collections_TryReserveError_loc  std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_mutu8_std_collections_TryReserveError_std_collections_TryReserveError_loc  A_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_finish_grow A_rt A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs -[ulft_1] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_raw_vec_implRawVecInnerA_finish_grow (A_rt) (A_st) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (Allocator_A_spec_attrs) (Allocator_A_realization))-[ulft_1] -[A_ty]) π)
  ∗ ((introduce_direct ((let realization := (Tasconvert_IntoU_realization (((errors_TryReserveErrorKind_rt))) (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveErrorKind_els : syn_type) (errors_TryReserveError_sls : syn_type) errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_spec_attrs (trait_spec_realization_instantiate (errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_realization) -[] -[]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in realization.(trait_ctx_wf) -[] -[(errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))))
  ∗ ((introduce_direct ((let realization := (std_result_ResultTEasTry_realization (((layout_Layout_inv_t_rt))) (((errors_TryReserveError_inv_t_rt))) (layout_Layout_sls : syn_type) (errors_TryReserveError_sls : syn_type) (drop_glue_trivial_spec_attrs ((((layout_Layout_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((layout_Layout_inv_t_rt))) (layout_Layout_sls : syn_type)) -[] -[(layout_Layout_inv_t  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in realization.(trait_ctx_wf) -[] -[(layout_Layout_inv_t  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))))
  ∗ ((introduce_direct ((let realization := (std_result_ResultTFasFromResidualstd_result_ResultE_realization loc (((errors_TryReserveError_inv_t_rt))) (((errors_TryReserveError_inv_t_rt))) PtrSynType (errors_TryReserveError_sls : syn_type) (errors_TryReserveError_sls : syn_type) (Tasconvert_FromT_spec_attrs ((((errors_TryReserveError_inv_t_rt)))) ((drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))))) (trait_spec_realization_instantiate (Tasconvert_FromT_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) -[] -[(errors_TryReserveError_inv_t  -[] -[])]) (drop_glue_trivial_spec_attrs (loc)) (trait_spec_realization_instantiate (drop_glue_trivial_realization loc PtrSynType) -[] -[alias_ptr_t]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in realization.(trait_ctx_wf) -[] -[alias_ptr_t; (errors_TryReserveError_inv_t  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))))
  ∗ (□ (∀ (late_lft_0 : lft), allocation_allocate_raw_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (∀ (late_lft_0 : lft), allocation_grow_raw_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_align_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (panic_shim_loc_linking -[] -[] π))
  ∗ (□ (raw_vec_assert_unchecked_loc_linking -[] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), raw_vec_implRawVecInnerA_current_memory_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (raw_vec_layout_array_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_implRawVecInnerA_finish_grow_prelude :=
  unfold raw_vec_implRawVecInnerA_finish_grow_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecInnerA_finish_grow");
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
  start_function "raw_vec_implRawVecInnerA_finish_grow" ϝ fid ( [ulft_1 [] ] ) ( [A_ty [] ] ) ( [ [ [  v self ] cap ] elem_layout ] ) ( v self cap elem_layout );
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
