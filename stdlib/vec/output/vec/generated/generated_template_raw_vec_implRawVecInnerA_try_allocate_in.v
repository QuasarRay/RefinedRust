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
Definition raw_vec_implRawVecInnerA_try_allocate_in_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(A_st : !syn_type) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_A_drop_glue_loc : loc) (Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc : loc) (allocation_allocate_raw_A_loc : loc) (allocation_allocate_zeroed_raw_A_loc : loc) (layout_Layout_alignment_loc : loc) (layout_Layout_size_loc : loc) (raw_vec_implRawVecInnerA_new_in_A_loc : loc) (raw_vec_layout_array_loc : loc) (unique_Unique_T_new_unchecked_u8_loc : loc) (allocation_allocate_raw_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (allocation_allocate_zeroed_raw_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (layout_Layout_alignment_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (layout_Layout_size_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_new_in_A_loc_linking : spec_with 0 [A_rt] (thread_id → iProp Σ)) (raw_vec_layout_array_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (unique_Unique_T_new_unchecked_u8_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable ((errors_AllocError_sls : syn_type)) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_els : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_AllocError_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveErrorKind_CapacityOverflow_sls : syn_type)) →
  syn_type_is_layoutable ((alignment_Alignment_sls : syn_type)) →
  syn_type_is_layoutable (((Result_Err_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((unique_Unique_sls ((IntSynType U8))) : syn_type)) →
  syn_type_is_layoutable (((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls (A_st)) : syn_type)) →
  syn_type_is_layoutable ((raw_vec_AllocInit_els : syn_type)) →
  DropGlue_A_drop_glue_loc ◁ᵥ{π, MetaNone} DropGlue_A_drop_glue_loc @ function_ptr [RefSynType] (<tag_type> spec_collapse_params _ _ (λ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst -[] -[]))  -[] -[]) (λ π, (DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I)) -∗
  Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc ◁ᵥ{π, MetaNone} Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc @ function_ptr [(errors_TryReserveErrorKind_els : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), let realization := (Tasconvert_IntoU_realization (((errors_TryReserveErrorKind_rt))) (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveErrorKind_els : syn_type) (errors_TryReserveError_sls : syn_type) errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_spec_attrs (trait_spec_realization_instantiate (errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_realization) -[] -[]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in fn_spec_add_late_pre ((convert_Into_into_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[(errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[(errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))%I) -∗
  allocation_allocate_raw_A_loc ◁ᵥ{π, MetaNone} allocation_allocate_raw_A_loc @ function_ptr [RefSynType; (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_allocation_allocate_raw (RRGS:=RRGS) ((A_rt)) (A_st) Allocator_A_spec_attrs DropGlue_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (allocation_allocate_raw_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  allocation_allocate_zeroed_raw_A_loc ◁ᵥ{π, MetaNone} allocation_allocate_zeroed_raw_A_loc @ function_ptr [RefSynType; (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_allocation_allocate_zeroed_raw (RRGS:=RRGS) ((A_rt)) (A_st) Allocator_A_spec_attrs DropGlue_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (allocation_allocate_zeroed_raw_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  layout_Layout_alignment_loc ◁ᵥ{π, MetaNone} layout_Layout_alignment_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_alignment (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_alignment_loc_linking -[late_lft_0] -[] π)))%I) -∗
  layout_Layout_size_loc ◁ᵥ{π, MetaNone} layout_Layout_size_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_size (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_size_loc_linking -[late_lft_0] -[] π)))%I) -∗
  raw_vec_implRawVecInnerA_new_in_A_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_new_in_A_loc @ function_ptr [A_st; (alignment_Alignment_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_new_in (RRGS:=RRGS) ((A_rt)) (A_st) DropGlue_A_spec_attrs Allocator_A_spec_attrs -[] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (raw_vec_implRawVecInnerA_new_in_A_loc_linking -[] -[A_ty] π)))%I) -∗
  raw_vec_layout_array_loc ◁ᵥ{π, MetaNone} raw_vec_layout_array_loc @ function_ptr [(IntSynType USize); (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_layout_array (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (raw_vec_layout_array_loc_linking -[] -[] π)))%I) -∗
  unique_Unique_T_new_unchecked_u8_loc ◁ᵥ{π, MetaNone} unique_Unique_T_new_unchecked_u8_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_unique_Unique_T_new_unchecked (RRGS:=RRGS) (Z) ((IntSynType U8)) (drop_glue_trivial_spec_attrs (Z)) -[] -[(int U8)]) (λ π, (from_assumption_hint (unique_Unique_T_new_unchecked_u8_loc_linking -[] -[] π)))%I) -∗
  typed_function π (raw_vec_implRawVecInnerA_try_allocate_in_def DropGlue_A_drop_glue_loc  Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc  allocation_allocate_raw_A_loc  allocation_allocate_zeroed_raw_A_loc  layout_Layout_alignment_loc  layout_Layout_size_loc  raw_vec_implRawVecInnerA_new_in_A_loc  raw_vec_layout_array_loc  unique_Unique_T_new_unchecked_u8_loc  A_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_try_allocate_in A_rt A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs -[] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_raw_vec_implRawVecInnerA_try_allocate_in (A_rt) (A_st) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (Allocator_A_spec_attrs) (Allocator_A_realization))-[] -[A_ty]) π)
  ∗ ((introduce_direct ((let realization := (Tasconvert_IntoU_realization (((errors_TryReserveErrorKind_rt))) (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveErrorKind_els : syn_type) (errors_TryReserveError_sls : syn_type) errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_spec_attrs (trait_spec_realization_instantiate (errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_realization) -[] -[]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveErrorKind_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveErrorKind_rt))) (errors_TryReserveErrorKind_els : syn_type)) -[] -[(errors_TryReserveErrorKind_ty  -[] -[])]) (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (trait_spec_realization_instantiate (drop_glue_trivial_realization (((errors_TryReserveError_inv_t_rt))) (errors_TryReserveError_sls : syn_type)) -[] -[(errors_TryReserveError_inv_t  -[] -[])])) in realization.(trait_ctx_wf) -[] -[(errors_TryReserveErrorKind_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[])] π))))
  ∗ (□ (∀ (late_lft_0 : lft), allocation_allocate_raw_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (∀ (late_lft_0 : lft), allocation_allocate_zeroed_raw_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_alignment_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_size_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (raw_vec_implRawVecInnerA_new_in_A_loc_linking -[] -[A_ty] π))
  ∗ (□ (raw_vec_layout_array_loc_linking -[] -[] π))
  ∗ (□ (unique_Unique_T_new_unchecked_u8_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_implRawVecInnerA_try_allocate_in_prelude :=
  unfold raw_vec_implRawVecInnerA_try_allocate_in_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecInnerA_try_allocate_in");
  intros A_rt A_st DropGlue_A_spec_attrs DropGlue_A_realization Allocator_A_spec_attrs Allocator_A_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let A_ty := fresh "A_ty" in
  let capacity := fresh "capacity" in
  let init := fresh "init" in
  let alloc := fresh "alloc" in
  let elem_layout := fresh "elem_layout" in
  start_function "raw_vec_implRawVecInnerA_try_allocate_in" ϝ fid ( [] ) ( [A_ty [] ] ) ( [ [ [  capacity init ] alloc ] elem_layout ] ) ( capacity init alloc elem_layout );
  intros arg_capacity arg_init arg_alloc arg_elem_layout;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "A" :=
  existT _ (A_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
