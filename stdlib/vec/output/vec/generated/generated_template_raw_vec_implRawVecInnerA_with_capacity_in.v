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
Definition raw_vec_implRawVecInnerA_with_capacity_in_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(A_st : !syn_type) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (drop_glue_RawVecInner_A_loc : loc) (raw_vec_assert_unchecked_loc : loc) (raw_vec_handle_error_loc : loc) (raw_vec_implRawVecInnerA_needs_to_grow_A_loc : loc) (raw_vec_implRawVecInnerA_try_allocate_in_A_loc : loc) (raw_vec_assert_unchecked_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (raw_vec_handle_error_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_needs_to_grow_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_try_allocate_in_A_loc_linking : spec_with 0 [A_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  syn_type_is_layoutable (((Result_Err_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls (A_st)) : syn_type)) →
  syn_type_is_layoutable ((raw_vec_AllocInit_els : syn_type)) →
  syn_type_is_layoutable ((raw_vec_AllocInit_Uninitialized_sls : syn_type)) →
  drop_glue_RawVecInner_A_loc ◁ᵥ{π, MetaNone} drop_glue_RawVecInner_A_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), let realization := (drop_glue_RawVecInner_realization (A_rt) A_st Allocator_A_spec_attrs Allocator_A_realization DropGlue_A_spec_attrs DropGlue_A_realization) in fn_spec_add_late_pre ((DropGlue_drop_glue_spec (RRGS:=RRGS) (realization.(trait_ctx_spec) -[] -[A_ty] -[] -[]))  -[] -[]) (λ π, (realization.(trait_ctx_wf) -[] -[A_ty] π))%I) -∗
  raw_vec_assert_unchecked_loc ◁ᵥ{π, MetaNone} raw_vec_assert_unchecked_loc @ function_ptr [BoolSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_assert_unchecked (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (raw_vec_assert_unchecked_loc_linking -[] -[] π)))%I) -∗
  raw_vec_handle_error_loc ◁ᵥ{π, MetaNone} raw_vec_handle_error_loc @ function_ptr [(errors_TryReserveError_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_handle_error (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (raw_vec_handle_error_loc_linking -[] -[] π)))%I) -∗
  raw_vec_implRawVecInnerA_needs_to_grow_A_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_needs_to_grow_A_loc @ function_ptr [RefSynType; (IntSynType USize); (IntSynType USize); (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_needs_to_grow (RRGS:=RRGS) ((A_rt)) (A_st) DropGlue_A_spec_attrs Allocator_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (raw_vec_implRawVecInnerA_needs_to_grow_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  raw_vec_implRawVecInnerA_try_allocate_in_A_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_try_allocate_in_A_loc @ function_ptr [(IntSynType USize); raw_vec_AllocInit_st; A_st; (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_try_allocate_in (RRGS:=RRGS) ((A_rt)) (A_st) DropGlue_A_spec_attrs Allocator_A_spec_attrs -[] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (raw_vec_implRawVecInnerA_try_allocate_in_A_loc_linking -[] -[A_ty] π)))%I) -∗
  typed_function π (raw_vec_implRawVecInnerA_with_capacity_in_def drop_glue_RawVecInner_A_loc  raw_vec_assert_unchecked_loc  raw_vec_handle_error_loc  raw_vec_implRawVecInnerA_needs_to_grow_A_loc  raw_vec_implRawVecInnerA_try_allocate_in_A_loc  A_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_with_capacity_in A_rt A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs -[] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_raw_vec_implRawVecInnerA_with_capacity_in (A_rt) (A_st) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (Allocator_A_spec_attrs) (Allocator_A_realization))-[] -[A_ty]) π)
  ∗ ((introduce_direct ((let realization := (drop_glue_RawVecInner_realization (A_rt) A_st Allocator_A_spec_attrs Allocator_A_realization DropGlue_A_spec_attrs DropGlue_A_realization) in realization.(trait_ctx_wf) -[] -[A_ty] π))))
  ∗ (□ (raw_vec_assert_unchecked_loc_linking -[] -[] π))
  ∗ (□ (raw_vec_handle_error_loc_linking -[] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), raw_vec_implRawVecInnerA_needs_to_grow_A_loc_linking -[late_lft_0] -[A_ty] π))
  ∗ (□ (raw_vec_implRawVecInnerA_try_allocate_in_A_loc_linking -[] -[A_ty] π)))).
End proof.

Ltac raw_vec_implRawVecInnerA_with_capacity_in_prelude :=
  unfold raw_vec_implRawVecInnerA_with_capacity_in_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecInnerA_with_capacity_in");
  intros A_rt A_st DropGlue_A_spec_attrs DropGlue_A_realization Allocator_A_spec_attrs Allocator_A_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let A_ty := fresh "A_ty" in
  let capacity := fresh "capacity" in
  let alloc := fresh "alloc" in
  let elem_layout := fresh "elem_layout" in
  start_function "raw_vec_implRawVecInnerA_with_capacity_in" ϝ fid ( [] ) ( [A_ty [] ] ) ( [ [  capacity alloc ] elem_layout ] ) ( capacity alloc elem_layout );
  intros arg_capacity arg_alloc arg_elem_layout;
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
