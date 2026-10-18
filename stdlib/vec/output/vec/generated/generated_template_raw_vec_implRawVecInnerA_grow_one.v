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
Definition raw_vec_implRawVecInnerA_grow_one_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(A_st : !syn_type) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (raw_vec_handle_error_loc : loc) (raw_vec_implRawVecInnerA_grow_amortized_A_loc : loc) (raw_vec_handle_error_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_grow_amortized_A_loc_linking : spec_with 1 [A_rt] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  syn_type_is_layoutable (((Result_Err_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls (A_st)) : syn_type)) →
  raw_vec_handle_error_loc ◁ᵥ{π, MetaNone} raw_vec_handle_error_loc @ function_ptr [(errors_TryReserveError_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_handle_error (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (raw_vec_handle_error_loc_linking -[] -[] π)))%I) -∗
  raw_vec_implRawVecInnerA_grow_amortized_A_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_grow_amortized_A_loc @ function_ptr [RefSynType; (IntSynType USize); (IntSynType USize); (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_grow_amortized (RRGS:=RRGS) ((A_rt)) (A_st) DropGlue_A_spec_attrs Allocator_A_spec_attrs -[late_lft_0] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (from_assumption_hint (raw_vec_implRawVecInnerA_grow_amortized_A_loc_linking -[late_lft_0] -[A_ty] π)))%I) -∗
  typed_function π (raw_vec_implRawVecInnerA_grow_one_def raw_vec_handle_error_loc  raw_vec_implRawVecInnerA_grow_amortized_A_loc  A_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_grow_one A_rt A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs -[ulft_1] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_raw_vec_implRawVecInnerA_grow_one (A_rt) (A_st) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (Allocator_A_spec_attrs) (Allocator_A_realization))-[ulft_1] -[A_ty]) π)
  ∗ (□ (raw_vec_handle_error_loc_linking -[] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), raw_vec_implRawVecInnerA_grow_amortized_A_loc_linking -[late_lft_0] -[A_ty] π)))).
End proof.

Ltac raw_vec_implRawVecInnerA_grow_one_prelude :=
  unfold raw_vec_implRawVecInnerA_grow_one_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecInnerA_grow_one");
  intros A_rt A_st DropGlue_A_spec_attrs DropGlue_A_realization Allocator_A_spec_attrs Allocator_A_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let A_ty := fresh "A_ty" in
  let v := fresh "v" in
  let self := fresh "self" in
  let elem_layout := fresh "elem_layout" in
  start_function "raw_vec_implRawVecInnerA_grow_one" ϝ fid ( [ulft_1 [] ] ) ( [A_ty [] ] ) ( [ [  v self ] elem_layout ] ) ( v self elem_layout );
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
