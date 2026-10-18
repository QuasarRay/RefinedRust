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
Definition raw_vec_implRawVecInner_with_capacity_lemma (π : thread_id) : Prop :=
  ∀ (raw_vec_handle_error_loc : loc) (raw_vec_implRawVecInnerA_try_allocate_in_std_alloc_Global_loc : loc) (raw_vec_handle_error_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_try_allocate_in_std_alloc_Global_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable ((Global_sls : syn_type)) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  syn_type_is_layoutable (((Result_Err_sls ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_Ok_sls ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls ((Global_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable ((raw_vec_AllocInit_els : syn_type)) →
  syn_type_is_layoutable ((raw_vec_AllocInit_Uninitialized_sls : syn_type)) →
  raw_vec_handle_error_loc ◁ᵥ{π, MetaNone} raw_vec_handle_error_loc @ function_ptr [(errors_TryReserveError_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_handle_error (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (raw_vec_handle_error_loc_linking -[] -[] π)))%I) -∗
  raw_vec_implRawVecInnerA_try_allocate_in_std_alloc_Global_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_try_allocate_in_std_alloc_Global_loc @ function_ptr [(IntSynType USize); raw_vec_AllocInit_st; (Global_sls : syn_type); (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_try_allocate_in (RRGS:=RRGS) ((((Global_inv_t_rt)))) ((Global_sls : syn_type)) (drop_glue_trivial_spec_attrs ((((Global_inv_t_rt))))) GlobalasAllocator_spec_attrs -[] -[(Global_inv_t  -[] -[])]) (λ π, (from_assumption_hint (raw_vec_implRawVecInnerA_try_allocate_in_std_alloc_Global_loc_linking -[] -[] π)))%I) -∗
  typed_function π (raw_vec_implRawVecInner_with_capacity_def raw_vec_handle_error_loc  raw_vec_implRawVecInnerA_try_allocate_in_std_alloc_Global_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInner_with_capacity -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_raw_vec_implRawVecInner_with_capacity-[] -[]) π)
  ∗ (□ (raw_vec_handle_error_loc_linking -[] -[] π))
  ∗ (□ (raw_vec_implRawVecInnerA_try_allocate_in_std_alloc_Global_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_implRawVecInner_with_capacity_prelude :=
  unfold raw_vec_implRawVecInner_with_capacity_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecInner_with_capacity");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let capacity := fresh "capacity" in
  let elem_layout := fresh "elem_layout" in
  start_function "raw_vec_implRawVecInner_with_capacity" ϝ fid ( [] ) ( [] ) ( [  capacity elem_layout ] ) ( capacity elem_layout );
  intros arg_capacity arg_elem_layout;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
