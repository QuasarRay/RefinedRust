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
Definition raw_vec_implRawVecT_with_capacity_zeroed_lemma (π : thread_id) : Prop :=
  ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_T_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (layout_Layout_new_T_loc : loc) (raw_vec_implRawVecInnerA_with_capacity_zeroed_in_std_alloc_Global_loc : loc) (layout_Layout_new_T_loc_linking : spec_with 0 [T_rt] (thread_id → iProp Σ)) (raw_vec_implRawVecInnerA_with_capacity_zeroed_in_std_alloc_Global_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (T_st) →
  syn_type_is_layoutable ((Global_sls : syn_type)) →
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable (((core_marker_PhantomData_sls (T_st)) : syn_type)) →
  syn_type_is_layoutable (((RawVec_sls (T_st) ((Global_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls ((Global_sls : syn_type))) : syn_type)) →
  layout_Layout_new_T_loc ◁ᵥ{π, MetaNone} layout_Layout_new_T_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_new (RRGS:=RRGS) ((T_rt)) (T_st) DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (from_assumption_hint (layout_Layout_new_T_loc_linking -[] -[T_ty] π)))%I) -∗
  raw_vec_implRawVecInnerA_with_capacity_zeroed_in_std_alloc_Global_loc ◁ᵥ{π, MetaNone} raw_vec_implRawVecInnerA_with_capacity_zeroed_in_std_alloc_Global_loc @ function_ptr [(IntSynType USize); (Global_sls : syn_type); (layout_Layout_sls : syn_type)] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_with_capacity_zeroed_in (RRGS:=RRGS) ((((Global_inv_t_rt)))) ((Global_sls : syn_type)) (drop_glue_trivial_spec_attrs ((((Global_inv_t_rt))))) GlobalasAllocator_spec_attrs -[] -[(Global_inv_t  -[] -[])]) (λ π, (from_assumption_hint (raw_vec_implRawVecInnerA_with_capacity_zeroed_in_std_alloc_Global_loc_linking -[] -[] π)))%I) -∗
  typed_function π (raw_vec_implRawVecT_with_capacity_zeroed_def layout_Layout_new_T_loc  raw_vec_implRawVecInnerA_with_capacity_zeroed_in_std_alloc_Global_loc  T_st  ) (<tag_type> spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecT_with_capacity_zeroed T_rt T_st DropGlue_T_spec_attrs -[] -[T_ty]) (λ π, ((typaram_wf T_rt T_st T_ty))
  ∗ (((trait_incl_of_raw_vec_implRawVecT_with_capacity_zeroed (T_rt) (T_st) (DropGlue_T_spec_attrs) (DropGlue_T_realization))-[] -[T_ty]) π)
  ∗ (□ (layout_Layout_new_T_loc_linking -[] -[T_ty] π))
  ∗ (□ (raw_vec_implRawVecInnerA_with_capacity_zeroed_in_std_alloc_Global_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_implRawVecT_with_capacity_zeroed_prelude :=
  unfold raw_vec_implRawVecT_with_capacity_zeroed_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecT_with_capacity_zeroed");
  intros T_rt T_st DropGlue_T_spec_attrs DropGlue_T_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let T_ty := fresh "T_ty" in
  let capacity := fresh "capacity" in
  start_function "raw_vec_implRawVecT_with_capacity_zeroed" ϝ fid ( [] ) ( [T_ty [] ] ) (  capacity ) ( capacity );
  intros arg_capacity;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( <[
      "T" :=
  existT _ (T_ty)
      ]>%E $ ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
