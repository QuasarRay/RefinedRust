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
Definition raw_vec_implRawVecInnerA_set_ptr_and_cap_lemma (π : thread_id) : Prop :=
  ∀ `(A_rt : !RT) `(A_st : !syn_type) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_A_realization : !(trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(Allocator_A_realization : !(trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (unique_Unique_T_new_unchecked_u8_loc : loc) (unique_Unique_T_new_unchecked_u8_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable (A_st) →
  syn_type_is_layoutable (((unique_Unique_sls ((IntSynType U8))) : syn_type)) →
  syn_type_is_layoutable (((RawVecInner_sls (A_st)) : syn_type)) →
  unique_Unique_T_new_unchecked_u8_loc ◁ᵥ{π, MetaNone} unique_Unique_T_new_unchecked_u8_loc @ function_ptr [PtrSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_unique_Unique_T_new_unchecked (RRGS:=RRGS) (Z) ((IntSynType U8)) (drop_glue_trivial_spec_attrs (Z)) -[] -[(int U8)]) (λ π, (from_assumption_hint (unique_Unique_T_new_unchecked_u8_loc_linking -[] -[] π)))%I) -∗
  typed_function π (raw_vec_implRawVecInnerA_set_ptr_and_cap_def unique_Unique_T_new_unchecked_u8_loc  A_st  ) (<tag_type> spec! ( *[ulft_1]) : 1 | ( *[A_ty]) : ([A_rt] : list RT), fn_spec_add_late_pre (type_of_raw_vec_implRawVecInnerA_set_ptr_and_cap A_rt A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs -[ulft_1] -[A_ty]) (λ π, ((typaram_wf A_rt A_st A_ty))
  ∗ (((trait_incl_of_raw_vec_implRawVecInnerA_set_ptr_and_cap (A_rt) (A_st) (DropGlue_A_spec_attrs) (DropGlue_A_realization) (Allocator_A_spec_attrs) (Allocator_A_realization))-[ulft_1] -[A_ty]) π)
  ∗ (□ (unique_Unique_T_new_unchecked_u8_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_implRawVecInnerA_set_ptr_and_cap_prelude :=
  unfold raw_vec_implRawVecInnerA_set_ptr_and_cap_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_implRawVecInnerA_set_ptr_and_cap");
  intros A_rt A_st DropGlue_A_spec_attrs DropGlue_A_realization Allocator_A_spec_attrs Allocator_A_realization;
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let ulft_1 := fresh "ulft_1" in
  let A_ty := fresh "A_ty" in
  let self := fresh "self" in
  let ptr := fresh "ptr" in
  let cap := fresh "cap" in
  start_function "raw_vec_implRawVecInnerA_set_ptr_and_cap" ϝ fid ( [ulft_1 [] ] ) ( [A_ty [] ] ) ( [ [  self ptr ] cap ] ) ( self ptr cap );
  intros arg_self arg_ptr arg_cap;
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
