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
Definition raw_vec_layout_array_lemma (π : thread_id) : Prop :=
  ∀ (Result_TE_map_err_std_alloc_Layout_std_alloc_LayoutError_std_collections_TryReserveError_closuresrcraw_vecrs758975812_loc : loc) (layout_Layout_pad_to_align_loc : loc) (layout_Layout_repeat_packed_loc : loc) (layout_Layout_size_loc : loc) (panic_shim_loc : loc) (Result_TE_map_err_std_alloc_Layout_std_alloc_LayoutError_std_collections_TryReserveError_closuresrcraw_vecrs758975812_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) (layout_Layout_pad_to_align_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (layout_Layout_repeat_packed_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (layout_Layout_size_loc_linking : spec_with 1 [] (thread_id → iProp Σ)) (panic_shim_loc_linking : spec_with 0 [] (thread_id → iProp Σ)) , 
  syn_type_is_layoutable ((layout_Layout_sls : syn_type)) →
  syn_type_is_layoutable ((layout_LayoutError_sls : syn_type)) →
  syn_type_is_layoutable ((errors_TryReserveError_sls : syn_type)) →
  syn_type_is_layoutable (((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)) →
  syn_type_is_layoutable (((Result_els ((layout_Layout_sls : syn_type)) ((layout_LayoutError_sls : syn_type))) : syn_type)) →
  Result_TE_map_err_std_alloc_Layout_std_alloc_LayoutError_std_collections_TryReserveError_closuresrcraw_vecrs758975812_loc ◁ᵥ{π, MetaNone} Result_TE_map_err_std_alloc_Layout_std_alloc_LayoutError_std_collections_TryReserveError_closuresrcraw_vecrs758975812_loc @ function_ptr [((Result_els ((layout_Layout_sls : syn_type)) ((layout_LayoutError_sls : syn_type))) : syn_type); UnitSynType] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_Result_TE_map_err (RRGS:=RRGS) ((((layout_Layout_inv_t_rt)))) ((((layout_LayoutError_rt)))) ((((errors_TryReserveError_inv_t_rt)))) (unit) ((layout_Layout_sls : syn_type)) ((layout_LayoutError_sls : syn_type)) ((errors_TryReserveError_sls : syn_type)) (UnitSynType) (drop_glue_trivial_spec_attrs ((((layout_Layout_inv_t_rt))))) (drop_glue_trivial_spec_attrs ((((layout_LayoutError_rt))))) raw_vec_layout_array_closure0_FnOnce_spec_attrs (drop_glue_trivial_spec_attrs ((((errors_TryReserveError_inv_t_rt))))) (drop_glue_trivial_spec_attrs (unit)) -[] -[(layout_Layout_inv_t  -[] -[]); (layout_LayoutError_ty  -[] -[]); (errors_TryReserveError_inv_t  -[] -[]); unit_t]) (λ π, (from_assumption_hint (Result_TE_map_err_std_alloc_Layout_std_alloc_LayoutError_std_collections_TryReserveError_closuresrcraw_vecrs758975812_loc_linking -[] -[] π)))%I) -∗
  layout_Layout_pad_to_align_loc ◁ᵥ{π, MetaNone} layout_Layout_pad_to_align_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_pad_to_align (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_pad_to_align_loc_linking -[late_lft_0] -[] π)))%I) -∗
  layout_Layout_repeat_packed_loc ◁ᵥ{π, MetaNone} layout_Layout_repeat_packed_loc @ function_ptr [RefSynType; (IntSynType USize)] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_repeat_packed (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_repeat_packed_loc_linking -[late_lft_0] -[] π)))%I) -∗
  layout_Layout_size_loc ◁ᵥ{π, MetaNone} layout_Layout_size_loc @ function_ptr [RefSynType] (<tag_type> spec! ( *[late_lft_0]) : 1 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_layout_Layout_size (RRGS:=RRGS)  -[late_lft_0] -[]) (λ π, (from_assumption_hint (layout_Layout_size_loc_linking -[late_lft_0] -[] π)))%I) -∗
  panic_shim_loc ◁ᵥ{π, MetaNone} panic_shim_loc @ function_ptr [] (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_panic_shim (RRGS:=RRGS)  -[] -[]) (λ π, (from_assumption_hint (panic_shim_loc_linking -[] -[] π)))%I) -∗
  typed_function π (raw_vec_layout_array_def Result_TE_map_err_std_alloc_Layout_std_alloc_LayoutError_std_collections_TryReserveError_closuresrcraw_vecrs758975812_loc  layout_Layout_pad_to_align_loc  layout_Layout_repeat_packed_loc  layout_Layout_size_loc  panic_shim_loc  ) (<tag_type> spec! ( *[]) : 0 | ( *[]) : ([] : list RT), fn_spec_add_late_pre (type_of_raw_vec_layout_array -[] -[]) (λ π, (True)
  ∗ ((trait_incl_of_raw_vec_layout_array-[] -[]) π)
  ∗ (□ (Result_TE_map_err_std_alloc_Layout_std_alloc_LayoutError_std_collections_TryReserveError_closuresrcraw_vecrs758975812_loc_linking -[] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_pad_to_align_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_repeat_packed_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (∀ (late_lft_0 : lft), layout_Layout_size_loc_linking -[late_lft_0] -[] π))
  ∗ (□ (panic_shim_loc_linking -[] -[] π)))).
End proof.

Ltac raw_vec_layout_array_prelude :=
  unfold raw_vec_layout_array_lemma;
  set (FN_NAME := FUNCTION_NAME "raw_vec_layout_array");
  intros;
  iStartProof;
  let ϝ := fresh "ϝ" in
  let fid := fresh "fid" in
  let cap := fresh "cap" in
  let elem_layout := fresh "elem_layout" in
  start_function "raw_vec_layout_array" ϝ fid ( [] ) ( [] ) ( [  cap elem_layout ] ) ( cap elem_layout );
  intros arg_cap arg_elem_layout;
  let π := get_π in
  let Σ := get_Σ in
  specialize (pose_bb_inv (PolyNil)) as loop_map;
  init_lfts π fid (("_flft", ϝ) :: ("static", static) :: [] );
  init_tyvars ( ∅ );
  unfold_generic_inst; simpl;
  generalize RR_CONFIG_DO_STRICT_RESOLUTION; intros ?.
