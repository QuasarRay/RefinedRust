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
Section raw_vec_AllocInit_els.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition raw_vec_AllocInit_Uninitialized_sls  : struct_layout_spec :=
    let raw_vec_AllocInit_Uninitialized_st  := UnitSynType in
    let raw_vec_AllocInit_st  := UnitSynType in
    mk_sls "raw_vec_AllocInit_Uninitialized" [] StructReprRust.
  Definition raw_vec_AllocInit_Uninitialized_st  : syn_type := raw_vec_AllocInit_Uninitialized_sls .

  Definition raw_vec_AllocInit_Zeroed_sls  : struct_layout_spec :=
    let raw_vec_AllocInit_Zeroed_st  := UnitSynType in
    let raw_vec_AllocInit_st  := UnitSynType in
    mk_sls "raw_vec_AllocInit_Zeroed" [] StructReprRust.
  Definition raw_vec_AllocInit_Zeroed_st  : syn_type := raw_vec_AllocInit_Zeroed_sls .

  Program Definition raw_vec_AllocInit_els  : enum_layout_spec := mk_els "raw_vec_AllocInit" ISize [
    ("Uninitialized", raw_vec_AllocInit_Uninitialized_st );
    ("Zeroed", raw_vec_AllocInit_Zeroed_st )] EnumReprRust [("Uninitialized", 0); ("Zeroed", 1)] _ _ _ _.
  Next Obligation. solve_enum_layout_spec_variants_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_variants_eq. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.
  Final Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.
  Global Typeclasses Opaque raw_vec_AllocInit_els.
  Definition raw_vec_AllocInit_st  : syn_type := raw_vec_AllocInit_els .
End raw_vec_AllocInit_els.

Section Iter_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Iter_sls (T_st: syn_type) : struct_layout_spec :=
    let Iter_st (T_st: syn_type) := UnitSynType in
    mk_sls "Iter" [
    ("end_or_len", PtrSynType);
    ("_marker", ((core_marker_PhantomData_sls (RefSynType)) : syn_type))] StructReprRust.
  Definition Iter_st (T_st: syn_type) : syn_type := Iter_sls T_st.
End Iter_sls.

Section IterMut_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition IterMut_sls (T_st: syn_type) : struct_layout_spec :=
    let IterMut_st (T_st: syn_type) := UnitSynType in
    mk_sls "IterMut" [
    ("ptr", ((nonnull_NonNull_sls (T_st)) : syn_type));
    ("end_or_len", PtrSynType);
    ("_marker", ((core_marker_PhantomData_sls (RefSynType)) : syn_type))] StructReprRust.
  Definition IterMut_st (T_st: syn_type) : syn_type := IterMut_sls T_st.
End IterMut_sls.

Section IntoIter_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition IntoIter_sls (T_st: syn_type) (A_st: syn_type) : struct_layout_spec :=
    let IntoIter_st (T_st: syn_type) (A_st: syn_type) := UnitSynType in
    mk_sls "IntoIter" [
    ("_x", ((core_marker_PhantomData_sls (T_st)) : syn_type));
    ("_y", A_st)] StructReprRust.
  Definition IntoIter_st (T_st: syn_type) (A_st: syn_type) : syn_type := IntoIter_sls T_st A_st.
End IntoIter_sls.

Section RawVecInner_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition RawVecInner_sls (A_st: syn_type) : struct_layout_spec :=
    let RawVecInner_st (A_st: syn_type) := UnitSynType in
    mk_sls "RawVecInner" [
    ("ptr", ((unique_Unique_sls ((IntSynType U8))) : syn_type));
    ("cap", (IntSynType USize));
    ("alloc", A_st)] StructReprRust.
  Definition RawVecInner_st (A_st: syn_type) : syn_type := RawVecInner_sls A_st.
End RawVecInner_sls.

Section RawVec_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition RawVec_sls (T_st: syn_type) (A_st: syn_type) : struct_layout_spec :=
    let RawVec_st (T_st: syn_type) (A_st: syn_type) := UnitSynType in
    mk_sls "RawVec" [
    ("inner", (RawVecInner_st (A_st)));
    ("_marker", ((core_marker_PhantomData_sls (T_st)) : syn_type))] StructReprRust.
  Definition RawVec_st (T_st: syn_type) (A_st: syn_type) : syn_type := RawVec_sls T_st A_st.
End RawVec_sls.

Section Vec_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Vec_sls (T_st: syn_type) (A_st: syn_type) : struct_layout_spec :=
    let Vec_st (T_st: syn_type) (A_st: syn_type) := UnitSynType in
    mk_sls "Vec" [
    ("buf", (RawVec_st (T_st) (A_st)));
    ("len", (IntSynType USize))] StructReprRust.
  Definition Vec_st (T_st: syn_type) (A_st: syn_type) : syn_type := Vec_sls T_st A_st.
End Vec_sls.

Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

Program Definition RawVecTAasstd_ops_Drop_drop_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_deallocate_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__2";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__2" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (layout_Layout_sls : syn_type) } "__3";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__3"))
      ( Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_deallocate_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__2"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__3")] (Some (Na1Ord, (StructOp unit_sl []), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__3";
      local_dead "__2";
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition Vec_TA_is_empty_def (Vec_TA_len_T_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "__2";
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft4"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["Vec_inv_t"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "vlft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS Vec_TA_len_T_A_loc ["vlft6"] [RSTTyVar "T"; RSTTyVar "A"] [@{expr} move{ RefOp } ("__3")] (Some (Na1Ord, (IntOp USize), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__2")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      local_dead "__2";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_IntoIter_def (DropGlue_A_drop_glue_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (IntoIter_sls (T_st) (A_st)) } "_y")] None
      ( Goto "_bb1")
      ( Unwind)
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_RawVec_def (RawVecTAasstd_ops_Drop_drop_T_A_loc: loc) (drop_glue_RawVecInner_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      local_live{ RefSynType } "__2";
      local_live{ UnitSynType } "__3";
      "__2" <-{ RefOp } copy{ RefOp } ("ptr");
      CallS RawVecTAasstd_ops_Drop_drop_T_A_loc ["_flft"] [RSTTyVar "T"; RSTTyVar "A"] [@{expr} move{ RefOp } ("__2")] (Some (Na1Ord, (StructOp unit_sl []), "__3"))
      ( Goto "_bb4")
      ( Goto "_bb3")
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
     <[
     "_bb2" :=
      Unwind
     ]>%E $
     <[
     "_bb3" :=
      CallS drop_glue_RawVecInner_A_loc [] [RSTTyVar "A"] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (RawVec_sls (T_st) (A_st)) } "inner")] None
      ( Goto "_bb2")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb4" :=
      CallS drop_glue_RawVecInner_A_loc [] [RSTTyVar "A"] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (RawVec_sls (T_st) (A_st)) } "inner")] None
      ( Goto "_bb1")
      ( Unwind)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition drop_glue_RawVecInner_def (DropGlue_A_drop_glue_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "ret";
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ((!{ RefOp } ( "ptr" )) at{ (RawVecInner_sls (A_st)) } "alloc")] None
      ( Goto "_bb1")
      ( Unwind)
     ]>%E $
     <[
     "_bb1" :=
      return (zst_val)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_capacity_overflow_def (panic_shim_loc: loc) : function :=
  {|
     f_args := [
      
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ NeverSynType } "__0";
      local_live{ NeverSynType } "__1";
      CallS panic_shim_loc [] [] [@{expr} ] None
      ( StuckS)
      ( Unwind)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_handle_error_def (errors_TryReserveError_kind_loc: loc) (handle_alloc_error_loc: loc) (raw_vec_capacity_overflow_loc: loc) : function :=
  {|
     f_args := [
      ("e", (use_layout_alg' (errors_TryReserveError_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ NeverSynType } "__0";
      local_live{ (IntSynType ISize) } "__4";
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__2";
      local_live{ RefSynType } "__3";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])), "llft2" } ("e");
      annot{ 1 }: CopyLftNameAnnot "plft3" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft3"; (* function_call *)
      CallS errors_TryReserveError_kind_loc ["vlft4"] [] [@{expr} move{ RefOp } ("__3")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)), "__2"))
      ( annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__4" <-{ (IntOp ISize) } EnumDiscriminant (errors_TryReserveErrorKind_els) ("__2");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__4")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      StuckS
     ]>%E $
     <[
     "_bb3" :=
      local_live{ (layout_Layout_sls : syn_type) } "layout";
      "layout" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ((EnumData (errors_TryReserveErrorKind_els) "AllocError" ("__2")) at{ errors_TryReserveErrorKind_AllocError_sls } "layout");
      local_live{ (layout_Layout_sls : syn_type) } "__6";
      "__6" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("layout");
      CallS handle_alloc_error_loc [] [] [@{expr} move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__6")] (Some (Na1Ord, NeverOp, "__0"))
      ( StuckS)
      ( Unwind)
     ]>%E $
     <[
     "_bb4" :=
      CallS raw_vec_capacity_overflow_loc [] [] [@{expr} ] (Some (Na1Ord, NeverOp, "__0"))
      ( StuckS)
      ( Unwind)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_allocator_def (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ RefSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__2";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft6"; (* borrow *)
      "__2" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft3" } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "alloc");
      annot{ 1 }: CopyLftNameAnnot "plft7" "vlft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft7"; (* borrow *)
      "__0" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft4" } (!{ RefOp } ( "__2" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft4"; (* post-assignment *)
      local_dead "__2";
      annot{ 1 }: ExtendLftAnnot "plft5"; (* return *)
      return (move{ RefOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_capacity_def (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("elem_size", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("elem_size");
      "__3" <-{ BoolOp } (move{ (IntOp USize) } ("__4")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      "__0" <-{ (IntOp USize) } i2v (18446744073709551615) USize;
      Goto "_bb3"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__4";
      "__0" <-{ (IntOp USize) } copy{ (IntOp USize) } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "cap");
      Goto "_bb3"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__3";
      return (move{ (IntOp USize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_current_memory_def (Tasconvert_IntoU_into_std_ptr_Uniqueu8_std_ptr_NonNullu8_loc: loc) (layout_Layout_align_loc: loc) (layout_Layout_from_size_align_unchecked_loc: loc) (layout_Layout_size_loc: loc) (usize_unchecked_mul_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType USize) } "__4";
      local_live{ RefSynType } "__5";
      annot{ 1 }: StartLftAnnot "llft3" ["_flft"]; (* borrow *)
      "__5" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft3" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft7"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft10"] [] [@{expr} move{ RefOp } ("__5")] (Some (Na1Ord, (IntOp USize), "__4"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      "__3" <-{ BoolOp } (move{ (IntOp USize) } ("__4")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb2"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__4";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__4";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "cap");
      "__6" <-{ BoolOp } (move{ (IntOp USize) } ("__7")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb4"
      else
       Goto "_bb6"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__7";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      "__0" <-{ (use_op_alg' ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) } EnumInit (Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) "None" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["tuple2_ty"] (RSTScopeInst [] [RSTLitType ["nonnull_NonNull_inv_t"] (RSTScopeInst [] [RSTInt U8] []); RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])] [])] [])) (StructInit (Option_None_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) []);
      Goto "_bb12"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__7";
      local_live{ (IntSynType USize) } "alloc_size";
      local_live{ (IntSynType USize) } "__9";
      local_live{ RefSynType } "__10";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__10" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft4" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft8"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft11"] [] [@{expr} move{ RefOp } ("__10")] (Some (Na1Ord, (IntOp USize), "__9"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb7")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__10";
      local_live{ (IntSynType USize) } "__11";
      "__11" <-{ (IntOp USize) } copy{ (IntOp USize) } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "cap");
      CallS usize_unchecked_mul_loc [] [] [@{expr} move{ (IntOp USize) } ("__9"); move{ (IntOp USize) } ("__11")] (Some (Na1Ord, (IntOp USize), "alloc_size"))
      ( Goto "_bb8")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__11";
      local_dead "__9";
      local_live{ (layout_Layout_sls : syn_type) } "layout";
      local_live{ (IntSynType USize) } "__13";
      "__13" <-{ (IntOp USize) } copy{ (IntOp USize) } ("alloc_size");
      local_live{ (IntSynType USize) } "__14";
      local_live{ RefSynType } "__15";
      annot{ 1 }: StartLftAnnot "llft5" ["_flft"]; (* borrow *)
      "__15" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft5" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft9"; (* function_call *)
      CallS layout_Layout_align_loc ["vlft12"] [] [@{expr} move{ RefOp } ("__15")] (Some (Na1Ord, (IntOp USize), "__14"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb9")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__15";
      CallS layout_Layout_from_size_align_unchecked_loc [] [] [@{expr} move{ (IntOp USize) } ("__13"); move{ (IntOp USize) } ("__14")] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "layout"))
      ( Goto "_bb10")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__14";
      local_dead "__13";
      local_live{ ((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type) } "__16";
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "__17";
      local_live{ ((unique_Unique_sls ((IntSynType U8))) : syn_type) } "__18";
      "__18" <-{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "ptr");
      CallS Tasconvert_IntoU_into_std_ptr_Uniqueu8_std_ptr_NonNullu8_loc [] [] [@{expr} move{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } ("__18")] (Some (Na1Ord, (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)), "__17"))
      ( Goto "_bb11")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__18";
      local_live{ (layout_Layout_sls : syn_type) } "__19";
      "__19" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("layout");
      "__16" <-{ (use_op_alg' ((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)) } StructInit (tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) [("0", move{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("__17") : expr); ("1", move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__19") : expr)];
      local_dead "__19";
      local_dead "__17";
      "__0" <-{ (use_op_alg' ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) } EnumInit (Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) "Some" (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTLitType ["tuple2_ty"] (RSTScopeInst [] [RSTLitType ["nonnull_NonNull_inv_t"] (RSTScopeInst [] [RSTInt U8] []); RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])] [])] [])) (StructInit (Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) [("0", move{ (use_op_alg' ((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)) } ("__16") : expr)]);
      local_dead "__16";
      local_dead "layout";
      local_dead "alloc_size";
      Goto "_bb12"
     ]>%E $
     <[
     "_bb12" :=
      local_dead "__6";
      local_dead "__3";
      return (move{ (use_op_alg' ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_deallocate_def (allocation_deallocate_raw_A_loc: loc) (raw_vec_implRawVecInnerA_current_memory_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ (IntSynType ISize) } "__6";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      local_live{ ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type) } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft3" ["plft6"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft3"; (* post-assignment *)
      local_live{ (layout_Layout_sls : syn_type) } "__5";
      "__5" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft7"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_current_memory_A_loc ["vlft10"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__4"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__5")] (Some (Na1Ord, (use_op_alg' ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)), "__3"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__6" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)))) ("__3");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__6")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb4")
     ]>%E $
     <[
     "_bb2" :=
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "ptr";
      "ptr" <-{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } (((EnumData ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)))) "Some" ("__3")) at{ (Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) } "0") at{ (tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) } "0");
      local_live{ (layout_Layout_sls : syn_type) } "layout";
      "layout" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } (((EnumData ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)))) "Some" ("__3")) at{ (Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) } "0") at{ (tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) } "1");
      local_live{ UnitSynType } "__9";
      local_live{ RefSynType } "__10";
      local_live{ RefSynType } "__11";
      annot{ 1 }: StartLftAnnot "llft4" ["plft6"]; (* borrow *)
      "__11" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "llft4" } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "alloc");
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft9"; (* borrow *)
      "__10" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft5" } (!{ RefOp } ( "__11" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft5"; (* post-assignment *)
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "__12";
      "__12" <-{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("ptr");
      local_live{ (layout_Layout_sls : syn_type) } "__13";
      "__13" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("layout");
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft8"; (* function_call *)
      CallS allocation_deallocate_raw_A_loc ["vlft11"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__10"); move{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("__12"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__13")] (Some (Na1Ord, (StructOp unit_sl []), "__9"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb3")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__13";
      local_dead "__12";
      local_dead "__11";
      local_dead "__10";
      local_dead "__9";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "layout";
      local_dead "ptr";
      local_dead "__3";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__3";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_finish_grow_def (Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveError_closuresrcraw_vecrs6361363616_loc: loc) (allocation_allocate_raw_A_loc: loc) (allocation_grow_raw_A_loc: loc) (layout_Layout_align_loc: loc) (panic_shim_loc: loc) (raw_vec_assert_unchecked_loc: loc) (raw_vec_implRawVecInnerA_current_memory_A_loc: loc) (raw_vec_layout_array_loc: loc) (std_result_ResultTEasTry_branch_std_alloc_Layout_std_collections_TryReserveError_loc: loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_mutu8_std_collections_TryReserveError_std_collections_TryReserveError_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("cap", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__9";
      local_live{ NeverSynType } "__11";
      local_live{ (IntSynType ISize) } "__18";
      annot{ 1 }: CopyLftNameAnnot "plft16" "ulft_1"; (* initialization *)
      local_live{ (layout_Layout_sls : syn_type) } "new_layout";
      local_live{ ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type) } "__5";
      local_live{ ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ (layout_Layout_sls : syn_type) } "__8";
      "__8" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      CallS raw_vec_layout_array_loc [] [] [@{expr} move{ (IntOp USize) } ("__7"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__8")] (Some (Na1Ord, (use_op_alg' ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__6"))
      ( Goto "_bb1")
      ( Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__8";
      local_dead "__7";
      CallS std_result_ResultTEasTry_branch_std_alloc_Layout_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__6")] (Some (Na1Ord, (use_op_alg' ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)), "__5"))
      ( Goto "_bb2")
      ( Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__6";
      "__9" <-{ (IntOp ISize) } EnumDiscriminant ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type)))) ("__5");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__9")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb5"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb3" :=
      StuckS
     ]>%E $
     <[
     "_bb4" :=
      local_live{ (layout_Layout_sls : syn_type) } "val";
      "val" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type)))) "Continue" ("__5")) at{ (ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type))) } "0");
      "new_layout" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("val");
      local_dead "val";
      local_dead "__5";
      local_live{ ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type) } "memory";
      local_live{ ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type) } "__15";
      local_live{ RefSynType } "__16";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft16"; (* borrow *)
      "__16" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "vlft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft17" "vlft3"; (* post-assignment *)
      local_live{ (layout_Layout_sls : syn_type) } "__17";
      "__17" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft28" "plft17"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_current_memory_A_loc ["vlft28"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__16"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__17")] (Some (Na1Ord, (use_op_alg' ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)), "__15"))
      ( Goto "_bb7")
      ( Unwind)
     ]>%E $
     <[
     "_bb5" :=
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "residual";
      "residual" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type)))) "Break" ("__5")) at{ (ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) ((layout_Layout_sls : syn_type))) } "0");
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__12";
      "__12" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("residual");
      CallS std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_mutu8_std_collections_TryReserveError_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__12")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb6")
      ( Unwind)
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__12";
      local_dead "residual";
      local_dead "__5";
      local_dead "new_layout";
      Goto "_bb24"
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__17";
      local_dead "__16";
      "__18" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)))) ("__15");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__18")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb8"]) (Goto "_bb20")
     ]>%E $
     <[
     "_bb8" :=
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "ptr";
      "ptr" <-{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } (((EnumData ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)))) "Some" ("__15")) at{ (Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) } "0") at{ (tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) } "0");
      local_live{ (layout_Layout_sls : syn_type) } "old_layout";
      "old_layout" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } (((EnumData ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)))) "Some" ("__15")) at{ (Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) } "0") at{ (tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) } "1");
      local_live{ UnitSynType } "__21";
      local_live{ BoolSynType } "__22";
      "__22" <-{ BoolOp } val_of_bool true;
      if{ BoolOp }: move{ BoolOp } ("__22") then
       Goto "_bb9"
      else
       Goto "_bb14"
     ]>%E $
     <[
     "_bb9" :=
      local_live{ UnitSynType } "__23";
      local_live{ BoolSynType } "__24";
      local_live{ (IntSynType USize) } "__25";
      local_live{ RefSynType } "__26";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__26" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft4" } ("old_layout");
      annot{ 1 }: CopyLftNameAnnot "plft18" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft29" "plft18"; (* function_call *)
      CallS layout_Layout_align_loc ["vlft29"] [] [@{expr} move{ RefOp } ("__26")] (Some (Na1Ord, (IntOp USize), "__25"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb10")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__26";
      local_live{ (IntSynType USize) } "__27";
      local_live{ RefSynType } "__28";
      annot{ 1 }: StartLftAnnot "llft5" ["_flft"]; (* borrow *)
      "__28" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft5" } ("new_layout");
      annot{ 1 }: CopyLftNameAnnot "plft19" "llft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft30" "plft19"; (* function_call *)
      CallS layout_Layout_align_loc ["vlft30"] [] [@{expr} move{ RefOp } ("__28")] (Some (Na1Ord, (IntOp USize), "__27"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb11")
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__28";
      "__24" <-{ BoolOp } (move{ (IntOp USize) } ("__25")) = { (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__27"));
      if{ BoolOp }: move{ BoolOp } ("__24") then
       Goto "_bb12"
      else
       Goto "_bb13"
     ]>%E $
     <[
     "_bb12" :=
      local_dead "__27";
      local_dead "__25";
      "__23" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__24";
      local_dead "__23";
      "__21" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb15"
     ]>%E $
     <[
     "_bb13" :=
      local_dead "__27";
      local_dead "__25";
      local_live{ NeverSynType } "__29";
      CallS panic_shim_loc [] [] [@{expr} ] None
      ( StuckS)
      ( Unwind)
     ]>%E $
     <[
     "_bb14" :=
      "__21" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb15"
     ]>%E $
     <[
     "_bb15" :=
      local_dead "__22";
      local_dead "__21";
      local_live{ UnitSynType } "__30";
      local_live{ BoolSynType } "__31";
      local_live{ (IntSynType USize) } "__32";
      local_live{ RefSynType } "__33";
      annot{ 1 }: StartLftAnnot "llft7" ["_flft"]; (* borrow *)
      "__33" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft7" } ("old_layout");
      annot{ 1 }: CopyLftNameAnnot "plft20" "llft7"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft31" "plft20"; (* function_call *)
      CallS layout_Layout_align_loc ["vlft31"] [] [@{expr} move{ RefOp } ("__33")] (Some (Na1Ord, (IntOp USize), "__32"))
      ( annot{ 2 }: EndLftAnnot "llft7"; (* endlft *)
       Goto "_bb16")
      ( annot{ 2 }: EndLftAnnot "llft7"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb16" :=
      local_dead "__33";
      local_live{ (IntSynType USize) } "__34";
      local_live{ RefSynType } "__35";
      annot{ 1 }: StartLftAnnot "llft8" ["_flft"]; (* borrow *)
      "__35" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft8" } ("new_layout");
      annot{ 1 }: CopyLftNameAnnot "plft21" "llft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft32" "plft21"; (* function_call *)
      CallS layout_Layout_align_loc ["vlft32"] [] [@{expr} move{ RefOp } ("__35")] (Some (Na1Ord, (IntOp USize), "__34"))
      ( annot{ 2 }: EndLftAnnot "llft8"; (* endlft *)
       Goto "_bb17")
      ( annot{ 2 }: EndLftAnnot "llft8"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb17" :=
      local_dead "__35";
      "__31" <-{ BoolOp } (move{ (IntOp USize) } ("__32")) = { (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__34"));
      local_dead "__34";
      local_dead "__32";
      CallS raw_vec_assert_unchecked_loc [] [] [@{expr} move{ BoolOp } ("__31")] (Some (Na1Ord, (StructOp unit_sl []), "__30"))
      ( Goto "_bb18")
      ( Unwind)
     ]>%E $
     <[
     "_bb18" :=
      local_dead "__31";
      local_dead "__30";
      local_live{ RefSynType } "__36";
      local_live{ RefSynType } "__37";
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft16"; (* borrow *)
      "__37" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft9" } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "alloc");
      annot{ 1 }: CopyLftNameAnnot "plft23" "vlft9"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft23"; (* borrow *)
      "__36" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft10" } (!{ RefOp } ( "__37" ));
      annot{ 1 }: CopyLftNameAnnot "plft22" "vlft10"; (* post-assignment *)
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "__38";
      "__38" <-{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("ptr");
      local_live{ (layout_Layout_sls : syn_type) } "__39";
      "__39" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("old_layout");
      local_live{ (layout_Layout_sls : syn_type) } "__40";
      "__40" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("new_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft33" "plft22"; (* function_call *)
      CallS allocation_grow_raw_A_loc ["vlft33"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__36"); move{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("__38"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__39"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__40")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)), "memory"))
      ( Goto "_bb19")
      ( Unwind)
     ]>%E $
     <[
     "_bb19" :=
      local_dead "__40";
      local_dead "__39";
      local_dead "__38";
      local_dead "__37";
      local_dead "__36";
      local_dead "old_layout";
      local_dead "ptr";
      local_dead "__15";
      Goto "_bb22"
     ]>%E $
     <[
     "_bb20" :=
      local_dead "__15";
      local_live{ RefSynType } "__41";
      local_live{ RefSynType } "__42";
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft16"; (* borrow *)
      "__42" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft11" } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "alloc");
      annot{ 1 }: CopyLftNameAnnot "plft25" "vlft11"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft25"; (* borrow *)
      "__41" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft12" } (!{ RefOp } ( "__42" ));
      annot{ 1 }: CopyLftNameAnnot "plft24" "vlft12"; (* post-assignment *)
      local_live{ (layout_Layout_sls : syn_type) } "__43";
      "__43" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("new_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft34" "plft24"; (* function_call *)
      CallS allocation_allocate_raw_A_loc ["vlft34"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__41"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__43")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)), "memory"))
      ( Goto "_bb21")
      ( Unwind)
     ]>%E $
     <[
     "_bb21" :=
      local_dead "__43";
      local_dead "__42";
      local_dead "__41";
      Goto "_bb22"
     ]>%E $
     <[
     "_bb22" :=
      local_live{ ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type) } "__44";
      "__44" <-{ (use_op_alg' ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)) } copy{ (use_op_alg' ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)) } ("memory");
      local_live{ ((tuple1_sls (RefSynType)) : syn_type) } "__45";
      local_live{ RefSynType } "__46";
      annot{ 1 }: StartLftAnnot "llft13" ["_flft"]; (* borrow *)
      "__46" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft13" } ("new_layout");
      annot{ 1 }: CopyLftNameAnnot "plft27" "llft13"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft14" "plft27"; (* rvalue *)
      "__45" <-{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } StructInit (tuple1_sls (RefSynType)) [("0", move{ RefOp } ("__46") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft26" "vlft14"; (* post-assignment *)
      local_dead "__46";
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft26"; (* function_call *)
      CallS Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveError_closuresrcraw_vecrs6361363616_loc ["vlft15"] [RSTTyVar "A"] [@{expr} move{ (use_op_alg' ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)) } ("__44"); move{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } ("__45")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft13"; (* endlft *)
       Goto "_bb23")
      ( annot{ 2 }: EndLftAnnot "llft13"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb23" :=
      local_dead "__45";
      local_dead "__44";
      local_dead "memory";
      local_dead "new_layout";
      Goto "_bb24"
     ]>%E $
     <[
     "_bb24" :=
      return (move{ (use_op_alg' ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_finish_grow_closure0_def (Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("__1", (use_layout_alg' ((tuple1_sls (RefSynType)) : syn_type)) : layout);
     ("__2", (use_layout_alg' (errors_AllocError_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft1"; (* initialization *)
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__3";
      local_live{ (layout_Layout_sls : syn_type) } "__4";
      "__4" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } (!{ RefOp } ( ("__1") at{ (tuple1_sls (RefSynType)) } "0" ));
      local_live{ UnitSynType } "__5";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      "__3" <-{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } EnumInit errors_TryReserveErrorKind_els "AllocError" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_AllocError_sls [("layout", move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__4") : expr); ("non_exhaustive", move{ (StructOp unit_sl []) } ("__5") : expr)]);
      local_dead "__5";
      local_dead "__4";
      CallS Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__3")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveError_sls : syn_type)), "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      return (move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_from_nonnull_in_def (DropGlue_A_drop_glue_loc: loc) (Tasconvert_IntoU_into_std_ptr_NonNullu8_std_ptr_Uniqueu8_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", (use_layout_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) : layout);
     ("cap", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVecInner_st (A_st)) } "__0";
      local_live{ ((unique_Unique_sls ((IntSynType U8))) : syn_type) } "__4";
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "__5";
      "__5" <-{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("ptr");
      CallS Tasconvert_IntoU_into_std_ptr_NonNullu8_std_ptr_Uniqueu8_loc [] [] [@{expr} move{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("__5")] (Some (Na1Ord, (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)), "__4"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb2")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ A_st } "__7";
      "__7" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      "__0" <-{ (use_op_alg' (RawVecInner_st (A_st))) } StructInit (RawVecInner_sls (A_st)) [("ptr", move{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } ("__4") : expr); ("cap", move{ (IntOp USize) } ("__6") : expr); ("alloc", move{ (use_op_alg' A_st) } ("__7") : expr)];
      local_dead "__7";
      local_dead "__6";
      local_dead "__4";
      return (move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__0"))
     ]>%E $
     <[
     "_bb2" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("alloc")] None
      ( Goto "_bb3")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb3" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_from_raw_parts_in_def (DropGlue_A_drop_glue_loc: loc) (unique_Unique_T_new_unchecked_u8_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout);
     ("cap", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVecInner_st (A_st)) } "__0";
      local_live{ ((unique_Unique_sls ((IntSynType U8))) : syn_type) } "__4";
      local_live{ PtrSynType } "__5";
      "__5" <-{ PtrOp } copy{ PtrOp } ("ptr");
      CallS unique_Unique_T_new_unchecked_u8_loc [] [] [@{expr} move{ PtrOp } ("__5")] (Some (Na1Ord, (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)), "__4"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb2")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ A_st } "__7";
      "__7" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      "__0" <-{ (use_op_alg' (RawVecInner_st (A_st))) } StructInit (RawVecInner_sls (A_st)) [("ptr", move{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } ("__4") : expr); ("cap", move{ (IntOp USize) } ("__6") : expr); ("alloc", move{ (use_op_alg' A_st) } ("__7") : expr)];
      local_dead "__7";
      local_dead "__6";
      local_dead "__4";
      return (move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__0"))
     ]>%E $
     <[
     "_bb2" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("alloc")] None
      ( Goto "_bb3")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb3" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_grow_amortized_def (Option_T_ok_or_usize_std_collections_TryReserveErrorKind_loc: loc) (Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc: loc) (layout_Layout_size_loc: loc) (max_usize_loc: loc) (panic_shim_loc: loc) (raw_vec_implRawVecInnerA_finish_grow_A_loc: loc) (raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc: loc) (raw_vec_min_non_zero_cap_loc: loc) (std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveError_loc: loc) (std_result_ResultTEasTry_branch_usize_std_collections_TryReserveErrorKind_loc: loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc: loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveError_std_collections_TryReserveError_loc: loc) (usize_checked_add_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ NeverSynType } "__15";
      local_live{ (IntSynType ISize) } "__25";
      local_live{ NeverSynType } "__27";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__33";
      local_live{ (IntSynType ISize) } "__46";
      local_live{ NeverSynType } "__48";
      annot{ 1 }: CopyLftNameAnnot "plft8" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__5";
      local_live{ BoolSynType } "__6";
      "__6" <-{ BoolOp } val_of_bool true;
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb1"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb1" :=
      local_live{ UnitSynType } "__7";
      local_live{ BoolSynType } "__8";
      local_live{ (IntSynType USize) } "__9";
      "__9" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      "__8" <-{ BoolOp } (move{ (IntOp USize) } ("__9")) >{ (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__8") then
       Goto "_bb2"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__9";
      "__7" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__8";
      local_dead "__7";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__9";
      local_live{ NeverSynType } "__10";
      CallS panic_shim_loc [] [] [@{expr} ] None
      ( StuckS)
      ( Unwind)
     ]>%E $
     <[
     "_bb4" :=
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__6";
      local_dead "__5";
      local_live{ UnitSynType } "__11";
      local_live{ BoolSynType } "__12";
      local_live{ (IntSynType USize) } "__13";
      local_live{ RefSynType } "__14";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__14" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft4" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft13" "plft9"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft13"] [] [@{expr} move{ RefOp } ("__14")] (Some (Na1Ord, (IntOp USize), "__13"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb6")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__14";
      "__12" <-{ BoolOp } (move{ (IntOp USize) } ("__13")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__12") then
       Goto "_bb7"
      else
       Goto "_bb9"
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__13";
      local_live{ (errors_TryReserveError_sls : syn_type) } "__16";
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__17";
      "__17" <-{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } EnumInit errors_TryReserveErrorKind_els "CapacityOverflow" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_CapacityOverflow_sls []);
      CallS Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__17")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveError_sls : syn_type)), "__16"))
      ( Goto "_bb8")
      ( Unwind)
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__17";
      "__0" <-{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTUnit; RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Err_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__16") : expr)]);
      local_dead "__16";
      local_dead "__12";
      local_dead "__11";
      Goto "_bb29"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__13";
      "__11" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__12";
      local_dead "__11";
      local_live{ (IntSynType USize) } "required_cap";
      local_live{ ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize))) : syn_type) } "__19";
      local_live{ ((Result_els ((IntSynType USize)) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type) } "__20";
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__21";
      local_live{ (IntSynType USize) } "__22";
      "__22" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__23";
      "__23" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      CallS usize_checked_add_loc [] [] [@{expr} move{ (IntOp USize) } ("__22"); move{ (IntOp USize) } ("__23")] (Some (Na1Ord, (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)), "__21"))
      ( Goto "_bb10")
      ( Unwind)
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__23";
      local_dead "__22";
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__24";
      "__24" <-{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } EnumInit errors_TryReserveErrorKind_els "CapacityOverflow" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_CapacityOverflow_sls []);
      CallS Option_T_ok_or_usize_std_collections_TryReserveErrorKind_loc [] [] [@{expr} move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__21"); move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__24")] (Some (Na1Ord, (use_op_alg' ((Result_els ((IntSynType USize)) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)), "__20"))
      ( Goto "_bb11")
      ( Unwind)
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__24";
      local_dead "__21";
      CallS std_result_ResultTEasTry_branch_usize_std_collections_TryReserveErrorKind_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els ((IntSynType USize)) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ("__20")] (Some (Na1Ord, (use_op_alg' ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize))) : syn_type)), "__19"))
      ( Goto "_bb12")
      ( Unwind)
     ]>%E $
     <[
     "_bb12" :=
      local_dead "__20";
      "__25" <-{ (IntOp ISize) } EnumDiscriminant ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize)))) ("__19");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__25")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb14"; Goto "_bb15"]) (Goto "_bb13")
     ]>%E $
     <[
     "_bb13" :=
      StuckS
     ]>%E $
     <[
     "_bb14" :=
      local_live{ (IntSynType USize) } "val";
      "val" <-{ (IntOp USize) } copy{ (IntOp USize) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize)))) "Continue" ("__19")) at{ (ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize))) } "0");
      "required_cap" <-{ (IntOp USize) } copy{ (IntOp USize) } ("val");
      local_dead "val";
      local_dead "__19";
      local_live{ (IntSynType USize) } "cap";
      local_live{ (IntSynType USize) } "__31";
      local_live{ (IntSynType USize) } "__32";
      "__32" <-{ (IntOp USize) } copy{ (IntOp USize) } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "cap");
      "__33" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ (IntOp USize) } ("__32")) ×{ (IntOp USize) , (IntOp USize) } (i2v (2) USize) : expr); ("1", (copy{ (IntOp USize) } ("__32")) ×c{ (IntOp USize) , (IntOp USize) } (i2v (2) USize) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__33") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb17"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( Unwind)
     ]>%E $
     <[
     "_bb15" :=
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type) } "residual";
      "residual" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize)))) "Break" ("__19")) at{ (ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize))) } "0");
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type) } "__28";
      "__28" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ("residual");
      CallS std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ("__28")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb16")
      ( Unwind)
     ]>%E $
     <[
     "_bb16" :=
      local_dead "__28";
      local_dead "residual";
      local_dead "__19";
      Goto "_bb28"
     ]>%E $
     <[
     "_bb17" :=
      "__31" <-{ (IntOp USize) } move{ (IntOp USize) } (("__33") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__32";
      local_live{ (IntSynType USize) } "__34";
      "__34" <-{ (IntOp USize) } copy{ (IntOp USize) } ("required_cap");
      CallS max_usize_loc [] [] [@{expr} move{ (IntOp USize) } ("__31"); move{ (IntOp USize) } ("__34")] (Some (Na1Ord, (IntOp USize), "cap"))
      ( Goto "_bb18")
      ( Unwind)
     ]>%E $
     <[
     "_bb18" :=
      local_dead "__34";
      local_dead "__31";
      local_live{ (IntSynType USize) } "__35";
      local_live{ (IntSynType USize) } "__36";
      local_live{ (IntSynType USize) } "__37";
      local_live{ RefSynType } "__38";
      annot{ 1 }: StartLftAnnot "llft5" ["_flft"]; (* borrow *)
      "__38" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft5" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft10" "llft5"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft14" "plft10"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft14"] [] [@{expr} move{ RefOp } ("__38")] (Some (Na1Ord, (IntOp USize), "__37"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb19")
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb19" :=
      local_dead "__38";
      CallS raw_vec_min_non_zero_cap_loc [] [] [@{expr} move{ (IntOp USize) } ("__37")] (Some (Na1Ord, (IntOp USize), "__36"))
      ( Goto "_bb20")
      ( Unwind)
     ]>%E $
     <[
     "_bb20" :=
      local_dead "__37";
      local_live{ (IntSynType USize) } "__39";
      "__39" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      CallS max_usize_loc [] [] [@{expr} move{ (IntOp USize) } ("__36"); move{ (IntOp USize) } ("__39")] (Some (Na1Ord, (IntOp USize), "__35"))
      ( Goto "_bb21")
      ( Unwind)
     ]>%E $
     <[
     "_bb21" :=
      local_dead "__39";
      local_dead "__36";
      local_live{ PtrSynType } "ptr";
      local_live{ ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType)) : syn_type) } "__41";
      local_live{ ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__42";
      local_live{ RefSynType } "__43";
      annot{ 1 }: StartLftAnnot "llft6" ["plft8"]; (* borrow *)
      "__43" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft6" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft11" "llft6"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__44";
      "__44" <-{ (IntOp USize) } copy{ (IntOp USize) } ("__35");
      local_live{ (layout_Layout_sls : syn_type) } "__45";
      "__45" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft11"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_finish_grow_A_loc ["vlft15"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__43"); move{ (IntOp USize) } ("__44"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__45")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__42"))
      ( annot{ 2 }: EndLftAnnot "llft6"; (* endlft *)
       Goto "_bb22")
      ( annot{ 2 }: EndLftAnnot "llft6"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb22" :=
      local_dead "__45";
      local_dead "__44";
      local_dead "__43";
      CallS std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__42")] (Some (Na1Ord, (use_op_alg' ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType)) : syn_type)), "__41"))
      ( Goto "_bb23")
      ( Unwind)
     ]>%E $
     <[
     "_bb23" :=
      local_dead "__42";
      "__46" <-{ (IntOp ISize) } EnumDiscriminant ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType))) ("__41");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__46")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb24"; Goto "_bb25"]) (Goto "_bb13")
     ]>%E $
     <[
     "_bb24" :=
      local_live{ PtrSynType } "__50";
      "__50" <-{ PtrOp } copy{ PtrOp } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType))) "Continue" ("__41")) at{ (ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType)) } "0");
      "ptr" <-{ PtrOp } copy{ PtrOp } ("__50");
      local_dead "__50";
      local_dead "__41";
      local_live{ UnitSynType } "__51";
      local_live{ RefSynType } "__52";
      annot{ 1 }: StartLftAnnot "llft7" ["plft8"]; (* borrow *)
      "__52" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft7" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft12" "llft7"; (* post-assignment *)
      local_live{ PtrSynType } "__53";
      "__53" <-{ PtrOp } copy{ PtrOp } ("ptr");
      local_live{ (IntSynType USize) } "__54";
      "__54" <-{ (IntOp USize) } copy{ (IntOp USize) } ("__35");
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft12"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc ["vlft16"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__52"); move{ PtrOp } ("__53"); move{ (IntOp USize) } ("__54")] (Some (Na1Ord, (StructOp unit_sl []), "__51"))
      ( annot{ 2 }: EndLftAnnot "llft7"; (* endlft *)
       Goto "_bb27")
      ( annot{ 2 }: EndLftAnnot "llft7"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb25" :=
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__47";
      "__47" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType))) "Break" ("__41")) at{ (ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType)) } "0");
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__49";
      "__49" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__47");
      CallS std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveError_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__49")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb26")
      ( Unwind)
     ]>%E $
     <[
     "_bb26" :=
      local_dead "__49";
      local_dead "__47";
      local_dead "__41";
      local_dead "ptr";
      local_dead "__35";
      local_dead "cap";
      Goto "_bb28"
     ]>%E $
     <[
     "_bb27" :=
      local_dead "__54";
      local_dead "__53";
      local_dead "__52";
      local_dead "__51";
      local_live{ UnitSynType } "__55";
      "__55" <-{ (StructOp unit_sl []) } zst_val;
      "__0" <-{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTUnit; RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (StructOp unit_sl []) } ("__55") : expr)]);
      local_dead "__55";
      local_dead "ptr";
      local_dead "__35";
      local_dead "cap";
      local_dead "required_cap";
      Goto "_bb29"
     ]>%E $
     <[
     "_bb28" :=
      local_dead "required_cap";
      Goto "_bb29"
     ]>%E $
     <[
     "_bb29" :=
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_grow_exact_def (Option_T_ok_or_usize_std_collections_TryReserveErrorKind_loc: loc) (Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc: loc) (layout_Layout_size_loc: loc) (raw_vec_implRawVecInnerA_finish_grow_A_loc: loc) (raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc: loc) (std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveError_loc: loc) (std_result_ResultTEasTry_branch_usize_std_collections_TryReserveErrorKind_loc: loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc: loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveError_std_collections_TryReserveError_loc: loc) (usize_checked_add_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ NeverSynType } "__9";
      local_live{ (IntSynType ISize) } "__19";
      local_live{ NeverSynType } "__21";
      local_live{ (IntSynType ISize) } "__30";
      local_live{ NeverSynType } "__32";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__5";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType USize) } "__7";
      local_live{ RefSynType } "__8";
      annot{ 1 }: StartLftAnnot "llft3" ["_flft"]; (* borrow *)
      "__8" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft3" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft7"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft10"] [] [@{expr} move{ RefOp } ("__8")] (Some (Na1Ord, (IntOp USize), "__7"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__8";
      "__6" <-{ BoolOp } (move{ (IntOp USize) } ("__7")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb2"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__7";
      local_live{ (errors_TryReserveError_sls : syn_type) } "__10";
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__11";
      "__11" <-{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } EnumInit errors_TryReserveErrorKind_els "CapacityOverflow" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_CapacityOverflow_sls []);
      CallS Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__11")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveError_sls : syn_type)), "__10"))
      ( Goto "_bb3")
      ( Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__11";
      "__0" <-{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTUnit; RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Err_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__10") : expr)]);
      local_dead "__10";
      local_dead "__6";
      local_dead "__5";
      Goto "_bb19"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__7";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__6";
      local_dead "__5";
      local_live{ (IntSynType USize) } "cap";
      local_live{ ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize))) : syn_type) } "__13";
      local_live{ ((Result_els ((IntSynType USize)) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type) } "__14";
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__15";
      local_live{ (IntSynType USize) } "__16";
      "__16" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__17";
      "__17" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      CallS usize_checked_add_loc [] [] [@{expr} move{ (IntOp USize) } ("__16"); move{ (IntOp USize) } ("__17")] (Some (Na1Ord, (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)), "__15"))
      ( Goto "_bb5")
      ( Unwind)
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__17";
      local_dead "__16";
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__18";
      "__18" <-{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } EnumInit errors_TryReserveErrorKind_els "CapacityOverflow" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_CapacityOverflow_sls []);
      CallS Option_T_ok_or_usize_std_collections_TryReserveErrorKind_loc [] [] [@{expr} move{ (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)) } ("__15"); move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__18")] (Some (Na1Ord, (use_op_alg' ((Result_els ((IntSynType USize)) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)), "__14"))
      ( Goto "_bb6")
      ( Unwind)
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__18";
      local_dead "__15";
      CallS std_result_ResultTEasTry_branch_usize_std_collections_TryReserveErrorKind_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els ((IntSynType USize)) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ("__14")] (Some (Na1Ord, (use_op_alg' ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize))) : syn_type)), "__13"))
      ( Goto "_bb7")
      ( Unwind)
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__14";
      "__19" <-{ (IntOp ISize) } EnumDiscriminant ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize)))) ("__13");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__19")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb9"; Goto "_bb10"]) (Goto "_bb8")
     ]>%E $
     <[
     "_bb8" :=
      StuckS
     ]>%E $
     <[
     "_bb9" :=
      local_live{ (IntSynType USize) } "val";
      "val" <-{ (IntOp USize) } copy{ (IntOp USize) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize)))) "Continue" ("__13")) at{ (ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize))) } "0");
      "cap" <-{ (IntOp USize) } copy{ (IntOp USize) } ("val");
      local_dead "val";
      local_dead "__13";
      local_live{ PtrSynType } "ptr";
      local_live{ ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType)) : syn_type) } "__25";
      local_live{ ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__26";
      local_live{ RefSynType } "__27";
      annot{ 1 }: StartLftAnnot "llft4" ["plft6"]; (* borrow *)
      "__27" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft4"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__28";
      "__28" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ (layout_Layout_sls : syn_type) } "__29";
      "__29" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft8"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_finish_grow_A_loc ["vlft11"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__27"); move{ (IntOp USize) } ("__28"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__29")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__26"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb12")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb10" :=
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type) } "residual";
      "residual" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize)))) "Break" ("__13")) at{ (ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) ((IntSynType USize))) } "0");
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type) } "__22";
      "__22" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ("residual");
      CallS std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ("__22")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb11")
      ( Unwind)
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__22";
      local_dead "residual";
      local_dead "__13";
      Goto "_bb18"
     ]>%E $
     <[
     "_bb12" :=
      local_dead "__29";
      local_dead "__28";
      local_dead "__27";
      CallS std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (PtrSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__26")] (Some (Na1Ord, (use_op_alg' ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType)) : syn_type)), "__25"))
      ( Goto "_bb13")
      ( Unwind)
     ]>%E $
     <[
     "_bb13" :=
      local_dead "__26";
      "__30" <-{ (IntOp ISize) } EnumDiscriminant ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType))) ("__25");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__30")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb14"; Goto "_bb15"]) (Goto "_bb8")
     ]>%E $
     <[
     "_bb14" :=
      local_live{ PtrSynType } "__34";
      "__34" <-{ PtrOp } copy{ PtrOp } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType))) "Continue" ("__25")) at{ (ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType)) } "0");
      "ptr" <-{ PtrOp } copy{ PtrOp } ("__34");
      local_dead "__34";
      local_dead "__25";
      local_live{ UnitSynType } "__35";
      local_live{ RefSynType } "__36";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__36" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft5"; (* post-assignment *)
      local_live{ PtrSynType } "__37";
      "__37" <-{ PtrOp } copy{ PtrOp } ("ptr");
      local_live{ (IntSynType USize) } "__38";
      "__38" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft9"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc ["vlft12"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__36"); move{ PtrOp } ("__37"); move{ (IntOp USize) } ("__38")] (Some (Na1Ord, (StructOp unit_sl []), "__35"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb17")
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb15" :=
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__31";
      "__31" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType))) "Break" ("__25")) at{ (ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (PtrSynType)) } "0");
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__33";
      "__33" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__31");
      CallS std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveError_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__33")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb16")
      ( Unwind)
     ]>%E $
     <[
     "_bb16" :=
      local_dead "__33";
      local_dead "__31";
      local_dead "__25";
      local_dead "ptr";
      Goto "_bb18"
     ]>%E $
     <[
     "_bb17" :=
      local_dead "__38";
      local_dead "__37";
      local_dead "__36";
      local_dead "__35";
      local_live{ UnitSynType } "__39";
      "__39" <-{ (StructOp unit_sl []) } zst_val;
      "__0" <-{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTUnit; RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (StructOp unit_sl []) } ("__39") : expr)]);
      local_dead "__39";
      local_dead "ptr";
      local_dead "cap";
      Goto "_bb19"
     ]>%E $
     <[
     "_bb18" :=
      local_dead "cap";
      Goto "_bb19"
     ]>%E $
     <[
     "_bb19" :=
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_grow_one_def (raw_vec_handle_error_loc: loc) (raw_vec_implRawVecInnerA_grow_amortized_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ (IntSynType ISize) } "__8";
      local_live{ NeverSynType } "__10";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "cap";
      "cap" <-{ (IntOp USize) } copy{ (IntOp USize) } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "cap");
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__4";
      local_live{ RefSynType } "__5";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__5" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ (layout_Layout_sls : syn_type) } "__7";
      "__7" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_grow_amortized_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__5"); move{ (IntOp USize) } ("__6"); i2v (1) USize; move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__7")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__4"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      "__8" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type)))) ("__4");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__8")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb2" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "err";
      "err" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ((EnumData ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type)))) "Err" ("__4")) at{ (Result_Err_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ NeverSynType } "__11";
      local_live{ (errors_TryReserveError_sls : syn_type) } "__12";
      "__12" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("err");
      CallS raw_vec_handle_error_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__12")] (Some (Na1Ord, NeverOp, "__11"))
      ( StuckS)
      ( Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__4";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "cap";
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_needs_to_grow_def (layout_Layout_size_loc: loc) (raw_vec_implRawVecInnerA_capacity_A_loc: loc) (usize_wrapping_sub_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (IntSynType USize) } "__6";
      local_live{ (IntSynType USize) } "__7";
      local_live{ RefSynType } "__8";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft5"; (* borrow *)
      "__8" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "vlft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft6" "vlft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__9";
      local_live{ RefSynType } "__10";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__10" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft4" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft7"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft8"] [] [@{expr} move{ RefOp } ("__10")] (Some (Na1Ord, (IntOp USize), "__9"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__10";
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft6"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_capacity_A_loc ["vlft9"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__8"); move{ (IntOp USize) } ("__9")] (Some (Na1Ord, (IntOp USize), "__7"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__9";
      local_dead "__8";
      local_live{ (IntSynType USize) } "__11";
      "__11" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      CallS usize_wrapping_sub_loc [] [] [@{expr} move{ (IntOp USize) } ("__7"); move{ (IntOp USize) } ("__11")] (Some (Na1Ord, (IntOp USize), "__6"))
      ( Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__11";
      local_dead "__7";
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__5")) >{ (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__6"));
      local_dead "__6";
      local_dead "__5";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_non_null_def (unique_Unique_T_as_non_null_ptr_T_loc: loc) (unique_Unique_T_cast_u8_T_loc: loc) (A_st: syn_type) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((nonnull_NonNull_sls (T_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ ((unique_Unique_sls (T_st)) : syn_type) } "__2";
      local_live{ ((unique_Unique_sls ((IntSynType U8))) : syn_type) } "__3";
      "__3" <-{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "ptr");
      CallS unique_Unique_T_cast_u8_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } ("__3")] (Some (Na1Ord, (use_op_alg' ((unique_Unique_sls (T_st)) : syn_type)), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      CallS unique_Unique_T_as_non_null_ptr_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' ((unique_Unique_sls (T_st)) : syn_type)) } ("__2")] (Some (Na1Ord, (use_op_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)), "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__2";
      return (move{ (use_op_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_ptr_def (nonnull_NonNull_T_as_ptr_T_loc: loc) (raw_vec_implRawVecInnerA_non_null_A_T_loc: loc) (A_st: syn_type) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ PtrSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ ((nonnull_NonNull_sls (T_st)) : syn_type) } "__2";
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft4"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "vlft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_non_null_A_T_loc ["vlft6"] [RSTTyVar "A"; RSTTyVar "T"] [@{expr} move{ RefOp } ("__3")] (Some (Na1Ord, (use_op_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      CallS nonnull_NonNull_T_as_ptr_T_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)) } ("__2")] (Some (Na1Ord, PtrOp, "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__2";
      return (move{ PtrOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_reserve_def (raw_vec_implRawVecInnerA_needs_to_grow_A_loc: loc) (raw_vec_implRawVecInnerA_reserve_do_reserve_and_handle_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_1"; (* initialization *)
      local_live{ BoolSynType } "__5";
      local_live{ RefSynType } "__6";
      annot{ 1 }: StartLftAnnot "llft3" ["plft5"]; (* borrow *)
      "__6" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft6" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__9";
      "__9" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft6"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_needs_to_grow_A_loc ["vlft8"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__6"); move{ (IntOp USize) } ("__7"); move{ (IntOp USize) } ("__8"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__9")] (Some (Na1Ord, BoolOp, "__5"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      if{ BoolOp }: move{ BoolOp } ("__5") then
       Goto "_bb2"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      local_live{ UnitSynType } "__10";
      local_live{ RefSynType } "__11";
      annot{ 1 }: StartLftAnnot "llft4" ["plft5"]; (* borrow *)
      "__11" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft4"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__12";
      "__12" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__13";
      "__13" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__14";
      "__14" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft7"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_reserve_do_reserve_and_handle_A_loc ["vlft9"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__11"); move{ (IntOp USize) } ("__12"); move{ (IntOp USize) } ("__13"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__14")] (Some (Na1Ord, (StructOp unit_sl []), "__10"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb3")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__14";
      local_dead "__13";
      local_dead "__12";
      local_dead "__11";
      local_dead "__10";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__5";
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_reserve_do_reserve_and_handle_def (raw_vec_handle_error_loc: loc) (raw_vec_implRawVecInnerA_grow_amortized_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("slf", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ (IntSynType ISize) } "__10";
      local_live{ NeverSynType } "__12";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__5";
      local_live{ RefSynType } "__6";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__6" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "slf" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__9";
      "__9" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_grow_amortized_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__6"); move{ (IntOp USize) } ("__7"); move{ (IntOp USize) } ("__8"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__9")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__5"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      "__10" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type)))) ("__5");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__10")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb2" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "err";
      "err" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ((EnumData ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type)))) "Err" ("__5")) at{ (Result_Err_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ NeverSynType } "__13";
      local_live{ (errors_TryReserveError_sls : syn_type) } "__14";
      "__14" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("err");
      CallS raw_vec_handle_error_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__14")] (Some (Na1Ord, NeverOp, "__13"))
      ( StuckS)
      ( Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_reserve_exact_def (raw_vec_handle_error_loc: loc) (raw_vec_implRawVecInnerA_try_reserve_exact_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ (IntSynType ISize) } "__10";
      local_live{ NeverSynType } "__12";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__5";
      local_live{ RefSynType } "__6";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__6" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__9";
      "__9" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_try_reserve_exact_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__6"); move{ (IntOp USize) } ("__7"); move{ (IntOp USize) } ("__8"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__9")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__5"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      "__10" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type)))) ("__5");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__10")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb2" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "err";
      "err" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ((EnumData ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type)))) "Err" ("__5")) at{ (Result_Err_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ NeverSynType } "__13";
      local_live{ (errors_TryReserveError_sls : syn_type) } "__14";
      "__14" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("err");
      CallS raw_vec_handle_error_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__14")] (Some (Na1Ord, NeverOp, "__13"))
      ( StuckS)
      ( Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_set_ptr_and_cap_def (unique_Unique_T_new_unchecked_u8_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("ptr", void* : layout);
     ("cap", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ ((unique_Unique_sls ((IntSynType U8))) : syn_type) } "__4";
      local_live{ PtrSynType } "__5";
      "__5" <-{ PtrOp } copy{ PtrOp } ("ptr");
      CallS unique_Unique_T_new_unchecked_u8_loc [] [] [@{expr} move{ PtrOp } ("__5")] (Some (Na1Ord, (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)), "__4"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      (!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "ptr" <-{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } move{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } ("__4");
      local_dead "__4";
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      (!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "cap" <-{ (IntOp USize) } move{ (IntOp USize) } ("__6");
      local_dead "__6";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_shrink_def (layout_Layout_size_loc: loc) (panic_shim_loc: loc) (raw_vec_implRawVecInnerA_capacity_A_loc: loc) (raw_vec_implRawVecInnerA_shrink_unchecked_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("cap", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__4";
      local_live{ BoolSynType } "__5";
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ (IntSynType USize) } "__7";
      local_live{ RefSynType } "__8";
      annot{ 1 }: StartLftAnnot "llft3" ["plft7"]; (* borrow *)
      "__8" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__9";
      local_live{ RefSynType } "__10";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__10" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft4" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft9"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft11"] [] [@{expr} move{ RefOp } ("__10")] (Some (Na1Ord, (IntOp USize), "__9"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__10";
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft8"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_capacity_A_loc ["vlft12"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__8"); move{ (IntOp USize) } ("__9")] (Some (Na1Ord, (IntOp USize), "__7"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__9";
      local_dead "__8";
      "__5" <-{ BoolOp } (move{ (IntOp USize) } ("__6")) ≤{ (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__7"));
      if{ BoolOp }: move{ BoolOp } ("__5") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__7";
      local_dead "__6";
      "__4" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__5";
      local_dead "__4";
      local_live{ RefSynType } "__12";
      annot{ 1 }: StartLftAnnot "llft5" ["plft7"]; (* borrow *)
      "__12" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft10" "llft5"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__13";
      "__13" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ (layout_Layout_sls : syn_type) } "__14";
      "__14" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft13" "plft10"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_shrink_unchecked_A_loc ["vlft13"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__12"); move{ (IntOp USize) } ("__13"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__14")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb5")
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__7";
      local_dead "__6";
      local_live{ NeverSynType } "__11";
      CallS panic_shim_loc [] [] [@{expr} ] None
      ( StuckS)
      ( Unwind)
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__14";
      local_dead "__13";
      local_dead "__12";
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_shrink_to_fit_def (raw_vec_handle_error_loc: loc) (raw_vec_implRawVecInnerA_shrink_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("cap", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      local_live{ (IntSynType ISize) } "__8";
      local_live{ NeverSynType } "__10";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__4";
      local_live{ RefSynType } "__5";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__5" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ (layout_Layout_sls : syn_type) } "__7";
      "__7" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_shrink_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__5"); move{ (IntOp USize) } ("__6"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__7")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__4"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      "__8" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type)))) ("__4");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__8")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb2" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "err";
      "err" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ((EnumData ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type)))) "Err" ("__4")) at{ (Result_Err_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ NeverSynType } "__11";
      local_live{ (errors_TryReserveError_sls : syn_type) } "__12";
      "__12" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("err");
      CallS raw_vec_handle_error_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__12")] (Some (Na1Ord, NeverOp, "__11"))
      ( StuckS)
      ( Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__4";
      "__0" <-{ (StructOp unit_sl []) } zst_val;
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_shrink_unchecked_def (Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveErrorKind_closuresrcraw_vecrs7182571828_loc: loc) (allocation_deallocate_raw_A_loc: loc) (allocation_shrink_raw_A_loc: loc) (layout_Layout_align_loc: loc) (layout_Layout_from_size_align_unchecked_loc: loc) (layout_Layout_size_loc: loc) (raw_vec_implRawVecInnerA_current_memory_A_loc: loc) (raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc: loc) (std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveErrorKind_loc: loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc: loc) (unique_Unique_T_new_unchecked_u8_loc: loc) (usize_unchecked_mul_loc: loc) (without_provenance_mut_u8_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("cap", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ NeverSynType } "__4";
      local_live{ (IntSynType ISize) } "__11";
      local_live{ (IntSynType ISize) } "__43";
      local_live{ NeverSynType } "__45";
      annot{ 1 }: CopyLftNameAnnot "plft15" "ulft_1"; (* initialization *)
      local_live{ ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type) } "__8";
      local_live{ RefSynType } "__9";
      annot{ 1 }: StartLftAnnot "llft3" ["plft15"]; (* borrow *)
      "__9" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft16" "llft3"; (* post-assignment *)
      local_live{ (layout_Layout_sls : syn_type) } "__10";
      "__10" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft27" "plft16"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_current_memory_A_loc ["vlft27"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__9"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__10")] (Some (Na1Ord, (use_op_alg' ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) : syn_type)), "__8"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__10";
      local_dead "__9";
      "__11" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)))) ("__8");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__11")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb2" :=
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "ptr";
      "ptr" <-{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } (((EnumData ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)))) "Some" ("__8")) at{ (Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) } "0") at{ (tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) } "0");
      local_live{ (layout_Layout_sls : syn_type) } "layout";
      "layout" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } (((EnumData ((Option_els (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type)))) "Some" ("__8")) at{ (Option_Some_sls (((tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) : syn_type))) } "0") at{ (tuple2_sls (((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) ((layout_Layout_sls : syn_type))) } "1");
      local_dead "__8";
      local_live{ UnitSynType } "__12";
      local_live{ BoolSynType } "__13";
      local_live{ (IntSynType USize) } "__14";
      "__14" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      "__13" <-{ BoolOp } (move{ (IntOp USize) } ("__14")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__13") then
       Goto "_bb4"
      else
       Goto "_bb9"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_live{ UnitSynType } "__5";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      "__0" <-{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTUnit; RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (StructOp unit_sl []) } ("__5") : expr)]);
      local_dead "__5";
      Goto "_bb23"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__14";
      local_live{ UnitSynType } "__15";
      local_live{ RefSynType } "__16";
      local_live{ RefSynType } "__17";
      annot{ 1 }: StartLftAnnot "llft4" ["plft15"]; (* borrow *)
      "__17" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "llft4" } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "alloc");
      annot{ 1 }: CopyLftNameAnnot "plft18" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft18"; (* borrow *)
      "__16" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft5" } (!{ RefOp } ( "__17" ));
      annot{ 1 }: CopyLftNameAnnot "plft17" "vlft5"; (* post-assignment *)
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "__18";
      "__18" <-{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("ptr");
      local_live{ (layout_Layout_sls : syn_type) } "__19";
      "__19" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("layout");
      annot{ 1 }: CopyLftNameAnnot "vlft28" "plft17"; (* function_call *)
      CallS allocation_deallocate_raw_A_loc ["vlft28"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__16"); move{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("__18"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__19")] (Some (Na1Ord, (StructOp unit_sl []), "__15"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb5")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__19";
      local_dead "__18";
      local_dead "__17";
      local_dead "__16";
      local_dead "__15";
      local_live{ ((unique_Unique_sls ((IntSynType U8))) : syn_type) } "__20";
      local_live{ PtrSynType } "__21";
      local_live{ (IntSynType USize) } "__22";
      local_live{ RefSynType } "__23";
      annot{ 1 }: StartLftAnnot "llft6" ["_flft"]; (* borrow *)
      "__23" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft6" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft19" "llft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft29" "plft19"; (* function_call *)
      CallS layout_Layout_align_loc ["vlft29"] [] [@{expr} move{ RefOp } ("__23")] (Some (Na1Ord, (IntOp USize), "__22"))
      ( annot{ 2 }: EndLftAnnot "llft6"; (* endlft *)
       Goto "_bb6")
      ( annot{ 2 }: EndLftAnnot "llft6"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__23";
      CallS without_provenance_mut_u8_loc [] [] [@{expr} move{ (IntOp USize) } ("__22")] (Some (Na1Ord, PtrOp, "__21"))
      ( Goto "_bb7")
      ( Unwind)
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__22";
      CallS unique_Unique_T_new_unchecked_u8_loc [] [] [@{expr} move{ PtrOp } ("__21")] (Some (Na1Ord, (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)), "__20"))
      ( Goto "_bb8")
      ( Unwind)
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__21";
      (!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "ptr" <-{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } move{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } ("__20");
      local_dead "__20";
      (!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "cap" <-{ (IntOp USize) } i2v (0) USize;
      "__12" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb22"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__14";
      local_live{ PtrSynType } "__24";
      local_live{ (IntSynType USize) } "new_size";
      local_live{ (IntSynType USize) } "__26";
      local_live{ RefSynType } "__27";
      annot{ 1 }: StartLftAnnot "llft7" ["_flft"]; (* borrow *)
      "__27" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft7" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft20" "llft7"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft30" "plft20"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft30"] [] [@{expr} move{ RefOp } ("__27")] (Some (Na1Ord, (IntOp USize), "__26"))
      ( annot{ 2 }: EndLftAnnot "llft7"; (* endlft *)
       Goto "_bb10")
      ( annot{ 2 }: EndLftAnnot "llft7"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__27";
      local_live{ (IntSynType USize) } "__28";
      "__28" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      CallS usize_unchecked_mul_loc [] [] [@{expr} move{ (IntOp USize) } ("__26"); move{ (IntOp USize) } ("__28")] (Some (Na1Ord, (IntOp USize), "new_size"))
      ( Goto "_bb11")
      ( Unwind)
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__28";
      local_dead "__26";
      local_live{ (layout_Layout_sls : syn_type) } "new_layout";
      local_live{ (IntSynType USize) } "__30";
      "__30" <-{ (IntOp USize) } copy{ (IntOp USize) } ("new_size");
      local_live{ (IntSynType USize) } "__31";
      local_live{ RefSynType } "__32";
      annot{ 1 }: StartLftAnnot "llft8" ["_flft"]; (* borrow *)
      "__32" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft8" } ("layout");
      annot{ 1 }: CopyLftNameAnnot "plft21" "llft8"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft31" "plft21"; (* function_call *)
      CallS layout_Layout_align_loc ["vlft31"] [] [@{expr} move{ RefOp } ("__32")] (Some (Na1Ord, (IntOp USize), "__31"))
      ( annot{ 2 }: EndLftAnnot "llft8"; (* endlft *)
       Goto "_bb12")
      ( annot{ 2 }: EndLftAnnot "llft8"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb12" :=
      local_dead "__32";
      CallS layout_Layout_from_size_align_unchecked_loc [] [] [@{expr} move{ (IntOp USize) } ("__30"); move{ (IntOp USize) } ("__31")] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "new_layout"))
      ( Goto "_bb13")
      ( Unwind)
     ]>%E $
     <[
     "_bb13" :=
      local_dead "__31";
      local_dead "__30";
      local_live{ ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType)) : syn_type) } "__33";
      local_live{ ((Result_els (PtrSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type) } "__34";
      local_live{ ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type) } "__35";
      local_live{ RefSynType } "__36";
      local_live{ RefSynType } "__37";
      annot{ 1 }: StartLftAnnot "llft9" ["plft15"]; (* borrow *)
      "__37" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "llft9" } ((!{ RefOp } ( "self" )) at{ (RawVecInner_sls (A_st)) } "alloc");
      annot{ 1 }: CopyLftNameAnnot "plft23" "llft9"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft23"; (* borrow *)
      "__36" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft10" } (!{ RefOp } ( "__37" ));
      annot{ 1 }: CopyLftNameAnnot "plft22" "vlft10"; (* post-assignment *)
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "__38";
      "__38" <-{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("ptr");
      local_live{ (layout_Layout_sls : syn_type) } "__39";
      "__39" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("layout");
      local_live{ (layout_Layout_sls : syn_type) } "__40";
      "__40" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("new_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft32" "plft22"; (* function_call *)
      CallS allocation_shrink_raw_A_loc ["vlft32"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__36"); move{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("__38"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__39"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__40")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)), "__35"))
      ( annot{ 2 }: EndLftAnnot "llft9"; (* endlft *)
       Goto "_bb14")
      ( annot{ 2 }: EndLftAnnot "llft9"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb14" :=
      local_dead "__40";
      local_dead "__39";
      local_dead "__38";
      local_dead "__36";
      local_live{ ((tuple1_sls (RefSynType)) : syn_type) } "__41";
      local_live{ RefSynType } "__42";
      annot{ 1 }: StartLftAnnot "llft11" ["_flft"]; (* borrow *)
      "__42" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft11" } ("new_layout");
      annot{ 1 }: CopyLftNameAnnot "plft25" "llft11"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft25"; (* rvalue *)
      "__41" <-{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } StructInit (tuple1_sls (RefSynType)) [("0", move{ RefOp } ("__42") : expr)];
      annot{ 1 }: CopyLftNameAnnot "plft24" "vlft12"; (* post-assignment *)
      local_dead "__42";
      annot{ 1 }: CopyLftNameAnnot "vlft13" "plft24"; (* function_call *)
      CallS Result_TE_map_err_mutu8_std_alloc_AllocError_std_collections_TryReserveErrorKind_closuresrcraw_vecrs7182571828_loc ["vlft13"] [RSTTyVar "A"] [@{expr} move{ (use_op_alg' ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)) } ("__35"); move{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } ("__41")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)), "__34"))
      ( annot{ 2 }: EndLftAnnot "llft11"; (* endlft *)
       Goto "_bb15")
      ( annot{ 2 }: EndLftAnnot "llft11"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb15" :=
      local_dead "__41";
      local_dead "__35";
      CallS std_result_ResultTEasTry_branch_mutu8_std_collections_TryReserveErrorKind_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (PtrSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ("__34")] (Some (Na1Ord, (use_op_alg' ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType)) : syn_type)), "__33"))
      ( Goto "_bb16")
      ( Unwind)
     ]>%E $
     <[
     "_bb16" :=
      local_dead "__34";
      "__43" <-{ (IntOp ISize) } EnumDiscriminant ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType))) ("__33");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__43")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb18"; Goto "_bb19"]) (Goto "_bb17")
     ]>%E $
     <[
     "_bb17" :=
      StuckS
     ]>%E $
     <[
     "_bb18" :=
      local_live{ PtrSynType } "val";
      "val" <-{ PtrOp } copy{ PtrOp } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType))) "Continue" ("__33")) at{ (ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType)) } "0");
      "__24" <-{ PtrOp } copy{ PtrOp } ("val");
      local_dead "val";
      local_dead "__37";
      local_dead "__33";
      local_dead "new_layout";
      local_dead "new_size";
      local_live{ UnitSynType } "__48";
      local_live{ RefSynType } "__49";
      annot{ 1 }: StartLftAnnot "llft14" ["plft15"]; (* borrow *)
      "__49" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft14" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft26" "llft14"; (* post-assignment *)
      local_live{ PtrSynType } "__50";
      "__50" <-{ PtrOp } copy{ PtrOp } ("__24");
      local_live{ (IntSynType USize) } "__51";
      "__51" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      annot{ 1 }: CopyLftNameAnnot "vlft33" "plft26"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_set_ptr_and_cap_A_loc ["vlft33"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__49"); move{ PtrOp } ("__50"); move{ (IntOp USize) } ("__51")] (Some (Na1Ord, (StructOp unit_sl []), "__48"))
      ( annot{ 2 }: EndLftAnnot "llft14"; (* endlft *)
       Goto "_bb21")
      ( annot{ 2 }: EndLftAnnot "llft14"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb19" :=
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type) } "residual";
      "residual" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType))) "Break" ("__33")) at{ (ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) (PtrSynType)) } "0");
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type) } "__46";
      "__46" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ("residual");
      CallS std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveErrorKind_els : syn_type))) : syn_type)) } ("__46")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb20")
      ( Unwind)
     ]>%E $
     <[
     "_bb20" :=
      local_dead "__46";
      local_dead "residual";
      local_dead "__37";
      local_dead "__33";
      local_dead "new_layout";
      local_dead "new_size";
      local_dead "__24";
      local_dead "__13";
      local_dead "__12";
      local_dead "layout";
      local_dead "ptr";
      Goto "_bb23"
     ]>%E $
     <[
     "_bb21" :=
      local_dead "__51";
      local_dead "__50";
      local_dead "__49";
      local_dead "__48";
      "__12" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__24";
      Goto "_bb22"
     ]>%E $
     <[
     "_bb22" :=
      local_dead "__13";
      local_dead "__12";
      local_live{ UnitSynType } "__52";
      "__52" <-{ (StructOp unit_sl []) } zst_val;
      "__0" <-{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTUnit; RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (StructOp unit_sl []) } ("__52") : expr)]);
      local_dead "__52";
      local_dead "layout";
      local_dead "ptr";
      Goto "_bb23"
     ]>%E $
     <[
     "_bb23" :=
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_shrink_unchecked_closure0_def (A_st: syn_type) : function :=
  {|
     f_args := [
      ("__1", (use_layout_alg' ((tuple1_sls (RefSynType)) : syn_type)) : layout);
     ("__2", (use_layout_alg' (errors_AllocError_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft7" "ulft1"; (* initialization *)
      local_live{ (layout_Layout_sls : syn_type) } "__3";
      "__3" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } (!{ RefOp } ( ("__1") at{ (tuple1_sls (RefSynType)) } "0" ));
      local_live{ UnitSynType } "__4";
      "__4" <-{ (StructOp unit_sl []) } zst_val;
      "__0" <-{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } EnumInit errors_TryReserveErrorKind_els "AllocError" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_AllocError_sls [("layout", move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__3") : expr); ("non_exhaustive", move{ (StructOp unit_sl []) } ("__4") : expr)]);
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_try_allocate_in_def (DropGlue_A_drop_glue_loc: loc) (Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc: loc) (allocation_allocate_raw_A_loc: loc) (allocation_allocate_zeroed_raw_A_loc: loc) (layout_Layout_alignment_loc: loc) (layout_Layout_size_loc: loc) (raw_vec_implRawVecInnerA_new_in_A_loc: loc) (raw_vec_layout_array_loc: loc) (unique_Unique_T_new_unchecked_u8_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout);
     ("init", (use_layout_alg' raw_vec_AllocInit_st) : layout);
     ("alloc", (use_layout_alg' A_st) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__9";
      local_live{ NeverSynType } "__11";
      local_live{ NeverSynType } "__18";
      local_live{ (IntSynType ISize) } "__24";
      local_live{ (IntSynType ISize) } "__32";
      local_live{ NeverSynType } "__34";
      local_live{ BoolSynType } "__44";
      local_live{ BoolSynType } "__45";
      "__44" <-{ BoolOp } val_of_bool false;
      "__45" <-{ BoolOp } val_of_bool false;
      "__44" <-{ BoolOp } val_of_bool true;
      local_live{ (layout_Layout_sls : syn_type) } "layout";
      local_live{ ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ (layout_Layout_sls : syn_type) } "__8";
      "__8" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      CallS raw_vec_layout_array_loc [] [] [@{expr} move{ (IntOp USize) } ("__7"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__8")] (Some (Na1Ord, (use_op_alg' ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__6"))
      ( Goto "_bb1")
      ( Goto "_bb27")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__8";
      local_dead "__7";
      "__9" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type)))) ("__6");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__9")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      StuckS
     ]>%E $
     <[
     "_bb3" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "__12";
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__13";
      "__13" <-{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } EnumInit errors_TryReserveErrorKind_els "CapacityOverflow" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_CapacityOverflow_sls []);
      CallS Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__13")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveError_sls : syn_type)), "__12"))
      ( Goto "_bb5")
      ( Goto "_bb27")
     ]>%E $
     <[
     "_bb4" :=
      local_live{ (layout_Layout_sls : syn_type) } "__10";
      "__10" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ((EnumData ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type)))) "Ok" ("__6")) at{ (Result_Ok_sls ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) } "0");
      "layout" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__10");
      local_dead "__10";
      local_dead "__6";
      local_live{ UnitSynType } "__14";
      local_live{ BoolSynType } "__15";
      local_live{ (IntSynType USize) } "__16";
      local_live{ RefSynType } "__17";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__17" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft2" } ("layout");
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft14" "plft8"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft14"] [] [@{expr} move{ RefOp } ("__17")] (Some (Na1Ord, (IntOp USize), "__16"))
      ( annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb6")
      ( annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb27")
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__13";
      "__0" <-{ (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []]); RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Err_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__12") : expr)]);
      local_dead "__12";
      local_dead "__6";
      Goto "_bb20"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__17";
      "__15" <-{ BoolOp } (move{ (IntOp USize) } ("__16")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__15") then
       Goto "_bb7"
      else
       Goto "_bb10"
     ]>%E $
     <[
     "_bb7" :=
      local_dead "__16";
      local_live{ (RawVecInner_st (A_st)) } "__19";
      local_live{ A_st } "__20";
      "__44" <-{ BoolOp } val_of_bool false;
      "__45" <-{ BoolOp } val_of_bool true;
      "__20" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      local_live{ (alignment_Alignment_sls : syn_type) } "__21";
      local_live{ RefSynType } "__22";
      annot{ 1 }: StartLftAnnot "llft3" ["_flft"]; (* borrow *)
      "__22" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft3" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft15" "plft9"; (* function_call *)
      CallS layout_Layout_alignment_loc ["vlft15"] [] [@{expr} move{ RefOp } ("__22")] (Some (Na1Ord, (use_op_alg' (alignment_Alignment_sls : syn_type)), "__21"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb8")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb25")
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__22";
      "__45" <-{ BoolOp } val_of_bool false;
      CallS raw_vec_implRawVecInnerA_new_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ (use_op_alg' A_st) } ("__20"); move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__21")] (Some (Na1Ord, (use_op_alg' (RawVecInner_st (A_st))), "__19"))
      ( Goto "_bb9")
      ( Goto "_bb25")
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__21";
      "__45" <-{ BoolOp } val_of_bool false;
      local_dead "__20";
      "__0" <-{ (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []]); RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__19") : expr)]);
      local_dead "__19";
      local_dead "__15";
      local_dead "__14";
      Goto "_bb20"
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__16";
      "__14" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__15";
      local_dead "__14";
      local_live{ ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type) } "result";
      "__24" <-{ (IntOp ISize) } EnumDiscriminant (raw_vec_AllocInit_els) ("init");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__24")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb12"; Goto "_bb11"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb11" :=
      local_live{ RefSynType } "__28";
      local_live{ RefSynType } "__29";
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__29" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "llft4" } ("alloc");
      annot{ 1 }: CopyLftNameAnnot "plft13" "llft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft5" "plft13"; (* borrow *)
      "__28" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft5" } (!{ RefOp } ( "__29" ));
      annot{ 1 }: CopyLftNameAnnot "plft12" "vlft5"; (* post-assignment *)
      local_live{ (layout_Layout_sls : syn_type) } "__30";
      "__30" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("layout");
      annot{ 1 }: CopyLftNameAnnot "vlft16" "plft12"; (* function_call *)
      CallS allocation_allocate_zeroed_raw_A_loc ["vlft16"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__28"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__30")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)), "result"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb14")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb27")
     ]>%E $
     <[
     "_bb12" :=
      local_live{ RefSynType } "__25";
      local_live{ RefSynType } "__26";
      annot{ 1 }: StartLftAnnot "llft6" ["_flft"]; (* borrow *)
      "__26" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "llft6" } ("alloc");
      annot{ 1 }: CopyLftNameAnnot "plft11" "llft6"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft7" "plft11"; (* borrow *)
      "__25" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft7" } (!{ RefOp } ( "__26" ));
      annot{ 1 }: CopyLftNameAnnot "plft10" "vlft7"; (* post-assignment *)
      local_live{ (layout_Layout_sls : syn_type) } "__27";
      "__27" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("layout");
      annot{ 1 }: CopyLftNameAnnot "vlft17" "plft10"; (* function_call *)
      CallS allocation_allocate_raw_A_loc ["vlft17"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__25"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__27")] (Some (Na1Ord, (use_op_alg' ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type))) : syn_type)), "result"))
      ( annot{ 2 }: EndLftAnnot "llft6"; (* endlft *)
       Goto "_bb13")
      ( annot{ 2 }: EndLftAnnot "llft6"; (* endlft *)
       Goto "_bb27")
     ]>%E $
     <[
     "_bb13" :=
      local_dead "__27";
      local_dead "__25";
      local_dead "__26";
      Goto "_bb15"
     ]>%E $
     <[
     "_bb14" :=
      local_dead "__30";
      local_dead "__28";
      local_dead "__29";
      Goto "_bb15"
     ]>%E $
     <[
     "_bb15" :=
      local_live{ PtrSynType } "ptr";
      "__32" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type)))) ("result");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__32")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb17"; Goto "_bb16"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb16" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "__35";
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__36";
      local_live{ (layout_Layout_sls : syn_type) } "__37";
      "__37" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("layout");
      local_live{ UnitSynType } "__38";
      "__38" <-{ (StructOp unit_sl []) } zst_val;
      "__36" <-{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } EnumInit errors_TryReserveErrorKind_els "AllocError" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_AllocError_sls [("layout", move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__37") : expr); ("non_exhaustive", move{ (StructOp unit_sl []) } ("__38") : expr)]);
      local_dead "__38";
      local_dead "__37";
      CallS Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__36")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveError_sls : syn_type)), "__35"))
      ( Goto "_bb18")
      ( Goto "_bb27")
     ]>%E $
     <[
     "_bb17" :=
      local_live{ PtrSynType } "__33";
      "__33" <-{ PtrOp } copy{ PtrOp } ((EnumData ((Result_els (PtrSynType) ((errors_AllocError_sls : syn_type)))) "Ok" ("result")) at{ (Result_Ok_sls (PtrSynType) ((errors_AllocError_sls : syn_type))) } "0");
      "ptr" <-{ PtrOp } copy{ PtrOp } ("__33");
      local_dead "__33";
      local_live{ (RawVecInner_st (A_st)) } "__39";
      local_live{ ((unique_Unique_sls ((IntSynType U8))) : syn_type) } "__40";
      local_live{ PtrSynType } "__41";
      "__41" <-{ PtrOp } copy{ PtrOp } ("ptr");
      CallS unique_Unique_T_new_unchecked_u8_loc [] [] [@{expr} move{ PtrOp } ("__41")] (Some (Na1Ord, (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)), "__40"))
      ( Goto "_bb19")
      ( Goto "_bb27")
     ]>%E $
     <[
     "_bb18" :=
      local_dead "__36";
      "__0" <-{ (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []]); RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Err_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__35") : expr)]);
      local_dead "__35";
      local_dead "ptr";
      local_dead "result";
      Goto "_bb20"
     ]>%E $
     <[
     "_bb19" :=
      local_dead "__41";
      local_live{ (IntSynType USize) } "__42";
      "__42" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ A_st } "__43";
      "__44" <-{ BoolOp } val_of_bool false;
      "__43" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      "__39" <-{ (use_op_alg' (RawVecInner_st (A_st))) } StructInit (RawVecInner_sls (A_st)) [("ptr", move{ (use_op_alg' ((unique_Unique_sls ((IntSynType U8))) : syn_type)) } ("__40") : expr); ("cap", move{ (IntOp USize) } ("__42") : expr); ("alloc", move{ (use_op_alg' A_st) } ("__43") : expr)];
      local_dead "__43";
      local_dead "__42";
      local_dead "__40";
      "__0" <-{ (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []]); RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__39") : expr)]);
      local_dead "__39";
      local_dead "ptr";
      local_dead "result";
      local_dead "layout";
      Goto "_bb21"
     ]>%E $
     <[
     "_bb20" :=
      local_dead "layout";
      if{ BoolOp }: copy{ BoolOp } ("__44") then
       Goto "_bb23"
      else
       Goto "_bb21"
     ]>%E $
     <[
     "_bb21" :=
      return (move{ (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
     <[
     "_bb22" :=
      Unwind
     ]>%E $
     <[
     "_bb23" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("alloc")] None
      ( Goto "_bb21")
      ( Goto "_bb22")
     ]>%E $
     <[
     "_bb24" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("__20")] None
      ( Goto "_bb27")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb25" :=
      if{ BoolOp }: copy{ BoolOp } ("__45") then
       Goto "_bb24"
      else
       Goto "_bb27"
     ]>%E $
     <[
     "_bb26" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("alloc")] None
      ( Goto "_bb22")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb27" :=
      if{ BoolOp }: copy{ BoolOp } ("__44") then
       Goto "_bb26"
      else
       Goto "_bb22"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_try_reserve_def (raw_vec_assert_unchecked_loc: loc) (raw_vec_implRawVecInnerA_grow_amortized_A_loc: loc) (raw_vec_implRawVecInnerA_needs_to_grow_A_loc: loc) (std_result_ResultTEasTry_branch_unit_std_collections_TryReserveError_loc: loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveError_std_collections_TryReserveError_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__18";
      local_live{ NeverSynType } "__20";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__5";
      local_live{ BoolSynType } "__6";
      local_live{ RefSynType } "__7";
      annot{ 1 }: StartLftAnnot "llft3" ["plft6"]; (* borrow *)
      "__7" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__9";
      "__9" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__10";
      "__10" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft7"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_needs_to_grow_A_loc ["vlft10"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__7"); move{ (IntOp USize) } ("__8"); move{ (IntOp USize) } ("__9"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__10")] (Some (Na1Ord, BoolOp, "__6"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb2"
      else
       Goto "_bb9"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__10";
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      local_live{ UnitSynType } "__11";
      local_live{ ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType)) : syn_type) } "__12";
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__13";
      local_live{ RefSynType } "__14";
      annot{ 1 }: StartLftAnnot "llft4" ["plft6"]; (* borrow *)
      "__14" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft4"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__15";
      "__15" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__16";
      "__16" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__17";
      "__17" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft8"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_grow_amortized_A_loc ["vlft11"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__14"); move{ (IntOp USize) } ("__15"); move{ (IntOp USize) } ("__16"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__17")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__13"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb3")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__17";
      local_dead "__16";
      local_dead "__15";
      local_dead "__14";
      CallS std_result_ResultTEasTry_branch_unit_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__13")] (Some (Na1Ord, (use_op_alg' ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType)) : syn_type)), "__12"))
      ( Goto "_bb4")
      ( Unwind)
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__13";
      "__18" <-{ (IntOp ISize) } EnumDiscriminant ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType))) ("__12");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__18")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb6"; Goto "_bb7"]) (Goto "_bb5")
     ]>%E $
     <[
     "_bb5" :=
      StuckS
     ]>%E $
     <[
     "_bb6" :=
      local_live{ UnitSynType } "val";
      "val" <-{ (StructOp unit_sl []) } copy{ (StructOp unit_sl []) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType))) "Continue" ("__12")) at{ (ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType)) } "0");
      "__11" <-{ (StructOp unit_sl []) } copy{ (StructOp unit_sl []) } ("val");
      local_dead "val";
      local_dead "__12";
      local_dead "__11";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb10"
     ]>%E $
     <[
     "_bb7" :=
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "residual";
      "residual" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType))) "Break" ("__12")) at{ (ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType)) } "0");
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__21";
      "__21" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("residual");
      CallS std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveError_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__21")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb8")
      ( Unwind)
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__21";
      local_dead "residual";
      local_dead "__12";
      local_dead "__11";
      local_dead "__6";
      local_dead "__5";
      Goto "_bb13"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__10";
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb10"
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__6";
      local_dead "__5";
      local_live{ UnitSynType } "__23";
      local_live{ BoolSynType } "__24";
      local_live{ BoolSynType } "__25";
      local_live{ RefSynType } "__26";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__26" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft5"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__27";
      "__27" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__28";
      "__28" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__29";
      "__29" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft9"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_needs_to_grow_A_loc ["vlft12"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__26"); move{ (IntOp USize) } ("__27"); move{ (IntOp USize) } ("__28"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__29")] (Some (Na1Ord, BoolOp, "__25"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb11")
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__29";
      local_dead "__28";
      local_dead "__27";
      local_dead "__26";
      "__24" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (move{ BoolOp } ("__25"));
      local_dead "__25";
      CallS raw_vec_assert_unchecked_loc [] [] [@{expr} move{ BoolOp } ("__24")] (Some (Na1Ord, (StructOp unit_sl []), "__23"))
      ( Goto "_bb12")
      ( Unwind)
     ]>%E $
     <[
     "_bb12" :=
      local_dead "__24";
      local_dead "__23";
      local_live{ UnitSynType } "__30";
      "__30" <-{ (StructOp unit_sl []) } zst_val;
      "__0" <-{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTUnit; RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (StructOp unit_sl []) } ("__30") : expr)]);
      local_dead "__30";
      Goto "_bb13"
     ]>%E $
     <[
     "_bb13" :=
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_try_reserve_exact_def (raw_vec_assert_unchecked_loc: loc) (raw_vec_implRawVecInnerA_grow_exact_A_loc: loc) (raw_vec_implRawVecInnerA_needs_to_grow_A_loc: loc) (std_result_ResultTEasTry_branch_unit_std_collections_TryReserveError_loc: loc) (std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveError_std_collections_TryReserveError_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__18";
      local_live{ NeverSynType } "__20";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      local_live{ UnitSynType } "__5";
      local_live{ BoolSynType } "__6";
      local_live{ RefSynType } "__7";
      annot{ 1 }: StartLftAnnot "llft3" ["plft6"]; (* borrow *)
      "__7" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__9";
      "__9" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__10";
      "__10" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft10" "plft7"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_needs_to_grow_A_loc ["vlft10"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__7"); move{ (IntOp USize) } ("__8"); move{ (IntOp USize) } ("__9"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__10")] (Some (Na1Ord, BoolOp, "__6"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb2"
      else
       Goto "_bb9"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__10";
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      local_live{ UnitSynType } "__11";
      local_live{ ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType)) : syn_type) } "__12";
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__13";
      local_live{ RefSynType } "__14";
      annot{ 1 }: StartLftAnnot "llft4" ["plft6"]; (* borrow *)
      "__14" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft4"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__15";
      "__15" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__16";
      "__16" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__17";
      "__17" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft8"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_grow_exact_A_loc ["vlft11"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__14"); move{ (IntOp USize) } ("__15"); move{ (IntOp USize) } ("__16"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__17")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__13"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb3")
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__17";
      local_dead "__16";
      local_dead "__15";
      local_dead "__14";
      CallS std_result_ResultTEasTry_branch_unit_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__13")] (Some (Na1Ord, (use_op_alg' ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType)) : syn_type)), "__12"))
      ( Goto "_bb4")
      ( Unwind)
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__13";
      "__18" <-{ (IntOp ISize) } EnumDiscriminant ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType))) ("__12");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__18")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb6"; Goto "_bb7"]) (Goto "_bb5")
     ]>%E $
     <[
     "_bb5" :=
      StuckS
     ]>%E $
     <[
     "_bb6" :=
      local_live{ UnitSynType } "val";
      "val" <-{ (StructOp unit_sl []) } copy{ (StructOp unit_sl []) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType))) "Continue" ("__12")) at{ (ControlFlow_Continue_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType)) } "0");
      "__11" <-{ (StructOp unit_sl []) } copy{ (StructOp unit_sl []) } ("val");
      local_dead "val";
      local_dead "__12";
      local_dead "__11";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb10"
     ]>%E $
     <[
     "_bb7" :=
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "residual";
      "residual" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ((EnumData ((ControlFlow_els (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType))) "Break" ("__12")) at{ (ControlFlow_Break_sls (((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) (UnitSynType)) } "0");
      local_live{ ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__21";
      "__21" <-{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("residual");
      CallS std_result_ResultTFasFromResidualstd_result_ResultE_from_residual_unit_std_collections_TryReserveError_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els (NeverSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__21")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb8")
      ( Unwind)
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__21";
      local_dead "residual";
      local_dead "__12";
      local_dead "__11";
      local_dead "__6";
      local_dead "__5";
      Goto "_bb13"
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__10";
      local_dead "__9";
      local_dead "__8";
      local_dead "__7";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb10"
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__6";
      local_dead "__5";
      local_live{ UnitSynType } "__23";
      local_live{ BoolSynType } "__24";
      local_live{ BoolSynType } "__25";
      local_live{ RefSynType } "__26";
      annot{ 1 }: StartLftAnnot "llft5" ["plft6"]; (* borrow *)
      "__26" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft5" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft5"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__27";
      "__27" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__28";
      "__28" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__29";
      "__29" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft9"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_needs_to_grow_A_loc ["vlft12"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__26"); move{ (IntOp USize) } ("__27"); move{ (IntOp USize) } ("__28"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__29")] (Some (Na1Ord, BoolOp, "__25"))
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Goto "_bb11")
      ( annot{ 2 }: EndLftAnnot "llft5"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb11" :=
      local_dead "__29";
      local_dead "__28";
      local_dead "__27";
      local_dead "__26";
      "__24" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (move{ BoolOp } ("__25"));
      local_dead "__25";
      CallS raw_vec_assert_unchecked_loc [] [] [@{expr} move{ BoolOp } ("__24")] (Some (Na1Ord, (StructOp unit_sl []), "__23"))
      ( Goto "_bb12")
      ( Unwind)
     ]>%E $
     <[
     "_bb12" :=
      local_dead "__24";
      local_dead "__23";
      local_live{ UnitSynType } "__30";
      "__30" <-{ (StructOp unit_sl []) } zst_val;
      "__0" <-{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTUnit; RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls (UnitSynType) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (StructOp unit_sl []) } ("__30") : expr)]);
      local_dead "__30";
      Goto "_bb13"
     ]>%E $
     <[
     "_bb13" :=
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_try_shrink_to_fit_def (raw_vec_implRawVecInnerA_shrink_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("cap", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ (layout_Layout_sls : syn_type) } "__6";
      "__6" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_shrink_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__4"); move{ (IntOp USize) } ("__5"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__6")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_try_with_capacity_in_def (raw_vec_implRawVecInnerA_try_allocate_in_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ raw_vec_AllocInit_st } "__5";
      "__5" <-{ (use_op_alg' raw_vec_AllocInit_st) } EnumInit raw_vec_AllocInit_els "Uninitialized" (RSTEnumDef ["raw_vec_AllocInit_enum"] (RSTScopeInst [] [] [])) (StructInit raw_vec_AllocInit_Uninitialized_sls []);
      local_live{ A_st } "__6";
      "__6" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      local_live{ (layout_Layout_sls : syn_type) } "__7";
      "__7" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      CallS raw_vec_implRawVecInnerA_try_allocate_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ (IntOp USize) } ("__4"); move{ (use_op_alg' raw_vec_AllocInit_st) } ("__5"); move{ (use_op_alg' A_st) } ("__6"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__7")] (Some (Na1Ord, (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb1")
      ( Goto "_bb2")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      return (move{ (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
     <[
     "_bb2" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_with_capacity_in_def (drop_glue_RawVecInner_A_loc: loc) (raw_vec_assert_unchecked_loc: loc) (raw_vec_handle_error_loc: loc) (raw_vec_implRawVecInnerA_needs_to_grow_A_loc: loc) (raw_vec_implRawVecInnerA_try_allocate_in_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVecInner_st (A_st)) } "__0";
      local_live{ (IntSynType ISize) } "__9";
      local_live{ BoolSynType } "__20";
      local_live{ BoolSynType } "__21";
      "__21" <-{ BoolOp } val_of_bool false;
      "__20" <-{ BoolOp } val_of_bool false;
      local_live{ ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__4";
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ raw_vec_AllocInit_st } "__6";
      "__6" <-{ (use_op_alg' raw_vec_AllocInit_st) } EnumInit raw_vec_AllocInit_els "Uninitialized" (RSTEnumDef ["raw_vec_AllocInit_enum"] (RSTScopeInst [] [] [])) (StructInit raw_vec_AllocInit_Uninitialized_sls []);
      local_live{ A_st } "__7";
      "__7" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      local_live{ (layout_Layout_sls : syn_type) } "__8";
      "__8" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      CallS raw_vec_implRawVecInnerA_try_allocate_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ (IntOp USize) } ("__5"); move{ (use_op_alg' raw_vec_AllocInit_st) } ("__6"); move{ (use_op_alg' A_st) } ("__7"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__8")] (Some (Na1Ord, (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__4"))
      ( Goto "_bb1")
      ( Goto "_bb8")
     ]>%E $
     <[
     "_bb1" :=
      "__20" <-{ BoolOp } val_of_bool true;
      "__21" <-{ BoolOp } val_of_bool true;
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      "__9" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type)))) ("__4");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__9")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      StuckS
     ]>%E $
     <[
     "_bb3" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "err";
      "err" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ((EnumData ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type)))) "Err" ("__4")) at{ (Result_Err_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ NeverSynType } "__18";
      local_live{ (errors_TryReserveError_sls : syn_type) } "__19";
      "__19" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("err");
      CallS raw_vec_handle_error_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__19")] (Some (Na1Ord, NeverOp, "__18"))
      ( StuckS)
      ( Goto "_bb8")
     ]>%E $
     <[
     "_bb4" :=
      local_live{ (RawVecInner_st (A_st)) } "this";
      "this" <-{ (use_op_alg' (RawVecInner_st (A_st))) } move{ (use_op_alg' (RawVecInner_st (A_st))) } ((EnumData ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type)))) "Ok" ("__4")) at{ (Result_Ok_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ UnitSynType } "__11";
      local_live{ BoolSynType } "__12";
      local_live{ BoolSynType } "__13";
      local_live{ RefSynType } "__14";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__14" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft2" } ("this");
      annot{ 1 }: CopyLftNameAnnot "plft3" "llft2"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__15";
      "__15" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ (layout_Layout_sls : syn_type) } "__16";
      "__16" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft3"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_needs_to_grow_A_loc ["vlft4"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__14"); i2v (0) USize; move{ (IntOp USize) } ("__15"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__16")] (Some (Na1Ord, BoolOp, "__13"))
      ( annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb5")
      ( annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb7")
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__16";
      local_dead "__15";
      local_dead "__14";
      "__12" <-{ BoolOp } UnOp (NotBoolOp) (BoolOp) (move{ BoolOp } ("__13"));
      local_dead "__13";
      CallS raw_vec_assert_unchecked_loc [] [] [@{expr} move{ BoolOp } ("__12")] (Some (Na1Ord, (StructOp unit_sl []), "__11"))
      ( Goto "_bb6")
      ( Goto "_bb7")
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__12";
      local_dead "__11";
      "__0" <-{ (use_op_alg' (RawVecInner_st (A_st))) } move{ (use_op_alg' (RawVecInner_st (A_st))) } ("this");
      local_dead "this";
      "__20" <-{ BoolOp } val_of_bool false;
      "__21" <-{ BoolOp } val_of_bool false;
      local_dead "__4";
      return (move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__0"))
     ]>%E $
     <[
     "_bb7" :=
      CallS drop_glue_RawVecInner_A_loc [] [RSTTyVar "A"] [@{expr} &raw{ PRef, Mut } ("this")] None
      ( Goto "_bb8")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb8" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_with_capacity_zeroed_in_def (raw_vec_handle_error_loc: loc) (raw_vec_implRawVecInnerA_try_allocate_in_A_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVecInner_st (A_st)) } "__0";
      local_live{ (IntSynType ISize) } "__9";
      local_live{ ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__4";
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ raw_vec_AllocInit_st } "__6";
      "__6" <-{ (use_op_alg' raw_vec_AllocInit_st) } EnumInit raw_vec_AllocInit_els "Zeroed" (RSTEnumDef ["raw_vec_AllocInit_enum"] (RSTScopeInst [] [] [])) (StructInit raw_vec_AllocInit_Zeroed_sls []);
      local_live{ A_st } "__7";
      "__7" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      local_live{ (layout_Layout_sls : syn_type) } "__8";
      "__8" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      CallS raw_vec_implRawVecInnerA_try_allocate_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ (IntOp USize) } ("__5"); move{ (use_op_alg' raw_vec_AllocInit_st) } ("__6"); move{ (use_op_alg' A_st) } ("__7"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__8")] (Some (Na1Ord, (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__4"))
      ( Goto "_bb1")
      ( Goto "_bb5")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__8";
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      "__9" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type)))) ("__4");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__9")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      StuckS
     ]>%E $
     <[
     "_bb3" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "err";
      "err" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ((EnumData ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type)))) "Err" ("__4")) at{ (Result_Err_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ NeverSynType } "__12";
      local_live{ (errors_TryReserveError_sls : syn_type) } "__13";
      "__13" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("err");
      CallS raw_vec_handle_error_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__13")] (Some (Na1Ord, NeverOp, "__12"))
      ( StuckS)
      ( Goto "_bb5")
     ]>%E $
     <[
     "_bb4" :=
      local_live{ (RawVecInner_st (A_st)) } "res";
      "res" <-{ (use_op_alg' (RawVecInner_st (A_st))) } move{ (use_op_alg' (RawVecInner_st (A_st))) } ((EnumData ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type)))) "Ok" ("__4")) at{ (Result_Ok_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) } "0");
      "__0" <-{ (use_op_alg' (RawVecInner_st (A_st))) } move{ (use_op_alg' (RawVecInner_st (A_st))) } ("res");
      local_dead "res";
      local_dead "__4";
      return (move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__0"))
     ]>%E $
     <[
     "_bb5" :=
      Unwind
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInner_with_capacity_def (raw_vec_handle_error_loc: loc) (raw_vec_implRawVecInnerA_try_allocate_in_std_alloc_Global_loc: loc) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVecInner_st ((Global_sls : syn_type))) } "__0";
      local_live{ (IntSynType ISize) } "__8";
      local_live{ ((Result_els ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ raw_vec_AllocInit_st } "__5";
      "__5" <-{ (use_op_alg' raw_vec_AllocInit_st) } EnumInit raw_vec_AllocInit_els "Uninitialized" (RSTEnumDef ["raw_vec_AllocInit_enum"] (RSTScopeInst [] [] [])) (StructInit raw_vec_AllocInit_Uninitialized_sls []);
      local_live{ (Global_sls : syn_type) } "__6";
      "__6" <-{ (use_op_alg' (Global_sls : syn_type)) } StructInit Global_sls [];
      local_live{ (layout_Layout_sls : syn_type) } "__7";
      "__7" <-{ (use_op_alg' (layout_Layout_sls : syn_type)) } copy{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("elem_layout");
      CallS raw_vec_implRawVecInnerA_try_allocate_in_std_alloc_Global_loc [] [] [@{expr} move{ (IntOp USize) } ("__4"); move{ (use_op_alg' raw_vec_AllocInit_st) } ("__5"); move{ (use_op_alg' (Global_sls : syn_type)) } ("__6"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__7")] (Some (Na1Ord, (use_op_alg' ((Result_els ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__3"))
      ( Goto "_bb1")
      ( Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      "__8" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type)))) ("__3");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__8")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb4"; Goto "_bb3"]) (Goto "_bb2")
     ]>%E $
     <[
     "_bb2" :=
      StuckS
     ]>%E $
     <[
     "_bb3" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "err";
      "err" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ((EnumData ((Result_els ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type)))) "Err" ("__3")) at{ (Result_Err_sls ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ NeverSynType } "__11";
      local_live{ (errors_TryReserveError_sls : syn_type) } "__12";
      "__12" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("err");
      CallS raw_vec_handle_error_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__12")] (Some (Na1Ord, NeverOp, "__11"))
      ( StuckS)
      ( Unwind)
     ]>%E $
     <[
     "_bb4" :=
      local_live{ (RawVecInner_st ((Global_sls : syn_type))) } "res";
      "res" <-{ (use_op_alg' (RawVecInner_st ((Global_sls : syn_type)))) } move{ (use_op_alg' (RawVecInner_st ((Global_sls : syn_type)))) } ((EnumData ((Result_els ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type)))) "Ok" ("__3")) at{ (Result_Ok_sls ((RawVecInner_st ((Global_sls : syn_type)))) ((errors_TryReserveError_sls : syn_type))) } "0");
      "__0" <-{ (use_op_alg' (RawVecInner_st ((Global_sls : syn_type)))) } move{ (use_op_alg' (RawVecInner_st ((Global_sls : syn_type)))) } ("res");
      local_dead "res";
      local_dead "__3";
      return (move{ (use_op_alg' (RawVecInner_st ((Global_sls : syn_type)))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_allocator_def (raw_vec_implRawVecInnerA_allocator_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ RefSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft6" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__2";
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft6"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "vlft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft8" "vlft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft8"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_allocator_A_loc ["vlft9"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__3")] (Some (Na1Ord, RefOp, "__2"))
      ( annot{ 1 }: CopyLftNameAnnot "plft7" "vlft9"; (* post_function_call (assign) *)
       Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft7"; (* borrow *)
      "__0" <-{ RefOp } &ref{ Shr, Some (RSTTyVar "A"), "vlft4" } (!{ RefOp } ( "__2" ));
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft4"; (* post-assignment *)
      local_dead "__3";
      local_dead "__2";
      annot{ 1 }: ExtendLftAnnot "plft5"; (* return *)
      return (move{ RefOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_capacity_def (mem_size_of_T_loc: loc) (raw_vec_implRawVecInnerA_capacity_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__2";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft4"; (* borrow *)
      "__2" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "vlft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__3";
      CallS mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (IntOp USize), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_capacity_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__2"); move{ (IntOp USize) } ("__3")] (Some (Na1Ord, (IntOp USize), "__0"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__3";
      local_dead "__2";
      return (move{ (IntOp USize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_from_nonnull_in_def (DropGlue_A_drop_glue_loc: loc) (nonnull_NonNull_T_cast_T_u8_loc: loc) (raw_vec_implRawVecInnerA_from_nonnull_in_A_loc: loc) (raw_vec_new_cap_T_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", (use_layout_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)) : layout);
     ("capacity", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVec_st (T_st) (A_st)) } "__0";
      local_live{ BoolSynType } "__13";
      "__13" <-{ BoolOp } val_of_bool false;
      "__13" <-{ BoolOp } val_of_bool true;
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "__4";
      local_live{ ((nonnull_NonNull_sls (T_st)) : syn_type) } "__5";
      "__5" <-{ (use_op_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)) } ("ptr");
      CallS nonnull_NonNull_T_cast_T_u8_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)) } ("__5")] (Some (Na1Ord, (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)), "__4"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb6")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_live{ (IntSynType USize) } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      CallS raw_vec_new_cap_T_loc [] [RSTTyVar "T"] [@{expr} move{ (IntOp USize) } ("__7")] (Some (Na1Ord, (IntOp USize), "__6"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb6")
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__7";
      local_live{ (RawVecInner_st (A_st)) } "__8";
      local_live{ ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type) } "__9";
      "__9" <-{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } copy{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("__4");
      local_live{ (IntSynType USize) } "__10";
      "__10" <-{ (IntOp USize) } copy{ (IntOp USize) } ("__6");
      local_live{ A_st } "__11";
      "__13" <-{ BoolOp } val_of_bool false;
      "__11" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      CallS raw_vec_implRawVecInnerA_from_nonnull_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ (use_op_alg' ((nonnull_NonNull_sls ((IntSynType U8))) : syn_type)) } ("__9"); move{ (IntOp USize) } ("__10"); move{ (use_op_alg' A_st) } ("__11")] (Some (Na1Ord, (use_op_alg' (RawVecInner_st (A_st))), "__8"))
      ( Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb6")
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__11";
      local_dead "__10";
      local_dead "__9";
      local_live{ ((core_marker_PhantomData_sls (T_st)) : syn_type) } "__12";
      "__12" <-{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } StructInit (core_marker_PhantomData_sls (T_st)) [];
      "__0" <-{ (use_op_alg' (RawVec_st (T_st) (A_st))) } StructInit (RawVec_sls (T_st) (A_st)) [("inner", move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__8") : expr); ("_marker", move{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } ("__12") : expr)];
      local_dead "__12";
      local_dead "__8";
      local_dead "__6";
      local_dead "__4";
      return (move{ (use_op_alg' (RawVec_st (T_st) (A_st))) } ("__0"))
     ]>%E $
     <[
     "_bb4" :=
      Unwind
     ]>%E $
     <[
     "_bb5" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("alloc")] None
      ( Goto "_bb4")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb6" :=
      if{ BoolOp }: copy{ BoolOp } ("__13") then
       Goto "_bb5"
      else
       Goto "_bb4"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_from_raw_parts_in_def (DropGlue_A_drop_glue_loc: loc) (mut_ptr_cast_T_u8_loc: loc) (raw_vec_implRawVecInnerA_from_raw_parts_in_A_loc: loc) (raw_vec_new_cap_T_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("ptr", void* : layout);
     ("capacity", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVec_st (T_st) (A_st)) } "__0";
      local_live{ BoolSynType } "__13";
      "__13" <-{ BoolOp } val_of_bool false;
      "__13" <-{ BoolOp } val_of_bool true;
      local_live{ PtrSynType } "__4";
      local_live{ PtrSynType } "__5";
      "__5" <-{ PtrOp } copy{ PtrOp } ("ptr");
      CallS mut_ptr_cast_T_u8_loc [] [RSTTyVar "T"] [@{expr} move{ PtrOp } ("__5")] (Some (Na1Ord, PtrOp, "__4"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb6")
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_live{ (IntSynType USize) } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      CallS raw_vec_new_cap_T_loc [] [RSTTyVar "T"] [@{expr} move{ (IntOp USize) } ("__7")] (Some (Na1Ord, (IntOp USize), "__6"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb6")
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__7";
      local_live{ (RawVecInner_st (A_st)) } "__8";
      local_live{ PtrSynType } "__9";
      "__9" <-{ PtrOp } copy{ PtrOp } ("__4");
      local_live{ (IntSynType USize) } "__10";
      "__10" <-{ (IntOp USize) } copy{ (IntOp USize) } ("__6");
      local_live{ A_st } "__11";
      "__13" <-{ BoolOp } val_of_bool false;
      "__11" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      CallS raw_vec_implRawVecInnerA_from_raw_parts_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ PtrOp } ("__9"); move{ (IntOp USize) } ("__10"); move{ (use_op_alg' A_st) } ("__11")] (Some (Na1Ord, (use_op_alg' (RawVecInner_st (A_st))), "__8"))
      ( Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb6")
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__11";
      local_dead "__10";
      local_dead "__9";
      local_live{ ((core_marker_PhantomData_sls (T_st)) : syn_type) } "__12";
      "__12" <-{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } StructInit (core_marker_PhantomData_sls (T_st)) [];
      "__0" <-{ (use_op_alg' (RawVec_st (T_st) (A_st))) } StructInit (RawVec_sls (T_st) (A_st)) [("inner", move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__8") : expr); ("_marker", move{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } ("__12") : expr)];
      local_dead "__12";
      local_dead "__8";
      local_dead "__6";
      local_dead "__4";
      return (move{ (use_op_alg' (RawVec_st (T_st) (A_st))) } ("__0"))
     ]>%E $
     <[
     "_bb4" :=
      Unwind
     ]>%E $
     <[
     "_bb5" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("alloc")] None
      ( Goto "_bb4")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb6" :=
      if{ BoolOp }: copy{ BoolOp } ("__13") then
       Goto "_bb5"
      else
       Goto "_bb4"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_grow_one_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_grow_one_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__2";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__2" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (layout_Layout_sls : syn_type) } "__3";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__3"))
      ( Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_grow_one_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__2"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__3")] (Some (Na1Ord, (StructOp unit_sl []), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__3";
      local_dead "__2";
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_new_in_def (DropGlue_A_drop_glue_loc: loc) (alignment_Alignment_of_T_loc: loc) (raw_vec_implRawVecInnerA_new_in_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("alloc", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVec_st (T_st) (A_st)) } "__0";
      local_live{ BoolSynType } "__6";
      "__6" <-{ BoolOp } val_of_bool false;
      local_live{ (RawVecInner_st (A_st)) } "__2";
      local_live{ A_st } "__3";
      "__6" <-{ BoolOp } val_of_bool true;
      "__3" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      local_live{ (alignment_Alignment_sls : syn_type) } "__4";
      CallS alignment_Alignment_of_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (alignment_Alignment_sls : syn_type)), "__4"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb5")
     ]>%E $
     <[
     "_bb1" :=
      "__6" <-{ BoolOp } val_of_bool false;
      CallS raw_vec_implRawVecInnerA_new_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ (use_op_alg' A_st) } ("__3"); move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__4")] (Some (Na1Ord, (use_op_alg' (RawVecInner_st (A_st))), "__2"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Goto "_bb5")
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__4";
      "__6" <-{ BoolOp } val_of_bool false;
      local_dead "__3";
      local_live{ ((core_marker_PhantomData_sls (T_st)) : syn_type) } "__5";
      "__5" <-{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } StructInit (core_marker_PhantomData_sls (T_st)) [];
      "__0" <-{ (use_op_alg' (RawVec_st (T_st) (A_st))) } StructInit (RawVec_sls (T_st) (A_st)) [("inner", move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__2") : expr); ("_marker", move{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } ("__5") : expr)];
      local_dead "__5";
      local_dead "__2";
      return (move{ (use_op_alg' (RawVec_st (T_st) (A_st))) } ("__0"))
     ]>%E $
     <[
     "_bb3" :=
      Unwind
     ]>%E $
     <[
     "_bb4" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("__3")] None
      ( Goto "_bb3")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb5" :=
      if{ BoolOp }: copy{ BoolOp } ("__6") then
       Goto "_bb4"
      else
       Goto "_bb3"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_non_null_def (raw_vec_implRawVecInnerA_non_null_A_T_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((nonnull_NonNull_sls (T_st)) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__2";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft4"; (* borrow *)
      "__2" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "vlft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_non_null_A_T_loc ["vlft6"] [RSTTyVar "T"; RSTTyVar "A"] [@{expr} move{ RefOp } ("__2")] (Some (Na1Ord, (use_op_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)), "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__2";
      return (move{ (use_op_alg' ((nonnull_NonNull_sls (T_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_ptr_def (raw_vec_implRawVecInnerA_ptr_A_T_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ PtrSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__2";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft4"; (* borrow *)
      "__2" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "vlft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_ptr_A_T_loc ["vlft6"] [RSTTyVar "T"; RSTTyVar "A"] [@{expr} move{ RefOp } ("__2")] (Some (Na1Ord, PtrOp, "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__2";
      return (move{ PtrOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_reserve_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_reserve_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__7";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__7"))
      ( Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_reserve_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__4"); move{ (IntOp USize) } ("__5"); move{ (IntOp USize) } ("__6"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__7")] (Some (Na1Ord, (StructOp unit_sl []), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_reserve_exact_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_reserve_exact_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__7";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__7"))
      ( Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_reserve_exact_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__4"); move{ (IntOp USize) } ("__5"); move{ (IntOp USize) } ("__6"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__7")] (Some (Na1Ord, (StructOp unit_sl []), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_shrink_to_fit_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_shrink_to_fit_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("cap", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ UnitSynType } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__3" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ (layout_Layout_sls : syn_type) } "__5";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__5"))
      ( Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_shrink_to_fit_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__3"); move{ (IntOp USize) } ("__4"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__5")] (Some (Na1Ord, (StructOp unit_sl []), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      return (move{ (StructOp unit_sl []) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_try_reserve_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_try_reserve_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__7";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__7"))
      ( Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_try_reserve_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__4"); move{ (IntOp USize) } ("__5"); move{ (IntOp USize) } ("__6"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__7")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_try_reserve_exact_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_try_reserve_exact_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("len", (it_layout USize) : layout);
     ("additional", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__4";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__4" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("len");
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("additional");
      local_live{ (layout_Layout_sls : syn_type) } "__7";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__7"))
      ( Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_try_reserve_exact_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__4"); move{ (IntOp USize) } ("__5"); move{ (IntOp USize) } ("__6"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__7")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__7";
      local_dead "__6";
      local_dead "__5";
      local_dead "__4";
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_try_shrink_to_fit_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_try_shrink_to_fit_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("cap", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__3";
      annot{ 1 }: StartLftAnnot "llft3" ["plft4"]; (* borrow *)
      "__3" <-{ RefOp } &ref{ Mut, Some (RSTLitType ["RawVecInner_inv_t"] (RSTScopeInst [] [RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []])), "llft3" } ((!{ RefOp } ( "self" )) at{ (RawVec_sls (T_st) (A_st)) } "inner");
      annot{ 1 }: CopyLftNameAnnot "plft5" "llft3"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      local_live{ (layout_Layout_sls : syn_type) } "__5";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__5"))
      ( Goto "_bb1")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS raw_vec_implRawVecInnerA_try_shrink_to_fit_A_loc ["vlft6"] [RSTTyVar "A"] [@{expr} move{ RefOp } ("__3"); move{ (IntOp USize) } ("__4"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__5")] (Some (Na1Ord, (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb2")
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' ((Result_els (UnitSynType) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_try_with_capacity_in_def (DropGlue_A_drop_glue_loc: loc) (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_try_with_capacity_in_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els ((RawVec_st (T_st) (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__7";
      local_live{ BoolSynType } "__14";
      local_live{ BoolSynType } "__15";
      local_live{ BoolSynType } "__16";
      "__16" <-{ BoolOp } val_of_bool false;
      "__15" <-{ BoolOp } val_of_bool false;
      "__14" <-{ BoolOp } val_of_bool false;
      local_live{ ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ A_st } "__5";
      "__16" <-{ BoolOp } val_of_bool true;
      "__5" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      local_live{ (layout_Layout_sls : syn_type) } "__6";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__6"))
      ( Goto "_bb1")
      ( Goto "_bb9")
     ]>%E $
     <[
     "_bb1" :=
      "__16" <-{ BoolOp } val_of_bool false;
      CallS raw_vec_implRawVecInnerA_try_with_capacity_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ (IntOp USize) } ("__4"); move{ (use_op_alg' A_st) } ("__5"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__6")] (Some (Na1Ord, (use_op_alg' ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__3"))
      ( Goto "_bb2")
      ( Goto "_bb9")
     ]>%E $
     <[
     "_bb2" :=
      "__14" <-{ BoolOp } val_of_bool true;
      "__15" <-{ BoolOp } val_of_bool true;
      local_dead "__6";
      "__16" <-{ BoolOp } val_of_bool false;
      local_dead "__5";
      local_dead "__4";
      "__7" <-{ (IntOp ISize) } EnumDiscriminant ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type)))) ("__3");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__7")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb5"; Goto "_bb4"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb3" :=
      StuckS
     ]>%E $
     <[
     "_bb4" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "e";
      "e" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ((EnumData ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type)))) "Err" ("__3")) at{ (Result_Err_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ (errors_TryReserveError_sls : syn_type) } "__13";
      "__13" <-{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("e");
      "__0" <-{ (use_op_alg' ((Result_els ((RawVec_st (T_st) (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els ((RawVec_st (T_st) (A_st))) ((errors_TryReserveError_sls : syn_type))) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["RawVec_inv_t"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []]); RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Err_sls ((RawVec_st (T_st) (A_st))) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__13") : expr)]);
      local_dead "__13";
      local_dead "e";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb5" :=
      local_live{ (RawVecInner_st (A_st)) } "inner";
      "inner" <-{ (use_op_alg' (RawVecInner_st (A_st))) } move{ (use_op_alg' (RawVecInner_st (A_st))) } ((EnumData ((Result_els ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type)))) "Ok" ("__3")) at{ (Result_Ok_sls ((RawVecInner_st (A_st))) ((errors_TryReserveError_sls : syn_type))) } "0");
      local_live{ (RawVec_st (T_st) (A_st)) } "__9";
      local_live{ (RawVecInner_st (A_st)) } "__10";
      "__10" <-{ (use_op_alg' (RawVecInner_st (A_st))) } move{ (use_op_alg' (RawVecInner_st (A_st))) } ("inner");
      local_live{ ((core_marker_PhantomData_sls (T_st)) : syn_type) } "__11";
      "__11" <-{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } StructInit (core_marker_PhantomData_sls (T_st)) [];
      "__9" <-{ (use_op_alg' (RawVec_st (T_st) (A_st))) } StructInit (RawVec_sls (T_st) (A_st)) [("inner", move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__10") : expr); ("_marker", move{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } ("__11") : expr)];
      local_dead "__11";
      local_dead "__10";
      "__0" <-{ (use_op_alg' ((Result_els ((RawVec_st (T_st) (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } EnumInit (Result_els ((RawVec_st (T_st) (A_st))) ((errors_TryReserveError_sls : syn_type))) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["RawVec_inv_t"] (RSTScopeInst [] [RSTTyVar "T"; RSTTyVar "A"] [AppDef ["Allocator_A_spec_attrs"] []]); RSTLitType ["errors_TryReserveError_inv_t"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls ((RawVec_st (T_st) (A_st))) ((errors_TryReserveError_sls : syn_type))) [("0", move{ (use_op_alg' (RawVec_st (T_st) (A_st))) } ("__9") : expr)]);
      local_dead "__9";
      local_dead "inner";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      "__14" <-{ BoolOp } val_of_bool false;
      "__15" <-{ BoolOp } val_of_bool false;
      local_dead "__3";
      return (move{ (use_op_alg' ((Result_els ((RawVec_st (T_st) (A_st))) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
     <[
     "_bb7" :=
      Unwind
     ]>%E $
     <[
     "_bb8" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("__5")] None
      ( Goto "_bb7")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb9" :=
      if{ BoolOp }: copy{ BoolOp } ("__16") then
       Goto "_bb8"
      else
       Goto "_bb7"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_with_capacity_in_def (DropGlue_A_drop_glue_loc: loc) (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_with_capacity_in_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVec_st (T_st) (A_st)) } "__0";
      local_live{ BoolSynType } "__8";
      "__8" <-{ BoolOp } val_of_bool false;
      local_live{ (RawVecInner_st (A_st)) } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ A_st } "__5";
      "__8" <-{ BoolOp } val_of_bool true;
      "__5" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      local_live{ (layout_Layout_sls : syn_type) } "__6";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__6"))
      ( Goto "_bb1")
      ( Goto "_bb5")
     ]>%E $
     <[
     "_bb1" :=
      "__8" <-{ BoolOp } val_of_bool false;
      CallS raw_vec_implRawVecInnerA_with_capacity_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ (IntOp USize) } ("__4"); move{ (use_op_alg' A_st) } ("__5"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__6")] (Some (Na1Ord, (use_op_alg' (RawVecInner_st (A_st))), "__3"))
      ( Goto "_bb2")
      ( Goto "_bb5")
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__6";
      "__8" <-{ BoolOp } val_of_bool false;
      local_dead "__5";
      local_dead "__4";
      local_live{ ((core_marker_PhantomData_sls (T_st)) : syn_type) } "__7";
      "__7" <-{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } StructInit (core_marker_PhantomData_sls (T_st)) [];
      "__0" <-{ (use_op_alg' (RawVec_st (T_st) (A_st))) } StructInit (RawVec_sls (T_st) (A_st)) [("inner", move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__3") : expr); ("_marker", move{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } ("__7") : expr)];
      local_dead "__7";
      local_dead "__3";
      return (move{ (use_op_alg' (RawVec_st (T_st) (A_st))) } ("__0"))
     ]>%E $
     <[
     "_bb3" :=
      Unwind
     ]>%E $
     <[
     "_bb4" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("__5")] None
      ( Goto "_bb3")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb5" :=
      if{ BoolOp }: copy{ BoolOp } ("__8") then
       Goto "_bb4"
      else
       Goto "_bb3"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecTA_with_capacity_zeroed_in_def (DropGlue_A_drop_glue_loc: loc) (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_with_capacity_zeroed_in_A_loc: loc) (T_st: syn_type) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout);
     ("alloc", (use_layout_alg' A_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVec_st (T_st) (A_st)) } "__0";
      local_live{ BoolSynType } "__8";
      "__8" <-{ BoolOp } val_of_bool false;
      local_live{ (RawVecInner_st (A_st)) } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ A_st } "__5";
      "__8" <-{ BoolOp } val_of_bool true;
      "__5" <-{ (use_op_alg' A_st) } move{ (use_op_alg' A_st) } ("alloc");
      local_live{ (layout_Layout_sls : syn_type) } "__6";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__6"))
      ( Goto "_bb1")
      ( Goto "_bb5")
     ]>%E $
     <[
     "_bb1" :=
      "__8" <-{ BoolOp } val_of_bool false;
      CallS raw_vec_implRawVecInnerA_with_capacity_zeroed_in_A_loc [] [RSTTyVar "A"] [@{expr} move{ (IntOp USize) } ("__4"); move{ (use_op_alg' A_st) } ("__5"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__6")] (Some (Na1Ord, (use_op_alg' (RawVecInner_st (A_st))), "__3"))
      ( Goto "_bb2")
      ( Goto "_bb5")
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__6";
      "__8" <-{ BoolOp } val_of_bool false;
      local_dead "__5";
      local_dead "__4";
      local_live{ ((core_marker_PhantomData_sls (T_st)) : syn_type) } "__7";
      "__7" <-{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } StructInit (core_marker_PhantomData_sls (T_st)) [];
      "__0" <-{ (use_op_alg' (RawVec_st (T_st) (A_st))) } StructInit (RawVec_sls (T_st) (A_st)) [("inner", move{ (use_op_alg' (RawVecInner_st (A_st))) } ("__3") : expr); ("_marker", move{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } ("__7") : expr)];
      local_dead "__7";
      local_dead "__3";
      return (move{ (use_op_alg' (RawVec_st (T_st) (A_st))) } ("__0"))
     ]>%E $
     <[
     "_bb3" :=
      Unwind
     ]>%E $
     <[
     "_bb4" :=
      CallS DropGlue_A_drop_glue_loc [] [] [@{expr} &raw{ PRef, Mut } ("__5")] None
      ( Goto "_bb3")
      ( UnwindTerminate)
     ]>%E $
     <[
     "_bb5" :=
      if{ BoolOp }: copy{ BoolOp } ("__8") then
       Goto "_bb4"
      else
       Goto "_bb3"
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecT_new_def (raw_vec_implRawVecTA_new_in_T_std_alloc_Global_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVec_st (T_st) ((Global_sls : syn_type))) } "__0";
      local_live{ (Global_sls : syn_type) } "__1";
      "__1" <-{ (use_op_alg' (Global_sls : syn_type)) } StructInit Global_sls [];
      CallS raw_vec_implRawVecTA_new_in_T_std_alloc_Global_loc [] [RSTTyVar "T"] [@{expr} move{ (use_op_alg' (Global_sls : syn_type)) } ("__1")] (Some (Na1Ord, (use_op_alg' (RawVec_st (T_st) ((Global_sls : syn_type)))), "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__1";
      return (move{ (use_op_alg' (RawVec_st (T_st) ((Global_sls : syn_type)))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecT_with_capacity_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInner_with_capacity_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVec_st (T_st) ((Global_sls : syn_type))) } "__0";
      local_live{ (RawVecInner_st ((Global_sls : syn_type))) } "__2";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ (layout_Layout_sls : syn_type) } "__4";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__4"))
      ( Goto "_bb1")
      ( Unwind)
     ]>%E $
     <[
     "_bb1" :=
      CallS raw_vec_implRawVecInner_with_capacity_loc [] [] [@{expr} move{ (IntOp USize) } ("__3"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__4")] (Some (Na1Ord, (use_op_alg' (RawVecInner_st ((Global_sls : syn_type)))), "__2"))
      ( Goto "_bb2")
      ( Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__4";
      local_dead "__3";
      local_live{ ((core_marker_PhantomData_sls (T_st)) : syn_type) } "__5";
      "__5" <-{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } StructInit (core_marker_PhantomData_sls (T_st)) [];
      "__0" <-{ (use_op_alg' (RawVec_st (T_st) ((Global_sls : syn_type)))) } StructInit (RawVec_sls (T_st) ((Global_sls : syn_type))) [("inner", move{ (use_op_alg' (RawVecInner_st ((Global_sls : syn_type)))) } ("__2") : expr); ("_marker", move{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } ("__5") : expr)];
      local_dead "__5";
      local_dead "__2";
      return (move{ (use_op_alg' (RawVec_st (T_st) ((Global_sls : syn_type)))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecT_with_capacity_zeroed_def (layout_Layout_new_T_loc: loc) (raw_vec_implRawVecInnerA_with_capacity_zeroed_in_std_alloc_Global_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("capacity", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (RawVec_st (T_st) ((Global_sls : syn_type))) } "__0";
      local_live{ (RawVecInner_st ((Global_sls : syn_type))) } "__2";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } ("capacity");
      local_live{ (Global_sls : syn_type) } "__4";
      "__4" <-{ (use_op_alg' (Global_sls : syn_type)) } StructInit Global_sls [];
      local_live{ (layout_Layout_sls : syn_type) } "__5";
      CallS layout_Layout_new_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__5"))
      ( Goto "_bb1")
      ( Unwind)
     ]>%E $
     <[
     "_bb1" :=
      CallS raw_vec_implRawVecInnerA_with_capacity_zeroed_in_std_alloc_Global_loc [] [] [@{expr} move{ (IntOp USize) } ("__3"); move{ (use_op_alg' (Global_sls : syn_type)) } ("__4"); move{ (use_op_alg' (layout_Layout_sls : syn_type)) } ("__5")] (Some (Na1Ord, (use_op_alg' (RawVecInner_st ((Global_sls : syn_type)))), "__2"))
      ( Goto "_bb2")
      ( Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_dead "__3";
      local_live{ ((core_marker_PhantomData_sls (T_st)) : syn_type) } "__6";
      "__6" <-{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } StructInit (core_marker_PhantomData_sls (T_st)) [];
      "__0" <-{ (use_op_alg' (RawVec_st (T_st) ((Global_sls : syn_type)))) } StructInit (RawVec_sls (T_st) ((Global_sls : syn_type))) [("inner", move{ (use_op_alg' (RawVecInner_st ((Global_sls : syn_type)))) } ("__2") : expr); ("_marker", move{ (use_op_alg' ((core_marker_PhantomData_sls (T_st)) : syn_type)) } ("__6") : expr)];
      local_dead "__6";
      local_dead "__2";
      return (move{ (use_op_alg' (RawVec_st (T_st) ((Global_sls : syn_type)))) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_layout_array_def (Result_TE_map_err_std_alloc_Layout_std_alloc_LayoutError_std_collections_TryReserveError_closuresrcraw_vecrs758975812_loc: loc) (layout_Layout_pad_to_align_loc: loc) (layout_Layout_repeat_packed_loc: loc) (layout_Layout_size_loc: loc) (panic_shim_loc: loc) : function :=
  {|
     f_args := [
      ("cap", (it_layout USize) : layout);
     ("elem_layout", (use_layout_alg' (layout_Layout_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type) } "__0";
      local_live{ UnitSynType } "__3";
      local_live{ BoolSynType } "__4";
      "__4" <-{ BoolOp } val_of_bool true;
      if{ BoolOp }: move{ BoolOp } ("__4") then
       Goto "_bb1"
      else
       Goto "_bb7"
     ]>%E $
     <[
     "_bb1" :=
      local_live{ UnitSynType } "__5";
      local_live{ BoolSynType } "__6";
      local_live{ (IntSynType USize) } "__7";
      local_live{ RefSynType } "__8";
      annot{ 1 }: StartLftAnnot "llft2" ["_flft"]; (* borrow *)
      "__8" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft2" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft7" "llft2"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft11" "plft7"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft11"] [] [@{expr} move{ RefOp } ("__8")] (Some (Na1Ord, (IntOp USize), "__7"))
      ( annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       annot{ 2 }: EndLftAnnot "llft2"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__8";
      local_live{ (IntSynType USize) } "__9";
      local_live{ RefSynType } "__10";
      local_live{ (layout_Layout_sls : syn_type) } "__11";
      local_live{ RefSynType } "__12";
      annot{ 1 }: StartLftAnnot "llft3" ["_flft"]; (* borrow *)
      "__12" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft3" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft9" "llft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft12" "plft9"; (* function_call *)
      CallS layout_Layout_pad_to_align_loc ["vlft12"] [] [@{expr} move{ RefOp } ("__12")] (Some (Na1Ord, (use_op_alg' (layout_Layout_sls : syn_type)), "__11"))
      ( annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       annot{ 2 }: EndLftAnnot "llft3"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      annot{ 1 }: StartLftAnnot "llft4" ["_flft"]; (* borrow *)
      "__10" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft4" } ("__11");
      annot{ 1 }: CopyLftNameAnnot "plft8" "llft4"; (* post-assignment *)
      local_dead "__12";
      annot{ 1 }: CopyLftNameAnnot "vlft13" "plft8"; (* function_call *)
      CallS layout_Layout_size_loc ["vlft13"] [] [@{expr} move{ RefOp } ("__10")] (Some (Na1Ord, (IntOp USize), "__9"))
      ( annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Goto "_bb4")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       annot{ 2 }: EndLftAnnot "llft4"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__10";
      "__6" <-{ BoolOp } (move{ (IntOp USize) } ("__7")) = { (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__9"));
      if{ BoolOp }: move{ BoolOp } ("__6") then
       Goto "_bb5"
      else
       Goto "_bb6"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__9";
      local_dead "__7";
      local_dead "__11";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      local_dead "__6";
      local_dead "__5";
      "__3" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb8"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__9";
      local_dead "__7";
      local_dead "__11";
      local_live{ NeverSynType } "__13";
      CallS panic_shim_loc [] [] [@{expr} ] None
      ( StuckS)
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb7" :=
      "__3" <-{ (StructOp unit_sl []) } zst_val;
      Goto "_bb8"
     ]>%E $
     <[
     "_bb8" :=
      local_dead "__4";
      local_dead "__3";
      local_live{ ((Result_els ((layout_Layout_sls : syn_type)) ((layout_LayoutError_sls : syn_type))) : syn_type) } "__14";
      local_live{ RefSynType } "__15";
      annot{ 1 }: StartLftAnnot "llft6" ["_flft"]; (* borrow *)
      "__15" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "llft6" } ("elem_layout");
      annot{ 1 }: CopyLftNameAnnot "plft10" "llft6"; (* post-assignment *)
      local_live{ (IntSynType USize) } "__16";
      "__16" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      annot{ 1 }: CopyLftNameAnnot "vlft14" "plft10"; (* function_call *)
      CallS layout_Layout_repeat_packed_loc ["vlft14"] [] [@{expr} move{ RefOp } ("__15"); move{ (IntOp USize) } ("__16")] (Some (Na1Ord, (use_op_alg' ((Result_els ((layout_Layout_sls : syn_type)) ((layout_LayoutError_sls : syn_type))) : syn_type)), "__14"))
      ( annot{ 2 }: EndLftAnnot "llft6"; (* endlft *)
       Goto "_bb9")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       annot{ 2 }: EndLftAnnot "llft6"; (* endlft *)
       Unwind)
     ]>%E $
     <[
     "_bb9" :=
      local_dead "__16";
      local_dead "__15";
      local_live{ UnitSynType } "__17";
      "__17" <-{ (StructOp unit_sl []) } zst_val;
      CallS Result_TE_map_err_std_alloc_Layout_std_alloc_LayoutError_std_collections_TryReserveError_closuresrcraw_vecrs758975812_loc [] [] [@{expr} move{ (use_op_alg' ((Result_els ((layout_Layout_sls : syn_type)) ((layout_LayoutError_sls : syn_type))) : syn_type)) } ("__14"); move{ (StructOp unit_sl []) } ("__17")] (Some (Na1Ord, (use_op_alg' ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)), "__0"))
      ( Goto "_bb10")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb10" :=
      local_dead "__17";
      local_dead "__14";
      return (move{ (use_op_alg' ((Result_els ((layout_Layout_sls : syn_type)) ((errors_TryReserveError_sls : syn_type))) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_layout_array_closure0_def (Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc: loc) : function :=
  {|
     f_args := [
      ("__1", (layout_of unit_sl) : layout);
     ("__2", (use_layout_alg' (layout_LayoutError_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "__0";
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__3";
      "__3" <-{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } EnumInit errors_TryReserveErrorKind_els "CapacityOverflow" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_CapacityOverflow_sls []);
      CallS Tasconvert_IntoU_into_std_collections_TryReserveErrorKind_std_collections_TryReserveError_loc [] [] [@{expr} move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__3")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveError_sls : syn_type)), "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      return (move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_min_non_zero_cap_def  : function :=
  {|
     f_args := [
      ("size", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ BoolSynType } "__2";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      "__2" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (1) USize);
      if{ BoolOp }: move{ BoolOp } ("__2") then
       Goto "_bb1"
      else
       Goto "_bb2"
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ (IntOp USize) } i2v (8) USize;
      Goto "_bb6"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__3";
      local_live{ BoolSynType } "__4";
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      "__4" <-{ BoolOp } (move{ (IntOp USize) } ("__5")) ≤{ (IntOp USize) , (IntOp USize) , U8 } (i2v (1024) USize);
      if{ BoolOp }: move{ BoolOp } ("__4") then
       Goto "_bb3"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      "__0" <-{ (IntOp USize) } i2v (4) USize;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__5";
      "__0" <-{ (IntOp USize) } i2v (1) USize;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__4";
      Goto "_bb6"
     ]>%E $
     <[
     "_bb6" :=
      local_dead "__2";
      return (move{ (IntOp USize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_new_cap_def (mem_size_of_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      ("cap", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ BoolSynType } "__2";
      local_live{ (IntSynType USize) } "__3";
      CallS mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (IntOp USize), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      "__2" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) = { (IntOp USize) , (IntOp USize) , U8 } (i2v (0) USize);
      if{ BoolOp }: move{ BoolOp } ("__2") then
       Goto "_bb2"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__3";
      "__0" <-{ (IntOp USize) } i2v (0) USize;
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__3";
      "__0" <-{ (IntOp USize) } copy{ (IntOp USize) } ("cap");
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__2";
      return (move{ (IntOp USize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
Program Definition raw_vec_implRawVecInnerA_finish_grow_closure0_call_once_code (raw_vec_implRawVecInnerA_finish_grow_closure0_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' ((tuple1_sls (RefSynType)) : syn_type)) : layout);
     ("args", (use_layout_alg' ((tuple1_sls ((errors_AllocError_sls : syn_type))) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "__0";
      local_live{ ((tuple1_sls (RefSynType)) : syn_type) } "__1";
      "__1" <-{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } move{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } ("self");
      CallS raw_vec_implRawVecInnerA_finish_grow_closure0_loc ["ulft1"] [RSTTyVar "A"] [@{expr} move{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } ("__1"); move{ (use_op_alg' (errors_AllocError_sls : syn_type)) } (("args") at{ (tuple1_sls ((errors_AllocError_sls : syn_type))) } "0")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveError_sls : syn_type)), "__0"))
      ( return (move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__0")))
      ( Unwind)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_layout_array_closure0_call_once_code (raw_vec_layout_array_closure0_loc: loc) : function :=
  {|
     f_args := [
      ("self", (layout_of unit_sl) : layout);
     ("args", (use_layout_alg' ((tuple1_sls ((layout_LayoutError_sls : syn_type))) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (errors_TryReserveError_sls : syn_type) } "__0";
      local_live{ UnitSynType } "__1";
      "__1" <-{ (StructOp unit_sl []) } move{ (StructOp unit_sl []) } ("self");
      CallS raw_vec_layout_array_closure0_loc [] [] [@{expr} move{ (StructOp unit_sl []) } ("__1"); move{ (use_op_alg' (layout_LayoutError_sls : syn_type)) } (("args") at{ (tuple1_sls ((layout_LayoutError_sls : syn_type))) } "0")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveError_sls : syn_type)), "__0"))
      ( return (move{ (use_op_alg' (errors_TryReserveError_sls : syn_type)) } ("__0")))
      ( Unwind)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition raw_vec_implRawVecInnerA_shrink_unchecked_closure0_call_once_code (raw_vec_implRawVecInnerA_shrink_unchecked_closure0_loc: loc) (A_st: syn_type) : function :=
  {|
     f_args := [
      ("self", (use_layout_alg' ((tuple1_sls (RefSynType)) : syn_type)) : layout);
     ("args", (use_layout_alg' ((tuple1_sls ((errors_AllocError_sls : syn_type))) : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (errors_TryReserveErrorKind_els : syn_type) } "__0";
      local_live{ ((tuple1_sls (RefSynType)) : syn_type) } "__1";
      "__1" <-{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } move{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } ("self");
      CallS raw_vec_implRawVecInnerA_shrink_unchecked_closure0_loc ["ulft1"] [RSTTyVar "A"] [@{expr} move{ (use_op_alg' ((tuple1_sls (RefSynType)) : syn_type)) } ("__1"); move{ (use_op_alg' (errors_AllocError_sls : syn_type)) } (("args") at{ (tuple1_sls ((errors_AllocError_sls : syn_type))) } "0")] (Some (Na1Ord, (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)), "__0"))
      ( return (move{ (use_op_alg' (errors_TryReserveErrorKind_els : syn_type)) } ("__0")))
      ( Unwind)
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




End code.