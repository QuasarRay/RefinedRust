From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.result.result.generated Require Export generated_specs_result.
Section errors_AllocError_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition errors_AllocError_sls  : struct_layout_spec :=
    let errors_AllocError_st  := UnitSynType in
    mk_sls "errors_AllocError" [] StructReprRust.
  Definition errors_AllocError_st  : syn_type := errors_AllocError_sls .
End errors_AllocError_sls.

Section Global_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition Global_sls  : struct_layout_spec :=
    let Global_st  := UnitSynType in
    mk_sls "Global" [] StructReprRust.
  Definition Global_st  : syn_type := Global_sls .
End Global_sls.

Section layout_LayoutError_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition layout_LayoutError_sls  : struct_layout_spec :=
    let layout_LayoutError_st  := UnitSynType in
    mk_sls "layout_LayoutError" [] StructReprRust.
  Definition layout_LayoutError_st  : syn_type := layout_LayoutError_sls .
End layout_LayoutError_sls.

Section layout_Layout_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition layout_Layout_sls  : struct_layout_spec :=
    let layout_Layout_st  := UnitSynType in
    mk_sls "layout_Layout" [
    ("size", (IntSynType USize));
    ("align", (alignment_Alignment_sls : syn_type))] StructReprRust.
  Definition layout_Layout_st  : syn_type := layout_Layout_sls .
End layout_Layout_sls.

Section errors_TryReserveErrorKind_els.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition errors_TryReserveErrorKind_CapacityOverflow_sls  : struct_layout_spec :=
    let errors_TryReserveErrorKind_CapacityOverflow_st  := UnitSynType in
    let errors_TryReserveErrorKind_st  := UnitSynType in
    mk_sls "errors_TryReserveErrorKind_CapacityOverflow" [] StructReprRust.
  Definition errors_TryReserveErrorKind_CapacityOverflow_st  : syn_type := errors_TryReserveErrorKind_CapacityOverflow_sls .

  Definition errors_TryReserveErrorKind_AllocError_sls  : struct_layout_spec :=
    let errors_TryReserveErrorKind_AllocError_st  := UnitSynType in
    let errors_TryReserveErrorKind_st  := UnitSynType in
    mk_sls "errors_TryReserveErrorKind_AllocError" [
    ("layout", layout_Layout_st);
    ("non_exhaustive", UnitSynType)] StructReprRust.
  Definition errors_TryReserveErrorKind_AllocError_st  : syn_type := errors_TryReserveErrorKind_AllocError_sls .

  Program Definition errors_TryReserveErrorKind_els  : enum_layout_spec := mk_els "errors_TryReserveErrorKind" ISize [
    ("CapacityOverflow", errors_TryReserveErrorKind_CapacityOverflow_st );
    ("AllocError", errors_TryReserveErrorKind_AllocError_st )] EnumReprRust [("CapacityOverflow", 0); ("AllocError", 1)] _ _ _ _.
  Next Obligation. solve_enum_layout_spec_variants_nodup. Qed.
  Next Obligation. solve_enum_layout_spec_variants_eq. Qed.
  Next Obligation. solve_enum_layout_spec_discriminant_nodup. Qed.
  Final Obligation. solve_enum_layout_spec_discriminant_in_range. Qed.
  Global Typeclasses Opaque errors_TryReserveErrorKind_els.
  Definition errors_TryReserveErrorKind_st  : syn_type := errors_TryReserveErrorKind_els .
End errors_TryReserveErrorKind_els.

Section errors_TryReserveError_sls.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition errors_TryReserveError_sls  : struct_layout_spec :=
    let errors_TryReserveError_st  := UnitSynType in
    mk_sls "errors_TryReserveError" [
    ("kind", errors_TryReserveErrorKind_st)] StructReprRust.
  Definition errors_TryReserveError_st  : syn_type := errors_TryReserveError_sls .
End errors_TryReserveError_sls.

Section code.
Context `{!LayoutAlg}.
Open Scope printing_sugar.

Program Definition errors_AllocErrorasstd_clone_Clone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ errors_AllocError_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (use_op_alg' errors_AllocError_st) } copy{ (use_op_alg' errors_AllocError_st) } (!{ RefOp } ( "self" ));
      return (move{ (use_op_alg' errors_AllocError_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition errors_TryReserveErrorKindasstd_clone_Clone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ errors_TryReserveErrorKind_st } "__0";
      local_live{ (IntSynType ISize) } "__2";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      "__2" <-{ (IntOp ISize) } EnumDiscriminant (errors_TryReserveErrorKind_els) (!{ RefOp } ( "self" ));
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__2")) (<[ 0%Z := 0%nat ]> $ <[ 1%Z := 1%nat ]> $ ∅) ([Goto "_bb3"; Goto "_bb2"]) (Goto "_bb1")
     ]>%E $
     <[
     "_bb1" :=
      StuckS
     ]>%E $
     <[
     "_bb2" :=
      local_live{ RefSynType } "layout";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft4"; (* borrow *)
      "layout" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "vlft3" } ((EnumData (errors_TryReserveErrorKind_els) "AllocError" (!{ RefOp } ( "self" ))) at{ errors_TryReserveErrorKind_AllocError_sls } "layout");
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      local_live{ layout_Layout_st } "__4";
      "__4" <-{ (use_op_alg' layout_Layout_st) } copy{ (use_op_alg' layout_Layout_st) } (!{ RefOp } ( "layout" ));
      local_live{ UnitSynType } "__5";
      "__5" <-{ (StructOp unit_sl []) } zst_val;
      "__0" <-{ (use_op_alg' errors_TryReserveErrorKind_st) } EnumInit errors_TryReserveErrorKind_els "AllocError" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_AllocError_sls [("layout", move{ (use_op_alg' layout_Layout_st) } ("__4") : expr); ("non_exhaustive", move{ (StructOp unit_sl []) } ("__5") : expr)]);
      local_dead "__5";
      local_dead "__4";
      local_dead "layout";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      "__0" <-{ (use_op_alg' errors_TryReserveErrorKind_st) } EnumInit errors_TryReserveErrorKind_els "CapacityOverflow" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_CapacityOverflow_sls []);
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      return (move{ (use_op_alg' errors_TryReserveErrorKind_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from_def  : function :=
  {|
     f_args := [
      ("__1", (use_layout_alg' layout_LayoutError_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ errors_TryReserveErrorKind_st } "__0";
      "__0" <-{ (use_op_alg' errors_TryReserveErrorKind_st) } EnumInit errors_TryReserveErrorKind_els "CapacityOverflow" (RSTEnumDef ["errors_TryReserveErrorKind_enum"] (RSTScopeInst [] [] [])) (StructInit errors_TryReserveErrorKind_CapacityOverflow_sls []);
      return (move{ (use_op_alg' errors_TryReserveErrorKind_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition errors_TryReserveError_kind_def (errors_TryReserveErrorKindasstd_clone_Clone_clone_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ errors_TryReserveErrorKind_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft4" "ulft_1"; (* initialization *)
      local_live{ RefSynType } "__2";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft4"; (* borrow *)
      "__2" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["errors_TryReserveErrorKind_ty"] (RSTScopeInst [] [] [])), "vlft3" } ((!{ RefOp } ( "self" )) at{ errors_TryReserveError_sls } "kind");
      annot{ 1 }: CopyLftNameAnnot "plft5" "vlft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft6" "plft5"; (* function_call *)
      CallS errors_TryReserveErrorKindasstd_clone_Clone_clone_loc ["vlft6"] [] [@{expr} move{ RefOp } ("__2")] (Some (Na1Ord, (use_op_alg' errors_TryReserveErrorKind_st), "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__2";
      return (move{ (use_op_alg' errors_TryReserveErrorKind_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition errors_TryReserveErrorasstd_clone_Clone_clone_def (errors_TryReserveErrorKindasstd_clone_Clone_clone_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ errors_TryReserveError_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_1"; (* initialization *)
      local_live{ errors_TryReserveErrorKind_st } "__2";
      local_live{ RefSynType } "__3";
      local_live{ RefSynType } "__4";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft5"; (* borrow *)
      "__4" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["errors_TryReserveErrorKind_ty"] (RSTScopeInst [] [] [])), "vlft3" } ((!{ RefOp } ( "self" )) at{ errors_TryReserveError_sls } "kind");
      annot{ 1 }: CopyLftNameAnnot "plft7" "vlft3"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft7"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["errors_TryReserveErrorKind_ty"] (RSTScopeInst [] [] [])), "vlft4" } (!{ RefOp } ( "__4" ));
      annot{ 1 }: CopyLftNameAnnot "plft6" "vlft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft6"; (* function_call *)
      CallS errors_TryReserveErrorKindasstd_clone_Clone_clone_loc ["vlft8"] [] [@{expr} move{ RefOp } ("__3")] (Some (Na1Ord, (use_op_alg' errors_TryReserveErrorKind_st), "__2"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__3";
      "__0" <-{ (use_op_alg' errors_TryReserveError_st) } StructInit errors_TryReserveError_sls [("kind", move{ (use_op_alg' errors_TryReserveErrorKind_st) } ("__2") : expr)];
      local_dead "__4";
      local_dead "__2";
      return (move{ (use_op_alg' errors_TryReserveError_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_from_def  : function :=
  {|
     f_args := [
      ("kind", (use_layout_alg' errors_TryReserveErrorKind_st) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ errors_TryReserveError_st } "__0";
      local_live{ errors_TryReserveErrorKind_st } "__2";
      "__2" <-{ (use_op_alg' errors_TryReserveErrorKind_st) } move{ (use_op_alg' errors_TryReserveErrorKind_st) } ("kind");
      "__0" <-{ (use_op_alg' errors_TryReserveError_st) } StructInit errors_TryReserveError_sls [("kind", move{ (use_op_alg' errors_TryReserveErrorKind_st) } ("__2") : expr)];
      local_dead "__2";
      return (move{ (use_op_alg' errors_TryReserveError_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_align_def (alignment_Alignment_as_usize_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (alignment_Alignment_sls : syn_type) } "__2";
      "__2" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ((!{ RefOp } ( "self" )) at{ layout_Layout_sls } "align");
      CallS alignment_Alignment_as_usize_loc [] [] [@{expr} move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__2")] (Some (Na1Ord, (IntOp USize), "__0"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__2";
      return (move{ (IntOp USize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_alignment_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (alignment_Alignment_sls : syn_type) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ((!{ RefOp } ( "self" )) at{ layout_Layout_sls } "align");
      return (move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_from_size_align_def (alignment_Alignment_new_unchecked_loc: loc) (layout_Layout_is_size_align_valid_loc: loc) : function :=
  {|
     f_args := [
      ("size", (it_layout USize) : layout);
     ("align", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type) } "__0";
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("align");
      CallS layout_Layout_is_size_align_valid_loc [] [] [@{expr} move{ (IntOp USize) } ("__4"); move{ (IntOp USize) } ("__5")] (Some (Na1Ord, BoolOp, "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb2"
      else
       Goto "_bb4"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ layout_Layout_st } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      local_live{ (alignment_Alignment_sls : syn_type) } "__8";
      local_live{ (IntSynType USize) } "__9";
      "__9" <-{ (IntOp USize) } copy{ (IntOp USize) } ("align");
      CallS alignment_Alignment_new_unchecked_loc [] [] [@{expr} move{ (IntOp USize) } ("__9")] (Some (Na1Ord, (use_op_alg' (alignment_Alignment_sls : syn_type)), "__8"))
      ( Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__9";
      "__6" <-{ (use_op_alg' layout_Layout_st) } StructInit layout_Layout_sls [("size", move{ (IntOp USize) } ("__7") : expr); ("align", move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__8") : expr)];
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } EnumInit (Result_els (layout_Layout_st) (layout_LayoutError_st)) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] []); RSTLitType ["layout_LayoutError_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls (layout_Layout_st) (layout_LayoutError_st)) [("0", move{ (use_op_alg' layout_Layout_st) } ("__6") : expr)]);
      local_dead "__6";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ layout_LayoutError_st } "__10";
      "__10" <-{ (use_op_alg' layout_LayoutError_st) } StructInit layout_LayoutError_sls [];
      "__0" <-{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } EnumInit (Result_els (layout_Layout_st) (layout_LayoutError_st)) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] []); RSTLitType ["layout_LayoutError_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Err_sls (layout_Layout_st) (layout_LayoutError_st)) [("0", move{ (use_op_alg' layout_LayoutError_st) } ("__10") : expr)]);
      local_dead "__10";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      local_dead "__3";
      return (move{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_from_size_align_unchecked_def (alignment_Alignment_new_unchecked_loc: loc) : function :=
  {|
     f_args := [
      ("size", (it_layout USize) : layout);
     ("align", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ layout_Layout_st } "__0";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      local_live{ (alignment_Alignment_sls : syn_type) } "__4";
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("align");
      CallS alignment_Alignment_new_unchecked_loc [] [] [@{expr} move{ (IntOp USize) } ("__5")] (Some (Na1Ord, (use_op_alg' (alignment_Alignment_sls : syn_type)), "__4"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      "__0" <-{ (use_op_alg' layout_Layout_st) } StructInit layout_Layout_sls [("size", move{ (IntOp USize) } ("__3") : expr); ("align", move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__4") : expr)];
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' layout_Layout_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_from_size_alignment_def (layout_Layout_is_size_alignment_valid_loc: loc) : function :=
  {|
     f_args := [
      ("size", (it_layout USize) : layout);
     ("alignment", (use_layout_alg' (alignment_Alignment_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type) } "__0";
      local_live{ BoolSynType } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      local_live{ (alignment_Alignment_sls : syn_type) } "__5";
      "__5" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("alignment");
      CallS layout_Layout_is_size_alignment_valid_loc [] [] [@{expr} move{ (IntOp USize) } ("__4"); move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__5")] (Some (Na1Ord, BoolOp, "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      if{ BoolOp }: move{ BoolOp } ("__3") then
       Goto "_bb2"
      else
       Goto "_bb3"
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ layout_Layout_st } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      local_live{ (alignment_Alignment_sls : syn_type) } "__8";
      "__8" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("alignment");
      "__6" <-{ (use_op_alg' layout_Layout_st) } StructInit layout_Layout_sls [("size", move{ (IntOp USize) } ("__7") : expr); ("align", move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__8") : expr)];
      local_dead "__8";
      local_dead "__7";
      "__0" <-{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } EnumInit (Result_els (layout_Layout_st) (layout_LayoutError_st)) "Ok" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] []); RSTLitType ["layout_LayoutError_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Ok_sls (layout_Layout_st) (layout_LayoutError_st)) [("0", move{ (use_op_alg' layout_Layout_st) } ("__6") : expr)]);
      local_dead "__6";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__4";
      local_live{ layout_LayoutError_st } "__9";
      "__9" <-{ (use_op_alg' layout_LayoutError_st) } StructInit layout_LayoutError_sls [];
      "__0" <-{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } EnumInit (Result_els (layout_Layout_st) (layout_LayoutError_st)) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] []); RSTLitType ["layout_LayoutError_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Err_sls (layout_Layout_st) (layout_LayoutError_st)) [("0", move{ (use_op_alg' layout_LayoutError_st) } ("__9") : expr)]);
      local_dead "__9";
      Goto "_bb4"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__3";
      return (move{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_from_size_alignment_unchecked_def  : function :=
  {|
     f_args := [
      ("size", (it_layout USize) : layout);
     ("alignment", (use_layout_alg' (alignment_Alignment_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ layout_Layout_st } "__0";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      local_live{ (alignment_Alignment_sls : syn_type) } "__4";
      "__4" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("alignment");
      "__0" <-{ (use_op_alg' layout_Layout_st) } StructInit layout_Layout_sls [("size", move{ (IntOp USize) } ("__3") : expr); ("align", move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__4") : expr)];
      local_dead "__4";
      local_dead "__3";
      return (move{ (use_op_alg' layout_Layout_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_is_size_align_valid_def (alignment_Alignment_new_loc: loc) (layout_Layout_is_size_alignment_valid_loc: loc) : function :=
  {|
     f_args := [
      ("size", (it_layout USize) : layout);
     ("align", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ NeverSynType } "__3";
      local_live{ (IntSynType ISize) } "__7";
      local_live{ ((Option_els ((alignment_Alignment_sls : syn_type))) : syn_type) } "__5";
      local_live{ (IntSynType USize) } "__6";
      "__6" <-{ (IntOp USize) } copy{ (IntOp USize) } ("align");
      CallS alignment_Alignment_new_loc [] [] [@{expr} move{ (IntOp USize) } ("__6")] (Some (Na1Ord, (use_op_alg' ((Option_els ((alignment_Alignment_sls : syn_type))) : syn_type)), "__5"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__6";
      "__7" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els ((alignment_Alignment_sls : syn_type)))) ("__5");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__7")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb3")
     ]>%E $
     <[
     "_bb2" :=
      local_live{ (alignment_Alignment_sls : syn_type) } "alignment";
      "alignment" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ((EnumData ((Option_els ((alignment_Alignment_sls : syn_type)))) "Some" ("__5")) at{ (Option_Some_sls ((alignment_Alignment_sls : syn_type))) } "0");
      local_dead "__5";
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      local_live{ (alignment_Alignment_sls : syn_type) } "__9";
      "__9" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("alignment");
      CallS layout_Layout_is_size_alignment_valid_loc [] [] [@{expr} move{ (IntOp USize) } ("__8"); move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__9")] (Some (Na1Ord, BoolOp, "__0"))
      ( Goto "_bb4")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      "__0" <-{ BoolOp } val_of_bool false;
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__9";
      local_dead "__8";
      local_dead "alignment";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_is_size_alignment_valid_def (layout_Layout_max_size_for_alignment_loc: loc) : function :=
  {|
     f_args := [
      ("size", (it_layout USize) : layout);
     ("alignment", (use_layout_alg' (alignment_Alignment_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ BoolSynType } "__0";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      local_live{ (IntSynType USize) } "__4";
      local_live{ (alignment_Alignment_sls : syn_type) } "__5";
      "__5" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("alignment");
      CallS layout_Layout_max_size_for_alignment_loc [] [] [@{expr} move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__5")] (Some (Na1Ord, (IntOp USize), "__4"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      "__0" <-{ BoolOp } (move{ (IntOp USize) } ("__3")) ≤{ (IntOp USize) , (IntOp USize) , U8 } (move{ (IntOp USize) } ("__4"));
      local_dead "__4";
      local_dead "__3";
      return (move{ BoolOp } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_max_size_for_alignment_def (alignment_Alignment_as_usize_loc: loc) (panic_shim_loc: loc) (usize_unchecked_sub_loc: loc) : function :=
  {|
     f_args := [
      ("alignment", (use_layout_alg' (alignment_Alignment_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      local_live{ ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type) } "__4";
      local_live{ (IntSynType USize) } "__2";
      local_live{ (IntSynType USize) } "__3";
      "__3" <-{ (IntOp USize) } UnOp (CastOp ((IntOp USize))) ((IntOp ISize)) (i2v (9223372036854775807) ISize);
      "__4" <-{ (use_op_alg' ((tuple2_sls ((IntSynType USize)) (BoolSynType)) : syn_type)) } StructInit (tuple2_sls ((IntSynType USize)) BoolSynType) [("0", (copy{ (IntOp USize) } ("__3")) +{ (IntOp USize) , (IntOp USize) } (i2v (1) USize) : expr); ("1", (copy{ (IntOp USize) } ("__3")) +c{ (IntOp USize) , (IntOp USize) } (i2v (1) USize) : expr)];
      if{ BoolOp }: (move{ BoolOp } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "1")) = { BoolOp , BoolOp , U8 } (val_of_bool false) then
       Goto "_bb1"
      else
       CallS panic_shim_loc [] [] [@{expr} ] None
       ( StuckS)
       ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
        Unwind)
     ]>%E $
     <[
     "_bb1" :=
      "__2" <-{ (IntOp USize) } move{ (IntOp USize) } (("__4") at{ (tuple2_sls ((IntSynType USize)) (BoolSynType)) } "0");
      local_dead "__3";
      local_live{ (IntSynType USize) } "__5";
      local_live{ (alignment_Alignment_sls : syn_type) } "__6";
      "__6" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("alignment");
      CallS alignment_Alignment_as_usize_loc [] [] [@{expr} move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__6")] (Some (Na1Ord, (IntOp USize), "__5"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__6";
      CallS usize_unchecked_sub_loc [] [] [@{expr} move{ (IntOp USize) } ("__2"); move{ (IntOp USize) } ("__5")] (Some (Na1Ord, (IntOp USize), "__0"))
      ( Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__5";
      local_dead "__2";
      return (move{ (IntOp USize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_new_def (layout_Layout_from_size_align_unchecked_loc: loc) (mem_align_of_T_loc: loc) (mem_size_of_T_loc: loc) (T_st: syn_type) : function :=
  {|
     f_args := [
      
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ layout_Layout_st } "__0";
      local_live{ (IntSynType USize) } "__1";
      CallS mem_size_of_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (IntOp USize), "__1"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_live{ (IntSynType USize) } "__2";
      CallS mem_align_of_T_loc [] [RSTTyVar "T"] [@{expr} ] (Some (Na1Ord, (IntOp USize), "__2"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      CallS layout_Layout_from_size_align_unchecked_loc [] [] [@{expr} move{ (IntOp USize) } ("__1"); move{ (IntOp USize) } ("__2")] (Some (Na1Ord, (use_op_alg' layout_Layout_st), "__0"))
      ( Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__2";
      local_dead "__1";
      return (move{ (use_op_alg' layout_Layout_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_pad_to_align_def (layout_Layout_alignment_loc: loc) (layout_Layout_from_size_alignment_unchecked_loc: loc) (layout_Layout_size_rounded_up_to_custom_alignment_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ layout_Layout_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft5" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "new_size";
      local_live{ RefSynType } "__3";
      annot{ 1 }: CopyLftNameAnnot "vlft3" "plft5"; (* borrow *)
      "__3" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "vlft3" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft6" "vlft3"; (* post-assignment *)
      local_live{ (alignment_Alignment_sls : syn_type) } "__4";
      "__4" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ((!{ RefOp } ( "self" )) at{ layout_Layout_sls } "align");
      annot{ 1 }: CopyLftNameAnnot "vlft8" "plft6"; (* function_call *)
      CallS layout_Layout_size_rounded_up_to_custom_alignment_loc ["vlft8"] [] [@{expr} move{ RefOp } ("__3"); move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__4")] (Some (Na1Ord, (IntOp USize), "new_size"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__4";
      local_dead "__3";
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("new_size");
      local_live{ (alignment_Alignment_sls : syn_type) } "__6";
      local_live{ RefSynType } "__7";
      annot{ 1 }: CopyLftNameAnnot "vlft4" "plft5"; (* borrow *)
      "__7" <-{ RefOp } &ref{ Shr, Some (RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] [])), "vlft4" } (!{ RefOp } ( "self" ));
      annot{ 1 }: CopyLftNameAnnot "plft7" "vlft4"; (* post-assignment *)
      annot{ 1 }: CopyLftNameAnnot "vlft9" "plft7"; (* function_call *)
      CallS layout_Layout_alignment_loc ["vlft9"] [] [@{expr} move{ RefOp } ("__7")] (Some (Na1Ord, (use_op_alg' (alignment_Alignment_sls : syn_type)), "__6"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__7";
      CallS layout_Layout_from_size_alignment_unchecked_loc [] [] [@{expr} move{ (IntOp USize) } ("__5"); move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__6")] (Some (Na1Ord, (use_op_alg' layout_Layout_st), "__0"))
      ( Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__6";
      local_dead "__5";
      local_dead "new_size";
      return (move{ (use_op_alg' layout_Layout_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_repeat_packed_def (layout_Layout_from_size_alignment_loc: loc) (usize_checked_mul_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("n", (it_layout USize) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type) } "__0";
      local_live{ (IntSynType ISize) } "__6";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ ((Option_els ((IntSynType USize))) : syn_type) } "__3";
      local_live{ (IntSynType USize) } "__4";
      "__4" <-{ (IntOp USize) } copy{ (IntOp USize) } ((!{ RefOp } ( "self" )) at{ layout_Layout_sls } "size");
      local_live{ (IntSynType USize) } "__5";
      "__5" <-{ (IntOp USize) } copy{ (IntOp USize) } ("n");
      CallS usize_checked_mul_loc [] [] [@{expr} move{ (IntOp USize) } ("__4"); move{ (IntOp USize) } ("__5")] (Some (Na1Ord, (use_op_alg' ((Option_els ((IntSynType USize))) : syn_type)), "__3"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      local_dead "__4";
      "__6" <-{ (IntOp ISize) } EnumDiscriminant ((Option_els ((IntSynType USize)))) ("__3");
      Switch (ISize: int_type) (move{ (IntOp ISize) } ("__6")) (<[ 1%Z := 0%nat ]> $ ∅) ([Goto "_bb2"]) (Goto "_bb4")
     ]>%E $
     <[
     "_bb2" :=
      local_live{ (IntSynType USize) } "size";
      "size" <-{ (IntOp USize) } copy{ (IntOp USize) } ((EnumData ((Option_els ((IntSynType USize)))) "Some" ("__3")) at{ (Option_Some_sls ((IntSynType USize))) } "0");
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ (IntOp USize) } copy{ (IntOp USize) } ("size");
      local_live{ (alignment_Alignment_sls : syn_type) } "__9";
      "__9" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ((!{ RefOp } ( "self" )) at{ layout_Layout_sls } "align");
      CallS layout_Layout_from_size_alignment_loc [] [] [@{expr} move{ (IntOp USize) } ("__8"); move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__9")] (Some (Na1Ord, (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)), "__0"))
      ( Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__9";
      local_dead "__8";
      local_dead "size";
      local_dead "__3";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb4" :=
      local_dead "__3";
      local_live{ layout_LayoutError_st } "__10";
      "__10" <-{ (use_op_alg' layout_LayoutError_st) } StructInit layout_LayoutError_sls [];
      "__0" <-{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } EnumInit (Result_els (layout_Layout_st) (layout_LayoutError_st)) "Err" (RSTEnumDef ["Result_enum"] (RSTScopeInst [] [RSTLitType ["layout_Layout_inv_t"] (RSTScopeInst [] [] []); RSTLitType ["layout_LayoutError_ty"] (RSTScopeInst [] [] [])] [])) (StructInit (Result_Err_sls (layout_Layout_st) (layout_LayoutError_st)) [("0", move{ (use_op_alg' layout_LayoutError_st) } ("__10") : expr)]);
      local_dead "__10";
      Goto "_bb5"
     ]>%E $
     <[
     "_bb5" :=
      return (move{ (use_op_alg' ((Result_els (layout_Layout_st) (layout_LayoutError_st)) : syn_type)) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_size_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (IntOp USize) } copy{ (IntOp USize) } ((!{ RefOp } ( "self" )) at{ layout_Layout_sls } "size");
      return (move{ (IntOp USize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layout_size_rounded_up_to_custom_alignment_def (alignment_Alignment_as_usize_loc: loc) (usize_unchecked_add_loc: loc) (usize_unchecked_sub_loc: loc) : function :=
  {|
     f_args := [
      ("self", void* : layout);
     ("alignment", (use_layout_alg' (alignment_Alignment_sls : syn_type)) : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ (IntSynType USize) } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      local_live{ (IntSynType USize) } "align_m1";
      local_live{ (IntSynType USize) } "__4";
      local_live{ (alignment_Alignment_sls : syn_type) } "__5";
      "__5" <-{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } copy{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("alignment");
      CallS alignment_Alignment_as_usize_loc [] [] [@{expr} move{ (use_op_alg' (alignment_Alignment_sls : syn_type)) } ("__5")] (Some (Na1Ord, (IntOp USize), "__4"))
      ( Goto "_bb1")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb1" :=
      local_dead "__5";
      CallS usize_unchecked_sub_loc [] [] [@{expr} move{ (IntOp USize) } ("__4"); i2v (1) USize] (Some (Na1Ord, (IntOp USize), "align_m1"))
      ( Goto "_bb2")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb2" :=
      local_dead "__4";
      local_live{ (IntSynType USize) } "__6";
      local_live{ (IntSynType USize) } "__7";
      "__7" <-{ (IntOp USize) } copy{ (IntOp USize) } ((!{ RefOp } ( "self" )) at{ layout_Layout_sls } "size");
      local_live{ (IntSynType USize) } "__8";
      "__8" <-{ (IntOp USize) } copy{ (IntOp USize) } ("align_m1");
      CallS usize_unchecked_add_loc [] [] [@{expr} move{ (IntOp USize) } ("__7"); move{ (IntOp USize) } ("__8")] (Some (Na1Ord, (IntOp USize), "__6"))
      ( Goto "_bb3")
      ( annot{ 1 }: UnwindFreeAnnot; (* unwind condition is False *)
       Unwind)
     ]>%E $
     <[
     "_bb3" :=
      local_dead "__8";
      local_dead "__7";
      local_live{ (IntSynType USize) } "__9";
      local_live{ (IntSynType USize) } "__10";
      "__10" <-{ (IntOp USize) } copy{ (IntOp USize) } ("align_m1");
      "__9" <-{ (IntOp USize) } UnOp (NotIntOp) ((IntOp USize)) (move{ (IntOp USize) } ("__10"));
      local_dead "__10";
      "__0" <-{ (IntOp USize) } (move{ (IntOp USize) } ("__6")) &b{ (IntOp USize) , (IntOp USize) } (move{ (IntOp USize) } ("__9"));
      local_dead "__9";
      local_dead "__6";
      local_dead "align_m1";
      return (move{ (IntOp USize) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




Program Definition layout_Layoutasstd_clone_Clone_clone_def  : function :=
  {|
     f_args := [
      ("self", void* : layout)
     ];
     f_code :=
      <[
     "_bb0" :=
      local_live{ layout_Layout_st } "__0";
      annot{ 1 }: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
      "__0" <-{ (use_op_alg' layout_Layout_st) } copy{ (use_op_alg' layout_Layout_st) } (!{ RefOp } ( "self" ));
      return (move{ (use_op_alg' layout_Layout_st) } ("__0"))
     ]>%E $
      ∅;
     f_init := "_bb0";
    |}.
Final Obligation.
  solve_fn_vars_nodup.
Qed.




(* closure shims *)
End code.