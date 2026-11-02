From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.boxed.boxed.generated Require Import generated_code_boxed generated_specs_boxed generated_template_box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_from.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_from_proof (π : thread_id) :
  box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_from_lemma π.
Proof.
  box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_from_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
