From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from_proof (π : thread_id) :
  errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from_lemma π.
Proof.
  errors_TryReserveErrorKindasstd_convert_Fromlayout_LayoutError_from_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
