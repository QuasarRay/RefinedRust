From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_from.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_from_proof (π : thread_id) :
  errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_from_lemma π.
Proof.
  errors_TryReserveErrorasstd_convert_Fromerrors_TryReserveErrorKind_from_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
