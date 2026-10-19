From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_errors_TryReserveErrorKindasstd_clone_Clone_clone.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma errors_TryReserveErrorKindasstd_clone_Clone_clone_proof (π : thread_id) :
  errors_TryReserveErrorKindasstd_clone_Clone_clone_lemma π.
Proof.
  errors_TryReserveErrorKindasstd_clone_Clone_clone_prelude.
  rep <-! <3000 liRStep.
  Unshelve.
  1-5: sidecond_solver.
Qed.
End proof.
