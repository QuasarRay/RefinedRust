From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_handle_error.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_handle_error_proof (π : thread_id) :
  raw_vec_handle_error_lemma π.
Proof.
  raw_vec_handle_error_prelude.
  rep 2000 liRStep.
  Unshelve.
  1-8: sidecond_solver.
  Unshelve.
  1-2: sidecond_hammer.
Qed.
End proof.
