From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_layout_array_closure0_call_once.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_layout_array_closure0_call_once_proof (π : thread_id) :
  raw_vec_layout_array_closure0_call_once_lemma π.
Proof.
  raw_vec_layout_array_closure0_call_once_prelude.

  rep <-! <3000 liRStep.
  Unshelve.
  1-5: sidecond_solver.
Qed.
End proof.
