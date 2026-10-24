From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_drop_liveness_drop_after_element_lifetime.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_drop_liveness_drop_after_element_lifetime_proof (π : thread_id) :
  raw_vec_drop_liveness_drop_after_element_lifetime_lemma π.
Proof.
  raw_vec_drop_liveness_drop_after_element_lifetime_prelude.

  rep 3000 liRStep.
  Unshelve.
  1-6: sidecond_solver.
  Unshelve. sidecond_hammer.
Qed.
End proof.
