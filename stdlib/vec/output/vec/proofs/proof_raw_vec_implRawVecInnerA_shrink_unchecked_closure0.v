From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_shrink_unchecked_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_shrink_unchecked_closure0_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_shrink_unchecked_closure0_lemma π.
Proof.
  raw_vec_implRawVecInnerA_shrink_unchecked_closure0_prelude.

  rep <-! <3000 liRStep.
  Unshelve.
  1-3: sidecond_solver.
Qed.
End proof.
