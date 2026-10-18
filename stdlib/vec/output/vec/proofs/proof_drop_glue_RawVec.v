From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_drop_glue_RawVec.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_RawVec_proof (π : thread_id) :
  drop_glue_RawVec_lemma π.
Proof.
  drop_glue_RawVec_prelude.

  rep <-! <3000 liRStep.
  Unshelve.
  1-5: sidecond_solver.
  Unshelve.
  1-3: first [exact (#(x, x'0, $# x')) | exact (#tt) | sidecond_hammer].
Qed.
End proof.
