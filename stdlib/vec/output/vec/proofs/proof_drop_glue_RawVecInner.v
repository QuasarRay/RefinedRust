From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_drop_glue_RawVecInner.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_RawVecInner_proof (π : thread_id) :
  drop_glue_RawVecInner_lemma π.
Proof.
  drop_glue_RawVecInner_prelude.

  rep <-! <3000 liRStep.
  Unshelve.
  1-3: sidecond_solver.
  Unshelve.
  1-5: first [exact (#x) | exact (#(Z.of_nat x0)) | exact (#($# x1)) | sidecond_hammer].
  Unshelve. sidecond_solver.
Qed.
End proof.
