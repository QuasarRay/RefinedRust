From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_try_shrink_to_fit.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_try_shrink_to_fit_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_try_shrink_to_fit_lemma π.
Proof.
  raw_vec_implRawVecInnerA_try_shrink_to_fit_prelude.

  rep 1000 liRStep.
  rep liRStep.
  liInst Hevar_x1 v. liShow. iApply prove_with_subtype_default.
  iFrame. liFromSyntaxGoal. rep 2000 liRStep.
  Unshelve.
  1-6: sidecond_solver.
  Unshelve.
  eexists _, _. repeat split; try reflexivity; assumption.
Qed.
End proof.
