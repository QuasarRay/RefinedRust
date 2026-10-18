From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_reserve_do_reserve_and_handle.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_reserve_do_reserve_and_handle_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_reserve_do_reserve_and_handle_lemma π.
Proof.
  raw_vec_implRawVecInnerA_reserve_do_reserve_and_handle_prelude.

  rep 3000 liRStep.
  rep liRStep.
  liInst Hevar_x1 v.
  liShow. iApply prove_with_subtype_default. iFrame.
  liFromSyntaxGoal.
  rep 1000 liRStep.
  { (* Successful growth. *)
    liInst Hevar_x2 x'1.
    liShow. iApply prove_with_subtype_default. iFrame.
    liFromSyntaxGoal. rep 1000 liRStep.
  }
  { (* Failure preserves the original state before invoking the error handler. *)
    rep 3000 liRStep.
  }
  Unshelve.
  1-14: sidecond_solver.
  Unshelve.
  - sidecond_hammer.
  - sidecond_hammer.
  - sidecond_hammer.
Qed.
End proof.
