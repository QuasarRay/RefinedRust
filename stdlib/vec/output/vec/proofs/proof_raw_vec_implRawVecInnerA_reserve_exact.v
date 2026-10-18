From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_reserve_exact.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_reserve_exact_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_reserve_exact_lemma π.
Proof.
  raw_vec_implRawVecInnerA_reserve_exact_prelude.

  1: rep 3000 liRStep.
  1: rep liRStep.
  1: liInst Hevar_x1 v.
  1: liShow.
  1: iApply prove_with_subtype_default.
  1: iFrame.
  1: liFromSyntaxGoal.
  all: rep 1000 liRStep.
  all: rep liRStep.
  1: liInst Hevar_x0 x'2.
  1: liShow.
  1: iApply prove_with_subtype_default.
  1: iFrame.
  1: liFromSyntaxGoal.
  all: rep 1000 liRStep.
  all: rep liRStep.

  all: print_remaining_goal.
  Unshelve.
  all: try exact ([] : val).
  all: try exact (self : loc).
  all: try exact (self0 : nat).
  all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
