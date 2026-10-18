From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_try_with_capacity_in.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_try_with_capacity_in_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_try_with_capacity_in_lemma π.
Proof.
  raw_vec_implRawVecInnerA_try_with_capacity_in_prelude.

  1: rep <-! <3000 liRStep.
  rename select val into allocated_bytes.
  1: match goal with
    | allocation_result : result _ reserve_error |- _ =>
        destruct allocation_result as [[[l cap] a] | err]
    end.
  all: simpl.
  all: rep <-! <3000 liRStep.
  all: rep liRStep.
  { liInst Hevar_x2 allocated_bytes.
    rep <-! <3000 liRStep. }
  { destruct err.
    all: rep <-! <3000 liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
