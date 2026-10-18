From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInner_with_capacity.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInner_with_capacity_proof (π : thread_id) :
  raw_vec_implRawVecInner_with_capacity_lemma π.
Proof.
  raw_vec_implRawVecInner_with_capacity_prelude.

  1: rep <-! <3000 liRStep.
  all: rep <-! <3000 liRStep.
  all: rep liRStep.
  { match goal with Hzeroed : false = true → ?allocated_bytes = _ |- _ =>
      liInst Hevar_x0 allocated_bytes
    end.
    rep <-! <3000 liRStep. }
  { match goal with err : reserve_error |- _ => destruct err end.
    all: rep <-! <3000 liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
