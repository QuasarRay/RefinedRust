From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num.generated Require Import generated_code_num generated_specs_num generated_template_u128_unchecked_mul.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u128_unchecked_mul_proof (π : thread_id) :
  u128_unchecked_mul_lemma π.
Proof.
  u128_unchecked_mul_prelude.

  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
