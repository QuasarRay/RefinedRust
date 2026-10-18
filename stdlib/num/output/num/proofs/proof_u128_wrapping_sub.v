From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num.generated Require Import generated_code_num generated_specs_num generated_template_u128_wrapping_sub.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u128_wrapping_sub_proof (π : thread_id) :
  u128_wrapping_sub_lemma π.
Proof.
  u128_wrapping_sub_prelude.
  assert (Hmax : MaxInt u128 = 340282366920938463463374607431768211455) by (rewrite MaxInt_eq; reflexivity).

  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
