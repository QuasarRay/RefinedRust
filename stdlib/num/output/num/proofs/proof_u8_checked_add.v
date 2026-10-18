From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num.generated Require Import generated_code_num generated_specs_num generated_template_u8_checked_add.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u8_checked_add_proof (π : thread_id) :
  u8_checked_add_lemma π.
Proof.
  u8_checked_add_prelude.
  assert (Hmax : MaxInt u8 = 255) by (rewrite MaxInt_eq; reflexivity).

  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
