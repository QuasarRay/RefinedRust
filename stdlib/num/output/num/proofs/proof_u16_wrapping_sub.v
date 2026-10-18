From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num.generated Require Import generated_code_num generated_specs_num generated_template_u16_wrapping_sub.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u16_wrapping_sub_proof (π : thread_id) :
  u16_wrapping_sub_lemma π.
Proof.
  u16_wrapping_sub_prelude.
  assert (Hmax : MaxInt u16 = 65535) by (rewrite MaxInt_eq; reflexivity).

  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
