From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num.generated Require Import generated_code_num generated_specs_num generated_template_usize_checked_add.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma usize_checked_add_proof (π : thread_id) :
  usize_checked_add_lemma π.
Proof.
  usize_checked_add_prelude.
  assert (Husize_max : MaxInt usize = 18446744073709551615).
  { rewrite MaxInt_eq. reflexivity. }

  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
