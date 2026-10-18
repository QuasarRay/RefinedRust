From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num.generated Require Import generated_code_num generated_specs_num generated_template_u128_checked_sub.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u128_checked_sub_proof (π : thread_id) :
  u128_checked_sub_lemma π.
Proof.
  u128_checked_sub_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
