From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_min_non_zero_cap.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_min_non_zero_cap_proof (π : thread_id) :
  raw_vec_min_non_zero_cap_lemma π.
Proof.
  raw_vec_min_non_zero_cap_prelude.

  have Husize_max : MaxInt usize = 18446744073709551615 by rewrite MaxInt_eq; reflexivity.
  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  all: unfold raw_vec_min_non_zero_cap; repeat case_decide; lia.
Qed.
End proof.
