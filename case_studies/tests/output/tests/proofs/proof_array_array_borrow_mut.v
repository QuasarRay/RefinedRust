From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_array_array_borrow_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma array_array_borrow_mut_proof (π : thread_id) :
  array_array_borrow_mut_lemma π.
Proof.
  array_array_borrow_mut_prelude.

  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
