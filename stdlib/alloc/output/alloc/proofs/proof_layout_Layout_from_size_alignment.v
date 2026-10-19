From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_from_size_alignment.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma layout_Layout_from_size_alignment_proof (π : thread_id) :
  layout_Layout_from_size_alignment_lemma π.
Proof.
  layout_Layout_from_size_alignment_prelude.
  assert (Hisize_max : MaxInt isize = 9223372036854775807) by (rewrite MaxInt_eq; reflexivity).

  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
