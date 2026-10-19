From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_max_size_for_alignment.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma layout_Layout_max_size_for_alignment_proof (π : thread_id) :
  layout_Layout_max_size_for_alignment_lemma π.
Proof.
  layout_Layout_max_size_for_alignment_prelude.

  assert (Hisize_max : MaxInt isize = 9223372036854775807) by (rewrite MaxInt_eq; reflexivity).
  assert (Husize_max : MaxInt usize = 18446744073709551615) by (rewrite MaxInt_eq; reflexivity).
  pose proof (layout_alignment_bounds alignment) as Halignment.
  1: rep <-! <3000 liRStep.
  Unshelve.
  1-14: sidecond_solver.
  Unshelve.
  1-5: sidecond_hammer.
Qed.
End proof.
