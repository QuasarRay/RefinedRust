From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_size_rounded_up_to_custom_alignment.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma layout_Layout_size_rounded_up_to_custom_alignment_proof (π : thread_id) :
  layout_Layout_size_rounded_up_to_custom_alignment_lemma π.
Proof.
  layout_Layout_size_rounded_up_to_custom_alignment_prelude.
  pose proof (layout_alignment_bounds alignment) as Halignment.
  assert (Hmax_relation : 2 * MaxInt isize + 1 = MaxInt usize) by (rewrite !MaxInt_eq; reflexivity).

  1: rep <-! <3000 liRStep.
  Unshelve.
  1-15: sidecond_solver.
  Unshelve.
  1-4: sidecond_hammer.
  Unshelve.
  apply layout_round_up_aligned; [done | |].
  - change (0 ≤ Z.of_nat self.(layout_sz) < 18446744073709551616).
    assert (Hmax : MaxInt isize = 9223372036854775807) by (rewrite MaxInt_eq; reflexivity).
    lia.
  - exists n. done.
Qed.
End proof.
