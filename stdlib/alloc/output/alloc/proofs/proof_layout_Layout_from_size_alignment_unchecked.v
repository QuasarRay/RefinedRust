From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_from_size_alignment_unchecked.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma layout_Layout_from_size_alignment_unchecked_proof (π : thread_id) :
  layout_Layout_from_size_alignment_unchecked_lemma π.
Proof.
  layout_Layout_from_size_alignment_unchecked_prelude.

  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  rewrite /layout_wf /ly_align /rust_layout_to_layout /layout_alignment_log2_nat /= Nat2Z.inj_pow.
  change (alignment_to_align r' | Z.of_nat (Z.to_nat (n * alignment_to_align r'))).
  rewrite Z2Nat.id; last nia.
  exists n; ring.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
