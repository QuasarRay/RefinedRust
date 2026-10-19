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
  {
    rep liRStep.
    liInst Hevar_r2 (mk_rust_layout (Z.to_nat (n * alignment_to_align alignment)) alignment).
    split; first done. split; first done.
    liFromSyntaxGoal. rep <-! <3000 liRStep.
  }
  { rep <-! <3000 liRStep. }
  Unshelve.
  1-15: sidecond_solver.
  Unshelve.
  - pose proof (layout_alignment_bounds alignment). nia.
  - rewrite /layout_wf /ly_align /rust_layout_to_layout /layout_alignment_log2_nat /= Nat2Z.inj_pow.
    change (alignment_to_align alignment | Z.of_nat (Z.to_nat (n * alignment_to_align alignment))).
    rewrite Z2Nat.id; last (pose proof (layout_alignment_bounds alignment); nia).
    exists n; ring.
  - pose proof (layout_alignment_bounds alignment). unfold int_elem_of_it. split; [solve_goal | lia].
  - rewrite bool_decide_true; first done.
    pose proof (layout_alignment_bounds r'). lia.
  - rewrite bool_decide_false; first done.
    intros Hbound.
    assert (Hdiv : (alignment_to_align r' | n * alignment_to_align r')) by (exists n; ring).
    apply (proj2 (layout_aligned_size_valid _ r' Hdiv)) in Hbound.
    lia.
Qed.
End proof.
