From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_repeat_packed.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma layout_Layout_repeat_packed_proof (π : thread_id) :
  layout_Layout_repeat_packed_lemma π.
Proof.
  layout_Layout_repeat_packed_prelude.

  assert (Hisize_max : MaxInt isize = 9223372036854775807).
  { rewrite MaxInt_eq. reflexivity. }

  1: rep <-! <3000 liRStep.
  all: rep <-! <3000 liRStep.
  all: case_bool_decide as Hproduct_fits.
  all: simplify_eq.
  all: simpl.
  all: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rewrite /alignment_to_align -(Nat2Z.inj_pow 2) Nat2Z.id.
    eexists _. reflexivity.
  - apply Z.divide_mul_l.
    rename select (layout_wf self) into Hlayout_wf.
    rewrite /layout_wf /ly_align /rust_layout_to_layout
      /layout_alignment_log2_nat /= in Hlayout_wf.
    rewrite /alignment_to_align -(Nat2Z.inj_pow 2).
    exact Hlayout_wf.
  - rewrite bool_decide_true; last lia.
    rewrite alignment_from_to.
    eexists _. split; reflexivity.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
