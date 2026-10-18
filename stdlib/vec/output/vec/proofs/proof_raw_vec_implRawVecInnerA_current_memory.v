From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_current_memory.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_current_memory_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_current_memory_lemma π.
Proof.
  raw_vec_implRawVecInnerA_current_memory_prelude.

  1: rep <-! <3000 liRStep.
  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rewrite /layout_alignment_nat /alignment_to_align_nat.
    eexists _. reflexivity.
  - apply Z.divide_mul_l.
    rename select (layout_wf elem_layout) into Hlayout_wf.
    rewrite /layout_wf /ly_align /rust_layout_to_layout
      /layout_alignment_log2_nat /= in Hlayout_wf.
    exact Hlayout_wf.
  - rewrite /layout_alignment_nat /alignment_to_align_nat Nat2Z.inj_pow /=.
    rewrite -/alignment_to_align alignment_from_to. reflexivity.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
