From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_is_size_alignment_valid.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma layout_Layout_is_size_alignment_valid_proof (π : thread_id) :
  layout_Layout_is_size_alignment_valid_lemma π.
Proof.
  layout_Layout_is_size_alignment_valid_prelude.

  1: rep <-! <3000 liRStep.
  Unshelve.
  1-5: sidecond_solver.
Qed.
End proof.
