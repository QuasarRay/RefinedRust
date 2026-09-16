From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_ExtractIf_TFAasstd_iter_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma ExtractIf_TFAasstd_iter_Iterator_next_proof (π : thread_id) :
  ExtractIf_TFAasstd_iter_Iterator_next_lemma π.
Proof.
  ExtractIf_TFAasstd_iter_Iterator_next_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
