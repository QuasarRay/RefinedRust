From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_cursor_back.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_cursor_back_proof (π : thread_id) :
  LinkedList_TA_cursor_back_lemma π.
Proof.
  LinkedList_TA_cursor_back_prelude.

  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { by rewrite last_lookup Hlen. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
