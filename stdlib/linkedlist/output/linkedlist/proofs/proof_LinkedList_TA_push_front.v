From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_push_front.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_push_front_proof (π : thread_id) :
  LinkedList_TA_push_front_lemma π.
Proof.
  LinkedList_TA_push_front_prelude.

  1: rep <-! <3000 liRStep.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.
End proof.
