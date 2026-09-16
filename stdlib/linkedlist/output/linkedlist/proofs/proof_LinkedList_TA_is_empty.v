From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_is_empty.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_is_empty_proof (π : thread_id) :
  LinkedList_TA_is_empty_lemma π.
Proof.
  LinkedList_TA_is_empty_prelude.

  rep <-! liRStep; liShow.

  Unshelve. all: sidecond_solver.
  all: destruct self, locs; simpl in Hlen; naive_solver.
Qed.
End proof.
