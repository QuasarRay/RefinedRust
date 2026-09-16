From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_pop_back_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_pop_back_closure0_proof (π : thread_id) :
  LinkedList_TA_pop_back_closure0_lemma π.
Proof.
  LinkedList_TA_pop_back_closure0_prelude.

  rep <-! liRStep; liShow.

  Unshelve. all: sidecond_solver.
  all: sidecond_hammer.
Qed.
End proof.
