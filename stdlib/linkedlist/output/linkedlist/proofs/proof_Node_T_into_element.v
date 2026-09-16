From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_Node_T_into_element.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Node_T_into_element_proof (π : thread_id) :
  Node_T_into_element_lemma π.
Proof.
  Node_T_into_element_prelude.

  rep <-! <3000 liRStep.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.
End proof.
