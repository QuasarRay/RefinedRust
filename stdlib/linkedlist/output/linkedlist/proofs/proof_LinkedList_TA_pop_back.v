From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_pop_back.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_pop_back_proof (π : thread_id) :
  LinkedList_TA_pop_back_lemma π.
Proof.
  LinkedList_TA_pop_back_prelude.

  rep <-! liRStep; liShow.

  revert select (if_None x' _). revert select (if_Some x' _).
  destruct x' as [[[next prev] element]|].
  - rep liRStep.
    (* Expose the remaining concrete elements to the LinkedList resolver. *)
    iEval (rewrite removelast_firstn_len length_fmap -fmap_take list_fmap_compose).
    1: rep <-! <3000 liRStep.
  - intros _ ->.
    1: rep <-! <3000 liRStep.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: first
    [ rename select (last self = Some element) into Hlast; rewrite Hlast; done
    | rewrite removelast_firstn_len length_fmap -fmap_take list_fmap_compose; done ].
Qed.
End proof.
