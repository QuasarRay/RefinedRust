From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_pop_front.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_pop_front_proof (π : thread_id) :
  LinkedList_TA_pop_front_lemma π.
Proof.
  LinkedList_TA_pop_front_prelude.

  rep <-! liRStep; liShow.

  revert select (if_None x' _). revert select (if_Some x' _).
  destruct x' as [[[next prev] element]|].
  - rep liRStep.
    (* Expose the remaining concrete elements to the LinkedList resolver. *)
    iEval (rewrite -fmap_tail list_fmap_compose).
    1: rep <-! <3000 liRStep.
  - intros _ ->.
    1: rep <-! <3000 liRStep.

  Unshelve. all: sidecond_solver.
  all: sidecond_hammer.
  all: first
    [ rename select (head self = Some element) into Hhead; rewrite Hhead; done
    | rewrite -fmap_tail list_fmap_compose; done ].
Qed.
End proof.
