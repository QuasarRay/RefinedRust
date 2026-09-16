From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_iter_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_iter_mut_proof (π : thread_id) :
  LinkedList_TA_iter_mut_lemma π.
Proof.
  LinkedList_TA_iter_mut_prelude.

  1: rep <-! <3000 liRStep.
  1: rep liRStep; liShow.
  { iRename select (LL _ _ _ _ _)%I into "Hall".
    iPoseProof (LL_separate_freeable with "Hall") as "[Hnodes Hfree]".
    { by rewrite !length_fmap Hlen. }
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
