From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_iter.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_iter_proof (π : thread_id) :
  LinkedList_TA_iter_lemma π.
Proof.
  LinkedList_TA_iter_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_all_elems self.
  liInst Hevar_locs locs.
  liInst Hevar_idx 0%nat.
  liInst Hevar_back_idx (length self).
  rep liRStep; liShow.
  iRename select (LL _ _ _ _ _)%I into "Hall".
  iEval (rewrite LL_fmap) in "Hall".
  iApply prove_with_subtype_default.
  iSplitL "Hall". { done. }
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: try solve [rewrite list_fmap_id take_ge; [done | lia]].
  Unshelve. all: try solve [rewrite take_ge; [done | lia]].
  Unshelve. all: try solve [rewrite head_lookup; reflexivity].
  Unshelve. all: sidecond_hammer.
Qed.
End proof.
