From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_push_front_node.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_push_front_node_proof (π : thread_id) :
  LinkedList_TA_push_front_node_lemma π.
Proof.
  LinkedList_TA_push_front_node_prelude.

  rep <-! liRStep; liShow.
  { iRename select (LL _ _ _ _ _)%I into "Hall".
    rename select (head locs = Some _) into Hhead.
    apply head_Some in Hhead as (locs' & ->).
    destruct elems as [|head_el elems']; simpl in Hlen; [lia|].
    iEval (rewrite LL_cons) in "Hall".
    iDestruct "Hall" as "[Hhead Htail]".
    iDestruct "Hhead" as (head_loc next prev) "(%Hloc & %Hnext & %Hprev & Hnode & Hfree)".
    simpl in Hloc, Hnext, Hprev; simplify_eq.
    apply_update updateable_strip_guards.
    rep <-! <3000 liRStep.
    { rep liRStep. iEval (rewrite LL_cons). 
      iEval (rewrite LL_segment_cons).
      rep liRStep. }
    { rep liRStep. } 
  } 
  { destruct locs as [|old_head locs']; simpl in *; [|done].
    destruct elems as [|old_el elems']; simpl in Hlen; [|lia].
    rep <-! <3000 liRStep.
    rep liRStep.
    iEval (rewrite LL_cons).
    rep liRStep.
    iEval (rewrite LL_segment_nil). 
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.
End proof.
