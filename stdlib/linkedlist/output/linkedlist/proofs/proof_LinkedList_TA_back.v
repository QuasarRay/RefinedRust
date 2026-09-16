From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_back.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_back_proof (π : thread_id) :
  LinkedList_TA_back_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft4" ["ulft_1"].
  LinkedList_TA_back_prelude.

  rep <-! liRStep; liShow.
  { iRename select (LL _ _ _ _ _ )%I into "Hall".
    rename select (last locs = Some _) into Htail.
    apply last_Some in Htail as (locs' & ->).
    assert (self ≠ []) as Hself by
      (intros ->; rewrite length_app in Hlen; simpl in Hlen; lia).
    destruct (exists_last Hself) as (self' & tail_el & ->).
    simpl in Hlen.
    iEval (rewrite !fmap_app LL_snoc) in "Hall".
    iDestruct "Hall" as "[Hprefix Htail]".
    iSimpl in "Htail".
    iDestruct "Htail" as (tail_loc next prev)
      "(%Hloc & %Hnext & %Hprev & Hnode & _)".
    assert (length locs' = length self') as Hlen' by
      (rewrite !length_app in Hlen; simpl in Hlen; lia).
    rewrite length_map in Hloc, Hnext, Hprev.
    rewrite <- Hlen' in Hloc, Hnext, Hprev.
    replace (length locs' + 0)%nat with (length locs') in Hloc, Hnext, Hprev by lia.
    have Hloc' : (locs' ++ [x']) !! length locs' = Some x' by
      (erewrite lookup_app_r; [rewrite Nat.sub_diag; reflexivity | lia]).
    have Hnext' : (locs' ++ [x']) !! S (length locs') = None by
         (erewrite lookup_app_r;
          [replace (S (length locs') - length locs')%nat with 1%nat by lia; reflexivity | lia]).
    rewrite Hloc' in Hloc; rewrite Hnext' in Hnext; simplify_eq.
    rewrite last_snoc.
    apply_update updateable_strip_guards.
    rep <-! <3000 liRStep. }
  { rename select (last locs = None) into Htail.
    apply last_None in Htail; subst locs.
    destruct self; simpl in Hlen; [|lia].
    rep <-! <3000 liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - exists tail_el. rewrite last_snoc. done.
Qed.
End proof.
