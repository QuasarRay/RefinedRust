From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_unlink_node.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_unlink_node_proof (π : thread_id) :
  LinkedList_TA_unlink_node_lemma π.
Proof.
  LinkedList_TA_unlink_node_prelude.

  1: liRStepUntil typed_call.
  1: iRename select (LL _ _ _ _ _)%I into "Hall".
  assert (i < length locs)%nat as Hilocs by
    (eapply lookup_lt_Some; exact Hnode).
  odestruct (lookup_lt_is_Some_2 elems i _) as (elem & Helem).
  { rewrite <- Hlen. exact Hilocs. }
  iPoseProof (big_sepL_delete _ _ i with "Hall") as "[Hnode_res Hrest]"; first done.
  iDestruct "Hnode_res" as (node_loc next prev)
    "(%Hnode_loc & %Hnext & %Hprev & Hnode_own & Hnode_free)".
  rewrite Hnode in Hnode_loc; simplify_eq.

  apply_update updateable_strip_guards.
  rep <-! liRStep; liShow.
  apply_update (updateable_start_lft "as_ref_lft1" ["ulft_1"]).
  1: rep <-! liRStep.
  pose_unconstrained_lft_hint "vuclft3" ["as_ref_lft1"].
  rep <-! liRStep.
  { (* there is a predecessor *)
    (* destruct [i] *)
    destruct i as [|pred]; first done.
    odestruct (lookup_lt_is_Some_2 elems pred _) as (prev_elem & Hprev_elem).
    { rewrite <- Hlen. apply lookup_lt_Some in Hnode. lia. }
    liShow.
    iPoseProof (big_sepL_delete _ _ pred with "Hrest") as
         "[Hprev_res Hrest_prev]"; first exact Hprev_elem.
    iEval (rewrite decide_False; last lia) in "Hprev_res".
    iDestruct "Hprev_res" as (prev_loc prev_next prev_prev)
       "(%Hprev_loc & %Hprev_next & %Hprev_prev & Hprev_own & Hprev_free)".
    rewrite /= list_lookup_fmap Hprev_loc /= in Hprev.
    injection Hprev as <-.

    apply_update updateable_strip_guards.
    rep <-! liRStep.
    { (* there is a successor *)
      liShow.
      destruct (locs !! S (S pred)) as [succ_loc|] eqn:Hsucc_lookup; last done.
      odestruct (lookup_lt_is_Some_2 elems (S (S pred)) _) as
        (succ_elem & Hsucc_elem).
      { rewrite <- Hlen. apply lookup_lt_Some in Hsucc_lookup. exact Hsucc_lookup. }
      iPoseProof (big_sepL_delete _ _ (S (S pred)) with "Hrest_prev") as "[Hsucc_res Hremaining]"; first exact Hsucc_elem.
      iEval (rewrite decide_False; last lia) in "Hsucc_res".
      iEval (rewrite decide_False; last lia) in "Hsucc_res".
      iDestruct "Hsucc_res" as (succ_node_loc succ_next succ_prev)
        "(%Hsucc_loc & %Hsucc_next & %Hsucc_prev & Hsucc_own & Hsucc_free)".
      rewrite Hsucc_lookup in Hsucc_loc; simplify_eq.

      apply_update updateable_strip_guards.
      rep <-! liRStep.
      2: rep liRStep.
      liShow.

      (* returning, have to assemble ownership of second part *)
      apply_update (updateable_end_lft "vuclft3").
      rep <-! liRStep.
      apply_update (updateable_end_lft "as_ref_lft1").
      rep <-! <3000 liRStep.
      (* TODO: maybe return context fold should also stratify other things *)
      liRStepUntil typed_context_fold. liShow.
      iApply (typed_context_fold_add_loc node_loc).

      rep liRStep. liShow.
      iApply (prove_with_subtype_stratify r'0).
      rep liRStep. liShow.
      iApply (prove_with_subtype_stratify r').
      rep liRStep. liShow.
      iAcquireCredits as "Hprev_credit".
      iAcquireCredits as "Hsucc_credit".
      iApply prove_with_subtype_default.
      iSplitL "Hremaining Hprev_free Hsucc_free Hprev_credit Hsucc_credit".
      {
        iIntros "Hprev_struct _ Hsucc_struct _".
        iApply (big_sepL_delete _ _ pred).
        { rewrite list_lookup_delete_lt; [exact Hprev_elem|lia]. }
        iSplitL "Hprev_struct Hprev_free Hprev_credit".
        { iExists r', (Some r'0), prev_prev.
          iSplit; first (iPureIntro; rewrite list_lookup_delete_lt; [exact Hprev_loc|lia]).
          iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [exact Hsucc_lookup|lia]).
          iSplit; first (iPureIntro; destruct pred as [|pred']; simpl; [exact Hprev_prev|rewrite list_lookup_fmap; rewrite list_lookup_delete_lt; [rewrite /= list_lookup_fmap in Hprev_prev; exact Hprev_prev|lia]]).
          iSplitL "Hprev_struct Hprev_credit".
          { iApply guarded_intro. iFrame. iApply ltype_own_mut_fixpoint_unfold.
            iApply ltype_own_ex_plain_t_intro. iFrame.
            unfold inv_P; simpl. iSplit; done. }
          iFrame. }
        iApply (big_sepL_delete _ _ (S pred)).
        { rewrite list_lookup_delete_ge; [exact Hsucc_elem|lia]. }
        iSplitL "Hsucc_struct Hsucc_free Hsucc_credit".
        { iEval (rewrite decide_False; last lia).
          iExists r'0, (locs !! S (S (S pred))), (Some r').
          iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [exact Hsucc_lookup|lia]).
          iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [done|lia]).
          iSplit.
          { iPureIntro. simpl. rewrite list_lookup_fmap.
            rewrite list_lookup_delete_lt; [rewrite Hprev_loc; reflexivity|lia]. }
          iSplitL "Hsucc_struct Hsucc_credit".
          { iApply guarded_intro. iFrame. iApply ltype_own_mut_fixpoint_unfold.
            iApply ltype_own_ex_plain_t_intro. iFrame.
            unfold inv_P; simpl. iSplit; done. }
          iFrame. }
        rewrite (delete_take_drop elems (S pred)) big_sepL_app.
        iPoseProof (big_sepL_app _ (take (S pred) elems) (drop (S pred) elems) with "[Hremaining]") as "[Hprefix Htail]".
        { rewrite -big_sepL_app take_drop. iFrame. }
        iEval (rewrite (drop_S elems elem (S pred) Helem)) in "Htail".
        iEval (rewrite big_sepL_cons) in "Htail".
        iDestruct "Htail" as "[_ Htail]".
        iSplitL "Hprefix".
        { iApply (big_sepL_impl with "Hprefix").
          iModIntro. iIntros (k y Hky) "Hnode".
          have Hk : (k < S pred)%nat.
          { apply lookup_lt_Some in Hky. rewrite length_take in Hky.
            apply lookup_lt_Some in Hprev_elem. lia. }
          iEval (rewrite decide_False; last lia).
          destruct (decide (k = pred)) as [->|Hneq].
          { done. }
          iEval (rewrite decide_False; last lia) in "Hnode".
          iEval (rewrite decide_False; last lia) in "Hnode".
          iDestruct "Hnode" as (nl nx pv) "(%Hnl & %Hnx & %Hpv & Hown & Hfree)".
          iExists nl, nx, pv.
          iSplit; first (iPureIntro; rewrite list_lookup_delete_lt; [exact Hnl|lia]).
          iSplit; first (iPureIntro; rewrite list_lookup_delete_lt; [exact Hnx|lia]).
          iSplit.
          { iPureIntro. destruct k as [|k']; simpl; first exact Hpv.
            rewrite list_lookup_fmap. rewrite list_lookup_delete_lt; last lia.
            rewrite /= list_lookup_fmap in Hpv. exact Hpv. }
          iFrame.
        }
        iApply (big_sepL_impl with "Htail").
        iModIntro. iIntros (k y Hky) "Hnode".
        rewrite length_take_le; last (apply lookup_lt_Some in Helem; lia).
        destruct k as [|k].
        { iEval (rewrite decide_True; last lia) in "Hnode".
          iEval (rewrite decide_True; last lia). done. }
        iEval (rewrite decide_False; last lia) in "Hnode".
        iEval (rewrite decide_False; last lia) in "Hnode".
        iEval (rewrite decide_False; last lia) in "Hnode".
        iEval (rewrite decide_False; last lia).
        iEval (rewrite decide_False; last lia).
        iDestruct "Hnode" as (nl nx pv) "(%Hnl & %Hnx & %Hpv & Hown & Hfree)".
        iExists nl, nx, pv.
        assert (Hidx : (S (S pred + S k) = S pred + S (S k))%nat) by lia.
        iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [rewrite Hidx; exact Hnl|lia]).
        iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [rewrite Hidx; exact Hnx|lia]).
        iSplit.
        { iPureIntro. rewrite /= list_lookup_fmap list_lookup_delete_ge; last lia.
          assert (Hprev_idx : (S (pred + S k) = pred + S (S k))%nat) by lia.
          rewrite Hprev_idx.
          rewrite /= list_lookup_fmap in Hpv. exact Hpv. }
        iFrame.
      }
       rep liRStep. }
    { (* there is no successor *)
      rep <-! liRStep; liShow.
      2: rep liRStep.

      (* returning, have to assemble ownership of second part *)
      apply_update (updateable_end_lft "vuclft3").
      rep <-! liRStep.
      apply_update (updateable_end_lft "as_ref_lft1").
      rep <-! <3000 liRStep.
      (* TODO: maybe return context fold should also stratify other things *)
      liRStepUntil typed_context_fold. liShow.
      iApply (typed_context_fold_add_loc node_loc).

      rep liRStep. liShow.
      (*iApply (prove_with_subtype_stratify r'0).*)
      (*rep liRStep. liShow.*)
      iApply (prove_with_subtype_stratify r').
      rep liRStep. liShow.
      iAcquireCredits as "Hprev_credit".
      (*iAcquireCredits as "Hsucc_credit".*)
      iApply prove_with_subtype_default.
       iSplitL "Hrest_prev Hprev_free Hprev_credit".
       {
         iIntros "Hprev_struct _".
         iApply (big_sepL_delete _ _ pred).
         { rewrite list_lookup_delete_lt; [exact Hprev_elem|lia]. }
         iSplitL "Hprev_struct Hprev_free Hprev_credit".
         { iExists r', None, prev_prev.
           iSplit; first (iPureIntro; rewrite list_lookup_delete_lt; [exact Hprev_loc|lia]).
           iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [exact H37|lia]).
           iSplit; first (iPureIntro; destruct pred as [|pred']; simpl; [exact Hprev_prev|rewrite list_lookup_fmap; rewrite list_lookup_delete_lt; [rewrite /= list_lookup_fmap in Hprev_prev; exact Hprev_prev|lia]]).
           iSplitL "Hprev_struct Hprev_credit".
           { iApply guarded_intro. iFrame. iApply ltype_own_mut_fixpoint_unfold.
             iApply ltype_own_ex_plain_t_intro. iFrame.
             unfold inv_P; simpl. iSplit; [iPureIntro; rewrite H37; done|done]. }
           iFrame. }
         rewrite (delete_take_drop elems (S pred)) big_sepL_app.
         iPoseProof (big_sepL_app _ (take (S pred) elems) (drop (S pred) elems) with "[Hrest_prev]") as "[Hprefix Htail]".
         { rewrite -big_sepL_app take_drop. iFrame. }
         iEval (rewrite (drop_S elems elem (S pred) Helem)) in "Htail".
         iEval (rewrite big_sepL_cons) in "Htail".
         iDestruct "Htail" as "[_ Htail]".
         iSplitL "Hprefix".
         { iApply (big_sepL_impl with "Hprefix").
           iModIntro. iIntros (k y Hky) "Hnode".
           have Hk : (k < S pred)%nat.
           { apply lookup_lt_Some in Hky. rewrite length_take in Hky.
             apply lookup_lt_Some in Hprev_elem. lia. }
           destruct (decide (k = pred)) as [->|Hneq].
           { done. }
           iEval (rewrite decide_False; last lia) in "Hnode".
           iDestruct "Hnode" as (nl nx pv) "(%Hnl & %Hnx & %Hpv & Hown & Hfree)".
           iExists nl, nx, pv.
           iSplit; first (iPureIntro; rewrite list_lookup_delete_lt; [exact Hnl|lia]).
           iSplit; first (iPureIntro; rewrite list_lookup_delete_lt; [exact Hnx|lia]).
           iSplit.
           { iPureIntro. destruct k as [|k']; simpl; first exact Hpv.
             rewrite list_lookup_fmap. rewrite list_lookup_delete_lt; last lia.
             rewrite /= list_lookup_fmap in Hpv. exact Hpv. }
           iFrame. }
         have Htail_nil : drop (S (S pred)) elems = [].
         { apply drop_ge. apply lookup_ge_None in H37. rewrite Hlen in H37. lia. }
         rewrite Htail_nil big_sepL_nil. iFrame.
       }

       rep liRStep. }
  }
  { (* there is no predecessor *)
    assert (i = 0%nat).
    { move: Hprev. clear. destruct i as [ | i]; simpl; first done.
      induction locs as [ | l locs IH] in i |-*; simpl; first done.
      destruct i; first done.
      simpl. intros ?%IH. done. }

    rep <-! liRStep; liShow.
    { (* there is a successor *)
      1: liShow.
      1: destruct (locs !! 1%nat) as [succ_loc|] eqn:Hsucc_lookup; last done.
      1: odestruct (lookup_lt_is_Some_2 elems 1%nat _) as (succ_elem & Hsucc_elem).
      1: { rewrite <- Hlen. apply lookup_lt_Some in Hsucc_lookup. exact Hsucc_lookup. }
      1: iPoseProof (big_sepL_delete _ _ 1%nat with "Hrest") as "[Hsucc_res Hremaining]"; first exact Hsucc_elem.
      1: iEval (simpl) in "Hsucc_res".
      1: iDestruct "Hsucc_res" as (succ_node_loc succ_next succ_prev)
       "(%Hsucc_loc & %Hsucc_next & %Hsucc_prev & Hsucc_own & Hsucc_free)".
      1: rewrite Hsucc_lookup in Hsucc_loc; simplify_eq.

      1: apply_update updateable_strip_guards.
      1: rep <-! liRStep.
      2: { (* doesn't overflow *)rep liRStep. }

      apply_update (updateable_end_lft "vuclft3").
      rep <-! liRStep.
      apply_update (updateable_end_lft "as_ref_lft1").
      rep <-! <3000 liRStep.
      (* TODO: maybe return context fold should also stratify other things *)
      liRStepUntil typed_context_fold. liShow.
      iApply (typed_context_fold_add_loc node_loc).

      rep liRStep. liShow.
      (*iApply (prove_with_subtype_stratify r'0).*)
      (*rep liRStep. liShow.*)
      iApply (prove_with_subtype_stratify r').
      rep liRStep. liShow.
      (*iAcquireCredits as "Hprev_credit".*)
      iAcquireCredits as "Hsucc_credit".
       iApply prove_with_subtype_default.
       iSplitL "Hremaining Hsucc_free Hsucc_credit".
       { (* We have to re-establish the bigsep*)
         iIntros "Hsucc_struct _".
         iApply (big_sepL_delete _ _ 0%nat).
         { rewrite list_lookup_delete_ge; [exact Hsucc_elem|lia]. }
         iSplitL "Hsucc_struct Hsucc_free Hsucc_credit".
         { iExists r', (locs !! 2%nat), None.
           iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [exact Hsucc_lookup|lia]).
           iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [done|lia]).
           iSplit; first (iPureIntro; done).
           iSplitL "Hsucc_struct Hsucc_credit".
           { iApply guarded_intro. iFrame. iApply ltype_own_mut_fixpoint_unfold.
             iApply ltype_own_ex_plain_t_intro. iFrame.
             unfold inv_P; simpl. iSplit; done. }
           iFrame. }
         rewrite (delete_take_drop elems 0%nat) /=.
         iPoseProof (big_sepL_app _ (take 1 elems) (drop 1 elems) with "[Hremaining]") as "[_ Htail]".
         { rewrite -big_sepL_app take_drop. iFrame. }
         iApply (big_sepL_impl with "Htail").
         iModIntro. iIntros (k y Hky) "Hnode".
         rewrite length_take_le; last (apply lookup_lt_Some in Helem; lia).
         destruct k as [|k].
         { iEval (simpl) in "Hnode". iEval (simpl). done. }
         iEval (simpl) in "Hnode". iEval (simpl).
         iDestruct "Hnode" as (nl nx pv) "(%Hnl & %Hnx & %Hpv & Hown & Hfree)".
         iExists nl, nx, pv.
         iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [exact Hnl|lia]).
         iSplit; first (iPureIntro; rewrite list_lookup_delete_ge; [exact Hnx|lia]).
         iSplit.
         { iPureIntro. rewrite /= list_lookup_fmap list_lookup_delete_ge; last lia.
           rewrite /= list_lookup_fmap in Hpv. exact Hpv. }
         iFrame.
       }
      rep  liRStep; liShow. }
    { (* there is no successor *)
      rep <-! liRStep; liShow.
      2: rep liRStep.

      apply_update (updateable_end_lft "vuclft3").
      rep <-! liRStep.
      apply_update (updateable_end_lft "as_ref_lft1").
      rep <-! <3000 liRStep.
      (* TODO: maybe return context fold should also stratify other things *)
      liRStepUntil typed_context_fold. liShow.
      iApply (typed_context_fold_add_loc node_loc).


      rep liRStep; liShow.
      destruct locs as [ | l0 [ | l1 locs]]; [ simpl in *; lia |  | simpl in *; done].
      destruct elems as [ | e0 [ | e1 elems]]; [ simpl in *; lia |  | simpl in *; done].
      simpl in*. simplify_eq.
      rep liRStep.
    }
  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  all: try by apply Forall_delete.
  all: try (rewrite length_delete; first solve_goal; last done).
  all: try (erewrite list_lookup_total_correct; last done; first done).

  all: try (match goal with
    | |- context [head (delete (S ?i) ?xs)] =>
        destruct xs as [|hdloc xs_locs];
        [simpl in Hnode; discriminate|reflexivity]
    end).
  all: try (match goal with
    | |- Some ?r = last (take (S ?i) ?xs) =>
        rewrite (take_S_r xs i r); [rewrite last_snoc; reflexivity|assumption]
    end).
  all: try apply unit.
  - rewrite (delete_take_drop locs (S pred));
    rewrite <- (take_drop (S (S pred)) locs) at 1;
    rewrite !last_app;
    destruct (last (drop (S (S pred)) locs)) eqn:Hlast;
    [reflexivity|];
    apply last_None in Hlast;
    apply lookup_lt_Some in Hsucc_lookup;
    assert (length (drop (S (S pred)) locs) = 0)%nat as Hzero
      by (rewrite Hlast; reflexivity);
    rewrite length_drop in Hzero; lia.
  - match goal with
    | |- exists _, last (delete (S ?i) ?xs) = _ /\ _ =>
        exists r'; split;
        [rewrite delete_take_drop;
         assert (drop (S (S i)) xs = []) as Hdrop
           by (apply drop_ge; apply lookup_ge_None in H37; lia);
         rewrite Hdrop app_nil_r;
         rewrite (take_S_r xs i r' Hprev_loc) last_snoc;
         reflexivity|reflexivity]
    end.
  - exists eq_refl; reflexivity.
  - exists r'; split;
    [rewrite head_lookup list_lookup_delete_ge;
     [exact Hsucc_lookup|lia]|reflexivity].
  - rewrite (delete_take_drop locs 0); simpl;
    rewrite <- (take_drop 1 locs) at 1;
    rewrite last_app;
    destruct (last (drop 1 locs)) eqn:Hlast;
    [reflexivity|];
    apply last_None in Hlast;
    apply lookup_lt_Some in Hsucc_lookup;
    assert (length (drop 1 locs) = 0)%nat as Hzero
      by (rewrite Hlast; reflexivity);
    rewrite length_drop in Hzero; lia.
  - exists eq_refl. done.
  - try (rewrite head_lookup list_lookup_delete_ge; [reflexivity|lia]).
  - rewrite delete_take_drop; simpl;
    apply last_None, drop_ge.
    rename select (locs !! 1%nat = None) into Hnone.
    apply lookup_ge_None in Hnone; lia.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
