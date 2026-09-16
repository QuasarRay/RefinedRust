From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_pop_back_node.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_pop_back_node_proof (π : thread_id) :
  LinkedList_TA_pop_back_node_lemma π.
Proof.
  LinkedList_TA_pop_back_node_prelude.

  rep <-! liRStep; liShow.

  { iRename select (LL _ _ _ _ _)%I into "Hall".
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
       "(%Hloc & %Hnext & %Hprev & Hnode & Hfree)".
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
    rep <-! <500 liRStep.
    rep <-! <3000 liRStep.
     {
      liShow.
      rename select
         ((None :: (Some <$> locs' ++ [r'0])) !! length locs' = Some (Some x'))
         into Hnewtail.
      destruct locs' as [|first_loc locs_tail]; simpl in Hnewtail; [done |].
      odestruct (lookup_lt_is_Some_2 self' (length locs_tail) _) as
         (new_tail_el & Hnew_tail_el).
      { rewrite <- Hlen'; simpl; lia. }
      iPoseProof (LL_last with "Hprefix") as "(Hrest & Hnewtail)".
       { rewrite last_lookup.
         rewrite list_lookup_fmap.
         rewrite length_fmap.
        rewrite -Hlen'/=. rewrite Hnew_tail_el//. }
      iEval (rewrite /LL_item) in "Hnewtail".
      iRevert "Hnewtail".
      rep <-! liRStep; liShow.
      assert (l0 = x') as -> by shelve_sidecond.
      apply_update updateable_strip_guards.
      rep <-! liRStep; liShow.
       {
        iRename select (Allocator_FreeablePerm Allocator_A_spec_attrs a r' _)%I into "Hnewtail_free".
        iRename select (r' ◁ₗ[π, Owned] _ @ _)%I into "Hnewtail_raw".
        iAcquireCredits as "Hnewtail_credit".

        have Hnewtail_prev :
           (None :: (Some <$> (first_loc :: locs_tail))) !! length locs_tail = Some prev.
        { shelve_sidecond. }
        rep liRStep.
        liInst Hevar_self (PlaceIn ∘ RT_xrt T_rt <$> self').
        liInst Hevar_locs (first_loc :: locs_tail).
        liInst Hevar_a a.
        liInst Hevar_x first_loc.
        rep liRStep. liShow.
        iApply (prove_with_subtype_stratify r').
        rep liRStep. liShow.
         iApply prove_with_subtype_default.
        iSplitL "Hrest Hnewtail_free Hnewtail_credit".
        { iIntros "Hnewtail_struct _".
          iApply LL_last.
           { rewrite last_lookup.
             rewrite list_lookup_fmap.
             rewrite length_fmap.
            rewrite -Hlen'/=. rewrite Hnew_tail_el//. }
           iSplitL "Hrest".
          { iApply LL_prefix_stable; last done.
            shelve_sidecond. }
          rewrite /LL_item.
          iExists r', None, prev.
          iSplitR; first (iPureIntro; shelve_sidecond).
          iSplitR; first (iPureIntro; shelve_sidecond).
          iSplitR; first (iPureIntro; shelve_sidecond).
          iFrame.
          iApply guarded_intro. iFrame.
          iApply ltype_own_mut_fixpoint_unfold.
          iApply ltype_own_ex_plain_t_intro.
          iFrame. unfold inv_P; simpl.
          iSplit; done. }
        liRStepUntil owned_subtype.
        rep 20 liRStep.
        liRStepUntil owned_subtype.
        (* TODO: We should have better support for sealing ADTs at module boundaries and then just having Rust's subtyping *)
        iApply owned_subtype_strong_subtype.
        rep liRStep. }
      { rep <-! <3000 liRStep. } }
    { (* The predecessor is [None] exactly when the removed tail was the only node. *)
      destruct locs' as [|first_loc locs_tail]; last (exfalso; shelve_sidecond).
      destruct self' as [|first_el self_tail]; simpl in Hlen'; [|lia].
      rep liRStep.
      {  
        liInst Hevar_self [].
        liInst Hevar_locs [].
        liInst Hevar_a a.
        liRStepUntil owned_subtype.
        rep 20 liRStep.
        liRStepUntil owned_subtype.
        iApply owned_subtype_strong_subtype.
        rep liRStep. }
      { rep <-! <3000 liRStep. } } }
  { (* If the outer option is [None], the old list itself was empty. *)
    rename select (last locs = None) into Hlast.
    apply last_None in Hlast; subst locs.
    destruct self as [|first_el self_tail]; simpl in Hlen; [|lia].
    rep liRStep.
    liInst Hevar_self [].
    liInst Hevar_locs [].
    liInst Hevar_a a.
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve.
  all: try solve [constructor; solve_goal].
  all: sidecond_solver.
  all: sidecond_hammer.
   - have Hidx : length (removelast (PlaceIn ∘ RT_xrt T_rt <$> self')) = length locs_tail.
     { rewrite removelast_firstn_len length_take length_fmap -Hlen' /= Nat.min_l; lia. }
     rename select (_ !! _ = Some l0) into Hnewtail_loc_lookup.
     rewrite Hidx in Hnewtail_loc_lookup.
     change (((first_loc :: locs_tail) ++ [r'0]) !! length locs_tail = Some l0) in Hnewtail_loc_lookup.
     change ((Some <$> ((first_loc :: locs_tail) ++ [r'0])) !! length locs_tail = Some (Some x')) in Hnewtail.
     rewrite list_lookup_fmap in Hnewtail.
     rewrite lookup_app_l in Hnewtail_loc_lookup; last (simpl; lia).
     rewrite lookup_app_l in Hnewtail; last (simpl; lia).
     rewrite Hnewtail_loc_lookup in Hnewtail. simpl in Hnewtail. by simplify_eq.
   - have Hidx : length (removelast (PlaceIn ∘ RT_xrt T_rt <$> self')) = length locs_tail.
     { rewrite removelast_firstn_len length_take length_fmap -Hlen' /= Nat.min_l; lia. }
     rename select ((None :: Some first_loc :: _) !! length (removelast _) = Some prev)
       into Hnewtail_prev_lookup.
     rewrite Hidx in Hnewtail_prev_lookup.
     change ((None :: Some first_loc :: (Some <$> (locs_tail ++ [r'1]))) !! length locs_tail = Some prev) in Hnewtail_prev_lookup.
     rewrite fmap_app /= in Hnewtail_prev_lookup.
     change (((None :: Some first_loc :: (Some <$> locs_tail)) ++ [Some r'1]) !! length locs_tail = Some prev) in Hnewtail_prev_lookup.
     rewrite lookup_app_l in Hnewtail_prev_lookup;
       [exact Hnewtail_prev_lookup | simpl; rewrite length_fmap; lia].
   - exists r'. split; last done.
     rewrite last_lookup /=.
     have Hidx : length (removelast (PlaceIn ∘ RT_xrt T_rt <$> self')) = length locs_tail.
     { rewrite removelast_firstn_len length_take length_fmap -Hlen' /= Nat.min_l; lia. }
     rename select (_ !! _ = Some r') into Hnewtail_loc_lookup.
     rewrite Hidx in Hnewtail_loc_lookup.
     change (((first_loc :: locs_tail) ++ [r'1]) !! length locs_tail = Some r') in Hnewtail_loc_lookup.
     rewrite lookup_app_l in Hnewtail_loc_lookup;
       [exact Hnewtail_loc_lookup | simpl; lia].
  - inversion Hnonnull; done.
  - inversion Hnonnull as [| ? ? Hfirst Htail].
    apply Forall_app in Htail as [Hmiddle _]. exact Hmiddle.
   - have Hidx : length (removelast (PlaceIn ∘ RT_xrt T_rt <$> self')) = length locs_tail.
     { rewrite removelast_firstn_len length_take length_fmap -Hlen' /= Nat.min_l; lia. }
     rewrite Hidx take_app_le; [done | lia].
   - have Hidx : length (removelast (PlaceIn ∘ RT_xrt T_rt <$> self')) = length locs_tail.
     { rewrite removelast_firstn_len length_take length_fmap -Hlen' /= Nat.min_l; lia. }
     rename select (_ !! _ = Some r') into Hnewtail_loc_lookup.
     rewrite Hidx in Hnewtail_loc_lookup |- *.
     change (((first_loc :: locs_tail) ++ [r'1]) !! length locs_tail = Some r') in Hnewtail_loc_lookup.
     rewrite lookup_app_l in Hnewtail_loc_lookup;
       [exact Hnewtail_loc_lookup | simpl; lia].
   - apply lookup_ge_None.
     rewrite removelast_firstn_len length_take length_fmap -Hlen' /= Nat.min_l; lia.
   - have Hidx : length (removelast (PlaceIn ∘ RT_xrt T_rt <$> self')) = length locs_tail.
     { rewrite removelast_firstn_len length_take length_fmap -Hlen' /= Nat.min_l; lia. }
     rewrite Hidx. exact Hnewtail_prev.
  - symmetry. rewrite fmap_app removelast_last//.
   - rewrite removelast_last. destruct locs_tail; reflexivity.
  - rewrite last_snoc. done.
  - change ((Some <$> (first_loc :: locs_tail ++ [r'0])) !! length locs_tail = Some None) in Hprev.
    rewrite list_lookup_fmap in Hprev.
    destruct ((first_loc :: locs_tail ++ [r'0]) !! length locs_tail); discriminate.
Qed.
End proof.
