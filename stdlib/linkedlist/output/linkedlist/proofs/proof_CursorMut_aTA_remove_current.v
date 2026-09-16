From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_CursorMut_aTA_remove_current.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma CursorMut_aTA_remove_current_proof (π : thread_id) :
  CursorMut_aTA_remove_current_lemma π.
Proof.
  CursorMut_aTA_remove_current_prelude.

  1: rep <-! <3000 liRStep.
  { rep liRStep.
    destruct (linked_list_locs (cursor_list self) !! cursor_pos self) as [loc_cur |] eqn:Hlookup; last done.
    rep <-! <3000 liRStep.
    pose_unconstrained_lft_hint "vuclft6" ["ulft_a"].
    iRename select (LL _ _ _ _ _)%I into "Hall".
    odestruct (lookup_lt_is_Some_2 (linked_list_elems (cursor_list self)) (cursor_pos self) _) as (elem & Helem).
    { rewrite <- Hlen. eapply lookup_lt_Some; exact Hlookup. }
    have Hmapped : ((PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)) !! cursor_pos self) =
      Some (PlaceIn (RT_xrt T_rt elem)).
    { by rewrite list_lookup_fmap Helem. }
    iPoseProof (LL_extract _ _ _ _ _ (cursor_pos self) _ with "Hall") as "[Hitem Hrest]"; first exact Hmapped.
    iDestruct "Hitem" as (node_loc next prev) "(%Hloc & %Hnext & %Hprev & Hnode & Hfree)".
    rewrite Hlookup in Hloc. injection Hloc as <-.
    apply_update updateable_strip_guards.
    liRStepUntil typed_call.
    liRStep.
    liRStepUntil typed_call.
    apply_update (updateable_end_lft "vuclft6").
    rep liRStep.
    liInst Hevar_x3 (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)).
    liInst Hevar_x4 (cursor_pos self).
    liInst Hevar_x5 (linked_list_alloc (cursor_list self)).
    liRStepUntil prove_with_subtype.
    iApply (prove_with_subtype_stratify r').
    rep liRStep. liShow.
    iAcquireCredits as "Hguard".
    iApply prove_with_subtype_default.
    iSplitL "Hrest Hfree Hguard".
    { iIntros "Hnode _".
      have Hlayout : use_struct_layout_alg' (Node_sls (st_of T_ty MetaNone)) = Node_sl.
      { apply simplify_use_struct_layout_alg'. solve_goal. }
      iEval (rewrite Hlayout) in "Hrest Hfree".
      iSplit; first (iPureIntro; rewrite /name_hint length_fmap; exact Hlen).
      iSplit; first done.
      iSplit; first done.
      iSplit; first (iPureIntro; by rewrite /name_hint length_fmap).
      rewrite (LL_extract _ _ _ _ _ (cursor_pos self)).
      2: { exact Hmapped. }
      iFrame "Hrest".
      iExists r', (linked_list_locs (cursor_list self) !! S (cursor_pos self)), prev.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iFrame "Hfree".
      iApply guarded_intro. rewrite !option_fmap_id. iFrame.
    }
    { rep <-! <3000 liRStep.
      rep liRStep. liShow.
      iRename select (LL _ _ _ _ _)%I into "Hall".
      have Hlayout : use_struct_layout_alg' (Node_sls (st_of T_ty MetaNone)) = Node_sl.
      { apply simplify_use_struct_layout_alg'. solve_goal. }
      iEval (rewrite -Hlayout) in "Hall".
      iApply prove_with_subtype_default.
      iSplitL "Hall".
      { iExact "Hall". }
      { rep liRStep.
        liInst Hevar_rf (mk_cursor_mut_x (mk_linked_list_x (delete (cursor_pos self) (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self))) (delete (cursor_pos self) (linked_list_locs (cursor_list self))) (linked_list_alloc (cursor_list self))) self.(cursor_pos) self.(cursor_ghost)).
        rep <-! <3000 liRStep.
      }
    }
  }
  { destruct (linked_list_locs (cursor_list self) !! cursor_pos self) as [loc_cur |] eqn:Hlookup; first done.
    rep liRStep.
    liInst Hevar_rf (mk_cursor_mut_x (mk_linked_list_x (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)) (linked_list_locs (cursor_list self)) (linked_list_alloc (cursor_list self))) self.(cursor_pos) self.(cursor_ghost)).
    rep <-! <3000 liRStep.
  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { by rewrite list_lookup_delete_ge; last lia. }
  { rewrite length_delete; last (rewrite list_lookup_fmap Helem; done).
    rewrite length_fmap.
    have Hwithin : (cursor_pos self < length (linked_list_elems (cursor_list self)))%nat.
    { eapply lookup_lt_Some; exact Helem. }
    lia.
  }
  { apply lookup_ge_None in Hlookup.
    apply lookup_ge_None_2. lia.
  }
  { apply lookup_ge_None in Hlookup.
    have Hdelete_locs : delete (cursor_pos self) (linked_list_locs (cursor_list self)) = linked_list_locs (cursor_list self).
    { rewrite delete_take_drop take_ge; last lia.
      rewrite drop_ge; last lia. apply app_nil_r.
    }
    have Hdelete_elems : delete (cursor_pos self) (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)) = PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self).
    { rewrite delete_take_drop take_ge; last (rewrite length_fmap; lia).
      rewrite drop_ge; last (rewrite length_fmap; lia). apply app_nil_r.
    }
    by rewrite Hdelete_locs Hdelete_elems.
  }
Qed.
End proof.
