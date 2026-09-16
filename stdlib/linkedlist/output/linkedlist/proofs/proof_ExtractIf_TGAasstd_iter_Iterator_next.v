From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_ExtractIf_TGAasstd_iter_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Global Instance li_sealed_pers (P : iProp Σ) `{!Persistent P} :
  Persistent (li_sealed P).
Proof.
  unfold li_sealed. apply _.
Qed.

Lemma ExtractIf_TGAasstd_iter_Iterator_next_proof (π : thread_id) :
  ExtractIf_TGAasstd_iter_Iterator_next_lemma π.
Proof.
  ExtractIf_TGAasstd_iter_Iterator_next_prelude.
  rewrite /traits_iterator_Iterator_Inv /ExtractIf_TGAasstd_iter_Iterator_spec_attrs /=.

  1: rep <-! <3000 liRStep.
  { rep liRStep.
    destruct (locs !! pos) as [loc_cur |] eqn:Hlookup.
    2: { done. }
    rep <-! <3000 liRStep.
    rep liRStep.
    rewrite Hlookup /=.
    rep <-! <3000 liRStep.
    pose_unconstrained_lft_hint "vuclft7" ["ulft_1"].
    iRename select (LL _ _ _ _ _)%I into "Hall".
    odestruct (lookup_lt_is_Some_2 self pos _) as (elem & Helem).
    { rewrite <- Hlen.
      eapply lookup_lt_Some. exact Hlookup. }
    have Hmapped : ((PlaceIn ∘ RT_xrt T_rt <$> self) !! pos) =
      Some (PlaceIn (RT_xrt T_rt elem)).
    { by rewrite list_lookup_fmap Helem. }
    iPoseProof (LL_extract _ _ _ _ _ pos _ with "Hall") as "[Hitem Hrest]".
    { exact Hmapped. }
    iDestruct "Hitem" as (node_loc next prev) "(%Hloc & %Hnext & %Hprev & Hnode & Hfree)".
    rewrite Hlookup in Hloc. injection Hloc as <-.
    apply_update updateable_strip_guards.
    rep <-! <3000 liRStep.
    { apply_update (updateable_end_lft "vuclft7").
      rep liRStep.
      pose_unconstrained_lft_hint "vuclft10" ["ulft_1"].
      repeat (lazymatch goal with
        | |- environments.envs_entails _ (prove_with_subtype _ _ true _ _ _ _) => fail
        | _ => liRStep
        end).
      liShow.
      iApply (prove_with_subtype_stratify r'0).
      rep <-! <3000 liRStep.
      rep liRStep.
      liInst Hevar_x0 elem.
      liInst Hevar_x1 (locs !! S pos).
      liInst Hevar_x2 prev.
      liShow.
      iApply prove_with_subtype_default.
      iSplitR.
      { iIntros "Hnode _". iExact "Hnode". }
      rep <-! <3000 liRStep.
      liShow.
      iRename select (∀ _ _, ∃ _, _)%I into "Hcallable".
      iDestruct ("Hcallable" $! f
        (((elem, γ2) -:: -[]) : plist (RT_xt ∘ place_rfnRT)
          [prodRT (place_rfnRT T_rt) gnameRT])) as (q) "Hpre".
      liRStepUntilTac (fun _ => lazymatch goal with
        | _ : FnOnce_UnwindCondition _ _ _ _ |- _ => idtac
        | |- environments.envs_entails _ ?P =>
            lazymatch P with context [typed_if] => idtac end
        end).
      { (* The predicate cannot unwind, so its unwind continuation is unreachable. *)
        rename select (closure_may_unwind _ → False) into Hno_unwind.
        rename select (FnOnce_UnwindCondition _ _ _ _) into Hunwind.
        exfalso. apply Hno_unwind.
        unfold closure_may_unwind. eauto.
      }
      liShow.
      iRename select (li_sealed _)%I into "Hobserve".
      iDestruct "Hobserve" as "#Hobserve".
      iPoseProof (li_sealed_use_pers with "Hobserve") as "#Hobserve_rule".
      iRename select (FnOnce_PostMut _ π q f _ _ _)%I into "Hpost".
      iDestruct ("Hobserve_rule" with "Hpost") as (updated_elem) "#Helement".
      iClear "Hobserve_rule".
      liRStep.
      liRStepUntil typed_stmt.
      { liRStepUntil typed_call.
        (* End the node borrow before reconstructing unlink_node's ownership. *)
        apply_update (updateable_end_lft "vuclft10").
        rep liRStep.
        liInst Hevar_x3 (PlaceIn ∘ RT_xrt T_rt <$> (<[pos := updated_elem]> self)).
        rep liRStep.
        liInst Hevar_x4 pos.
        rep liRStep.
        liShow.
        iApply (prove_with_subtype_stratify r'0).
        rep liRStep. liShow.
        iAcquireCredits as "Hguard".
        iApply prove_with_subtype_default.
        iSplitL "Hrest Hfree Hguard".
        { iIntros "Hnode _".
          have Hlayout : use_struct_layout_alg' (Node_sls (st_of T_ty MetaNone)) = Node_sl.
          { apply simplify_use_struct_layout_alg'. solve_goal. }
          iEval (rewrite Hlayout) in "Hrest Hfree".
          (* The predicate may have changed the element; all other nodes retain
             their refinements and allocation permissions. *)
          rewrite list_fmap_insert /LL big_sepL_insert.
          2: { eapply lookup_lt_Some. exact Hmapped. }
          iFrame "Hrest".
          iExists r'0, (locs !! S pos), prev.
          iSplit. { done. }
          iSplit. { done. }
          iSplit. { done. }
          iFrame "Hfree".
          iApply guarded_intro. iFrame.
        }
        1: rep <-! <300 liRStep.
        1: rep <-! <300 liRStep.
        1: rep <-! <300 liRStep.
        1: rep <-! <300 liRStep.
        rep liRStep. liShow.
        iRename select (LL _ _ _ _ _)%I into "Hall".
        have Hlayout : use_struct_layout_alg' (Node_sls (st_of T_ty MetaNone)) = Node_sl.
        { apply simplify_use_struct_layout_alg'. solve_goal. }
        iEval (rewrite -Hlayout) in "Hall".
        iApply prove_with_subtype_default.
        (*iSplitL "Hall".*)
        (*{ iExact "Hall". }*)
        rep <-! <3000 liRStep.
        rep liRStep.
        liInst Hevar_self (delete pos (<[pos := updated_elem]> self)).
        liInst Hevar_locs (delete pos locs).
        liInst Hevar_a a.
        liInst Hevar_γlist γlist.
        liInst Hevar_f x'1.
        liInst Hevar_pos pos.
        liInst Hevar_visited (S visited).
        liInst Hevar_initial_len initial_len.
        liRStepUntil prove_with_subtype.
        rep <- 4 liRStep.
        { iApply "Hcallable". }
        rep <-! <3000 liRStep.
      }
      { (* false branch: we re-establish the loop invariant *)
        liRStepUntil typed_annot_stmt.
        apply_update (updateable_end_lft "vuclft10").
        liRStepUntil typed_context_fold.
        rep liRStep.
        liInst Hevar_self (PlaceIn ∘ RT_xrt T_rt <$> (<[pos := updated_elem]> self)).
        liInst Hevar_a a.
        rep liRStep.
        liShow.
        iApply (prove_with_subtype_stratify r').
        rep liRStep. liShow.
        iAcquireCredits as "Hguard".
        iApply prove_with_subtype_default.
        iSplitL "Hrest Hfree Hguard".
        { iIntros "Hnode _".
          rewrite list_fmap_insert /LL big_sepL_insert.
          2: { eapply lookup_lt_Some. exact Hmapped. }
          iFrame "Hrest".
          iExists r', (locs !! S pos), prev.
          iSplit. { done. }
          iSplit. { done. }
          iSplit. { done. }
          iFrame "Hfree".
          iApply guarded_intro. iFrame.
        }
        rep <-! <3000 liRStep.
        rep liRStep.
        liInst Hevar_f x'1.
        liInst Hevar_pos (S pos).
        liInst Hevar_visited (S visited).
        liInst Hevar_initial_len initial_len.
        rep <-! <3000 liRStep.
      }
    }
    { (* A remaining node implies that the visit counter can still be incremented. *)
      have Hvisited_strict : (visited < initial_len)%nat by lia.
      exfalso.
      rename select (Z.succ visited ∉ usize) into Hoverflow.
      apply Hoverflow. unfold int_elem_of_it.
      split; [solve_goal | lia].
    }
  }
  { rep <- 4liRStep.
    { done. }
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rewrite list_fmap_delete//.
  - rewrite list_lookup_delete_ge//.
  - rewrite length_delete.
    { rewrite length_insert. lia. }
    apply lookup_lt_is_Some_2.
    rewrite length_insert. lia.
  - rewrite length_delete.
    2: { apply lookup_lt_is_Some_2. rewrite length_insert. lia. }
    rewrite length_insert. lia.
  - apply unit.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
