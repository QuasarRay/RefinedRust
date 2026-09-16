From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_push_back_mut.
From rrstd.linkedlist.linkedlist.proofs Require Import proof_LinkedList_TA_push_front_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma push_back_prev_lookup (locs : list loc) fresh :
  (None :: (Some <$> (locs ++ [fresh]))) !! length locs = Some (last locs).
Proof.
  destruct locs as [|l locs]; first done.
  change ((Some <$> ((l :: locs) ++ [fresh])) !! length locs =
    Some (last (l :: locs))).
  rewrite list_lookup_fmap lookup_app_l; last (simpl; lia).
  rewrite last_lookup /=.
  destruct ((l :: locs) !! length locs) eqn:Hlast; first done.
  apply lookup_ge_None in Hlast. simpl in Hlast. lia.
Qed.

Lemma LinkedList_TA_push_back_mut_proof (π : thread_id) :
  LinkedList_TA_push_back_mut_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft7" ["ulft_1"].
  pose_unconstrained_lft_hint "vuclft10" ["ulft_1"].
  LinkedList_TA_push_back_mut_prelude.

  1: rep <-! <3000 liRStep.
  liShow.
  rename r' into new_loc.
  (* Count exclusively owned, non-zero-sized Nodes and restore the guarded LL. *)
  add_updateable.
  iIntros "#CTX #HE HL".
  iRename select (LL _ _ _ _ _)%I into "Helems".
  iRename select (credit_store _ _)%I into "Hstore".
  iDestruct (credit_store_scrounge 1 with "Hstore") as "[Hcredit Hstore]"; first lia.
  open_cache.
  rename select (use_struct_layout_alg (Node_sls _) = Some Node_sl) into Hnode_layout.
  iPoseProof (push_front_guarded_LL_bound with "Helems") as "Hcount".
  { rewrite length_fmap. exact Hlen. }
  { intros node_loc next prev elem.
    apply (push_front_owned_heap _ _ _ _ Node_sl).
    - rewrite mut_fixpoint_project_ty_syn_type.
      by apply use_struct_layout_alg_Some_inv.
    - by apply (push_front_Node_size _ _ Hnode_layout). }
  iMod (lc_fupd_elim_later with "Hcredit Hcount") as "Hcount".
  iMod "Hcount" as "(%Hstrict & Helems)".
  rewrite length_fmap in Hstrict.
  iModIntro. iExists _. iFrame "HL".
  apply_update updateable_strip_guards.
  1: rep <-! <3000 liRStep.
  1: rep liRStep.
  liShow.
  iRename select (LL _ _ _ _ _)%I into "Helems".
  iEval (rewrite list_fmap_compose) in "Helems".
  iApply prove_with_subtype_default.
  iSplitL "Helems". { simplify_layout_goal. done. }

  1: rep <-! <3000 liRStep.
  pose_unconstrained_lft_hint "vuclft8" ["ulft_1"].
  1: rep <-! <3000 liRStep.
  liShow.
  apply_update updateable_strip_guards.
  iRename select (LL _ _ _ _ _)%I into "Helems".
  (* The old prefix retains the extended locations: its last next pointer
     now points to the appended Node, including when the prefix is empty. *)
  iEval (rewrite !fmap_app /= LL_snoc) in "Helems".
  iDestruct "Helems" as "(Helems & Htail)".
  iEval (rewrite /LL_item) in "Htail".
  iDestruct "Htail" as (tail_loc next prev)
    "(%Htail_loc & %Htail_next & %Htail_prev & Hnode & Hfree)".
  rewrite !length_fmap -Hlen in Htail_loc, Htail_next, Htail_prev.
  rewrite lookup_app_r in Htail_loc; last lia.
  rewrite Nat.sub_diag /= in Htail_loc.
  have Hnext : (locs ++ [new_loc]) !! S (length locs) = None.
  { rewrite lookup_app_r; last lia.
    replace (S (length locs) - length locs)%nat with 1%nat by lia. done. }
  rewrite Hnext in Htail_next.
  rewrite push_back_prev_lookup in Htail_prev.
  injection Htail_loc as Htail_loc. subst tail_loc.
  injection Htail_prev as Htail_prev. subst prev next.
  iAssert (guarded true (new_loc ◁ₗ[π, Owned] #((None, last locs, # $#@{T_rt} elt)) @
    ◁(Node_inv_t T_rt -[] -[T_ty])) ∗
    Allocator_A_spec_attrs.(Allocator_FreeablePerm) a new_loc
      (ly_size Node_sl))%I with "[Hnode Hfree]" as "Htail".
  { iFrame. }
  iRevert "Htail".
  1: rep <-! <3000 liRStep.
  liShow.
  rename r' into new_loc.

  (* Compose the element reborrows and transport the blocked tail refinement
     to the ghost carried by the returned reference. *)
  add_updateable.
  iIntros "#CTX2 #HE2 HL".
  iPoseProof (lctx_lft_incl_incl _ κ4 κ6 with "HL HE2") as "#H46".
  { solve_lft_incl. }
  iPoseProof (lctx_lft_incl_incl _ κ5 κ6 with "HL HE2") as "#H56".
  { solve_lft_incl. }
  iRename select (Inherit [κ4] (RelEq γ1 γ0))%I into "H10".
  iRename select (Inherit [κ5] (RelEq γ2 γ1))%I into "H21".
  iRename select (Inherit [κ6] (RelEq γ3 γ2))%I into "H32".
  iPoseProof (Inherit_mono [κ4] [κ6] with "[] H10") as "H10".
  { rewrite /lft_intersect_list /= !right_id. done. }
  iPoseProof (Inherit_mono [κ5] [κ6] with "[] H21") as "H21".
  { rewrite /lft_intersect_list /= !right_id. done. }
  iPoseProof (Inherit_RelEq_trans with "H32 H21") as "H31".
  iPoseProof (Inherit_RelEq_trans with "H31 H10") as "H30".
  iPoseProof (lctx_lft_incl_incl _ κ6 κ2 with "HL HE2") as "#H62".
  { solve_lft_incl. }
  iPoseProof (Inherit_mono [κ6] [κ2] with "[] H30") as "H30".
  { rewrite /lft_intersect_list /= !right_id. done. }
  iRename select (_ ◁ₗ[π, Owned] _ @ BlockedLtype _ κ2)%I into "Hnode".
  iRename select (Obs x' _)%I into "Hobs".
  iAssert (new_loc ◁ₗ[π, Owned] #((None, last locs, PlaceGhost γ3)) @
    BlockedLtype (Node_inv_t T_rt -[] -[T_ty]) κ2)%I
    with "[Hnode H30]" as "Hnode".
  { iApply (blocked_ltype_owned_transport with "[] H30 Hnode").
    iIntros (old node_v) "Hrel Hold Hv".
    iEval (rewrite /place_rfn_interp_owned) in "Hold".
    iDestruct (gvar_pobs_agree_2 with "Hobs Hold") as %Heq. subst old.
    iPoseProof (push_front_Node_reborrow with "Hrel Hv") as "Hv".
    iModIntro. iExists _. iSplit; first done.
    iFrame. }
  iModIntro. iExists _. iFrame "HL".
  rep liRStep.
  (* LL stratification introduced head/tail evars. The appended list is
     nonempty even when self is empty; instantiate them with its hd and tl. *)
  pose (updated := ((PlaceIn ∘ RT_xrt T_rt) <$> self) ++
    [PlaceGhost (rt := T_rt) γ3]).
  have Hupdated : hd (PlaceGhost γ3) updated :: tl updated = updated.
  { unfold updated. destruct self; done. }
  liInst Hevar_x (hd (PlaceGhost γ3)
    (((PlaceIn ∘ RT_xrt T_rt) <$> self) ++ [PlaceGhost γ3])).
  liInst Hevar_x0 (tl
    (((PlaceIn ∘ RT_xrt T_rt) <$> self) ++ [PlaceGhost γ3])).
  liInst Hevar_a a.
  1: rep <-! <3000 liRStep.
  liShow.
  iEval (rewrite Hupdated /updated LL_snoc /LL_item).
  rep liRStep.
  liShow.
  iApply prove_with_subtype_default.
  iRename select (LL _ _ _ _ _)%I into "Helems".
  iSplitL "Helems".
  { rewrite list_fmap_compose.
    rewrite (simplify_use_struct_layout_alg' _ _ Hnode_layout). done. }
  1: rep <-! <3000 liRStep.
  liShow.
  iEval (rewrite Hlen Nat.sub_diag /=).
  1: rep <-! <3000 liRStep.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: try rewrite mut_fixpoint_project_ty_syn_type//.
  all: try congruence.
  - destruct self; simpl; rewrite ?length_app ?length_fmap; simpl; lia.
  - symmetry. apply list_lookup_total_correct.
    rewrite -Hlen. apply push_back_prev_lookup.
Qed.
End proof.
