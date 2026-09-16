From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_split_off_after_node.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_split_off_after_node_proof (π : thread_id) :
  LinkedList_TA_split_off_after_node_lemma π.
Proof.
  (* These are too long. We need to create artificial lifetimes for them instead. *)
  (*pose_unconstrained_lft_hint "vuclft4" ["ulft_1"].*)
  (*pose_unconstrained_lft_hint "vuclft7" ["ulft_1"].*)
  LinkedList_TA_split_off_after_node_prelude.

  1: rep <-! <3000 liRStep.
  1: liShow.
  1: { (* outer [Some]: the split node is the last node of the prefix *)
    rename x' into split_node_loc.
    iRename select (LL _ _ _ _ _)%I into "Hall".
    rename select (last (take i locs) = Some _) into Hsplit.
    have Hilocs : (i ≤ length locs)%nat by lia.
    have Hie : length (take i elems) = i.
    { apply length_take_le. lia. }
    have Hilocs_len : length (take i locs) = i.
    { apply length_take_le. exact Hilocs. }
    apply last_Some in Hsplit as (prefix_locs & Hprefix_locs).
    have Hi_pos : (0 < i)%nat.
    { rewrite Hprefix_locs in Hilocs_len; rewrite length_app in Hilocs_len; simpl in Hilocs_len; lia. }
    have Hprefix_elems_ne : take i elems ≠ [].
    { intros Hnil. rewrite Hnil in Hie. simpl in Hie. lia. }
    destruct (exists_last Hprefix_elems_ne) as (prefix_elems & split_elem & Hprefix_elems).
    have Hprefix_len : length prefix_locs = length prefix_elems.
    { rewrite Hprefix_locs in Hilocs_len.
      rewrite Hprefix_elems in Hie.
      rewrite !length_app in Hilocs_len, Hie; simpl in Hilocs_len, Hie; lia. }

    iEval (rewrite (LL_split _ _ _ _ _ i)) in "Hall".
    iDestruct "Hall" as "[Hprefix Hsuffix]".
    iEval (rewrite !firstn_map) in "Hprefix".
    iEval (rewrite Hprefix_elems) in "Hprefix".
    iEval (rewrite (map_last (RT_xrt T_rt)) (map_last PlaceIn)) in "Hprefix".
    iEval (rewrite LL_snoc) in "Hprefix".

    iDestruct "Hprefix" as "[Hprefix Hsplit_node]".
    iDestruct "Hsplit_node" as (split_loc split_next split_prev)
      "(%Hsplit_loc & %Hsplit_next & %Hsplit_prev & Hsplit_node & Hsplit_free)".
    have Hlocs_decomp : locs = (prefix_locs ++ [split_node_loc]) ++ drop i locs.
    { rewrite <-Hprefix_locs. symmetry. apply take_drop. }
    have Hsplit_lookup : locs !! length prefix_locs = Some split_node_loc.
    { rewrite Hlocs_decomp lookup_app_l.
      - erewrite lookup_app_r; [rewrite Nat.sub_diag; reflexivity | lia].
      - rewrite length_app; simpl; lia. }
    rewrite !length_map in Hsplit_loc, Hsplit_next, Hsplit_prev.
    rewrite <-Hprefix_len in Hsplit_loc, Hsplit_next, Hsplit_prev.
    rewrite Hsplit_lookup in Hsplit_loc; simplify_eq.
    have Hsplit_nonnull : loc_a split_loc ≠ 0 := Forall_lookup_1 _ _ _ _ Hnonnull Hsplit_lookup.
    rewrite Hprefix_locs last_snoc.
    apply_update updateable_strip_guards.
    1: rep <-! <3000 liRStep.
    1: liShow.

    1: apply_update (updateable_start_lft "as_ref_lft1" ["ulft_1"]).
    1: rep <-! liRStep.
    pose_unconstrained_lft_hint "vuclft4" ["as_ref_lft1"].
    1: rep <-! <3000 liRStep.
    { (* there's a second_part_head *)
      rep liRStep.
      rename select (locs !! S (length prefix_locs) = Some _) into Hsuffix_head_lookup.
      rewrite Hsuffix_head_lookup. simpl.
      rep <-! liRStep.
      (* let's use the same lifetime and end it together later *)
      pose_unconstrained_lft_hint "vuclft7" ["as_ref_lft1"].
      rep <-! liRStep.
      liShow.

      have Hi_succ : i = S (length prefix_locs).
      { rewrite Hprefix_locs in Hilocs_len.
        rewrite length_app in Hilocs_len; simpl in Hilocs_len; lia. }
      opose proof
        (lookup_lt_is_Some_2 (drop i (<#> <$#@{T_rt}> elems)) 0%nat _)
        as (second_elem & Hsecond_drop).
      { shelve_sidecond. }
      iPoseProof (LL_segment_head with "Hsuffix") as "[Hsecond_head Hsuffix_rest]".
      { rewrite head_lookup. done. }
      iDestruct "Hsecond_head" as (head_loc head_next head_prev)
        "(%Hhead_loc & %Hhead_next & %Hhead_prev & Hhead_node & Hhead_free)".
      rewrite Hi_succ in Hhead_loc.
      rewrite Hsuffix_head_lookup in Hhead_loc; simplify_eq.
      have Hhead_nonnull : loc_a head_loc ≠ 0 :=
        Forall_lookup_1 _ _ _ _ Hnonnull Hsuffix_head_lookup.
      have Hhead_prev_expected :
          (None :: (Some <$> locs)) !! S (length prefix_locs) = Some (Some split_loc).
      { rewrite /= list_lookup_fmap Hsplit_lookup /=. done. }
      rewrite Hhead_prev_expected in Hhead_prev; simplify_eq.
      have Hsecond_lookup := Hsecond_drop.
      rewrite lookup_drop Nat.add_0_r in Hsecond_lookup.
      apply list_lookup_fmap_Some_1 in Hsecond_lookup as
        (second_rfn & Hsecond_place & Hsecond_lookup).
      apply list_lookup_fmap_Some_1 in Hsecond_lookup as
        (second_value & Hsecond_rfn & Hsecond_value_lookup).
      subst second_elem second_rfn.
      apply_update updateable_strip_guards.
      rep <-! <3000 liRStep.
      2: rep liRStep. (* overflow *)

      apply_update (updateable_end_lft "vuclft7").
      rep <-! <3000 liRStep.
      apply_update (updateable_end_lft "vuclft4").
      rep <-! <3000 liRStep.
      apply_update (updateable_end_lft "as_ref_lft1").

      liRStepUntil typed_context_fold. liShow.
      match goal with
      | H : locs !! (S (length prefix_locs)) = Some ?x |- _ =>
        rename x into l_prefix_succ;
        rename H into Hprefix_succ
      end.
      iApply (typed_context_fold_add_loc l_prefix_succ).
      let splitloc := lazymatch type of Hsplit_lookup with
        | _ = Some ?loc => loc
        end in iApply (typed_context_fold_add_loc splitloc).
      rep liRStep. liShow.

      (*liInst Hevar_locs (drop (S (length prefix_locs)) locs).*)
      (*liInst Hevar_x l_prefix_succ.*)
      (*rep <-! <3000 liRStep.*)

      have Htarget_head :
          ((PlaceIn ∘ RT_xrt T_rt) <$> drop (S (length prefix_locs)) elems) !! 0%nat =
            Some (# ($#@{T_rt} second_value)).
      {
        rewrite list_lookup_fmap lookup_drop Nat.add_0_r Hsecond_value_lookup /=.
        done.
      }
      liShow.

      rewrite (LL_rebase_head _ _ (prefix_locs ++ [r'0]) locs
        (drop (S (length prefix_locs)) locs)
        (drop (S (length prefix_locs)) (<#> <$#@{T_rt}> elems))
        ((PlaceIn ∘ RT_xrt T_rt) <$> drop (S (length prefix_locs)) elems)
        (# ($#@{T_rt} second_value))
        (S (S (length prefix_locs)))
      ).
      2-5: shelve_sidecond.

       do 70 liRStep.
       (*rep 10 liRStep.*)
       (* TODO: evar instantiation makes an instantiation it shouldn't, culprit: solve_protected_eq *)
       liInst Hevar_locs (take (S (length prefix_locs)) locs).
       rep <-! <3000 liRStep. liShow.
       rewrite Hprefix_elems.
       rewrite list_fmap_compose. rewrite !fmap_app.
       rewrite LL_snoc.
       have Hprefix_agree :
           take (S (length (<#> <$#@{T_rt}> prefix_elems))) locs =
             take (S (length (<#> <$#@{T_rt}> prefix_elems)))
               (take (S (length prefix_locs)) locs).
       { rewrite !length_map take_take. rewrite Nat.min_l; [done|lia]. }
       rewrite -(LL_prefix_stable _ _ _ _ _ _ Hprefix_agree).
       rep liRStep. liShow.
       have Hsplit_loc_total : locs !!! length prefix_elems = r'0.
       { apply list_lookup_total_correct. rewrite <-Hprefix_len. exact Hsplit_lookup. }
      rewrite Hsplit_loc_total.
      rep liRStep.
    }
    { (* there's no second_part_head *)
      have Hi_succ_none : i = S (length prefix_locs).
      {
        rewrite Hprefix_locs in Hilocs_len.
        rewrite length_app in Hilocs_len; simpl in Hilocs_len.
        lia.
      }
      match goal with
      | H : locs !! (S (length prefix_locs)) = None |- _ =>
        rename H into Hprefix_last
      end.
      have Hlocs_le_i : length locs ≤ i.
      {
        pose proof (lookup_ge_None_1 locs _ Hprefix_last) as Hlocs_le_next.
        lia.
      }
      have Hi_eq_len : i = length elems by lia.
      have Hdrop_elems : drop i elems = [] by apply drop_ge; lia.
      have Htake_locs : take i locs = locs by apply take_ge; lia.

      rep <-! <3000 liRStep.
      2: (* overflow *) rep liRStep.
      (* returning, have to assemble ownership of second part *)
      apply_update (updateable_end_lft "vuclft4").
      rep <-! liRStep.
      apply_update (updateable_end_lft "as_ref_lft1").
      rep <-! <3000 liRStep.

      (* TODO: maybe =return context fold should also stratify other things *)
      liRStepUntil typed_context_fold. liShow.
      iApply (typed_context_fold_add_loc r').

      (* establish invariant for suffix part *)
      rep liRStep; liShow.
      (*liInst Hevar_locs [].*)
      (*rep <-! <3000 liRStep.*)
      rewrite Hdrop_elems.
      rep <-! <3000 liRStep.
      liShow.

      (* establish invariant for prefix part *)
      iEval (rewrite -(take_drop (S (length prefix_locs)) elems)).
      rewrite Hdrop_elems app_nil_r.
      rewrite Hprefix_elems.
      rewrite !fmap_app.
      rewrite list_fmap_compose.
      iEval (rewrite LL_snoc).
      rep liRStep.
      assert (locs !!! length prefix_elems = r') as <-.
      { rewrite Hlocs_decomp. normalize_and_simpl_goal.
        replace (length prefix_elems - length prefix_locs)%nat with 0%nat by lia.
        done. }
      rep liRStep.
    }
  }
  { (* outer [None] *)
    rep <-! liRStep.
    match goal with
    | H : last (take i locs) = None |- _ => rename H into Hsplit_none
    end.
    have Hilocs_outer : (i ≤ length locs)%nat by lia.
    have Htake_locs_empty : take i locs = [].
    { apply last_None. exact Hsplit_none. }
    have Htake_locs_len : length (take i locs) = i.
    { rewrite length_take. lia. }
    rewrite Htake_locs_empty /= in Htake_locs_len. subst i.
    rep liRStep.  liShow.
    (* we're mutably borrowing self now and need to establish its LinkedList invariant *)
    liInst Hevar_self (<#> <$#@{T_rt}> elems).
    liInst Hevar_a alloc.
    rep <-! <3000 liRStep. liShow.
    rep liRStep. rewrite list_fmap_compose.
    rep <-! liRStep.
  }


  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
   - exists l_prefix_succ. split; last done.
     rewrite head_lookup lookup_drop Nat.add_0_r; exact Hprefix_succ.
  - have Hdrop_ne : drop (S (length prefix_locs)) locs ≠ [].
    { have Hdrop_head : drop (S (length prefix_locs)) locs !! 0%nat = Some l_prefix_succ.
      { rewrite lookup_drop Nat.add_0_r. exact Hprefix_succ. }
      intro Heq. rewrite Heq /= in Hdrop_head. discriminate. }
    have Hlast_eq :
        last locs = last (drop (S (length prefix_locs)) locs).
    { erewrite Hlocs_decomp at 1. rewrite last_app.
      destruct (last (drop (S (length prefix_locs)) locs)) eqn:Hlast;
        first done.
      exfalso. apply Hdrop_ne. apply last_None. exact Hlast. }
    rewrite Hlast_eq. sidecond_hammer.
  - apply Forall_drop; exact Hnonnull.
  - rewrite list_fmap_compose. done.
  - rewrite head_lookup. exact Htarget_head.
  - normalize_and_simpl_goal; rewrite lookup_drop; f_equal; lia.
  - rewrite !head_lookup lookup_take_lt; [done|lia].
  - exists r'0. split; last done. rewrite Hprefix_locs last_snoc. done.
  - apply Forall_take; exact Hnonnull.
  - symmetry. apply list_lookup_total_correct.
    rewrite <-Hprefix_len.
    destruct (length prefix_locs) as [|k] eqn:Hk.
    + simpl in Hsplit_prev |- *. exact Hsplit_prev.
    + simpl in Hsplit_prev |- *.
      rewrite list_lookup_fmap in Hsplit_prev.
      rewrite list_lookup_fmap lookup_take_lt; [|lia].
      exact Hsplit_prev.
   - rewrite head_lookup lookup_drop Nat.add_0_r. reflexivity.
   - rewrite drop_ge; [done | lia].
   - apply Forall_drop; exact Hnonnull.
  - exists r'. split; last done. rewrite -Htake_locs Hprefix_locs last_snoc. done.
  - rewrite <-Hprefix_len. symmetry. exact Hprefix_last.
  - symmetry. apply list_lookup_total_correct. rewrite <-Hprefix_len. exact Hsplit_prev.
  - rewrite list_fmap_compose. done.
  - exact unit.
  - exact unit.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
