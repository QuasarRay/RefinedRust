From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_CursorMut_aTA_move_prev.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma CursorMut_aTA_move_prev_proof (π : thread_id) :
  CursorMut_aTA_move_prev_lemma π.
Proof.
  CursorMut_aTA_move_prev_prelude.

  rep <-! liRStep; liShow.
  { rep liRStep.
    destruct (linked_list_locs (cursor_list self) !! cursor_pos self) as [ loc_cur | ] eqn:Hlookup; last done.
    rep <-! liRStep.
    pose_unconstrained_lft_hint "vuclft7" ["ulft_a"].
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
    apply_update (updateable_end_lft "vuclft7").
    rep <-! liRStep.
    { destruct (bool_decide (index >= 1)) eqn:Hchecked; last discriminate.
      rep liRStep.
      liInst Hevar_self (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)).
      rep liRStep.
      rewrite (LL_extract _ _ _ _ _ (cursor_pos self)).
      2: { by rewrite list_lookup_fmap Helem. }
      rep liRStep.
      liInst Hevar_rf (mk_cursor_mut_x (mk_linked_list_x (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)) (linked_list_locs (cursor_list self)) (linked_list_alloc (cursor_list self))) (Nat.pred self.(cursor_pos)) self.(cursor_ghost)).
      rep liRStep. }
    { destruct (bool_decide (index >= 1)) eqn:Hchecked; first discriminate.
      rep liRStep.
      liInst Hevar_self (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)).
      rep liRStep.
      rewrite (LL_extract _ _ _ _ _ (cursor_pos self)).
      2: { by rewrite list_lookup_fmap Helem. }
      rep liRStep.
      liInst Hevar_rf (mk_cursor_mut_x (mk_linked_list_x (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)) (linked_list_locs (cursor_list self)) (linked_list_alloc (cursor_list self))) (length (linked_list_elems (cursor_list self))) self.(cursor_ghost)).
       rep liRStep. }
  }
  { destruct (linked_list_locs (cursor_list self) !! cursor_pos self) as [ loc_cur | ] eqn:Hlookup; first done.
    rep liRStep.
    liInst Hevar_self (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)).
    rep liRStep.
    liInst Hevar_rf (mk_cursor_mut_x (mk_linked_list_x (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)) (linked_list_locs (cursor_list self)) (linked_list_alloc (cursor_list self))) (Nat.pred (length (linked_list_elems (cursor_list self)))) self.(cursor_ghost)).
    rep <-! liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { apply bool_decide_eq_true in Hchecked.
    have Hwithin : (cursor_pos self < length (linked_list_elems (cursor_list self)))%nat.
    { apply lookup_lt_Some in Hlookup. lia. }
    specialize (Hindex ltac:(lia)).
    destruct (cursor_pos self) as [ | pos] eqn:Hpos; first lia.
    simpl in Hprev |- *.
    rewrite list_lookup_fmap in Hprev.
    destruct (linked_list_locs (cursor_list self) !! pos); naive_solver. }
  { apply bool_decide_eq_true in Hchecked.
    have Hwithin : (cursor_pos self < length (linked_list_elems (cursor_list self)))%nat.
    { apply lookup_lt_Some in Hlookup. lia. }
    specialize (Hindex ltac:(lia)).
    unfold cursor_prev.
    rewrite decide_False; last lia.
    rewrite decide_False; last lia.
    reflexivity. }
  { apply bool_decide_eq_false in Hchecked.
    have Hwithin : (cursor_pos self < length (linked_list_elems (cursor_list self)))%nat.
    { apply lookup_lt_Some in Hlookup. lia. }
    specialize (Hindex ltac:(lia)).
    have Hpos : cursor_pos self = 0%nat by lia.
    rewrite Hpos in Hprev. simpl in Hprev. injection Hprev as <-.
    rewrite <- Hlen. symmetry. apply lookup_ge_None_2. lia. }
  { apply bool_decide_eq_false in Hchecked.
    have Hwithin : (cursor_pos self < length (linked_list_elems (cursor_list self)))%nat.
    { apply lookup_lt_Some in Hlookup. lia. }
    specialize (Hindex ltac:(lia)).
    have Hpos : cursor_pos self = 0%nat by lia.
    unfold cursor_prev.
    rewrite decide_False; last lia.
    rewrite decide_True; last done.
    reflexivity. }
  { by rewrite last_lookup Hlen. }
  { apply lookup_ge_None in Hlookup.
    have Hpos : cursor_pos self = length (linked_list_elems (cursor_list self)) by lia.
    unfold cursor_prev. rewrite decide_True; last done.
    reflexivity. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
