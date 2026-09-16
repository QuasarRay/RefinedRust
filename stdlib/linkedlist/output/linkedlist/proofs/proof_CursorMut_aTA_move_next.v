From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_CursorMut_aTA_move_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma CursorMut_aTA_move_next_proof (π : thread_id) :
  CursorMut_aTA_move_next_lemma π.
Proof.
  CursorMut_aTA_move_next_prelude.

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
    rep <-! liRStep.
    2: rep liRStep.
    apply_update (updateable_end_lft "vuclft7").
    rep liRStep.
    (* The extracted node suffices to read Node.next. Before folding the
       cursor again, end vuclft7 and restore Hnode/Hfree into Hrest. *)
    liInst Hevar_self (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)).
    rep liRStep. liShow.
    rewrite (LL_extract _ _ _ _ _ (cursor_pos self)).
    2: { by rewrite list_lookup_fmap Helem. }
    rep liRStep.

    liInst Hevar_rf (mk_cursor_mut_x (mk_linked_list_x (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)) (linked_list_locs (cursor_list self)) (linked_list_alloc (cursor_list self))) (S self.(cursor_pos)) self.(cursor_ghost)).
    rep liRStep. }
  { rep liRStep.
    liInst Hevar_self (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)).
    rep liRStep.
    liInst Hevar_rf (mk_cursor_mut_x (mk_linked_list_x (PlaceIn ∘ RT_xrt T_rt <$> linked_list_elems (cursor_list self)) (linked_list_locs (cursor_list self)) (linked_list_alloc (cursor_list self))) 0%nat self.(cursor_ghost)).
    rep <-! liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - unfold cursor_next.
    assert (Hwithin_locs : (cursor_pos self < length (linked_list_locs (cursor_list self)))%nat).
    { eapply lookup_lt_Some; exact Hlookup. }
    rewrite Hlen in Hwithin_locs.
    destruct (decide (cursor_pos self = length (linked_list_elems (cursor_list self)))); [lia | reflexivity].
  - destruct (linked_list_locs (cursor_list self)); reflexivity.
  - assert (Hpast_end : (length (linked_list_locs (cursor_list self)) <= cursor_pos self)%nat).
    { apply lookup_ge_None. assumption. }
    rewrite Hlen in Hpast_end.
    unfold cursor_next.
    destruct (decide (cursor_pos self = length (linked_list_elems (cursor_list self)))); [reflexivity | lia].
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
