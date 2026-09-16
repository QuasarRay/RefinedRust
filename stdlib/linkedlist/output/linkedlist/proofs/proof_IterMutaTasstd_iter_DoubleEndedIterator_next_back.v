From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_IterMutaTasstd_iter_DoubleEndedIterator_next_back.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma IterMutaTasstd_iter_DoubleEndedIterator_next_back_proof (π : thread_id) :
  IterMutaTasstd_iter_DoubleEndedIterator_next_back_lemma π.
Proof.
  IterMutaTasstd_iter_DoubleEndedIterator_next_back_prelude.

  1: rep <-! <3000 liRStep; liShow.
  (*{ rename select ((back - front)%nat = 0%nat) into Hempty.*)
    (*have Hsame : front = back by lia.*)
    (*rep liRStep; liShow.*)
    (*rewrite decide_False; last lia.*)
    (*rep liRStep. }*)
  { rename select ((back - front)%nat ≠ 0%nat) into Hnonzero.
    rename select (last (take back locs) = Some _) into Htail.
    have Hnonempty : (front < back)%nat by lia.
    have Hlookup : locs !! Nat.pred back = Some l.
    { rewrite last_lookup length_take Nat.min_l in Htail; last lia.
      rewrite lookup_take decide_True in Htail; [exact Htail | lia]. }
    odestruct (lookup_lt_is_Some_2 elems (Nat.pred back) _) as (elem & Helem).
    { lia. }
    have Howned_lookup : (<#> <$#@{T_rt}> elems) !! Nat.pred back = Some (PlaceIn ($#@{T_rt} elem)).
    { by rewrite !list_lookup_fmap Helem. }
    iRename select (LL _ _ _ _ _)%I into "Hall".
    iEval (rewrite (LL_extract _ _ _ _ _ _ _ Howned_lookup)) in "Hall".
    iDestruct "Hall" as "[Hitem Hrest]".
    iDestruct "Hitem" as (node_loc next prev) "(%Hloc & %Hnext & %Hprev & Hnode & _)".
    rewrite Hlookup in Hloc. injection Hloc as <-.
    have Hprev_tail : prev = last (take (Nat.pred back) locs).
    { destruct (Nat.pred back) as [|j] eqn:Hpred.
      { simpl in Hprev |- *. by injection Hprev as <-. }
      { rewrite last_lookup length_take Nat.min_l; last lia.
        rewrite lookup_take decide_True; last lia.
        simpl in Hprev |- *. rewrite list_lookup_fmap in Hprev.
        destruct (locs !! j); simpl in Hprev; congruence. } }
    subst prev.
    pose_unconstrained_lft_hint "vuclft5" ["_flft"].
    apply_update updateable_strip_guards.
    liRStepUntil (typed_val_expr _ _ _ (Ref _ _ _ _)).
    change (Ref _ _ _ ?e) with (Raw PRef Mut e).
    liRStep.
    liRStepUntil (typed_val_expr _ _ _ (Ref _ _ _ _)).
    change (Ref _ _ _ ?e) with (Raw PRef Mut e).
    liRStepUntil (typed_val_expr _ _ _ (EnumInit _ _ _ _)).
    change (EnumInit ?els ?v _) with (EnumInit els v (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTAliasRef] []))).


    liRStepUntil typed_context_fold.
    iApply (typed_context_fold_add_loc l).
    rep liRStep.
    iEval (rewrite (LL_extract _ _ _ _ _ _ _ Howned_lookup)).
    rep <-! <3000 liRStep. }
  { rename select ((back - front)%nat ≠ 0%nat) into Hnonzero.
    rename select (last (take back locs) = None) into Htail.
    apply last_None in Htail.
    have Hzero : length (take back locs) = 0%nat by rewrite Htail.
    rewrite length_take Nat.min_l in Hzero; [exfalso; lia | lia]. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: try apply inhabitant.
  - rename select (use_struct_layout_alg (Node_sls _) = Some _) into Hnode_layout.
    rewrite Hlookup /=.
    eexists. split.
    { reflexivity. }
    { by rewrite /GetMemberLocSt /use_struct_layout_alg' Hnode_layout /=. }
  - apply Mut.
  - apply Mut.
  - apply Ordering_els.
  - apply (RSTEnumDef ["Option_enum"] (RSTScopeInst [] [RSTAliasRef] [])).
  - apply unit.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
