From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_back_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_back_mut_proof (π : thread_id) :
  LinkedList_TA_back_mut_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft4" ["ulft_a"].
  LinkedList_TA_back_mut_prelude.

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
      "(%Hloc & %Hnext & %Hprev & Hnode & Hfreeable)".
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
    destruct self' as [|head_el self']; simpl in Hlen', Hlen, Hnonnull, Hbound.

    { (* list is empty *)
    (* The tail is also the head, so there is no guarded prefix to preserve. *)
      1: apply_update updateable_strip_guards.
      1: rep <-! <3000 liRStep.
      rep liRStep. liShow.
      liInst Hevar_x (👻 γ0).
      rep liRStep.
      rewrite (LL_snoc _ _ []).
      rep liRStep. }

  (* Keep the unchanged prefix guarded; only the modified tail needs to be
     exposed at the update point. *)
    destruct locs' as [|l locs']; [simpl in Hlen'; lia |].
    assert (length locs' = length self') as Hlenprefix by
      (simpl in Hlen'; lia).
    apply_update updateable_strip_guards.
    rep <-! <3000 liRStep.
    rep liRStep; liShow.
    liInst Hevar_self
      (PlaceIn (RT_xrt T_rt head_el) ::
       ((PlaceIn ∘ RT_xrt T_rt) <$> self') ++ [PlaceGhost γ0]).
    liInst Hevar_a a.
    liInst Hevar_locs ((l :: locs') ++ [r']).
    liInst Hevar_x l.
    rep liRStep. liShow.
    iEval (rewrite (LL_snoc _ _ (_ :: _))).
    rep liRStep. liShow.
    replace (length self' - length locs')%nat with 0%nat by lia.
    rep <-! < 3000 liRStep.
    liInst Hevar_x γ0.
    liInst Hevar_x1 tail_el.
    liInst Hevar_x2 γ0.
    liInst Hevar_x0 tail_el.
    rep <-! <3000 liRStep.
  } 

  { rename select (last locs = None) into Htail.
    apply last_None in Htail; subst locs.
    destruct self; simpl in Hlen; [|lia].
    rep <-! <3000 liRStep.
    rep liRStep.
    liInst Hevar_self [].
    liInst Hevar_a a.
    liInst Hevar_locs [].
    rep <-! <3000 liRStep. }

  Unshelve. all: try exact self0.
  all: sidecond_solver.
  all: sidecond_hammer.
  - exists r'. split; [apply last_snoc | done].
  - apply length_zero_iff_nil in Hlen'. subst locs'. done.
  - apply length_zero_iff_nil in Hlen'. subst locs'.
    simpl in Hprev. simplify_eq. done.
   - exists r'. split; [rewrite last_cons last_snoc; done | done].
  - rewrite length_app in Hbound. simpl in Hbound. lia.
  - rewrite <- Hlenprefix. exact Hnext'.
  - rewrite <- Hlenprefix.
    f_equal. symmetry. apply list_lookup_total_correct.
    move: Hprev. done.
  - rewrite last_cons. rewrite last_snoc//.
   - exists head_el, self'.
     rewrite removelast_last.
     destruct self' as [|first rest]; simpl; repeat split; done.

Qed.
End proof.
