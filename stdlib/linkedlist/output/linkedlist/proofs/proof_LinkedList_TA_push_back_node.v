From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_push_back_node.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_push_back_node_proof (π : thread_id) :
  LinkedList_TA_push_back_node_lemma π.
Proof.
  LinkedList_TA_push_back_node_prelude.

  rep <-! liRStep; liShow.
  { iRename select (LL _ _ _ _ _)%I into "Hall".
    rename select (last locs = Some _) into Htail.
    apply last_Some in Htail as (locs' & ->).
    assert (elems ≠ []) as Helems by (intros ->; rewrite length_app in Hlen; simpl in Hlen; lia).
    destruct (exists_last Helems) as (elems' & tail_el & ->).
    simpl in Hlen.
    iEval (rewrite !fmap_app) in "Hall".
    iEval (rewrite LL_snoc) in "Hall".
    iDestruct "Hall" as "[Hprefix Htail]".
    iDestruct "Htail" as (tail_loc next prev) "(%Hloc & %Hnext & %Hprev & Hnode & Hfree)".
    assert (length locs' = length elems') as Hlen' by
       (rewrite !length_app in Hlen; simpl in Hlen; lia).
    have Hmaplen : length (<#> <$#> elems') = length elems' by
       (change (length (List.map PlaceIn (List.map (@RT_xrt T_rt) elems')) = length elems');
        rewrite !length_map; done).
    rewrite Hmaplen in Hloc, Hnext, Hprev.
    rewrite <- Hlen' in Hloc, Hnext, Hprev.
    replace (length locs' + 0)%nat with (length locs') in Hloc, Hnext, Hprev by lia.
    have Hloc' : (locs' ++ [x']) !! length locs' = Some x' by
       (erewrite lookup_app_r; [rewrite Nat.sub_diag; reflexivity | lia]).
    have Hnext' : (locs' ++ [x']) !! S (length locs') = None by
       (erewrite lookup_app_r;
        [replace (S (length locs') - length locs')%nat with 1%nat by lia; reflexivity | lia]).
    rewrite Hloc' in Hloc; rewrite Hnext' in Hnext; simplify_eq.
    rewrite last_snoc.
    have Hpred_app :
       None :: (Some <$> locs') ++ [Some tail_loc; Some node] =
       (None :: (Some <$> locs') ++ [Some tail_loc]) ++ [Some node] by
       exact (app_assoc (None :: (Some <$> locs')) [Some tail_loc] [Some node]).
    have Hprev_new :
       (None :: (Some <$> locs') ++ [Some tail_loc; Some node]) !! length locs' = Some prev.
    { shelve_sidecond. }
    have Hhead :
       head (locs' ++ [tail_loc]) = head (locs' ++ [tail_loc; node]) by
       symmetry; apply head_snoc_snoc.

    apply_update updateable_strip_guards.
    rep <-! <3000 liRStep.
    { rename r' into l1.
      rename r'1 into l2.
      liRStepUntil weak_subtype.
      rewrite Hhead.
      rep  liRStep. liShow.
      rewrite !fmap_app.
      iEval (rewrite !LL_snoc).
      rep liRStep. liShow.
      rewrite (LL_prefix_stable _ _ _ _ (locs' ++ [l1])); last shelve_sidecond.
      rep liRStep. liShow.
      assert (length elems' = length locs') as Hlen_eq by shelve_sidecond.
      rewrite Hlen_eq Nat.sub_diag.
      rep liRStep. liShow.
      rewrite Hlen_eq.
      replace (S (length locs') - length locs')%nat with 1%nat by lia.
      rep liRStep.
    }
    rep <-! <3000 liRStep.
  }
  { rep <-! liRStep.
    1: rename select (last locs = None) into Hempty_tail.
    { rep liRStep.
      rewrite !fmap_app.
      rewrite LL_snoc.
      rep liRStep. liShow.
      have Helems_nil : elems = [].
      { apply length_zero_iff_nil. rewrite <-Hlen.
         apply last_None in Hempty_tail. rewrite Hempty_tail. done. }
      rewrite Helems_nil !fmap_nil LL_nil.
      rep liRStep.
      liShow.
        have Hlocs_nil : locs = [] by (apply last_None; exact Hempty_tail).
       rewrite Hlocs_nil.
      rep liRStep. }
    { rep liRStep. }
  }
  
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - replace (None :: (Some <$> locs') ++ [Some tail_loc; Some node]) with
         ((None :: (Some <$> locs' ++ [tail_loc])) ++ [Some node]).
     + rewrite lookup_app_l; [exact Hprev | apply lookup_lt_Some in Hprev; lia].
     + rewrite !fmap_app /= -app_assoc. reflexivity.
  - exists r'; split; [rewrite last_app; done | done].
  - rewrite <- Hlen'.
     replace (locs' ++ [l1; r']) with ((locs' ++ [l1]) ++ [r']) by
       (rewrite -app_assoc; done).
     rewrite take_app_le; [done | rewrite length_app /=; lia].
  - exists r'. split; last done.
     rewrite lookup_app_r; [replace (S (length locs') - length locs')%nat with 1%nat by lia; done | lia].
  - rewrite !fmap_app /= in Hprev_new |- *.
     rewrite /lookup in Hprev_new.
     f_equal. symmetry. apply list_lookup_total_correct. exact Hprev_new.
  - rewrite lookup_app_r; [replace (S (S (length locs')) - length locs')%nat with 2%nat by lia; done | lia].
  - rewrite !Forall_app in Hnonnull |- *.
     destruct Hnonnull as [Hnonloc Hnontail].
      split; [exact Hnonloc | constructor; [inversion Hnontail; assumption | constructor; [exact Hnode_nonnull | constructor]]].
  - rewrite length_app /= in Hbound. lia.
  - exists r'. split; [rewrite head_snoc | done].
      rename select (last locs = None) into Hempty_tail.
      apply last_None in Hempty_tail. subst locs. done.
  - exists r'. split; [rewrite last_snoc; done | done].

Qed.
End proof.
