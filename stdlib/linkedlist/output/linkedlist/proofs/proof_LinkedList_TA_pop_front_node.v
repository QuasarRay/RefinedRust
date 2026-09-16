From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_pop_front_node.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_pop_front_node_proof (π : thread_id) :
  LinkedList_TA_pop_front_node_lemma π.
Proof.
  LinkedList_TA_pop_front_node_prelude.

  rep <-! liRStep; liShow.
  {
    iRename select (LL _ _ _ _ _)%I into "Hall".
    destruct self as [ | head_el self].
    { destruct locs; simpl in *; [done | lia]. }
    rename select (head locs = Some _) into Hhead.
    apply head_Some in Hhead as (locs' & ->).
    iEval (rewrite /=LL_cons/=) in "Hall".
    iDestruct "Hall" as "[Hhead Htail]".
    iDestruct "Hhead" as (head_loc next prev) "(%Hloc & %Hnext & %Hprev & Hnode & Hfree)".
    simpl in Hloc, Hnext, Hprev; simplify_eq.
    destruct locs' as [ | new_loc locs_tail]; destruct self as [ | new_el self_tail]; simpl in *; try lia.
    { liRStepUntil typed_call.
      apply_update updateable_strip_guards.
      rep <-! <3000 liRStep.
      { rep liRStep.
        liInst Hevar_self [].
        liInst Hevar_locs [].
        liInst Hevar_a a.
        liRStepUntil owned_subtype.
        liRStepUntil owned_subtype.
        liInst Hevar_x (Some (None, None, head_el, a)).
        liRStep.
        liRStepUntil owned_subtype.
        iApply owned_subtype_strong_subtype.
        rep liRStep. }
      { liRStepUntil typed_call.
        apply_update updateable_strip_guards.
        rep <-! <3000 liRStep. } }
    { (* extract ownership *)
      iEval (rewrite LL_segment_cons) in "Htail".
      iDestruct "Htail" as "(Hnew_head & Htail)".
      iDestruct "Hnew_head" as (new_head_loc next' prev') "(%Hloc' & %Hnext' & %Hprev' & Hnode_new_head & Hfree_new_head)".
      (*liRStepUntil typed_call.*)
      apply_update updateable_strip_guards.
      rep <-! <3000 liRStep.
      simpl in Hloc'. injection Hloc' as ->.
      rep <-! <3000 liRStep.
      { rep liRStep. liShow.
        liInst Hevar_self ((# $#new_el) :: (PlaceIn ∘ RT_xrt T_rt <$> self_tail)).
        liInst Hevar_locs (r' :: locs_tail).
        liInst Hevar_a a.
        liInst Hevar_x r'.
        liRStepUntil owned_subtype.
        simpl in Hprev'. injection Hprev' as <-.
        iEval (rewrite LL_segment_drop_head_suffix) in "Htail".
        iEval (rewrite LL_cons).
        liRStepUntil owned_subtype.
        liInst Hevar_x (Some (Some r', None, head_el, a)).
        iApply owned_subtype_strong_subtype.
        rep liRStep. }
      { rep <-! <3000 liRStep. } }
  }
  { destruct locs as [|l locs]; simpl in *; [|done].
    destruct self as [|el self]; simpl in Hlen; [|lia].
    rep liRStep.
    liInst Hevar_self [].
    liInst Hevar_locs [].
    liInst Hevar_a a.
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve.  all: sidecond_hammer.
  - apply Forall_cons in Hnonnull as [? Hnonnull].
    apply Forall_cons in Hnonnull as [? Hnonnull].
    done.
Qed.
End proof.
