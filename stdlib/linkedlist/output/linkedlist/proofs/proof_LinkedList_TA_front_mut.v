From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_front_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_front_mut_proof (π : thread_id) :
  LinkedList_TA_front_mut_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft4" ["ulft_a"].
  LinkedList_TA_front_mut_prelude.

  rep <-! liRStep; liShow.

  { iRename select (LL _ _ _ _ _)%I into "Hall".

    rename select (head locs = Some _) into Hhead.
    apply head_Some in Hhead as (locs' & ->).
    destruct self as [|head_el self]; simpl in Hlen; [lia |].
    iEval (rewrite LL_cons) in "Hall".
    iDestruct "Hall" as  "[Hhead Htail]".
    iDestruct "Hhead" as (head_loc next prev)
      "(%Hloc & %Hnext & %Hprev & Hnode & Hfreeable)".
    simpl in Hloc, Hprev; simplify_eq.
    apply_update updateable_strip_guards.
    rep <-! <3000 liRStep.

    rep liRStep; liShow.
    liInst Hevar_self
      (PlaceGhost γ0 :: ((PlaceIn ∘ RT_xrt T_rt) <$> self)).
    liInst Hevar_a a.
    liInst Hevar_locs (r' :: locs').
    liInst Hevar_x r'.
    rep liRStep.
    iEval (rewrite LL_cons).
    rep <-! liRStep; liShow. }
  { rename select (head locs = None) into Hhead.
    apply head_None in Hhead; subst locs.
    destruct self; simpl in Hlen; [|lia].
    rep <-! <3000 liRStep.
    rep liRStep.
    liInst Hevar_self [].
    liInst Hevar_a a.
    liInst Hevar_locs [].
    rep <-! <3000 liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
Qed.
End proof.
