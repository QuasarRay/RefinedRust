From refinedrust Require Import typing.
From rrstd.iterator.theories Require Export iterator.

(** External attributes, indexed by the inherited Iterator attributes so both
    directions use the same parameters and invariant. *)
Definition traits_double_ended_DoubleEndedIterator_NextBack_sig `{RRGS : !refinedrustGS Σ}
    (Self_rt Item_rt : RT) (It_attrs : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) :=
  thread_id → It_attrs.(traits_iterator_Iterator_Params) → RT_xt Self_rt →
    option (RT_xt Item_rt) → RT_xt Self_rt → iProp Σ.
Record traits_double_ended_DoubleEndedIterator_spec_attrs `{RRGS : !refinedrustGS Σ}
    `{Self_rt : !RT} `{Item_rt : !RT}
    `{It_attrs : !(traits_iterator_Iterator_spec_attrs Self_rt Item_rt)} : Type :=
  mk_traits_double_ended_DoubleEndedIterator_spec_attrs {
    traits_double_ended_DoubleEndedIterator_NextBack :
      traits_double_ended_DoubleEndedIterator_NextBack_sig Self_rt Item_rt It_attrs;
  }.
#[global] Arguments traits_double_ended_DoubleEndedIterator_spec_attrs : clear implicits.
#[global] Arguments traits_double_ended_DoubleEndedIterator_spec_attrs {_ _}.
#[global] Arguments mk_traits_double_ended_DoubleEndedIterator_spec_attrs {_ _ _ _ _}.

(** Successful backward steps, in call order (not forward sequence order).
    A terminal None step is separate; this does not assume a fused iterator.
    Keep the whole attribute record to support LearnFromHyp, as in the forward theory. *)
Fixpoint IteratorNextBackFusedTrans `{RRGS : !refinedrustGS Σ} {Self_rt Item_rt : RT}
    {It_attrs : traits_iterator_Iterator_spec_attrs Self_rt Item_rt}
    (attrs : traits_double_ended_DoubleEndedIterator_spec_attrs Self_rt Item_rt It_attrs)
    (π : thread_id) p
    (s1 : RT_xt Self_rt) (els : list (RT_xt Item_rt)) (s2 : RT_xt Self_rt) : iProp Σ :=
  match els with
  | [] => ⌜s1 = s2⌝
  | e :: els =>
      ∃ s1', attrs.(traits_double_ended_DoubleEndedIterator_NextBack) π p s1 (Some e) s1' ∗
        IteratorNextBackFusedTrans attrs π p s1' els s2
  end.

Section trans.
  Context `{RRGS : !refinedrustGS Σ} {Self_rt Item_rt : RT}.
  Context {It_attrs : traits_iterator_Iterator_spec_attrs Self_rt Item_rt}.
  Context (A : traits_double_ended_DoubleEndedIterator_spec_attrs Self_rt Item_rt It_attrs).

  Lemma iterator_next_back_fused_trans_nil π p s1 s2 :
    IteratorNextBackFusedTrans A π p s1 [] s2 ⊣⊢ ⌜s1 = s2⌝.
  Proof. done. Qed.

  Lemma iterator_next_back_fused_trans_cons π p s1 hist s2 s2' x :
    A.(traits_double_ended_DoubleEndedIterator_NextBack) π p s1 (Some x) s2 -∗
    IteratorNextBackFusedTrans A π p s2 hist s2' -∗
    IteratorNextBackFusedTrans A π p s1 (x :: hist) s2'.
  Proof. simpl. iIntros "? $". eauto. Qed.

  Lemma iterator_next_back_fused_trans_snoc π p s1 hist s2 x :
    IteratorNextBackFusedTrans A π p s1 (hist ++ [x]) s2 ⊣⊢
      ∃ s2', IteratorNextBackFusedTrans A π p s1 hist s2' ∗
        A.(traits_double_ended_DoubleEndedIterator_NextBack) π p s2' (Some x) s2.
  Proof.
    iInduction hist as [ | y hist] "IH" forall (s1 s2); simpl.
    - iSplit.
      + iIntros "(%s1' & ? & <-)". by iFrame.
      + iIntros "(%s2' & -> & ?)". by iFrame.
    - iSplit.
      + iIntros "(%s1' & Ha & Hb)".
        iPoseProof ("IH" with "Hb") as "(%s2' & Hb & Hc)".
        iFrame.
      + iIntros "(%s2' & (%s1' & ? & ?) & ?)".
        iFrame. iApply "IH". iFrame.
  Qed.

  Lemma iterator_next_back_fused_trans_app π p s1 hist1 hist2 s2 :
    IteratorNextBackFusedTrans A π p s1 (hist1 ++ hist2) s2 ⊣⊢
      ∃ s2', IteratorNextBackFusedTrans A π p s1 hist1 s2' ∗
        IteratorNextBackFusedTrans A π p s2' hist2 s2.
  Proof.
    iInduction hist1 as [ | y hist] "IH" forall (s1 s2); simpl.
    - iSplit.
      + iIntros "$". done.
      + iIntros "(%s2' & -> & $)".
    - iSplit.
      + iIntros "(%s1' & Ha & Hb)".
        iPoseProof ("IH" with "Hb") as "(%s2' & Hb & Hc)".
        iFrame.
      + iIntros "(%s2' & (%s1' & ? & ?) & ?)".
        iFrame. iApply "IH". iFrame.
  Qed.

  Lemma simplify_goal_iterator_next_back_fused_trans_snoc π p s1 hist s2 s1' hist' T :
    (∃ x, ⌜hist = hist' ++ [x]⌝ ∗
      IteratorNextBackFusedTrans A π p s1 hist' s1' ∗
      A.(traits_double_ended_DoubleEndedIterator_NextBack) π p s1' (Some x) s2) ∗ T
    ⊢ simplify_goal (IteratorNextBackFusedTrans A π p s1 hist s2) T.
  Proof.
    rewrite /simplify_goal.
    iIntros "((%x & -> & Ha & Hb) & $)".
    rewrite iterator_next_back_fused_trans_snoc. iFrame.
  Qed.

  Definition simplify_goal_iterator_next_back_fused_trans_snoc_find_next π p s1 hist s2 s1' hist'
      `{!CheckOwnInContext (IteratorNextBackFusedTrans A π p s1 hist' s1')}
      e s1''
      `{!CheckOwnInContext (A.(traits_double_ended_DoubleEndedIterator_NextBack) π p s1' (Some e) s1'')} T :=
    simplify_goal_iterator_next_back_fused_trans_snoc π p s1 hist s2 s1' hist' T.
  Definition simplify_goal_iterator_next_back_fused_trans_snoc_find_next_inst :=
    [instance @simplify_goal_iterator_next_back_fused_trans_snoc_find_next with 50%N].
  Global Existing Instance simplify_goal_iterator_next_back_fused_trans_snoc_find_next_inst.

  Definition simplify_goal_iterator_next_back_fused_trans_snoc_not_var π p s1 hist s2 s1' hist'
      `{!CheckOwnInContext (IteratorNextBackFusedTrans A π p s1 hist' s1')}
      `{!IsNotVar A} T :=
    simplify_goal_iterator_next_back_fused_trans_snoc π p s1 hist s2 s1' hist' T.
  Definition simplify_goal_iterator_next_back_fused_trans_snoc_not_var_inst :=
    [instance @simplify_goal_iterator_next_back_fused_trans_snoc_not_var with 50%N].
  Global Existing Instance simplify_goal_iterator_next_back_fused_trans_snoc_not_var_inst.

  Lemma simplify_goal_iterator_next_back_fused_trans_nil π p s1 hist T :
    ⌜hist = []⌝ ∗ T ⊢ simplify_goal (IteratorNextBackFusedTrans A π p s1 hist s1) T.
  Proof. rewrite /simplify_goal. iIntros "(-> & $)". eauto. Qed.
  Definition simplify_goal_iterator_next_back_fused_trans_nil_inst :=
    [instance @simplify_goal_iterator_next_back_fused_trans_nil with 10%N].
  Global Existing Instance simplify_goal_iterator_next_back_fused_trans_nil_inst.

  Global Instance IteratorNextBackFusedTrans_pers π p :
    (∀ s1 e s2, Persistent (A.(traits_double_ended_DoubleEndedIterator_NextBack) π p s1 e s2)) →
    ∀ s1 hist s2, Persistent (IteratorNextBackFusedTrans A π p s1 hist s2).
  Proof.
    intros Hpers s1 hist s2.
    induction hist as [ | x hist IH] in s1, s2, hist |-*; simpl; first apply _.
    apply _.
  Qed.

  Class IteratorBackLearnInductive p := mk_iterator_back_learn {
    iterator_back_learn_inductive_Q : RT_xt Self_rt → list (RT_xt Item_rt) → RT_xt Self_rt → Prop;
    iterator_back_learn_inductive_proof π s1 hist s2 :
      ☒ IteratorNextBackFusedTrans A π p s1 hist s2 -∗
        ⌜iterator_back_learn_inductive_Q s1 hist s2⌝;
  }.

  Global Program Instance learn_from_hyp_iterator_back π p s1 xs s2 :
    IteratorBackLearnInductive p → LearnFromHyp (IteratorNextBackFusedTrans A π p s1 xs s2) :=
    λ L, {| learn_from_hyp_Q := ⌜L.(iterator_back_learn_inductive_Q) s1 xs s2⌝ |}.
  Next Obligation.
    iIntros (π p s1 xs s2 L F ?) "Ha".
    iPoseProof (boringly_intro with "Ha") as "#Hx".
    iPoseProof (iterator_back_learn_inductive_proof with "Hx") as "$".
    done.
  Qed.
End trans.
