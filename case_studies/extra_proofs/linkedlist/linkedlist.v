From refinedrust Require Import typing.

Section linkedlist.
  Context `{!typeGS Σ}.
  Context {rt : RT}.

  Lemma linkedlist_node_to_xrfn (ty : type rt) sls F π x l next prev q :
    lftE ⊆ F →
    rrust_ctx -∗ q.[lft_intersect_list (ty_lfts ty)] -∗
    guarded true (l ◁ₗ[π, Owned] #( *[#x; #next; #prev]) @
      ◁ struct_t sls +[ty; alias_ptr_t; alias_ptr_t]) -∗
    logical_step F ((∃ xr : RT_xt rt,
      guarded true (l ◁ₗ[π, Owned] #( *[#($# xr); #next; #prev]) @
        ◁ struct_t sls +[ty; alias_ptr_t; alias_ptr_t])) ∗
      q.[lft_intersect_list (ty_lfts ty)]).
  Proof.
    iIntros (HF) "#CTX Htok Hg".
    rewrite /guarded /maybe_creds /have_creds /num_cred.
    iDestruct "Hg" as "((Hcreds & Hat) & Hl)".
    iDestruct "Hcreds" as "(Hc & Hcreds)".
    iApply fupd_logical_step.
    iApply (lc_fupd_add_later with "Hc"). iNext.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & %Hly & #Hsc & #Hlb & %ri & Hrfn & Hown)".
    iEval (simpl) in "Hrfn". iDestruct "Hrfn" as "<-".
    iMod (fupd_mask_mono with "Hown") as "(%v & Hl & Hown)"; first done.
    iDestruct (struct_own_val_acc _ _ 0 rt ty (#x) with "Hown")
      as "(%v' & %r' & Hrfn & Hown & Hclose)"; first done.
    iEval (simpl) in "Hrfn". iDestruct "Hrfn" as "<-".
    iPoseProof (ty_own_val_to_xrfn ty F π x MetaNone v' q
      with "CTX Htok Hown") as "Hstep"; first done.
    iModIntro. iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_tr with "Hat").
    iIntros "Hat Hnewcreds". iModIntro.
    iIntros "((%xr & Hown) & Htok)".
    iSpecialize ("Hclose" $! rt ty ($# xr) with "[] Hown"); first done.
    iModIntro. iFrame "Htok". iExists xr.
    rewrite /guarded /maybe_creds /have_creds /num_cred.
    iSplitL "Hnewcreds Hat".
    { iFrame. iApply tr_weaken; last done.
      simpl. unfold num_laters_per_step. lia. }
    iNext. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly. iFrame "#%".
    iExists (-[#($# xr); #next; #prev]). iSplitR; first done.
    iModIntro. iExists v. iFrame "Hl". done.
  Qed.

  Definition linkedlist_node π (ty : type rt) sls (locs : list loc) i x : iProp Σ :=
    ∃ l lnext lprev : loc, ⌜locs !! i = Some l⌝ ∗
      ⌜(locs ++ [NULL_loc]) !! S i = Some lnext⌝ ∗
      ⌜(NULL_loc :: locs) !! i = Some lprev⌝ ∗
      guarded true (l ◁ₗ[π, Owned] #( *[#x; #lnext; #lprev]) @
        ◁ struct_t sls +[ty; alias_ptr_t; alias_ptr_t]) ∗
      freeable_nz l (ly_size (use_struct_layout_alg' sls)) 1 HeapAlloc.

  Definition linkedlist_node_shared π κ (ty : type rt) sls (locs : list loc) prev_ptr i x : iProp Σ :=
    ∃ l lnext lprev : loc, ⌜locs !! i = Some l⌝ ∗
      ⌜(locs ++ [NULL_loc]) !! S i = Some lnext⌝ ∗
      ⌜(prev_ptr :: locs) !! i = Some lprev⌝ ∗
      guarded false (l ◁ₗ[π, Shared κ] #( *[#x; #lnext; #lprev]) @
        ◁ struct_t sls +[ty; alias_ptr_t; alias_ptr_t]) ∗ True.

  Global Instance linkedlist_nodes_shareable π κ (ty : type rt) sls locs xs (assumptions : Prop) :
    Shareable π κ (ty_lfts ty) xs assumptions
      ([∗ list] i ↦ x ∈ xs, linkedlist_node π ty sls locs i x).
  Proof.
    apply big_sepL_shareable_lookup. intros i x.
    unfold linkedlist_node.
    apply exist_shareable. intros l.
    apply exist_shareable. intros next.
    apply exist_shareable. intros prev.
    assert (Hcanonical : (assumptions ∧ xs !! i = Some x) →
      IsXrfnImplies (rt2 := place_rfnRT (plistRT [rt; locRT; locRT]))
        xs (#( *[#x; #next; #prev]))).
    { intros [_ Hlook]. constructor. intros Houter.
      assert (Hx : IsXrfn x).
      { constructor. apply is_xrfn_list_iff in Houter.
        eapply Forall_lookup_1; eauto. }
      apply is_xrfn_proof. }
    apply _.
  Defined.
  Lemma linkedlist_nodes_to_xrfn (ty : type rt) sls F π xs locs q :
    lftE ⊆ F → rrust_ctx -∗ q.[lft_intersect_list (ty_lfts ty)] -∗
    ([∗ list] i ↦ x ∈ xs, linkedlist_node π ty sls locs i x) -∗
    logical_step F ((∃ xrs : list (RT_xt rt), ⌜length xrs = length xs⌝ ∗
      [∗ list] i ↦ xr ∈ xrs, linkedlist_node π ty sls locs i ($# xr)) ∗
      q.[lft_intersect_list (ty_lfts ty)]).
  Proof.
    iIntros (HF) "#CTX Htok Hnodes".
    iPoseProof (Fractional_split_big_sepL
      (λ q, q.[lft_intersect_list (ty_lfts ty)])%I (length xs) with "Htok")
      as "(%qs & %Hlen & Htoks & Hclose)".
    iAssert ([∗ list] i ↦ x; q' ∈ xs; qs,
      logical_step F ((∃ xr : RT_xt rt,
        linkedlist_node π ty sls locs i ($# xr)) ∗
        q'.[lft_intersect_list (ty_lfts ty)]))%I
      with "[Hnodes Htoks]" as "Hsteps".
    { iApply (big_sepL2_wand with "[Hnodes Htoks]").
      { iApply big_sepL2_sep_sepL_r. iFrame "Htoks".
        iApply big_sepL2_const_sepL_l. iSplit; first done. done. }
      iApply big_sepL2_intro; first done.
      iModIntro. iIntros (i x q' Hlook Hlookq) "(Hnode & Htok)".
      iDestruct "Hnode" as "(%l & %next & %prev & %Hl & %Hnext & %Hprev & Hg & Hfree)".
      iPoseProof (linkedlist_node_to_xrfn ty sls F π x l next prev q'
        with "CTX Htok Hg") as "Hstep"; first done.
      iApply (logical_step_wand with "Hstep").
      iIntros "((%xr & Hg) & Htok)". iFrame "Htok".
      iExists xr. iExists l, next, prev. iFrame "∗%". }
    iPoseProof (logical_step_big_sepL2 with "Hsteps") as "Hsteps".
    iApply (logical_step_wand with "Hsteps"). iIntros "Hnodes".
    iPoseProof (big_sepL2_sep_sepL_r with "Hnodes") as "(Hnodes & Htoks)".
    iPoseProof ("Hclose" with "Htoks") as "Htok". iFrame "Htok".
    iPoseProof (big_sepL2_const_sepL_l with "Hnodes") as "(_ & Hnodes)".
    iDestruct (big_sepL_exists with "Hnodes") as "(%xrs & Hnodes)".
    iPoseProof (big_sepL2_length with "Hnodes") as "%Hxrs".
    iExists xrs. iSplit; first by iPureIntro; lia.
    iApply (big_sepL2_elim_l with "Hnodes").
  Qed.

  Definition linkedlist_inv π (ty : type rt) sls
      (inner : plist (RT_rt ∘ place_rfnRT) [locRT; locRT]) (xs : list rt) : iProp Σ :=
    ∃ (locs : list loc) (hd tl : loc), ⌜inner = -[#hd; #tl]⌝ ∗
      ⌜if decide (tl.(loc_a) = 0)
        then xs = [] ∧ hd = NULL_loc ∧ tl = NULL_loc
        else length xs > 0 ∧ head locs = Some hd ∧ last locs = Some tl⌝ ∗
      ⌜length locs = length xs⌝ ∗ ⌜hd.(loc_a) = 0 ↔ tl.(loc_a) = 0⌝ ∗
      ⌜Forall (λ l, l.(loc_a) ≠ 0) locs⌝ ∗
      ([∗ list] i ↦ x ∈ xs, linkedlist_node π ty sls locs i x) ∗ True.

  Global Instance canonicalizable_linkedlist π (ty : type rt) sls
      (repr : type (plistRT [locRT; locRT])) inner xs :
    Canonicalizable π (ty_lfts ty) repr inner xs
      (linkedlist_inv π ty sls inner xs) (linkedlist_inv π ty sls).
  Proof.
    constructor. intros F m v q HF.
    iIntros "#CTX Htok ((%locs & %hd & %tl & %Hinner & %Hends & %Hlen & %Hnull & %Hnonnull & Hnodes & _) & Hrepr)".
    rewrite lft_intersect_list_app -lft_tok_sep.
    iDestruct "Htok" as "(Htoki & Htokr)".
    iPoseProof (linkedlist_nodes_to_xrfn ty sls F π xs locs q
      with "CTX Htoki Hnodes") as "Hstep"; first done.
    iApply (logical_step_wand with "Hstep").
    iIntros "((%xrs & %Hxrs & Hnodes) & Htoki)".
    iSplitR "Htoki Htokr"; last by iFrame.
    iExists inner, xrs. iFrame "Hrepr".
    rewrite /linkedlist_inv /=.
    iExists locs, hd, tl. rewrite big_sepL_fmap. iFrame "Hnodes".
    simpl. repeat iSplit; try iPureIntro; try done.
    - case_decide; simpl in *.
      + destruct Hends as (-> & -> & ->). rewrite length_nil in Hxrs.
        apply length_zero_iff_nil in Hxrs. subst xrs. done.
      + rewrite length_fmap Hxrs. done.
    - rewrite length_fmap Hxrs. done.
    - naive_solver.
    - naive_solver.
  Qed.
End linkedlist.

Global Hint Extern 10 (Canonicalizable _ _ _ _ _ _ _) =>
  apply canonicalizable_linkedlist : typeclass_instances.
