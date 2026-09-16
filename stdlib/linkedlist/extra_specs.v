Section linkedlist_resolve.
  Context `{RRGS : !refinedrustGS Σ}.

  Definition linkedlist_Node_pointer {T_rt} (T_ty : type T_rt) :=
    Option_ty (nonnull_NonNull_inv_t_rt (Node_inv_t_rt T_rt)) -[]
      -[nonnull_NonNull_inv_t (Node_inv_t_rt T_rt) -[] -[Node_inv_t T_rt -[] -[T_ty]]].

  Definition linkedlist_Node_struct {T_rt} (T_ty : type T_rt) :=
    struct_t (Node_sls (ty_syn_type T_ty MetaNone))
      +[linkedlist_Node_pointer T_ty; linkedlist_Node_pointer T_ty; T_ty].

  Lemma linkedlist_Node_unfold_owned {T_rt} (T_ty : type T_rt) F π l next prev elem :
    lftE ⊆ F →
    l ◁ₗ[π, Owned] #(next, prev, elem) @ ◁(Node_inv_t T_rt -[] -[T_ty]) -∗
    |={F}=> l ◁ₗ[π, Owned] #(-[#(<#>@{option} next); #(<#>@{option} prev); elem])
      @ ◁(linkedlist_Node_struct T_ty).
  Proof.
    iIntros (HF) "Hnode".
    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hnode".
    iDestruct "Hnode" as "(%ly & %Halg & %Hloc & Hsc & #Hlb & %r & %Hr & Hv)".
    subst r.
    iMod (fupd_mask_mono with "Hv") as "(%v & Hbytes & Hv)"; first done.
    iPoseProof (mut_type_project_fixpoint_own_val_unfold
      (λ tys, Node_inv_t_bundle_F tys -[] -[T_ty]) 0 eq_refl π
      (next, prev, elem)
      (Hne := Node_inv_t_bundle_tys_obligation_1 T_ty)
      (Hcontr := Node_inv_t_bundle_tys_obligation_2 T_ty)
      MetaNone v with "Hv") as "Hv".
    iEval (rewrite /mutual_fixpoint.mut_fixpoint_project_unfolded /=
      /Node_inv_t_pre /Node_inv_t_pre_raw /ty_own_val /=
      ex_plain_own_val_unfold /ex_plain_own_val_def /Node_inv_t_inv_spec /=) in "Hv".
    iDestruct "Hv" as "(%inner & (-> & _) & Hv)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly.
    iSplitR. { iPureIntro. rewrite mut_fixpoint_project_ty_syn_type in Halg. exact Halg. }
    iSplitR; first done. iSplitR; first done. iFrame "Hlb".
    iExists _. iSplitR; first done. iModIntro. iExists v. by iFrame.
  Qed.

  Lemma linkedlist_Node_fold_owned {T_rt} (T_ty : type T_rt) F π l next prev elem :
    lftE ⊆ F →
    l ◁ₗ[π, Owned] #(-[#(<#>@{option} next); #(<#>@{option} prev); elem])
      @ ◁(linkedlist_Node_struct T_ty) -∗
    |={F}=> l ◁ₗ[π, Owned] #(next, prev, elem) @ ◁(Node_inv_t T_rt -[] -[T_ty]).
  Proof.
    iIntros (HF) "Hnode".
    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hnode".
    iDestruct "Hnode" as "(%ly & %Halg & %Hloc & Hsc & #Hlb & %r & %Hr & Hv)".
    subst r.
    iMod (fupd_mask_mono with "Hv") as "(%v & Hbytes & Hv)"; first done.
    iAssert (v ◁ᵥ{π, MetaNone} (next, prev, elem) @ (Node_inv_t T_rt -[] -[T_ty]))%I
      with "[Hv]" as "Hv".
    { iApply (mut_type_project_fixpoint_own_val_fold
        (λ tys, Node_inv_t_bundle_F tys -[] -[T_ty]) 0 eq_refl π
        (next, prev, elem)
        (Hne := Node_inv_t_bundle_tys_obligation_1 T_ty)
        (Hcontr := Node_inv_t_bundle_tys_obligation_2 T_ty) MetaNone v).
      rewrite /mutual_fixpoint.mut_fixpoint_project_unfolded /=
        /Node_inv_t_pre /Node_inv_t_pre_raw /ty_own_val /=
        ex_plain_own_val_unfold /ex_plain_own_val_def /Node_inv_t_inv_spec /=.
      iExists _. by iFrame. }
    iPoseProof (ty_own_val_sidecond with "Hv") as "#Hside".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iModIntro. iExists ly.
    iSplitR. { iPureIntro. rewrite mut_fixpoint_project_ty_syn_type. exact Halg. }
    iSplitR; first done. iFrame "Hside Hlb".
    iExists _. iSplitR; first done. iModIntro. iExists v. by iFrame.
  Qed.
  (** Expose the actual element-field location, retaining a logical-step
      restoration of the node with unchanged links. *)
  Lemma linkedlist_Node_element_acc {T_rt} (T_ty : type T_rt) F π l next prev elem :
    lftE ⊆ F →
    l ◁ₗ[π, Owned] #(next, prev, elem) @ ◁(Node_inv_t T_rt -[] -[T_ty]) -∗
    |={F}=> ∃ element_loc,
      element_loc ◁ₗ[π, Owned] elem @ ◁T_ty ∗
      logical_step F (∀ elem', element_loc ◁ₗ[π, Owned] elem' @ ◁T_ty ={F}=∗
        l ◁ₗ[π, Owned] #(next, prev, elem') @ ◁(Node_inv_t T_rt -[] -[T_ty])).
  Proof.
    iIntros (HF) "Hnode".
    iMod (linkedlist_Node_unfold_owned with "Hnode") as "Hnode"; first done.
    iMod (ltype_incl'_use F with "[] Hnode") as "Hnode"; first done.
    { iApply struct_t_unfold_1_owned. }
    iDestruct (struct_ltype_acc_owned with "Hnode") as
      "(%sl & %Halg & %Hloc & %Hlen & #Hlb & Hnode)"; first done.
    iMod "Hnode" as "(Hfields & Hclose)".
    iPoseProof (pad_struct_focus_no_uninit with "Hfields") as "(Hfields & Hpad)".
    { rewrite -(struct_layout_spec_has_layout_fields_length' _ _ Halg). done. }
    { exact (bool_decide_unpack _ (sl_nodup sl)). }
    iDestruct "Hfields" as "(Hnext & Hprev & (%j & %ly & %name & %Hfield & %Hnamed & %ly' & %Hmem & %Hty & Helt) & _)".
    iExists (l +ₗ offset_of_idx (sl_members sl) j). iFrame "Helt".
    iModIntro.
    iApply (logical_step_wand with "Hclose [Hnext Hprev Hpad]").
    iIntros "Hclose" (elem') "Helt".
    iMod ("Hclose" $! [optionRT (place_rfnRT locRT); optionRT (place_rfnRT locRT); T_rt]
      +[(◁linkedlist_Node_pointer T_ty)%I; (◁linkedlist_Node_pointer T_ty)%I; (◁T_ty)%I]
      (-[#(<#>@{option} next); #(<#>@{option} prev); elem'])
      with "[//] [Hnext Hprev Hpad Helt]") as "Hnode".
    { iApply ("Hpad" $! (hpzipl (F := ltype) (G := λ rt : RT, place_rfnRT rt)
        [optionRT (place_rfnRT locRT); optionRT (place_rfnRT locRT); T_rt]
        +[(◁linkedlist_Node_pointer T_ty)%I; (◁linkedlist_Node_pointer T_ty)%I; (◁T_ty)%I]
        (-[#(<#>@{option} next); #(<#>@{option} prev); elem']))
        with "[//] [Hnext Hprev Helt]").
      simpl. iFrame "Hnext Hprev".
      iSplit; last done.
      iExists j, ly, name. iSplit; first done. iSplit; first done.
      iExists ly'. by iFrame "Helt %". }
    iMod (ltype_incl'_use F with "[] Hnode") as "Hnode"; first done.
    { iApply (struct_t_unfold_2_owned
        +[linkedlist_Node_pointer T_ty; linkedlist_Node_pointer T_ty; T_ty]
        (Node_sls (ty_syn_type T_ty MetaNone))). }
    by iApply (linkedlist_Node_fold_owned with "Hnode").
  Qed.
  Lemma linkedlist_guarded_Node_element_acc {T_rt} (T_ty : type T_rt) F π l next prev elem :
    lftE ⊆ F →
    guarded true (l ◁ₗ[π, Owned] #(next, prev, elem) @ ◁(Node_inv_t T_rt -[] -[T_ty])) -∗
    |={F}=> ∃ element_loc,
      element_loc ◁ₗ[π, Owned] elem @ ◁T_ty ∗
      logical_step F (∀ elem', element_loc ◁ₗ[π, Owned] elem' @ ◁T_ty ={F}=∗
        guarded true (l ◁ₗ[π, Owned] #(next, prev, elem') @ ◁(Node_inv_t T_rt -[] -[T_ty]))).
  Proof.
    iIntros (HF) "Hnode".
    unfold guarded. iDestruct "Hnode" as "(((Hcredit & Hcredits) & Htime) & Hnode)".
    iApply (lc_fupd_add_later with "Hcredit"). iNext.
    iMod (linkedlist_Node_element_acc with "Hnode") as "(%element_loc & Helt & Hclose)"; first done.
    iExists element_loc. iFrame "Helt". iModIntro.
    iApply (logical_step_compose with "Hclose").
    iApply (logical_step_intro_tr with "Htime").
    iIntros "Htime Hcredit !> Hclose" (elem') "Helt".
    iMod ("Hclose" with "Helt") as "Hnode".
    iModIntro. rewrite /guarded /maybe_creds /have_creds.
    iFrame "Hnode". iSplitL "Hcredit".
    { iApply (lc_weaken with "Hcredit"). simpl. unfold num_cred, num_laters_per_step. lia. }
    iDestruct "Htime" as "(_ & $)".
  Qed.

  Lemma linkedlist_LL_elements_acc {T_rt A} (T_ty : type T_rt)
      (freeable : A → loc → iProp Σ) F π elems locs alloc offset :
    lftE ⊆ F →
    LL_segment (λ l next prev elem, guarded true
      (l ◁ₗ[π, Owned] #(next, prev, elem) @ ◁(Node_inv_t T_rt -[] -[T_ty])))
      freeable offset elems locs alloc -∗
    |={F}=> ∃ element_locs, ⌜length element_locs = length elems⌝ ∗
      ([∗ list] l; elem ∈ element_locs; elems, l ◁ₗ[π, Owned] elem @ ◁T_ty) ∗
      logical_step F (∀ elems', ⌜length elems' = length elems⌝ -∗
        ([∗ list] l; elem ∈ element_locs; elems', l ◁ₗ[π, Owned] elem @ ◁T_ty) ={F}=∗
        LL_segment (λ l next prev elem, guarded true
          (l ◁ₗ[π, Owned] #(next, prev, elem) @ ◁(Node_inv_t T_rt -[] -[T_ty])))
          freeable offset elems' locs alloc).
  Proof.
    intros HF. revert offset.
    induction elems as [|elem elems IH]; intros offset.
    - iIntros "_". iModIntro. iExists []. iSplit; first done. iSplit; first done.
      iApply logical_step_intro. iIntros (elems') "%Hlen _".
      destruct elems'; last discriminate. iModIntro. rewrite /LL_segment. done.
    - rewrite LL_segment_cons.
      iIntros "(Hhead & Htail)".
      iDestruct "Hhead" as "(%l & %next & %prev & %Hl & %Hnext & %Hprev & Hnode & Hfree)".
      iMod (linkedlist_guarded_Node_element_acc with "Hnode") as "(%element_loc & Helt & Hhead)"; first done.
      iMod (IH with "Htail") as "(%element_locs & %Hlocs & Helts & Htail)".
      iModIntro. iExists (element_loc :: element_locs).
      iSplit; first by iPureIntro; simpl; f_equal.
      iSplitL "Helt Helts"; first by iFrame.
      iApply (logical_step_compose with "Hhead").
      iApply (logical_step_wand with "Htail [Hfree]").
      iIntros "Htail Hhead" (elems') "%Hlen Helts".
      destruct elems' as [|elem' elems']; first discriminate.
      iDestruct "Helts" as "(Helt & Helts)".
      iMod ("Hhead" with "Helt") as "Hnode".
      iMod ("Htail" $! elems' with "[] Helts") as "Htail"; first by iPureIntro; injection Hlen.
      iModIntro. rewrite LL_segment_cons. iFrame "Htail".
      iExists l, next, prev. by iFrame.
  Qed.
  (** Resolve elements at their extracted locations and restore the list's
      node ownership, guards, allocator permissions, and length invariant. *)
  Lemma resolve_ghost_LinkedList {T_rt A_rt} A_attrs (T_ty : type T_rt) (A_ty : type A_rt)
      π E L rm r T :
    resolve_ghost_iter π E L rm true
      (replicate (length r.(linked_list_elems)) (◁T_ty)) Owned
      r.(linked_list_elems) [] 0%nat
      (λ L' elems' R progress,
        T L' (mk_linked_list_x elems' r.(linked_list_locs) r.(linked_list_alloc)) R progress) ⊢
    resolve_ghost_adt π E L rm r
      (LinkedList_inv_t T_rt A_rt A_attrs -[] -[T_ty; A_ty]) T.
  Proof.
    rewrite /resolve_ghost_adt /resolve_ghost_iter.
    iIntros "HT" (F v ??) "#CTX #HE HL Hv".
    rewrite ex_plain_t_unfold_val.
    destruct r as [elems locs alloc].
    iDestruct "Hv" as "(%inner & Hinv & Hv)".
    iDestruct "Hinv" as "(%Hinner & %Hlen & %Hnonnull & %Hbound & Helems & _)".
    subst inner. simpl in *.
    iEval (rewrite /LL) in "Helems".
    iMod (linkedlist_LL_elements_acc T_ty _ F π elems locs alloc 0%nat with "Helems") as
      "(%element_locs & %Helement_locs & Helts & Hclose)"; first done.
    iMod ("HT" $! F element_locs with "[//] [//] CTX HE HL [//] [] [Helts]") as
      "(%L' & %elems' & %R & %progress & Hstep & HL & HT)".
    { iPureIntro. apply length_replicate. }
    { rewrite big_sepL2_replicate_r; last done.
      iApply (big_sepL2_elim_l).
      iApply (big_sepL2_impl with "Helts"). iModIntro.
      iIntros (i l elem Hl Helem) "Helt".
      rewrite (list_lookup_total_correct element_locs i l Hl). done. }
    iExists L', (mk_linked_list_x elems' locs alloc), R, progress. iFrame "HL HT".
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hclose").
    iApply (logical_step_wand with "Hstep [Hv]").
    iIntros "(Helts & HR) Hclose".
    iDestruct (big_sepL2_length with "Helts") as %Hnewlen.
    rewrite length_replicate in Hnewlen.
    iEval (rewrite big_sepL2_replicate_r; last done) in "Helts".
    iAssert ([∗ list] l; elem ∈ element_locs; elems', l ◁ₗ[π, Owned] elem @ ◁T_ty)%I
      with "[Helts]" as "Helts".
    { iAssert ([∗ list] i ↦ l; elem ∈ element_locs; elems',
        True ∗ (element_locs !!! i) ◁ₗ[π, Owned] elem @ ◁T_ty)%I
        with "[Helts]" as "Helts".
      { iApply (big_sepL2_sepL_2 _ _ element_locs elems' with "[] Helts").
        { rewrite Helement_locs. symmetry. exact Hnewlen. }
        iApply big_sepL_intro. by iIntros "!>" (i l Hl). }
      iApply (big_sepL2_impl with "Helts"). iModIntro.
      iIntros (i l elem Hl Helem) "(_ & Helt)".
      rewrite (list_lookup_total_correct element_locs i l Hl). done. }
    iMod ("Hclose" with "[] Helts") as "Helems"; first by iPureIntro; exact Hnewlen.
    iModIntro. iFrame "HR". rewrite ex_plain_t_unfold_val.
    iExists (-[#(<#>@{option} (head locs)); #(<#>@{option} (last locs));
      #(Z.of_nat (length elems)); #($# alloc); #tt]). iFrame "Hv".
    iSplit; first by iPureIntro; simpl; rewrite Hnewlen.
    iSplit; first by iPureIntro; simpl; rewrite Hnewlen.
    iSplit; first done. iSplit; first by iPureIntro; simpl; rewrite Hnewlen.
    iSplit; last done.
    iEval (rewrite /LL_segment) in "Helems". rewrite /LL.
    iApply (big_sepL_impl with "Helems"). iModIntro.
    iIntros (i elem Hlookup) "Hitem". rewrite Nat.add_0_l. done.
  Qed.
  Definition resolve_ghost_LinkedList_inst := [instance @resolve_ghost_LinkedList].
  Global Existing Instance resolve_ghost_LinkedList_inst.
End linkedlist_resolve.
