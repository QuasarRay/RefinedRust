From radium Require Import lang notation.
From iris.algebra Require Import auth gmap frac agree.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_push_front_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* Count physical addresses, not locations: allocation provenance is unbounded. *)
Lemma push_front_mbyte_addr_ne l1 l2 b1 b2 :
  heap_pointsto_mbyte l1 1 b1 -∗ heap_pointsto_mbyte l2 1 b2 -∗
  ⌜l1.(loc_a) ≠ l2.(loc_a)⌝.
Proof.
  rewrite heap_pointsto_mbyte_eq /heap_pointsto_mbyte_def /heap_pointsto_mbyte_st.
  iIntros "(%id1 & _ & H1) (%id2 & _ & H2)".
  iIntros (Heq). rewrite Heq.
  iCombine "H1 H2" as "H".
  rewrite own_valid internal_cmra_valid_discrete.
  iDestruct "H" as %Hvalid. iPureIntro.
  move: Hvalid => /auth_frag_valid /singleton_valid /=.
  rewrite !pair_valid /=. move => [[Hfrac _] _].
  exact (Qp.not_add_le_l 1 1 Hfrac).
Qed.

Definition push_front_nonempty_heap (l : loc) : iProp Σ :=
  ∃ v, ⌜v ≠ []⌝ ∗ l ↦ v.

Lemma push_front_heap_addr_ne l1 l2 :
  push_front_nonempty_heap l1 -∗ push_front_nonempty_heap l2 -∗
  ⌜l1.(loc_a) ≠ l2.(loc_a)⌝.
Proof.
  iIntros "(%v1 & %Hv1 & H1) (%v2 & %Hv2 & H2)".
  destruct v1 as [|b1 v1]; first done.
  destruct v2 as [|b2 v2]; first done.
  rewrite !heap_pointsto_cons_mbyte.
  iDestruct "H1" as "(H1 & _)". iDestruct "H2" as "(H2 & _)".
  by iApply (push_front_mbyte_addr_ne with "H1 H2").
Qed.

Lemma push_front_heap_nodup locs :
  ([∗ list] l ∈ locs, push_front_nonempty_heap l) -∗
  ⌜NoDup (loc_a <$> locs)⌝.
Proof.
  induction locs as [|l locs IH]; simpl; first by iIntros "_"; iPureIntro; constructor.
  iIntros "[Hl Hlocs]".
  iDestruct (IH with "Hlocs") as %Hnodup.
  rewrite NoDup_cons. iSplit; last done. iIntros (Hin).
  apply list_elem_of_fmap in Hin as (l' & Heq & Hin).
  apply list_elem_of_lookup_1 in Hin as (i & Hlookup).
  iDestruct (big_sepL_lookup with "Hlocs") as "Hl'"; first exact Hlookup.
  iDestruct (push_front_heap_addr_ne with "Hl Hl'") as %Hne.
  done.
Qed.

Lemma push_front_heap_bound locs :
  ([∗ list] l ∈ locs, push_front_nonempty_heap l) -∗
  ⌜Z.of_nat (length locs) < MaxInt usize⌝.
Proof.
  iIntros "Hlocs".
  iDestruct (push_front_heap_nodup with "Hlocs") as %Hnodup.
  iAssert (⌜Forall (λ l, 1 ≤ l.(loc_a) < MaxInt usize) locs⌝)%I as %Hrange.
  { rewrite Forall_forall. iIntros (l Hin).
    apply list_elem_of_lookup_1 in Hin as (i & Hlookup).
    iDestruct (big_sepL_lookup with "Hlocs") as "(%v & %Hv & Hl)"; first exact Hlookup.
    iDestruct (heap_pointsto_ptr_in_range with "Hl") as %[Hlo Hhi].
    iPureIntro. rewrite MaxInt_eq. rewrite /min_alloc_start in Hlo.
    destruct v; simpl in *; [done | lia]. }
  iPureIntro.
  opose proof* (NoDup_list_subseteq_length_le (loc_a <$> locs)
    (seqZ 1 (MaxInt usize - 1))) as Hcount; first done.
  { intros a Ha. apply list_elem_of_fmap in Ha as (l & -> & Hin).
    apply elem_of_seqZ. rewrite Forall_forall in Hrange.
    specialize (Hrange l Hin). lia. }
  rewrite length_fmap length_seqZ in Hcount.
  assert (0 ≤ MaxInt usize - 1) by (rewrite MaxInt_eq; cbv; lia).
  lia.
Qed.

(* Expose bytes only temporarily; the continuation restores the same value. *)
Lemma push_front_owned_heap {rt} (ty : type rt) π r l ly :
  syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly →
  (0 < ly.(ly_size))%nat →
  l ◁ₗ[π, Owned] r @ ◁ ty ={lftE}=∗
    ∃ v, ⌜v ≠ []⌝ ∗ l ↦ v ∗ (l ↦ v -∗ l ◁ₗ[π, Owned] r @ ◁ ty).
Proof.
  iIntros (Hlayout Hsize) "Hown".
  iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hown".
  iDestruct "Hown" as (ly') "(%Hlayout' & %Hloc & Hsc & Hlb & %r' & Hr & Hown)".
  assert (ly' = ly) as -> by (eapply syn_type_has_layout_inj; done).
  iMod "Hown" as (v) "[Hl Hv]".
  iDestruct (ty_own_val_has_layout with "Hv") as %Hval; first exact Hlayout.
  iModIntro. iExists v. iSplit.
  { iPureIntro. rewrite /has_layout_val in Hval. intros ->. simpl in Hval. lia. }
  iFrame "Hl". iIntros "Hl".
  rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iExists ly. iSplit; first done. iSplit; first done.
  iFrame "Hsc Hlb". iExists r'. iFrame "Hr".
  iModIntro. iExists v. iFrame.
Qed.

Lemma push_front_LL_bound {E A : Type}
    (node : loc → option loc → option loc → E → iProp Σ)
    (freeable : A → loc → iProp Σ) elems locs alloc :
  length locs = length elems →
  (∀ l next prev elem, node l next prev elem ={lftE}=∗
    ∃ v, ⌜v ≠ []⌝ ∗ l ↦ v ∗ (l ↦ v -∗ node l next prev elem)) →
  LL node freeable elems locs alloc ={lftE}=∗
    ⌜Z.of_nat (length elems) < MaxInt usize⌝ ∗ LL node freeable elems locs alloc.
Proof.
  iIntros (Hlen Hnode) "HLL".
  set (opened := λ l next prev elem,
    (∃ v, ⌜v ≠ []⌝ ∗ l ↦ v ∗ (l ↦ v -∗ node l next prev elem))%I).
  iAssert (|={lftE}=> LL opened freeable elems locs alloc)%I
    with "[HLL]" as ">HLL".
  { rewrite /LL /LL_item /opened.
    iApply big_sepL_fupd.
    iEval (rewrite /LL /LL_item) in "HLL".
    iApply (big_sepL_impl with "HLL"). iIntros "!>" (i elem Hlookup).
    iIntros "(%l & %next & %prev & %Hl & %Hnext & %Hprev & Hnode & Hfree)".
    iMod (Hnode with "Hnode") as (v) "(%Hv & Hbytes & Hrestore)".
    iModIntro. iExists l, next, prev. iSplit; first done.
    iSplit; first done. iSplit; first done.
    iSplitL "Hbytes Hrestore"; last by iFrame.
    iExists v. by iFrame. }
  iEval (rewrite /LL /LL_item /opened) in "HLL".
  iAssert (⌜Z.of_nat (length locs) < MaxInt usize⌝)%I as %Hbound.
  { iApply push_front_heap_bound.
    iApply (big_sepL2_elim_l elems).
    iPoseProof (big_sepL2_sepL_2 _ (λ _ _, emp)%I elems locs with "HLL []") as "HLL"; [lia | done |].
    iApply (big_sepL2_impl with "HLL"). iIntros "!>" (i elem l Helem Hl).
    iIntros "[(%l' & %next & %prev & %Hl' & %Hnext & %Hprev & (%v & %Hv & Hbytes & Hrestore) & Hfree) _]".
    assert (l' = l) as -> by congruence. iExists v. by iFrame. }
  iModIntro. iSplit; first by iPureIntro; lia.
  rewrite /LL /LL_item.
  iApply (big_sepL_impl with "HLL"). iIntros "!>" (i elem Hlookup).
  iIntros "(%l & %next & %prev & %Hl & %Hnext & %Hprev & (%v & %Hv & Hbytes & Hrestore) & Hfree)".
  iExists l, next, prev. iFrame. iSplit; first done. iSplit; first done.
  iSplit; first done. by iApply "Hrestore".
Qed.

Lemma push_front_zero_fields fields :
  sum_list (ly_size <$> fields.*2) = 0%nat →
  Forall (λ '(_, ly), ly_size ly = 0%nat) (named_fields fields).
Proof.
  induction fields as [|[name ly] fields IH]; simpl; first done.
  intros Hzero. apply Nat.eq_add_0 in Hzero as [Hly Hrest].
  destruct name; simpl.
  - constructor; [exact Hly | by apply IH].
  - by apply IH.
Qed.

Lemma push_front_Node_size T_st sl :
  use_struct_layout_alg (Node_sls T_st) = Some sl →
  (0 < ly_size sl)%nat.
Proof.
  intros Hlayout. destruct (decide (ly_size sl = 0%nat)) as [Hzero|]; last lia.
  apply use_struct_layout_alg_inv in Hlayout as (fields & Halg & Hfields).
  apply struct_layout_alg_has_fields in Halg.
  change (sum_list (ly_size <$> (sl_members sl).*2) = 0%nat) in Hzero.
  apply push_front_zero_fields in Hzero. rewrite -Halg in Hzero.
  apply Forall2_cons_inv_l in Hfields as ([name ly] & rest & [Hname Hly] & Hrest & ->).
  apply Forall_cons in Hzero as [Hlyzero _]. simpl in Hlyzero.
  apply syn_type_has_layout_enum_inv in Hly as (el & variants & Helalg & -> & Hvariants & Hwf).
  apply enum_layout_alg_has_variants in Helalg as [Htag Hvariants_eq].
  apply Forall2_cons_inv_l in Hvariants as (variant & variants' & _ & _ & ->).
  pose proof (el_tag_before_data el) as Hbefore.
  rewrite Htag in Hbefore. simpl in Hbefore.
  pose proof (el_variants_in_bounds el) as Hinbounds.
  rewrite -Hvariants_eq in Hinbounds. apply Forall_cons in Hinbounds as [Hfirst _].
  assert (0 < bytes_per_int ISize)%nat by (cbv; lia).
  change (el_size el = 0%nat) in Hlyzero. lia.
Qed.

Lemma push_front_guarded_LL_bound {E A : Type}
    (node : loc → option loc → option loc → E → iProp Σ)
    (freeable : A → loc → iProp Σ) elems locs alloc :
  length locs = length elems →
  (∀ l next prev elem, node l next prev elem ={lftE}=∗
    ∃ v, ⌜v ≠ []⌝ ∗ l ↦ v ∗ (l ↦ v -∗ node l next prev elem)) →
  LL (λ l next prev elem, guarded true (node l next prev elem))
    freeable elems locs alloc -∗
  ▷ |={⊤}=> ⌜Z.of_nat (length elems) < MaxInt usize⌝ ∗
    LL (λ l next prev elem, guarded true (node l next prev elem))
      freeable elems locs alloc.
Proof.
  iIntros (Hlen Hnode) "HLL".
  set (unguarded := λ l next prev elem,
    (maybe_creds true ∗ node l next prev elem)%I).
  iAssert (▷ LL unguarded freeable elems locs alloc)%I with "[HLL]" as "HLL".
  { rewrite /LL big_sepL_later.
    iEval (rewrite /LL) in "HLL".
    iApply (big_sepL_impl with "HLL"). iIntros "!>" (i elem Hlookup).
    rewrite /LL_item /guarded /unguarded.
    iIntros "(%l & %next & %prev & %Hl & %Hnext & %Hprev & [Hcreds Hnode] & Hfree)".
    iNext. iExists l, next, prev. iFrame. done. }
  iNext.
  iAssert (|={lftE}=> ⌜Z.of_nat (length elems) < MaxInt usize⌝ ∗
    LL unguarded freeable elems locs alloc)%I with "[HLL]" as "Hbound".
  { iApply (push_front_LL_bound unguarded with "HLL"); first exact Hlen.
    iIntros (l next prev elem) "[Hcreds Hnode]".
    iMod (Hnode with "Hnode") as (v) "(%Hv & Hbytes & Hrestore)".
    iModIntro. iExists v. iFrame "Hbytes". iSplit; first done.
    iIntros "Hbytes". iFrame "Hcreds". by iApply "Hrestore". }
  iMod (fupd_mask_mono lftE ⊤ with "Hbound") as "(%Hbound & HLL)"; first done.
  iModIntro. iSplit; first done.
  rewrite /LL. iEval (rewrite /LL) in "HLL".
  iApply (big_sepL_impl with "HLL"). iIntros "!>" (i elem Hlookup).
  rewrite /LL_item /unguarded.
  iIntros "(%l & %next & %prev & %Hl & %Hnext & %Hprev & Hnode & Hfree)".
  iExists l, next, prev. iFrame "Hfree".
  iSplit; first done. iSplit; first done. iSplit; first done.
  by iApply guarded_intro.
Qed.

Lemma push_front_Node_reborrow {T_rt} (T_ty : type T_rt) π next prev γold γnew v :
  RelEq (T := RT_rt T_rt) γnew γold -∗
  v ◁ᵥ{π, MetaNone} (next, prev, PlaceGhost γold) @ (Node_inv_t T_rt -[] -[T_ty]) -∗
  v ◁ᵥ{π, MetaNone} (next, prev, PlaceGhost γnew) @ (Node_inv_t T_rt -[] -[T_ty]).
Proof.
  iIntros "Hrel Hv".
  iPoseProof (mut_type_project_fixpoint_own_val_unfold
    (λ tys, Node_inv_t_bundle_F tys -[] -[T_ty]) 0 eq_refl π
    (next, prev, PlaceGhost γold)
    (Hne := generated_specs_linkedlist.Node_inv_t_bundle_tys_obligation_1 T_ty)
    (Hcontr := generated_specs_linkedlist.Node_inv_t_bundle_tys_obligation_2 T_ty)
    MetaNone v with "Hv") as "Hv".
  iApply (mut_type_project_fixpoint_own_val_fold
    (λ tys, Node_inv_t_bundle_F tys -[] -[T_ty]) 0 eq_refl π
    (next, prev, PlaceGhost γnew)
    (Hne := generated_specs_linkedlist.Node_inv_t_bundle_tys_obligation_1 T_ty)
    (Hcontr := generated_specs_linkedlist.Node_inv_t_bundle_tys_obligation_2 T_ty)
    MetaNone v).
  iEval (rewrite /mutual_fixpoint.mut_fixpoint_project_unfolded /=) in "Hv".
  rewrite /mutual_fixpoint.mut_fixpoint_project_unfolded /=.
  iApply (ex_plain_t_own_val_transport with "[Hrel] Hv").
  iIntros (inner) "HP Hv".
  iEval (rewrite /Node_inv_t_inv_spec /=) in "HP".
  iDestruct "HP" as "(-> & _)".
  rewrite /Node_inv_t_inv_spec /=.
  iExists _. iSplit; first done.
  iApply (struct_own_val_transport _ _ 2 with "[Hrel] Hv"); first done.
  iIntros (r) "Hr".
  iDestruct (place_rfn_interp_owned_RelEq with "Hrel Hr") as "(Hr & _)".
  done.
Qed.

Lemma LinkedList_TA_push_front_mut_proof (π : thread_id) :
  LinkedList_TA_push_front_mut_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft7" ["ulft_1"].
  pose_unconstrained_lft_hint "vuclft10" ["ulft_1"].
  LinkedList_TA_push_front_mut_prelude.

  1: rep <-! <3000 liRStep.
  liShow.
  (* One credit opens the common later of the guarded list, without losing
     the ownership needed by the call below. *)
  add_updateable.
  iIntros "#CTX #HE HL".
  iRename select (LL _ _ _ _ _)%I into "Helems".
  iRename select (credit_store _ _)%I into "Hstore".
  iDestruct (credit_store_scrounge 1 with "Hstore") as "[Hcredit Hstore]"; first lia.
  open_cache.
  rename select (use_struct_layout_alg (Node_sls _) = Some Node_sl) into Hnode_layout.
  iPoseProof (push_front_guarded_LL_bound with "Helems") as "Hcount".
  { rewrite length_fmap. exact Hlen. }
  { intros node_loc next prev elem.
    apply (push_front_owned_heap _ _ _ _ Node_sl).
    - rewrite mut_fixpoint_project_ty_syn_type.
      by apply use_struct_layout_alg_Some_inv.
    - by apply (push_front_Node_size _ _ Hnode_layout). }
  iMod (lc_fupd_elim_later with "Hcredit Hcount") as "Hcount".
  iMod "Hcount" as "(%Hstrict & Helems)".
  rewrite length_fmap in Hstrict.
  iModIntro. iExists _. iFrame "HL".
  apply_update updateable_strip_guards.
  1: rep <-! <3000 liRStep.
  1: rep liRStep.
  liShow.
  iRename select (LL _ _ _ _ _)%I into "Helems".
  iEval ( rewrite list_fmap_compose) in "Helems".
  iApply prove_with_subtype_default. 
  iSplitL "Helems". { simplify_layout_goal. done. }

  1: rep <-! <3000 liRStep.
  pose_unconstrained_lft_hint "vuclft8" ["ulft_1"].
  1: rep <-! <3000 liRStep.
  liShow.
  apply_update updateable_strip_guards.
  iRename select (LL _ _ _ _ _)%I into "Helems".
  iEval (rewrite LL_cons) in "Helems".
  iDestruct "Helems" as "(Hhead & Helems)".
  iEval (rewrite /LL_item) in "Hhead".
  iRevert "Hhead".
  1: rep <-! <3000 liRStep.
  liShow.

  (* The returned reference is a chain of reborrows of the head element. *)
  add_updateable.
  iIntros "#CTX2 #HE2 HL".
  iPoseProof (lctx_lft_incl_incl _ κ4 κ6 with "HL HE2") as "#H46".
  { solve_lft_incl. }
  iPoseProof (lctx_lft_incl_incl _ κ5 κ6 with "HL HE2") as "#H56".
  { solve_lft_incl. }
  iRename select (Inherit [κ4] (RelEq γ1 γ0))%I into "H10".
  iRename select (Inherit [κ5] (RelEq γ2 γ1))%I into "H21".
  iRename select (Inherit [κ6] (RelEq γ3 γ2))%I into "H32".
  iPoseProof (Inherit_mono [κ4] [κ6] with "[] H10") as "H10".
  { rewrite /lft_intersect_list /= !right_id. done. }
  iPoseProof (Inherit_mono [κ5] [κ6] with "[] H21") as "H21".
  { rewrite /lft_intersect_list /= !right_id. done. }
  iPoseProof (Inherit_RelEq_trans with "H32 H21") as "H31".
  iPoseProof (Inherit_RelEq_trans with "H31 H10") as "H30".
  iPoseProof (lctx_lft_incl_incl _ κ6 κ2 with "HL HE2") as "#H62".
  { solve_lft_incl. }
  iPoseProof (Inherit_mono [κ6] [κ2] with "[] H30") as "H30".
  { rewrite /lft_intersect_list /= !right_id. done. }
  iRename select (r' ◁ₗ[π, Owned] _ @ BlockedLtype _ κ2)%I into "Hnode".
  iRename select (Obs x' _)%I into "Hobs".
  iAssert (r' ◁ₗ[π, Owned] #((locs !! 0%nat, None, PlaceGhost γ3)) @
    BlockedLtype (Node_inv_t T_rt -[] -[T_ty]) κ2)%I
    with "[Hnode H30]" as "Hnode".
    { iApply (blocked_ltype_owned_transport with "[] H30 Hnode").
      iIntros (old node_v) "Hrel Hold Hv".
      iEval (rewrite /place_rfn_interp_owned) in "Hold".
      iDestruct (gvar_pobs_agree_2 with "Hobs Hold") as %Heq. subst old.
     iPoseProof (push_front_Node_reborrow with "Hrel Hv") as "Hv".
     iModIntro. iExists _. iSplit; first done.
     iFrame. }
  iModIntro. iExists _. iFrame "HL".
  rep liRStep.
  liInst Hevar_self
    (PlaceGhost (rt := T_rt) γ3 :: ((PlaceIn ∘ RT_xrt T_rt) <$> self)).
  liInst Hevar_a a.
  liInst Hevar_locs (r' :: locs).
  liInst Hevar_x r'.
  1: rep <-! <3000 liRStep.
  liShow.
  iEval (rewrite LL_cons /LL_item). 
  rep liRStep.
  liShow.
  iApply prove_with_subtype_default.
  iRename select (LL_segment _ _ _ _ _ _)%I into "Helems".
  iSplitL "Helems".
  { rewrite list_fmap_compose.
    rewrite (simplify_use_struct_layout_alg' _ _ Hnode_layout). done. }
  1: rep <-! <3000 liRStep.

  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - congruence.
Qed.
End proof.
