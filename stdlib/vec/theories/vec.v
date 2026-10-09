From refinedrust Require Import typing.

#[universes(polymorphic)]
Definition extract_val {rt : RT} (r : place_rfn rt) := if r is #r then Some r else None.

Section project_vec_els.
  Context {rt : RT}.
  Set Universe Polymorphism.

  Definition project_vec_els (len : nat) (els : list (place_rfn (option (place_rfn rt))))
    : list (place_rfn rt) :=
    (λ x, default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)) <$> (take len els).

  Lemma project_vec_els_lookup_Some len i els x :
    project_vec_els len els !! i = Some x →
    ∃ x', els !! i = Some x' ∧ x = default (👻 inhabitant) (extract_val x' ≫= id) ∧ (i < len)%nat. 
  Proof.
    rewrite /project_vec_els.
    rewrite list_lookup_fmap_Some.
    intros (x' & Heq & Hlook).
    apply lookup_take_Some in Hlook as (Hlook & ?).
    eauto.
  Qed.

  Lemma project_vec_els_length len els :
    length (project_vec_els len els) = (len `min` length els)%nat.
  Proof. by rewrite /project_vec_els length_fmap length_take. Qed.

  Global Instance is_xrfn_vec_hint (els : list (place_rfn (option (place_rfn rt)))) (xr : list (RT_xt rt)) len cap : 
    TCDone (∀ i : nat, (0 <= i < len)%nat → els !! i = Some (# Some ((PlaceIn ∘ RT_xrt rt <$> xr) !!! i))) →
    TCDone (∀ i : nat, (len <= i < cap)%nat → els !! i = Some (# None)) →
    TCDone (length els = cap) →
    TCDone ((PlaceIn ∘ RT_xrt rt <$> xr) = project_vec_els len els) →
    IsXrfn els. 
  Proof.
    unfold TCDone.
    intros Hlook1 Hlook2 Hlen Hx.
    econstructor.
    apply is_xrfn_list_iff.
    apply Forall_forall.
    intros x (i & Hlook)%list_elem_of_lookup_1.
    have Hiels : (i < length els)%nat by apply lookup_lt_Some in Hlook.
    destruct (decide (i < len)) as [Hi | Hi].
    - opose proof (Hlook1 i _) as Hlook'; first lia.
      rewrite Hlook in Hlook'.
      simplify_eq.
      have Hixr : (i < length ((PlaceIn ∘ RT_xrt rt) <$> xr))%nat.
      { rewrite Hx project_vec_els_length. lia. }
      rewrite length_fmap in Hixr.
      destruct (lookup_lt_is_Some_2 xr i Hixr) as (xri & Hxri).
      erewrite list_lookup_total_correct; last by rewrite list_lookup_fmap Hxri.
      apply is_xrfn_proof.
    - opose proof (Hlook2 i _) as Hlook'.
      { lia. }
      rewrite Hlook in Hlook'.
      simplify_eq.
      apply is_xrfn_proof.
  Qed.

End project_vec_els.

Section vec_array_canonicalizable.
  Context `{!typeGS Σ} {rt : RT}.

  Lemma vec_els_shape (xs : list (place_rfn rt)) len cap els :
    len = length xs → length els = cap →
    (∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))) →
    (∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)) →
    els = ((λ x, #(Some x)) <$> xs) ++ replicate (cap - len) (#None).
  Proof.
    intros -> Hlen Hinit Huninit. apply list_eq. intros i.
    destruct (decide (i < length xs)%nat).
    - destruct (lookup_lt_is_Some_2 xs i l) as [x Hx].
      have Hxt : xs !!! i = x by apply list_lookup_total_correct.
      rewrite lookup_app_l; last by rewrite length_fmap.
      rewrite list_lookup_fmap Hinit; last lia.
      by rewrite Hx Hxt.
    - rewrite lookup_app_r; last by rewrite length_fmap; lia.
      rewrite length_fmap.
      destruct (decide (i < cap)%nat).
      + rewrite lookup_replicate_2; last lia.
        rewrite Huninit; [done | lia].
      + rewrite lookup_ge_None_2; last by rewrite Hlen; lia.
        symmetry. apply lookup_ge_None_2. rewrite length_replicate. lia.
  Qed.

  Lemma vec_init_own_el_vals_to_xrfn (ty : type rt) F π
      (xs : list (place_rfn rt)) vs q :
    lftE ⊆ F → rrust_ctx -∗
    q.[lft_intersect_list (ty_lfts ty)] -∗
    ([∗ list] x; v ∈ xs; vs,
      array_own_el_val π (maybe_uninit ty) (#(Some x)) v) -∗
    logical_step F ((∃ xrs : list (RT_xt rt),
      [∗ list] xr; v ∈ xrs; vs,
        array_own_el_val π (maybe_uninit ty) (#(Some (#(RT_xrt rt xr)))) v) ∗
      q.[lft_intersect_list (ty_lfts ty)]).
  Proof.
    iIntros (HF) "#[LFT TIME] Htok Hown".
    rewrite big_sepL2_alt. iDestruct "Hown" as "(%Hlen & Hown)".
    iPoseProof (Fractional_split_big_sepL
      (λ q, q.[lft_intersect_list (ty_lfts ty)])%I (length xs) with "Htok") as
      "(%qs & %Hlen_qs & Htoks & Hclose_toks)".
    iAssert ([∗ list] i ↦ xv; q' ∈ zip xs vs; qs,
      logical_step F ((∃ xr : RT_xt rt,
        array_own_el_val π (maybe_uninit ty) (#(Some (#(RT_xrt rt xr)))) xv.2) ∗
        q'.[lft_intersect_list (ty_lfts ty)]))%I
      with "[Hown Htoks]" as "Hsteps".
    { iApply (big_sepL2_wand with "[Hown Htoks]").
      { iApply big_sepL2_sep_sepL_r; iFrame.
        iApply big_sepL2_const_sepL_l. iSplitR; last done.
        rewrite length_zip Hlen Nat.min_id Hlen_qs. done. }
      iApply big_sepL2_intro.
      { rewrite length_zip Hlen Nat.min_id Hlen_qs. done. }
      iModIntro. iIntros (i [x v] q' Hlook Hlookq) "(Hown & Htok)".
      rewrite /array_own_el_val.
      iDestruct "Hown" as "(%r' & Hrfn0 & Hmu)".
      iEval (simpl) in "Hrfn0". iDestruct "Hrfn0" as %<-.
      iEval (rewrite /ty_own_val /= maybe_uninit_own_val_unfold
        /maybe_uninit_own_val_def) in "Hmu".
      iDestruct "Hmu" as "(%r'' & Hrfn & Hown)".
      iPoseProof (ty_own_val_to_xrfn ty F π r'' MetaNone v q'
        with "[$LFT $TIME] Htok Hown") as "Hstep"; first done.
      iApply (logical_step_wand with "Hstep").
      iIntros "((%xr & Hown) & Htok)".
      iFrame "Htok". iExists xr. rewrite /array_own_el_val.
      iExists (Some (#(RT_xrt rt xr))). iSplit; first done.
      rewrite /ty_own_val /= maybe_uninit_own_val_unfold
        /maybe_uninit_own_val_def.
      iExists (RT_xrt rt xr). iFrame. done. }
    iPoseProof (logical_step_big_sepL2 with "Hsteps") as "Hsteps".
    iApply (logical_step_wand with "Hsteps"). iIntros "Hresults".
    iPoseProof (big_sepL2_sep_sepL_r with "Hresults") as "(Hown & Htoks)".
    iPoseProof ("Hclose_toks" with "Htoks") as "Htok".
    iPoseProof (big_sepL2_const_sepL_l with "Hown") as "(_ & Hown)".
    iPoseProof (big_sepL2_from_zip' xs vs _ Hlen with "Hown") as "Hown".
    iEval (simpl) in "Hown".
    iPoseProof (big_sepL2_elim_l with "Hown") as "Hown".
    iDestruct (big_sepL_exists_l with "Hown") as "(%xrs & Hown)".
    iFrame "Htok". iExists xrs. done.
  Qed.

  Lemma vec_array_to_xrfn (ty : type rt) F π xs len cap els l q :
    lftE ⊆ F → len = length xs → length els = cap → len ≤ cap →
    (∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))) →
    (∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)) →
    rrust_ctx -∗ q.[lft_intersect_list (ty_lfts ty)] -∗
    guarded true (l ◁ₗ[π, Owned] #els @ ◁ array_t cap (maybe_uninit ty)) -∗
    logical_step F (∃ xrs : list (RT_xt rt), ⌜length xrs = len⌝ ∗
      guarded true (l ◁ₗ[π, Owned]
        #(((λ xr, #(Some (#(RT_xrt rt xr)))) <$> xrs) ++ replicate (cap - len) (#None))
        @ ◁ array_t cap (maybe_uninit ty)) ∗
      q.[lft_intersect_list (ty_lfts ty)]).
  Proof.
    iIntros (HF Hlen Helslen' Hcap Hinit Huninit) "#CTX Htok Hg".
    rewrite /guarded /maybe_creds /have_creds /num_cred.
    iDestruct "Hg" as "((Hcreds & Hat) & Hl)".
    iDestruct "Hcreds" as "(Hc & Hcreds)".
    iApply fupd_logical_step.
    iApply (lc_fupd_add_later with "Hc"). iNext.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly0 & %Hst & %Hly & #Hsc & #Hlb & %ri & Hrfn & Hown)".
    iEval (simpl) in "Hrfn". iDestruct "Hrfn" as "<-".
    iMod (fupd_mask_mono with "Hown") as "(%w & Hl & Hown)"; first done.
    iEval (rewrite /ty_own_val /= array_t_own_val_unfold /array_t_own_val_def) in "Hown".
    iDestruct "Hown" as "(%ely & %Hm & %Helst & %Helsz & %Helslen & %Hwly & Hown)".
    pose proof (vec_els_shape xs len cap els Hlen Helslen Hinit Huninit) as Hels.
    iEval (rewrite Hels) in "Hown".
    iDestruct (big_sepL2_app_inv_l with "Hown") as
      "(%vs1 & %vs2 & %Hvs & Hinitown & Hnoneown)".
    iEval (rewrite big_sepL2_fmap_l) in "Hinitown".
    iPoseProof (vec_init_own_el_vals_to_xrfn ty F π xs vs1 q
      with "CTX Htok Hinitown") as "Hstep"; first done.
    iModIntro. iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_tr with "Hat").
    iIntros "Hat Hnewcreds". iModIntro.
    iIntros "((%xrs & Hinitown) & Htok)".
    iPoseProof (big_sepL2_length with "Hinitown") as "%Hxrslen".
    iPoseProof (big_sepL2_length with "Hnoneown") as "%Hnonelen".
    have Hvslen : length vs1 + length vs2 = cap.
    { have H := f_equal length Hvs.
      rewrite length_reshape length_replicate length_app in H. lia. }
    have Hxrs : length xrs = len.
    { rewrite length_replicate in Hnonelen. lia. }
    iModIntro. iExists xrs. iFrame "Htok". iSplit; first done.
    iSplitL "Hnewcreds Hat".
    { iFrame. iApply tr_weaken; last done.
      simpl. unfold num_laters_per_step. lia. }
    iNext. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly0. iFrame "#%".
    iExists (((λ xr, #(Some (#(RT_xrt rt xr)))) <$> xrs) ++ replicate (cap - len) (#None)).
    iSplit; first done. iModIntro. iExists w. iFrame "Hl".
    rewrite /ty_own_val /= array_t_own_val_unfold /array_t_own_val_def.
    iExists ely. repeat iSplit; try iPureIntro; try done.
    { rewrite length_app length_fmap length_replicate. lia. }
    rewrite Hvs.
    iAssert ([∗ list] r; v ∈
      (λ xr, #(Some (#(RT_xrt rt xr)))) <$> xrs; vs1,
      array_own_el_val π (maybe_uninit ty) r v)%I with "[Hinitown]" as "Hinitown'".
    { rewrite big_sepL2_fmap_l. done. }
    iApply (big_sepL2_app with "Hinitown' Hnoneown").
  Qed.

  Definition vec_inv (π : thread_id) (ty : type rt)
      (inner : plist (RT_rt ∘ place_rfnRT) [prodRT locRT natRT; ZRT])
      (xs : list (place_rfn rt)) : iProp Σ :=
    ∃ (cap : nat) (l : loc) (len : nat)
      (els : list (place_rfn (option (place_rfn rt)))),
      ⌜inner = -[#(l, cap); #(Z.of_nat len)]⌝ ∗
      guarded true (l ◁ₗ[π, Owned] #els @ ◁ array_t cap (maybe_uninit ty)) ∗
      ⌜xs = project_vec_els len els⌝ ∗
      ⌜∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))⌝ ∗
      ⌜∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)⌝ ∗
      ⌜length els = cap⌝ ∗ ⌜len = length xs⌝ ∗ ⌜len ≤ cap⌝ ∗
      ⌜len ≤ MaxInt usize⌝ ∗
      ⌜if decide (size_of_st (ty_syn_type ty MetaNone) = 0%nat)
        then cap = Z.to_nat (MaxInt USize)
        else size_of_array_in_bytes (ty_syn_type ty MetaNone) cap ≤ MaxInt ISize⌝ ∗
      True.

  Global Instance canonicalizable_vec (π : thread_id) (ty : type rt)
      (repr_ty : type (plistRT [prodRT locRT natRT; ZRT]))
      (inner : plist (RT_rt ∘ place_rfnRT) [prodRT locRT natRT; ZRT])
      (xs : list (place_rfn rt)) :
    Canonicalizable π (ty_lfts ty) repr_ty inner xs
      (vec_inv π ty inner xs) (vec_inv π ty).
  Proof.
    constructor. intros F m v q HF.
    iIntros "#CTX Htok ((%cap & %l & %len & %els & %Hinner & Hg & %Hxs & %Hinit & %Huninit & %Helslen & %Hlen & %Hcap & %Hbound & %Hsize & _) & Hrepr)".
    rewrite lft_intersect_list_app -lft_tok_sep.
    iDestruct "Htok" as "(Htoki & Htokr)".
    iPoseProof (vec_array_to_xrfn ty F π xs len cap els l q
      with "CTX Htoki Hg") as "Hstep"; [done.. |].
    iApply (logical_step_wand with "Hstep").
    iIntros "(%xrs & %Hxrs & Hg & Htoki)".
    iSplitR "Htoki Htokr"; last by iFrame.
    iExists inner, xrs. iFrame "Hrepr".
    iExists cap, l, len,
      (((λ xr, #(Some (#(RT_xrt rt xr)))) <$> xrs) ++ replicate (cap - len) (#None)).
    iFrame "Hg". iSplit; first done.
    repeat iSplit; try iPureIntro; try done.
    - rewrite /project_vec_els take_app_le; last by rewrite length_fmap; lia.
      rewrite take_ge; last by rewrite length_fmap; lia.
      rewrite -list_fmap_compose. apply list_fmap_ext. intros xr Hin. done.
    - intros i Hi. rewrite lookup_app_l; last by rewrite length_fmap; lia.
      rewrite list_lookup_fmap.
      destruct (xrs !! i) as [xr |] eqn:Hxri; simpl; last first.
      { apply lookup_ge_None in Hxri. lia. }
      erewrite list_lookup_total_correct; last by rewrite list_lookup_fmap Hxri.
      done.
    - intros i Hi. rewrite lookup_app_r; last by rewrite length_fmap; lia.
      rewrite length_fmap Hxrs lookup_replicate_2; [done | lia].
    - rewrite length_app length_fmap length_replicate. lia.
    - by rewrite length_fmap Hxrs.
  Qed.

  Global Program Instance shareable_vec (π : thread_id) (κ : lft) (ty : type rt)
      (inner : plist (RT_rt ∘ place_rfnRT) [prodRT locRT natRT; ZRT])
      (xs : list (place_rfn rt)) :
    Shareable π κ (ty_lfts ty) xs (vec_inv π ty inner xs) := {|
      shareable_prop := (∃ (cap : nat) (l : loc) (len : nat)
        (els : list (place_rfn (option (place_rfn rt)))),
        ⌜inner = -[#(l, cap); #(Z.of_nat len)]⌝ ∗
        guarded false (l ◁ₗ[π, Shared κ] #els @ ◁ array_t cap (maybe_uninit ty)) ∗
        ⌜xs = project_vec_els len els⌝ ∗
        ⌜∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))⌝ ∗
        ⌜∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)⌝ ∗
        ⌜length els = cap⌝ ∗ ⌜len = length xs⌝ ∗ ⌜len ≤ cap⌝ ∗
        ⌜len ≤ MaxInt usize⌝ ∗
        ⌜if decide (size_of_st (ty_syn_type ty MetaNone) = 0%nat)
          then cap = Z.to_nat (MaxInt USize)
          else size_of_array_in_bytes (ty_syn_type ty MetaNone) cap ≤ MaxInt ISize⌝ ∗
        True)%I
    |}.
  Next Obligation.
    intros π κ ty inner xs Hxsxr F G q HF.
    iIntros "#CTX Hna Htok1 Htok2 Hb Hcont".
    iPoseProof "CTX" as "#(LFT & LLCTX)".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as "(%cap & Hb)"; first done.
    iMod (bor_exists with "LFT Hb") as "(%l & Hb)"; first done.
    iMod (bor_exists with "LFT Hb") as "(%len & Hb)"; first done.
    iMod (bor_exists with "LFT Hb") as "(%els & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Heq & Hb)"; first done.
    iMod (bor_persistent with "LFT Heq Htok1") as "(>%Hinner & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hg & Hrest)"; first done.
    iMod (bor_persistent with "LFT Hrest Htok1") as "(>Hrest & Htok1)"; first done.
    iDestruct "Hrest" as "(%Hxs & %Hinit & %Huninit & %Helslen & %Hlen & %Hcap & %Hbound & %Hsize & _)".
    destruct Hxsxr as (xr & Hxsxr). subst xs.
    have Helsxr : is_xrfn els by apply is_xrfn_proof.
    have Helsplacexr : is_xrfn (#els).
    { destruct Helsxr as (elsxr & ->). eexists elsxr. done. }
    iPoseProof (ltype_own_ofty_share' π F κ (ty_lfts ty) q l
      (array_t cap (maybe_uninit ty)) (#els)
      with "CTX Hna Htok1 Htok2 Hg") as "Hstep".
    { done. }
    { exact Helsplacexr. }
    { repeat rewrite ty_lfts_unfold /=. set_solver. }
    iApply (logical_step_compose with "Hcont").
    iApply (logical_step_wand with "Hstep").
    iModIntro. iIntros "(Hg & Htok1 & Htok2) Hclose".
    iApply "Hclose". iFrame "Htok1 Htok2".
    iExists cap, l, len, els. iFrame "Hg". done.
  Qed.
End vec_array_canonicalizable.

Global Hint Extern 10 (Canonicalizable _ _ _ _ _ _ _) =>
  apply canonicalizable_vec : typeclass_instances.

Global Hint Extern 10 (Shareable _ _ _ _ _) =>
  apply shareable_vec : typeclass_instances.
