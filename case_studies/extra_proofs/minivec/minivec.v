From radium Require Import lang notation.
From refinedrust Require Import typing.

Lemma list_lookup_insert_Some' {A} (l : list A) i x j y :
  <[i:=x]>l !! j = Some y ↔
    (i = j → x = y ∧ (j < length l)%nat) ∧ (i ≠ j → l !! j = Some y).
Proof. rewrite list_lookup_insert_Some. destruct (decide (i = j)); naive_solver. Qed.

Lemma list_eq_singleton {A} (l : list A) x:
  l = [x] ↔ (length l ≤ 1)%nat ∧ l !! 0%nat = Some x.
Proof.
  split.
  - move => ->. naive_solver.
  - move => [??]. destruct l as [|? [|]]; naive_solver lia.
Qed.

Global Instance simpl_lookup_total_insert_eq {A} `{!Inhabited A} (l : list A) i j x x' `{!CanSolve (i = j)} `{!CanSolve (j < length l)%nat}:
  SimplBothRel (=) (<[i := x']> l !!! j) (x) (x = x').
Proof.
  unfold SimplBothRel, CanSolve in *; subst.
  rewrite list_lookup_total_insert_eq; naive_solver.
Qed.

#[universes(polymorphic)]
Definition extract_val {rt : RT} (r : place_rfn rt) := if r is #r then Some r else None.

Section project_vec_els.
  Context {rt : RT}.
  Set Universe Polymorphism.

  Global Instance is_xrfn_minivec_nested_fmap (xr : list (RT_xt rt)) :
    IsXrfn (<#> <$#@{rt}> xr).
  Proof.
    constructor. exists xr. rewrite -list_fmap_compose.
    apply list_fmap_ext. intros. done.
  Qed.

  Global Instance is_xrfn_minivec_nested_fmap_lookup_total
      (xr : list (RT_xt rt)) i `{!CanSolve (i < length xr)%nat} :
    IsXrfn ((<#> <$#@{rt}> xr) !!! i).
  Proof.
    unfold CanSolve in *.
    destruct (lookup_lt_is_Some_2 xr i ltac:(lia)) as (x & Hx).
    constructor. exists x.
    erewrite list_lookup_total_correct; last by rewrite !list_lookup_fmap Hx.
    done.
  Qed.

  Definition project_vec_els (len : nat) (els : list (place_rfn (option (place_rfn rt))))
    : list (place_rfn rt) :=
    (λ x, default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)) <$> (take len els).

  Lemma project_vec_els_length len els :
    length (project_vec_els len els) = (len `min` length els)%nat.
  Proof. by rewrite /project_vec_els length_fmap length_take. Qed.

  Lemma project_vec_els_insert_lt (len : nat) (i : nat) x els:
    (i < len)%nat →
    project_vec_els len (<[i:=x]> els) =
       <[i:=default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)]>
         (project_vec_els len els).
  Proof.
    rewrite {1}/project_vec_els => ?. by rewrite take_insert_lt // list_fmap_insert.
  Qed.
  Lemma project_vec_els_insert_ge (len : nat) (i : nat) x els:
    (len ≤ i)%nat →
    project_vec_els len (<[i:=x]> els) = project_vec_els len els.
  Proof. rewrite {1}/project_vec_els => ?. by rewrite take_insert_ge. Qed.

  Lemma project_vec_els_lookup_mono (len : nat) (i : nat) els len' els':
    (i < len `min` len')%nat →
    els !! i = els' !! i →
    project_vec_els len els !! i = project_vec_els len' els' !! i.
  Proof.
    move => ? Hels. rewrite /project_vec_els !list_lookup_fmap. f_equal.
    rewrite !lookup_take_lt //; lia.
  Qed.

  Lemma project_vec_els_take len els len':
    take len' (project_vec_els len els) = project_vec_els (len' `min` len) els.
  Proof. rewrite /project_vec_els. by rewrite !fmap_take take_take. Qed.
  Lemma project_vec_els_take_r len els :
    project_vec_els len els = project_vec_els len (take len els).
  Proof. rewrite /project_vec_els. f_equal. rewrite take_take. f_equal. lia. Qed.
  Lemma project_vec_els_drop len els len':
    drop len' (project_vec_els len els) = project_vec_els (len - len') (drop len' els).
  Proof. rewrite /project_vec_els. by rewrite -!fmap_drop skipn_firstn_comm. Qed.

  Lemma project_vec_els_lookup (len i : nat) els x :
    (i < len)%nat →
    els !! i = Some (#(Some x)) →
    project_vec_els len els !! i = Some x.
  Proof.
    intros Hi Hlook. rewrite /project_vec_els.
    simpl.
    rewrite list_lookup_fmap.
    rewrite lookup_take_lt; last lia.
    rewrite Hlook. done.
  Qed.

  Lemma project_vec_els_length' xs x2 len :
    <#> <$#@{rt}> xs = project_vec_els len x2 → length xs ≤ min len (length x2).
  Proof.
    intros Ha.
    assert (length (<#> <$#> xs) = length (project_vec_els len x2)) as Hlen.
    { rewrite Ha. done. }
    rewrite length_map project_vec_els_length in Hlen.
    rewrite length_map in Hlen.
    lia.
  Qed.

  Global Instance is_xrfn_minivec_vec_hint
      (els : list (place_rfn (option (place_rfn rt))))
      (xr : list (RT_xt rt)) len cap:
    TCDone (∀ i : nat, (0 ≤ i < len)%nat →
      els !! i = Some (#(Some ((PlaceIn ∘ RT_xrt rt <$> xr) !!! i)))) →
    TCDone (∀ i : nat, (len ≤ i < cap)%nat → els !! i = Some (#None)) →
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
    - opose proof (Hlook2 i _) as Hlook'; first lia.
      rewrite Hlook in Hlook'.
      simplify_eq.
      apply is_xrfn_proof.
  Qed.
End project_vec_els.

Global Typeclasses Opaque project_vec_els.
Global Opaque project_vec_els.

Global Hint Rewrite @project_vec_els_length : lithium_rewrite.
Global Hint Rewrite @list_fmap_compose : lithium_rewrite.

Section vec_canonicalizable.
  Context `{!typeGS Σ} {rt : RT}.

  Local Transparent project_vec_els.

  Lemma vec_els_shape (xs : list (place_rfn rt)) len cap els :
    len = length xs →
    length els = cap →
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
    lftE ⊆ F →
    rrust_ctx -∗
    q.[lft_intersect_list (ty_lfts ty)] -∗
    ([∗ list] x; v ∈ xs; vs,
      array_own_el_val π (maybe_uninit ty) (#(Some x)) v) -∗
    logical_step F (
      (∃ xrs : list (RT_xt rt),
        [∗ list] xr; v ∈ xrs; vs,
          array_own_el_val π (maybe_uninit ty)
            (#(Some (#(RT_xrt rt xr)))) v) ∗
      q.[lft_intersect_list (ty_lfts ty)]).
  Proof.
    iIntros (HF) "#[LFT TIME] Htok Hown".
    rewrite big_sepL2_alt. iDestruct "Hown" as "(%Hlen & Hown)".
    iPoseProof (Fractional_split_big_sepL
      (λ q, q.[lft_intersect_list (ty_lfts ty)])%I (length xs) with "Htok") as
      "(%qs & %Hlen_qs & Htoks & Hclose_toks)".
    iAssert ([∗ list] i ↦ xv; q' ∈ zip xs vs; qs,
      logical_step F
        ((∃ xr : RT_xt rt,
          array_own_el_val π (maybe_uninit ty)
            (#(Some (#(RT_xrt rt xr)))) xv.2) ∗
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
    iApply (logical_step_wand with "Hsteps").
    iIntros "Hresults".
    iPoseProof (big_sepL2_sep_sepL_r with "Hresults") as "(Hown & Htoks)".
    iPoseProof ("Hclose_toks" with "Htoks") as "Htok".
    iPoseProof (big_sepL2_const_sepL_l with "Hown") as "(_ & Hown)".
    iPoseProof (big_sepL2_from_zip' xs vs _ Hlen with "Hown") as "Hown".
    iEval (simpl) in "Hown".
    iPoseProof (big_sepL2_elim_l with "Hown") as "Hown".
    iDestruct (big_sepL_exists_l with "Hown") as "(%xrs & Hown)".
    iFrame "Htok". iExists xrs. done.
  Qed.

  Global Instance canonicalizable_minivec_vec
      (π : thread_id) (ty : type rt)
      (repr_ty : type (plistRT [prodRT locRT natRT; ZRT]))
      (inner : plist (RT_rt ∘ place_rfnRT) [prodRT locRT natRT; ZRT])
      (xs : list (place_rfn rt)) :
    Canonicalizable π (ty_lfts ty) repr_ty inner xs
      (∃ (cap : nat) (l : loc) (len : nat)
          (els : list (place_rfn (option (place_rfn rt)))),
        ⌜inner = -[#(l, cap); #(Z.of_nat len)]⌝ ∗
        guarded true
          (l ◁ₗ[π, Owned] #(els) @ ◁ array_t cap (maybe_uninit ty)) ∗
        ⌜xs = project_vec_els len els⌝ ∗
        ⌜∀ i, (0 ≤ i < len)%nat →
          els !! i = Some (#(Some (xs !!! i)))⌝ ∗
        ⌜∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)⌝ ∗
        ⌜length els = cap⌝ ∗
        ⌜len = length xs⌝ ∗ ⌜len ≤ cap⌝ ∗
        ⌜if decide (size_of_st (ty_syn_type ty MetaNone) = 0%nat)
          then cap = Z.to_nat (MaxInt USize)
          else size_of_array_in_bytes (ty_syn_type ty MetaNone) cap ≤ MaxInt ISize⌝ ∗
        True)%I
      (λ inner' xs', ∃ (cap : nat) (l : loc) (len : nat)
          (els : list (place_rfn (option (place_rfn rt)))),
        ⌜inner' = -[#(l, cap); #(Z.of_nat len)]⌝ ∗
        guarded true
          (l ◁ₗ[π, Owned] #(els) @ ◁ array_t cap (maybe_uninit ty)) ∗
        ⌜xs' = project_vec_els len els⌝ ∗
        ⌜∀ i, (0 ≤ i < len)%nat →
          els !! i = Some (#(Some (xs' !!! i)))⌝ ∗
        ⌜∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)⌝ ∗
        ⌜length els = cap⌝ ∗
        ⌜len = length xs'⌝ ∗ ⌜len ≤ cap⌝ ∗
        ⌜if decide (size_of_st (ty_syn_type ty MetaNone) = 0%nat)
          then cap = Z.to_nat (MaxInt USize)
          else size_of_array_in_bytes (ty_syn_type ty MetaNone) cap ≤ MaxInt ISize⌝ ∗
        True)%I.
  Proof.
    constructor. intros F m v q HF.
    iIntros "#CTX Htok ((%cap & %l & %len & %els & %Hinner & Hg & %Hxs & %Hinit & %Huninit & %Helslen' & %Hlen & %Hcap & %Hsize & _) & Hrepr)".
    rewrite lft_intersect_list_app -lft_tok_sep.
    iDestruct "Htok" as "(Htoki & Htokr)".
    rewrite /guarded /maybe_creds /have_creds /num_cred.
    iDestruct "Hg" as "((Hcreds & Hat) & Hl)".
    iDestruct "Hcreds" as "(Hc & Hcreds)".
    iApply fupd_logical_step.
    iApply (lc_fupd_add_later with "Hc"). iNext.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as
      "(%ly0 & %Hst & %Hly & #Hsc & #Hlb & %ri & Hrfn & Hown)".
    iEval (simpl) in "Hrfn". iDestruct "Hrfn" as "<-".
    iMod (fupd_mask_mono with "Hown") as "(%w & Hl & Hown)"; first done.
    iEval (rewrite /ty_own_val /= array_t_own_val_unfold
      /array_t_own_val_def) in "Hown".
    iDestruct "Hown" as
      "(%ely & %Hm & %Helst & %Helsz & %Helslen & %Hwly & Hown)".
    pose proof (vec_els_shape xs len cap els Hlen Helslen Hinit Huninit) as Hels.
    iEval (rewrite Hels) in "Hown".
    iDestruct (big_sepL2_app_inv_l with "Hown") as
      "(%vs1 & %vs2 & %Hvs & Hinitown & Hnoneown)".
    iEval (rewrite big_sepL2_fmap_l) in "Hinitown".
    iPoseProof (vec_init_own_el_vals_to_xrfn ty F π xs vs1 q
      with "CTX Htoki Hinitown") as "Hstep"; first done.
    iModIntro. iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_tr with "Hat").
    iIntros "Hat Hnewcreds". iModIntro.
    iIntros "((%xrs & Hinitown) & Htoki)".
    iPoseProof (big_sepL2_length with "Hinitown") as "%Hxrslen".
    iPoseProof (big_sepL2_length with "Hnoneown") as "%Hnonelen".
    have Hvslen : length vs1 + length vs2 = cap.
    { have H := f_equal length Hvs.
      rewrite length_reshape length_replicate length_app in H. lia. }
    have Hxrs : length xrs = len.
    { rewrite length_replicate in Hnonelen. lia. }
    set (xs' := (λ xr, #(RT_xrt rt xr)) <$> xrs).
    set (els' := ((λ xr, #(Some (#(RT_xrt rt xr)))) <$> xrs) ++
      replicate (cap - len) (#None)).
    iModIntro.
    iSplitR "Htoki Htokr".
    - subst inner.
      iExists (-[#(l, cap); #(Z.of_nat len)]), xrs. simpl.
      iSplitR "Hrepr"; last done.
      iExists cap, l, len, els'. iSplit; first done.
      iSplitL "Hnewcreds Hat Hl Hinitown Hnoneown".
      { rewrite /guarded /maybe_creds /have_creds /num_cred.
        iSplitL "Hnewcreds Hat".
        { iFrame. iApply tr_weaken; last done.
          simpl. unfold num_laters_per_step. lia. }
        iNext.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly0. iFrame "#%". iExists els'. iSplit; first done.
        iModIntro. iExists w. iFrame "Hl".
        rewrite /ty_own_val /= array_t_own_val_unfold /array_t_own_val_def.
        iExists ely. repeat iSplit; try iPureIntro; try done.
        { subst els'. rewrite length_app length_fmap length_replicate. lia. }
        subst els' xs'. rewrite Hvs.
        iAssert ([∗ list] r; v ∈
            (λ xr, #(Some (#(RT_xrt rt xr)))) <$> xrs; vs1,
            array_own_el_val π (maybe_uninit ty) r v)%I
          with "[Hinitown]" as "Hinitown'".
        { rewrite big_sepL2_fmap_l. done. }
        iApply (big_sepL2_app with "Hinitown' Hnoneown"). }
      subst xs' els'. repeat iSplit; try iPureIntro; try done.
      + rewrite /project_vec_els take_app_le; last by rewrite length_fmap; lia.
        rewrite take_ge; last by rewrite length_fmap; lia.
        rewrite -list_fmap_compose. apply list_fmap_ext. intros xr Hin. done.
      + intros i Hi. rewrite lookup_app_l; last by rewrite length_fmap; lia.
        rewrite list_lookup_fmap.
        destruct (xrs !! i) as [xr |] eqn:Hxri; simpl; last first.
        { apply lookup_ge_None in Hxri. lia. }
        erewrite list_lookup_total_correct; last by rewrite list_lookup_fmap Hxri.
        done.
      + intros i Hi. rewrite lookup_app_r; last by rewrite length_fmap; lia.
        rewrite length_fmap Hxrs lookup_replicate_2; [done | lia].
      + rewrite length_app length_fmap length_replicate. lia.
      + by rewrite length_fmap Hxrs.
    - iFrame.
  Qed.

End vec_canonicalizable.

Global Hint Extern 10 (Canonicalizable _ _ _ _ _ _ _) =>
  apply canonicalizable_minivec_vec : typeclass_instances.
