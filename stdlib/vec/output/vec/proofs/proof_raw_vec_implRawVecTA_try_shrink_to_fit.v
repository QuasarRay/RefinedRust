From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecTA_try_shrink_to_fit.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecTA_try_shrink_to_fit_proof (π : thread_id) :
  raw_vec_implRawVecTA_try_shrink_to_fit_lemma π.
Proof.
  raw_vec_implRawVecTA_try_shrink_to_fit_prelude.

  rep 3000 liRStep.
  liShow. iIntros "Hfree". liShow.
  iMatchHyp ltac:(fun H P => lazymatch P with context [array_t] => iRename H into "Harray" end).
  rename select (length self1 = _) into Heffective.
  change (length self1 = raw_vec_effective_capacity (ly_size T_st_ly) stored_cap) in Heffective.
  have Hsize : (ly_size T_st_ly * stored_cap ≤ MaxInt ISize)%Z.
  { rename select (if decide (ly_size T_st_ly = 0%nat) then _ else _) into Hphysical.
    destruct (decide (ly_size T_st_ly = 0%nat)) as [Hzero | Hnonzero].
    - rewrite Hzero. pose proof (MaxInt_ge_127 ISize). lia.
    - move: Hphysical. rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /= Nat2Z.inj_mul. done. }
  iPoseProof (ltype_own_has_layout with "Harray") as "(%array_ly & %Harrayalg & %Halign)".
  apply syn_type_has_layout_array_inv in Harrayalg as (ly & Hly & -> & _).
  apply syn_type_has_layout_untyped_inv in Hly.
  have Hlyeq : ly = T_st_ly by eapply syn_type_has_layout_inj; [exact Hly | exact T_st_alg].
  subst ly. rewrite /has_layout_loc ly_align_mk_array_layout in Halign.
  iEval (rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /= Heffective) in "Hfree".
  iEval (rewrite Heffective) in "Harray".
  iPoseProof (raw_vec_array_storage_shrink T_ty with "Hfree Harray") as "Hupdate";
    [exact T_st_alg | exact Hsize | done | done |].
  rewrite {1}/introduce_with_hooks.
  iIntros (F HF) "#Hctx #HE HL _".
  iMod (fupd_mask_mono lftE F _ HF with "Hupdate") as (old_bytes) "(%Hlength & Hstorage & Hrestore)".
  iModIntro. iExists [κ ⊑ₗ{0} [ulft_1]; ϝ ⊑ₗ{1} []]. iFrame "HL".
  liFromSyntaxGoal. rep 1000 liRStep. rep liRStep.
  liInst Hevar_x1 old_bytes.
  liShow. iApply prove_with_subtype_default. iSplitL "Hstorage".
  { iEval (rewrite raw_vec_layout_roundtrip; last (apply ly_align_in_usize; eapply use_layout_alg_align; exact T_st_alg)). done. }
  liFromSyntaxGoal. rep 30 liRStep. 1: rep liRStep.
  liShow. iIntros (returned_value [shrink_result new_ptr]).
  destruct shrink_result as [[]|err].
  - cbn. rewrite {1}/introduce_with_hooks.
    iIntros (F1 HF1) "#Hctx1 #HE1 HL1 Hpost".
    iDestruct "Hpost" as "(Hcred & Htime & Hna & _ & Hpost & Hval)".
    iDestruct "Hpost" as "(Hobs & Hstorage & _ & _)".
    have Hrequest : (Z.to_nat cap ≤ raw_vec_effective_capacity (ly_size T_st_ly) stored_cap)%nat by lia.
    opose proof* (raw_vec_shrink_capacity (ly_size T_st_ly) stored_cap (Z.to_nat cap)) as (Hsmaller & Hcap & Hbytesize); first exact Hrequest.
    set (new_cap := if decide (ly_size T_st_ly * stored_cap = 0)%nat then stored_cap else Z.to_nat cap) in *.
    have Hnewsize : (ly_size T_st_ly * new_cap ≤ MaxInt ISize)%Z by nia.
    have Hmono : (raw_vec_effective_capacity (ly_size T_st_ly) new_cap ≤ raw_vec_effective_capacity (ly_size T_st_ly) stored_cap)%nat.
    { rewrite Hcap. unfold raw_vec_effective_capacity in Hrequest |- *.
      destruct (decide (ly_size T_st_ly = 0%nat)); simpl in *; lia. }
    iEval (rewrite raw_vec_layout_roundtrip; last (apply ly_align_in_usize; eapply use_layout_alg_align; exact T_st_alg)) in "Hstorage".
    iPoseProof ("Hrestore" $! new_ptr new_cap with "[] [] [Hstorage]") as "Hupdate"; [done | done | |].
    { by rewrite Hbytesize. }
    iMod (fupd_mask_mono lftE F1 _ HF1 with "Hupdate") as "[(%Hnewnonzero & %Hnewalign) [Hfree Harray]]".
    iModIntro. iExists [κ ⊑ₗ{0} [ulft_1]; ϝ ⊑ₗ{1} []]. iFrame "HL1".
    liFromSyntaxGoal. rep 1000 liRStep.
    rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /=.
    liShow. iApply prove_with_subtype_default. iFrame "Hfree".
    liFromSyntaxGoal. rep 1000 liRStep.
  - cbn. rewrite {1}/introduce_with_hooks.
    iIntros (F1 HF1) "#Hctx1 #HE1 HL1 Hpost".
    iDestruct "Hpost" as "(Hcred & Htime & Hna & _ & Hpost & Hval)".
    iDestruct "Hpost" as "(Hobs & _ & Hstorage & %Herror)".
    iEval (rewrite raw_vec_layout_roundtrip; last (apply ly_align_in_usize; eapply use_layout_alg_align; exact T_st_alg)) in "Hstorage".
    iPoseProof ("Hrestore" $! self stored_cap) as "Hupdate".
    iEval (rewrite -Hlength firstn_all) in "Hupdate".
    iSpecialize ("Hupdate" with "[] [] Hstorage"); [done | done |].
    iMod (fupd_mask_mono lftE F1 _ HF1 with "Hupdate") as "[(%Hnewnonzero & %Hnewalign) [Hfree Harray]]".
    iEval (rewrite -Heffective /= -!fmap_take firstn_all) in "Harray".
    iModIntro. iExists [κ ⊑ₗ{0} [ulft_1]; ϝ ⊑ₗ{1} []]. iFrame "HL1".
    liFromSyntaxGoal. rep 1000 liRStep.
    rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /= Heffective.
    liShow. iApply prove_with_subtype_default. iFrame "Hfree".
    liFromSyntaxGoal. rep 1000 liRStep.
  Unshelve.
  1-16: first [exact (self : loc) | sidecond_solver].
  Unshelve.
  1-8: sidecond_hammer.
  Unshelve.
  + by rewrite Hcap.
  + destruct Herror as (layout & extra & Herr & Hlayout & Hextra & Hpositive & Helem_nonzero).
    unfold raw_vec_effective_capacity in Heffective.
    rewrite decide_False in Heffective; done.
Qed.
End proof.
