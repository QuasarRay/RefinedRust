From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecTA_reserve_exact.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecTA_reserve_exact_proof (π : thread_id) :
  raw_vec_implRawVecTA_reserve_exact_lemma π.
Proof.
  raw_vec_implRawVecTA_reserve_exact_prelude.

  1: rep 3000 liRStep.
  1: liShow.
  1: iIntros "Hfree".
  1: liShow.
  1: iMatchHyp ltac:(fun H P => lazymatch P with context [array_t] => iRename H into "Harray" end).
  1: rename select (length self1 = _) into Heffective.
  1: change (length self1 = raw_vec_effective_capacity (ly_size T_st_ly) stored_cap) in Heffective.
  1: have Hsize : (ly_size T_st_ly * stored_cap ≤ MaxInt ISize)%Z.
  { rename select (if decide (ly_size T_st_ly = 0%nat) then _ else _) into Hphysical.
    destruct (decide (ly_size T_st_ly = 0%nat)) as [Hzero | Hnonzero].
    - rewrite Hzero. pose proof (MaxInt_ge_127 ISize). lia.
    - move: Hphysical. rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /= Nat2Z.inj_mul. done. }
  1: iPoseProof (ltype_own_has_layout with "Harray") as "(%array_ly & %Harrayalg & %Halign)".
  1: apply syn_type_has_layout_array_inv in Harrayalg as (ly & Hly & -> & _).
  1: apply syn_type_has_layout_untyped_inv in Hly.
  1: have Hlyeq : ly = T_st_ly by eapply syn_type_has_layout_inj; [exact Hly | exact T_st_alg].
  1: subst ly.
  1: rewrite /has_layout_loc ly_align_mk_array_layout in Halign.
  1: iEval (rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /= Heffective) in "Hfree".
  1: iEval (rewrite Heffective) in "Harray".
  1: iPoseProof (raw_vec_array_storage T_ty with "Hfree Harray") as "Hupdate";
    [exact T_st_alg | exact Hsize | done | done |].
  1: rewrite {1}/introduce_with_hooks.
  1: iIntros (F HF) "#Hctx #HE HL _".
  1: iMod (fupd_mask_mono lftE F _ HF with "Hupdate") as (old_bytes) "[Hstorage Hrestore]".
  1: iModIntro.
  1: iExists [κ ⊑ₗ{0} [ulft_1]; ϝ ⊑ₗ{1} []].
  1: iFrame "HL".
  1: liFromSyntaxGoal.
  1: rep 1000 liRStep.
  1: rep liRStep.
  1: liInst Hevar_x1 old_bytes.
  1: liShow.
  1: iApply prove_with_subtype_default.
  1: iSplitL "Hstorage".
  { iEval (rewrite raw_vec_layout_roundtrip; last (apply ly_align_in_usize; eapply use_layout_alg_align; exact T_st_alg)). done. }
  1: liFromSyntaxGoal.
  1: rep 30 liRStep.
  - rep 5 liRStep. liShow.
    rewrite {1}/introduce_with_hooks.
    iIntros (Hunwind F1 HF1) "#Hctx1 #HE1 HL1 Hpost".
    iDestruct "Hpost" as "(Hobs & Hstorage)".
    iEval (rewrite raw_vec_layout_roundtrip; last (apply ly_align_in_usize; eapply use_layout_alg_align; exact T_st_alg)) in "Hstorage".
    iPoseProof ("Hrestore" $! self stored_cap []) as "Hupdate".
    iEval (rewrite app_nil_r) in "Hupdate".
    iSpecialize ("Hupdate" with "[] [] Hstorage"); [done | done |].
    iMod (fupd_mask_mono lftE F1 _ HF1 with "Hupdate") as "[(%Hnewnonzero & %Hnewalign) [Hfree Harray]]".
    iModIntro. iExists [κ ⊑ₗ{0} [ulft_1]; ϝ ⊑ₗ{1} []]. iFrame "HL1".
    liFromSyntaxGoal. rep 1000 liRStep.
    rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /=.
    liShow. iApply prove_with_subtype_default. iFrame "Hfree".
    liFromSyntaxGoal. rep 1000 liRStep.
  - liShow.
    iIntros (returned_value [[[new_ptr new_cap] suffix] ret]).
    destruct ret.
    rewrite {1}/introduce_with_hooks.
    iIntros (F1 HF1) "#Hctx1 #HE1 HL1 Hpost".
    iDestruct "Hpost" as "(Hcred & Htime & Hna & _ & Hpost & Hval)".
    iDestruct "Hpost" as "(Hobs & Hstorage & %Hsuccess)".
    destruct Hsuccess as (Hsufficient & Hcap & Hnewsize).
    have Hmono : (raw_vec_effective_capacity (ly_size T_st_ly) stored_cap ≤ raw_vec_effective_capacity (ly_size T_st_ly) new_cap)%nat.
    { destruct (decide (len + additional ≤ Z.of_nat (raw_vec_effective_capacity (ly_size T_st_ly) stored_cap))) as [Hfits|Hgrow].
      - subst new_cap. done.
      - lia. }
    iEval (rewrite raw_vec_layout_roundtrip; last (apply ly_align_in_usize; eapply use_layout_alg_align; exact T_st_alg)) in "Hstorage".
    iPoseProof ("Hrestore" $! new_ptr new_cap suffix with "[] [] Hstorage") as "Hupdate"; [done | done |].
    iMod (fupd_mask_mono lftE F1 _ HF1 with "Hupdate") as "[(%Hnewnonzero & %Hnewalign) [Hfree Harray]]".
    iModIntro. iExists [κ ⊑ₗ{0} [ulft_1]; ϝ ⊑ₗ{1} []]. iFrame "HL1".
    liFromSyntaxGoal. rep 1000 liRStep.
    rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /=.
    liShow. iApply prove_with_subtype_default. iFrame "Hfree".
    liFromSyntaxGoal. rep 1000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  all: try solve [destruct Hunwind; done].
  all: try solve [
    destruct (decide (len + additional ≤ Z.of_nat (raw_vec_effective_capacity (ly_size T_st_ly) stored_cap))) as [Hfits|Hgrow]; simpl in *;
    [done | destruct (decide (ly_size T_st_ly = 0%nat)) as [Hzero|Hnonzero];
      [unfold raw_vec_effective_capacity in Hsufficient, Hgrow; rewrite Hzero /= in Hsufficient, Hgrow; lia | nia]]].
  all: try solve [rewrite fmap_replicate /= Heffective; done].
  all: try solve [rewrite Heffective;
    destruct (decide (len + additional ≤ Z.of_nat (raw_vec_effective_capacity (ly_size T_st_ly) stored_cap))) as [Hfits|Hgrow]; simpl in *;
    [done | unfold raw_vec_effective_capacity in Hsufficient, Hgrow |- *;
      destruct (decide (ly_size T_st_ly = 0%nat)); simpl in *; nia]].
  all: print_remaining_sidecond.
Qed.
End proof.
