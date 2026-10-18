From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecTA_grow_one.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecTA_grow_one_proof (π : thread_id) :
  raw_vec_implRawVecTA_grow_one_lemma π.
Proof.
  raw_vec_implRawVecTA_grow_one_prelude.

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
  iPoseProof (raw_vec_array_storage T_ty with "Hfree Harray") as "Hupdate";
    [exact T_st_alg | exact Hsize | done | done |].
  rewrite {1}/introduce_with_hooks.
  iIntros (F HF) "#Hctx #HE HL _".
  iMod (fupd_mask_mono lftE F _ HF with "Hupdate") as (old_bytes) "[Hstorage Hrestore]".
  iModIntro. iExists [κ ⊑ₗ{0} [ulft_1]; ϝ ⊑ₗ{1} []]. iFrame "HL".
  liFromSyntaxGoal. rep 1000 liRStep. rep liRStep.
  liInst Hevar_x1 old_bytes.
  liShow. iApply prove_with_subtype_default.
  iSplitL "Hstorage".
  { iEval (rewrite raw_vec_layout_roundtrip; last (apply ly_align_in_usize; eapply use_layout_alg_align; exact T_st_alg)). done. }
  liFromSyntaxGoal. rep 30 liRStep.
  { (* ZSTs and failed allocation preserve the original buffer on unwind. *)
    rep 5 liRStep. liShow. rewrite {1}/introduce_with_hooks.
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
  }
  { (* Successful growth appends only logically uninitialized elements. *)
    liShow. iIntros (returned_value [[new_ptr suffix] ret]).
    destruct ret. rewrite {1}/introduce_with_hooks.
    iIntros (F1 HF1) "#Hctx1 #HE1 HL1 Hpost".
    iDestruct "Hpost" as "(Hcred & Htime & Hna & _ & Hpost & Hval)".
    iDestruct "Hpost" as "(Hobs & Hstorage & %Hsuccess)".
    destruct Hsuccess as (Helem_nonzero & Hstrict & Hnewsize).
    set (new_cap := Z.to_nat (raw_vec_amortized_capacity (ly_size T_st_ly) stored_cap (Z.of_nat stored_cap + 1))).
    have Hmono : (raw_vec_effective_capacity (ly_size T_st_ly) stored_cap ≤ raw_vec_effective_capacity (ly_size T_st_ly) new_cap)%nat.
    { unfold raw_vec_effective_capacity. rewrite !decide_False; try done. unfold new_cap. lia. }
    iEval (rewrite raw_vec_layout_roundtrip; last (apply ly_align_in_usize; eapply use_layout_alg_align; exact T_st_alg)) in "Hstorage".
    iPoseProof ("Hrestore" $! new_ptr new_cap suffix with "[] [] Hstorage") as "Hupdate"; [done | done |].
    iMod (fupd_mask_mono lftE F1 _ HF1 with "Hupdate") as "[(%Hnewnonzero & %Hnewalign) [Hfree Harray]]".
    iModIntro. iExists [κ ⊑ₗ{0} [ulft_1]; ϝ ⊑ₗ{1} []]. iFrame "HL1".
    liFromSyntaxGoal. rep 1000 liRStep.
    rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /=.
    liShow. iApply prove_with_subtype_default. iFrame "Hfree".
    liFromSyntaxGoal. rep 1000 liRStep.
  }
  Unshelve.
  1-11: sidecond_solver.
  Unshelve.
  1-6: sidecond_hammer.
  Unshelve.
  - change (ly_size T_st_ly * new_cap ≤ MaxInt ISize)%Z in Hnewsize.
    pose proof (MaxInt_ge_127 ISize) as Hmax.
    clear -Helem_nonzero Hnewsize Hmax. nia.
  - unfold raw_vec_effective_capacity. rewrite decide_False; done.
  - rewrite fmap_replicate /= Heffective. done.
  - rewrite Heffective /raw_vec_effective_capacity !decide_False; try done.
    unfold new_cap. lia.
  - rewrite Heffective /raw_vec_effective_capacity !decide_False; try done.
Qed.
End proof.
