From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_RawVecTAasstd_ops_Drop_drop.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma RawVecTAasstd_ops_Drop_drop_proof (π : thread_id) :
  RawVecTAasstd_ops_Drop_drop_lemma π.
Proof.
  RawVecTAasstd_ops_Drop_drop_prelude.

  rep 3000 liRStep.
  liShow. iIntros "Hfree". liShow.
  iMatchHyp ltac:(fun H P => lazymatch P with context [array_t] => iRename H into "Harray" end).
  rename select (length x1 = _) into Heffective.
  change (length x1 = raw_vec_effective_capacity (ly_size T_st_ly) stored_cap) in Heffective.
  have Hsamecap : stored_cap = x5.
  { rename select (if decide (ly_size T_st_ly = 0%nat) then stored_cap = 0%nat else _) into Hphysical.
    rename select (if decide (ly_size T_st_ly = 0%nat) then x5 = 0%nat else _) into Hinnerphysical.
    rename select ((if decide (ly_size T_st_ly = 0%nat) then _ else stored_cap) = _) into Hcaps.
    destruct (decide (ly_size T_st_ly = 0%nat)); naive_solver. }
  subst x5.
  have Hsize : (ly_size T_st_ly * stored_cap ≤ MaxInt ISize)%Z.
  { rename select (if decide (ly_size T_st_ly = 0%nat) then _ else _) into Hphysical.
    destruct (decide (ly_size T_st_ly = 0%nat)) as [Hzero | Hnonzero].
    - rewrite Hzero. pose proof (MaxInt_ge_127 ISize). lia.
    - move: Hphysical. rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /= Nat2Z.inj_mul. congruence. }
  iEval (rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /=) in "Hfree".
  iPoseProof (raw_vec_array_storage T_ty with "Hfree Harray") as "Hupdate";
    [exact T_st_alg | exact Hsize | done | done |].
  rewrite {1}/introduce_with_hooks.
  iIntros (F HF) "#Hctx #HE HL _".
  iMod (fupd_mask_mono lftE F _ HF with "Hupdate") as (old_bytes) "[Hstorage _]".
  iModIntro. iExists [κ ⊑ₗ{0} [ulft_1]; ϝ ⊑ₗ{0} []]. iFrame "HL".
  liFromSyntaxGoal. rep 1000 liRStep. rep liRStep.
  liInst Hevar_x1 old_bytes.
  liShow. iApply prove_with_subtype_default. iSplitL "Hstorage".
  { iEval (rewrite raw_vec_layout_roundtrip; last (apply ly_align_in_usize; eapply use_layout_alg_align; exact T_st_alg)). done. }
  liFromSyntaxGoal. rep 2000 liRStep.
  Unshelve.
  1-5: sidecond_solver.
Qed.
End proof.
