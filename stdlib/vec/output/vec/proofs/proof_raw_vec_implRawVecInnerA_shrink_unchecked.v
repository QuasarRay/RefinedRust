From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_shrink_unchecked.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_shrink_unchecked_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_shrink_unchecked_lemma π.
Proof.
  raw_vec_implRawVecInnerA_shrink_unchecked_prelude.

  destruct (decide (layout_sz elem_layout = 0%nat ∨ self0 = 0%nat)) as [Hmemory|Hmemory].
  { rep 1000 liRStep.
    liShow. iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
    iEval (rewrite /raw_vec_storage decide_True; last (simpl; destruct Hmemory; nia)) in "Hstorage".
    iDestruct "Hstorage" as "[(%Hvempty & %Hnonnull & %Halign) #Hbounds]".
    subst v. liFromSyntaxGoal. rep 2000 liRStep.
  }
  { rep 2000 liRStep.
    rewrite decide_False; last exact Hmemory.
    simpl. liShow.
    iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
    iEval (rewrite /raw_vec_storage decide_False; last (simpl; nia)) in "Hstorage".
    iDestruct "Hstorage" as "[(%Hnonnull & %Halign & %Hlength) [Hfree Hv]]".
    liFromSyntaxGoal. rep 2000 liRStep.
    { liInst Hevar_x1 v. split; first done.
      liFromSyntaxGoal. rep 2000 liRStep. rep liRStep.
      rewrite decide_True; last (rewrite /layout_alignment_nat /alignment_to_align_nat;
        pose proof (Nat.pow_nonzero 2 (alignment_to_align_log2 (layout_alignment elem_layout))); lia).
      liShow. iIntros "Hunit". liFromSyntaxGoal. rep 2000 liRStep.
    }
    { rep 2000 liRStep. rep 3000 liRStep.
      liInst Hevar_x1 v. split; first done.
      liFromSyntaxGoal. rep 3000 liRStep.
      { rep 2000 liRStep. split; first shelve_sidecond. liFromSyntaxGoal. rep 1000 liRStep. }
      { rep 1000 liRStep. rep liRStep. }
    }
  }
  Unshelve.
  1-82: first [exact (self : loc) | sidecond_solver].
  Unshelve.
  1-14: first [exact (self : loc) | sidecond_hammer].
  Unshelve.
  - rename select (loc_a x' = _) into Haddr.
    rewrite Haddr /layout_alignment_nat /alignment_to_align_nat.
    pose proof (Nat.pow_nonzero 2 (alignment_to_align_log2 (layout_alignment elem_layout))). lia.
  - by rewrite Nat.mul_0_r take_0.
  - rename select (MinInt usize = 0) into Hmin.
    rewrite Hmin. unfold raw_vec_effective_capacity in Hshrink_cap.
    rewrite decide_False in Hshrink_cap; last lia. nia.
  - rewrite /layout_alignment_nat /alignment_to_align_nat /=.
    eexists _. reflexivity.
  - unfold raw_vec_effective_capacity in Hshrink_cap.
    rewrite decide_False in Hshrink_cap; last lia. nia.
  - apply Z.divide_mul_l.
    rename select (layout_wf elem_layout) into Hlayout_wf.
    rewrite /layout_wf /ly_align /rust_layout_to_layout /layout_alignment_log2_nat /= in Hlayout_wf.
    exact Hlayout_wf.
  - unfold raw_vec_effective_capacity in Hshrink_cap.
    rewrite decide_False in Hshrink_cap; last lia. nia.
  - unfold raw_vec_effective_capacity in Hshrink_cap.
    rewrite decide_False in Hshrink_cap; last lia. lia.
  - rename select (l `has_layout_loc` _) into Hnewalign.
    rewrite raw_vec_alignment_roundtrip in Hnewalign. exact Hnewalign.
  - rewrite raw_vec_alignment_roundtrip. reflexivity.
  - rewrite raw_vec_alignment_roundtrip.
     eexists _. repeat split; try reflexivity; lia.
Qed.
End proof.
