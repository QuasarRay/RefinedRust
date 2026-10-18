From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_try_reserve.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_try_reserve_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_try_reserve_lemma π.
Proof.
  raw_vec_implRawVecInnerA_try_reserve_prelude.

  rep 3000 liRStep.
  { (* Growth is necessary. *)
    rep liRStep.
    liInst Hevar_x1 v.
    liShow. iApply prove_with_subtype_default. iFrame.
    liFromSyntaxGoal.
    rep 1000 liRStep.
    { (* Successful growth preserves the old bytes and adds a suffix. *)
      liShow. split; first solve_local_fresh.
      iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
      iEval (rewrite /raw_vec_storage decide_False; last
        (simpl; pose proof (raw_vec_amortized_capacity_positive (layout_sz elem_layout) self0 (len + additional)); nia)) in "Hstorage".
      iDestruct "Hstorage" as "[(%Hnonnull & %Halign & %Hlength) [Hfree Hv]]".
      liFromSyntaxGoal.
      rep 1000 liRStep. rep liRStep.
      liInst Hevar_x3 x'1.
      liShow. iApply prove_with_subtype_default.
      rewrite /raw_vec_storage decide_False /raw_allocation; last
        (simpl; pose proof (raw_vec_amortized_capacity_positive (layout_sz elem_layout) self0 (len + additional)); nia).
      iFrame. iSplitR; first (iPureIntro; done).
      liFromSyntaxGoal. rep 1000 liRStep.
    }
    { (* Allocation failure returns the unchanged storage. *)
      rep 3000 liRStep.
    }
  }
  { (* Existing capacity suffices; no allocation occurs. *)
    rep 3000 liRStep. rep liRStep.
    liInst Hevar_x3 ([] : val).
    rewrite app_nil_r.
    liShow. iApply prove_with_subtype_default. iFrame.
    liFromSyntaxGoal. rep 1000 liRStep.
  }

  Unshelve.
  1-48: first [exact ([] : val) | exact (self : loc) | exact (self0 : nat) | sidecond_solver].
  Unshelve.
  - sidecond_hammer.
  - sidecond_hammer.
    right.
    have Hcap_max : raw_vec_effective_capacity (layout_sz elem_layout) self0 ≤ MaxInt usize.
    { unfold raw_vec_effective_capacity. case_decide; nia. }
    match goal with H : additional > _ `mod` _ |- _ =>
      rewrite Z.mod_small in H; lia end.
  - sidecond_hammer.
    pose proof (raw_vec_amortized_capacity_positive (layout_sz elem_layout) self0 (len + additional)) as Hpositive.
    pose proof (raw_vec_amortized_capacity_required (layout_sz elem_layout) self0 (len + additional)) as Hrequired.
    rename select (layout_sz elem_layout ≠ 0%nat) into Helem_nonzero.
    rename select (layout_sz elem_layout * Z.to_nat (raw_vec_amortized_capacity _ _ _) ≤ MaxInt isize)%Z into Hnew_size.
    rewrite Z2Nat.id in Hnew_size; last lia.
    unfold raw_vec_effective_capacity.
    rewrite decide_False; last done.
    rewrite Z2Nat.id; last lia.
    rewrite Z.mod_small; nia.
  - sidecond_hammer.
    rename select (layout_sz elem_layout ≠ 0%nat) into Helem_nonzero.
    unfold raw_vec_effective_capacity. rewrite decide_False; last done.
    pose proof (raw_vec_amortized_capacity_positive (layout_sz elem_layout) self0 (len + additional)) as Hpositive.
    rewrite Z2Nat.id; last lia.
    apply raw_vec_amortized_capacity_required.
  - sidecond_hammer.
    have Hcap_max : raw_vec_effective_capacity (layout_sz elem_layout) self0 ≤ MaxInt usize.
    { unfold raw_vec_effective_capacity. case_decide; nia. }
    match goal with H : additional > _ `mod` _ |- _ =>
      rewrite Z.mod_small in H; lia end.
  - sidecond_hammer.
    have Hcap_max : raw_vec_effective_capacity (layout_sz elem_layout) self0 ≤ MaxInt usize.
    { rename select (2 * MaxInt isize < MaxInt usize)%Z into Hmax_relation.
      clear -Hallocation_size Hmax_relation.
      unfold raw_vec_effective_capacity. case_decide; nia. }
    match goal with H : ¬ additional > _ `mod` _ |- _ =>
      rewrite Z.mod_small in H; lia end.
Qed.
End proof.
