From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_reserve.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_reserve_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_reserve_lemma π.
Proof.
  raw_vec_implRawVecInnerA_reserve_prelude.

  rep 3000 liRStep.
  { (* Growth uses the existing cold helper. *)
    rep liRStep.
    liInst Hevar_x1 v.
    liShow. iApply prove_with_subtype_default. iFrame.
    liFromSyntaxGoal.
    rep 1000 liRStep.
    rep liRStep.
    liInst Hevar_x0 x'0.
    liShow. iApply prove_with_subtype_default. iFrame.
    liFromSyntaxGoal. rep 1000 liRStep.
  }
  { (* Existing capacity suffices. *)
    rep 3000 liRStep. rep liRStep.
    liInst Hevar_x0 ([] : val).
    rewrite app_nil_r.
    liShow. iApply prove_with_subtype_default. iFrame.
    liFromSyntaxGoal. rep 1000 liRStep.
  }
  Unshelve.
  1-17: sidecond_solver.
  Unshelve.
  - sidecond_hammer.
    have Hcap_max : raw_vec_effective_capacity (layout_sz elem_layout) self0 ≤ MaxInt usize.
    { unfold raw_vec_effective_capacity. case_decide; nia. }
    match goal with H : additional > _ `mod` _ |- _ =>
      rewrite Z.mod_small in H; lia end.
  - sidecond_hammer.
  - sidecond_hammer.
    rename select (layout_sz elem_layout ≠ 0%nat) into Helem_nonzero.
    unfold raw_vec_effective_capacity. rewrite decide_False; last done.
    pose proof (raw_vec_amortized_capacity_positive (layout_sz elem_layout) self0 (len + additional)) as Hpositive.
    rewrite Z2Nat.id; last lia.
    apply raw_vec_amortized_capacity_required.
  - sidecond_hammer.
    have Hcap_max : raw_vec_effective_capacity (layout_sz elem_layout) self0 ≤ MaxInt usize.
    { rename select (2 * MaxInt isize < MaxInt usize)%Z into Hmax_relation.
      clear -Hallocation_size Hmax_relation.
      unfold raw_vec_effective_capacity. case_decide; nia. }
    match goal with H : ¬ additional > _ `mod` _ |- _ =>
      rewrite Z.mod_small in H; lia end.
Qed.
End proof.
