From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_try_reserve_exact.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_try_reserve_exact_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_try_reserve_exact_lemma π.
Proof.
  raw_vec_implRawVecInnerA_try_reserve_exact_prelude.

  1: rep 3000 liRStep.
  all: rep liRStep.
  1: liInst Hevar_x1 v.
  1: liShow.
  1: iApply prove_with_subtype_default.
  1: iFrame.
  1: liFromSyntaxGoal.
  all: rep 1000 liRStep.
  1: liShow.
  1: iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
  1: iEval (rewrite /raw_vec_storage decide_False; last (simpl; nia)) in "Hstorage".
  1: iDestruct "Hstorage" as "[(%Hnonnull & %Halign & %Hlength) [Hfree Hv]]".
  1: liFromSyntaxGoal.
  all: rep 1000 liRStep.
  all: rep liRStep.
   1: liInst Hevar_x3 x'1.
  1: split; first by rewrite -app_length.
  all: rep 1000 liRStep.
  all: rep liRStep.
  1: liInst Hevar_x3 ([] : val).
  1: rewrite app_nil_r.
  1: liShow.
  1: iApply prove_with_subtype_default.
  1: iFrame.
  1: liFromSyntaxGoal.
  all: rep 1000 liRStep.

  all: print_remaining_goal.
  Unshelve.
  all: try exact ([] : val).
  all: try exact (self : loc).
  all: try exact (self0 : nat).
  all: try (timeout 10 sidecond_solver).
  all: try (timeout 10 sidecond_hammer).
  all: sidecond_solver.
  all: sidecond_hammer.
  Unshelve.
  - have Hcap_max : raw_vec_effective_capacity (layout_sz elem_layout) self0 ≤ MaxInt usize.
    { unfold raw_vec_effective_capacity. case_decide; nia. }
    match goal with H : additional > _ `mod` _ |- _ =>
      rewrite Z.mod_small in H; lia end.
  - unfold raw_vec_effective_capacity.
    case_decide; rewrite ?Z2Nat.id; try lia.
    rewrite Z.mod_small; lia.
  - unfold raw_vec_effective_capacity.
     rename select (layout_sz elem_layout ≠ 0%nat) into Helem_nonzero.
    rewrite decide_False; last done.
    rewrite Z2Nat.id; lia.
  - have Hcap_max : raw_vec_effective_capacity (layout_sz elem_layout) self0 ≤ MaxInt usize.
    { rename select (2 * MaxInt isize < MaxInt usize)%Z into Hmax_relation.
      clear -Hallocation_size Hmax_relation.
      unfold raw_vec_effective_capacity. case_decide; nia. }
    match goal with H : ¬ additional > _ `mod` _ |- _ =>
      rewrite Z.mod_small in H; lia end.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
