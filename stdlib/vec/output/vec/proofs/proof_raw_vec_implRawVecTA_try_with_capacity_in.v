From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecTA_try_with_capacity_in.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecTA_try_with_capacity_in_proof (π : thread_id) :
  raw_vec_implRawVecTA_try_with_capacity_in_lemma π.
Proof.
  raw_vec_implRawVecTA_try_with_capacity_in_prelude.

  1: rep <-! <3000 liRStep.
  1: rep liRStep.
  - liShow.
    iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
    have Halignrange : ly_align T_st_ly ∈ usize.
    { apply ly_align_in_usize. eapply use_layout_alg_align. exact T_st_alg. }
    iEval (rewrite (raw_vec_layout_roundtrip T_st_ly Halignrange)) in "Hstorage".
    iDestruct (raw_vec_storage_array T_ty with "[] Hstorage") as "[(%Hnonzero & %Halign) [Hfree Harray]]".
    { exact T_st_alg. }
    { done. }
    { iAssumption. }
    liInst Hevar_x2 (raw_vec_effective_capacity (ly_size T_st_ly) (Z.to_nat capacity)).
    liInst Hevar_x0 (replicate (raw_vec_effective_capacity (ly_size T_st_ly) (Z.to_nat capacity)) (#None)).
    liFromSyntaxGoal.
    1: rep <-! <3000 liRStep.
    have Hbytes : size_of_array_in_bytes (st_of T_ty MetaNone)
        (raw_vec_effective_capacity (ly_size T_st_ly) (Z.to_nat capacity)) =
        (ly_size T_st_ly * raw_vec_effective_capacity (ly_size T_st_ly)
          (if decide (ly_size T_st_ly = 0%nat) then 0%nat else Z.to_nat capacity))%nat.
    { rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /=.
      unfold raw_vec_effective_capacity. repeat case_decide; done. }
    rewrite Hbytes.
    liShow. iApply prove_with_subtype_default. iFrame "Hfree".
    liFromSyntaxGoal.
    1: rep <-! <3000 liRStep.
    1: rep liRStep.
    liShow.
    liInst Hevar_x0 (replicate (raw_vec_effective_capacity (ly_size T_st_ly) (Z.to_nat capacity)) None).
    split; first by rewrite fmap_replicate /=.
    liFromSyntaxGoal.
    1: rep <-! <3000 liRStep.
  - rename select reserve_error into err.
    destruct err.
    all: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  case_decide; nia.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
