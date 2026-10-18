From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecTA_new_in.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecTA_new_in_proof (π : thread_id) :
  raw_vec_implRawVecTA_new_in_lemma π.
Proof.
  raw_vec_implRawVecTA_new_in_prelude.

  1: rep <-! <3000 liRStep.
  1: rep liRStep.
  liShow.
  iAssert (x' ◁ₗ[π, Owned]
    #(replicate (raw_vec_effective_capacity (size_of_st (st_of T_ty MetaNone)) 0) (#None))
    @ ◁ array_t (raw_vec_effective_capacity (size_of_st (st_of T_ty MetaNone)) 0)
      (maybe_uninit T_ty))%I as "Harray".
  { iApply (raw_vec_zero_array _ _ _ T_st_ly).
    - exact T_st_alg.
    - shelve.
    - unfold raw_vec_effective_capacity, size_of_st, use_layout_alg'.
      rewrite T_st_alg /=. case_decide; nia.
    - iAssumption.
    - iAssumption. }
  rep <-! <3000 liRStep.
  liInst Hevar_r2' None.
  rep <-! <3000 liRStep.
  have Hzero : size_of_array_in_bytes (st_of T_ty MetaNone)
      (raw_vec_effective_capacity (size_of_st (st_of T_ty MetaNone)) 0) = 0%nat.
  { unfold size_of_array_in_bytes, size_of_st, use_layout_alg', raw_vec_effective_capacity.
    rewrite T_st_alg /=. case_decide; nia. }
  rewrite Hzero /=.
  rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  1: by rewrite fmap_replicate /=.
  all: rename select (ly_align_in_bounds T_st_ly) into Halign_bound.
  all: rename select (x' `aligned_to` _) into Hptr_align.
  all: rename select (MinInt usize = 0) into Husize_min.
  all: assert (alignment_to_align (alignment_of_align (ly_align T_st_ly)) =
      Z.of_nat (ly_align T_st_ly)) as Hround by (apply alignment_to_from;
    [split; [rewrite Husize_min; lia | rewrite MaxInt_eq; exact Halign_bound]
    | rewrite Nat2Z.id; exists (ly_align_log T_st_ly); reflexivity]).
  all: unfold alignment_to_align in Hround.
  all: rewrite -(Nat2Z.inj_pow 2) in Hround.
  all: apply Nat2Z.inj in Hround.
  all: unfold alignment_to_align_nat in Hptr_align.
  all: rewrite Hround in Hptr_align.
  all: exact Hptr_align.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
