From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecTA_from_raw_parts_in.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecTA_from_raw_parts_in_proof (π : thread_id) :
  raw_vec_implRawVecTA_from_raw_parts_in_lemma π.
Proof.
  raw_vec_implRawVecTA_from_raw_parts_in_prelude.

  1: rep <-! <3000 liRStep.
  liShow. iIntros "Hfree". liFromSyntaxGoal.
  case_decide as Hstorage.
  all: rep <-! <3000 liRStep.
  all: rep liRStep.
  all: have Hbytes : size_of_array_in_bytes (st_of T_ty MetaNone)
      (raw_vec_effective_capacity (size_of_st (st_of T_ty MetaNone)) (Z.to_nat capacity)) =
      size_of_array_in_bytes (st_of T_ty MetaNone) (Z.to_nat capacity) by
      (unfold size_of_array_in_bytes, size_of_st, use_layout_alg', raw_vec_effective_capacity;
       rewrite T_st_alg /=; case_decide; nia).
  all: try rewrite Hbytes.
  all: try case_decide.
  all: rep <-! <3000 liRStep.
  all: rep liRStep.
  all: rewrite Hbytes.
  all: case_decide.
  all: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: unfold raw_vec_effective_capacity.
  all: repeat case_decide.
  all: try reflexivity.
  all: unfold size_of_array_in_bytes, use_layout_alg' in Hallocation_size.
  all: rewrite T_st_alg /= Nat2Z.inj_mul Z2Nat.id in Hallocation_size; last lia.
  all: destruct (decide (ly_size T_st_ly = 0%nat)) as [Hzero | Hnonzero];
    [left; done | right; nia].
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
