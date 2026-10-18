From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num.generated Require Import generated_code_num generated_specs_num generated_template_u16_checked_mul.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u16_checked_mul_proof (π : thread_id) :
  u16_checked_mul_lemma π.
Proof.
  u16_checked_mul_prelude.
  assert (Hmax : MaxInt u16 = 65535) by (rewrite MaxInt_eq; reflexivity).

  1: rep <-! <3000 liRStep.
  1: rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  { exists 0. rewrite Z.mul_0_r bool_decide_true; [done | lia]. }
  all: assert (Hrhs_pos : 0 < rhs) by lia.
  { case_bool_decide as Hproduct; last done.
    rename select (x > _ `quot` rhs) into Hoverflow.
    assert (Hquot_lower : x ≤ 65535 `quot` rhs).
    { apply Z.quot_le_lower_bound; [exact Hrhs_pos |].
      rewrite Hmax in Hproduct. lia. }
    lia.
  }
  rename select (¬ x > _ `quot` rhs) into Hfits.
  rename select (¬ MinInt u16 ≤ x * rhs ≤ MaxInt u16) into Hout_of_range.
  rename select (0 ≤ x) into Hx_nonneg.
  assert (Hquot_product : rhs * (65535 `quot` rhs) ≤ 65535).
  { rewrite Z.quot_div_nonneg; [| lia | exact Hrhs_pos].
    apply Z.mul_div_le. exact Hrhs_pos.
  }
  rename select (MinInt u16 = 0) into Hmin.
  exfalso. apply Hout_of_range. rewrite Hmin Hmax.
  clear - Hfits Hx_nonneg Hrhs_pos Hquot_product. nia.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
