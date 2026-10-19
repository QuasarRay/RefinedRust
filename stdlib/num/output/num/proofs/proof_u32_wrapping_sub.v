From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.num.num.generated Require Import generated_code_num generated_specs_num generated_template_u32_wrapping_sub.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma u32_wrapping_sub_proof (π : thread_id) :
  u32_wrapping_sub_lemma π.
Proof.
  u32_wrapping_sub_prelude.
  assert (Hmax : MaxInt u32 = 4294967295) by (rewrite MaxInt_eq; reflexivity).

  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  by rewrite /wrap_to_it /wrap_unsigned /int_modulus /= Hmax.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
