From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_drop_liveness_bind_element_lifetime.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_drop_liveness_bind_element_lifetime_proof (π : thread_id) :
  raw_vec_drop_liveness_bind_element_lifetime_lemma π.
Proof.
  raw_vec_drop_liveness_bind_element_lifetime_prelude.

  rep 3000 liRStep.
  liShow.
  iAssert (x' ◁ₗ[π, Owned] #(replicate 0 (#None)) @ ◁ array_t 0 (maybe_uninit (shr_ref ulft_a (int u8))))%I with "[]" as "Harray".
  { iApply (raw_vec_zero_array (shr_ref ulft_a (int u8)) π x' void* 0).
    - solve_layout_alg.
    - rename select (x' `aligned_to` _) into Halign.
      change (x' `aligned_to` 8%nat) in Halign. exact Halign.
    - done.
    - done.
    - iAssumption. }
  liFromSyntaxGoal.
  rep 3000 liRStep.
  Unshelve.
  1-8: sidecond_solver.
  Unshelve.
  have Hlayout : use_layout_alg RefSynType = Some void* by solve_layout_alg.
  rewrite /raw_vec_capacity_valid /size_of_st /size_of_array_in_bytes /use_layout_alg' Hlayout /=.
  repeat split; try done; lia.
Qed.
End proof.
