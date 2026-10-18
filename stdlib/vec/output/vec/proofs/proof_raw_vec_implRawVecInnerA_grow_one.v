From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_grow_one.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_grow_one_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_grow_one_lemma π.
Proof.
  raw_vec_implRawVecInnerA_grow_one_prelude.

  rep 3000 liRStep.
  liInst Hevar_x1 v.
  liShow. iApply prove_with_subtype_default. iFrame.
  liFromSyntaxGoal. rep 1000 liRStep.
  { (* Successful growth preserves the old bytes and adds the returned suffix. *)
    liInst Hevar_x2 x'1.
    liShow. iApply prove_with_subtype_default. iFrame.
    liFromSyntaxGoal. rep 1000 liRStep.
  }
  { (* Errors retain the original state, including on panic. *)
    rep 3000 liRStep.
  }
  Unshelve.
  1-15: sidecond_solver.
  Unshelve.
  - sidecond_hammer.
  - sidecond_hammer.
    unfold raw_vec_effective_capacity. case_decide; lia.
  - sidecond_hammer.
    unfold raw_vec_effective_capacity. case_decide; intuition lia.
  - sidecond_hammer.
    pose proof (raw_vec_amortized_capacity_required (layout_sz elem_layout) self0 (Z.succ self0)) as Hrequired.
    pose proof (raw_vec_amortized_capacity_positive (layout_sz elem_layout) self0 (Z.succ self0)) as Hpositive.
    lia.
  - sidecond_hammer.
Qed.
End proof.
