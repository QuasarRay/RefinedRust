From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_grow_exact.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_grow_exact_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_grow_exact_lemma π.
Proof.
  raw_vec_implRawVecInnerA_grow_exact_prelude.

  1: rep 1000 liRStep.
  1: liShow.
  1: iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
  1: iEval (rewrite /raw_vec_storage decide_True; last (simpl; nia)) in "Hstorage".
  1: iDestruct "Hstorage" as "[(%Hvempty & %Hnonnull & %Halign) #Hbounds]".
  1: subst v.
  1: liFromSyntaxGoal.
  1: rep 2000 liRStep.
  all: rep 1000 liRStep.
  all: rep liRStep.
  all: try case_bool_decide as Hsum_fits.
  all: simplify_eq.
  all: simpl.
  all: rep 1000 liRStep.
  all: rep liRStep.
  1: liInst Hevar_x1 v.
  1: liShow.
  1: iApply prove_with_subtype_default.
  1: iFrame.
  1: liFromSyntaxGoal.
  1: rep 1000 liRStep.
  1: liShow.
  1: iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
  1: iEval (rewrite /raw_vec_storage decide_False; last (simpl; nia)) in "Hstorage".
  1: iDestruct "Hstorage" as "[(%Hnonnull & %Halign & %Hlength) [Hfree Hv]]".
  1: liFromSyntaxGoal.
  1: rep 1000 liRStep.
  1: rep 2000 liRStep.
   1: liInst Hevar_x0 x'0.
  1: split; first by rewrite -app_length.
  all: rep 1000 liRStep.
  all: rep liRStep.

  all: print_remaining_goal.
  Unshelve.
  all: try exact ([] : val).
  all: try exact (self : loc).
  all: try (timeout 2 sidecond_solver).
  all: try (timeout 2 sidecond_hammer).
  all: try (timeout 10 sidecond_solver).
  all: try (timeout 10 sidecond_hammer).
  all: sidecond_solver.
  all: sidecond_hammer.
  Unshelve.
  - unfold raw_vec_effective_capacity in Hgrow_requested.
    rewrite decide_False in Hgrow_requested; last done.
    exact Hgrow_requested.
  - rename select (layout_sz elem_layout * (len + additional) ≤ MaxInt isize)%Z into Hnew_size.
    rename select (layout_sz elem_layout ≠ 0%nat) into Helem_nonzero.
    rename select (0 ≤ len + additional)%Z into Hsum_nonneg.
    clear -Hnew_size Helem_nonzero Hsum_nonneg.
    nia.
   - destruct x'2; simpl in *; intuition nia.
Qed.
End proof.
