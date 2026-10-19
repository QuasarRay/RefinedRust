From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_grow_amortized.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_grow_amortized_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_grow_amortized_lemma π.
Proof.
  raw_vec_implRawVecInnerA_grow_amortized_prelude.

  1: rep 1000 liRStep.
  { rep 1000 liRStep.
    { liShow.
      iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
      iEval (rewrite /raw_vec_storage decide_True; last (simpl; nia)) in "Hstorage".
      iDestruct "Hstorage" as "[(%Hvempty & %Hnonnull & %Halign) #Hbounds]".
      subst v.
      liFromSyntaxGoal.
      rep <-! < 2000 liRStep. }
    { rep <-! < 1000 liRStep.
      rep <-! < 1000 liRStep.
      { rep  liRStep.
        try case_bool_decide as Hsum_fits.
        all: simplify_eq.
        all: simpl.
        { rep liRStep.
          { rewrite !raw_vec_max.
            liInst Hevar_x1 v.
            liShow.
            iApply prove_with_subtype_default.
            iRename select (raw_vec_storage _ _ _ _ _ _) into "Hraw".
            iSplitL "Hraw". { done. }
            liFromSyntaxGoal.
            rep 1000 liRStep.
            { liShow.
              iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
              iEval (rewrite /raw_vec_storage decide_False; last (simpl; nia)) in "Hstorage".
              iDestruct "Hstorage" as "[(%Hnonnull & %Halign & %Hlength) [Hfree Hv]]".
              liFromSyntaxGoal.
              rep liRStep.
              liInst Hevar_x0 x'0.
              rep liRStep. }
            { rep liRStep. }
          } 
          { rep <-! <3000 liRStep. }
        } 
      } 
      { rep <-! <3000 liRStep.
        try case_bool_decide as Hsum_fits.
        all: simplify_eq.
        all: simpl.
        rep liRStep. }
    } 
  } 

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve.
  all: try exact ([] : val).
  all: try exact (self : loc).
  all: sidecond_hammer.
  all: unfold raw_vec_amortized_capacity.
  all: rewrite ?raw_vec_max.
  all: replace (2 * Z.of_nat self0)%Z with (Z.of_nat self0 * 2)%Z by ring.
  all: try reflexivity.
  all: repeat match goal with
    | H : context [bool_decide ((?a ?= ?b) = Lt)] |- _ =>
        progress rewrite !raw_vec_max in H
    end.
  all: try assumption.
  - rename select (layout_sz elem_layout ≠ 0%nat) into Helem_nonzero.
    rename select (layout_sz elem_layout * _ ≤ MaxInt isize)%Z into Hnew_size.
    rename select (0 ≤ Z.max _ _)%Z into Hcap_nonneg.
    clear -Helem_nonzero Hnew_size Hcap_nonneg.
    nia.
  - by rewrite -app_length.
  - pose proof (Z.le_max_r (raw_vec_min_non_zero_cap (layout_sz elem_layout))
        (Z.max (Z.of_nat self0 * 2) (len + additional))) as Hmax_outer.
    pose proof (Z.le_max_l (raw_vec_min_non_zero_cap (layout_sz elem_layout))
        (Z.max (Z.of_nat self0 * 2) (len + additional))) as Hmin_bound.
    pose proof (raw_vec_min_non_zero_cap_positive (layout_sz elem_layout)) as Hmin_positive.
    rename select (layout_sz elem_layout ≠ 0%nat) into Helem_nonzero.
    match goal with
    | H : match x'2 with | ReserveCapacityOverflow => _ | ReserveAllocError _ => _ end |- _ =>
        rename H into Herror
    end.
     clear -Herror Hmin_bound Hmin_positive Helem_nonzero.
     destruct x'2; simpl in *. 
     + right; right; exact Herror.
     + destruct Herror as (Hlayout & Hsize).
       repeat split; try assumption; nia.
Qed.
End proof.
