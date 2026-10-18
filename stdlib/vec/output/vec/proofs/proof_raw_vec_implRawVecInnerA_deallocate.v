From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_deallocate.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_deallocate_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_deallocate_lemma π.
Proof.
  raw_vec_implRawVecInnerA_deallocate_prelude.

  destruct (decide (layout_sz elem_layout = 0%nat ∨ self0 = 0%nat)) as [Hmemory | Hmemory].
  { rep 1000 liRStep.
    liShow. iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
    iEval (rewrite /raw_vec_storage decide_True; last (simpl; nia)) in "Hstorage".
    iDestruct "Hstorage" as "[(%Hvempty & %Hnonnull & %Halign) #Hbounds]".
    subst v. liFromSyntaxGoal. rep 2000 liRStep.
  }
  { rep 1000 liRStep.
    rewrite decide_False; last exact Hmemory. simpl.
    liShow. iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
    iEval (rewrite /raw_vec_storage decide_False; last (simpl; nia)) in "Hstorage".
    iDestruct "Hstorage" as "[(%Hnonnull & %Halign & %Hlength) [Hfree Hv]]".
    liFromSyntaxGoal. rep 2000 liRStep.
    liInst Hevar_x1 v. split; first done.
    liFromSyntaxGoal. rep 2000 liRStep.
  }
  Unshelve.
  1-16: sidecond_solver.
  Unshelve.
Qed.
End proof.
