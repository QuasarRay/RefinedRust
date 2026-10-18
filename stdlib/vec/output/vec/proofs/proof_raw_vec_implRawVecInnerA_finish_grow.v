From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_finish_grow.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_finish_grow_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_finish_grow_lemma π.
Proof.
  raw_vec_implRawVecInnerA_finish_grow_prelude.

  1: rep <-! <3000 liRStep.
  all: case_bool_decide as Hlayout_fits.
  all: simplify_eq.
  all: simpl.
  all: rep <-! <3000 liRStep.
  all: rep liRStep.
  all: try case_decide as Hmemory.
  all: simplify_eq.
  all: simpl.
  all: rep <-! <3000 liRStep.
  1: liShow.
  1: iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
  1: iEval (rewrite /raw_vec_storage decide_False; last (simpl; nia)) in "Hstorage".
  1: iDestruct "Hstorage" as "[(%Hnonnull & %Halign & %Hlength) [Hfree Hv]]".
  1: liFromSyntaxGoal.
  1: rep liRStep.
  1: liInst Hevar_x1 v.
  1: split; first done.
  1: liFromSyntaxGoal.
  2: liShow.
  2: iRename select (raw_vec_storage _ _ _ _ _ _) into "Hstorage".
  2: iEval (rewrite /raw_vec_storage decide_True; last (simpl; nia)) in "Hstorage".
  2: iDestruct "Hstorage" as "[(%Hvempty & %Hnonnull & %Halign) #Hbounds]".
  2: subst v.
  2: liFromSyntaxGoal.
  all: rep 1000 liRStep.
  all: rep 1000 liRStep.
  all: rep 1000 liRStep.
  1: match goal with
     Hlength_suffix : (length v + length ?suffix)%nat = _ |- _ =>
       liInst Hevar_x2 suffix; split; first exact Hlength_suffix
     end.
  all: rep 1000 liRStep.
  all: rep 1000 liRStep.
  all: rep 1000 liRStep.
  1: liShow.
  1: liFromSyntaxGoal.
  1: rep liRStep.
  1: match goal with
     Hlength_bytes : length ?bytes = (layout_sz elem_layout * Z.to_nat cap)%nat |- _ =>
       liInst Hevar_x2 bytes; simpl; split; first exact Hlength_bytes
     end.
  all: rep 1000 liRStep.
  all: rep 1000 liRStep.
  all: rep 1000 liRStep.
  all: rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: try exact ([] : val).
  all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: nia.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
