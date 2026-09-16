From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_specs_linkedlist.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma IterMutaTasstd_iter_DoubleEndedIterator_spec_subsumption_correct  : (IterMutaTasstd_iter_DoubleEndedIterator_spec_subsumption).
Proof.
  unfold IterMutaTasstd_iter_DoubleEndedIterator_spec_subsumption; solve_trait_incl_prelude.
  { rep 20 liRStep.
    { unfold traits_iterator_Iterator_Inv.  simpl. done. } 
    { rep liRStep. } }
  { rep 20 liRStep. }

  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
