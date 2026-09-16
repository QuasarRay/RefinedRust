From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_cursor_back_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_cursor_back_mut_proof (π : thread_id) :
  LinkedList_TA_cursor_back_mut_lemma π.
Proof.
  LinkedList_TA_cursor_back_mut_prelude.

  rep <-! liRStep; liShow.
  rep liRStep.
  liInst Hevar_a a.
  liInst Hevar_self ((PlaceIn ∘ RT_xrt T_rt <$> self)).
  rep <-! liRStep.
  rep liRStep; liShow.
  iRename select (Inherit _ _) into "Hinh".
  iApply (prove_with_subtype_inherit_manual with "Hinh").
  { shelve_sidecond. }
  { eauto. }
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { by rewrite last_lookup Hlen. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
