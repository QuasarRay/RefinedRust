From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_extract_if.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_extract_if_proof (π : thread_id) :
  LinkedList_TA_extract_if_lemma π.
Proof.
  LinkedList_TA_extract_if_prelude.

  1: rep <-! <3000 liRStep.
  rep liRStep.
  liInst Hevar_a a.
  liInst Hevar_self (PlaceIn ∘ RT_xrt T_rt <$> self).
  1: rep <-! <3000 liRStep.
  rep liRStep.
  liInst Hevar_f filter.
  liInst Hevar_pos 0%nat.
  liInst Hevar_visited 0%nat.
  liInst Hevar_initial_len (length self).
  1: rep <-! <3000 liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { apply head_lookup. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
