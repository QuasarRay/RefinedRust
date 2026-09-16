From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_clear.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_clear_proof (π : thread_id) :
  LinkedList_TA_clear_lemma π.
Proof.
  LinkedList_TA_clear_prelude.

  1: rep <-! <3000 liRStep.
  { rep liRStep.
    liInst Hevar_self ([] : list (place_rfn T_rt)).
    liInst Hevar_locs ([] : list loc).
    liInst Hevar_a a.
    rep <-! <3000 liRStep. }
  { rep <-! <3000 liRStep.
    rep liRStep.
    liInst Hevar_self ([] : list (place_rfn T_rt)).
    liInst Hevar_locs ([] : list loc).
    liInst Hevar_a a.
    rep <-! <3000 liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
