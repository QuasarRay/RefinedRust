From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_specs_linkedlist.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_pop_back_closure0_FnOnce_spec_subsumption_correct  : (LinkedList_TA_pop_back_closure0_FnOnce_spec_subsumption).
Proof.
  unfold LinkedList_TA_pop_back_closure0_FnOnce_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
