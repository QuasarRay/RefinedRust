From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_specs_linkedlist.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedListTAasstd_ops_Drop_drop_DropGuardaTAasstd_ops_Drop_spec_subsumption_correct  : (LinkedListTAasstd_ops_Drop_drop_DropGuardaTAasstd_ops_Drop_spec_subsumption).
Proof.
  unfold LinkedListTAasstd_ops_Drop_drop_DropGuardaTAasstd_ops_Drop_spec_subsumption; solve_trait_incl_prelude.
  all: repeat liRStep; liShow.
  all: print_remaining_trait_goal.
  Unshelve.
  all: sidecond_solver.
  Unshelve.
  all: sidecond_hammer.
Qed.

End proof.
