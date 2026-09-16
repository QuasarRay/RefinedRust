From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_drop_glue_LinkedListTAasstd_ops_Drop_drop_DropGuard.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma drop_glue_LinkedListTAasstd_ops_Drop_drop_DropGuard_proof (π : thread_id) :
  drop_glue_LinkedListTAasstd_ops_Drop_drop_DropGuard_lemma π.
Proof.
  drop_glue_LinkedListTAasstd_ops_Drop_drop_DropGuard_prelude.

  rep <-! liRStep. liShow.
  iRename select (x1 ◁ₗ[π, Owned] _ @ ◁ _)%I into "Ha". 
  iApply updateable_add_fupd.
  iMod (ex_plain_t_destruct_owned with "Ha") as "(% & Hinv & ?)"; first done.
  iModIntro. 
  iEval (rewrite /inv_P/=) in "Hinv".
  iRevert "Hinv". simpl.
  rep <-! liRStep; liShow.
  apply_update updateable_strip_guards.
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: apply inhabitant.
Qed.
End proof.
