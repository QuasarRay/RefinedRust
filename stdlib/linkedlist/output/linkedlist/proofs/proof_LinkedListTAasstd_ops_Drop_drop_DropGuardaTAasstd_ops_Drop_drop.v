From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedListTAasstd_ops_Drop_drop_DropGuardaTAasstd_ops_Drop_drop.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedListTAasstd_ops_Drop_drop_DropGuardaTAasstd_ops_Drop_drop_proof (π : thread_id) :
  LinkedListTAasstd_ops_Drop_drop_DropGuardaTAasstd_ops_Drop_drop_lemma π.
Proof.
  LinkedListTAasstd_ops_Drop_drop_DropGuardaTAasstd_ops_Drop_drop_prelude.

  1: rep <-! <500 liRStep.
  1: rep <-! <500 liRStep.
  rep liRStep.
  match goal with
  | |- @is_xrfn ?rt ?r ∧ _ =>
      assert (IsXrfn (rt := rt) r) as Hcanonical by
        (constructor; exists x'; destruct x'; done)
  end.
  rep <-! liRStep.
  { rep liRStep.
    liInst Hevar_self (tail remaining').
    rep liRStep. }
  { rep liRStep.
    iEval (rewrite -fmap_tail list_fmap_compose).
    rep liRStep.
    liInst Hevar_self (tail remaining').
    rep liRStep. }
  { rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rewrite -fmap_tail. solve_goal.
  - rewrite list_fmap_compose. solve_goal.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
