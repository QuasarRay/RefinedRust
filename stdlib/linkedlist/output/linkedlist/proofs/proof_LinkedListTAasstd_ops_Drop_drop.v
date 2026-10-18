From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedListTAasstd_ops_Drop_drop.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedListTAasstd_ops_Drop_drop_proof (π : thread_id) :
  LinkedListTAasstd_ops_Drop_drop_lemma π.
Proof.
  LinkedListTAasstd_ops_Drop_drop_prelude.

  liRStepUntil (typed_val_expr _ _ _ (&ref{Mut,_,_} _)%E). 
  change ((&ref{Mut,_,_} (!{RefOp} "self"))%E) with ((&raw{PRef,Mut} (!{RefOp} "self"))%E).
  liRStepUntil (typed_stmt _ _ _ (Goto _)).
  rep liRStep.
  match goal with
  | |- @is_xrfn ?rt ?r ∧ _ =>
      assert (IsXrfn (rt := rt) r) as Hcanonical by
        (constructor; exists x'; destruct x'; done)
  end.
  rep <-! liRStep.
  { rename select (head remaining = Some _) into Hrem.
    destruct remaining as [|xhead remaining]; simpl in *; first done.
    injection Hrem as <-.
    rep liRStep. }
  { rep <-! liRStep.
    rename select (head remaining = Some _) into Hrem.
    destruct remaining as [|xhead remaining]; simpl in *; first done.
    injection Hrem as <-.
    rep liRStep. liShow.
    liInst Hevar_dropped (dropped ++ [xhead]).
    rep <-! liRStep. }
  { rep <-! liRStep. liShow.

    (* we have to destruct the invariant of the "mem::forget"-ed DropGuard *)
    iRename select (v8 ◁ᵥ{π, MetaNone} _ @ _)%I into "Hguard" .
    iEval (rewrite ex_plain_t_unfold_val/inv_P/=) in "Hguard".
    apply_update updateable_strip_guards.
    iRevert "Hguard".
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
