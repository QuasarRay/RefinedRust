From iris.proofmode Require Import proofmode.
From lithium Require Import all.

Section tests.
  Context {Σ : gFunctors}.

  Lemma exact_context_lookup_spatial (P Q : iProp Σ) : P -∗ Q -∗ P ∗ Q.
  Proof.
    iIntros "HP HQ". let_bind_envs.
    let H := constr:(ltac:(typeclasses eauto) : CheckExactOwnInContext P) in idtac.
    iFrame.
  Qed.

  Lemma exact_context_lookup_persistent (P : iProp Σ) `{!Persistent P} : P -∗ P.
  Proof.
    iIntros "#HP". let_bind_envs.
    let H := constr:(ltac:(typeclasses eauto) : CheckExactOwnInContext P) in idtac.
    li_pm_reduce. done.
  Qed.

  (* An unknown parameter must not be inferred from the context. The existing
     unifying lookup remains available when that behavior is wanted. *)
  Lemma exact_context_lookup_no_instantiation (P : nat → iProp Σ) : P 3 -∗ P 3.
  Proof.
    iIntros "HP". let_bind_envs.
    let x := fresh "x" in
    evar (x : nat);
    let v := eval unfold x in x in
    (tryif check_exact_own_in_context (P v)
      then fail "exact lookup instantiated a parameter" else is_evar v);
    check_own_in_context (P v);
    constr_eq v 3.
    li_pm_reduce. done.
  Qed.
End tests.
