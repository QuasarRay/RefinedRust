From radium Require Import machine.

(** Regression tests for the parametric low-level machine wrapper. *)

Definition record_event : event_interp (list radium_event) :=
  λ events event events', events' = events ++ [event].

Example interpret_no_events_stutters {low_level_state : Type}
    (interp : event_interp low_level_state) σ σ' :
  interpret_events interp σ [] σ' -> σ = σ'.
Proof. inversion 1. done. Qed.

Example interpret_events_in_order event1 event2 :
  interpret_events record_event [] [event1; event2] [event1; event2].
Proof.
  eapply InterpretEventsCons with (σ2 := [event1]); first done.
  eapply InterpretEventsCons with (σ2 := [event1; event2]); first done.
  apply InterpretEventsNil.
Qed.

Example machine_steps_are_silent {low_level_state : Type}
    (conf : RadiumConfig) (interp : event_interp low_level_state)
    e σ κ e' σ' efs :
  machine_step conf interp e σ κ e' σ' efs -> κ = [].
Proof. by inversion 1. Qed.

Example unknown_expr_can_step {low_level_state : Type}
    (conf : RadiumConfig) (interp : event_interp low_level_state)
    (σ : machine_state low_level_state) low' :
  machine_step conf interp UnknownExpr σ [] UnknownExpr
    {| low_state := low';
       radium_state := σ.(radium_state) |} [].
Proof. destruct σ. apply EnvStep. Qed.

Example unknown_expr_step_inv {low_level_state : Type}
    (conf : RadiumConfig) (interp : event_interp low_level_state)
    σ κ e' σ' efs :
  machine_step conf interp UnknownExpr σ κ e' σ' efs ->
  κ = [] /\ e' = UnknownExpr /\
    σ'.(radium_state) = σ.(radium_state) /\ efs = [].
Proof. inversion 1; subst. repeat split; done. Qed.

Example radium_expr_steps_require_runtime_step {low_level_state : Type}
    (conf : RadiumConfig) (interp : event_interp low_level_state)
    e σ κ e2 σ2 efs :
  machine_step conf interp (RadiumExpr e) σ κ e2 σ2 efs ->
  ∃ K redex events redex' redex_efs,
    e = machine_fill conf K redex /\
    runtime_step conf redex σ.(radium_state) events redex'
      σ2.(radium_state) redex_efs.
Proof.
  intros Hstep. inversion Hstep; subst.
  eexists _, _, _, _, _. split; first done.
  eassumption.
Qed.
