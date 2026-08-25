From iris.program_logic Require Export ectxi_language.
From radium Require Export lang.
Set Default Proof Using "Type".

(** Can later be extended with expressions from other languages. *)
Inductive machine_expr :=
 (* Lift a Radium expression to the machine level *)
 | RadiumExpr (e : radium.lang.runtime_expr)
 (* Model other executables mutating the low-level state. *)
 | UnknownExpr
.

Definition machine_to_val (e : machine_expr) : option runtime_result :=
  match e with
    RadiumExpr e => to_val e
  | UnknownExpr => None
  end.

Definition machine_of_val (v : runtime_result) : machine_expr :=
  RadiumExpr (of_val v).

Definition machine_fill (conf : RadiumConfig) (K : list lang_ectx)
    (e : runtime_expr) : ectxi_language.expr c_ectxi_lang :=
  @ectxi_language.fill (@c_ectxi_lang conf) K e.

Definition machine_context_fill (conf : RadiumConfig) (K : list lang_ectx)
    (e : machine_expr) : machine_expr :=
  match e with
  | RadiumExpr e => RadiumExpr (machine_fill conf K e)
  | UnknownExpr => UnknownExpr
  end.

Lemma machine_fill_app conf K1 K2 e :
  machine_fill conf (K1 ++ K2) e = machine_fill conf K2 (machine_fill conf K1 e).
Proof. apply ectxi_language.fill_app. Qed.

Record machine_state (low_level_state : Type) := {
  low_state : low_level_state;
  radium_state : radium.lang.state;
}.
Arguments low_state {_} _.
Arguments radium_state {_} _.

(** Interpretation of one Radium event on a lower-level machine state. *)
Definition event_interp (low_level_state : Type) :=
  low_level_state -> radium_event -> low_level_state -> Prop.

(** Sequential interpretation of the events produced by one Radium step. *)
Inductive interpret_events {low_level_state : Type} (interp : event_interp low_level_state) :
    low_level_state -> list radium_event -> low_level_state -> Prop :=
  | InterpretEventsNil σ :
      interpret_events interp σ [] σ
  | InterpretEventsCons σ1 σ2 σ3 event events :
      interp σ1 event σ2 ->
      interpret_events interp σ2 events σ3 ->
      interpret_events interp σ1 (event :: events) σ3.

Inductive machine_step {low_level_state : Type} (conf : RadiumConfig)
    (interp : event_interp low_level_state) :
 machine_expr -> machine_state low_level_state -> list Empty_set ->
 machine_expr -> machine_state low_level_state -> list machine_expr -> Prop :=
 | RadiumStep K σ σ' e events e' efs :
   runtime_step conf e σ.(radium_state) events e' σ'.(radium_state) efs ->
   interpret_events interp σ.(low_state) events σ'.(low_state) ->
   machine_step conf interp
     (RadiumExpr (machine_fill conf K e )) σ []
     (RadiumExpr (machine_fill conf K e')) σ'
     (RadiumExpr <$> efs)
 | EnvStep s low low' :
    machine_step conf interp
      UnknownExpr {| low_state := low ; radium_state := s |} []
      UnknownExpr {| low_state := low'; radium_state := s |} []
 .

Section machine_language.
Context {low_level_state : Type} (conf : RadiumConfig)
  (interp : event_interp low_level_state).

Lemma machine_lang_mixin :
  LanguageMixin machine_of_val machine_to_val (machine_step conf interp).
Proof.
  split.
  - intros []; done.
  - intros [e|] v Hv.
    + cbn [machine_to_val] in Hv. unfold machine_of_val.
      f_equal. by eapply of_to_val.
    + inversion Hv.
  - intros [e|] σ κ [e'|] σ' efs Hstep; inversion Hstep; subst.
    + cbn [machine_fill machine_to_val].
      apply ectx_language.fill_not_val. by eapply val_stuck.
    + done.
Qed.

Canonical Structure machine_lang := Language machine_lang_mixin.

End machine_language.

Global Instance machine_context_fill_ctx {low_level_state : Type}
    (conf : RadiumConfig) (interp : event_interp low_level_state) K :
    @LanguageCtx (machine_lang conf interp) (machine_context_fill conf K).
Proof.
  split.
  - intros [e|] Hval; cbn [machine_context_fill machine_to_val] in *.
    + by apply ectx_language.fill_not_val.
    + done.
  - intros e1 σ1 κ e2 σ2 efs Hstep. inversion Hstep; subst.
    + cbn [machine_context_fill machine_fill].
      rewrite -!machine_fill_app.
      by eapply RadiumStep.
    + apply EnvStep.
  - intros [e|] σ1 κ e2 σ2 efs Hval Hstep.
    + inversion Hstep; subst.
      assert (Hprim : @language.prim_step (c_lang conf)
        (machine_fill conf K e) σ1.(radium_state) events
        (machine_fill conf K0 e') σ2.(radium_state) efs0).
      { eapply ectx_language.Ectx_step with
          (K := K0) (e1' := e0) (e2' := e'); [symmetry; done | done | done]. }
      change (to_val e = None) in Hval.
      destruct (@language.fill_step_inv (c_lang conf) (machine_fill conf K) _
        e σ1.(radium_state) events (machine_fill conf K0 e')
        σ2.(radium_state) efs0 Hval Hprim) as (e2' & Heq & Hprim').
      exists (RadiumExpr e2'). split.
      { cbn [machine_context_fill]. by f_equal. }
      inversion Hprim' as [K' e1' e2'' Hfill1 Hfill2 Hbase].
      rewrite Hfill1 Hfill2.
      by eapply RadiumStep.
    + inversion Hstep; subst. exists UnknownExpr. split; first done. apply EnvStep.
Qed.
