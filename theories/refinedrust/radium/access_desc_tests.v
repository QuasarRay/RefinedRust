From radium Require Import notation.

(** Regression tests for memory-access descriptor preservation. *)

Example copy_syntax_preserves_desc desc ot o e :
  (copy{ot, o, desc} e)%E = Deref desc o ot (SkipE e).
Proof. reflexivity. Qed.

Example assign_syntax_preserves_desc desc ot o e1 e2 s :
  (e1 <-{ot, o, desc} e2; s)%E =
    Assign desc o ot (SkipE (SkipE e1)) e2 s.
Proof. reflexivity. Qed.

Example deref_first_phase_preserves_desc desc ot v π σ events e' σ' efs :
  expr_step (Deref desc Na1Ord ot (Val v)) π σ events e' σ' efs ->
  e' = to_rtexpr π (Deref desc Na2Ord ot (Val v)).
Proof. inversion 1. reflexivity. Qed.

Example assign_first_phase_preserves_desc desc ot v1 v2 s π rf σ events e' σ' efs :
  stmt_step (Assign desc Na1Ord ot (Val v1) (Val v2) s)
    π rf σ events e' σ' efs ->
  e' = to_rtstmt π rf (Assign desc Na2Ord ot (Val v1) (Val v2) s).
Proof. inversion 1. reflexivity. Qed.

Example atomic_deref_does_not_use_nonatomic_rule ot v π σ events e' σ' efs :
  ¬ expr_step (Deref normal_atomic_access ScOrd ot (Val v))
      π σ events e' σ' efs.
Proof. inversion 1. discriminate. Qed.

Example atomic_assign_does_not_use_nonatomic_rule ot v1 v2 s π rf σ events e' σ' efs :
  ¬ stmt_step (Assign normal_atomic_access ScOrd ot (Val v1) (Val v2) s)
      π rf σ events e' σ' efs.
Proof. inversion 1. discriminate. Qed.
