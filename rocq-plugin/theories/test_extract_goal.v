From refinedrust_extract_goal Require Import plugin.

Goal True.
Proof.
  exact I.
Qed.

Theorem extract_goal_smoke : forall x y : nat, x = y -> y = x.
Proof.
  intros x y H.
  Extract Goal as symmetry_subgoal.
Abort.

Lemma symmetry_subgoal : forall x y : nat, x = y -> y = x.
Proof.
  intros x y H.
  symmetry.
  exact H.
Qed.

Theorem use_extracted_goal_smoke : forall x y : nat, x = y -> y = x.
Proof.
  intros x y H.
  Use Extracted Goal symmetry_subgoal.
Qed.
