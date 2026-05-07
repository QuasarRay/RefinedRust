From refinedrust_extract_goal Require Import plugin.

Set Nested Proofs Allowed.

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

Theorem extract_goal_open_smoke : forall x y : nat, x = y -> y = x.
Proof.
  intros x y H.
  Extract Goal as nested_symmetry_subgoal.
  Open Extracted Goal nested_symmetry_subgoal.
  Proof.
    intros x y H.
    symmetry.
    exact H.
  Qed.
  Use Extracted Goal nested_symmetry_subgoal.
Qed.

Check nested_symmetry_subgoal.

Theorem extract_goal_open_anonymous_smoke : forall n : nat, n = n.
Proof.
  intro n.
  Extract Goal.
  Open Extracted Goal.
  Proof.
    intro n.
    exact eq_refl.
  Qed.
  Use Last Extracted Goal.
Qed.

Theorem extract_goal_open_defined_initial_smoke : forall n : nat, n = n.
Proof.
  intro n.
  Extract Goal as nested_defined_subgoal.
  Open Extracted Goal nested_defined_subgoal.
  Proof.
    intro n.
    exact eq_refl.
  Defined.
  Use Extracted Goal nested_defined_subgoal.
Qed.

Check nested_defined_subgoal.

Theorem extract_goal_open_after_abort_initial_smoke : forall n : nat, n = n.
Proof.
  intro n.
  Extract Goal as nested_aborted_subgoal.
  Open Extracted Goal nested_aborted_subgoal.
  Proof.
    intro n.
  Abort.
  exact eq_refl.
Qed.

Theorem extract_goal_open_sequential_left_smoke :
  forall x y : nat, x = y -> y = x.
Proof.
  intros x y H.
  Extract Goal as nested_seq_left.
  Open Extracted Goal nested_seq_left.
  Proof.
    intros x y H.
    symmetry.
    exact H.
  Qed.
  Use Extracted Goal nested_seq_left.
Qed.

Theorem extract_goal_open_sequential_right_smoke : forall n : nat, n = n.
Proof.
  intro n.
  Extract Goal as nested_seq_right.
  Open Extracted Goal nested_seq_right.
  Proof.
    intro n.
    exact eq_refl.
  Qed.
  Use Extracted Goal nested_seq_right.
Qed.

Section OpenInitialSection.
  Variable z : nat.

  Theorem extract_goal_open_initial_section_smoke : z = z.
  Proof.
    Extract Goal as nested_section_subgoal.
    Open Extracted Goal nested_section_subgoal.
    Proof.
      intro z'.
      exact eq_refl.
    Qed.
    Use Extracted Goal nested_section_subgoal.
  Qed.

  Check nested_section_subgoal.
End OpenInitialSection.

Check nested_section_subgoal.

Theorem extract_goal_open_split_smoke :
  (forall x y : nat, x = y -> y = x) /\ (forall n : nat, n = n).
Proof.
  split.
  - intros x y H.
    Extract Goal as prepared_split_left.
    Open Extracted Goal prepared_split_left.
    Proof.
      intros x y H.
      symmetry.
      exact H.
    Qed.
    Use Extracted Goal prepared_split_left.
  - intro n.
    Extract Goal as prepared_split_right.
    Open Extracted Goal prepared_split_right.
    Proof.
      intro n.
      exact eq_refl.
    Qed.
    Use Extracted Goal prepared_split_right.
Qed.

Check prepared_split_left.
Check prepared_split_right.

Theorem extract_goal_open_defined_smoke : forall n : nat, n = n.
Proof.
  intro n.
  Extract Goal as prepared_defined_subgoal.
  Open Extracted Goal prepared_defined_subgoal.
  Proof.
    intro n.
    exact eq_refl.
  Defined.
  Use Extracted Goal prepared_defined_subgoal.
Qed.

Check prepared_defined_subgoal.

Theorem extract_goal_open_after_abort_smoke : forall n : nat, n = n.
Proof.
  intro n.
  Extract Goal as prepared_aborted_subgoal.
  Open Extracted Goal prepared_aborted_subgoal.
  Proof.
    intro n.
  Abort.
  exact eq_refl.
Qed.

Theorem extract_goal_open_reuse_smoke : forall n : nat, n = n /\ n = n.
Proof.
  intro n.
  Extract Goal as prepared_reuse_subgoal.
  Open Extracted Goal prepared_reuse_subgoal.
  Proof.
    intro n.
    split; exact eq_refl.
  Qed.
  Use Extracted Goal prepared_reuse_subgoal.
Qed.

Theorem extract_goal_open_use_last_smoke : forall n : nat, n = n.
Proof.
  intro n.
  Extract Goal as prepared_use_last_subgoal.
  Open Extracted Goal prepared_use_last_subgoal.
  Proof using Type*.
    intro n.
    exact eq_refl.
  Qed.
  Use Last Extracted Goal.
Qed.

Theorem extract_goal_open_use_last_stack_smoke : forall n : nat, n = n /\ n = n.
Proof.
  intro n.
  Extract Goal as prepared_use_last_outer_subgoal.
  Open Extracted Goal prepared_use_last_outer_subgoal.
  Proof using Type*.
    intro n.
    split.
    - Extract Goal as prepared_use_last_inner_subgoal.
      Open Extracted Goal prepared_use_last_inner_subgoal.
      Proof using Type*.
        intro n.
        exact eq_refl.
      Qed.
      Use Last Extracted Goal.
    - exact eq_refl.
  Qed.
  Use Last Extracted Goal.
Qed.

Theorem extract_goal_open_three_way_split_smoke :
  (forall n : nat, n = n) /\
  (forall x y : nat, x = y -> y = x) /\
  (forall n : nat, n = n).
Proof.
  split.
  - intro n.
    Extract Goal as prepared_three_left.
    Open Extracted Goal prepared_three_left.
    Proof.
      intro n.
      exact eq_refl.
    Qed.
    Use Extracted Goal prepared_three_left.
  - split.
    + intros x y H.
      Extract Goal as prepared_three_middle.
      Open Extracted Goal prepared_three_middle.
      Proof.
        intros x y H.
        symmetry.
        exact H.
      Qed.
      Use Extracted Goal prepared_three_middle.
    + intro n.
      Extract Goal as prepared_three_right.
      Open Extracted Goal prepared_three_right.
      Proof.
        intro n.
        exact eq_refl.
      Qed.
      Use Extracted Goal prepared_three_right.
Qed.

Section OpenExtractedSection.
  Variable a : nat.

  Theorem extract_goal_open_section_smoke : a = a.
  Proof.
    Extract Goal as prepared_section_subgoal.
    Open Extracted Goal prepared_section_subgoal.
    Proof.
      intro a'.
      exact eq_refl.
    Qed.
    Use Extracted Goal prepared_section_subgoal.
  Qed.

  Check prepared_section_subgoal.
End OpenExtractedSection.

Check prepared_section_subgoal.
