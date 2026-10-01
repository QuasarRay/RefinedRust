From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_double_ended_DoubleEndedIterator_try_rfold.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Ltac hooks.solve_goal_final_hook ::=
  try congruence;
  refined_solver lia
.

Lemma traits_double_ended_DoubleEndedIterator_try_rfold_proof (π : thread_id) :
  traits_double_ended_DoubleEndedIterator_try_rfold_lemma π.
Proof.
  traits_double_ended_DoubleEndedIterator_try_rfold_prelude.

  rep liRStep.
  liInst Hevar_x2 self.
  liInst Hevar_seq [].
  1: rep <-! <3000 liRStep.

  2: {
    1: rep <-! <3000 liRStep.
    rep liRStep.
    liInst Hevar_x1 seq.
    liInst Hevar_x2 x8.
    rep liRStep.
    rewrite branchfn_from_output_eq.
    liInst Hevar_x3 x10.
    rep liRStep.
  }

  liShow.
  iRename select (∀ _ _ _ _, _)%I into "Hstep".
  iPoseProof ("Hstep" with "[$] [$] [$]") as "(%pclos & Hpre & Hnext & ? & Hcl)".
  1: rep <-! <3000 liRStep; liShow.
  { rep liRStep; liShow.
    rename select (Try_BranchFn _ _ = inl _) into Heq. rewrite Heq.
    rep liRStep; liShow.
    liInst Hevar_x x'1.
    iPoseProof ("Hcl" with "[$]") as "[Ha _]".
    iRevert "Ha".
    rewrite Heq.
    rep liRStep; liShow. }
  { 1: rep <-! <3000 liRStep; liShow.
    rename select (Try_BranchFn _ _ = inr _) into Heq. rewrite Heq.
    1: rep <-! <3000 liRStep; liShow.
    iPoseProof ("Hcl" with "[$]") as "[Ha _]".
    iRevert "Ha".
    rewrite Heq.
    1: rep <-! <3000 liRStep; liShow.
    rep liRStep; liShow.
    liInst Hevar_x2 x'.
    liInst Hevar_x x'1.
    rep liRStep; liShow.
    rename select (Try_BranchFn _ _ = _) into Hbranch.
    rewrite Hbranch.
    liInst Hevar_x3 x'0.
    rep liRStep.
  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
