(** Physical-step credits backed by a linear receipt supply and finite escrow.
    Issuance is a transfer from the adequacy driver's private stock, not an
    update exported by this module. *)
From iris.algebra Require Import auth numbers.
From iris.proofmode Require Import proofmode.
From radium.physical_step Require Export physical_step logical_step.
From iris.prelude Require Import options.
Import uPred.

Section accounting.
  Context `{!tr_generation}.
  Definition step_credit_next s := s + tr_f (1 + 2*s).
  Definition step_credit_cost s := tr_f (1 + 2*s) + S (tr_f (2*s)).
  Fixpoint step_credit_reserve s c :=
    match c with
    | 0 => 0
    | S c => step_credit_cost s + step_credit_reserve (step_credit_next s) c
    end.
  Lemma step_credit_reserve_linear (Hlinear : ∀ n, tr_f n = 5*n) s c :
    step_credit_reserve s c + 4*c + (2*s+1) = (2*s+1)*11^c.
  Proof.
    revert s. induction c as [|c IH]; intros s; first by simpl; lia.
    cbn [step_credit_reserve]. specialize (IH (step_credit_next s)).
    rewrite /step_credit_cost /step_credit_next !Hlinear in IH |- *.
    rewrite Nat.pow_succ_r'. nia.
  Qed.
End accounting.

Definition step_creditUR := authUR natUR.
Class step_creditGpreS (Σ : gFunctors) := StepCreditGpreS {
  #[local] step_creditGpreS_inG :: inG Σ step_creditUR;
}.
Class step_creditGS (Σ : gFunctors) := StepCreditGS {
  #[local] step_creditGS_inG :: inG Σ step_creditUR;
  step_credit_name : gname;
}.
Definition step_creditΣ := #[GFunctor step_creditUR].
Global Instance subG_step_creditΣ {Σ} : subG step_creditΣ Σ → step_creditGpreS Σ.
Proof. solve_inG. Qed.

Section tokens.
  Context `{!step_creditGS Σ}.
  Definition step_credit n : iProp Σ := own step_credit_name (◯ n).
  Global Instance step_credit_timeless n : Timeless (step_credit n) := _.
  Lemma step_credit_split n m :
    step_credit (n+m) ⊣⊢ step_credit n ∗ step_credit m.
  Proof. by rewrite /step_credit -own_op -auth_frag_op nat_op. Qed.
  Lemma step_credit_zero : ⊢ |==> step_credit 0.
  Proof. apply own_unit. Qed.
End tokens.

Section bank.
  Context `{!invGS Σ, !trGS Σ, !step_creditGS Σ, !tr_generation}.
  Definition step_credit_state : iProp Σ :=
    ∃ s c, own step_credit_name (● c) ∗ tr_supply s 0 ∗
      £ (step_credit_reserve s c).
  Definition step_credit_update E (P : iProp Σ) : iProp Σ :=
    step_credit_state -∗ |={E}=> step_credit_state ∗ P.

  Lemma step_credit_update_intro E P : P -∗ step_credit_update E P.
  Proof. iIntros "HP Hbank". by iFrame. Qed.
  Lemma step_credit_update_bind E P Q :
    step_credit_update E P -∗ (P -∗ step_credit_update E Q) -∗
    step_credit_update E Q.
  Proof.
    iIntros "Hupd Hcont Hbank". iMod ("Hupd" with "Hbank") as "[Hbank HP]".
    iApply ("Hcont" with "HP Hbank").
  Qed.
  Lemma step_credit_redeem E P :
    step_credit 1 -∗ physical_step E P -∗ step_credit_update E P.
  Proof.
    iIntros "Hcredit Hraw Hbank".
    iDestruct "Hbank" as (s c) "(Hauth & Hsupply & Hreserve)".
    iDestruct (own_valid_2 with "Hauth Hcredit") as %Hvalid.
    apply auth_both_valid_discrete in Hvalid as [Hincl _].
    apply nat_included in Hincl. destruct c as [|c]; first lia.
    iAssert (|==> own step_credit_name (● c))%I with "[Hauth Hcredit]" as ">Hauth".
    { iApply (own_update_2 with "Hauth Hcredit").
      apply auth_update_dealloc, nat_local_update.
      change (S c + 0 = c + 1). lia. }
    cbn [step_credit_reserve]. iDestruct "Hreserve" as "[Hcost Hreserve]".
    iMod (physical_step_execute with "Hsupply Hcost Hraw") as "[Hsupply HP]".
    iModIntro. iFrame "HP". iExists (step_credit_next s), c. iFrame.
  Qed.
  Lemma step_credit_redeem_logical E P :
    step_credit 1 -∗ logical_step.logical_step E P -∗ step_credit_update E P.
  Proof.
    iIntros "Hcredit Hlogical". iApply (step_credit_redeem with "Hcredit").
    iApply (physical_step_step_upd with "Hlogical").
    iApply physical_step_intro. by iNext; iIntros "$".
  Qed.
  (** Two-credit replacement of a one-credit, raw-step continuation. *)
  Lemma step_credit_wrapper E P :
    (step_credit 1 -∗ step_credit_update E (physical_step E P)) -∗
    step_credit 2 -∗ step_credit_update E P.
  Proof.
    iIntros "Hwrapper Hcredits Hbank".
    change 2 with (1+1). rewrite step_credit_split.
    iDestruct "Hcredits" as "[Hissued Hexecute]".
    iMod ("Hwrapper" with "Hissued Hbank") as "[Hbank Hraw]".
    iApply (step_credit_redeem with "Hexecute Hraw Hbank").
  Qed.
End bank.

Lemma step_credit_state_alloc `{!invGS Σ, !trGS Σ, !step_creditGpreS Σ,
    !tr_generation} s c :
  tr_supply s 0 -∗ £ (step_credit_reserve s c) ==∗
  ∃ _ : step_creditGS Σ, step_credit_state ∗ step_credit c.
Proof using All.
  iIntros "Hsupply Hreserve".
  iMod (own_alloc (● c ⋅ ◯ c)) as (γ) "[Hauth Hstock]".
  { apply auth_both_valid_discrete. split; done. }
  pose (Hcredits := StepCreditGS Σ _ γ). iExists Hcredits. iModIntro.
  iFrame "Hstock". iExists s, c. iFrame.
Qed.

(** Finite backing is allocated before the client proof, but only the caller
    of this theorem sees the future stock. In particular allocation/issuance
    is not a state-preserving update available to the client. *)
Lemma step_credit_soundness Σ `{!invGpreS Σ, !trGpreS Σ,
    !step_creditGpreS Σ, !tr_generation} c g (P : iProp Σ) `{!Plain P} :
  (∀ `{!invGS Σ, !trGS Σ, !step_creditGS Σ},
    step_credit_state -∗ step_credit c -∗ £ g -∗ |={⊤,∅}=> P) → ⊢ P.
Proof.
  intros Hproof. apply (fupd_soundness HasLc (step_credit_reserve 0 c + g) ⊤ ∅);
    first apply _.
  intros Hinv. iIntros "[Hreserve Hguards]".
  iMod (tr_supply_alloc 0) as (Htr) "Hsupply".
  iMod (step_credit_state_alloc with "Hsupply Hreserve") as (Hcredits) "[Hbank Hstock]".
  iApply (Hproof with "Hbank Hstock Hguards").
Qed.
