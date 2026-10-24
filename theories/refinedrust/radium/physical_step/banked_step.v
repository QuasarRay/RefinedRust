(** Finite-horizon models of banked logical-step elimination.

    The existing [physical_step] is the raw, non-issuing transformer. An actual
    step receives a credit from the adequacy driver, outside that transformer.
    [bank_state] and [stateful_actual_step] support a linear state-threaded
    interpretation without an invariant. [step_bank] and [actual_step] retain
    the earlier invariant-backed variant for comparison. See
    [banked_step_model.md] and [../program_logic/stateful_wp_model.md]. *)
From iris.algebra Require Import auth numbers.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From radium.physical_step Require Export physical_step logical_step.
From iris.prelude Require Import options.
Import uPred.

Section accounting.
  Context `{!tr_generation}.

  Definition bank_next (s : nat) : nat := s + tr_f (1 + 2*s).
  Definition bank_cost (s : nat) : nat :=
    tr_f (1 + 2*s) + S (tr_f (2*s)).

  Fixpoint bank_reserve (s h : nat) : nat :=
    match h with
    | 0 => 0
    | S h => bank_cost s + bank_reserve (bank_next s) h
    end.

  Lemma bank_reserve_step s h :
    bank_reserve s (S h) = bank_cost s + bank_reserve (bank_next s) h.
  Proof. done. Qed.

  (** Exact growth for RefinedRust's current [tr_f n = 5*n]. This form avoids
      truncated subtraction in the closed-form expression for the reserve. *)
  Lemma bank_reserve_linear (Hlinear : ∀ n, tr_f n = 5*n) s h :
    bank_reserve s h + 4*h + (2*s + 1) = (2*s + 1) * 11^h.
  Proof.
    revert s. induction h as [|h IH]; intros s.
    - cbn [bank_reserve Nat.pow]. lia.
    - rewrite bank_reserve_step. specialize (IH (bank_next s)).
      rewrite /bank_cost /bank_next !Hlinear in IH |- *.
      rewrite Nat.pow_succ_r'. nia.
  Qed.
End accounting.

(** The two coordinates are remaining real-step permits and remaining banked
    credits, respectively. Only the driver owns real-step permits. Initially it
    also owns the entire stock of banked credits, releasing one per reduction. *)
Definition bankUR := authUR (prodUR natUR natUR).

Class bankGpreS (Σ : gFunctors) := BankGpreS {
  #[local] bankGpreS_inG :: inG Σ bankUR;
}.
Class bankGS (Σ : gFunctors) := BankGS {
  #[local] bankGS_inG :: inG Σ bankUR;
  bank_name : gname;
}.
Definition bankΣ := #[GFunctor bankUR].
Global Instance subG_bankΣ {Σ} : subG bankΣ Σ → bankGpreS Σ.
Proof. solve_inG. Qed.

Section model.
  Context `{!invGS Σ, !trGS Σ, !bankGS Σ, !tr_generation}.

  (** [true] selects private real-step permits; [false] selects public credits. *)
  Local Definition bank_token (real : bool) (n : nat) : iProp Σ :=
    own bank_name (◯ (if real then (n, 0) else (0, n))).
  Definition real_step_permit (n : nat) : iProp Σ := bank_token true n.
  Definition step_credit (n : nat) : iProp Σ := bank_token false n.

  Definition bank_state : iProp Σ :=
    ∃ s q c, own bank_name (● (q, c)) ∗ tr_supply s 0 ∗
      £ (bank_reserve s (q + c)).
  Local Definition bank_inv : iProp Σ := bank_state.
  Definition step_bank (N : namespace) : iProp Σ := inv N bank_inv.

  (** Issuance is an INPUT supplied once by the operational-step driver. It is
      deliberately outside the raw transformer used by [logical_step]. *)
  Definition actual_step (N : namespace) (E : coPset) (P : iProp Σ) : iProp Σ :=
    step_credit 1 -∗ |={E ∪ ↑N}=> physical_step E P.

  Global Instance step_credit_timeless n : Timeless (step_credit n) := _.
  Global Instance real_step_permit_timeless n : Timeless (real_step_permit n) := _.
  Global Instance step_bank_persistent N : Persistent (step_bank N) := _.

  Local Lemma bank_token_split real n m :
    bank_token real (n + m) ⊣⊢ bank_token real n ∗ bank_token real m.
  Proof.
    rewrite /bank_token -own_op -auth_frag_op.
    by destruct real.
  Qed.

  Lemma step_credit_split n m :
    step_credit (n + m) ⊣⊢ step_credit n ∗ step_credit m.
  Proof. apply bank_token_split. Qed.

  Lemma real_step_permit_split n m :
    real_step_permit (n + m) ⊣⊢ real_step_permit n ∗ real_step_permit m.
  Proof. apply bank_token_split. Qed.

  (** Linear, state-threaded execution. No invariant or mask condition is
      involved; [bank_state] owns the single authoritative receipt supply. *)
  Local Lemma bank_state_run E real P :
    bank_state -∗ bank_token real 1 -∗ physical_step E P
      ={E}=∗ bank_state ∗ P.
  Proof.
    iIntros "Hbank Htoken Hstep".
    iDestruct "Hbank" as (s q c) "(Hauth & Hsup & Hreserve)".
    rewrite /bank_token.
    iDestruct (own_valid_2 with "Hauth Htoken") as %Hvalid.
    apply auth_both_valid_discrete in Hvalid as [Hincl _].
    apply prod_included in Hincl as [Hq Hc].
    apply nat_included in Hq, Hc.
    destruct real.
    - destruct q as [|q]; first (simpl in Hq; lia).
      iAssert (|==> own bank_name (● (q, c)))%I with "[Hauth Htoken]" as ">Hauth".
      { iApply (own_update_2 with "Hauth Htoken").
        apply auth_update_dealloc, prod_local_update; apply nat_local_update.
        - change (S q + 0 = q + 1). lia.
        - change (c + 0 = c + 0). done. }
      replace (S q + c) with (S (q + c)) by lia.
      rewrite bank_reserve_step.
      iDestruct "Hreserve" as "[Hcost Hreserve]".
      iMod (physical_step_execute with "Hsup Hcost Hstep") as "[Hsup HP]".
      iModIntro. iFrame "HP". iExists (bank_next s), q, c. iFrame.
    - destruct c as [|c]; first (simpl in Hc; lia).
      iAssert (|==> own bank_name (● (q, c)))%I with "[Hauth Htoken]" as ">Hauth".
      { iApply (own_update_2 with "Hauth Htoken").
        apply auth_update_dealloc, prod_local_update; apply nat_local_update.
        - change (q + 0 = q + 0). done.
        - change (S c + 0 = c + 1). lia. }
      replace (q + S c) with (S (q + c)) by lia.
      rewrite bank_reserve_step.
      iDestruct "Hreserve" as "[Hcost Hreserve]".
      iMod (physical_step_execute with "Hsup Hcost Hstep") as "[Hsup HP]".
      iModIntro. iFrame "HP". iExists (bank_next s), q, c. iFrame.
  Qed.

  Lemma bank_state_redeem E P :
    bank_state -∗ step_credit 1 -∗ physical_step E P
      ={E}=∗ bank_state ∗ P.
  Proof. apply (bank_state_run E false). Qed.

  Lemma bank_state_real_step E P :
    bank_state -∗ real_step_permit 1 -∗ physical_step E P
      ={E}=∗ bank_state ∗ P.
  Proof. apply (bank_state_run E true). Qed.

  Definition bank_update (E : coPset) (P : iProp Σ) : iProp Σ :=
    bank_state -∗ |={E}=> bank_state ∗ P.

  Lemma bank_update_intro E P : P -∗ bank_update E P.
  Proof. iIntros "HP Hbank". by iFrame. Qed.

  Lemma bank_update_bind E P Q :
    bank_update E P -∗ (P -∗ bank_update E Q) -∗ bank_update E Q.
  Proof.
    iIntros "Hupd Hcont Hbank". iMod ("Hupd" with "Hbank") as "[Hbank HP]".
    iApply ("Hcont" with "HP Hbank").
  Qed.

  Lemma bank_update_logical_step E P :
    step_credit 1 -∗ logical_step.logical_step E P -∗ bank_update E P.
  Proof.
    iIntros "Hcredit Hlogical Hbank".
    iApply (bank_state_redeem with "Hbank Hcredit").
    iApply (physical_step_step_upd with "Hlogical").
    iApply physical_step_intro. by iNext; iIntros "$".
  Qed.

  (** The outer bank update permits further redemptions before the receipt
      supply is lent to the non-issuing raw step. There is no namespace. *)
  Definition stateful_actual_step (E : coPset) (P : iProp Σ) : iProp Σ :=
    step_credit 1 -∗ bank_update E (physical_step E P).

  Global Instance stateful_actual_step_contractive E :
    Contractive (stateful_actual_step E).
  Proof.
    intros n P Q HPQ. rewrite /stateful_actual_step /bank_update.
    do 4 f_equiv. by f_contractive.
  Qed.

  Lemma stateful_actual_step_intro E P :
    physical_step E P -∗ stateful_actual_step E P.
  Proof. iIntros "Hraw _". by iApply bank_update_intro. Qed.

  Lemma stateful_actual_step_credit E :
    ⊢ stateful_actual_step E (step_credit 1).
  Proof.
    iIntros "Hcredit". iApply bank_update_intro.
    iApply physical_step_intro. by iNext.
  Qed.

  Lemma stateful_actual_step_logical_step E P Q :
    logical_step.logical_step E P -∗
    stateful_actual_step E (P -∗ Q) -∗ stateful_actual_step E Q.
  Proof.
    iIntros "Hlogical Hactual Hcredit Hbank".
    iMod ("Hactual" with "Hcredit Hbank") as "[Hbank Hraw]".
    iModIntro. iFrame "Hbank".
    iApply (physical_step_step_upd with "Hlogical Hraw").
  Qed.

  Lemma stateful_actual_step_run E P :
    bank_state -∗ real_step_permit 1 -∗ step_credit 1 -∗
    stateful_actual_step E P ={E}=∗ bank_state ∗ P.
  Proof.
    iIntros "Hbank Hpermit Hcredit Hactual".
    iMod ("Hactual" with "Hcredit Hbank") as "[Hbank Hraw]".
    iApply (bank_state_real_step with "Hbank Hpermit Hraw").
  Qed.

  Lemma stateful_actual_step_spend E P Q :
    logical_step.logical_step E P -∗
    (P -∗ physical_step E Q) -∗ stateful_actual_step E Q.
  Proof.
    iIntros "Hlogical Hcont Hcredit Hbank".
    iMod (bank_update_logical_step with "Hcredit Hlogical Hbank") as "[Hbank HP]".
    iModIntro. iFrame "Hbank". iApply ("Hcont" with "HP").
  Qed.

  Lemma actual_step_intro N E P : ▷ P -∗ actual_step N E P.
  Proof. iIntros "HP _". iModIntro. by iApply physical_step_intro. Qed.

  Lemma actual_step_credit N E : ⊢ actual_step N E (step_credit 1).
  Proof. iIntros "Hcredit". iModIntro. iApply physical_step_intro. by iNext. Qed.

  Lemma actual_step_wand N E P Q :
    actual_step N E P -∗ (P -∗ Q) -∗ actual_step N E Q.
  Proof.
    iIntros "Hstep Hwand Hcredit".
    iMod ("Hstep" with "Hcredit") as "Hraw". iModIntro.
    iApply (physical_step_wand with "Hraw Hwand").
  Qed.

  Lemma actual_step_logical_step N E P Q :
    logical_step.logical_step E P -∗
    actual_step N E (P -∗ Q) -∗ actual_step N E Q.
  Proof.
    iIntros "Hlogical Hactual Hcredit".
    iMod ("Hactual" with "Hcredit") as "Hraw". iModIntro.
    iApply (physical_step_step_upd with "Hlogical Hraw").
  Qed.

  Global Instance actual_step_contractive N E : Contractive (actual_step N E).
  Proof. intros n P Q HPQ. rewrite /actual_step. do 2 f_equiv. by f_contractive. Qed.

  Lemma actual_step_fupd N E P :
    (|={E ∪ ↑N}=> actual_step N E P) -∗ actual_step N E P.
  Proof.
    iIntros "Hupdate Hcredit". iMod "Hupdate" as "Hactual".
    iApply ("Hactual" with "Hcredit").
  Qed.

  (** The bank namespace must stay outside the raw step's mask. We return to
      the ambient mask only after closing the bank, before exposing [P]. *)
  Local Lemma bank_run N E real P :
    E ## ↑N →
    step_bank N -∗ bank_token real 1 -∗ physical_step E P
      ={E ∪ ↑N}=∗ P.
  Proof.
    iIntros (Hdisj) "#Hbank Htoken Hstep".
    iInv N as ">Hstate" "Hclose".
    assert ((E ∪ ↑N) ∖ ↑N = E) as Heq by set_solver.
    rewrite Heq.
    iMod (bank_state_run with "Hstate Htoken Hstep") as "[Hstate HP]".
    iMod ("Hclose" with "[Hstate]") as "_"; first by iNext.
    done.
  Qed.

  Lemma step_credit_elim_raw N E P :
    E ## ↑N →
    step_bank N -∗ step_credit 1 -∗ physical_step E P
      ={E ∪ ↑N}=∗ P.
  Proof. apply (bank_run N E false). Qed.

  Lemma step_credit_elim_logical N E P :
    E ## ↑N →
    step_bank N -∗ step_credit 1 -∗ logical_step.logical_step E P
      ={E ∪ ↑N}=∗ P.
  Proof.
    iIntros (Hdisj) "#Hbank Hcredit Hlogical".
    iApply (step_credit_elim_raw with "Hbank Hcredit"); first done.
    iApply (physical_step_step_upd with "Hlogical").
    iApply physical_step_intro. by iNext; iIntros "$".
  Qed.

  (** Driver-only execution: the credit argument comes from its private stock,
      and the permit is consumed. There is no raw-step rule producing either. *)
  Lemma actual_step_run N E P :
    E ## ↑N →
    step_bank N -∗ real_step_permit 1 -∗ step_credit 1 -∗ actual_step N E P
      ={E ∪ ↑N}=∗ P.
  Proof.
    iIntros (Hdisj) "#Hbank Hpermit Hcredit Hactual".
    iMod ("Hactual" with "Hcredit") as "Hraw".
    iApply (bank_run N E true with "Hbank Hpermit Hraw"); done.
  Qed.

  Lemma actual_step_runN N E k P :
    E ## ↑N →
    step_bank N -∗ real_step_permit k -∗ step_credit k -∗
    Nat.iter k (actual_step N E) P ={E ∪ ↑N}=∗ P.
  Proof.
    iIntros (Hdisj) "#Hbank Hpermits Hcredits Hsteps".
    iInduction k as [|k] "IH" forall (P); first by iFrame.
    replace (S k) with (1 + k) by lia.
    rewrite real_step_permit_split step_credit_split.
    iDestruct "Hpermits" as "[Hpermit Hpermits]".
    iDestruct "Hcredits" as "[Hcredit Hcredits]".
    rewrite Nat.iter_succ.
    iMod (actual_step_run with "Hbank Hpermit Hcredit Hsteps") as "Hsteps";
      first done.
    iApply ("IH" with "Hpermits Hcredits Hsteps").
  Qed.

  (** A logical step's existing receipt-boosting effect is supported, not just
      its later elimination. The credit itself is consumed. *)
  Lemma step_credit_elim_tr N E n :
    E ## ↑N →
    step_bank N -∗ step_credit 1 -∗ ⧗ n
      ={E ∪ ↑N}=∗ ⧗ (tr_f n) ∗ £ (tr_f n).
  Proof.
    iIntros (Hdisj) "#Hbank Hcredit Htr".
    iApply (step_credit_elim_logical with "Hbank Hcredit"); first done.
    iApply (logical_step.logical_step_intro_tr with "Htr").
    iIntros "$ $". done.
  Qed.

  (** Issuing a credit and redeeming it are separate bank transactions. In
      particular, the real transaction has closed the bank before redemption. *)
  Lemma actual_step_then_redeem N E P :
    E ## ↑N →
    step_bank N -∗ real_step_permit 1 -∗ step_credit 1 -∗
    logical_step.logical_step E P ={E ∪ ↑N}=∗ P.
  Proof.
    iIntros (Hdisj) "#Hbank Hpermit Hstock Hlogical".
    iPoseProof (actual_step_credit N E) as "Hactual".
    iMod (actual_step_run with "Hbank Hpermit Hstock Hactual") as "Hcredit";
      first done.
    iApply (step_credit_elim_logical with "Hbank Hcredit Hlogical"); done.
  Qed.

  (** The newly issued credit can be spent before the raw step starts. This
      outer update phase runs with the bank closed and supports bank access. *)
  Lemma actual_step_spend_credit N E P Q :
    E ## ↑N →
    step_bank N -∗ logical_step.logical_step E P -∗
    (P -∗ physical_step E Q) -∗ actual_step N E Q.
  Proof.
    iIntros (Hdisj) "#Hbank Hlogical Hcont Hcredit".
    iMod (step_credit_elim_logical with "Hbank Hcredit Hlogical") as "HP";
      first done.
    iModIntro. iApply ("Hcont" with "HP").
  Qed.
End model.

Section allocation.
  Context `{!invGS Σ, !trGS Σ, !bankGpreS Σ, !tr_generation}.

  Lemma bank_state_alloc s k :
    tr_supply s 0 -∗ £ (bank_reserve s (k + k)) ==∗
    ∃ _ : bankGS Σ, bank_state ∗ real_step_permit k ∗ step_credit k.
  Proof using All.
    iIntros "Hsup Hreserve".
    iMod (own_alloc (● (k, k) ⋅ ◯ (k, k))) as (γ) "[Hauth Hstock]".
    { apply auth_both_valid_discrete. split; first done. done. }
    pose (Hbank := BankGS Σ _ γ). iExists Hbank. iModIntro.
    iSplitL "Hauth Hsup Hreserve".
    { iExists s, k, k. iFrame. }
    rewrite /real_step_permit /step_credit /bank_token -own_op -auth_frag_op.
    replace ((k, 0) ⋅ (0, k)) with (k, k) by
      (change ((k, k) = (k + 0, 0 + k)); f_equal; lia).
    done.
  Qed.

  Lemma step_bank_alloc N s k :
    tr_supply s 0 -∗ £ (bank_reserve s (k + k)) ={⊤}=∗
    ∃ _ : bankGS Σ, step_bank N ∗ real_step_permit k ∗ step_credit k.
  Proof using All.
    iIntros "Hsup Hreserve".
    iMod (own_alloc (● (k, k) ⋅ ◯ (k, k))) as (γ) "[Hauth Hstock]".
    { apply auth_both_valid_discrete. split; first done. done. }
    pose (Hbank := BankGS Σ _ γ).
    iExists Hbank.
    iMod (inv_alloc N _ (bank_inv) with "[Hauth Hsup Hreserve]") as "$".
    { iNext. iExists s, k, k. iFrame. }
    rewrite /real_step_permit /step_credit /bank_token -own_op -auth_frag_op.
    replace ((k, 0) ⋅ (0, k)) with (k, k) by
      (change ((k, k) = (k + 0, 0 + k)); f_equal; lia).
    done.
  Qed.
End allocation.

(** The horizon and future credit stock are private to this soundness proof.
    Client proofs are uniform over the bank instance and receive no stock or
    permits. They can obtain credits only through actual-step continuations. *)
Lemma actual_stepN_soundness
    `{!invGpreS Σ, !trGpreS Σ, !bankGpreS Σ, !tr_generation}
    N E n k (P : iProp Σ) `{!Plain P} :
  E ## ↑N →
  (∀ `{!invGS Σ, !trGS Σ, !bankGS Σ},
    step_bank N -∗ ⧗ n ∗ £ n -∗
    |={⊤}=> Nat.iter k (actual_step N E) (|={⊤,∅}=> P)) →
  ⊢ P.
Proof using All.
  intros Hdisj HP.
  apply (fupd_soundness HasLc (bank_reserve n (k + k) + n) ⊤ ∅); first apply _.
  iIntros (Hinv) "[Hreserve Hcredits]".
  iMod (tr_supply_alloc n) as (Htr) "Hsup".
  iDestruct (tr_supply_tr_2 n 0 n with "Hsup") as "[Hsup Hreceipts]".
  iMod (step_bank_alloc with "Hsup Hreserve") as (Hbank) "(#Hbank & Hpermits & Hstock)".
  iMod (HP with "Hbank [$Hreceipts $Hcredits]") as "Hsteps".
  iMod (fupd_mask_subseteq (E ∪ ↑N)) as "Hmask"; first set_solver.
  iMod (actual_step_runN with "Hbank Hpermits Hstock Hsteps") as "HP"; first done.
  iMod "Hmask" as "_". by iMod "HP".
Qed.
