(** Lifting operational reductions into the credit-producing HasLc WP. *)
From iris.proofmode Require Import proofmode.
From radium.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types e : expr Λ.
Implicit Types Φ : val Λ → iProp Σ.

(** Credit-only lifting. The bank remains available throughout the successor
    continuation, including when the successor is a value. *)
Lemma wp_lift_step_credits s E Φ e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt -∗
    (|={E,∅}=> ⌜if s is NotStuck then reducible e σ else True⌝) ∧
    ∀ e' σ' efs, ⌜prim_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update E
        (state_interp σ' (S ns) κs (length efs + nt) ∗
         WP e' @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  intros He. rewrite wp_unfold /wp_pre He.
  iIntros "H" (σ ns κ κs nt) "[Hstate Hbank]". iSplit.
  { iDestruct ("H" with "Hstate") as "[$ _]". }
  iIntros (e' σ' efs Hstep) "Hcredits".
  iDestruct ("H" with "Hstate") as "[_ H]".
  iMod ("H" with "[//] Hcredits Hbank") as "[Hbank (Hstate & Hwp & Hforks)]".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iModIntro. iFrame.
Qed.

(** The usual E→∅→E discipline; bank updates need no enabled namespace. *)
Lemma wp_lift_step_fupd s E Φ e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e σ else True⌝ ∗
    ∀ e' σ' efs, ⌜prim_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update ∅
        (|={∅,E}=> state_interp σ' (S ns) κs (length efs + nt) ∗
         WP e' @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  intros He. rewrite wp_unfold /wp_pre He.
  iIntros "H" (σ ns κ κs nt) "[Hstate Hbank]". iSplit.
  { iMod ("H" with "Hstate") as "[$ _]". done. }
  iIntros (e' σ' efs Hstep) "Hcredits".
  iMod ("H" with "Hstate") as "[_ H]".
  iMod ("H" with "[//] Hcredits Hbank") as "[Hbank Hnext]".
  iModIntro. iNext. iMod "Hnext" as "(Hstate & Hwp & Hforks)".
  iModIntro. iFrame.
Qed.

(** Guarded lifting for proofs that use the operational later. *)
Lemma wp_lift_step s E Φ e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e σ else True⌝ ∗
    ▷ ∀ e' σ' efs, ⌜prim_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update ∅
        (|={∅,E}=> state_interp σ' (S ns) κs (length efs + nt) ∗
         WP e' @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  intros He. rewrite wp_unfold /wp_pre He.
  iIntros "H" (σ ns κ κs nt) "[Hstate Hbank]". iSplit.
  { iMod ("H" with "Hstate") as "[$ _]". done. }
  iIntros (e' σ' efs Hstep) "Hcredits".
  iMod ("H" with "Hstate") as "[_ H]". iModIntro. iNext.
  iMod ("H" with "[//] Hcredits Hbank") as "[Hbank Hnext]".
  iMod "Hnext" as "(Hstate & Hwp & Hforks)". iModIntro. iFrame.
Qed.

(** Compatibility: reserve one issued credit for interpreting a raw step. *)
Lemma wp_lift_step_physical_step s E Φ e :
  0 < step_credits_per_step → to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt -∗
    (|={E,∅}=> ⌜if s is NotStuck then reducible e σ else True⌝) ∧
    ∀ e' σ' efs, ⌜prim_step e σ κ e' σ' efs⌝ -∗
      step_credit (step_credits_per_step - 1) -∗ physical_step E
        (state_interp σ' (S ns) κs (length efs + nt) ∗
         WP e' @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (Hr He) "H". iApply (wp_lift_step_credits _ _ _ _ He).
  iIntros (σ ns κ κs nt) "Hstate". iDestruct ("H" with "Hstate") as "H".
  iSplit; first by iDestruct "H" as "[$ _]".
  iIntros (e' σ' efs Hstep) "Hcredits". iDestruct "H" as "[_ H]".
  replace step_credits_per_step with (1 + (step_credits_per_step - 1)) at 1 by lia.
  rewrite step_credit_split. iDestruct "Hcredits" as "[Hexecute Hrest]".
  iApply (step_credit_redeem with "Hexecute (H [//] Hrest)").
Qed.

Lemma wp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E,∅}=∗ ⌜stuck e σ⌝) ⊢
  WP e @ E ?{{ Φ }}.
Proof.
  intros He. rewrite wp_unfold /wp_pre He.
  iIntros "H" (σ ns κ κs nt) "[Hstate Hbank]". iSplit.
  - iMod ("H" with "Hstate") as "%". done.
  - iIntros (e' σ' efs Hstep) "Hcredits".
    iMod ("H" with "Hstate") as %[_ Hstuck].
    by case: (Hstuck κ e' σ' efs).
Qed.

Lemma wp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s E Φ e :
  (∀ σ, if s is NotStuck then reducible e σ else to_val e = None) →
  (∀ κ σ e' σ' efs, prim_step e σ κ e' σ' efs → κ = [] ∧ σ' = σ ∧ efs = []) →
  (∀ κ e' efs σ, ⌜prim_step e σ κ e' σ efs⌝ -∗
    step_credit step_credits_per_step -∗ step_credit_update E (WP e' @ s; E {{ Φ }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step_credits.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ ns κ κs nt) "Hstate". iSplit.
  { iApply fupd_mask_intro; first set_solver. iIntros "_".
    iPureIntro. destruct s; done. }
  iIntros (e' σ' efs Hp) "Hcredits Hbank".
  destruct (Hstep κ σ e' σ' efs Hp) as (-> & <- & ->).
  iMod ("H" with "[//] Hcredits Hbank") as "[Hbank Hwp]".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
  iMod (state_interp_mono with "Hstate") as "Hstate".
  iMod "Hclose" as "_". iModIntro. simpl. iFrame.
Qed.

Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E Φ} e e' :
  (∀ σ, if s is NotStuck then reducible e σ else to_val e = None) →
  (∀ σ κ e'' σ' efs, prim_step e σ κ e'' σ' efs →
    κ = [] ∧ σ' = σ ∧ e'' = e' ∧ efs = []) →
  (step_credit step_credits_per_step -∗ step_credit_update E (WP e' @ s; E {{ Φ }})) ⊢
  WP e @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_pure_step_no_fork; first done.
  { intros. naive_solver. }
  iIntros (κ e'' efs σ Hp). destruct (Hstep _ _ _ _ _ Hp) as (_ & _ & -> & _).
  done.
Qed.

Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) → True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  { destruct (to_val e) as [v|] eqn:He; last done.
    specialize (Hstuck inhabitant). destruct Hstuck as [Hnv _]. congruence. }
  iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; first set_solver.
  iIntros "_". done.
Qed.

Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E1}=∗
    ⌜if s is NotStuck then reducible e σ else True⌝ ∗
    ∀ e' σ' efs, ⌜prim_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update E1
        (|={E1}[E2]▷=> state_interp σ' (S ns) κs (length efs + nt) ∗
         from_option Φ False (to_val e') ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  intros He. rewrite wp_unfold /wp_pre He.
  iIntros "H" (σ ns κ κs nt) "[Hstate Hbank]". iSplit.
  { iMod ("H" with "Hstate") as "[$ _]".
    iApply fupd_mask_intro; first set_solver. by iIntros "_". }
  iIntros (e' σ' efs Hstep) "Hcredits".
  iMod ("H" with "Hstate") as "[_ H]".
  iMod ("H" with "[//] Hcredits Hbank") as "[Hbank Hnext]".
  iMod "Hnext" as "Hnext".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "Hnext" as "(Hstate & HΦ & Hforks)".
  iModIntro. iFrame. destruct (to_val e') as [v|] eqn:Hv; last done.
  apply of_to_val in Hv as <-. by iApply wp_value'.
Qed.

Lemma wp_lift_atomic_step {s E Φ} e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E}=∗
    ⌜if s is NotStuck then reducible e σ else True⌝ ∗
    ▷ ∀ e' σ' efs, ⌜prim_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update E
        (state_interp σ' (S ns) κs (length efs + nt) ∗
         from_option Φ False (to_val e') ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "H". iApply (wp_lift_step _ _ _ _ He).
  iIntros (σ ns κ κs nt) "Hstate".
  iMod ("H" with "Hstate") as "[$ H]".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iIntros (e' σ' efs Hstep) "Hcredits Hbank".
  iMod "Hclose" as "_".
  iMod ("H" with "[//] Hcredits Hbank") as "[Hbank (Hstate & HΦ & Hforks)]".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iFrame "Hbank". iMod "Hclose" as "_". iModIntro. iFrame.
  destruct (to_val e') as [v|] eqn:Hv; last done.
  apply of_to_val in Hv as <-. by iApply wp_value'.
Qed.
Lemma wp_lift_pure_step_no_fork_fupd `{!Inhabited (state Λ)} s E E' Φ e :
  (∀ σ, if s is NotStuck then reducible e σ else to_val e = None) →
  (∀ κ σ e' σ' efs, prim_step e σ κ e' σ' efs → κ = [] ∧ σ' = σ ∧ efs = []) →
  (|={E}[E']▷=> ∀ κ e' efs σ, ⌜prim_step e σ κ e' σ efs⌝ -∗
    step_credit step_credits_per_step -∗ step_credit_update E (WP e' @ s; E {{ Φ }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ ns κ κs nt) "Hstate". iMod "H" as "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e' σ' efs Hp) "Hcredits Hbank".
  destruct (Hstep κ σ e' σ' efs Hp) as (-> & <- & ->).
  iMod (state_interp_mono with "Hstate") as "Hstate".
  iMod "Hclose" as "_". iMod "H" as "H".
  iMod ("H" with "[//] Hcredits Hbank") as "[Hbank Hwp]".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iFrame "Hbank". iMod "Hclose" as "_". iModIntro. simpl. iFrame.
Qed.

Lemma wp_lift_pure_det_step_no_fork_fupd `{!Inhabited (state Λ)} {s E E' Φ} e e' :
  (∀ σ, if s is NotStuck then reducible e σ else to_val e = None) →
  (∀ σ κ e'' σ' efs, prim_step e σ κ e'' σ' efs →
    κ = [] ∧ σ' = σ ∧ e'' = e' ∧ efs = []) →
  (|={E}[E']▷=> step_credit step_credits_per_step -∗
    step_credit_update E (WP e' @ s; E {{ Φ }})) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_pure_step_no_fork_fupd; first done.
  { intros. naive_solver. }
  iApply (step_fupd_wand with "H"). iIntros "H" (κ e'' efs σ Hp).
  destruct (Hstep _ _ _ _ _ Hp) as (_ & _ & -> & _). done.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e e' φ n Φ :
  PureExec φ n e e' → φ →
  (|={E}[E']▷=>^n step_credit (step_credits_per_step * n) -∗
    WP e' @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe Hdet] Hsteps IH]; simpl.
  { rewrite Nat.mul_0_r. iMod step_credit_zero as "Hz". by iApply "Hwp". }
  iApply (wp_lift_pure_det_step_no_fork_fupd (E':=E') e1 e2).
  - intros σ. pose proof (reducible_no_obs_reducible _ _ (Hsafe σ)) as Hred.
    destruct s; eauto using reducible_not_val.
  - done.
  - iApply (step_fupd_wand with "Hwp"). iIntros "Hwp Hissued".
    iApply step_credit_update_intro. iApply "IH".
    iApply (step_fupdN_wand with "Hwp"). iIntros "Hwp Hcredits".
    iApply ("Hwp" with "[Hissued Hcredits]").
    rewrite Nat.mul_succ_r Nat.add_comm step_credit_split. iFrame.
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} s E e e' φ n Φ :
  PureExec φ n e e' → φ →
  ▷^n (step_credit (step_credits_per_step * n) -∗ WP e' @ s; E {{ Φ }}) ⊢
  WP e @ s; E {{ Φ }}.
Proof.
  intros Hexec Hφ. rewrite -(wp_pure_step_fupd s E E e e' φ n Φ) //.
  enough (∀ P : iProp Σ, ▷^n P ⊢ |={E}▷=>^n P) as Hintro by apply Hintro.
  intros P. apply step_fupdN_intro. set_solver.
Qed.
End lifting.
