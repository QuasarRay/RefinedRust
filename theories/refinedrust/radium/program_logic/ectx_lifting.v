(** Credit-aware lifting for evaluation-context languages. *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export ectx_language.
From radium.program_logic Require Export weakestpre lifting.
From iris.prelude Require Import options.

Section wp.
Context {Λ : ectxLanguage} `{!irisGS Λ Σ} `{!Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types e : expr Λ.
Local Hint Resolve base_prim_reducible base_reducible_prim_step : core.

Lemma wp_lift_base_step_fupd {s E Φ} e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E,∅}=∗
    ⌜base_reducible e σ⌝ ∗
    ∀ e' σ' efs, ⌜base_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update ∅
        (|={∅,E}=> state_interp σ' (S ns) κs (length efs + nt) ∗
         WP e' @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "H". iApply (wp_lift_step_fupd _ _ _ _ He).
  iIntros (σ ns κ κs nt) "Hstate". iMod ("H" with "Hstate") as "[% H]".
  iModIntro. iSplit; first by destruct s; eauto.
  iIntros (e' σ' efs Hstep). iApply "H"; eauto.
Qed.

Lemma wp_lift_base_step {s E Φ} e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E,∅}=∗
    ⌜base_reducible e σ⌝ ∗
    ▷ ∀ e' σ' efs, ⌜base_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update ∅
        (|={∅,E}=> state_interp σ' (S ns) κs (length efs + nt) ∗
         WP e' @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "H". iApply (wp_lift_step _ _ _ _ He).
  iIntros (σ ns κ κs nt) "Hstate". iMod ("H" with "Hstate") as "[% H]".
  iModIntro. iSplit; first by destruct s; eauto.
  iNext. iIntros (e' σ' efs Hstep). iApply "H"; eauto.
Qed.

Lemma wp_lift_base_step_physical_step {s E Φ} e :
  0 < step_credits_per_step → to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E,∅}=∗
    ⌜base_reducible e σ⌝ ∗
    ∀ e' σ' efs, ⌜base_step e σ κ e' σ' efs⌝ -∗
      step_credit (step_credits_per_step - 1) -∗ physical_step ∅
        (|={∅,E}=> state_interp σ' (S ns) κs (length efs + nt) ∗
         WP e' @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (Hr He) "H". iApply (wp_lift_base_step_fupd _ He).
  iIntros (σ ns κ κs nt) "Hstate". iMod ("H" with "Hstate") as "[$ H]".
  iModIntro. iIntros (e' σ' efs Hstep) "Hcredits".
  replace step_credits_per_step with (1 + (step_credits_per_step - 1)) at 1 by lia.
  rewrite step_credit_split. iDestruct "Hcredits" as "[Hexecute Hrest]".
  iApply (step_credit_redeem with "Hexecute (H [//] Hrest)").
Qed.

Lemma wp_lift_base_stuck E Φ e :
  to_val e = None → sub_redexes_are_values e →
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E,∅}=∗ ⌜base_stuck e σ⌝) ⊢
  WP e @ E ?{{ Φ }}.
Proof.
  iIntros (He Hsub) "H". iApply (wp_lift_stuck _ _ _ He).
  iIntros (σ ns κs nt) "Hstate". iMod ("H" with "Hstate") as "%".
  iModIntro. iPureIntro. by apply base_stuck_stuck.
Qed.

Lemma wp_lift_pure_base_stuck E Φ e :
  to_val e = None → sub_redexes_are_values e → (∀ σ, base_stuck e σ) →
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (He Hsub Hstuck). iApply (wp_lift_base_stuck _ _ _ He Hsub).
  iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; first set_solver.
  iIntros "_". done.
Qed.

Lemma wp_lift_atomic_base_step_fupd {s E1 E2 Φ} e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E1}=∗
    ⌜base_reducible e σ⌝ ∗
    ∀ e' σ' efs, ⌜base_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update E1
        (|={E1}[E2]▷=> state_interp σ' (S ns) κs (length efs + nt) ∗
         from_option Φ False (to_val e') ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He) "H". iApply (wp_lift_atomic_step_fupd _ He).
  iIntros (σ ns κ κs nt) "Hstate". iMod ("H" with "Hstate") as "[% H]".
  iModIntro. iSplit; first by destruct s; eauto.
  iIntros (e' σ' efs Hstep). iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_base_step {s E Φ} e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E}=∗
    ⌜base_reducible e σ⌝ ∗
    ▷ ∀ e' σ' efs, ⌜base_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update E
        (state_interp σ' (S ns) κs (length efs + nt) ∗
         from_option Φ False (to_val e') ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "H". iApply (wp_lift_atomic_step _ He).
  iIntros (σ ns κ κs nt) "Hstate". iMod ("H" with "Hstate") as "[% H]".
  iModIntro. iSplit; first by destruct s; eauto.
  iNext. iIntros (e' σ' efs Hstep). iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_base_step_no_fork_fupd {s E1 E2 Φ} e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E1}=∗
    ⌜base_reducible e σ⌝ ∗
    ∀ e' σ' efs, ⌜base_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update E1
        (|={E1}[E2]▷=> ⌜efs = []⌝ ∗ state_interp σ' (S ns) κs nt ∗
          from_option Φ False (to_val e')))
  ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He) "H". iApply (wp_lift_atomic_base_step_fupd _ He).
  iIntros (σ ns κ κs nt) "Hstate". iMod ("H" with "Hstate") as "[$ H]".
  iModIntro. iIntros (e' σ' efs Hstep) "Hcredits Hbank".
  iMod ("H" with "[//] Hcredits Hbank") as "[Hbank Hnext]".
  iModIntro. iFrame "Hbank". iMod "Hnext" as "Hnext". iModIntro. iNext.
  iMod "Hnext" as "(-> & Hstate & HΦ)". simpl. iModIntro. iFrame.
Qed.

Lemma wp_lift_atomic_base_step_no_fork {s E Φ} e :
  to_val e = None →
  (∀ σ ns κ κs nt, state_interp σ ns (κ ++ κs) nt ={E}=∗
    ⌜base_reducible e σ⌝ ∗
    ▷ ∀ e' σ' efs, ⌜base_step e σ κ e' σ' efs⌝ -∗
      step_credit step_credits_per_step -∗ step_credit_update E
        (⌜efs = []⌝ ∗ state_interp σ' (S ns) κs nt ∗ from_option Φ False (to_val e')))
  ⊢ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "H". iApply (wp_lift_atomic_base_step _ He).
  iIntros (σ ns κ κs nt) "Hstate". iMod ("H" with "Hstate") as "[$ H]".
  iModIntro. iNext. iIntros (e' σ' efs Hstep) "Hcredits Hbank".
  iMod ("H" with "[//] Hcredits Hbank") as "[Hbank (-> & Hstate & HΦ)]".
  simpl. iModIntro. iFrame.
Qed.

Lemma wp_lift_pure_det_base_step_no_fork {s E Φ} e e' :
  to_val e = None → (∀ σ, base_reducible e σ) →
  (∀ σ κ e'' σ' efs, base_step e σ κ e'' σ' efs →
    κ = [] ∧ σ' = σ ∧ e'' = e' ∧ efs = []) →
  (step_credit step_credits_per_step -∗ step_credit_update E (WP e' @ s; E {{ Φ }})) ⊢
  WP e @ s; E {{ Φ }}.
Proof using All.
  intros He Hsafe Hstep. apply wp_lift_pure_det_step_no_fork.
  { intros σ. destruct s; eauto. }
  intros σ κ e'' σ' efs Hp. apply Hstep.
  by eapply base_reducible_prim_step.
Qed.
End wp.
