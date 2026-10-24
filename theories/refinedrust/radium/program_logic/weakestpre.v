(** From the CPP'26 paper "Building Blocks for Step-Indexed Program Logics",
    by Thomas Somers, Jonas Kastberg Hinrichsen, Lennard Gäher, and Robbert Krebbers.
*)
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From radium.physical_step Require Export step_credits.
From iris.program_logic Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

(* TODO: should move into stdpp eventually? *)
Scheme Rewriting for TCEq.

Class irisGS (Λ : language) (Σ : gFunctors) := IrisG {
  #[global] iris_invGS :: invGS Σ;
  #[global] iris_trGS :: trGS Σ;
  #[global] iris_trGen :: tr_generation;
  #[global] iris_step_creditGS :: step_creditGS Σ;
  (** Issuance per actual reduction; independent of the adequacy horizon. *)
  step_credits_per_step : nat;

  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [Λstate] is the global state,
  the first [nat] is the number of steps already performed by the
  program, [list (observation Λ)] are the remaining observations, and the
  last [nat] is the number of forked-off threads (not the total number
  of threads, which is one higher because there is always a main
  thread). *)
  state_interp : state Λ → nat → list (observation Λ) → nat → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val Λ → iProp Σ;

  (** When performing pure steps, the state interpretation needs to be
  adapted for the change in the [ns] parameter.

  Note that we use an empty-mask fancy update here. We could also use
  a basic update or a bare magic wand, the expressiveness of the
  framework would be the same. If we removed the modality here, then
  the client would have to include the modality it needs as part of
  the definition of [state_interp]. Since adding the modality as part
  of the definition [state_interp_mono] does not significantly
  complicate the formalization in Iris, we prefer simplifying the
  client. *)
  state_interp_mono σ ns κs nt:
    state_interp σ ns κs nt ⊢ |={∅}=> state_interp σ (S ns) κs nt
}.
Global Opaque iris_invGS.
Global Arguments IrisG {Λ Σ}.

Definition wp_state_interp `{!irisGS Λ Σ} σ ns κs nt : iProp Σ :=
  state_interp σ ns κs nt ∗ step_credit_state.

Definition state_update `{!irisGS Λ Σ} E (P : iProp Σ) : iProp Σ :=
  ∀ σ ns κs nt, wp_state_interp σ ns κs nt -∗
    |={E}=> wp_state_interp σ ns κs nt ∗ P.

Lemma wp_state_interp_mono `{!irisGS Λ Σ} σ ns κs nt :
  wp_state_interp σ ns κs nt ⊢ |={∅}=> wp_state_interp σ (S ns) κs nt.
Proof.
  iIntros "[Hstate Hbank]". iMod (state_interp_mono with "Hstate") as "Hstate".
  iModIntro. iFrame.
Qed.

Lemma step_credit_update_state_update `{!irisGS Λ Σ} E P :
  step_credit_update E P -∗ state_update E P.
Proof.
  iIntros "Hupdate" (σ ns κs nt) "[Hstate Hbank]".
  iMod ("Hupdate" with "Hbank") as "[Hbank HP]". iModIntro. iFrame.
Qed.

(** The operational later guards the recursive WP independently of receipt
    advancement. Only the actual-successor branch receives issued credits;
    the safety branch receives none. Adequacy supplies these credits from a
    private, finitely backed stock. *)
Definition wp_pre `{!irisGS Λ Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κ κs nt,
     wp_state_interp σ1 ns (κ ++ κs) nt -∗
       (|={E,∅}=> ⌜if s is NotStuck then reducible e1 σ1 else True⌝) ∧
        ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
          step_credit step_credits_per_step -∗
          |={E,∅}=> ▷ |={∅,E}=>
          wp_state_interp σ2 (S ns) κs (length efs + nt) ∗
         wp E e2 Φ ∗
         [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post
  end%I.


Local Instance wp_pre_contractive `{!irisGS Λ Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  repeat (f_contractive || f_equiv || apply Hwp).
Qed.

Local Definition wp_def `{!irisGS Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) stuckness :=
  λ s : stuckness, fixpoint (wp_pre s).
Local Definition wp_aux : seal ( @wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ Σ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal `{!irisGS Λ Σ} : wp = @wp_def Λ Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre s (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold (wp_pre s)). Qed.

Global Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.

  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  repeat first [solve [apply (IH _ Hlt); intros v; eapply dist_lt; [apply HΦ|exact Hlt]]
    | f_contractive | f_equiv].
Qed.
Global Instance wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  repeat (f_contractive || f_equiv).
Qed.

Lemma wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite wp_unfold /wp_pre to_of_val. auto. Qed.

Lemma wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ns κ κs nt) "Hσ".
  iDestruct ("H" with "[$]") as "H".
  iSplit.
  { iDestruct "H" as "[H _]".
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iMod "H" as "%Hst". by destruct s1, s2.
  }
  iIntros (e2 σ2 efs Hstep) "Hcredit".
  iDestruct "H" as "[_ H]".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[//] Hcredit") as "Hnext".
  iModIntro. iNext. iMod "Hnext" as "($ & H & Hefs)".
  iMod "Hclose" as "_". iModIntro.
  iSplitR "Hefs".
  - iApply ("IH" with "[//] H HΦ").
  - iApply (big_sepL_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "H". iApply ("IH" with "[] H"); auto.
Qed.

Lemma fupd_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ns κ κs nt) "Hσ1".
  iSplit.
  - iMod "H"; iDestruct ("H" with "[$]") as "[$ _]".
  - iMod "H"; iDestruct ("H" with "[$]") as "[_ $]".
Qed.

Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.

Lemma wp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ns κ κs nt) "Hσ".
  iMod "H".
  iSplit; [iDestruct ("H" with "[$]") as "[$ _]"|].
  iIntros (e2 σ2 efs Hstep) "Hcredit".
  iDestruct ("H" with "Hσ") as "[_ H]".
  iMod ("H" with "[//] Hcredit") as "Hnext".
  iModIntro. iNext. iMod "Hnext" as "(Hσ & H & Hefs)". destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iDestruct ("H" $! _ _ [] with "[$]") as "[>H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ Hstep).
  - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
    rewrite wp_value_fupd'. iMod "H" as ">H".
    iModIntro. iFrame "Hσ Hefs". by iApply wp_value_fupd'.
Qed.

(** A state-preserving update executes before resuming the same nonvalue
    expression. Values retain their ordinary fancy-update rule. *)
Lemma wp_state_update s E e Φ :
  TCEq (to_val e) None →
  state_update E (WP e @ s; E {{ Φ }}) -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "Hupdate". iEval (rewrite wp_unfold /wp_pre He).
  iIntros (σ ns κ κs nt) "Hstate". iSplit.
  - iMod ("Hupdate" with "Hstate") as "[Hstate Hwp]".
    iEval (rewrite wp_unfold /wp_pre He) in "Hwp".
    iDestruct ("Hwp" with "Hstate") as "[$ _]".
  - iIntros (e' σ' efs Hstep) "Hcredit".
    iMod ("Hupdate" with "Hstate") as "[Hstate Hwp]".
    iEval (rewrite wp_unfold /wp_pre He) in "Hwp".
    iDestruct ("Hwp" with "Hstate") as "[_ Hwp]".
    iApply ("Hwp" with "[//] Hcredit").
Qed.

Lemma wp_step_credit_update s E e Φ :
  TCEq (to_val e) None →
  step_credit_update E (WP e @ s; E {{ Φ }}) -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "Hupdate". iApply (wp_state_update _ _ _ _ He).
  iIntros (σ ns κs nt) "[Hstate Hbank]".
  iMod ("Hupdate" with "Hbank") as "[Hbank Hwp]". iModIntro. iFrame.
Qed.

Lemma wp_physical_step s E e P Φ :
  TCEq (to_val e) None →
  step_credit 1 -∗ physical_step E P -∗
  (P -∗ WP e @ s; E {{ Φ }}) -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "Hcredit Hraw Hcont". iApply (wp_step_credit_update _ _ _ _ He).
  iIntros "Hbank". iMod (step_credit_redeem with "Hcredit Hraw Hbank") as "[Hbank HP]".
  iModIntro. iFrame "Hbank". iApply ("Hcont" with "HP").
Qed.

Lemma wp_logical_step s E e P Φ :
  TCEq (to_val e) None →
  step_credit 1 -∗ logical_step.logical_step E P -∗
  (P -∗ WP e @ s; E {{ Φ }}) -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "Hcredit Hlogical Hcont". iApply (wp_step_credit_update _ _ _ _ He).
  iIntros "Hbank".
  iMod (step_credit_redeem_logical with "Hcredit Hlogical Hbank") as "[Hbank HP]".
  iModIntro. iFrame "Hbank". iApply ("Hcont" with "HP").
Qed.


Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val /=; [|done].
  iIntros (σ1 step κ κs n) "Hσ". iDestruct ("H" with "[$]") as "H".
  iSplit.
  { iDestruct "H" as "[>%H _]". destruct s; eauto using reducible_fill. }
  iDestruct "H" as "[_ H]".
  iIntros (e2 σ2 efs Hstep) "Hcredit".
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//] Hcredit") as "Hnext".
  iModIntro. iNext. iMod "Hnext" as "($ & H & $)". iModIntro.
  by iApply "IH".
Qed.

Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  iSplit.
  { iDestruct ("H" with "[$]") as "[>%H _]". destruct s; eauto using reducible_fill_inv. }
  iIntros (e2 σ2 efs Hstep) "Hcredit".
  iDestruct ("H" with "Hσ") as "[_ H]".
  iMod ("H" with "[] Hcredit") as "Hnext"; first eauto using fill_step.
  iModIntro. iNext. iMod "Hnext" as "($ & H & $)". iModIntro. by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite wp_value_fupd'. auto. Qed.
Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

(** Direct payment with ordinary later credits does not need the bank. *)
Lemma wp_laterN n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  £ n -∗
  (|={E1,E2}=> ▷^n |={E2,E1}=> P) -∗
  WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He HE) "Hcredit HP Hwp". iApply fupd_wp.
  iMod "HP" as "HP". iMod (lc_fupd_add_laterN with "Hcredit HP") as "HP".
  iModIntro.
  iApply (wp_strong_mono with "Hwp"); [done|done|].
  iIntros (v) "HΦ". iApply ("HΦ" with "HP").
Qed.
(** Receipt-dependent step updates cost one banked credit. Conjunction lets
    the receipt-bound observation temporarily inspect the base state without
    consuming the resources needed for the continuation. *)
Lemma wp_step_fupdN_strong n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  step_credit 1 -∗
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E1,∅}=∗ ⧖ n) ∧
  ((|={E1,E2}=> |={∅}▷=>^(S (tr_f n)) |={E2,E1}=> P) ∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He HE) "Hcredit H". iApply (wp_state_update _ _ _ _ He).
  iIntros (σ ns κs nt) "[Hstate Hbank]".
  iMod (step_credit_redeem E1
    (state_interp σ ns κs nt ∗ P ∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }})%I
    with "Hcredit [H Hstate] Hbank") as "[Hbank (Hstate & HP & Hwp)]".
  { iApply (physical_step_fupdN E2 n P). iSplit.
    - iDestruct "H" as "[H _]". iApply ("H" with "Hstate").
    - iDestruct "H" as "[_ [$ Hwp]]".
      iApply physical_step_intro. iNext. iIntros "HP". iModIntro. iFrame. }
  iModIntro. iFrame "Hstate Hbank".
  iApply (wp_strong_mono with "Hwp"); [done|done|].
  iIntros (v) "HΦ". iApply ("HΦ" with "HP").
Qed.

Lemma wp_step_fupdN n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  step_credit 1 -∗
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E1,∅}=∗ ⧖ n) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^(S (tr_f n)) |={∅,E1∖E2}=> P) ∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He HE) "Hcredit H".
  iApply (wp_step_fupdN_strong _ _ _ _ _ _ _ He HE with "Hcredit [H]").
  iApply (and_mono_r with "H"). apply sep_mono_l. iIntros "HP".
  iMod (fupd_mask_subseteq_emptyset_difference E1 (E1 ∖ E2)) as "H"; [set_solver|].
  iMod "HP". iMod "H" as "_".
  replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
  iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.

Lemma wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He HE) "HP Hwp". rewrite !wp_unfold /wp_pre He.
  iIntros (σ ns κ κs nt) "Hstate". iSplit.
  { iMod "HP" as "HP". iDestruct ("Hwp" with "Hstate") as "[$ _]". }
  iIntros (e' σ' efs Hstep) "Hcredit".
  iMod "HP" as "HP". iDestruct ("Hwp" with "Hstate") as "[_ Hwp]".
  iMod ("Hwp" with "[//] Hcredit") as "Hnext".
  iModIntro. iNext. iMod "Hnext" as "($ & Hwp & $)".
  iMod "HP" as "HP". iModIntro.
  iApply (wp_strong_mono with "Hwp"); [done|done|].
  iIntros (v) "HΦ". iApply ("HΦ" with "HP").
Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

Lemma wp_step_update_strong E1 E2 P e s Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  step_credit 1 -∗
  (|~{E1, E2}~> P) -∗
  WP e @ s; E2 {{ v, P -∗ Φ v }} -∗
  WP e @ s; E1 {{ v, Φ v}}.
Proof.
  iIntros (He Hle) "Hcredit Hupdate Hwp".
  iApply (wp_physical_step s E1 e P Φ He with "Hcredit [Hupdate] [Hwp]").
  { iApply (physical_step_step_upd with "Hupdate").
    iApply physical_step_intro. by iNext; iIntros "$". }
  iIntros "HP". iApply (wp_strong_mono with "Hwp"); [done|done|].
  iIntros (v) "HΦ". iApply ("HΦ" with "HP").
Qed.
Lemma wp_step_update s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  step_credit 1 -∗
  (|~{E1∖E2}~> P) -∗
  WP e @ s; E2 {{ v, P -∗ Φ v }} -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (Hval HE) "Hcredit Hstep Hwp".
  iDestruct (step_update_frame (E1∖E2) ∅ (E2) with "Hstep") as "Hstep";
    [set_solver|set_solver|].
  replace (E1 ∖ E2 ∪ E2) with E1; last first.
  { rewrite difference_union_L. set_solver. }
  replace (∅ ∪ E2) with E2 by set_solver.
  by iApply (wp_step_update_strong with "Hcredit [$] [$]").
Qed.
Lemma wp_step_update_emp s E1 e P Φ :
  TCEq (to_val e) None →
  step_credit 1 -∗
  (|~~> P) -∗
  WP e @ s; E1 {{ v, P -∗ Φ v }} -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (Hval) "Hcredit Hstep Hwp".
  iApply (wp_step_update with "Hcredit [Hstep] Hwp"); [done|].
  by rewrite difference_diag_L.
Qed.

Lemma wp_trp_update s n E e Φ :
  TCEq (to_val e) None →
  step_credit 1 -∗
  ⧖ n -∗
  WP e @ s; E {{ v, ⧖ (tr_f $ S $ n) -∗ Φ v }} -∗
  WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "Hcredit H⧖ Hwp".
  iApply (wp_step_update_emp with "Hcredit [H⧖] Hwp").
  iApply (step_update_lb_update with "[$]").
Qed.

Lemma wp_tr_use s n E e Φ :
  TCEq (to_val e) None →
  step_credit 1 -∗
  ⧗ n -∗
  WP e @ s; E {{ v, ⧗ (tr_f n) -∗ £ (tr_f n) -∗ Φ v }} -∗
  WP e @ s; E {{ Φ }}.
Proof.
  iIntros (He) "Hcredit H⧗ Hwp".
  iDestruct (step_update_tr_use with "[$]") as "H".
  iApply (wp_step_update_emp with "Hcredit H").
  iApply (wp_mono with "[$]").
  iIntros (v) "H [A B]". iApply ("H" with "A B").
Qed.

End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (FrameInstantiateExistDisabled → ∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof.
    rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. constructor.
  Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.
  (** Error message instance for non-mask-changing view shifts.
  Also uses a slightly different error: we cannot apply [fupd_mask_subseteq]
  if [e] is not atomic, so we tell the user to first add a leading [fupd]
  and then change the mask of that. *)
  Global Instance elim_modal_fupd_wp_wrong_mask p s E1 E2 e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_wp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2}=> P) False (WP e @ s; E1 {{ Φ }}) False | 100.
  Proof. intros []. Qed.

  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r wp_atomic.
  Qed.
  (** Error message instance for mask-changing view shifts. *)
  Global Instance elim_modal_fupd_wp_atomic_wrong_mask p s E1 E2 E2' e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2,E2'}=> P) False
      (WP e @ s; E1 {{ Φ }}) False | 200.
  Proof. intros []. Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_modal_step_credit_update_wp E P s e Φ :
    TCEq (to_val e) None →
    ElimModal True false false (step_credit_update E P) P
      (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    rewrite /ElimModal. iIntros (He _) "[Hupdate Hcont]".
    iApply (wp_step_credit_update _ _ _ _ He). iIntros "Hbank".
    iMod ("Hupdate" with "Hbank") as "[Hbank HP]".
    iModIntro. iFrame "Hbank". iApply ("Hcont" with "HP").
  Qed.

End proofmode_classes.
