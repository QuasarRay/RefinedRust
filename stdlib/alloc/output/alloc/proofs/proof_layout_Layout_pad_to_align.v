From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_pad_to_align.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* A shared invariant remains available after inspecting one of its fields. *)
Local Lemma forget_shared_view {rt_cur rt_full} (cur : ltype rt_cur)
    (full : ltype rt_full) rcur r κ π l :
  l ◁ₗ[π, Owned] r @ ShrLtype (ShadowedLtype cur rcur full) κ -∗
  l ◁ₗ[π, Owned] r @ ShrLtype full κ.
Proof.
  rewrite !ltype_own_shr_ref_unfold /shr_ltype_own.
  iIntros "(%ly & Hlayout & Halign & Hbounds & %ri & Hrfn & Hb)".
  iExists ly. iFrame.
  iMod "Hb" as "(%li & Hli & Hshared)". iModIntro. iExists li. iFrame.
  rewrite ltype_own_shadowed_unfold /shadowed_ltype_own. iDestruct "Hshared" as "(_ & $)".
Qed.

Lemma layout_Layout_pad_to_align_proof (π : thread_id) :
  layout_Layout_pad_to_align_lemma π.
Proof.
  layout_Layout_pad_to_align_prelude.

  1: rep <-! <3000 liRStep.
  liShow.
  iMatchHyp ltac:(fun H P => lazymatch P with
    | context [ShadowedLtype] => iPoseProof (forget_shared_view with H) as "Hself"
    end).
  liFromSyntaxGoal. rep <-! <3000 liRStep.
  Unshelve.
  1-11: sidecond_solver.
  Unshelve.
  - rename select (layout_wf self) into Hlayout_wf.
    rewrite /layout_wf /ly_align /rust_layout_to_layout
      /layout_alignment_log2_nat /= in Hlayout_wf.
    rewrite /alignment_to_align -(Nat2Z.inj_pow 2). exact Hlayout_wf.
  - by destruct self.
Qed.
End proof.
