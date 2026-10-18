From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_handle_error.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* The dispatcher never returns a refinement involving the error payload, so
   its owned layout can be read without retaining the payload's ghost name. *)
Local Lemma resolve_error_layout π E L γ T :
  (∀ r : rust_layout, T L (#r) True%I true) ⊢
  resolve_ghost π E L ResolveAll false (◁ layout_Layout_inv_t -[] -[])%I
    Owned (PlaceGhost γ) T.
Proof.
  rewrite /resolve_ghost.
  iIntros "HT" (F l ??) "#CTX #HE HL Hl".
  iPoseProof (ltype_own_ofty_forget_obs with "Hl") as "(%r & Hl)".
  iSpecialize ("HT" $! r).
  iModIntro.
  iExists L, (#r), True%I, true. iFrame.
  done.
Qed.

Lemma raw_vec_handle_error_proof (π : thread_id) :
  raw_vec_handle_error_lemma π.
Proof.
  raw_vec_handle_error_prelude.

  rep 982 liRStep.
  destruct layout as [layout_value | layout_ghost].
  { rep 1000 liRStep. }
  { liShow. iApply typed_place_resolve_ghost.
    iSplitR; first (iPureIntro; shelve_sidecond).
    iApply resolve_error_layout. iIntros (layout_value).
    liFromSyntaxGoal. rep 1000 liRStep. }
  Unshelve.
  1-12: sidecond_solver.
  Unshelve.
  1-3: sidecond_hammer.
Qed.
End proof.
