From iris.proofmode Require Import proofmode.
From lithium Require Import all.

Section tests.
  Context {Σ : gFunctors}.

  (* The boolean can occur independently of the argument bound by the
     continuation. Both branches must rewrite these closed-over occurrences. *)
  Lemma case_destruct_bool_decide_continuation (P : Prop) `{!Decision P} :
    ⊢@{iProp Σ} case_destruct (bool_decide P)
      (λ b _, ⌜bool_decide P = b⌝).
  Proof.
    iStartProof.
    liCase; lazymatch goal with
    | |- environments.envs_entails _ ⌜?b = ?b⌝ => iPureIntro; reflexivity
    end.
  Qed.

  Lemma case_destruct_bool_decide_context (P : Prop) `{!Decision P}
      (Q R : iProp Σ) :
    (if bool_decide P then Q else R) ⊢
      case_destruct (bool_decide P) (λ b _, if b then Q else R).
  Proof. iIntros "H". liCase; iExact "H". Qed.

  Lemma case_destruct_bool_decide_cached_context (P : Prop) `{!Decision P}
      (Q R : iProp Σ) :
    (if bool_decide P then Q else R) ⊢
      case_destruct (bool_decide P) (λ b _, if b then Q else R).
  Proof. iIntros "H". let_bind_envs. liCase; iExact "H". Qed.
End tests.
