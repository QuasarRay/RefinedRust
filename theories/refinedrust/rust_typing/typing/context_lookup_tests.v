From refinedrust Require Import typing.

Section tests.
  Context `{!typeGS Σ}.

  (* The first typing step must frame the entire conditional, rather than
     branching on an undecided boolean. *)
  Lemma prove_direct_exact_conditional E L step b (P A : iProp Σ) T :
    if_iTrue b P -∗ T L [] A -∗
    prove_with_subtype E L step ProveDirect (if_iTrue b P) A T.
  Proof.
    iIntros "HP HT". liRStep.
    lazymatch goal with
    | |- environments.envs_entails _ (if_iTrue b P ∗ _) => iFrame
    end.
  Qed.

  (* With no whole conditional available, the conditional-splitting fallback must
     still be usable. *)
  Lemma prove_direct_conditional_fallback E L step b :
    ⊢ prove_with_subtype E L step ProveDirect (if_iTrue b True) True
        (λ _ _ _, True).
  Proof.
    iStartProof. rep liRStep.
    all: rep liRStep; iFrame.
  Qed.
End tests.

Section lifetime_tokens.
  Context `{!typeGS Σ}.

  Definition release_test_context (κ κ' : lft) : llctx :=
    [κ' ⊑ₗ{0} []; κ ⊑ₗ{1} []].

  (* The returned token must decrement its count even when the context list
     is hidden behind a definition, and must preserve the newer lifetime. *)
  Lemma release_tokens_hidden_context κ κ' :
    llctx_release_toks (release_test_context κ κ') [κ]
      [κ' ⊑ₗ{0} []; κ ⊑ₗ{0} []].
  Proof. solve_llctx_release_toks. Qed.
End lifetime_tokens.
