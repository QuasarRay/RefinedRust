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
