From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Import generated_code_alloc generated_specs_alloc generated_template_layout_Layout_from_size_align.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma layout_Layout_from_size_align_proof (π : thread_id) :
  layout_Layout_from_size_align_lemma π.
Proof.
  layout_Layout_from_size_align_prelude.

  rep <-! <3000 liRStep.
  {
    rep liRStep.
    liInst Hevar_r2 (mk_rust_layout (Z.to_nat (n * align)) (alignment_of_align align)).
    split; first done. split; first done.
    liFromSyntaxGoal. rep <-! <3000 liRStep.
  }
  { rep <-! <3000 liRStep. }
  Unshelve.
  1-16: first [exact ([] : list lft) | sidecond_solver].
  Unshelve.
  - nia.
  - unfold layout_wf. rewrite ly_align_of_rust_layout_align; [|assumption|split; solve_goal].
    rewrite !Z2Nat.id; try nia. exists n; ring.
  - exfalso.
    have Halign : alignment_to_align (alignment_of_align align) = align.
    { apply alignment_to_from; [split; solve_goal | assumption]. }
    assert (Hdiv : (alignment_to_align (alignment_of_align align) | n * align)).
    { rewrite Halign. exists n; ring. }
    pose proof (proj2 (layout_aligned_size_valid _ _ Hdiv) H9) as Hvalid.
    rewrite Halign in Hvalid. lia.
Qed.
End proof.
