From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_get_unchecked_mut.

Set Default Proof Using "Type".
Local Typeclasses Opaque alloc_alive_token alloc_alive_witness.

Section proof.
Context `{!refinedrustGS Σ}.
Lemma Vec_T_get_unchecked_mut_proof (π : thread_id) :
  Vec_T_get_unchecked_mut_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft4" ["ulft_1"].
  Vec_T_get_unchecked_mut_prelude.

  (* Reading the pointer field exposes RawVec's allocation ownership. *)
  rep <-! liRStep; liShow.
  iRename select (freeable_nz _ _ _ _)%I into "Hfree".
  iPoseProof (freeable_nz_alive_acc _ _ _ _
    (bool_decide (ly_size T_st_ly ≠ 0%nat)) with "Hfree") as "(Halive & Hrestore)".
  { intros Hnz. apply bool_decide_eq_true in Hnz.
    rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /=. nia. }
  rep liRStep; liShow.
  match goal with Hk := EVAR_ID _ : alloc_alive_kind |- _ =>
    liInst Hk AliveAlloc end.
  match goal with Hw := EVAR_ID _ : loc |- _ => liInst Hw l end.
  match goal with Hq := EVAR_ID _ : Qp |- _ => liInst Hq 1%Qp end.
  rep <-! liRStep; liShow.
  iRename select (if_iTrue _ (alloc_alive_token l 1))%I into "Halive".
  iPoseProof ("Hrestore" with "Halive") as "Hfree".
  apply_update (updateable_typed_array_access l index (UntypedSynType $ st_of T_ty MetaNone)).
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: try (rewrite project_vec_els_insert_lt /=; [|lia]; normalize_and_simpl_goal).
  all: rename select (_ = project_vec_els _ _) into Hxs.
  all: assert (length self ≤ length els); first (specialize (project_vec_els_length (length self) els); rewrite -Hxs; solve_goal).
  all: normalize_and_simpl_goal; try solve_goal with lia.

  { solve_goal with nia. }
  { solve_goal with nia. }
  { apply list_lookup_insert_Some'.
    split; normalize_and_simpl_goal.
    rewrite Hxs. solve_goal with lia.
  }
  { by rewrite Hxs. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
