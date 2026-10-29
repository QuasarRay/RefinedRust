From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_push.

Set Default Proof Using "Type".
Local Typeclasses Opaque alloc_alive_token alloc_alive_witness.

Section proof.
Context `{!refinedrustGS Σ}.

Lemma Vec_T_push_proof (π : thread_id) :
  Vec_T_push_lemma π.
Proof.
  generalize RR_CONFIG_DONT_FOLD_PLACES; intros ?.
  Vec_T_push_prelude.

  rep <-! liRStep; liShow.
  2: rep <-! liRStep.
  1: rename x'0 into buf.
  1: rename x' into cap.
  2: rename l into buf.
  2: pose (cap := length els).
  (* Both paths expose the current buffer's allocation through the reborrow. *)
  all: have Hcap_pos : (0 < cap)%nat by (try unfold cap; lia).
  all: li_pm_reduce.
  all: iRename select (freeable_nz _ _ _ _)%I into "Hfree".
  all: iPoseProof (freeable_nz_alive_acc _ _ _ _
    (bool_decide (ly_size ly ≠ 0%nat)) with "Hfree") as "(Halive & Hrestore)".
  1,3: intros Hnz; apply bool_decide_eq_true in Hnz;
    rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /=; nia.
  all: iEval (rewrite /alloc_alive_witness) in "Halive Hrestore".
  all: liRStepUntil prove_with_subtype.
  all: match goal with Hk := EVAR_ID _ : alloc_alive_kind |- _ =>
    liInst Hk AliveAlloc end.
  all: liInst Hevar_x2 buf.
  all: match goal with Hq := EVAR_ID _ : Qp |- _ => liInst Hq 1%Qp end.
  all: rep <-! liRStep; liShow.
  2: rep <-! liRStep; liShow.
  all: iRename select (if_iTrue _ (alloc_alive_token buf 1))%I into "Halive".
  all: iPoseProof ("Hrestore" with "Halive") as "Hfree".
  all: apply_update (updateable_typed_array_access buf (length self) (UntypedSynType $ st_of T_ty MetaNone)).
  all: rep liRStep; liShow.


  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  1: unfold cap; move: Hcap; clear; nia.

  all: rename select (_ = project_vec_els _ _) into Hxs.
  all: match type of Hxs with _ = project_vec_els ?len2 ?xs2 =>
      rename xs2 into xs';
      specialize (project_vec_els_length len2 xs') as Hlen_eq;
      rewrite -Hxs !length_fmap in Hlen_eq
      end.

  {
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply list_lookup_insert_Some'.
    split;normalize_and_simpl_goal.
    1: lia.
    rewrite Hxs.
    erewrite project_vec_els_lookup_mono; [solve_goal|lia|].
    rewrite lookup_app_l; [done|lia].
  }
  {
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply (list_eq_split (length self)).
    - rewrite take_insert_ge/=; [|lia].
      rewrite project_vec_els_take project_vec_els_take_r.
      solve_goal.
    - rewrite drop_insert_ge/=; [|lia].
      rewrite !fmap_app.
      rewrite drop_app_length' ?project_vec_els_length; last solve_goal.
      rewrite project_vec_els_drop. apply list_eq_singleton.
      split; solve_goal.
  }
  {
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply list_lookup_insert_Some'. split; normalize_and_simpl_goal.
    rewrite Hxs. erewrite project_vec_els_lookup_mono; [solve_goal|lia|done].
  }
  {
    rewrite project_vec_els_insert_lt /=; [|lia].
    apply (list_eq_split (length self)).
    - rewrite take_insert_ge/=; [|lia].
      rewrite !fmap_app.
      rewrite take_app_length' ?project_vec_els_length; last solve_goal.
      rewrite project_vec_els_take.
      solve_goal.
    - rewrite drop_insert_ge/=; [|lia]. rewrite !fmap_app drop_app_length' ?project_vec_els_length; [|solve_goal].
      rewrite project_vec_els_drop.
      apply list_eq_singleton.
      split; solve_goal.
  }

  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
