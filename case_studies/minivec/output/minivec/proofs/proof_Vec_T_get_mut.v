From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_get_mut.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma Vec_T_get_mut_proof (π : thread_id) :
  Vec_T_get_mut_lemma π.
Proof.
  Vec_T_get_mut_prelude.
  (* On the successful branch, [self] is not used after the call. Move its
     reference through the generated reborrow, preserving the observation γ. *)
  liRStepUntil typed_call.
  do 1 liRStep.
  repeat lazymatch goal with
  | |- environments.envs_entails _ (typed_val_expr _ _ _ (Ref Mut _ _ _) _) => fail
  | _ => liRStep
  end.
  apply_update (updateable_stratify arg_self StratRefoldFull StratifyUnblockOp).
  liRStepUntil typed_val_expr. li_pm_reduce.
  iApply (type_reborrow_mut_move _ _ _ _ _ _ arg_self
    (Vec_inv_t T_rt -[] -[T_ty]) ulft_a
    (#((PlaceIn ∘ RT_xrt T_rt) <$> xs : list (place_rfn T_rt)), γ)).
  iApply (type_local_addr _ _ _ "self" RefSynType arg_self).
  liRStepUntil typed_call. do 1 liRStep.
  (* Likewise move the returned temporary into [Some], preserving its ghost. *)
  repeat lazymatch goal with
  | |- environments.envs_entails _ (typed_val_expr _ _ _ (Ref Mut _ _ _) _) => fail
  | _ => liRStep
  end.
  li_pm_reduce.
  iApply (type_reborrow_mut_move _ _ _ _ _ _ local___8 T_ty κ0 (#($#xs !!! i), x'0)).
  iApply (type_local_addr _ _ _ "__8" RefSynType local___8).
  rep <-! liRStep; liShow.
  all: rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
