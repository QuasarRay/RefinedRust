From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_push_back.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_push_back_proof (π : thread_id) :
  LinkedList_TA_push_back_lemma π.
Proof.
  LinkedList_TA_push_back_prelude.

  1: rep <-! <3000 liRStep.
  liShow.
  1: rep liRStep.
  (* Expose the appended ghost as an insertion into a concrete list, so the
     existing iterator insertion rule can resolve it from the observation. *)
  assert (Hinsert :
    <[length self := PlaceGhost (rt := T_rt) x']>
      (PlaceIn <$> ((RT_xrt T_rt <$> self) ++ [RT_xrt T_rt elt])) =
    ((PlaceIn ∘ RT_xrt T_rt) <$> self) ++ [PlaceGhost x']).
  { rewrite fmap_app list_fmap_compose.
    rewrite insert_app_r_alt; last by rewrite !length_fmap; lia.
    rewrite !length_fmap Nat.sub_diag. done. }
  iEval (rewrite -Hinsert).
  1: rep <-! <3000 liRStep.
  liInst Hevar_lt (◁ T_ty)%I.
  split.
  { change (replicate (S (length self)) (◁ T_ty)%I !! length self = Some (◁ T_ty)%I).
    apply lookup_replicate_2. lia. }
  1: rep <-! <3000 liRStep.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rewrite insert_app_r_alt; last by rewrite length_fmap; lia.
  all: rewrite length_fmap Nat.sub_diag /=.
  - rewrite -(length_fmap (RT_xrt T_rt) self) take_app_length list_fmap_compose. done.
  - rewrite -(length_fmap (RT_xrt T_rt) self) drop_app_length.
    eexists _, []. done.
Qed.
End proof.
