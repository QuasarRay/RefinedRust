From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_get_unchecked.

Set Default Proof Using "Type".
Local Typeclasses Opaque alloc_alive_token alloc_alive_witness.

Section proof.
Context `{!refinedrustGS Σ}.

Lemma Vec_T_get_unchecked_proof (π : thread_id) :
  Vec_T_get_unchecked_lemma π.
Proof.
  generalize RR_CONFIG_DONT_FOLD_PLACES; intros ?.
  generalize RR_CONFIG_DONT_INTERPRET_SHR_REF_TYPING_HINTS; intros ?.
  pose_unconstrained_lft_hint "vuclft3" ["ulft_1"].
  Vec_T_get_unchecked_prelude.

  rep <-! <300 liRStep; liShow.
  (* Reading self.buf.cap exposes RawVec's shared allocation invariant. *)
  rep <-! liRStep.
  apply_update (updateable_borrow_shared_freeable ulft_1 l
    (size_of_array_in_bytes (st_of T_ty MetaNone) (length els)) 1 HeapAlloc
    (bool_decide (ly_size T_st_ly ≠ 0%nat))).
  rep liRStep. liShow.
  liInst Hevar_x2 l.
  liInst Hevar_x1 AliveAlloc.
  liInst Hevar_x0 qa.
  rep <-! liRStep; liShow.
  (* Recover the lifetime count before borrowing the actual element. *)
  apply_update (updateable_close_lft_loan
    (if_iTrue (bool_decide (ly_size T_st_ly ≠ 0%nat)) (alloc_alive_token l qa))%I).
  iExists _.
  iRename select (_ ={⊤}=∗ llft_elt_toks _)%I into "Hrestore".
  iRename select (if_iTrue _ (alloc_alive_token l qa))%I into "Halive".
  iFrame "Halive Hrestore". rep <-! liRStep. liShow.

  iRename select (_ ◁ₗ[_, Shared _] _ @ _)%I into "Harray".
  let Harray := iTypeOf' "Harray" in
  lazymatch Harray with
  | (?l ◁ₗ[_, Shared _] _ @ _)%I =>
    apply_update (updateable_typed_array_access l i (UntypedSynType $ st_of T_ty MetaNone))
  end.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rewrite /size_of_array_in_bytes /use_layout_alg' T_st_alg /=. nia. }
  { split; first lia.
    revert select ((ly_size _ * _)%nat ≤ _).
    move: Hi. revert select (length xs ≤ length _). clear. nia. }
  { move: Hi. revert select (length xs ≤ length _). clear. nia. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
