From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.ptr.ptr.generated Require Import generated_code_ptr generated_specs_ptr generated_template_const_ptr_add.

Set Default Proof Using "Type".
Local Typeclasses Opaque alloc_alive_witness.

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma const_ptr_add_proof (π : thread_id) :
  const_ptr_add_lemma π.
Proof.
  const_ptr_add_prelude.

  all: rep liRStep; liShow.
  match goal with Hkind := EVAR_ID _ : alloc_alive_kind |- _ => instantiate_protected Hkind kind end.
  match goal with Hw := EVAR_ID _ : loc |- _ => instantiate_protected Hw w end.
  match goal with Hq := EVAR_ID _ : Qp |- _ => instantiate_protected Hq q end.
  split; first done.
  have Hsize : size_of_st (st_of T_ty MetaNone) = ly_size T_st_ly.
  { by rewrite /size_of_st /use_layout_alg' T_st_alg. }
  iRename select (if_iTrue _ (alloc_alive_witness kind w q))%I into "Halive".
  iEval (rewrite Hsize) in "Halive".
  (* Normalize the return contract as well as the call precondition, so exact
     context lookup can preserve the whole conditional witness. *)
  rewrite /R Hsize.
  all: rep 2000 liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  (* basically, the reasoning is:
      - if T is a ZST, then the wrapped offset gets annihilated everywhere, so it's fine.
      - else, we also know that it's in isize_t, so it's same as before.
    *)
  all: try match goal with
  | |- @eq loc _ _ =>
      rewrite /OffsetLocSt/offset_loc;
      simplify_layout (use_layout_alg' (ty_syn_type T_ty MetaNone)); f_equiv
  end.
  all: destruct (decide (ly_size T_st_ly = 0%nat)); [lia | ].
  all: assert (MinInt ISize ≤ count ≤ MaxInt ISize)%Z; first by solve_goal with nia; sidecond_hammer.
  all: rewrite wrap_to_it_id; sidecond_hammer.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
