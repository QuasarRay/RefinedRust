From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_RawVec_T_ptr.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
(* Access allocation evidence without opening the sharing of any vector element. *)
Lemma RawVec_shared_freeable {rt} (ty : type rt) F π κ storage buf cap :
  lftE ⊆ F →
  storage ◁ₗ[π, Shared κ] #(buf, cap) @ ◁ (RawVec_inv_t rt -[] -[ty]) ={F}=∗
  freeable_nz_shared κ buf (size_of_array_in_bytes (st_of ty MetaNone) cap) 1 HeapAlloc.
Proof.
  iIntros (HF) "Hraw".
  iPoseProof (ofty_ltype_acc_shared F with "Hraw") as
    (ly Hly Halign) "(_ & Hacc)"; first done.
  iMod "Hacc" as "Hraw".
  iEval (rewrite /RawVec_inv_t /ex_plain_t /ty_shr /=) in "Hraw".
  iDestruct "Hraw" as "(_ & %raw_rfn & Halloc & _)".
  iEval (rewrite /RawVec_inv_t_inv_spec /mk_auto_ex_inv_def /=) in "Halloc".
  iDestruct "Halloc" as "(_ & #Hallocation & _)".
  by iFrame "Hallocation".
Qed.

Lemma RawVec_T_ptr_proof (π : thread_id) :
  RawVec_T_ptr_lemma π.
Proof.
  RawVec_T_ptr_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
