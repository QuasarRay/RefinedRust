From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_CursorMut_aTA_move_prev_closure0_call_once.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma CursorMut_aTA_move_prev_closure0_call_once_proof (π : thread_id) :
  CursorMut_aTA_move_prev_closure0_call_once_lemma π.
Proof.
  CursorMut_aTA_move_prev_closure0_call_once_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
