From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_CursorMut_aTA_index.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma CursorMut_aTA_index_proof (π : thread_id) :
  CursorMut_aTA_index_lemma π.
Proof.
  CursorMut_aTA_index_prelude.

  rep <-! liRStep; liShow.
  { rename select (match _ with _ => _ end = inl _) into Ha.
    destruct (linked_list_locs (cursor_list self) !! cursor_pos self) as [ loc_cur | ] eqn:Hlookup; simpl in Ha; last done.
    injection Ha as <-.
    rep liRStep. }
  { rename select (match _ with _ => _ end = inr _) into Ha.
    destruct (linked_list_locs (cursor_list self) !! cursor_pos self) as [ loc_cur | ] eqn:Hlookup; simpl in Ha; first done.
    injection Ha as <-.
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - apply lookup_ge_None in Hlookup.
    rewrite Hlen in Hlookup.
    destruct (decide (cursor_pos self < length (linked_list_elems (cursor_list self)))) as [Hlt | Hge]; [lia | reflexivity].
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
