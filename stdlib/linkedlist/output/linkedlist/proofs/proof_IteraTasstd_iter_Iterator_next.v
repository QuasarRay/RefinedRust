From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_IteraTasstd_iter_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma IteraTasstd_iter_Iterator_next_proof (π : thread_id) :
  IteraTasstd_iter_Iterator_next_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft6" ["ulft_a"].
  IteraTasstd_iter_Iterator_next_prelude.

  rep <-! liRStep; liShow.
  1: rep liRStep.
  1: liInst Hevar_all_elems all_elems.
  1: rep <-! liRStep; liShow.

  destruct x0 as [ | x_head xs]; first done.
  simpl in Hsuffix.
  have Hdrop_len := f_equal (@length _) Hsuffix.
   rewrite length_drop length_take Nat.min_l in Hdrop_len; last lia. simpl in Hdrop_len.
   have Hmap_len : length ((PlaceIn ∘ RT_xrt T_rt) <$> xs) = length xs :=
     length_fmap _ _.
   rewrite Hmap_len in Hdrop_len.
  assert (idx < length all_elems) as Hidxlt.
  { lia. }
  assert (S (length xs) <= length all_elems)%nat as Hremainle.
   { lia. }
  assert (Z.of_nat (S (length xs)) ≤ MaxInt usize)%Z as Hremaining_bound by lia.
  assert (MinInt usize ≤ (Z.of_nat (S (length xs)) - 1)%Z)%Z as Hdecr_lower.
  { solve_goal. }
  assert ((Z.of_nat (S (length xs)) - 1)%Z ≤ MaxInt usize)%Z as Hdecr_upper by lia.
  destruct (lookup_lt_is_Some_2 locs idx) as (l & Hloc); first lia.
  have Helem : all_elems !! idx = Some (# $#@{T_rt} x_head).
     { have Hlookup : take back_idx all_elems !! idx = Some (# $#@{T_rt} x_head).
     { rewrite -(Nat.add_0_r idx) -lookup_drop -Hsuffix. done. }
     rewrite lookup_take decide_True in Hlookup; last lia. done. }

  iRename select (LL _ _ _ _ _ )%I into "Hall".
  iDestruct "Hall" as "#Hall".
  iPoseProof (LL_lookup _ _ _ _ _ idx with "Hall") as "Hitem"; first done.
  
  iDestruct "Hitem" as (l0 next prev) "(%Hloc0 & %Hnext & %Hprev & -#Hnode)".
  rewrite Hloc in Hloc0. simplify_eq.
  rewrite Hloc.
  iRevert "Hnode".
  rep <-! liRStep; liShow.
  apply_update updateable_strip_guards.
  rep <-! liRStep; liShow.

  { rep liRStep. liShow.
    1: liInst Hevar_rf (PlaceIn ∘ RT_xrt T_rt <$> xs).
    1: liInst Hevar_all_elems all_elems.
    1: liInst Hevar_locs locs.
     1: liInst Hevar_idx (S idx).
     1: liInst Hevar_back_idx back_idx.
    1: rep liRStep; liShow. }
  { rep <-! liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

   - move: Hsuffix.
     erewrite drop_S. 2: { rewrite lookup_take decide_True; [done | lia]. }
    intros [= <-]. done.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
