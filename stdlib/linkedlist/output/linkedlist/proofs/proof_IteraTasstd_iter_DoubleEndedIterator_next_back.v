From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_IteraTasstd_iter_DoubleEndedIterator_next_back.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma IteraTasstd_iter_DoubleEndedIterator_next_back_proof (π : thread_id) :
  IteraTasstd_iter_DoubleEndedIterator_next_back_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft4" ["ulft_a"].
  pose_unconstrained_lft_hint "vuclft5" ["ulft_a"].
  IteraTasstd_iter_DoubleEndedIterator_next_back_prelude.

  rep <-! <3000 liRStep; liShow.
  1: rep liRStep.
  1: liInst Hevar_all_elems all_elems.
  1: rep <-! <3000 liRStep; liShow.

  destruct x0 as [ | x_head xs]; first done.
  have Hdrop_len := f_equal (@length _) Hsuffix.
  rewrite length_drop length_take Nat.min_l in Hdrop_len; last lia.
  rewrite length_fmap in Hdrop_len. simpl in Hdrop_len.
  assert (idx < back_idx) as Hidxlt by lia.
  assert (0 < back_idx) as Hbackpos by lia.
  assert (MinInt usize ≤ (Z.of_nat (S (length xs)) - 1)%Z)%Z as Hdecr_lower.
  { solve_goal. }
  assert ((Z.of_nat (S (length xs)) - 1)%Z ≤ MaxInt usize)%Z as Hdecr_upper by lia.
  destruct (reverse (x_head :: xs)) as [ | x_last rev_rest] eqn:Hrev.
  { have Hempty := f_equal (@length _) Hrev. rewrite length_reverse in Hempty. simpl in Hempty. lia. }
  have Hsplit : x_head :: xs = reverse rev_rest ++ [x_last].
  { rewrite -reverse_cons -Hrev reverse_involutive. done. }
  have Helem : all_elems !! (back_idx - 1)%nat = Some (# $#@{T_rt} x_last).
  { have Hlookup := f_equal (λ l : list (place_rfn T_rt), @list_lookup (place_rfn T_rt) (back_idx - idx - 1)%nat l) Hsuffix.
    change ((PlaceIn ∘ RT_xrt T_rt <$> x_head :: xs) !! (back_idx - idx - 1)%nat =
      drop idx (take back_idx all_elems) !! (back_idx - idx - 1)%nat) in Hlookup.
    rewrite Hsplit fmap_app fmap_cons fmap_nil lookup_app_r in Hlookup.
    2: { rewrite length_fmap length_reverse.
         have Hlength := f_equal (@length _) Hsplit. rewrite length_app length_reverse /= in Hlength. lia. }
    rewrite length_fmap length_reverse in Hlookup.
    have Hrestlen := f_equal (@length _) Hsplit.
    rewrite length_app length_reverse /= in Hrestlen.
    replace (back_idx - idx - 1 - length rev_rest)%nat with 0%nat in Hlookup by lia.
    rewrite lookup_drop lookup_take decide_True in Hlookup; last lia.
    replace (idx + (back_idx - idx - 1))%nat with (back_idx - 1)%nat in Hlookup by lia.
    exact (eq_sym Hlookup). }
  have Hrest_len : length xs = length (reverse rev_rest).
  { have Hlength := f_equal (@length _) Hsplit.
    rewrite length_app /= in Hlength. lia. }
  have Hslice : PlaceIn ∘ RT_xrt T_rt <$> reverse rev_rest =
      drop idx (take (back_idx - 1) all_elems).
  { apply (app_inv_tail [PlaceIn (RT_xrt T_rt x_last)]).
    change ((PlaceIn ∘ RT_xrt T_rt <$> reverse rev_rest) ++
      (PlaceIn ∘ RT_xrt T_rt <$> [x_last]) =
      drop idx (take (back_idx - 1) all_elems) ++ [PlaceIn (RT_xrt T_rt x_last)]).
    rewrite -fmap_app -Hsplit Hsuffix.
    replace back_idx with (S (back_idx - 1)) at 1 by lia.
    rewrite (take_S_r _ _ _ Helem) drop_app length_take Nat.min_l; last lia.
    replace (idx - (back_idx - 1))%nat with 0%nat by lia. done. }
  destruct (lookup_lt_is_Some_2 locs (back_idx - 1)) as (l & Hloc); first lia.
  have Htail : last (take back_idx locs) = Some l.
  { rewrite last_lookup length_take Nat.min_l; last lia.
    rewrite lookup_take decide_True; last lia.
    replace (Nat.pred back_idx) with (back_idx - 1)%nat by lia. done. }
  liShow.
  iRename select (LL _ _ _ _ _)%I into "Hall".
  iDestruct "Hall" as "#Hall".
  iPoseProof (LL_lookup _ _ _ _ _ (back_idx - 1) with "Hall") as "Hitem"; first done.
  iDestruct "Hitem" as (l0 next prev) "(%Hloc0 & %Hnext & %Hprev & -#Hnode)".
  rewrite Hloc in Hloc0. simplify_eq.
  have Hprev_tail : prev = last (take (back_idx - 1) locs).
  { destruct (back_idx - 1)%nat as [ | n] eqn:Hn.
    - simpl in Hprev. simplify_eq. done.
    - change ((Some <$> locs) !! n = Some prev) in Hprev.
      rewrite list_lookup_fmap in Hprev.
      rewrite last_lookup length_take Nat.min_l; last lia.
      simpl. rewrite lookup_take decide_True; last lia.
      change (prev = @list_lookup loc n locs).
      change (option_map Some (@list_lookup loc n locs) = Some prev) in Hprev.
      destruct (@list_lookup loc n locs); simpl in Hprev; simplify_eq; done. }
  rewrite Htail.
  iRevert "Hnode".
  rep <-! <3000 liRStep; liShow.
  apply_update updateable_strip_guards.
  rep <-! <3000 liRStep; liShow.
  { rep liRStep; liShow.
  1: liInst Hevar_rf (PlaceIn ∘ RT_xrt T_rt <$> reverse rev_rest).
  1: liInst Hevar_all_elems all_elems.
  rep <-! <3000 liRStep; liShow. }
  { rep <-! <3000 liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  all: try solve_goal.
  all: try lia.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
