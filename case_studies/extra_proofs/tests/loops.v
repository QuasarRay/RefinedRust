From refinedrust Require Import typing.

(* TODO upstream *)

Definition sum_list_Z_with {A} (f : A → Z) : list A → Z :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => f x + go l
  end.
Notation sum_list_Z := (sum_list_Z_with id).


(** ** Properties of the [sum_list_Z_with] function *)
Section sum_list.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.
  Lemma sum_list_Z_with_app (f : A → Z) l k :
    sum_list_Z_with f (l ++ k) = sum_list_Z_with f l + sum_list_Z_with f k.
  Proof. induction l; simpl; lia. Qed.
  Lemma sum_list_Z_with_reverse (f : A → Z) l :
    sum_list_Z_with f (reverse l) = sum_list_Z_with f l.
  Proof.
    induction l; simpl; rewrite ?reverse_cons ?sum_list_Z_with_app; simpl; lia.
  Qed.
  Lemma sum_list_Z_fmap_same n l f :
    Forall (λ x, f x = n) l →
    sum_list_Z (f <$> l) = length l * n.
  Proof. induction 1; csimpl; lia. Qed.
  Lemma sum_list_Z_fmap_const l n :
    sum_list_Z ((λ _, n) <$> l) = length l * n.
  Proof. by apply sum_list_Z_fmap_same, Forall_true. Qed.
End sum_list.

Global Hint Rewrite -> @sum_list_Z_with_app : lithium_rewrite.

Lemma seqZ_pos_seq start count :
  0 ≤ start →
  seqZ start count = Z.of_nat <$> seq (Z.to_nat start) (Z.to_nat count).
Proof.
  intros Hge.
  set (start' := Z.to_nat start).
  assert (start = Z.of_nat start') as Heq by lia.
  rewrite Heq in Hge.
  rewrite Heq.
  generalize start'.
  clear. intros start.
  unfold seqZ.
  generalize (Z.to_nat count) as count'. 
  clear. intros count.
  unfold fmap.
  (*induction count as [ | ? IH] in start |-*; simpl; try solve_goal.*)
  (*f_equiv; first lia.*)
  (*rewrite -IH.*)
  (*solve_goal.*)
Admitted.
Global Hint Rewrite -> seqZ_pos_seq using lia : lithium_rewrite.

(* Idea more generally: split at 0 *)

Lemma sum_list_Z_of_nat xs :
  sum_list_Z (Z.of_nat <$> xs) = sum_list xs.
Proof.
Admitted.
Global Hint Rewrite -> sum_list_Z_of_nat : lithium_rewrite.

Global Hint Rewrite -> Z2Nat.inj_0 : lithium_rewrite.
Global Hint Rewrite -> Z.sub_0_r Z.add_0_r Z.sub_0_l Z.add_0_l : lithium_rewrite.


Definition max_list_Z_with {A} (f : A → Z) (def : Z) : list A → Z :=
  fix go l :=
  match l with
  | [] => def
  | x :: l => f x `max` go l
  end.
Notation max_list_Z := (max_list_Z_with id).


(** ** Properties of the [max_list_Z_with] function *)
Section max_list.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.

  Lemma max_list_Z_with_def (f : A → Z) def l :
    max_list_Z_with f def l = def `max` max_list_Z_with f def l.
  Proof.
    induction l; simpl; lia.
  Qed.
  Lemma max_list_Z_with_app (f : A → Z) def l k :
    max_list_Z_with f def (l ++ k) = max_list_Z_with f def l `max` max_list_Z_with f def k.
  Proof. 
    induction l as [ | ?? IH] in k |-*; simpl. 
    - rewrite max_list_Z_with_def. lia.
    - rewrite IH. lia.
  Qed.
  Lemma max_list_Z_with_reverse (f : A → Z) def l :
    max_list_Z_with f def (reverse l) = max_list_Z_with f def l.
  Proof.
    induction l as [ | ?? IH]; simpl; rewrite ?reverse_cons ?max_list_Z_with_app; simpl; first lia.
    rewrite IH. rewrite max_list_Z_with_def. lia.
  Qed.
  Lemma max_list_Z_fmap_const l def n :
    max_list_Z def ((λ _, n) <$> l) =
    match l with | [] => def | _ => def `max` n end.
  Proof. 
    induction l as [ | ?? IH]; simpl; first done.
    rewrite IH. destruct l; lia.
  Qed.
End max_list.
Global Hint Rewrite -> @max_list_Z_with_app : lithium_rewrite.
