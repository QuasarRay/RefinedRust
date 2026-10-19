From refinedrust Require Import typing.
From rrstd.ptr.ptr.generated Require Import generated_specs_ptr.
From rrstd.ptr.theories Require Import specs.

Record rust_layout := mk_rust_layout {
  layout_sz : nat;
  layout_alignment : alignment_enum;
}.
Global Instance rust_layout_inh : Inhabited rust_layout.
Proof. exact (populate (mk_rust_layout inhabitant inhabitant)). Qed.

(* TODO: move? *)
Lemma is_power_of_two_log2_pow n :
  is_power_of_two n →
  2^(Nat.log2 n) = n.
Proof.
  intros (m & ->).
  rewrite Nat.log2_pow2; lia.
Qed.

Lemma layout_alignment_bounds alignment :
  1 ≤ alignment_to_align alignment ≤ MaxInt ISize + 1.
Proof. destruct alignment; rewrite /alignment_to_align /= MaxInt_eq; vm_compute; intuition congruence. Qed.

Lemma layout_alignment_divides_half alignment :
  (alignment_to_align alignment | MaxInt ISize + 1).
Proof.
  apply Z.mod_divide; first (pose proof (layout_alignment_bounds alignment); lia).
  destruct alignment; rewrite MaxInt_eq; vm_compute; reflexivity.
Qed.

Lemma layout_aligned_size_valid size alignment :
  (alignment_to_align alignment | size) →
  (size ≤ MaxInt ISize + 1 - alignment_to_align alignment ↔ size ≤ MaxInt ISize).
Proof.
  intros [k Hsize].
  pose proof (layout_alignment_bounds alignment) as Hbounds.
  destruct (layout_alignment_divides_half alignment) as [q Hhalf].
  split; intros Hbound.
  - lia.
  - destruct (Z_lt_ge_dec k q); nia.
Qed.
Lemma is_power_of_two_Z_log2_pow z :
  is_power_of_two (Z.to_nat z) →
  2^(Z.log2 z) = z.
Proof.
  intros (m & Heq).
  assert (z = 2^m) as -> by lia.
  rewrite Z.log2_pow2; lia.
Qed.

Lemma layout_round_up_aligned size alignment bits :
  0 ≤ bits → 0 ≤ size < 2 ^ bits →
  (alignment_to_align alignment | size) →
  Z.land (size + (alignment_to_align alignment - 1))
    (Z_lunot bits (alignment_to_align alignment - 1)) = size.
Proof.
  intros Hbits Hsize [k Hmultiple].
  pose proof (layout_alignment_bounds alignment) as Halign.
  have Hpow : alignment_to_align alignment - 1 =
      Z.ones (Z.of_nat (alignment_to_align_log2 alignment)).
  { rewrite Z.ones_equiv /alignment_to_align. lia. }
  rewrite /Z_lunot -(Z.land_ones _ _ Hbits) Z.land_assoc
    -Z.sub_land_same_l Hpow !Z.land_ones; try lia.
  rewrite -Hpow.
  have Hmod : (size + (alignment_to_align alignment - 1)) `mod`
      alignment_to_align alignment = alignment_to_align alignment - 1.
  { rewrite Hmultiple.
    replace (k * alignment_to_align alignment + (alignment_to_align alignment - 1))
      with ((alignment_to_align alignment - 1) + k * alignment_to_align alignment) by ring.
    rewrite Z.mod_add; last lia. apply Z.mod_small; lia. }
  change ((size + (alignment_to_align alignment - 1) -
    (size + (alignment_to_align alignment - 1)) `mod` alignment_to_align alignment)
    `mod` 2 ^ bits = size).
  rewrite Hmod. replace (size + (alignment_to_align alignment - 1) -
    (alignment_to_align alignment - 1)) with size by ring.
  apply Z.mod_small. exact Hsize.
Qed.

Canonical Structure rust_layoutRT := directRT rust_layout.

Definition layout_alignment_log2_nat (rly : rust_layout) : nat :=
  alignment_to_align_log2 rly.(layout_alignment).
Definition layout_alignment_nat (rly : rust_layout) : nat :=
  alignment_to_align_nat rly.(layout_alignment).

Definition rust_layout_to_layout (rly : rust_layout) : layout :=
  Layout rly.(layout_sz) (layout_alignment_log2_nat rly).

Global Coercion rust_layout_to_layout : rust_layout >-> layout.

Lemma ly_align_of_rust_layout_align sz (align : Z) :
  is_power_of_two (Z.to_nat align) →
  align ∈ usize →
  (ly_align (rust_layout_to_layout (mk_rust_layout sz (alignment_of_align align)))) = Z.to_nat align.
Proof.
  intros Hpow Hel.
  rewrite /ly_align/=.
  rewrite /layout_alignment_log2_nat/=.

  rewrite /alignment_of_align.
  rewrite alignment_to_from_log2.
  - rewrite -(Znat.Z2Nat.inj_pow 2); [ | lia | apply Z.log2_nonneg].
    rewrite is_power_of_two_Z_log2_pow; last done.
    lia.
  - opose proof (power_of_two_log2_usize_in_bounds align _ _); [ solve_goal | done | ].
    lia.
Qed.
