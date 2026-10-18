From refinedrust Require Import typing.

Definition raw_vec_effective_capacity (size stored : nat) : nat :=
  if decide (size = 0%nat) then Z.to_nat (MaxInt USize) else stored.

Definition raw_vec_min_non_zero_cap (size : Z) : Z :=
  if decide (size = 1) then 8 else if decide (size ≤ 1024) then 4 else 1.

Lemma raw_vec_min_non_zero_cap_positive size : 0 < raw_vec_min_non_zero_cap size.
Proof. unfold raw_vec_min_non_zero_cap. repeat case_decide; lia. Qed.

Definition raw_vec_amortized_capacity (size : Z) (stored : nat) (required : Z) : Z :=
  Z.max (raw_vec_min_non_zero_cap size) (Z.max (2 * Z.of_nat stored) required).

Lemma raw_vec_amortized_capacity_required size stored required :
  required ≤ raw_vec_amortized_capacity size stored required.
Proof. unfold raw_vec_amortized_capacity. etrans; apply Z.le_max_r. Qed.

Lemma raw_vec_amortized_capacity_positive size stored required :
  0 < raw_vec_amortized_capacity size stored required.
Proof.
  pose proof (raw_vec_min_non_zero_cap_positive size).
  unfold raw_vec_amortized_capacity.
  pose proof (Z.le_max_l (raw_vec_min_non_zero_cap size) (Z.max (2 * Z.of_nat stored) required)).
  lia.
Qed.

Lemma raw_vec_max (a b : Z) :
  (if bool_decide ((a ?= b) = Lt) then b else a) = Z.max a b.
Proof. unfold Z.max. destruct (a ?= b); reflexivity. Qed.

(* Empty arrays and arrays of uninitialized ZSTs require no allocated bytes. *)
Lemma raw_vec_zero_array `{!refinedrustGS Σ} {rt} (ty : type rt) π l ly n :
  syn_type_has_layout (st_of ty MetaNone) ly →
  l `has_layout_loc` ly →
  (ly_size ly * n = 0)%nat →
  ty_sidecond ty -∗ loc_in_bounds l 0 0 -∗
  l ◁ₗ[π, Owned] #(replicate n (#None)) @ ◁ array_t n (maybe_uninit ty).
Proof.
  intros Hlayout Halign Hsize. iIntros "#Hsc #Hbounds".
  pose proof (MaxInt_ge_127 ISize) as Hmax.
  rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iExists (mk_array_layout ly n).
  have Hmaybe : syn_type_has_layout (st_of (maybe_uninit ty) MetaNone) ly.
  { by apply syn_type_has_layout_untyped. }
  iSplitR. { iPureIntro. eapply syn_type_has_layout_array; [reflexivity | exact Hmaybe | rewrite -Nat2Z.inj_mul Hsize; lia]. }
  iSplitR. { iPureIntro. by rewrite /has_layout_loc ly_align_mk_array_layout. }
  iSplitR; first done.
  rewrite ly_size_mk_array_layout Hsize. iFrame "Hbounds".
  iExists (replicate n (#None)). iR. iModIntro. iExists ([] : val).
  iSplitR. { rewrite heap_pointsto_nil. done. }
  rewrite /ty_own_val /= array_t_own_val_unfold.
  iExists ly. iR. iR.
  iSplitR. { iPureIntro. rewrite -Nat2Z.inj_mul Hsize. lia. }
  rewrite length_replicate. iR.
  iSplitR. { iPureIntro. by rewrite /has_layout_val ly_size_mk_array_layout Hsize. }
  iApply big_sepL2_intro; first by rewrite length_replicate length_reshape length_replicate.
  iModIntro. iIntros (i r v Hr Hv).
  apply lookup_replicate in Hr as (-> & Hi).
  iExists None. iR. rewrite maybe_uninit_None_unfold uninit_own_spec.
  iR. iExists ly. iR. iPureIntro.
  apply list_elem_of_lookup_2 in Hv.
  apply reshape_replicate_elem_length in Hv; first done.
  simpl. nia.
Qed.

(* Arbitrary bytes can represent uninitialized elements, without asserting
   that those bytes form valid initialized values of the element type. *)
Lemma raw_vec_bytes_array `{!refinedrustGS Σ} {rt} (ty : type rt) π l ly (n : nat) v :
  syn_type_has_layout (st_of ty MetaNone) ly →
  (ly_size ly * n ≤ MaxInt ISize)%Z →
  l ◁ₗ[π, Owned] #v @ ◁ value_t false (LiteralSynType (mk_array_layout ly n)) -∗
  l ◁ₗ[π, Owned] #(replicate n (#None)) @ ◁ array_t n (maybe_uninit ty).
Proof.
  intros Hlayout Hsize.
  rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
  iIntros "(%ly' & %Hlayout' & %Halign & _ & #Hbounds & %v' & -> & Hv)".
  apply syn_type_has_layout_untyped_inv in Hlayout'.
  apply syn_type_has_layout_literal_inv in Hlayout' as (-> & _).
  iExists (mk_array_layout ly n).
  iSplitR.
  { iPureIntro. eapply syn_type_has_layout_array; [reflexivity | | exact Hsize].
    by apply syn_type_has_layout_untyped. }
  iR. iSplitR; first done. iFrame "Hbounds".
  iExists (replicate n (#None)). iR.
  iMod "Hv" as (bytes) "[Hl Hv]". iModIntro. iExists bytes. iFrame "Hl".
  iDestruct (value_t_untyped_equiv with "Hv") as "(%ly' & -> & %Halg & %Hbytes)".
  apply syn_type_has_layout_literal_inv in Halg as (-> & _).
  rewrite /ty_own_val /= array_t_own_val_unfold.
  iExists ly. iR.
  iSplitR. { iPureIntro. by apply syn_type_has_layout_untyped. }
  iR. rewrite length_replicate. iR. iR.
  iApply big_sepL2_intro; first by rewrite length_replicate length_reshape length_replicate.
  iModIntro. iIntros (i r bytes' Hr Hbytes').
  apply lookup_replicate in Hr as (-> & Hi).
  iExists None. iR. rewrite maybe_uninit_None_unfold uninit_own_spec.
  iR. iExists ly. iR. iPureIntro.
  apply list_elem_of_lookup_2 in Hbytes'.
  apply reshape_replicate_elem_length in Hbytes'; first done.
  rewrite Hbytes ly_size_mk_array_layout. lia.
Qed.

(* Keep the semantic ownership of the old elements while exposing their bytes
   to the allocator. Reattaching it after growth preserves initialized values;
   only the newly allocated tail is logically uninitialized. *)
Lemma raw_vec_array_bytes `{!refinedrustGS Σ} {rt} (ty : type rt) π l ly (n : nat) rs :
  syn_type_has_layout (st_of ty MetaNone) ly →
  l ◁ₗ[π, Owned] #rs @ ◁ array_t n (maybe_uninit ty) ={lftE}=∗
  ∃ v : val, ⌜length v = (ly_size ly * n)%nat⌝ ∗
    l ◁ₗ[π, Owned] #v @ ◁ value_t false (LiteralSynType (mk_array_layout ly n)) ∗
    (∀ l' (m : nat) suffix,
      ⌜n ≤ m⌝%nat -∗ ⌜(ly_size ly * m ≤ MaxInt ISize)%Z⌝ -∗
      l' ◁ₗ[π, Owned] #(v ++ suffix) @ ◁ value_t false (LiteralSynType (mk_array_layout ly m)) ={lftE}=∗
      l' ◁ₗ[π, Owned] #(rs ++ replicate (m - n) (#None)) @ ◁ array_t m (maybe_uninit ty)).
Proof.
  intros Hlayout.
  have Hmaybe : syn_type_has_layout (st_of (maybe_uninit ty) MetaNone) ly
    by apply syn_type_has_layout_untyped.
  have Hmaybe_alg : use_layout_alg (st_of (maybe_uninit ty) MetaNone) = Some ly
    by apply syn_type_has_layout_op_alg in Hmaybe as (? & ? & ?); solve_layout_alg.
  rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iIntros "(%array_ly & %Hlayout' & %Halign & _ & #Hbounds & %rs' & -> & Hv)".
  apply syn_type_has_layout_array_inv in Hlayout' as (ly' & Hlayout' & -> & Hsize).
  have Hly : ly' = ly by eapply syn_type_has_layout_inj.
  subst ly'.
  rewrite ly_size_mk_array_layout Nat2Z.inj_mul in Hsize.
  iMod "Hv" as (v) "[Hl Hsaved]".
  have Harray : syn_type_has_layout (st_of (array_t n (maybe_uninit ty)) MetaNone) (mk_array_layout ly n).
  { eapply syn_type_has_layout_array; [reflexivity | exact Hmaybe | exact Hsize]. }
  iPoseProof (ty_own_val_has_layout _ _ _ _ _ _ Harray with "Hsaved") as "%Hvsize".
  iModIntro. iExists v. iSplitR.
  { iPureIntro. exact Hvsize. }
  iSplitL "Hl".
  { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists (mk_array_layout ly n). iSplitR.
    { iPureIntro. apply syn_type_has_layout_untyped.
      eapply syn_type_has_layout_make_literal; [reflexivity | exact Harray]. }
    iR. iSplitR; first by rewrite /value_t /ty_sidecond /=. iFrame "Hbounds".
    iExists v. iR. iModIntro. iExists v. iFrame "Hl".
    iApply value_t_untyped_equiv. iExists (mk_array_layout ly n). iR.
    iSplitR; last done. iPureIntro.
    eapply syn_type_has_layout_make_literal; [reflexivity | exact Harray]. }
  iIntros (l' m suffix Hnm Hsize').
  rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iIntros "(%ly' & %Hnewlayout & %Halign' & _ & #Hbounds' & %v' & <- & Hv)".
  apply syn_type_has_layout_untyped_inv in Hnewlayout.
  apply syn_type_has_layout_literal_inv in Hnewlayout as (-> & _).
  iMod "Hv" as (bytes) "[Hl Hv]".
  iDestruct (value_t_untyped_equiv with "Hv") as "(%ly' & -> & %Halg & %Hbytes)".
  apply syn_type_has_layout_literal_inv in Halg as (-> & _).
  iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iExists (mk_array_layout ly m).
  iSplitR. { iPureIntro. eapply syn_type_has_layout_array; [reflexivity | exact Hmaybe | exact Hsize']. }
  iR. iSplitR; first done. iFrame "Hbounds'".
  iExists (rs' ++ replicate (m - n) (#None)). iR. iModIntro.
  iExists (v ++ suffix). iFrame "Hl".
  replace m with (n + (m - n))%nat by lia.
  iApply (array_t_own_val_merge with "Hsaved").
  { rewrite /size_of_st /use_layout_alg' Hmaybe_alg. simpl. nia. }
  rewrite /ty_own_val /= array_t_own_val_unfold.
  iExists ly. iR. iR.
  iSplitR. { iPureIntro. nia. }
  rewrite length_replicate. iSplitR; first (iPureIntro; lia).
  iSplitR. { iPureIntro. rewrite /has_layout_val length_app ly_size_mk_array_layout in Hbytes.
    rewrite /has_layout_val ly_size_mk_array_layout in Hvsize.
    rewrite /has_layout_val ly_size_mk_array_layout. nia. }
  iApply big_sepL2_intro; first by rewrite length_replicate length_reshape length_replicate; lia.
  iModIntro. iIntros (i r bytes' Hr Hbytes').
  apply lookup_replicate in Hr as (-> & Hi).
  iExists None. iR. rewrite maybe_uninit_None_unfold uninit_own_spec.
  iR. iExists ly. iR. iPureIntro.
  apply list_elem_of_lookup_2 in Hbytes'.
  apply reshape_replicate_elem_length in Hbytes'; first done.
  rewrite /has_layout_val length_app ly_size_mk_array_layout in Hbytes.
  rewrite /has_layout_val ly_size_mk_array_layout in Hvsize. nia.
Qed.

(* Shrinking keeps the semantic ownership of the retained element prefix. *)
Lemma raw_vec_array_bytes_shrink `{!refinedrustGS Σ} {rt} (ty : type rt) π l ly (n : nat) rs :
  syn_type_has_layout (st_of ty MetaNone) ly →
  l ◁ₗ[π, Owned] #rs @ ◁ array_t n (maybe_uninit ty) ={lftE}=∗
  ∃ v : val,
    ⌜length v = (ly_size ly * n)%nat⌝ ∗
    l ◁ₗ[π, Owned] #v @ ◁ value_t false (LiteralSynType (mk_array_layout ly n)) ∗
    (∀ l' (m : nat), ⌜m ≤ n⌝%nat -∗
      ⌜(ly_size ly * m ≤ MaxInt ISize)%Z⌝ -∗
      l' ◁ₗ[π, Owned] #(take (ly_size ly * m) v) @ ◁ value_t false (LiteralSynType (mk_array_layout ly m)) ={lftE}=∗
      l' ◁ₗ[π, Owned] #(take m rs) @ ◁ array_t m (maybe_uninit ty)).
Proof.
  intros Hlayout.
  have Hmaybe : syn_type_has_layout (st_of (maybe_uninit ty) MetaNone) ly
    by apply syn_type_has_layout_untyped.
  have Hmaybe_alg : use_layout_alg (st_of (maybe_uninit ty) MetaNone) = Some ly
    by apply syn_type_has_layout_op_alg in Hmaybe as (? & ? & ?); solve_layout_alg.
  rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iIntros "(%array_ly & %Hlayout' & %Halign & _ & #Hbounds & %rs' & -> & Hv)".
  apply syn_type_has_layout_array_inv in Hlayout' as (ly' & Hlayout' & -> & Hsize).
  have Hly : ly' = ly by eapply syn_type_has_layout_inj. subst ly'.
  rewrite ly_size_mk_array_layout Nat2Z.inj_mul in Hsize.
  iMod "Hv" as (v) "[Hl Hsaved]".
  have Harray : syn_type_has_layout (st_of (array_t n (maybe_uninit ty)) MetaNone) (mk_array_layout ly n).
  { eapply syn_type_has_layout_array; [reflexivity | exact Hmaybe | exact Hsize]. }
  iPoseProof (ty_own_val_has_layout _ _ _ _ _ _ Harray with "Hsaved") as "%Hvsize".
  iPoseProof (array_t_rfn_length_eq with "Hsaved") as "%Hrs".
  iModIntro. iExists v. iSplitR; first done. iSplitL "Hl".
  { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists (mk_array_layout ly n). iSplitR.
    { iPureIntro. apply syn_type_has_layout_untyped.
      eapply syn_type_has_layout_make_literal; [reflexivity | exact Harray]. }
    iR. iSplitR; first by rewrite /value_t /ty_sidecond /=. iFrame "Hbounds".
    iExists v. iR. iModIntro. iExists v. iFrame "Hl".
    iApply value_t_untyped_equiv. iExists (mk_array_layout ly n). iR.
    iSplitR; last done. iPureIntro.
    eapply syn_type_has_layout_make_literal; [reflexivity | exact Harray]. }
  iIntros (l' m Hmn Hsize').
  iIntros "Hbytes".
  iPoseProof (array_t_own_val_split (maybe_uninit ty) π m (n - m)
    (take (ly_size ly * m) v) (drop (ly_size ly * m) v)
    (take m rs') (drop m rs') MetaNone with "[Hsaved]") as "[Hprefix _]".
  { rewrite length_take Hrs. lia. }
  { rewrite length_drop Hrs. done. }
  { rewrite length_take /size_of_st /use_layout_alg' Hmaybe_alg /=.
    rewrite /has_layout_val ly_size_mk_array_layout in Hvsize. nia. }
  { rewrite length_drop /size_of_st /use_layout_alg' Hmaybe_alg /=.
    rewrite /has_layout_val ly_size_mk_array_layout in Hvsize. nia. }
  { rewrite !take_drop. replace (m + (n - m))%nat with n by lia. done. }
  rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iDestruct "Hbytes" as "(%ly' & %Hnewlayout & %Halign' & _ & #Hbounds' & %v' & <- & Hv)".
  apply syn_type_has_layout_untyped_inv in Hnewlayout.
  apply syn_type_has_layout_literal_inv in Hnewlayout as (-> & _).
  iMod "Hv" as (bytes) "[Hl Hv]".
  iDestruct (value_t_untyped_equiv with "Hv") as "(%ly' & -> & %Halg & %Hbytes)".
  iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
  iExists (mk_array_layout ly m). iSplitR.
  { iPureIntro. eapply syn_type_has_layout_array; [reflexivity | exact Hmaybe | exact Hsize']. }
  iR. iSplitR; first done. iFrame "Hbounds'".
  iExists (take m rs'). iR. iModIntro. iExists (take (ly_size ly * m) v).
  iFrame "Hl Hprefix".
Qed.

Lemma raw_vec_shrink_capacity (size stored requested : nat) :
  (requested ≤ raw_vec_effective_capacity size stored)%nat →
  let stored' := if decide (size * stored = 0)%nat then stored else requested in
  (stored' ≤ stored)%nat ∧
  raw_vec_effective_capacity size stored' = raw_vec_effective_capacity size requested ∧
  (size * stored' = size * requested)%nat.
Proof.
  intros Hrequested. cbn zeta.
  unfold raw_vec_effective_capacity in *.
  repeat case_decide; repeat split; nia.
Qed.

(* With a valid logical length, wrapping subtraction is ordinary subtraction. *)
Lemma raw_vec_capacity_sub_no_wrap (cap : nat) (len : Z) :
  (cap ≤ MaxInt USize)%Z →
  (0 ≤ len ≤ cap)%Z →
  ((Z.of_nat cap - len) mod (MaxInt USize + 1) = Z.of_nat cap - len)%Z.
Proof.
  intros Hcap Hlen. apply Z.mod_small. lia.
Qed.

Lemma raw_vec_needs_to_grow_iff (cap : nat) (len additional : Z) :
  (cap ≤ MaxInt USize)%Z →
  (0 ≤ len ≤ cap)%Z →
  bool_decide (additional > (Z.of_nat cap - len) mod (MaxInt USize + 1)) =
    bool_decide (cap < len + additional).
Proof.
  intros Hcap Hlen.
  rewrite raw_vec_capacity_sub_no_wrap; [|done..].
  apply bool_decide_ext. lia.
Qed.

Lemma raw_vec_capacity_sufficient (cap : nat) (len additional : Z) :
  (cap ≤ MaxInt USize)%Z →
  (0 ≤ len ≤ cap)%Z →
  bool_decide (additional > (Z.of_nat cap - len) mod (MaxInt USize + 1)) = false ↔
    (len + additional ≤ cap)%Z.
Proof.
  intros Hcap Hlen. rewrite raw_vec_needs_to_grow_iff; [|done..].
  rewrite bool_decide_eq_false. lia.
Qed.

(* RawVec's field is not its reported capacity for zero-sized elements. *)
Definition raw_vec_capacity_valid `{!LayoutAlg} (st : syn_type) (stored cap : nat) : Prop :=
  (stored ≤ Z.to_nat (MaxInt ISize))%nat ∧
  cap = (if decide (size_of_st st = 0%nat)
         then Z.to_nat (MaxInt USize) else stored) ∧
  (if decide (size_of_st st = 0%nat) then stored = 0%nat
   else (size_of_array_in_bytes st stored ≤ MaxInt ISize)%Z).

(* As with unconditional allocator permissions, shared access exposes no
   allocation token; ghost-drop may forget it without deallocating memory. *)
Global Instance raw_vec_shareable_optional `{!refinedrustGS Σ} π κ κs
    (P : Prop) `{!Decision P} (Q : iProp Σ) :
  Shareable π κ κs (if decide P then True else Q)%I :=
  shareable_discard _ _ _ _.

Global Instance raw_vec_ghost_droppable_optional `{!refinedrustGS Σ}
    (P : Prop) `{!Decision P} (Q : iProp Σ) :
  GhostDroppable (if decide P then True else Q)%I :=
  ghost_droppable_discard _.

#[universes(polymorphic)]
Definition extract_val {rt : RT} (r : place_rfn rt) := if r is #r then Some r else None.

Section project_vec_els.
  Context {rt : RT}.
  Set Universe Polymorphism.

  Definition project_vec_els (len : nat) (els : list (place_rfn (option (place_rfn rt))))
    : list (place_rfn rt) :=
    (λ x, default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)) <$> (take len els).

  Lemma project_vec_els_lookup_Some len i els x :
    project_vec_els len els !! i = Some x →
    ∃ x', els !! i = Some x' ∧ x = default (👻 inhabitant) (extract_val x' ≫= id) ∧ (i < len)%nat. 
  Proof.
    rewrite /project_vec_els.
    rewrite list_lookup_fmap_Some.
    intros (x' & Heq & Hlook).
    apply lookup_take_Some in Hlook as (Hlook & ?).
    eauto.
  Qed.

  Lemma project_vec_els_length len els :
    length (project_vec_els len els) = (len `min` length els)%nat.
  Proof. by rewrite /project_vec_els length_fmap length_take. Qed.


  Global Instance is_xrfn_vec_hint
      (els : list (place_rfn (option (place_rfn rt))))
      (xr : list (RT_xt rt)) len cap:
    TCDone (∀ i : nat, (0 ≤ i < len)%nat →
      els !! i = Some (#(Some ((PlaceIn ∘ RT_xrt rt <$> xr) !!! i)))) →
    TCDone (∀ i : nat, (len ≤ i < cap)%nat → els !! i = Some (#None)) →
    TCDone (length els = cap) →
    TCDone ((PlaceIn ∘ RT_xrt rt <$> xr) = project_vec_els len els) →
    IsXrfn els.
  Proof.
    unfold TCDone. intros Hlook1 Hlook2 Hlen Hx.
    constructor. apply is_xrfn_list_iff, Forall_forall.
    intros x (i & Hlook)%list_elem_of_lookup_1.
    have Hiels : (i < length els)%nat by apply lookup_lt_Some in Hlook.
    destruct (decide (i < len)) as [Hi | Hi].
    - opose proof (Hlook1 i _) as Hlook'; first lia.
      rewrite Hlook in Hlook'. simplify_eq.
      have Hixr : (i < length ((PlaceIn ∘ RT_xrt rt) <$> xr))%nat.
      { rewrite Hx project_vec_els_length. lia. }
      rewrite length_fmap in Hixr.
      destruct (lookup_lt_is_Some_2 xr i Hixr) as (xri & Hxri).
      erewrite list_lookup_total_correct; last by rewrite list_lookup_fmap Hxri.
      apply is_xrfn_proof.
    - opose proof (Hlook2 i _) as Hlook'; first lia.
      rewrite Hlook in Hlook'. simplify_eq. apply is_xrfn_proof.
  Qed.
End project_vec_els.
