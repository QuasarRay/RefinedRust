From refinedrust Require Import typing.
From rrstd.vec.theories Require Import vec.
From rrstd.alloc.theories Require Import layout.
From rrstd.ptr.theories Require Import specs.
From rrstd.ptr.ptr.generated Require Import generated_specs_ptr.

Lemma raw_vec_layout_roundtrip ly :
  ly_align ly ∈ usize →
  rust_layout_to_layout (mk_rust_layout (ly_size ly) (alignment_of_align (ly_align ly))) = ly.
Proof.
  intros Hrange.
  have Halign : ly_align (rust_layout_to_layout (mk_rust_layout (ly_size ly)
      (alignment_of_align (ly_align ly)))) = ly_align ly.
  { rewrite ly_align_of_rust_layout_align; [by rewrite Nat2Z.id | | done].
    rewrite Nat2Z.id. eexists _. reflexivity. }
  apply (proj2 (ly_align_log_ly_align_eq_iff _ _)) in Halign.
  destruct ly. simpl in *.
  unfold rust_layout_to_layout. simpl. f_equal. exact Halign.
Qed.

Lemma raw_vec_alignment_roundtrip ly :
  alignment_of_align (layout_alignment_nat ly) = layout_alignment ly.
Proof.
  rewrite /layout_alignment_nat /alignment_to_align_nat Nat2Z.inj_pow /=.
  rewrite -/alignment_to_align alignment_from_to. reflexivity.
Qed.

Section allocation.
  Context `{!refinedrustGS Σ}.

  (* The permission is indexed by the requested extent, not the allocator's
     possibly larger returned block. Its interpretation records that this
     layout fits the allocation; no slice metadata or exact-size assumption is
     exposed by the trusted boundary. *)
  Definition raw_allocation (π : thread_id) (freeable : loc → nat → iProp Σ)
      (l : loc) (ly : layout) (v : val) : iProp Σ :=
    (⌜l.(loc_a) ≠ 0 ∧ l `has_layout_loc` ly ∧ length v = ly_size ly⌝ ∗
    freeable l (ly_size ly) ∗
    l ◁ₗ[π, Owned] #v @ ◁ value_t false (LiteralSynType ly))%I.

  (* RawVecInner keeps allocation ownership external to its structural type. *)
  Definition raw_vec_storage (π : thread_id) (freeable : loc → nat → iProp Σ)
      (l : loc) (cap : nat) (elem_layout : layout) (v : val) : iProp Σ :=
    (if decide (ly_size elem_layout * cap = 0)%nat then
       ⌜v = [] ∧ l.(loc_a) ≠ 0 ∧ l `has_layout_loc` elem_layout⌝ ∗
       loc_in_bounds l 0 0
     else raw_allocation π freeable l (mk_array_layout elem_layout cap) v)%I.

  Lemma raw_vec_storage_bytes {rt} (ty : type rt) π freeable l (stored : nat) ly v :
    syn_type_has_layout (st_of ty MetaNone) ly →
    (ly_size ly * stored ≤ MaxInt ISize)%Z →
    raw_vec_storage π freeable l stored ly v -∗
    let cap := raw_vec_effective_capacity (ly_size ly) stored in
    ⌜l.(loc_a) ≠ 0 ∧ l `has_layout_loc` ly⌝ ∗
    (if decide (ly_size ly * cap = 0)%nat then True else freeable l (ly_size ly * cap)%nat) ∗
    l ◁ₗ[π, Owned] #v @ ◁ value_t false (LiteralSynType (mk_array_layout ly cap)).
  Proof.
    intros Hlayout Hsize. iIntros "Hstorage".
    rewrite /raw_vec_storage. case_decide as Hzero.
    - iDestruct "Hstorage" as "[(%Hv & %Hnonnull & %Halign) #Hbounds]". subst v.
      have Hzero' : (ly_size ly * raw_vec_effective_capacity (ly_size ly) stored = 0)%nat.
      { unfold raw_vec_effective_capacity. destruct (decide (ly_size ly = 0%nat)); nia. }
      have Harray : syn_type_has_layout
          (st_of (array_t (raw_vec_effective_capacity (ly_size ly) stored) (maybe_uninit ty)) MetaNone)
          (mk_array_layout ly (raw_vec_effective_capacity (ly_size ly) stored)).
      { eapply syn_type_has_layout_array; [reflexivity | by apply syn_type_has_layout_untyped |].
        rewrite -Nat2Z.inj_mul Hzero'. pose proof (MaxInt_ge_127 ISize). lia. }
      rewrite Hzero' /=. iR. iSplitR; first done.
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists (mk_array_layout ly (raw_vec_effective_capacity (ly_size ly) stored)).
      iSplitR. { iPureIntro. apply syn_type_has_layout_untyped.
        eapply syn_type_has_layout_make_literal; [reflexivity | exact Harray]. }
      iSplitR. { iPureIntro. by rewrite /has_layout_loc ly_align_mk_array_layout. }
      iSplitR; first by rewrite /value_t /ty_sidecond /=.
      rewrite ly_size_mk_array_layout Hzero'. iFrame "Hbounds".
      iExists ([] : val). iR. iModIntro. iExists ([] : val).
      iSplitR. { by rewrite heap_pointsto_nil. }
      iApply value_t_untyped_equiv.
      iExists (mk_array_layout ly (raw_vec_effective_capacity (ly_size ly) stored)). iR.
      iSplitR. { iPureIntro. eapply syn_type_has_layout_make_literal; [reflexivity | exact Harray]. }
      iPureIntro. by rewrite /has_layout_val ly_size_mk_array_layout Hzero'.
    - have Hcap : raw_vec_effective_capacity (ly_size ly) stored = stored.
      { rewrite /raw_vec_effective_capacity decide_False; [done | nia]. }
      rewrite Hcap decide_False; last done.
      iDestruct "Hstorage" as "[(%Hnonnull & %Halign & %Hlength) [Hfree Hbytes]]".
      iFrame. iPureIntro. split; first done.
      by rewrite /has_layout_loc ly_align_mk_array_layout in Halign.
  Qed.

  Lemma raw_vec_bytes_storage {rt} (ty : type rt) π freeable l (stored : nat) ly v :
    syn_type_has_layout (st_of ty MetaNone) ly →
    (ly_size ly * stored ≤ MaxInt ISize)%Z →
    l.(loc_a) ≠ 0 → l `has_layout_loc` ly →
    let cap := raw_vec_effective_capacity (ly_size ly) stored in
    (if decide (ly_size ly * cap = 0)%nat then True else freeable l (ly_size ly * cap)%nat) -∗
    l ◁ₗ[π, Owned] #v @ ◁ value_t false (LiteralSynType (mk_array_layout ly cap)) -∗
    |={lftE}=> raw_vec_storage π freeable l stored ly v.
  Proof.
    intros Hlayout Hsize Hnonnull Halign. cbn zeta. iIntros "Hfree Hbytes".
    iPoseProof (ltype_own_has_layout with "Hbytes") as "(%ly' & %Halg & %Halign')".
    apply syn_type_has_layout_untyped_inv in Halg.
    iMod (ofty_value_has_length with "Hbytes") as "(%Hv & Hbytes)"; [done | exact Halg |].
    have Hbytealg := Halg.
    apply syn_type_has_layout_literal_inv in Halg as (-> & _).
    iModIntro.
    rewrite /raw_vec_storage.
    destruct (decide (ly_size ly * stored = 0)%nat) as [Hzero | Hzero].
    - have Hzero' : (ly_size ly * raw_vec_effective_capacity (ly_size ly) stored = 0)%nat.
      { unfold raw_vec_effective_capacity. destruct (decide (ly_size ly = 0%nat)); nia. }
      iPoseProof (ltype_own_loc_in_bounds with "Hbytes") as "Hbounds".
      { apply syn_type_has_layout_untyped. exact Hbytealg. }
      rewrite ly_size_mk_array_layout Hzero'. iFrame "Hbounds".
      iPureIntro. split; last done.
      apply length_zero_iff_nil. move: Hv. rewrite /has_layout_val ly_size_mk_array_layout Hzero'. done.
    - have Hcap : raw_vec_effective_capacity (ly_size ly) stored = stored.
      { rewrite /raw_vec_effective_capacity decide_False; [done | nia]. }
      iEval (rewrite Hcap decide_False; last done) in "Hfree".
      iEval (rewrite Hcap) in "Hbytes".
      rewrite /raw_allocation. iFrame.
      iPureIntro. split; first done. split.
      { by rewrite /has_layout_loc ly_align_mk_array_layout. }
      move: Hv. by rewrite Hcap /has_layout_val.
  Qed.

  (* Expose bytes without forgetting the old elements, and retain the means to
     restore their ownership at the location returned by the allocator. *)
  Lemma raw_vec_array_storage {rt} (ty : type rt) π freeable l (stored : nat) ly rs :
    syn_type_has_layout (st_of ty MetaNone) ly →
    (ly_size ly * stored ≤ MaxInt ISize)%Z →
    l.(loc_a) ≠ 0 → l `has_layout_loc` ly →
    let cap := raw_vec_effective_capacity (ly_size ly) stored in
    (if decide (ly_size ly * cap = 0)%nat then True else freeable l (ly_size ly * cap)%nat) -∗
    l ◁ₗ[π, Owned] #rs @ ◁ array_t cap (maybe_uninit ty) ={lftE}=∗
    ∃ v : val, raw_vec_storage π freeable l stored ly v ∗
    (∀ l' (stored' : nat) suffix,
      ⌜cap ≤ raw_vec_effective_capacity (ly_size ly) stored'⌝%nat -∗
      ⌜(ly_size ly * stored' ≤ MaxInt ISize)%Z⌝ -∗
      raw_vec_storage π freeable l' stored' ly (v ++ suffix) ={lftE}=∗
      ⌜l'.(loc_a) ≠ 0 ∧ l' `has_layout_loc` ly⌝ ∗
      (if decide (ly_size ly * raw_vec_effective_capacity (ly_size ly) stored' = 0)%nat
       then True else freeable l' (ly_size ly * raw_vec_effective_capacity (ly_size ly) stored')%nat) ∗
      l' ◁ₗ[π, Owned] #(rs ++ replicate (raw_vec_effective_capacity (ly_size ly) stored' - cap) (#None))
        @ ◁ array_t (raw_vec_effective_capacity (ly_size ly) stored') (maybe_uninit ty)).
  Proof.
    intros Hlayout Hsize Hnonnull Halign. cbn zeta. iIntros "Hfree Harray".
    iMod (raw_vec_array_bytes with "Harray") as (v) "(%Hlength & Hbytes & Hrestore)"; first done.
    iMod (raw_vec_bytes_storage with "Hfree Hbytes") as "Hstorage"; [done.. |].
    iModIntro. iExists v. iFrame "Hstorage".
    iIntros (l' stored' suffix Hcap Hsize') "Hstorage".
    iPoseProof (raw_vec_storage_bytes ty with "Hstorage") as "(%Hptr & Hfree & Hbytes)"; [done.. |].
    iMod ("Hrestore" with "[] [] Hbytes") as "Harray"; [done | |].
    { iPureIntro. unfold raw_vec_effective_capacity.
      destruct (decide (ly_size ly = 0%nat)) as [Hzero | Hnonzero]; last done.
      rewrite Hzero. pose proof (MaxInt_ge_127 ISize). lia. }
    iModIntro. iFrame. done.
  Qed.

  Lemma raw_vec_array_storage_shrink {rt} (ty : type rt) π freeable l (stored : nat) ly rs :
    syn_type_has_layout (st_of ty MetaNone) ly →
    (ly_size ly * stored ≤ MaxInt ISize)%Z →
    l.(loc_a) ≠ 0 → l `has_layout_loc` ly →
    let cap := raw_vec_effective_capacity (ly_size ly) stored in
    (if decide (ly_size ly * cap = 0)%nat then True else freeable l (ly_size ly * cap)%nat) -∗
    l ◁ₗ[π, Owned] #rs @ ◁ array_t cap (maybe_uninit ty) ={lftE}=∗
    ∃ v : val, ⌜length v = (ly_size ly * stored)%nat⌝ ∗ raw_vec_storage π freeable l stored ly v ∗
    (∀ l' (stored' : nat),
      ⌜raw_vec_effective_capacity (ly_size ly) stored' ≤ cap⌝%nat -∗
      ⌜(ly_size ly * stored' ≤ MaxInt ISize)%Z⌝ -∗
      raw_vec_storage π freeable l' stored' ly (take (ly_size ly * stored') v) ={lftE}=∗
      ⌜l'.(loc_a) ≠ 0 ∧ l' `has_layout_loc` ly⌝ ∗
      (if decide (ly_size ly * raw_vec_effective_capacity (ly_size ly) stored' = 0)%nat
       then True else freeable l' (ly_size ly * raw_vec_effective_capacity (ly_size ly) stored')%nat) ∗
      l' ◁ₗ[π, Owned] #(take (raw_vec_effective_capacity (ly_size ly) stored') rs)
        @ ◁ array_t (raw_vec_effective_capacity (ly_size ly) stored') (maybe_uninit ty)).
  Proof.
    intros Hlayout Hsize Hnonnull Halign. cbn zeta. iIntros "Hfree Harray".
    iMod (raw_vec_array_bytes_shrink with "Harray") as (v) "(%Hlength & Hbytes & Hrestore)"; first done.
    iMod (raw_vec_bytes_storage with "Hfree Hbytes") as "Hstorage"; [done.. |].
    iModIntro. iExists v. iSplitR.
    { iPureIntro. rewrite Hlength. unfold raw_vec_effective_capacity. case_decide; nia. }
    iFrame "Hstorage".
    iIntros (l' stored' Hcap Hsize') "Hstorage".
    iPoseProof (raw_vec_storage_bytes ty with "Hstorage") as "(%Hptr & Hfree & Hbytes)"; [done.. |].
    have Hbytesize : (ly_size ly * raw_vec_effective_capacity (ly_size ly) stored' = ly_size ly * stored')%nat.
    { unfold raw_vec_effective_capacity. case_decide; nia. }
    iMod ("Hrestore" with "[] [] [Hbytes]") as "Harray"; [done | | |].
    { iPureIntro. unfold raw_vec_effective_capacity.
      destruct (decide (ly_size ly = 0%nat)) as [Hzero | Hnonzero]; last done.
      rewrite Hzero. pose proof (MaxInt_ge_127 ISize). lia. }
    { by rewrite Hbytesize. }
    iModIntro. iFrame. done.
  Qed.

  Lemma raw_vec_storage_array {rt} (ty : type rt) π freeable l (stored : nat) ly v :
    syn_type_has_layout (st_of ty MetaNone) ly →
    (ly_size ly * stored ≤ MaxInt ISize)%Z →
    ty_sidecond ty -∗ raw_vec_storage π freeable l stored ly v -∗
    let cap := raw_vec_effective_capacity (ly_size ly) stored in
    ⌜l.(loc_a) ≠ 0 ∧ l `has_layout_loc` ly⌝ ∗
    (if decide (ly_size ly * cap = 0)%nat then True else freeable l (ly_size ly * cap)%nat) ∗
    l ◁ₗ[π, Owned] #(replicate cap (#None)) @ ◁ array_t cap (maybe_uninit ty).
  Proof.
    intros Hlayout Hsize. iIntros "#Hsc Hstorage".
    rewrite /raw_vec_storage. case_decide as Hzero.
    - iDestruct "Hstorage" as "[(%Hv & %Hnonzero & %Halign) #Hbounds]".
      have Hzero' : (ly_size ly * raw_vec_effective_capacity (ly_size ly) stored = 0)%nat.
      { unfold raw_vec_effective_capacity. case_decide; nia. }
      rewrite Hzero' /=. iR. iSplitR; first done.
      iApply (raw_vec_zero_array with "Hsc Hbounds"); done.
    - have Hnonzero : ly_size ly ≠ 0%nat by nia.
      have Hcap : raw_vec_effective_capacity (ly_size ly) stored = stored.
      { by rewrite /raw_vec_effective_capacity decide_False. }
      rewrite Hcap decide_False; last done.
      iDestruct "Hstorage" as "[(%Hptr & %Halign & %Hlength) [Hfree Hv]]".
      iSplitR. { iPureIntro. split; first done.
        by rewrite /has_layout_loc ly_align_mk_array_layout in Halign. }
      iFrame "Hfree".
      iApply (raw_vec_bytes_array with "Hv"); done.
  Qed.
End allocation.
