From refinedrust Require Import typing shims.

Record LinkedListX (T A : Type) : Type := mk_linked_list_x {
  linked_list_elems : list T;
  linked_list_locs : list loc;
  linked_list_alloc : A;
}.
Global Arguments linked_list_elems {_ _}.
Global Arguments linked_list_locs {_ _}.
Global Arguments linked_list_alloc {_ _}.
Global Arguments mk_linked_list_x {_ _}.

Definition LinkedListRT (T A : RT) : RT :=
  mk_RT
    (LinkedListX (RT_rt (place_rfnRT T)) (RT_xt A))
    (LinkedListX (RT_xt (place_rfnRT T)) (RT_xt A))
    (λ p, mk_linked_list_x (RT_xrt (list (place_rfn T)) p.(linked_list_elems))
      p.(linked_list_locs) p.(linked_list_alloc)).
Canonical Structure LinkedListRT.

(** A shared cursor records its list snapshot and position. *)
Record CursorX (L : Type) : Type := mk_cursor_x {
  shared_cursor_list : L;
  shared_cursor_pos : nat;
}.
Global Arguments shared_cursor_list {_}.
Global Arguments shared_cursor_pos {_}.
Global Arguments mk_cursor_x {_}.

Definition CursorRT (T A : RT) : RT :=
  mk_RT
    (CursorX (RT_rt (LinkedListRT T A)))
    (CursorX (RT_xt (LinkedListRT T A)))
    (λ c, mk_cursor_x (RT_xrt (LinkedListRT T A) c.(shared_cursor_list))
      c.(shared_cursor_pos)).
Canonical Structure CursorRT.

Global Instance CursorX_inh (T A : RT) :
  Inhabited (RT_xt (LinkedListRT T A)) → Inhabited (RT_xt (CursorRT T A)).
Proof.
  intros ?. refine (populate (mk_cursor_x inhabitant 0%nat)).
Qed.

(** A mutable cursor retains the list borrow's ghost name so its eventual
    value remains observable through the cursor refinement. *)
Record CursorMutX (L : Type) : Type := mk_cursor_mut_x {
  cursor_list : L;
  cursor_pos : nat;
  cursor_ghost : gname;
}.
Global Arguments cursor_list {_}.
Global Arguments cursor_pos {_}.
Global Arguments cursor_ghost {_}.
Global Arguments mk_cursor_mut_x {_}.

Definition CursorMutRT (T A : RT) : RT :=
  mk_RT
    (CursorMutX (RT_rt (LinkedListRT T A)))
    (CursorMutX (RT_xt (LinkedListRT T A)))
    (λ c, mk_cursor_mut_x (RT_xrt (LinkedListRT T A) c.(cursor_list))
      c.(cursor_pos) c.(cursor_ghost)).
Canonical Structure CursorMutRT.

Global Instance CursorMutX_inh (T A : RT) :
  Inhabited (RT_xt (LinkedListRT T A)) → Inhabited (RT_xt (CursorMutRT T A)).
Proof.
  intros ?. refine (populate (mk_cursor_mut_x inhabitant 0%nat inhabitant)).
Qed.

(** The ghost cursor position is the length of the list. *)
Definition cursor_next (p n : nat) : nat :=
  if decide (p = n) then 0%nat else S p.

Definition cursor_prev (p n : nat) : nat :=
  if decide (p = n) then Nat.pred n else
  if decide (p = 0%nat) then n else Nat.pred p.

Global Instance LinkedListX_inh (T A : RT) :
  Inhabited (RT_xt A) → Inhabited (RT_xt (LinkedListRT T A)).
Proof.
  intros HA.  refine (populate (mk_linked_list_x [] [] inhabitant)).
Qed.

Global Instance LinkedListX_simpl_exist T A :
  SimplExist (LinkedListX T A)
    (λ H, ∃ (xs : name_hint_ty "self" (list T)) (locs : name_hint_ty "locs" (list loc)) (a : name_hint_ty "a" (A)), H (mk_linked_list_x xs locs a)).
Proof.
  intros ? (xs & locs & a & Ha). eexists _. done.
Qed.

Global Instance LinkedListX_simpl_forall T A :
  SimplForall (LinkedListX T A) 3
    (λ H, ∀ (xs : name_hint_ty "self" (list T)) (locs : name_hint_ty "locs" (list loc)) (a : name_hint_ty "a" (A)), H (mk_linked_list_x xs locs a)).
Proof.
  intros ? Ha [xs locs a]. apply Ha.
Qed.

Global Instance simpl_both_LinkedListX {T A} (x1 x2 : LinkedListX T A) :
  SimplBothRel (=) x1 x2
    (x1.(linked_list_elems) = x2.(linked_list_elems) ∧
     x1.(linked_list_locs) = x2.(linked_list_locs) ∧
     x1.(linked_list_alloc) = x2.(linked_list_alloc)).
Proof.
  unfold SimplBothRel. destruct x1, x2; naive_solver.
Qed.

(** Node ownership is supplied by the client: the generated [Node_inv_t] cannot
    be imported here, since the generated specifications import this theory.
    In particular, [node] can describe either owned or shared nodes, and
    [freeable] can be the allocator permission or [True]. *)
Section list_ownership.
  Context `{!typeGS Σ}.
  Context {E A : Type}.
  Context (node : loc → option loc → option loc → E → iProp Σ).
  Context (freeable : A → loc → iProp Σ).

  Definition LL_item (locs : list loc) (alloc : A) (i : nat) (elem : E) : iProp Σ :=
    ∃ l next prev,
      ⌜locs !! i = Some l⌝ ∗
      ⌜locs !! S i = next⌝ ∗
      ⌜(None :: (Some <$> locs)) !! i = Some prev⌝ ∗
      node l next prev elem ∗ freeable alloc l.

  Definition LL_segment (offset : nat) (elems : list E)
      (locs : list loc) (alloc : A) : iProp Σ :=
    [∗ list] i ↦ elem ∈ elems, LL_item locs alloc (offset + i) elem.

  Definition LL (elems : list E) (locs : list loc) (alloc : A) : iProp Σ :=
    [∗ list] i ↦ elem ∈ elems, LL_item locs alloc i elem.

  Definition LL_except (i : nat) (elems : list E)
      (locs : list loc) (alloc : A) : iProp Σ :=
    [∗ list] j ↦ elem ∈ elems,
      if decide (j = i) then emp else LL_item locs alloc j elem.

  Lemma LL_nil locs alloc : LL [] locs alloc ⊣⊢ emp.
  Proof. by rewrite /LL big_sepL_nil. Qed.

  Lemma LL_segment_nil offset locs alloc :
    LL_segment offset [] locs alloc ⊣⊢ emp.
  Proof. by rewrite /LL_segment big_sepL_nil. Qed.

  Lemma simplify_goal_LL_nil locs alloc T :
    T ⊢ simplify_goal (LL [] locs alloc) T.
  Proof. rewrite /simplify_goal LL_nil. iIntros "$". Qed.
  Definition simplify_goal_LL_nil_inst :=
    [instance @simplify_goal_LL_nil with 0%N].
  Global Existing Instance simplify_goal_LL_nil_inst.

  Lemma LL_lookup elems locs alloc i elem :
    elems !! i = Some elem →
    LL elems locs alloc -∗ LL_item locs alloc i elem.
  Proof.
    intros Hlookup. unfold LL. by iApply big_sepL_lookup.
  Qed.

  Lemma LL_extract elems locs alloc i elem :
    elems !! i = Some elem →
    LL elems locs alloc ⊣⊢
    LL_item locs alloc i elem ∗ LL_except i elems locs alloc.
  Proof.
    intros Hlookup. unfold LL, LL_except.
    rewrite (big_sepL_delete _ _ i); last done.
    done.
  Qed.

  Lemma LL_cons elem elems locs alloc :
    LL (elem :: elems) locs alloc ⊣⊢
      LL_item locs alloc 0 elem ∗ LL_segment 1 elems locs alloc.
  Proof. by rewrite /LL /LL_segment big_sepL_cons /=. Qed.

  Lemma LL_segment_cons offset elem elems locs alloc :
    LL_segment offset (elem :: elems) locs alloc ⊣⊢
      LL_item locs alloc offset elem ∗
      LL_segment (S offset) elems locs alloc.
  Proof.
    rewrite /LL_segment big_sepL_cons /= Nat.add_0_r.
    f_equiv. apply big_sepL_proper. intros i x Hi.
    by rewrite Nat.add_succ_r.
  Qed.

  Lemma LL_segment_head offset elems elem locs alloc :
    head elems = Some elem →
    LL_segment offset elems locs alloc ⊣⊢
      LL_item locs alloc offset elem ∗
      LL_segment (S offset) (tail elems) locs alloc.
  Proof.
    intros Hhead. apply head_Some in Hhead as (rest & ->).
    by rewrite LL_segment_cons.
  Qed.

  Lemma LL_segment_rebase_suffix prefix locs elems alloc :
    LL_segment (length prefix + 1) elems (prefix ++ locs) alloc ⊣⊢
      LL_segment 1 elems locs alloc.
  Proof.
    have Hlookup (i : nat) :
        @lookup nat loc (list loc) _ (length prefix + i)%nat (prefix ++ locs) =
        @lookup nat loc (list loc) _ i locs.
    { rewrite lookup_app_r; [by replace (length prefix + i - length prefix)%nat with i by lia | lia]. }
    rewrite /LL_segment.
    apply big_sepL_proper. intros i elem Hi.
    replace (length prefix + 1 + i)%nat with (length prefix + S i)%nat by lia.
    rewrite /LL_item.
    have Hnext : (prefix ++ locs) !! S (length prefix + S i) = locs !! S (S i).
    { replace (S (length prefix + S i)%nat) with (length prefix + S (S i))%nat by lia.
      exact (Hlookup (S (S i))). }
    have Hprev :
        @lookup nat (option loc) (list (option loc)) _ (length prefix + S i)%nat
          (None :: (Some <$> (prefix ++ locs))) =
        @lookup nat (option loc) (list (option loc)) _ (S i)
          (None :: (Some <$> locs)).
    { replace (length prefix + S i)%nat with (S (length prefix + i)%nat) by lia.
      simpl. rewrite !list_lookup_fmap. by rewrite Hlookup. }
    by rewrite (Hlookup (S i)) Hnext Hprev.
  Qed.

  Lemma LL_rebase_head prefix old_locs new_locs old_elems new_elems elem n alloc :
    old_locs = prefix ++ new_locs →
    old_elems = new_elems →
    head new_elems = Some elem →
    n = S (length prefix) →
    LL new_elems new_locs alloc ⊣⊢
      LL_item new_locs alloc 0 elem ∗
      LL_segment n (tail old_elems) old_locs alloc.
  Proof.
    intros Hlocs Helems Hhead Hn.
    subst old_locs old_elems n.
    apply head_Some in Hhead as (rest & ->).
    simpl. rewrite LL_cons.
    replace (S (length prefix)) with (length prefix + 1)%nat by lia.
    by rewrite LL_segment_rebase_suffix.
  Qed.

  Lemma LL_segment_drop_head_suffix elems old_head_loc new_locs alloc :
    LL_segment 2 elems (old_head_loc :: new_locs) alloc ⊣⊢
      LL_segment 1 elems new_locs alloc.
  Proof.
    rewrite /LL_segment.
    apply big_sepL_proper. intros i elem Hi.
    rewrite /LL_item. simpl. reflexivity.
  Qed.

  Lemma LL_snoc elems elem locs alloc :
    LL (elems ++ [elem]) locs alloc ⊣⊢
      LL elems locs alloc ∗ LL_item locs alloc (length elems) elem.
  Proof. by rewrite /LL big_sepL_snoc. Qed.

  Lemma LL_segment_snoc offset elems elem locs alloc :
    LL_segment offset (elems ++ [elem]) locs alloc ⊣⊢
      LL_segment offset elems locs alloc ∗
      LL_item locs alloc (offset + length elems) elem.
  Proof. by rewrite /LL_segment big_sepL_snoc. Qed.

  Lemma LL_last elems elem locs alloc :
    last elems = Some elem →
    LL elems locs alloc ⊣⊢
      LL (removelast elems) locs alloc ∗
      LL_item locs alloc (length (removelast elems)) elem.
  Proof.
    intros Hlast. apply last_Some in Hlast as (prefix & ->).
    by rewrite removelast_last LL_snoc.
  Qed.

  Lemma LL_split elems locs alloc n :
    LL elems locs alloc ⊣⊢
      LL (take n elems) locs alloc ∗
      LL_segment n (drop n elems) locs alloc.
  Proof. by rewrite /LL /LL_segment big_sepL_take_drop. Qed.

  Lemma LL_prefix_stable_dir elems locs locs' alloc :
    take (S (length elems)) locs = take (S (length elems)) locs' →
    LL elems locs alloc ⊢ LL elems locs' alloc.
  Proof.
    intros Htake.
    have Hlookup k : (k < S (length elems))%nat → locs !! k = locs' !! k.
    { intros Hk.
      pose proof (f_equal (λ ls : list loc, ls !! k) Htake) as Hsame.
      rewrite !lookup_take in Hsame.
      destruct (decide (k < S (length elems))%nat); [exact Hsame | lia]. }
    rewrite /LL. iApply big_sepL_mono.
    iIntros (i elem Hi) "Hitem".
    rewrite /LL_item.
    iDestruct "Hitem" as (l next prev)
      "(%Hloc & %Hnext & %Hprev & Hnode & Hfree)".
    have Hi_lt : (i < length elems)%nat by eapply lookup_lt_Some.
    iExists l, next, prev. iFrame.
    iPureIntro. repeat split.
    - by rewrite -(Hlookup i ltac:(lia)).
    - by rewrite -(Hlookup (S i) ltac:(lia)).
    - destruct i as [|i]; first exact Hprev.
      simpl in Hprev |- *. rewrite list_lookup_fmap in Hprev.
      rewrite list_lookup_fmap.
      by rewrite -(Hlookup i ltac:(lia)).
  Qed.

  Lemma LL_prefix_stable elems locs locs' alloc :
    take (S (length elems)) locs = take (S (length elems)) locs' →
    LL elems locs alloc ⊣⊢ LL elems locs' alloc.
  Proof.
    intros Htake. iSplit; iApply LL_prefix_stable_dir;
      [exact Htake | by symmetry].
  Qed.

End list_ownership.

Section list_ownership_freeable.
  Context `{!typeGS Σ}.
  Context {E A : Type}.
  Context (node : loc → option loc → option loc → E → iProp Σ).
  Context (freeable : A → loc → iProp Σ).

  Lemma LL_separate_freeable elems locs alloc :
    length elems = length locs →
    LL node freeable elems locs alloc -∗
    LL node (λ (_ : unit) _, True%I) elems locs tt ∗
    ([∗ list] l ∈ locs, freeable alloc l).
  Proof.
    intros Hlen. iIntros "Hall".
    rewrite /LL -(big_sepL2_sepL _ _ elems locs Hlen).
    iApply (big_sepL2_mono (λ i elem _, LL_item node freeable locs alloc i elem) with "[Hall]").
    { intros i elem l Helem Hloc. iIntros "Hitem".
      iDestruct "Hitem" as (node_loc next prev) "(%Hlookup & %Hnext & %Hprev & Hnode & Hfree)".
      have -> : node_loc = l by congruence.
      iFrame "Hfree". iExists l, next, prev. iFrame. done. }
    { rewrite big_sepL2_const_sepL_l. iSplit; first done. iExact "Hall". }
  Qed.
  Lemma LL_restore_freeable elems locs alloc :
    length elems = length locs →
    LL node (λ (_ : unit) _, True%I) elems locs tt ∗
    ([∗ list] l ∈ locs, freeable alloc l) -∗
    LL node freeable elems locs alloc.
  Proof.
    intros Hlen. rewrite /LL -(big_sepL2_sepL _ _ elems locs Hlen).
    iIntros "Hall".
    iAssert (big_sepL2 (λ i elem _, LL_item node freeable locs alloc i elem) elems locs) with "[Hall]" as "Hall".
    { iApply (big_sepL2_mono with "Hall").
    { intros i elem l Helem Hloc. iIntros "[Hitem Hfree]".
      iDestruct "Hitem" as (node_loc next prev) "(%Hlookup & %Hnext & %Hprev & Hnode & _)".
      have -> : node_loc = l by congruence.
      iExists l, next, prev. iFrame. done. } }
    rewrite big_sepL2_const_sepL_l. iDestruct "Hall" as "[_ Hall]". iExact "Hall".
  Qed.
End list_ownership_freeable.

(** The forward traversal stops at the last node of the retained prefix. *)
Lemma last_take_lookup {E : Type} (elems : list E) (i : nat) :
  (0 < i ≤ length elems)%nat →
  last (take i elems) = elems !! Nat.pred i.
Proof.
  intros Hi. rewrite last_lookup length_take Nat.min_l; last lia.
  rewrite lookup_take decide_True; [done | lia].
Qed.

(** Emitted nodes retain a blocked ownership predicate supplied by the client.
    Ghost names are stored in backing-list order, including for reverse traversal.
    The observations come from dropping the returned references without mutation.
    Keeping this predicate generic avoids an import cycle with [Node_inv_t]. *)
Section emitted_ownership.
  Context `{!typeGS Σ}.
  Context {E A : Type}.
  Context (node : loc → option loc → option loc → gname → iProp Σ).
  Context (freeable : A → loc → iProp Σ).
  Context (unchanged : E → gname → iProp Σ).

  Definition LL_emitted (offset : nat) (elems : list E) (ghosts : list gname)
      (locs : list loc) (alloc : A) : iProp Σ :=
    LL_segment node freeable offset ghosts locs alloc ∗
    [∗ list] elem; γ ∈ elems; ghosts, unchanged elem γ.

  Lemma LL_emitted_nil offset locs alloc :
    LL_emitted offset [] [] locs alloc ⊣⊢ emp.
  Proof. by rewrite /LL_emitted LL_segment_nil big_sepL2_nil left_id. Qed.
End emitted_ownership.

Section list_ownership_sharing.
  Context `{!typeGS Σ}.
  Context {E A : Type}.
  Context (node : loc → option loc → option loc → E → iProp Σ).
  Context (freeable : A → loc → iProp Σ).

  Global Instance LL_persistent elems locs alloc
      `{Hnode : ∀ l next prev elem, Persistent (node l next prev elem)}
      `{Hfree : ∀ l, Persistent (freeable alloc l)} :
    Persistent (LL node freeable elems locs alloc) | 1.
  Proof. unfold LL, LL_item. apply _. Qed.

  Global Program Instance LL_as_shared κ elems locs alloc
      `{Hnode : ∀ l next prev elem, AsShared κ (node l next prev elem)}
      `{Hfree : ∀ l, AsShared κ (freeable alloc l)} :
    AsShared κ (LL node freeable elems locs alloc) | 1 := {|
      as_shared_pred κ' :=
        LL (λ l next prev elem, (Hnode l next prev elem).(as_shared_pred) κ')
           (λ _ l, (Hfree l).(as_shared_pred) κ') elems locs alloc;
    |}.
  Next Obligation.
    intros κ elems locs alloc Hnode Hfree.
    rewrite /LL /LL_item.
    iApply big_sepL_mono. iIntros (i elem Hlookup) "Hitem".
    iDestruct "Hitem" as (l next prev) "(%Hloc & %Hnext & %Hprev & Hnode & Hfree)".
    iExists l, next, prev. iFrame "%".
    iSplitL "Hnode"; by iApply as_shared_to_pred.
  Qed.

  Local Definition LL_item_shr π κ κs locs alloc
      (Hnode : ∀ l next prev elem, Shareable π κ κs (node l next prev elem))
      (Hfree : ∀ l, Shareable π κ κs (freeable alloc l)) i elem :
    Shareable π κ κs (LL_item node freeable locs alloc i elem).
  Proof. unfold LL_item. typeclasses eauto. Defined.

  Global Program Instance LL_shareable π κ κs elems locs alloc
      `{Hnode : ∀ l next prev elem, Shareable π κ κs (node l next prev elem)}
      `{Hfree : ∀ l, Shareable π κ κs (freeable alloc l)} :
    Shareable π κ κs (LL node freeable elems locs alloc) | 1 := {|
      shareable_prop :=
        LL (λ l next prev elem, (Hnode l next prev elem).(shareable_prop))
           (λ _ l, (Hfree l).(shareable_prop)) elems locs alloc;
    |}.
  Next Obligation.
    intros π κ κs elems locs alloc Hnode Hfree.
    set (Hitem := LL_item_shr π κ κs locs alloc Hnode Hfree).
    exact (@shareable_proof _ _ π κ κs _ (big_sepL_shareable π κ κs elems
      (LL_item node freeable locs alloc) Hitem)).
  Qed.

  Local Definition LL_item_drop locs alloc
      (Hnode : ∀ l next prev elem, GhostDroppable (node l next prev elem))
      (Hfree : ∀ l, GhostDroppable (freeable alloc l)) i elem :
    GhostDroppable (LL_item node freeable locs alloc i elem).
  Proof. unfold LL_item. typeclasses eauto. Defined.

  Global Program Instance LL_ghost_droppable elems locs alloc
      `{Hnode : ∀ l next prev elem, GhostDroppable (node l next prev elem)}
      `{Hfree : ∀ l, GhostDroppable (freeable alloc l)} :
    GhostDroppable (LL node freeable elems locs alloc) | 1 := {|
      ghost_droppable_prop :=
        LL (λ l next prev elem, (Hnode l next prev elem).(ghost_droppable_prop))
           (λ _ l, (Hfree l).(ghost_droppable_prop)) elems locs alloc;
    |}.
  Next Obligation.
    intros elems locs alloc Hnode Hfree.
    set (Hitem := LL_item_drop locs alloc Hnode Hfree).
    exact (@ghost_droppable_proof _ _ _
      (big_sepL_ghost_droppable elems (LL_item node freeable locs alloc) Hitem)).
  Qed.
End list_ownership_sharing.

Section list_ownership_share_mono.
  Context `{!typeGS Σ}.
  Context {E A : Type}.
  Context (node : lft → loc → option loc → option loc → E → iProp Σ).
  Context (freeable : lft → A → loc → iProp Σ).

  Global Instance LL_share_mono elems locs alloc
      `{Hnode : ∀ l next prev elem, ShareMono (λ κ, node κ l next prev elem)}
      `{Hfree : ∀ l, ShareMono (λ κ, freeable κ alloc l)} :
    ShareMono (λ κ, LL (node κ) (freeable κ) elems locs alloc) | 1.
  Proof. unfold LL, LL_item. typeclasses eauto. Qed.
End list_ownership_share_mono.

Section list_ownership_as_shared_mono.
  Context `{!typeGS Σ}.
  Context {E A : Type}.
  Context (node : loc → option loc → option loc → E → iProp Σ).
  Context (freeable : A → loc → iProp Σ).

  Global Instance LL_as_shared_mono κ elems locs alloc
      `{Hnode : ∀ l next prev elem, AsShared κ (node l next prev elem)}
      `{Hfree : ∀ l, AsShared κ (freeable alloc l)}
      `{Hnode_mono : ∀ l next prev elem,
          ShareMono ((Hnode l next prev elem).(as_shared_pred))}
      `{Hfree_mono : ∀ l, ShareMono ((Hfree l).(as_shared_pred))} :
    ShareMono ((LL_as_shared node freeable κ elems locs alloc).(as_shared_pred)) | 1.
  Proof. apply LL_share_mono; assumption. Qed.
End list_ownership_as_shared_mono.

Section list_ownership_conversion.
  Context `{!typeGS Σ}.
  Context {E A : Type}.
  Context (node node' : loc → option loc → option loc → E → iProp Σ).
  Context (freeable freeable' : A → loc → iProp Σ).

  Lemma LL_mono elems locs alloc :
    (∀ l next prev elem,
      node l next prev elem -∗ node' l next prev elem) →
    (∀ l, freeable alloc l -∗ freeable' alloc l) →
    LL node freeable elems locs alloc -∗ LL node' freeable' elems locs alloc.
  Proof.
    intros Hnode Hfree. rewrite /LL.
    iApply big_sepL_mono. iIntros (i elem Hlookup) "Hitem".
    rewrite /LL_item.
    iDestruct "Hitem" as (l next prev) "(%Hloc & %Hnext & %Hprev & Hown & Hperm)".
    iExists l, next, prev. iFrame "%".
    iSplitL "Hown"; [iApply (Hnode with "Hown") | iApply (Hfree with "Hperm")].
  Qed.
End list_ownership_conversion.

Global Arguments LL : simpl never.
Global Arguments LL_except : simpl never.
Global Typeclasses Opaque LL.
