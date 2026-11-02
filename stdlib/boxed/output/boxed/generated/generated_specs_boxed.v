From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.alloc.alloc.generated Require Export generated_specs_alloc.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.controlflow.controlflow.generated Require Export generated_specs_controlflow.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.ptr.generated Require Export generated_specs_ptr.
From rrstd.ptr_advanced.ptr_advanced.generated Require Export generated_specs_ptr_advanced.
From rrstd.rr_internal.rr_internal.generated Require Export generated_specs_rr_internal.
From rrstd.sized.sized.generated Require Export generated_specs_sized.
From rrstd.boxed.boxed Require Export generated_code_boxed.

Section box_raw_BoxRaw_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Definition box_raw_BoxRaw_ty  : (spec_with 0 [(T_rt)] ((type (plist place_rfnRT [((((nonnull_NonNull_inv_t_rt)) ((T_rt)))) : RT; (((core_marker_PhantomData_rt) ((T_rt)))) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (struct_t (box_raw_BoxRaw_sls ((ty_syn_type T_ty MetaNone))) +[((nonnull_NonNull_inv_t ((T_rt)) -[] -[T_ty])); ((core_marker_PhantomData_ty ((T_rt)) -[] -[T_ty]))])).
  Defined.

  Definition box_raw_BoxRaw_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (box_raw_BoxRaw_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent box_raw_BoxRaw_rt.
  #[global] Typeclasses Transparent box_raw_BoxRaw_ty.
End box_raw_BoxRaw_ty.
#[global] Arguments box_raw_BoxRaw_rt : clear implicits.

#[global] Arguments box_raw_BoxRaw_ty : clear implicits.

#[global] Arguments box_raw_BoxRaw_ty {_ _} _  .

Section box_raw_BoxRaw_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT}.
  Program Definition box_raw_BoxRaw_inv_t_inv_spec  : (spec_with 0 [(T_rt)] ((ex_inv_def ((box_raw_BoxRaw_rt (T_rt)))%type ((loc))%type))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : (box_raw_BoxRaw_rt (T_rt))) (_ty_rfn : RT_rt ((loc)%type : RT)),
                  let 'l := _ty_rfn in ⌜inner_rfn = -[#(l); #(tt)]⌝ ∗ True)%I
          (true)
          _
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_is_xrfn.
  Qed.

  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Final Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition box_raw_BoxRaw_inv_t  : (spec_with 0 [(T_rt)] ((type (((loc))%type)))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ex_plain_t _ _ (box_raw_BoxRaw_inv_t_inv_spec  -[] -[T_ty]) ((box_raw_BoxRaw_ty (T_rt)) -[] -[T_ty]).
  #[global] Arguments box_raw_BoxRaw_inv_t_inv_spec : simpl never.

  #[global] Arguments box_raw_BoxRaw_inv_t : simpl never.

  #[global] Typeclasses Transparent box_raw_BoxRaw_inv_t.
  Definition box_raw_BoxRaw_inv_t_rt  : RT.
  Proof using T_rt .
    let __a := (normalized_rt_of_spec_ty (box_raw_BoxRaw_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent box_raw_BoxRaw_inv_t_rt.
End box_raw_BoxRaw_inv_t.
#[global] Arguments box_raw_BoxRaw_inv_t_rt : clear implicits.

#[global] Arguments box_raw_BoxRaw_inv_t : clear implicits.

#[global] Arguments box_raw_BoxRaw_inv_t {_ _} _  .

#[global] Arguments box_raw_BoxRaw_inv_t_inv_spec : clear implicits.

#[global] Arguments box_raw_BoxRaw_inv_t_inv_spec {_ _} _  .


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition box_raw_BoxRawTasstd_clone_Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Clone_spec_attrs (((box_raw_BoxRaw_inv_t_rt ((T_rt))))))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((convert_From_spec_attrs (((((nonnull_NonNull_inv_t_rt)) ((T_rt))))) (((box_raw_BoxRaw_inv_t_rt ((T_rt))))))) :=
  {|
    convert_From_FromFn  :=
      (id) : ((convert_From_FromFn_sig (((((nonnull_NonNull_inv_t_rt)) ((T_rt))))) (((box_raw_BoxRaw_inv_t_rt ((T_rt)))))));
  |}
.


End attrs.

Section Box_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT} {A_rt : RT}.
  Definition Box_ty (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(T_rt); (A_rt)] ((type (plist place_rfnRT [((box_raw_BoxRaw_inv_t_rt ((T_rt)))) : RT; (A_rt) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (struct_t (Box_sls ((ty_syn_type T_ty MetaNone)) ((ty_syn_type A_ty MetaNone))) +[((box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty])); (A_ty)])).
  Defined.

  Definition Box_rt  : RT.
  Proof using T_rt A_rt .
    let __a := (normalized_rt_of_spec_ty (Box_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent Box_rt.
  #[global] Typeclasses Transparent Box_ty.
End Box_ty.
#[global] Arguments Box_rt : clear implicits.

#[global] Arguments Box_ty : clear implicits.

#[global] Arguments Box_ty {_ _} _ _  .

Section Box_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Context {T_rt : RT} {A_rt : RT}.
  Program Definition Box_inv_t_inv_spec (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(T_rt); (A_rt)] ((ex_inv_def ((Box_rt (T_rt) (A_rt)))%type (((place_rfn (T_rt)) * (directRT (RT_xt (A_rt)))))%type))) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), mk_ex_inv_def_auto_shr
          (λ π (inner_rfn : (Box_rt (T_rt) (A_rt))) (_ty_rfn : RT_rt (((place_rfn (T_rt)) * (directRT (RT_xt (A_rt))))%type : RT)),
                  let '(x, a) := _ty_rfn in ∃ (l: name_hint_ty "l" ((loc))%Z), ⌜inner_rfn = -[#(l); #($# a)]⌝ ∗ guarded true (l ◁ₗ[π, Owned] x @ ◁ T_ty) ∗ Allocator_A_spec_attrs.(Allocator_FreeablePerm) a l (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))) ∗ True)%I
          (λ π _ (_rfn_binder : RT_rt (((place_rfn (T_rt)) * (directRT (RT_xt (A_rt))))%type : RT)),
                  let '(x, a) := _rfn_binder in (∃ r, place_rfn_interp_owned x r ∗ ty_ghost_drop T_ty π r) ∗ True)%I
          (false)
          _
          ([] ++ ty_lfts T_ty)
          ([] ++ ty_wf_E T_ty)
          _ _ _ _
        .
  Next Obligation.
    intros ?; ex_plain_t_solve_is_xrfn.
  Qed.

  Next Obligation.
    intros ?; ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    intros ?; ex_t_solve_persistent.
  Qed.

  Next Obligation.
    intros ?; ex_plain_t_solve_shr_mono.
  Qed.

  Final Obligation.
    intros ?; ex_plain_t_solve_ghost_drop.
  Qed.

  Definition Box_inv_t (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with 0 [(T_rt); (A_rt)] ((type ((((place_rfn (T_rt)) * (directRT (RT_xt (A_rt)))))%type)))) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), ex_plain_t _ _ (Box_inv_t_inv_spec Allocator_A_spec_attrs -[] -[T_ty; A_ty]) (((Box_ty (T_rt) (A_rt)) (Allocator_A_spec_attrs)) -[] -[T_ty; A_ty]).
  #[global] Arguments Box_inv_t_inv_spec : simpl never.

  #[global] Arguments Box_inv_t : simpl never.

  #[global] Typeclasses Transparent Box_inv_t.
  Definition Box_inv_t_rt  : RT.
  Proof using T_rt A_rt .
    let __a := (normalized_rt_of_spec_ty (Box_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent Box_inv_t_rt.
End Box_inv_t.
#[global] Arguments Box_inv_t_rt : clear implicits.

#[global] Arguments Box_inv_t : clear implicits.

#[global] Arguments Box_inv_t {_ _} _ _  .

#[global] Arguments Box_inv_t_inv_spec : clear implicits.

#[global] Arguments Box_inv_t_inv_spec {_ _} _ _  .


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition BoxTAasstd_ops_Drop_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (A_rt: RT) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : ((Drop_spec_attrs (((Box_inv_t_rt ((T_rt)) ((A_rt))))))) :=
  mk_Drop_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition box_raw_BoxRawTasstd_marker_Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : ((Copy_spec_attrs (((box_raw_BoxRaw_inv_t_rt ((T_rt))))) ((box_raw_BoxRawTasstd_clone_Clone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs))))) :=
  mk_Copy_spec_attrs.


End attrs.

Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition drop_glue_Box_spec_attrs `{RRGS : !(refinedrustGS Σ)} (T_rt: RT) (A_rt: RT) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : ((DropGlue_spec_attrs (((Box_inv_t_rt ((T_rt)) ((A_rt))))))) :=
  {|
    DropGlue_DropGlueUnwind  :=
      (DropGlue_T_spec_attrs.(DropGlue_DropGlueUnwind) ∨ DropGlue_A_spec_attrs.(DropGlue_DropGlueUnwind)) : ((DropGlue_DropGlueUnwind_sig (((Box_inv_t_rt ((T_rt)) ((A_rt)))))));
  |}
.


End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
Section contractive.
  Context `{!refinedrustGS Σ}.

  Global Instance BoxRaw_inv_t_contr {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, box_raw_BoxRaw_inv_t T_rt <TY> (T ty) <INST!>).
  Proof.
    intros X.
    apply ex_plain_t_contr.
    - constructor.
      + solve_proper.
      + solve_proper.
    - cbn; apply _.
  Qed.
  Global Instance BoxRaw_inv_t_ne {rt1 T_rt : RT} (T : type rt1 → type T_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, box_raw_BoxRaw_inv_t T_rt <TY> (T ty) <INST!>).
  Proof. apply _. Qed.

  Global Program Instance BoxRaw_inv_t_dep_lft_mor rts (rt : RT) (T : mut_types rts → type rt) deps :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x : mut_types rts, box_raw_BoxRaw_inv_t rt *[] *[(T x)]) :=
    λ Ht,
      dep_lft_morph_make_id _ _ _ Ht _ _.
  Next Obligation.
    intros. rewrite /lifecycle_lfts/=.
    repeat rewrite !ty_lfts_unfold/=.
    rewrite !right_id//.
  Qed.
  Next Obligation.
    intros. rewrite /lifecycle_wf_E/=.
    repeat rewrite !ty_wf_E_unfold/=.
    rewrite !right_id//.
  Qed.

  Global Instance Box_inv_t_contr {rt1 T_rt A_rt : RT} (T : type rt1 → type T_rt) (A_ty : type A_rt) (A_attrs : Allocator_spec_attrs A_rt) :
    TypeNonExpansive T →
    TypeContractive (λ ty, Box_inv_t T_rt A_rt A_attrs <TY> (T ty) <TY> A_ty <INST!>).
  Proof.
    intros X.
    apply ex_plain_t_contr.
    - constructor.
      + solve_proper_prepare.
        repeat solve_proper_step.
      + solve_proper_prepare. simpl in *. prepare_initial_coq_context. simpl.
        repeat solve_proper_step.
    - cbn; apply _.
  Qed.
  Global Instance Box_inv_t_ne {rt1 T_rt A_rt : RT} (T : type rt1 → type T_rt) (A_ty : type A_rt) (A_attrs : Allocator_spec_attrs A_rt) :
    TypeNonExpansive T →
    TypeNonExpansive (λ ty, Box_inv_t T_rt A_rt A_attrs <TY> (T ty) <TY> A_ty <INST!>).
  Proof. apply _. Qed.

  Instance Box_inv_t_dep_lft_mor rts (T_rt A_rt : RT) (A_attrs : Allocator_spec_attrs A_rt) (A_ty : type A_rt) (T : mut_types rts → type T_rt) deps :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x : mut_types rts, Box_inv_t_inv_spec T_rt A_rt A_attrs *[] *[(T x); A_ty]).
  Proof.
    simpl.
    intros Hdep.
    eapply (dep_lft_morph_make_id _ T); first done.
    - done.
    - done.
  Defined.
  Global Instance Box_inv_t_dep_lft_mor' rts (T_rt A_rt : RT) (A_attrs : Allocator_spec_attrs A_rt) (A_ty : type A_rt) (T : mut_types rts → type T_rt) deps :
    DepLftMorphism deps T →
    DepLftMorphism deps (λ x : mut_types rts, Box_inv_t T_rt A_rt A_attrs *[] *[(T x); A_ty]).
  Proof.
    intros Ha.
    eapply mk_ex_plain_t_dep_lft_morphism; [apply _.. | ].
    abstract (set_solver).
  Defined.

  (** Resolve ghost: Resolve observations on the contained value. *)
  Lemma resolve_ghost_box {T_rt A_rt} A_attrs (T_ty : type T_rt) (A_ty : type A_rt) π E L r rm T :
    (resolve_ghost π E L rm true (◁ T_ty) Owned r.1 (λ L2 r2 R prog,
      T L2 (r2, r.2) R prog))
    ⊢ resolve_ghost_adt π E L rm r (Box_inv_t T_rt A_rt A_attrs <TY> T_ty <TY> A_ty <INST!>) T.
  Proof.
    rewrite /resolve_ghost_adt /resolve_ghost.
    iIntros "HT" (????) "#CTX #HE HL Hv".
    rewrite ex_plain_t_unfold_val.
    destruct r as [r a].
    iDestruct "Hv" as ((l' & [])) "(Hinv & Hv)". simpl in *.
    iDestruct "Hinv" as "(%l'' & %Heq & Hl' & Halloc & _)".
    inversion Heq. subst.
    unfold guarded. iDestruct "Hl'" as "(Hc & Hl')".
    iDestruct "Hc" as "((Hc1 & Hc) & Ht)".
    iApply (lc_fupd_add_later with "Hc1"). iNext.
    iMod ("HT" with "[] [] CTX HE HL Hl'") as "(%L2 & %r' & %R & %progress & Hstep & HL & HT)"; [done.. | ].
    iFrame.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_tr with "Ht").
    iModIntro. iIntros "Ht Hcreds' !> (Hl' & $)".
    rewrite ex_plain_t_unfold_val.
    iFrame. iR.
    rewrite /guarded. iFrame.
    iDestruct "Ht" as "(_ & $)".
  Qed.

  (* Box is covariant in T and A *)
  Lemma subtype_box {T_rt A_rt} A_attrs (T_ty_1 T_ty_2 : type T_rt) (A_ty_1 A_ty_2 : type A_rt) E L T :
    mut_subtype E L T_ty_1 T_ty_2 (mut_subtype E L A_ty_1 A_ty_2 T)
    ⊢ subtype_adt E L (Box_inv_t_inv_spec T_rt A_rt A_attrs <TY> T_ty_1 <TY> A_ty_1 <INST!>) (Box_inv_t_inv_spec T_rt A_rt A_attrs <TY> T_ty_2 <TY> A_ty_2 <INST!>) T.
  Proof.
    rewrite /mut_subtype /subtype_adt.
    iIntros "(%HsubT & %HsubA & $)". iPureIntro.
    iIntros (?) "HL HE".
    iPoseProof (full_subtype_acc_noend with "HE HL") as "(%HstT & #HinclT)"; first apply HsubT.
    iPoseProof (full_subtype_acc_noend with "HE HL") as "(%HstA & #HinclA)"; first apply HsubA.
    iSplit; iModIntro.
    - iIntros (? x [r a]). simpl.
      iIntros "(%l & -> & Hl & Hperm)".
      iExists _. iR.
      rewrite HstT. iFrame.
      iApply (guarded_mono with "[] Hl").
      iIntros "Hl". iApply type_incl_ltype_owned_wand; [ | done..].
      rewrite HstT//.
    - iIntros (? ? x [r a]). simpl.
      iIntros "(%l &  -> & Hl & Hperm)".
      iExists _. iR. iL.
      iApply (guarded_mono with "[] Hl").
      iIntros "Hl". iApply type_incl_ltype_shared_wand; [ | done..].
      rewrite HstT//.
  Qed.
  Definition subtype_box_inst := [instance @subtype_box].
  Global Existing Instance subtype_box_inst.
End contractive.
Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_box_raw_BoxRawTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_box_raw_BoxRawTasstd_clone_Clone_clone (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_elctx (λ ϝ, typarams_elctx ϝ _ -[T_ty]) (scope_add_elctx (λ ϝ, []) (((Clone_base_spec (((box_raw_BoxRaw_inv_t_rt ((T_rt))))) ((box_raw_BoxRaw_st (T_st))) ((drop_glue_trivial_spec_attrs (((box_raw_BoxRaw_inv_t_rt ((T_rt))))))) ((box_raw_BoxRawTasstd_clone_Clone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty])]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_box_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_box_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) x :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x, tt) @ (Box_inv_t ((T_rt)) ((((Global_inv_t_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_inv_t  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_from (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_from (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT),(λ a b, scope_add_elctx (λ ϝ, typarams_elctx ϝ _ -[T_ty]) (scope_add_elctx (λ ϝ, []) (((convert_From_base_spec (((((nonnull_NonNull_inv_t_rt)) ((T_rt))))) (((box_raw_BoxRaw_inv_t_rt ((T_rt))))) (((nonnull_NonNull_sls (T_st)) : syn_type)) ((box_raw_BoxRaw_st (T_st))) ((drop_glue_trivial_spec_attrs (((((nonnull_NonNull_inv_t_rt)) ((T_rt))))))) ((drop_glue_trivial_spec_attrs (((box_raw_BoxRaw_inv_t_rt ((T_rt))))))) ((box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec_attrs (T_rt) (DropGlue_T_spec_attrs))))
    -[] -[(nonnull_NonNull_inv_t ((T_rt)) -[] -[T_ty]); (box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty])]).(convert_From_from_spec)   a b))) <MERGE!>.

Definition trait_incl_of_Box_T_from_raw (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Box_T_from_raw (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b, raw) : ((_ * _)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) raw :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (raw ◁ₗ[π, Owned] #(($#@{ (T_rt) } b)) @ (◁ T_ty))
        ∗ (freeable_nz raw (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))) 1 HeapAlloc)
        ∗ (⌜(raw.(loc_a) ≠ 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (b, tt) @ (Box_inv_t ((T_rt)) ((((Global_inv_t_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_inv_t  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Box_TA_from_raw_in (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π))%I).

Definition type_of_Box_TA_from_raw_in (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b, raw, alloc) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty; A_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) raw :@: alias_ptr_t, alloc :@: A_ty;
      (* precondition. *) (λ π : thread_id, (raw ◁ₗ[π, Owned] #(($#@{ (T_rt) } b)) @ (◁ T_ty))
        ∗ (Allocator_A_spec_attrs.(Allocator_FreeablePerm) alloc raw (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))))
        ∗ (⌜(raw.(loc_a) ≠ 0)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (b, alloc) @ (Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Box_T_into_non_null (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Box_T_into_non_null (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) b :@: (Box_inv_t ((T_rt)) ((((Global_inv_t_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_inv_t  -[] -[])]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : (((loc))), l @ (nonnull_NonNull_inv_t ((T_rt)) -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(($#@{ (T_rt) } b.1)) @ (◁ T_ty))
      ∗ (freeable_nz l (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))) 1 HeapAlloc)
      ∗ (⌜(l.(loc_a) ≠ 0)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Box_TA_into_non_null_with_allocator (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π))%I).

Definition type_of_Box_TA_into_non_null_with_allocator (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty; A_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) b :@: (Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : (((loc))), *[l; b.2] @ (tuple2_ty (((((nonnull_NonNull_inv_t_rt)) ((T_rt))))) ((A_rt)) -[] -[(nonnull_NonNull_inv_t ((T_rt)) -[] -[T_ty]); A_ty]);
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(($#@{ (T_rt) } b.1)) @ (◁ T_ty))
      ∗ (Allocator_A_spec_attrs.(Allocator_FreeablePerm) b.2 l (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))))
      ∗ (⌜(l.(loc_a) ≠ 0)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Box_T_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Box_T_new (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) x :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x, tt) @ (Box_inv_t ((T_rt)) ((((Global_inv_t_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_inv_t  -[] -[])]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_box_raw_BoxRaw_T_as_non_null_ptr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_box_raw_BoxRaw_T_as_non_null_ptr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) self :@: (box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ (nonnull_NonNull_inv_t ((T_rt)) -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_box_raw_BoxRaw_T_as_ptr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_box_raw_BoxRaw_T_as_ptr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) self :@: (box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_box_raw_BoxRaw_T_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) (DropGlue_U_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_U_lfts_inst : prod_vec lft DropGlue_U_realization.(trait_ctx_lfts)) (DropGlue_U_tys_inst : plist type DropGlue_U_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_U_realization.(trait_ctx_spec) DropGlue_U_lfts_inst DropGlue_U_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (U_rt) U_st DropGlue_U_spec_attrs-[] -[U_ty]))⌝ ∗ DropGlue_U_realization.(trait_ctx_wf) DropGlue_U_lfts_inst DropGlue_U_tys_inst π))%I).

Definition type_of_box_raw_BoxRaw_T_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; U_ty]) : ([(T_rt, T_st); (U_rt, U_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty; U_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) self :@: (box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, self @ (box_raw_BoxRaw_inv_t ((U_rt))  -[] -[U_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_box_raw_BoxRaw_T_dangling (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_box_raw_BoxRaw_T_dangling (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ (box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
      ∗ (l ◁ₗ[π, Owned] #(()) @ (◁ uninit UnitSynType))
      ∗ (freeable_nz l 0 1 HeapAlloc)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_box_raw_BoxRaw_T_new_unchecked (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_box_raw_BoxRaw_T_new_unchecked (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (ptr) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) ptr :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hptr_nonnull" (ptr.(loc_a) ≠ 0)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ptr @ (box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_drop_glue_Box (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (λ π, ((∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I).

Definition type_of_drop_glue_Box (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT),(λ a b, scope_add_elctx (λ ϝ, typarams_elctx ϝ _ -[T_ty; A_ty]) (scope_add_elctx (λ ϝ, []) (((DropGlue_base_spec (((Box_inv_t_rt ((T_rt)) ((A_rt))))) ((Box_st (T_st) (A_st))) ((drop_glue_Box_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs) (DropGlue_T_spec_attrs) (DropGlue_A_spec_attrs))))
    -[] -[(Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])]).(DropGlue_drop_glue_spec)   a b))) <MERGE!>.


Definition trait_incl_of_BoxTAasstd_ops_Drop_drop (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (λ π, ((∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π)
    ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I).

Definition type_of_BoxTAasstd_ops_Drop_drop (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, lmem, a) : ((_ * _ * _)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty; A_ty]) ϝ ++ (λ ϝ, [(ϝ, ulft_1)]) ϝ);
      (* args......... *) l :@: alias_ref_t;
      (* precondition. *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(-[#lmem; #($# a)]) @ (◁ Box_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]))
        ∗ (lmem ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))
        ∗ (Allocator_A_spec_attrs.(Allocator_FreeablePerm) a lmem (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(-[#lmem; #($# a)]) @ (◁ Box_ty T_rt A_rt Allocator_A_spec_attrs -[] -[T_ty; A_ty]))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Box_T_into_raw (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I).

Definition type_of_Box_T_into_raw (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) b :@: (Box_inv_t ((T_rt)) ((((Global_inv_t_rt)))) GlobalasAllocator_spec_attrs -[] -[T_ty; (Global_inv_t  -[] -[])]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : (((loc))), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(($#@{ (T_rt) } (b.1))) @ (◁ T_ty))
      ∗ (freeable_nz l (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))) 1 HeapAlloc)
      ∗ (⌜(l.(loc_a) ≠ 0)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Box_TA_into_raw_with_allocator (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π))%I).

Definition type_of_Box_TA_into_raw_with_allocator (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (b) : ((_)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty; A_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) b :@: (Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : (((loc))), *[l; b.2] @ (tuple2_ty (loc) ((A_rt)) -[] -[alias_ptr_t; A_ty]);
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(($#@{ (T_rt) } b.1)) @ (◁ T_ty))
      ∗ (Allocator_A_spec_attrs.(Allocator_FreeablePerm) b.2 l (ly_size (use_layout_alg' (ty_syn_type T_ty MetaNone))))
      ∗ (⌜(l.(loc_a) ≠ 0)%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_Box_TA_new_in (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (λ π, ((∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
    ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π)
    ∗ (∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π))%I).

Definition type_of_Box_TA_new_in (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; A_ty]) : ([(T_rt, T_st); (A_rt, A_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x, alloc) : ((_ * _)),
      (* elctx........ *) (λ ϝ, (λ ϝ, typarams_elctx ϝ _ -[T_ty; A_ty]) ϝ ++ (λ ϝ, []) ϝ);
      (* args......... *) x :@: T_ty, alloc :@: A_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x, alloc) @ (Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).



End specs.
Section BoxTAasstd_ops_Drop_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition BoxTAasstd_ops_Drop_spec (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (Drop_spec (((Box_inv_t_rt ((T_rt)) ((A_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), {|
        Drop_drop_spec  :=
          (type_of_BoxTAasstd_ops_Drop_drop ((T_rt)) ((A_rt)) (T_st) (A_st)) Allocator_A_spec_attrs DropGlue_T_spec_attrs DropGlue_A_spec_attrs 
             <TY> T_ty <TY> A_ty : (spec_with 1 [] fn_spec);
      |}
  .
  Arguments BoxTAasstd_ops_Drop_spec : simpl never.

  Program Definition BoxTAasstd_ops_Drop_realization (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) : trait_spec_realization (spec_with 0 [] (Drop_spec (RRGS:=RRGS) ((Box_inv_t_rt ((T_rt)) ((A_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt; A_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty; A_ty]) π, (((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf A_rt A_st A_ty))
  ∗ (∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π)
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty; A_ty]) _ _, (BoxTAasstd_ops_Drop_spec (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs) (DropGlue_T_spec_attrs) (DropGlue_A_spec_attrs))-[] -[T_ty; A_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition BoxTAasstd_ops_Drop_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl Drop_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (BoxTAasstd_ops_Drop_spec (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs) (DropGlue_T_spec_attrs) (DropGlue_A_spec_attrs))-[] -[T_ty; A_ty]) (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), scope_add_elctx (λ ϝ, typarams_elctx ϝ _ -[T_ty; A_ty]) ((Drop_base_spec ((Box_inv_t_rt ((T_rt)) ((A_rt)))) (Box_st (T_st) (A_st)) (drop_glue_Box_spec_attrs ((T_rt)) ((A_rt)) (Allocator_A_spec_attrs) (DropGlue_T_spec_attrs) (DropGlue_A_spec_attrs)) (BoxTAasstd_ops_Drop_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs) (DropGlue_T_spec_attrs) (DropGlue_A_spec_attrs))-[] -[(Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])])))).
End BoxTAasstd_ops_Drop_spec.

Section box_raw_BoxRawTasstd_clone_Clone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition box_raw_BoxRawTasstd_clone_Clone_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Clone_spec (((box_raw_BoxRaw_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        Clone_clone_spec  :=
          (type_of_box_raw_BoxRawTasstd_clone_Clone_clone ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec (((box_raw_BoxRaw_inv_t_rt ((T_rt))))) ((box_raw_BoxRaw_st (T_st)))) (drop_glue_trivial_spec_attrs (((box_raw_BoxRaw_inv_t_rt ((T_rt)))))) (box_raw_BoxRawTasstd_clone_Clone_spec_attrs (T_rt) (DropGlue_T_spec_attrs)) 
             <TY> (box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty]) : (spec_with 2 [] fn_spec);
      |}
  .
  Arguments box_raw_BoxRawTasstd_clone_Clone_spec : simpl never.

  Program Definition box_raw_BoxRawTasstd_clone_Clone_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Clone_spec (RRGS:=RRGS) ((box_raw_BoxRaw_inv_t_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (box_raw_BoxRawTasstd_clone_Clone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition box_raw_BoxRawTasstd_clone_Clone_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (box_raw_BoxRawTasstd_clone_Clone_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_elctx (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ((Clone_base_spec ((box_raw_BoxRaw_inv_t_rt ((T_rt)))) (box_raw_BoxRaw_st (T_st)) (drop_glue_trivial_spec_attrs (((box_raw_BoxRaw_inv_t_rt ((T_rt)))))) (box_raw_BoxRawTasstd_clone_Clone_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty])])))).
End box_raw_BoxRawTasstd_clone_Clone_spec.

Section box_raw_BoxRawTasstd_marker_Copy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition box_raw_BoxRawTasstd_marker_Copy_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (Copy_spec (((box_raw_BoxRaw_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (@mk_Copy_spec _ _ (((box_raw_BoxRaw_inv_t_rt ((T_rt)))))).
  Arguments box_raw_BoxRawTasstd_marker_Copy_spec : simpl never.

  Program Definition box_raw_BoxRawTasstd_marker_Copy_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (Copy_spec (RRGS:=RRGS) ((box_raw_BoxRaw_inv_t_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (box_raw_BoxRawTasstd_marker_Copy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition box_raw_BoxRawTasstd_marker_Copy_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (box_raw_BoxRawTasstd_marker_Copy_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_elctx (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ((Copy_base_spec ((box_raw_BoxRaw_inv_t_rt ((T_rt)))) (box_raw_BoxRaw_st (T_st)) (box_raw_BoxRawTasstd_clone_Clone_spec_attrs ((T_rt)) (DropGlue_T_spec_attrs)) (drop_glue_trivial_spec_attrs (((box_raw_BoxRaw_inv_t_rt ((T_rt)))))) (box_raw_BoxRawTasstd_marker_Copy_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty])])))).
  Lemma box_raw_BoxRawTasstd_marker_Copy_semantic_interp (T_rt: RT) (T_ty: (type (T_rt))) : (Copy_semantic_interp ((box_raw_BoxRaw_inv_t_rt ((T_rt)))) (box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty])).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End box_raw_BoxRawTasstd_marker_Copy_spec.

Section box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) : (spec_with _ _ (convert_From_spec (((((nonnull_NonNull_inv_t_rt)) ((T_rt))))) (((box_raw_BoxRaw_inv_t_rt ((T_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), {|
        convert_From_from_spec  :=
          (type_of_box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_from ((T_rt)) (T_st)) DropGlue_T_spec_attrs 
             <TY> T_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec : simpl never.

  Program Definition box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_realization (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) : trait_spec_realization (spec_with 0 [] (convert_From_spec (RRGS:=RRGS) ((((nonnull_NonNull_inv_t_rt)) ((T_rt)))) ((box_raw_BoxRaw_inv_t_rt ((T_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty]) π, (((typaram_wf T_rt T_st T_ty))
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty]) _ _, (box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(T_st : !syn_type) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )), trait_incl_marker (lift_trait_incl convert_From_spec_incl (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), (box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec (T_rt) (T_st) (DropGlue_T_spec_attrs))-[] -[T_ty]) (spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), scope_add_elctx (λ ϝ, typarams_elctx ϝ _ -[T_ty]) ((convert_From_base_spec ((((nonnull_NonNull_inv_t_rt)) ((T_rt)))) ((box_raw_BoxRaw_inv_t_rt ((T_rt)))) ((nonnull_NonNull_sls (T_st)) : syn_type) (box_raw_BoxRaw_st (T_st)) (drop_glue_trivial_spec_attrs (((((nonnull_NonNull_inv_t_rt)) ((T_rt)))))) (drop_glue_trivial_spec_attrs (((box_raw_BoxRaw_inv_t_rt ((T_rt)))))) (box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec_attrs (T_rt) (DropGlue_T_spec_attrs))-[] -[(nonnull_NonNull_inv_t ((T_rt)) -[] -[T_ty]); (box_raw_BoxRaw_inv_t ((T_rt))  -[] -[T_ty])])))).
End box_raw_implstd_convert_Frombox_raw_BoxRawTforstd_ptr_NonNullT_spec.

Section drop_glue_Box_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition drop_glue_Box_spec (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) : (spec_with _ _ (DropGlue_spec (((Box_inv_t_rt ((T_rt)) ((A_rt))))))) :=
    spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), {|
        DropGlue_drop_glue_spec  :=
          (type_of_drop_glue_Box ((T_rt)) ((A_rt)) (T_st) (A_st)) Allocator_A_spec_attrs DropGlue_T_spec_attrs DropGlue_A_spec_attrs 
             <TY> T_ty <TY> A_ty : (spec_with 0 [] fn_spec);
      |}
  .
  Arguments drop_glue_Box_spec : simpl never.

  Program Definition drop_glue_Box_realization (T_rt: RT) (A_rt: RT) (T_st: syn_type) (A_st: syn_type) (Allocator_A_spec_attrs: (Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) (Allocator_A_realization: (trait_spec_realization (spec_with 0 [] (Allocator_spec (RRGS:=RRGS) (A_rt))))) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt))))) (DropGlue_A_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )) (DropGlue_A_realization: (trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (A_rt))))) : trait_spec_realization (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) ((Box_inv_t_rt ((T_rt)) ((A_rt)))))) :=
  {|
    trait_ctx_lfts := 0;
    trait_ctx_tys := [T_rt; A_rt];
    trait_ctx_wf := λ '( *[]) '( *[T_ty; A_ty]) π, (((typaram_wf T_rt T_st T_ty)
  ∗ (typaram_wf A_rt A_st A_ty))
  ∗ (∃ (Allocator_A_lfts_inst : prod_vec lft Allocator_A_realization.(trait_ctx_lfts)) (Allocator_A_tys_inst : plist type Allocator_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl Allocator_spec_incl (Allocator_A_realization.(trait_ctx_spec) Allocator_A_lfts_inst Allocator_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), Allocator_base_spec (A_rt) A_st DropGlue_A_spec_attrs Allocator_A_spec_attrs-[] -[A_ty]))⌝ ∗ Allocator_A_realization.(trait_ctx_wf) Allocator_A_lfts_inst Allocator_A_tys_inst π)
  ∗ (∃ (DropGlue_T_lfts_inst : prod_vec lft DropGlue_T_realization.(trait_ctx_lfts)) (DropGlue_T_tys_inst : plist type DropGlue_T_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_T_realization.(trait_ctx_spec) DropGlue_T_lfts_inst DropGlue_T_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))⌝ ∗ DropGlue_T_realization.(trait_ctx_wf) DropGlue_T_lfts_inst DropGlue_T_tys_inst π)
  ∗ (∃ (DropGlue_A_lfts_inst : prod_vec lft DropGlue_A_realization.(trait_ctx_lfts)) (DropGlue_A_tys_inst : plist type DropGlue_A_realization.(trait_ctx_tys)), ⌜trait_incl_marker (lift_trait_incl DropGlue_spec_incl (DropGlue_A_realization.(trait_ctx_spec) DropGlue_A_lfts_inst DropGlue_A_tys_inst) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (A_rt) A_st DropGlue_A_spec_attrs-[] -[A_ty]))⌝ ∗ DropGlue_A_realization.(trait_ctx_wf) DropGlue_A_lfts_inst DropGlue_A_tys_inst π))%I;
    trait_ctx_spec := λ '( *[]) '( *[T_ty; A_ty]) _ _, (drop_glue_Box_spec (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs) (DropGlue_T_spec_attrs) (DropGlue_A_spec_attrs))-[] -[T_ty; A_ty];
  |}.
  Next Obligation.
    solve_trait_realization_pers.
  Qed.
  Definition drop_glue_Box_spec_subsumption  :=
    ∀ `(T_rt : !RT) `(A_rt : !RT) `(T_st : !syn_type) `(A_st : !syn_type) `(Allocator_A_spec_attrs : !(Allocator_spec_attrs (RRGS:=RRGS) (A_rt) )) `(DropGlue_T_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) `(DropGlue_A_spec_attrs : !(DropGlue_spec_attrs (RRGS:=RRGS) (A_rt) )), trait_incl_marker (lift_trait_incl DropGlue_spec_incl (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), (drop_glue_Box_spec (T_rt) (A_rt) (T_st) (A_st) (Allocator_A_spec_attrs) (DropGlue_T_spec_attrs) (DropGlue_A_spec_attrs))-[] -[T_ty; A_ty]) (spec! ( *[]) : 0 | ( *[T_ty; A_ty]) : ([T_rt; A_rt] : list RT), scope_add_elctx (λ ϝ, typarams_elctx ϝ _ -[T_ty; A_ty]) ((DropGlue_base_spec ((Box_inv_t_rt ((T_rt)) ((A_rt)))) (Box_st (T_st) (A_st)) (drop_glue_Box_spec_attrs (T_rt) (A_rt) (Allocator_A_spec_attrs) (DropGlue_T_spec_attrs) (DropGlue_A_spec_attrs))-[] -[(Box_inv_t ((T_rt)) ((A_rt)) Allocator_A_spec_attrs -[] -[T_ty; A_ty])])))).
End drop_glue_Box_spec.

