From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_adapters_map_MapMBMIMFastraits_iterator_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma adapters_map_MapMBMIMFastraits_iterator_Iterator_next_proof (π : thread_id) :
  adapters_map_MapMBMIMFastraits_iterator_Iterator_next_lemma π.
Proof.
  adapters_map_MapMBMIMFastraits_iterator_Iterator_next_prelude.

  rep liRStep. liShow.

  simpl.
  iRename select (li_sealed (□ (∀ _ _ _, traits_iterator_Iterator_Next _ _ _ None _ -∗ _))) into "Hnone".
  iRename select (li_sealed (□ (∀ _ _ _ _,  _))) into "Hsome".
  iRename select (_ (map_it _) (map_clos _)) into "Hinv".
  iRename select (traits_iterator_Iterator_Next _ _ _ _ _) into "Hnext".
  iPoseProof (li_sealed_use_pers with "Hsome") as "#Hsome'".
  iPoseProof (li_sealed_use_pers with "Hnone") as "#Hnone'".
  iPoseProof (boringly_intro with "Hnext") as "#Hnext_x".

  destruct x'0.
  { (* obtain an element *)
    iPoseProof ("Hsome'" with "Hnext Hinv") as "(Hpre & Hinv_clos)".
    iPoseProof (boringly_intro with "Hpre") as "#Hpre_x".
    rep <-! liRStep. liShow.
    iRename select (FnMut_PostMut _ _ _ _ _ _) into "Hpost".
    iPoseProof (boringly_intro with "Hpost") as "#Hpost_x".
    iPoseProof ("Hinv_clos" with "Hpost") as "Hinv".
    rep liRStep.
    liInst Hevar (mut_ref_ghost_drop _ _).
    liInst Hevar2 x4.
    rep liRStep. liShow.
    iApply prove_with_subtype_default.
    liInst Hevar r.
    rep liRStep. }
  { (* no element *)
    iPoseProof ("Hnone'" with "Hnext Hinv") as "Hinv".
    simpl.
    rep <-! liRStep. liShow. 
    rep liRStep.
    liInst Hevar1 x4.
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. 1-10: sidecond_solver.
  2: { 
    (* Point: I have map. I instantiate the generic spec for it for my particular monomorphization.
       Now I have my instance in a generic context.
       I add some trait incl things for that context, but I should also add stuff to the elctx, like the generics here.

       Is this a good time to try to fix some other issues with elctx?
       - For instance, for lifetimes of the surrounding context, we may also have lifetime inclusion constraints. These should also be included and satisfied.
       - What about lifetime constraints on ADTs? Should the ADT invariant be able to use them in some way? 
         Yes, this should add the constraint to the constraints of the ADT type.

       Can I fix all of this in a somewhat consistent way? 
       I guess GenericScope in the frontend should carry the constraints as well, and then we encode them dependent on the use site.
       Both the translation and Radium version of it. 


       For function types, I have add_elctx.
       - typaram_elctx
       - I guess I could add constraints here as well.


       How relevant are constraints outside of functions, anyways?

       Implementation steps:
       1. Add lifetime inclusion stuff to the generic context in Rust.
          Let's consistently do that. Probably similar to how trait assumptions are handled.
       2. Add inclusion assumptions function verification.
          Probably wherever I do fnspec_add_late_pre, I should also add an elctx.
          Pay attention to do that also for function assumptions we have.

       For this, we first need to unify a bit the handling of lifetime constraints for functions.
       - maybe do the direct/surrounding distinction?


       Maybe the point is that I should not put the implicit constraints directly, but have an explicit elctx_wf thing. 
       - lifetimes outlive function
       - type outlives 
       - other external constraints


       If I have 
       impl<'a> Foo for &'a T {
          fn bla() {

          }

       }

       is flft <= 'a an implicit constraint in bla? 
        Yeah, I guess.

       Should I just put all the constraints there? no probably not.
       It would be good for the lifetime constraints declared on the function to be baked into it, otherwise that kinda looks fishy.


       Do I have the same issue with substituting/specializing lifetimes that I have with types (for wf)?
       Not really, there are no interesting constructors for lifetimes I can use.
       Worst case, I require something about static, for instance. Not an issue.
       But maybe that still is a hint that wf should be added late, similar to types.


       What do I do about lifetime constraints from a surrounding context for specialized functions?
       - I guess for this I should add them.

      okay, let's do this.
      - when proving a particular specification, I need to add the elctx.
      - when using a particular (resolvable) implementation, I need to add it to the function.
      - when calling a function with trait assumptions, the spec I'm assuming for the callee needs to require the right trait inclusions.
        


       





    *)



    unshelve sidecond_solver.



        (* TODO: this is a bug in the contract...: For an instantiation, we also need to be able to assume that its elctx is okay. I.e., similar to how we add typaram_wf *)


  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
