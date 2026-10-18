From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.linkedlist.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_LinkedList_TA_split_off.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma LinkedList_TA_split_off_proof (π : thread_id) :
  LinkedList_TA_split_off_lemma π.
Proof.
  LinkedList_TA_split_off_prelude.

  1: rep <-! <3000 liRStep; liShow.
  { rep liRStep; liShow.
    liInst Hevar_self (<#> <$#@{T_rt}> elems).
    liInst Hevar_a alloc.
    rewrite list_fmap_compose.
    rep <-! <3000 liRStep; liShow.
    rep liRStep; liShow.
    rewrite list_fmap_id list_fmap_compose.
    rep liRStep; liShow.
    liInst Hevar_self elems.
    liInst Hevar_locs locs.
    liInst Hevar_a alloc.
    liInst Hevar_self0 (@nil (RT_xt T_rt)).
    liInst Hevar_locs0 (@nil loc).
    liInst Hevar_a0 alloc.
    rep <-! <3000 liRStep; liShow.
  }
  { rep <-! <3000 liRStep; liShow.
    { rep liRStep; liShow.
      liInst Hevar_self (<#> <$#@{T_rt}> elems).
      liInst Hevar_a alloc.
      rewrite list_fmap_compose.
      rep <-! <3000 liRStep; liShow.
      rewrite list_fmap_id list_fmap_compose.
      rep <-! <3000 liRStep; liShow.
    }
    { rep <-! <3000 liRStep.
      3: { (* impossible subtraction overflow *)
        exfalso. solve [sidecond_solver].
      }
      3: { (* impossible subtraction overflow *)
        exfalso. solve [sidecond_solver].
      }
      3: { (* impossible subtraction overflow *)
        exfalso. solve [sidecond_solver].
      }
      3: { (* impossible subtraction overflow *)
        exfalso. solve [sidecond_solver].
      }
      2: { (* backward traversal *)
        rep <-! <3000 liRStep.
        liShow.
        iApply updateable_add_fupd.
        iRename select (_ ◁ₗ[π, Owned] _ @ ◁ LinkedList_inv_t _ _ _ _ _)%I into "Hlist".
        iEval (rewrite /LinkedList_inv_t) in "Hlist".
        iMod (ex_plain_t_destruct_owned with "Hlist") as (r) "[Hinv Hlist]"; first solve_ndisj.
        iDestruct "Hinv" as "(%Hheader & %Hlen & %Hnonnull & %Hbound & Hall)".
        iDestruct "Hall" as "[Hall _]".
        subst r.
        simpl in Hlen, Hnonnull.
        rewrite length_fmap in Hlen, Hbound.
        iModIntro.
        rep liRStep; liShow.
        liInst Hevar_x0 elems.
        liInst Hevar_x2 locs.
        liInst Hevar_x3 alloc.
        rewrite list_fmap_compose.
        rep <-! <3000 liRStep; liShow.
        rep liRStep; liShow.
        iApply prove_with_subtype_default.
        iRename select (LL _ _ _ _ _) into "Hall".
        iSplitL "Hall".
        { open_cache.
          rename select (use_struct_layout_alg (Node_sls _) = Some _) into Hnode_layout.
          iEval (rewrite /use_struct_layout_alg' Hnode_layout /=) in "Hall".
          iExact "Hall".
        }
        rep <-! <3000 liRStep; liShow.
        { liRStepUntilTac (
            fun _ => lazymatch goal with
            | |- environments.envs_entails _
                   (typed_context_fold _ _ _ _ (arg_self :: _) _ _) => idtac
            end
          ).
          iApply (typed_context_fold_remove_loc arg_self).
          rep <-! <3000 liRStep; liShow.
          rep liRStep; liShow.
          liInst Hevar_k 0%nat.
          liInst Hevar_x0 l'0.
          rep <-! <3000 liRStep; liShow.
          replace (use_struct_layout_alg' (Node_sls (st_of T_ty MetaNone))) with Node_sl by shelve_sidecond.
          rep <-! <3000 liRStep; liShow.
          { (* re-establish the backward loop invariant *)
            rep liRStep; liShow.
            liInst Hevar_x0 0%nat.
            liInst Hevar_x1 locs.
            liInst Hevar_x2 elems.
            liInst Hevar_x3 (length elems - k)%nat.
            rep <-! <3000 liRStep; liShow.
            liRStepUntilTac (
              fun _ => lazymatch goal with
              | |- environments.envs_entails _
                     (typed_context_fold _ _ _ _ (arg_self :: _) _ _) => idtac
              end
            ).
            iApply (typed_context_fold_remove_loc arg_self).
            rep <-! <3000 liRStep; liShow.
            rep liRStep; liShow.
            liInst Hevar_k (S k).
            replace (Nat.pred (length elems - k)) with (length elems - S k)%nat by lia.
            rep <-! <3000 liRStep; liShow.
          }
          { (* exit the backward loop and call split_off_after_node *)
            rep <-! <3000 liRStep.
            rep liRStep; liShow.
            iRename select (LL _ _ _ _ _)%I into "Hall".
            iRename select (big_sepL _ locs)%I into "Hfree".
            iApply prove_with_subtype_default.
            iSplitL "Hall Hfree".
            { iApply LL_restore_freeable.
              { by rewrite !length_fmap Hlen. }
              iFrame.
            }
            rep <-! <100 liRStep; liShow.
            rep <-! <400 liRStep; liShow.
          }
        }
        { (* impossible subtraction overflow *)
          exfalso. shelve_sidecond.
        }
        { (* impossible subtraction overflow *)
          exfalso. shelve_sidecond.
        } 
        { (* impossible subtraction overflow *)
          exfalso. shelve_sidecond.
        } 
      }
      { liShow. 
        iApply updateable_add_fupd.
        iRename select (_ ◁ₗ[π, Owned] _ @ ◁ LinkedList_inv_t _ _ _ _ _)%I into "Hlist".
        iEval (rewrite /LinkedList_inv_t) in "Hlist".
        iMod (ex_plain_t_destruct_owned with "Hlist") as (r) "[Hinv Hlist]"; first solve_ndisj.
        iDestruct "Hinv" as "(%Hheader & %Hlen & %Hnonnull & %Hbound & Hall)".
        iDestruct "Hall" as "[Hall _]".
        subst r.
        simpl in Hlen, Hnonnull.
        rewrite length_fmap in Hlen.
        iModIntro.
        liShow.
        rep liRStep; liShow.
        liInst Hevar_x0 elems.
        liInst Hevar_x2 locs.
        liInst Hevar_x3 alloc.
        rewrite list_fmap_compose.
        rep <-! <3000 liRStep; liShow.
        rep liRStep; liShow.
        iApply prove_with_subtype_default.
        iRename select (LL _ _ _ _ _) into "Hall".
        iSplitL "Hall".
        { open_cache.
          rename select (use_struct_layout_alg (Node_sls _) = Some _) into Hnode_layout.
          iEval (rewrite /use_struct_layout_alg' Hnode_layout /=) in "Hall".
          iExact "Hall".
        }
        rep <-! <3000 liRStep; liShow.
        { liRStepUntilTac (
              fun _ => lazymatch goal with
              | |- environments.envs_entails _
                     (typed_context_fold _ _ _ _ (arg_self :: _) _ _) => idtac
              end
            ).
          iApply (typed_context_fold_remove_loc arg_self).
          rep <-! <3000 liRStep; liShow.
          rep liRStep; liShow.
          liInst Hevar_k 0%nat.
          liInst Hevar_x0 l'0.
          (*liInst Hevar_x1 0%Z.*)
          (*liInst Hevar_x2 (Z.of_nat (i - 1)).*)
          (*liInst Hevar__iter_hist_46 (@nil Z).*)
          rep <-! <3000 liRStep; liShow.
          replace (use_struct_layout_alg' (Node_sls (st_of T_ty MetaNone))) with Node_sl by shelve_sidecond.

          rep <-! <3000 liRStep; liShow.
          { (* re-establish loop invariant *)
            rep liRStep; liShow.
            liInst Hevar_x0 k.
            liInst Hevar_x1 locs.
            liInst Hevar_x2 elems.
            liInst Hevar_x3 (length elems).
            rep <-! <3000 liRStep; liShow.
            liRStepUntilTac (
              fun _ => lazymatch goal with
              | |- environments.envs_entails _
                     (typed_context_fold _ _ _ _ (arg_self :: _) _ _) => idtac
              end
            ).
            iApply (typed_context_fold_remove_loc arg_self).
            rep <-! <3000 liRStep; liShow. } 
          { (* exit loop, call split_off_after_node, return *)
            rep <-! <3000 liRStep.
            rep liRStep; liShow.
            iRename select (LL _ _ _ _ _)%I into "Hall".
            iRename select (big_sepL _ locs)%I into "Hfree".
            iApply prove_with_subtype_default.
            iSplitL "Hall Hfree".
            { iApply LL_restore_freeable.
              { by rewrite !length_fmap Hlen. }
              iFrame.
            }
            rep <-! <3000 liRStep; liShow. 
          } 
        }
        { (* panicking on subtraction *) exfalso. shelve_sidecond. }
      } 
    }
  }
  { rep <-! <3000 liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: try rewrite list_fmap_compose//.
  all: try rewrite drop_all//.
  all: try rewrite head_lookup//.
  all: try rewrite firstn_all//.
  all: try rewrite -Hlen ?drop_all ?firstn_all //.
  - rename select (Some _ = if bool_decide _ then _ else _) into Hcase.
    destruct (bool_decide (Z.succ k ∈ usize)).
    + injection Hcase. lia. 
    + discriminate Hcase. 
  - assert (k = length elems - 1 - (i - 1))%nat as Hk_eq by lia.
    rewrite Hk_eq. 
    f_equiv. f_equiv. 
    rewrite Hlen. lia. 
  - rename select (Some _ = if bool_decide _ then _ else _) into Hcase.
    destruct (bool_decide (Z.succ k ∈ usize)).
    + injection Hcase. lia. 
    + discriminate Hcase. 
  - rewrite last_take_lookup.
    + f_equiv. lia.
    + split; first lia. rewrite Hlen. lia.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
