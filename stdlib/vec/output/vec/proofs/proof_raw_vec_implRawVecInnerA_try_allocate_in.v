From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.vec.vec.generated Require Import generated_code_vec generated_specs_vec generated_template_raw_vec_implRawVecInnerA_try_allocate_in.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma raw_vec_implRawVecInnerA_try_allocate_in_proof (π : thread_id) :
  raw_vec_implRawVecInnerA_try_allocate_in_lemma π.
Proof.
  raw_vec_implRawVecInnerA_try_allocate_in_prelude.

  1: rep <-! <3000 liRStep.
  { case_bool_decide as Hlayout_fits.
    all: simplify_eq.
    simpl.
    rep <-! <3000 liRStep.
    rep <-! <3000 liRStep.
    { rep liRStep.
      match goal with
      | |- length (protected ?bytes) = ?size ∧ _ =>
          liInst bytes (replicate size (MByte byte0)); split;
          [change (length (replicate size (MByte byte0)) = size);
            rewrite length_replicate; done |]
      end.
      rep <-! < 3000 liRStep. }
    { rep 3000 liRStep. }
    { rep <-! <3000 liRStep.
      { rep liRStep.
        match goal with
        | |- length (protected ?bytes) = ?size ∧ _ =>
            match goal with Hbytes_length : length ?allocated_bytes = size |- _ =>
              liInst bytes allocated_bytes; split; [exact Hbytes_length |]
            end
        end.
        rep liRStep. }
      { rep <-! <3000 liRStep. } 
    } 
  } 
  { rep 3000 liRStep. }
  
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: try nia.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
