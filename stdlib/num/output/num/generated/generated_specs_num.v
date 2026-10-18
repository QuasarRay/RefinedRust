From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.num.num Require Export generated_code_num.

Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_i128_is_negative  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i128_is_positive  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i16_is_negative  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i16_is_positive  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i32_is_negative  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i32_is_positive  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i64_is_negative  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i64_is_positive  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i8_is_negative  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i8_is_positive  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_isize_is_negative  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isize_is_negative  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x < 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_isize_is_positive  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isize_is_positive  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x > 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), other :@: (int U128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U128);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_checked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_checked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), rhs :@: (int U128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x + rhs ≤ MaxInt u128) then Some (x + rhs)%Z else None @ (Option_ty (Z) -[] -[(int U128)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_checked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_checked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), rhs :@: (int U128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x * rhs ≤ MaxInt u128) then Some (x * rhs)%Z else None @ (Option_ty (Z) -[] -[(int U128)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_checked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_checked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), rhs :@: (int U128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x >= rhs) then Some (x - rhs)%Z else None @ (Option_ty (Z) -[] -[(int U128)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_unchecked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_unchecked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), rhs :@: (int U128);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hsum_in_range" (x + rhs ∈ u128)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x + rhs)%Z @ (int U128);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_unchecked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_unchecked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), rhs :@: (int U128);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hproduct_in_range" (x * rhs ∈ u128)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x * rhs)%Z @ (int U128);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_wrapping_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_wrapping_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), rhs :@: (int U128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ((x - rhs) `mod` (MaxInt u128 + 1))%Z @ (int U128);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), other :@: (int U16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U16);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_checked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_checked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), rhs :@: (int U16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x + rhs ≤ MaxInt u16) then Some (x + rhs)%Z else None @ (Option_ty (Z) -[] -[(int U16)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_checked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_checked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), rhs :@: (int U16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x * rhs ≤ MaxInt u16) then Some (x * rhs)%Z else None @ (Option_ty (Z) -[] -[(int U16)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_checked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_checked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), rhs :@: (int U16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x >= rhs) then Some (x - rhs)%Z else None @ (Option_ty (Z) -[] -[(int U16)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_unchecked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_unchecked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), rhs :@: (int U16);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hsum_in_range" (x + rhs ∈ u16)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x + rhs)%Z @ (int U16);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_unchecked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_unchecked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), rhs :@: (int U16);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hproduct_in_range" (x * rhs ∈ u16)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x * rhs)%Z @ (int U16);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_wrapping_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_wrapping_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), rhs :@: (int U16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ((x - rhs) `mod` (MaxInt u16 + 1))%Z @ (int U16);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), other :@: (int U32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U32);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_checked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_checked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), rhs :@: (int U32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x + rhs ≤ MaxInt u32) then Some (x + rhs)%Z else None @ (Option_ty (Z) -[] -[(int U32)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_checked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_checked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), rhs :@: (int U32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x * rhs ≤ MaxInt u32) then Some (x * rhs)%Z else None @ (Option_ty (Z) -[] -[(int U32)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_checked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_checked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), rhs :@: (int U32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x >= rhs) then Some (x - rhs)%Z else None @ (Option_ty (Z) -[] -[(int U32)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_unchecked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_unchecked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), rhs :@: (int U32);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hsum_in_range" (x + rhs ∈ u32)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x + rhs)%Z @ (int U32);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_unchecked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_unchecked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), rhs :@: (int U32);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hproduct_in_range" (x * rhs ∈ u32)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x * rhs)%Z @ (int U32);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_wrapping_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_wrapping_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), rhs :@: (int U32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ((x - rhs) `mod` (MaxInt u32 + 1))%Z @ (int U32);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), other :@: (int U64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U64);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_checked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_checked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), rhs :@: (int U64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x + rhs ≤ MaxInt u64) then Some (x + rhs)%Z else None @ (Option_ty (Z) -[] -[(int U64)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_checked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_checked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), rhs :@: (int U64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x * rhs ≤ MaxInt u64) then Some (x * rhs)%Z else None @ (Option_ty (Z) -[] -[(int U64)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_checked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_checked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), rhs :@: (int U64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x >= rhs) then Some (x - rhs)%Z else None @ (Option_ty (Z) -[] -[(int U64)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_unchecked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_unchecked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), rhs :@: (int U64);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hsum_in_range" (x + rhs ∈ u64)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x + rhs)%Z @ (int U64);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_unchecked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_unchecked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), rhs :@: (int U64);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hproduct_in_range" (x * rhs ∈ u64)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x * rhs)%Z @ (int U64);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_wrapping_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_wrapping_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), rhs :@: (int U64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ((x - rhs) `mod` (MaxInt u64 + 1))%Z @ (int U64);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), other :@: (int U8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_checked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_checked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), rhs :@: (int U8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x + rhs ≤ MaxInt u8) then Some (x + rhs)%Z else None @ (Option_ty (Z) -[] -[(int U8)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_checked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_checked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), rhs :@: (int U8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x * rhs ≤ MaxInt u8) then Some (x * rhs)%Z else None @ (Option_ty (Z) -[] -[(int U8)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_checked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_checked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), rhs :@: (int U8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x >= rhs) then Some (x - rhs)%Z else None @ (Option_ty (Z) -[] -[(int U8)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_unchecked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_unchecked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), rhs :@: (int U8);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hsum_in_range" (x + rhs ∈ u8)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x + rhs)%Z @ (int U8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_unchecked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_unchecked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), rhs :@: (int U8);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hproduct_in_range" (x * rhs ∈ u8)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x * rhs)%Z @ (int U8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_wrapping_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_wrapping_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), rhs :@: (int U8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ((x - rhs) `mod` (MaxInt u8 + 1))%Z @ (int U8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), other :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_checked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_checked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), rhs :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x + rhs ≤ MaxInt usize) then Some (x + rhs)%Z else None @ (Option_ty (Z) -[] -[(int USize)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_checked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_checked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), rhs :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x * rhs ≤ MaxInt usize) then Some (x * rhs)%Z else None @ (Option_ty (Z) -[] -[(int USize)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_checked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_checked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), rhs :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, if bool_decide (x >= rhs) then Some (x - rhs)%Z else None @ (Option_ty (Z) -[] -[(int USize)]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_unchecked_add  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_unchecked_add  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), rhs :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hsum_in_range" (x + rhs ∈ usize)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x + rhs)%Z @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_unchecked_mul  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_unchecked_mul  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), rhs :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(name_hint "Hproduct_in_range" (x * rhs ∈ usize)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x * rhs)%Z @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_wrapping_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_wrapping_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), rhs :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ((x - rhs) `mod` (MaxInt usize + 1))%Z @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).


Definition trait_incl_of_i128_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i128_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I128), other :@: (int I128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U128);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i16_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i16_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I16), other :@: (int I16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U16);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i32_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i32_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I32), other :@: (int I32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U32);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i64_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i64_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I64), other :@: (int I64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U64);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_i8_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_i8_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int I8), other :@: (int I8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int U8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_isize_abs_diff  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_isize_abs_diff  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, other) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int ISize), other :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.abs (x - other) @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_is_power_of_two  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_saturating_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_saturating_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), rhs :@: (int U128);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.max 0%Z (x - rhs)%Z @ (int U128);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u128_unchecked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u128_unchecked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U128), rhs :@: (int U128);
      (* precondition. *) (λ π : thread_id, (⌜((rhs ≤ x)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x - rhs)%Z @ (int U128);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_is_power_of_two  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_saturating_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_saturating_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), rhs :@: (int U16);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.max 0%Z (x - rhs)%Z @ (int U16);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u16_unchecked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u16_unchecked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U16), rhs :@: (int U16);
      (* precondition. *) (λ π : thread_id, (⌜((rhs ≤ x)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x - rhs)%Z @ (int U16);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_is_power_of_two  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_saturating_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_saturating_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), rhs :@: (int U32);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.max 0%Z (x - rhs)%Z @ (int U32);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u32_unchecked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u32_unchecked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U32), rhs :@: (int U32);
      (* precondition. *) (λ π : thread_id, (⌜((rhs ≤ x)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x - rhs)%Z @ (int U32);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_is_power_of_two  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_saturating_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_saturating_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), rhs :@: (int U64);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.max 0%Z (x - rhs)%Z @ (int U64);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u64_unchecked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u64_unchecked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U64), rhs :@: (int U64);
      (* precondition. *) (λ π : thread_id, (⌜((rhs ≤ x)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x - rhs)%Z @ (int U64);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_is_power_of_two  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_saturating_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_saturating_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), rhs :@: (int U8);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.max 0%Z (x - rhs)%Z @ (int U8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_u8_unchecked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_u8_unchecked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int U8), rhs :@: (int U8);
      (* precondition. *) (λ π : thread_id, (⌜((rhs ≤ x)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x - rhs)%Z @ (int U8);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_is_power_of_two  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_is_power_of_two  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (is_power_of_two (Z.to_nat x)) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_saturating_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_saturating_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), rhs :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, Z.max 0%Z (x - rhs)%Z @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_usize_unchecked_sub  : (spec_with _ _ (thread_id → iProp Σ)) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (λ π, (True)%I).

Definition type_of_usize_unchecked_sub  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (x, rhs) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: (int USize), rhs :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜((rhs ≤ x)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (x - rhs)%Z @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).



End specs.
