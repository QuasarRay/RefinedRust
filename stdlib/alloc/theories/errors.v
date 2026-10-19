From refinedrust Require Import typing.
From rrstd.alloc.theories Require Import layout.

Inductive reserve_error :=
  | ReserveCapacityOverflow
  | ReserveAllocError (layout : rust_layout).

Global Instance reserve_error_inh : Inhabited reserve_error :=
  populate ReserveCapacityOverflow.

Canonical Structure reserve_errorRT := directRT reserve_error.
