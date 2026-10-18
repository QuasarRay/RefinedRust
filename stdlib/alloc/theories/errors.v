From refinedrust Require Import typing.
From rrstd.alloc.theories Require Import layout.

Inductive reserve_error :=
  | ReserveCapacityOverflow
  | ReserveAllocError (layout : place_rfn rust_layout) (extra : place_rfn unit).

Global Instance reserve_error_inh : Inhabited reserve_error :=
  populate ReserveCapacityOverflow.

Canonical Structure reserve_errorRT := directRT reserve_error.
