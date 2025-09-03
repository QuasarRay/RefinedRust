From refinedrust Require Import typing.
From rrstd.iterator.theories Require Import iterator.

Record MapX (I : RT) (F : RT) : Type := mk_map_x {
  map_it : RT_xt I;
  map_clos : RT_xt F;
}.
Global Arguments map_it {_ _}.
Global Arguments map_clos {_ _}.
Global Arguments mk_map_x {_ _}.
Definition MapXRT (I F : RT) := directRT (MapX I F).

Global Instance MapX_inh I F :
Inhabited (RT_xt I) → Inhabited (RT_xt F) → Inhabited (MapX I F).
Proof.
  intros Ha Hb. exact (populate (mk_map_x inhabitant inhabitant)).
Qed.

Definition li_sealed `{!refinedrustGS Σ} (P : iProp Σ) : iProp Σ :=
  P.
Global Typeclasses Opaque li_sealed.
