From radium Require Export val.

Definition thread_id := nat.

Inductive memory_access_kind :=
| NormalAccess
| VolatileAccess.

Inductive memory_access_atomicity :=
| AtomicAccess
| NonAtomicAccess.

Record memory_access := {
  access_thread : thread_id;
  access_kind : memory_access_kind;
  access_atomicity : memory_access_atomicity;
  access_loc : loc;
  access_layout : layout;
}.

(** Observable Radium interactions with a lower-level machine state. *)
Inductive radium_event :=
| MemoryRead (access : memory_access) (value : val)
| MemoryWrite (access : memory_access) (value : val).
