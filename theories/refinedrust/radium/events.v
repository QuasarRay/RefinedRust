From radium Require Export val.

Definition thread_id := nat.

Inductive memory_access_kind :=
| NormalAccess
| VolatileAccess.

Inductive memory_access_atomicity :=
| AtomicAccess
| NonAtomicAccess.

(** Access qualifiers known before evaluating the pointer expression. *)
Record memory_access_desc := {
  access_kind : memory_access_kind;
  access_atomicity : memory_access_atomicity;
}.

Definition normal_nonatomic_access : memory_access_desc := {|
  access_kind := NormalAccess;
  access_atomicity := NonAtomicAccess;
|}.

Definition volatile_nonatomic_access : memory_access_desc := {|
  access_kind := VolatileAccess;
  access_atomicity := NonAtomicAccess;
|}.

Definition normal_atomic_access : memory_access_desc := {|
  access_kind := NormalAccess;
  access_atomicity := AtomicAccess;
|}.

Record memory_access := {
  access_thread : thread_id;
  access_desc : memory_access_desc;
  access_loc : loc;
  access_layout : layout;
}.

(** Complete a static descriptor with information resolved during execution. *)
Definition make_memory_access (π : thread_id) (desc : memory_access_desc)
    (l : loc) (ly : layout) : memory_access := {|
  access_thread := π;
  access_desc := desc;
  access_loc := l;
  access_layout := ly;
|}.

(** Observable Radium interactions with a lower-level machine state. *)
Inductive radium_event :=
| MemoryRead (access : memory_access) (value : val)
| MemoryWrite (access : memory_access) (value : val).
