# Canonical Op Compatibility Plan

## Goal

Add canonical `use_op_alg` compatibility to `type`, while keeping it sound for uninitialized bytes and unsized metadata-dependent types.

The compatibility field should be restricted to sized/no-metadata types:

```coq
_ty_has_op_type_compat ot mt :
  ty_metadata_kind = MetadataNone ->
  use_op_alg (ty_syn_type MetaNone) = Some ot ->
  mt <> MCId ->
  _ty_has_op_type ot mt;
```

This avoids forcing canonical ops for unsized types such as slices, where `ty_syn_type MetaNone` is currently only a placeholder.

## Type Interface Changes

1. Update `rust_typing/base/type.v`.

2. Re-enable/add `_ty_has_op_type_compat` to `Record type` with the `ty_metadata_kind = MetadataNone` premise.

3. Add a public wrapper after `ty_has_op_type_unfold`:

```coq
Lemma ty_has_op_type_compat `{!typeGS Σ} {rt} (ty : type rt) ot mt :
  ty.(ty_metadata_kind) = MetadataNone ->
  use_op_alg (ty.(ty_syn_type) MetaNone) = Some ot ->
  mt <> MCId ->
  ty_has_op_type ty ot mt.
```

4. Mirror the field in `simple_type`:

```coq
st_has_op_type_compat ot mt :
  use_op_alg st_syn_type = Some ot ->
  mt <> MCId ->
  st_has_op_type ot mt;
```

No metadata premise is needed for `simple_type`, because `ty_of_st` always has `MetadataNone`.

5. Forward the `ty_of_st` obligation through `st_has_op_type_compat`.

6. Update the OFE reconstruction predicates in `type.v` for both `type` and `simple_type` so the new proof fields are preserved.

## Uninit Changes

1. Update `rust_typing/base/uninit_def.v`.

2. Change `uninit st` to expose an untyped syntype over `st`'s layout:

```coq
st_syn_type := UntypedSynType (use_layout_alg' st)
```

3. Keep ownership semantically layout-based against the original syntype:

```coq
exists ly, syn_type_has_layout st ly /\ v `has_layout_val` ly
```

4. Keep `_has_op_type` layout-based, but ensure canonical compatibility now proves only `UntypedOp (use_layout_alg' st)` for `MCNone`/`MCCopy`.

5. Use these lemmas to bridge old and new layout facts:

- `syn_type_has_layout_make_untyped`
- `use_layout_alg_eq'`
- `syn_type_has_layout_inj`

6. Update `st_has_layout`, `st_op_type_stable`, `st_memcast_compat`, and `st_has_op_type_untyped` obligations accordingly.

7. Add `st_has_op_type_compat`; for `UntypedSynType ly`, `use_op_alg` canonicalizes to `UntypedOp ly`, which is sound for arbitrary bytes.

## MaybeUninit Changes

1. Update `rust_typing/primitive/maybe_uninit.v`.

2. Change exposed syntype to raw layout:

```coq
ty_syn_type m := UntypedSynType (use_layout_alg' (T.(ty_syn_type) m))
```

3. Keep semantic ownership split:

- `Some r`: owns initialized `T`.
- `None`: owns arbitrary bytes of `T.(ty_syn_type) m`'s layout.

4. Change `None` ownership/sharing to use the matching untyped `uninit` view where needed.

5. Restrict global `_ty_has_op_type` to untyped operations over `ty_syn_type MetaNone`:

```coq
exists ly,
  syn_type_has_layout (ty_syn_type maybe_uninit MetaNone) ly /\
  match mt with
  | MCNone => ot_layout ot = ly
  | MCCopy => ot = UntypedOp ly
  | MCId => ot = UntypedOp ly
  end
```

6. Do not expose typed `MCCopy` through `maybe_uninit` globally. Typed copying for initialized values should be handled locally through the `Some` refinement and delegated to `T` there.

7. Update memcast proof:

- `None`: delegate to uninit/untyped layout-preservation proof.
- `Some`: global copy is untyped, so preserve initialized ownership through untyped memcast/layout identity rather than typed `T` copy where possible.

8. Update helper lemmas such as `maybe_uninit_None_unfold`, `type_incl_maybe_uninit_None`, and `type_incl_None_maybe_uninit` to account for the changed exposed syntype.

## Other Type Definitions

Add the new canonical compatibility obligation to all direct `type` and `simple_type` definitions.

Expected locations:

- `rust_typing/base/int.v`
- `rust_typing/base/value.v`
- `rust_typing/base/uninit_def.v`
- `rust_typing/primitive/alias_ptr.v`
- `rust_typing/primitive/functions.v`
- `rust_typing/primitive/existentials.v`
- `rust_typing/primitive/existentials_na.v`
- `rust_typing/primitive/fixpoint.v`
- `rust_typing/primitive/maybe_uninit.v`
- `rust_typing/shr_ref/def.v`
- `rust_typing/mut_ref/def.v`
- `rust_typing/array/def.v`
- `rust_typing/array/slice.v`
- `rust_typing/struct/def.v`
- `rust_typing/enum/def.v`

Implementation notes:

- Simple int/bool/char/pointer/function-pointer types should discharge compatibility by inversion on `use_op_alg` and existing `is_*_ot` definitions.
- Arrays should use the canonical `UntypedOp` produced by `use_op_alg` for arrays.
- Structs should decompose canonical `StructOp` and use `ty_has_op_type_compat` recursively for fields.
- Enums and unions already expose untyped canonical ops, so their untyped-only definitions should remain compatible.
- Existentials and fixpoints should forward compatibility to the wrapped/base type.
- Unsized types can prove the field vacuously when `ty_metadata_kind <> MetadataNone`, or use the new metadata premise to avoid requiring any canonical op.

## Verification Steps

1. Check `rust_typing/base/type.v` first.

2. Check `rust_typing/base/uninit_def.v` next.

3. Check `rust_typing/primitive/maybe_uninit.v` after uninit compiles.

4. Then check affected type-definition files in dependency order:

- `rust_typing/base/int.v`
- `rust_typing/base/value.v`
- `rust_typing/primitive/functions.v`
- `rust_typing/shr_ref/def.v`
- `rust_typing/mut_ref/def.v`
- `rust_typing/array/def.v`
- `rust_typing/struct/def.v`
- `rust_typing/enum/def.v`
- `rust_typing/primitive/existentials.v`
- `rust_typing/primitive/existentials_na.v`
- `rust_typing/primitive/fixpoint.v`

5. Run the project build/check command used by the repository after individual files pass.

## Main Soundness Point

The canonical op compatibility must not force typed reads/copies through arbitrary uninitialized bytes. That is why `uninit` and `maybe_uninit` expose an untyped syntype over the underlying layout. Their canonical op becomes `UntypedOp ly`, whose memcast semantics only require layout/length preservation rather than typed decoding validity.
