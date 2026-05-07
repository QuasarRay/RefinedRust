# RefinedRust Extract Goal Plugin

Rocq plugin for extracting the current proof goal into a standalone lemma.

Implemented commands:

- `Extract Goal as ident.`
- `Extract Goal.` (generates a name from the current proof, such as `proof_subgoal_1`)
- `Open Extracted Goal ident.` (experimental; opens a nested proof from a previously extracted goal)
- `Open Extracted Goal.` (opens the most recently extracted goal)
- `Use Extracted Goal ident.`
- `Use Last Extracted Goal.` (uses the most recently saved extracted helper)

To open a helper proof inside the current proof, first run
`Extract Goal as ident.`, then `Open Extracted Goal ident.`. The anonymous
forms can be used as `Extract Goal.` followed by `Open Extracted Goal.`.

Build from this directory with:

```sh
dune build
```

Run the local smoke test with:

```sh
dune runtest
```

Install the plugin into the current opam switch with:

```sh
opam install .
```

The project follows Dune's Rocq plugin layout:

- `src/` contains the public OCaml plugin library `refinedrust_extract_goal.plugin`.
- `theories/` contains Rocq files and a `rocq.theory` stanza depending on that plugin.
