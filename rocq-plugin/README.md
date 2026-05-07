# RefinedRust Extract Goal Plugin

Rocq plugin for extracting the current proof goal into a standalone lemma.

Implemented commands:

- `Extract Goal as ident.`
- `Use Extracted Goal ident.`

Build from this directory with:

```sh
dune build
```

Run the local smoke test with:

```sh
dune runtest
```

The project follows Dune's Rocq plugin layout:

- `src/` contains the public OCaml plugin library `refinedrust_extract_goal.plugin`.
- `theories/` contains Rocq files and a `rocq.theory` stanza depending on that plugin.
