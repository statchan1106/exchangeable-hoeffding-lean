# Blueprint source

The mathematical source lives in `src/content.tex`. It is organized by paper
results, Lean declaration names, and proof roles. The `\lean`, `\leanok`, and
`\uses` annotations support declaration checking and dependency-graph
generation with LeanBlueprint.

From the repository root, after building the Lean project:

```sh
leanblueprint checkdecls
leanblueprint web
leanblueprint pdf
```

The hand-authored reader page in `docs/` is immediately viewable without the
blueprint toolchain. The generated blueprint remains the declaration-aware
source of truth for automated cross-checking.
