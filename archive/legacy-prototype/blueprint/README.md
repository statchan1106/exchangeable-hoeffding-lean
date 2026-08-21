# Exchangeable Hoeffding Blueprint

This directory contains the TeX source for the formal blueprint.  The published
GitHub Pages site is committed separately under the project’s static site
directory.

The intended build workflow is:

```powershell
python -m pip install leanblueprint invoke
python -m invoke blueprint
```

For a local preview without installing the blueprint toolchain, open the
committed static proof page under `site/blueprint/web/`.

The blueprint is declaration-centered.  Its source text describes the roles of
functions and the proof dependencies between them; source paths are not part of
the mathematical reading order.  The `lean_decls` registry lists every Lean
declaration referenced by the page.
