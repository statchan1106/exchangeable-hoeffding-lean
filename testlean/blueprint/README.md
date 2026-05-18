# Exchangeable Hoeffding Blueprint

This directory is the web blueprint for the Lean 4 project.

The intended workflow is:

```powershell
python -m pip install leanblueprint invoke
python -m invoke blueprint
```

On this Windows machine, installing `leanblueprint` may fail because its
dependency `pygraphviz` needs Microsoft C++ Build Tools.  The GitHub Actions
workflow in `.github/workflows/blueprint.yml` is configured to build on Ubuntu,
where those dependencies are easier to install.

For local preview without installing anything, open:

```text
blueprint/web/index.html
```

## Files

- `src/content.tex`: source blueprint text.
- `src/preamble.tex`: LaTeX setup for theorem environments and macros.
- `web.tex`: entry point for web generation.
- `print.tex`: entry point for a printable PDF-style version.
- `lean_decls`: Lean declaration names referenced by the blueprint.
- `web/index.html`: static preview page committed for immediate browsing.

