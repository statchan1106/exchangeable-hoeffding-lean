# Exchangeable Hoeffding in Lean 4

This repository is being developed as a Lean 4 companion project for Seongchan
Lee and Ilmun Kim, *A Sharper Hoeffding Bound for Weighted Sums of Exchangeable
Random Variables*.

The project explores how a proof assistant can clarify and verify the logical
structure of a statistical concentration proof.  The current Lean development
follows the submitted TeX notation.  It does not yet prove every analytic lemma
in the paper; instead, it avoids global axioms and collects the remaining
mathematical ingredients in an explicit interface:

```lean
ExchangeableHoeffding.ProofObligations
```

The main Lean-checked reduction theorem is:

```lean
ExchangeableHoeffding.theorem_2_1
```

It states that the paper's main exchangeable Hoeffding MGF bound follows once
the listed proof obligations are supplied.  A complete formalization means
proving every field of `ProofObligations`.

## Lean entry point

```lean
import Testlean.ExchangeableHoeffding.NoGlobalAxioms
```

The module defines the centered weighted statistic, exchangeability, the
finite-population inflation factor `Gamma`, Hamming-slice objects, and the
proof-obligation interface.

## Project layout

```text
lakefile.toml                         Lean package configuration
Testlean/ExchangeableHoeffding/       Lean source
blueprint/src/                        TeX blueprint source
site/                                 GitHub Pages source
tasks.py                              optional leanblueprint helper
DEPLOY.md                             deployment notes
```

The root of the Git repository is intentionally not a second Lean package; this
directory is the only Lake package.

## Blueprint website

The TeX blueprint source lives in:

- `blueprint/src/content.tex`
- `blueprint/web.tex`
- `blueprint/print.tex`
- `blueprint/lean_decls`

The committed GitHub Pages source lives in:

- `site/index.html`
- `site/blueprint/web/index.html`

Open `site/index.html` locally to preview the published page.  For the optional
Lean blueprint build from `blueprint/src`, install `leanblueprint` and run:

```powershell
python -m invoke blueprint
```

On Windows this may require Microsoft C++ Build Tools because the dependency
`pygraphviz` compiles native code.  The repository includes
`.github/workflows/blueprint.yml`, which builds the blueprint on Ubuntu and
deploys it to GitHub Pages.

## Near-term goals

1. Prove the deterministic projection identities over `Fin N`.
2. Verify endpoint computations such as `Gamma 2 = 2`.
3. Build the Hamming-slice API needed for the reduction step.
4. Gradually replace fields of `ProofObligations` with Lean proofs.

## Deployment

The GitHub Pages deployment notes are in `DEPLOY.md`.  The intended GitHub owner
is `statchan1106`.
