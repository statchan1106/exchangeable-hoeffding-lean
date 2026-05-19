# Exchangeable Hoeffding in Lean 4

This repository hosts a Lean 4 companion project for Seongchan Lee and Ilmun
Kim, *A Sharper Hoeffding Bound for Weighted Sums of Exchangeable Random
Variables*.

The project explores how Lean can make the structure of a modern statistical proof explicit. 
The current Lean development avoids global axioms by collecting the hard mathematical ingredients in an explicit interface, 
ExchangeableHoeffding.ProofObligations. Lean then checks that the main MGF statement follows once those named ingredients are supplied. 
A complete formalization means replacing each field of ProofObligations by a Lean proof.

## Repository Layout

Only the `testlean/` directory is a Lean/Lake package.

```text
.github/workflows/        GitHub Actions for Lean CI and Pages deployment
README.md                 Project overview
testlean/lakefile.toml    Lean package configuration
testlean/Testlean/        Lean source files
testlean/blueprint/src/   TeX blueprint source aligned with the paper
testlean/site/            Static GitHub Pages site
```

Obsolete Lake scaffold files from the initial repository setup have been
removed, so the repository root is no longer a second Lean project.

## Blueprint Site

GitHub Pages landing page:

https://statchan1106.github.io/exchangeable-hoeffding-lean/

Blueprint page:

https://statchan1106.github.io/exchangeable-hoeffding-lean/blueprint/web/

The published static site source is in:

```text
testlean/site
```

The Lean blueprint source is in:

```text
testlean/blueprint/src/content.tex
```

## Lean Entry Point

```lean
import Testlean.ExchangeableHoeffding.NoGlobalAxioms
```

Core theorem:

```lean
ExchangeableHoeffding.theorem_2_1
```

First exchangeability bridge:

```lean
ExchangeableHoeffding.exchangeability_supports_symmetrization
```

## Current Status

The project currently provides:

- Lean definitions for exchangeability, boundedness, centering, projection, and
  the finite-population inflation factor `Gamma`;
- a no-global-axiom proof-obligation interface;
- a Lean-checked reduction from the proof-obligation interface to the main
  exchangeable Hoeffding MGF bound;
- a blueprint-style web page mapping paper statements to Lean names.
