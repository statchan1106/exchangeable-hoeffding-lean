# Exchangeable Hoeffding in Lean 4

This repository hosts a Lean 4 companion project for Seongchan Lee and Ilmun
Kim, *A Sharper Hoeffding Bound for Weighted Sums of Exchangeable Random
Variables*.

The active Lake package is `testlean/`.  The main formalization is the modular
development:

```lean
import Testlean.Exchangeable_Hoeffding_ver2.All
```

The Lean namespace is `ExchangeableHoeffding`.  The project keeps the paper's
mathematical ingredients explicit: finite algebra and endpoint computations are
proved directly where available, while deeper analytic inputs are represented as
small named theorem interfaces rather than global axioms.

## Repository Layout

```text
.github/workflows/                 GitHub Actions for Lean CI and Pages
testlean/lakefile.toml             Lean package configuration
testlean/Testlean/Exchangeable_Hoeffding_ver2/
                                    Modular Lean source
testlean/blueprint/src/content.tex TeX blueprint source
testlean/site/                     Static GitHub Pages source
```

## Pages

- [Project landing](https://statchan1106.github.io/exchangeable-hoeffding-lean/)
- [Blueprint](https://statchan1106.github.io/exchangeable-hoeffding-lean/blueprint/web/)

The blueprint is written to help a first-time reader compare the paper formulas
with Lean declarations and see what each module contributes to the proof.

## Current Lean Entry Points

```lean
ExchangeableHoeffding.theorem_2_1
ExchangeableHoeffding.corollary_2_2
ExchangeableHoeffding.optimal_lower_bound
ExchangeableHoeffding.gamma_lt_barber
```

## Build

```powershell
cd testlean
lake build
```
