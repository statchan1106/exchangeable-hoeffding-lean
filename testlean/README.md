# Exchangeable Hoeffding in Lean 4

This directory is the Lake package for a Lean 4 companion project to Seongchan
Lee and Ilmun Kim, *A Sharper Hoeffding Bound for Weighted Sums of Exchangeable
Random Variables*.

The formalization follows the notation of `SeongchanLee.tex` and is organized
around the modular development in:

```lean
import Testlean.Exchangeable_Hoeffding_ver2.All
```

The namespace is `ExchangeableHoeffding`.  The files make the paper's proof
architecture explicit without adding global axioms.  Definitions and already
checked finite algebra, such as `sum_projOnePerp_eq_zero`, are ordinary Lean
declarations.  Deeper analytic ingredients that are intended as later
formalization targets are recorded as theorem fields inside small structures
such as `MainProofObligations`, `SliceProofObligations`,
`HypergeometricProofObligations`, `ThreePointProofObligations`, and
`GammaProofObligations`.

## Main Lean Entry Points

```lean
ExchangeableHoeffding.theorem_2_1
ExchangeableHoeffding.corollary_2_2
ExchangeableHoeffding.optimal_lower_bound
ExchangeableHoeffding.gamma_lt_barber
```

The main theorem states the paper's exchangeable Hoeffding MGF bound in Lean:
after projecting the zero-padded weight vector onto the all-ones orthogonal
complement, the MGF is bounded with finite-population factor `Gamma N`.

## Module Map

```text
Testlean/Exchangeable_Hoeffding_ver2/Basic.lean
  finite vectors, dot product, normSq, avg, projection, zero padding,
  centeredWeightedSum, exchangeability, boundedness

Testlean/Exchangeable_Hoeffding_ver2/Gamma.lean
  Gamma_N, GammaClosed, Barber epsilon, endpoint computations, Gamma obligations

Testlean/Exchangeable_Hoeffding_ver2/Hypergeometric.lean
  hypergeometric PMF/MGF, B_{N,m}, Hoeffding and hypergeometric MGF obligations

Testlean/Exchangeable_Hoeffding_ver2/ThreePoint.lean
  three-coordinate objective and the Lagrange/three-point obligations

Testlean/Exchangeable_Hoeffding_ver2/HammingSlice.lean
  Hamming slices, elementary symmetric polynomials, slice functional,
  two-level and slice-inequality obligations

Testlean/Exchangeable_Hoeffding_ver2/Main.lean
  admissible constants, tail threshold, high-level obligations,
  theorem_2_1, corollary_2_2, optimal_lower_bound
```

## Paper to Lean Bridge

| Paper notation | Lean declaration |
| --- | --- |
| \(x \in \mathbb R^N\) | `Fin N -> Real` / `Fin N -> ℝ` |
| \(\widetilde w\) | `zeroPad hn w` |
| \(\bar X_N\) | `avg x` |
| \(P_{\mathbf 1^\perp} z\) | `projOnePerp z` |
| \(\sum_i w_i(X_i-\bar X_N)\) | `centeredWeightedSum hn w x` |
| \(\Gamma_N\) | `Gamma N`, `GammaClosed N` |
| \(F_{N,k}(y)\) | `sliceFunctional k y` |
| \(B_{N,m}\) | `hypergeomB N m` |

## Blueprint Website

Published pages:

- https://statchan1106.github.io/exchangeable-hoeffding-lean/
- https://statchan1106.github.io/exchangeable-hoeffding-lean/blueprint/web/

Local sources:

```text
blueprint/src/content.tex       TeX blueprint source
blueprint/lean_decls            Lean declaration list used by the blueprint
site/index.html                 GitHub Pages landing page
site/blueprint/web/index.html   Static blueprint page
```

## Build

From this directory:

```powershell
lake build
```

The repository-level GitHub Actions workflow builds this package with
`lake-package-directory: testlean`.
