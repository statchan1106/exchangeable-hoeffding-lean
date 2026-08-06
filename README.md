# Exchangeable Hoeffding formalization

This repository is the Lean formalization project led by
[Seongchan Lee](https://statchan1106.github.io/) for the joint paper
*A Sharper Hoeffding Bound for Weighted Sums of Exchangeable Random Variables*,
coauthored with his advisor, Ilmun Kim.

The public import is:

```lean
import Testlean.ExchangeableHoeffding.All
```

All declarations live in the `ExchangeableHoeffding` namespace.  Names describe
their mathematical role, so the development can be read without knowing the
source-tree layout.

## Mathematical target

For exchangeable random variables in `[-1, 1]`, the project studies

\[
\mathbb E\exp\!\left(\lambda\sum_{i=1}^n
w_i(X_i-\overline X_N)\right)
\le
\exp\!\left(\frac{\lambda^2}{2}\Gamma_N
\|P_{\mathbf 1^\perp}\widetilde w\|_2^2\right).
\]

The formal bridge from the statistic on the left to the projected dot product
is proved by `centeredWeightedSum_eq_centered_coordinates`.

## Declaration guide

| Role | Main declarations |
| --- | --- |
| finite vectors and centering | `dot`, `normSq`, `avg`, `zeroPad`, `projOnePerp`, `centeredWeightedSum` |
| checked finite identities | `sum_zeroPad`, `dot_zeroPad`, `centeredWeightedSum_eq_centered_coordinates`, `sum_projOnePerp_eq_zero`, `projOnePerp_idempotent` |
| measurability and cube bounds | `measurable_dot`, `abs_dot_le_sum_abs`, `integrable_exp_mul_dot_of_bounded` |
| probabilistic assumptions | `Exchangeable`, `BoundedByOne` |
| inflation factor | `Gamma_eq_closed`, `gamma_asymptotic_expansion`, `gamma_strictly_improves_barber`, `gammaAnalyticInputs` |
| finite sampling martingale | `samplingMgf_step`, `samplingMgf_le_smallSamplingB`, `samplingMgf_complement`, `hypergeometric_mgf_bound` |
| hypergeometric identification | `sum_hypergeomPMF`, `hypergeomMgf_eq_pmf_sum`, `hypergeomPMF_symm`, `hypergeomMgf_symm` |
| two-level slice chain | `eq_centeredTwoLevelVector_of_atMostTwoValues`, `sliceAverage_exp_centeredTwoLevelVector_eq_hypergeomMgf`, `slice_mgf_bound_of_atMostTwoValues` |
| closed probability lemmas | `bounded_centered_mgf`, `exchangeable_tail_bound_from_mgf` |
| conditional assembly | `SliceAnalyticInputs.slice_mgf_bound`, `exchangeable_mgf_bound` |
| main conditional results | `exchangeable_mgf_bound`, `exchangeable_tail_bound`, `admissible_constant_lower_bound` |

## Verification contract

The repository distinguishes two kinds of declarations:

- Closed Lean proofs, which require only the assumptions shown in their theorem
  signatures.
- Explicit analytic-input structures, which make the remaining proof boundary
  visible. `GammaAnalyticInputs` and `HypergeometricAnalyticInputs` now have
  closed constructors. `SliceAnalyticInputs` contains only the global two-level
  extremizer assertion. `ThreePointAnalyticInputs` and `MainAnalyticInputs`
  still contain paper-level obligations.

Consequently, the full probability theorem is not yet unconditional. The
inflation-factor analysis, sharpened hypergeometric MGF, transpose symmetry,
and complete two-level slice estimate are closed. What remains is the
three-coordinate/global extremizer, the outer permutation-to-slice assembly,
and the parity-dependent lower-bound witness. The tail estimate is already
derived from the MGF estimate by a checked Chernoff argument.

## Project page

- [Project overview](https://statchan1106.github.io/exchangeable-hoeffding-lean/)
- [Proof blueprint](https://statchan1106.github.io/exchangeable-hoeffding-lean/blueprint/web/)

## Build

```powershell
cd testlean
lake build
```
