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
| inflation factor | `gammaTerm`, `Gamma`, `Gamma_nonneg`, `Gamma_pos`, `GammaClosed`, `harmonic`, `epsilonBarber` |
| slice and sampling objects | `sliceAverage`, `sliceFunctional`, `sliceAverage_exp_sum_eq_elemSym`, `centeredTwoLevelVector`, `sum_centeredTwoLevelVector_on`, `hypergeomPMF`, `hypergeomMgf`, `hypergeomB` |
| closed probability lemmas | `bounded_centered_mgf`, `exchangeable_tail_bound_from_mgf` |
| main conditional results | `exchangeable_mgf_bound`, `exchangeable_tail_bound`, `admissible_constant_lower_bound` |

## Verification contract

The repository distinguishes two kinds of declarations:

- Closed Lean proofs, which require only the assumptions shown in their theorem
  signatures.
- Explicit analytic-input structures, which record proof stages that are not
  yet derived inside the repository: `GammaAnalyticInputs`,
  `HypergeometricAnalyticInputs`, `ThreePointAnalyticInputs`,
  `SliceAnalyticInputs`, and `MainAnalyticInputs`.

Consequently, the main probability bounds are presently verified reductions
from named analytic inputs, not unconditional end-to-end formalizations.  The
tail estimate is now proved from the MGF estimate by a checked Chernoff
argument; it is no longer a separate field of `MainAnalyticInputs`.  The project
page displays the remaining boundary declaration by declaration.

## Project page

- [Project overview](https://statchan1106.github.io/exchangeable-hoeffding-lean/)
- [Proof blueprint](https://statchan1106.github.io/exchangeable-hoeffding-lean/blueprint/web/)

## Build

```powershell
cd testlean
lake build
```
