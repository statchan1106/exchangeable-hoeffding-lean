# Exchangeable Hoeffding formalization

This Lake package contains the formal development for a sharper Hoeffding bound
for weighted sums of bounded exchangeable random variables.

```lean
import Testlean.ExchangeableHoeffding.All
```

The namespace is `ExchangeableHoeffding`.  The public API is organized by
mathematical role rather than by source location:

- `centeredWeightedSum_eq_centered_coordinates` proves that the projected-dot
  definition equals the centered weighted statistic used in the paper.
- `sum_zeroPad`, `dot_zeroPad`, `sum_projOnePerp_eq_zero`, and
  `projOnePerp_idempotent` provide the finite-algebra foundation.
- `measurable_dot`, `abs_dot_le_sum_abs`, and
  `integrable_exp_mul_dot_of_bounded` close the bounded-statistic interface.
- `bounded_centered_mgf` is the checked Hoeffding lemma used by the sampling
  argument.
- `exchangeable_tail_bound_from_mgf` proves the Chernoff step from the MGF
  estimate instead of taking the tail estimate as an input.
- `Gamma`, `sliceFunctional`, `hypergeomMgf`, and `tailThreshold` represent the
  main analytic quantities.
- `exchangeable_mgf_bound`, `exchangeable_tail_bound`, and
  `admissible_constant_lower_bound` expose the high-level conclusions.

The project does not silently treat unformalized mathematics as proved.  The
remaining research-level steps are explicit parameters named
`GammaAnalyticInputs`, `HypergeometricAnalyticInputs`,
`ThreePointAnalyticInputs`, `SliceAnalyticInputs`, and `MainAnalyticInputs`.

The formalization is led by [Seongchan Lee](https://statchan1106.github.io/)
for joint work with his advisor, Ilmun Kim.

## Build

```powershell
lake build
```

## Documentation

- [Project overview](https://statchan1106.github.io/exchangeable-hoeffding-lean/)
- [Proof blueprint](https://statchan1106.github.io/exchangeable-hoeffding-lean/blueprint/web/)
