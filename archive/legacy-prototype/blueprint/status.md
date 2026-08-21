# Formalization status

The active import is:

```lean
import Testlean.ExchangeableHoeffding.All
```

## Closed proofs

The following declarations are proved directly and have no project-specific
analytic input parameter:

| Role | Declaration |
| --- | --- |
| squared-norm positivity | `normSq_nonneg` |
| dot products are measurable | `measurable_dot` |
| cube-valued coordinates bound a dot product | `abs_dot_le_sum_abs` |
| zero-padding preserves sums | `sum_zeroPad` |
| zero-padding preserves the relevant dot product | `dot_zeroPad` |
| projected statistic equals the centered coordinate formula | `centeredWeightedSum_eq_centered_coordinates` |
| projection has zero coordinate sum | `sum_projOnePerp_eq_zero` |
| zero-sum vectors are fixed by projection | `projOnePerp_eq_self` |
| projection is idempotent | `projOnePerp_idempotent` |
| permutation invariance follows from exchangeability | `exchangeability_supports_symmetrization` |
| endpoint inflation calculations | `gamma_two`, `harmonic_two`, `epsilonBarber_two`, `gamma_eq_barber_two` |
| inflation-factor positivity | `gammaTerm_nonneg`, `Gamma_nonneg`, `gammaTerm_one_pos`, `Gamma_pos` |
| slice average equals the elementary-symmetric formula | `sliceAverage_exp_sum_eq_elemSym`, `sliceFunctional_eq_log_sliceAverage` |
| slice cardinality and normalization | `sliceSubsets_eq_powersetCard`, `card_sliceSubsets`, `sliceAverage_one` |
| two-level parameterization and intersection-count algebra | `sum_twoLevelVector`, `normSq_twoLevelVector`, `sum_centeredTwoLevelVector`, `normSq_centeredTwoLevelVector`, `sum_centeredTwoLevelVector_on` |
| Lagrange tangent identities for three distinct coordinates | `lagrange_tangent_sum_zero`, `lagrange_tangent_weighted_sum_zero` |
| Hoeffding lemma in the sampling normalization | `bounded_centered_mgf` |
| exponential linear statistics are integrable | `integrable_exp_mul_dot_of_bounded` |
| Chernoff derivation of the tail estimate from the MGF estimate | `exchangeable_tail_bound_from_mgf` |

## Conditional reductions

The following declarations compile as rigorous implications, but their first
argument packages mathematics that is not yet proved inside this repository:

| Result | Required input |
| --- | --- |
| `gamma_strictly_improves_barber` | `GammaAnalyticInputs` |
| `exchangeable_mgf_bound` | `MainAnalyticInputs` |
| `exchangeable_tail_bound` | `MainAnalyticInputs.zero_sum_mgf_bound`; the Chernoff step is closed |
| `admissible_constant_lower_bound` | `MainAnalyticInputs` |

The remaining analytic stages are represented by
`HypergeometricAnalyticInputs`, `ThreePointAnalyticInputs`, and
`SliceAnalyticInputs`.  This boundary is intentional and machine-visible: the
project page must not label these stages as closed proofs until constructors for
the corresponding input structures are themselves proved.

## Completion criterion

The end-to-end formalization is complete only when every analytic-input
structure has a closed constructor and the public probability bounds no longer
require one of these structures as an argument.
