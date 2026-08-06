# Formalization status

The public import is:

```lean
import Testlean.ExchangeableHoeffding.All
```

The status is attached to declaration roles, not to source-file locations.

## Closed proof chains

| Proof role | Representative declarations |
| --- | --- |
| finite centering algebra | `sum_zeroPad`, `dot_zeroPad`, `centeredWeightedSum_eq_centered_coordinates`, `sum_projOnePerp_eq_zero` |
| inflation factor | `Gamma_eq_closed`, `gamma_asymptotic_expansion`, `gamma_strictly_improves_barber`, `gammaAnalyticInputs` |
| finite Hoeffding lemma | `bounded_centered_mgf` |
| hypergeometric normalization | `sum_hypergeomPMF`, `hypergeomMgf_eq_pmf_sum` |
| sampling martingale | `samplingMgf_step`, `samplingMgf_le_smallSamplingB`, `samplingMgf_complement` |
| sharpened hypergeometric MGF | `hypergeometric_mgf_bound`, `hypergeometricAnalyticInputs` |
| hypergeometric transpose symmetry | `hypergeomPMF_symm`, `hypergeomMgf_symm` |
| two-level slice representation | `eq_centeredTwoLevelVector_of_atMostTwoValues` |
| exact slice/hypergeometric identification | `sliceAverage_exp_centeredTwoLevelVector_eq_hypergeomMgf` |
| matching the sampling factor to the norm | `hypergeomB_eq_gammaTerm_mul_normFactor`, `hypergeomB_le_Gamma_mul_normFactor` |
| complete bound for every two-level vector | `slice_mgf_bound_of_atMostTwoValues` |
| extremizer-to-slice assembly | `SliceAnalyticInputs.slice_mgf_bound` |
| MGF-to-tail Chernoff step | `exchangeable_tail_bound_from_mgf` |

These declarations contain no `sorry`, `admit`, or project-local axiom.

## Remaining proof boundary

Three mathematical stages are not yet closed end to end.

1. `ThreePointAnalyticInputs` records the repeated-root interpolation sign and
   the constrained three-coordinate maximum used in the local replacement
   argument.
2. `SliceAnalyticInputs` now contains only the global two-level extremizer
   assertion. Once this field is supplied, `SliceAnalyticInputs.slice_mgf_bound`
   derives the complete Hamming-slice inequality from closed code.
3. `MainAnalyticInputs` still packages the permutation/vertex symmetrization
   step and the parity-dependent universal lower bound. The centering and
   Chernoff parts around it are already closed.

`GammaAnalyticInputs` and `HypergeometricAnalyticInputs` are retained as named
compatibility interfaces, but both now have proved constructors:
`gammaAnalyticInputs` and `hypergeometricAnalyticInputs`.

## Completion criterion

The full theorem is end-to-end complete when closed constructors are supplied
for the three-point extremizer, the global slice extremizer, and the two fields
of `MainAnalyticInputs`, after which the public MGF, tail, and lower-bound
theorems can be exported without project-specific input arguments.
