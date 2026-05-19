# Formalization Status

## Current Shape

The active development is:

```lean
import Testlean.Exchangeable_Hoeffding_ver2.All
```

The code is modularized into `Basic`, `Gamma`, `Hypergeometric`, `ThreePoint`,
`HammingSlice`, and `Main`.  It does not introduce global axioms.  Major
paper-level ingredients that are not yet fully derived from Mathlib are stated
as theorem fields in explicit structures:

```lean
MainProofObligations
SliceProofObligations
HypergeometricProofObligations
ThreePointProofObligations
GammaProofObligations
```

## Already Checked Directly

- Finite vector definitions: `dot`, `normSq`, `avg`, `zeroPad`.
- Projection and centered statistic definitions:
  `projOnePerp`, `centeredWeightedSum`.
- Projection zero-sum lemma: `sum_projOnePerp_eq_zero`.
- Exchangeability as permutation invariance and the direct bridge
  `exchangeability_supports_symmetrization`.
- Endpoint computations:
  `gamma_two`, `harmonic_two`, `epsilonBarber_two`,
  `gamma_eq_barber_two`.
- The reductions exporting:
  `theorem_2_1`, `corollary_2_2`, `optimal_lower_bound`,
  `gamma_lt_barber`.

## Modular Responsibilities

`Basic.lean` sets up the finite-dimensional language and the statistical
assumptions.

`Gamma.lean` defines the finite-population inflation factor and Barber
comparison objects.

`Hypergeometric.lean` states the Hoeffding and hypergeometric MGF ingredients.

`ThreePoint.lean` states the Lagrange sign and three-coordinate extremizer
ingredients.

`HammingSlice.lean` connects Hamming slices, elementary symmetric polynomials,
and the two-level reduction.

`Main.lean` assembles the high-level theorem, tail bound, and optimality lower
bound from the named interfaces.

## Remaining Research-Level Interfaces

- Zero-sum exchangeable MGF bound.
- Hamming-slice inequality.
- Two-level slice extremizer.
- Classical Hoeffding lemma in the needed measure-theoretic form.
- Lagrange sign lemma and three-coordinate extremizer.
- Hypergeometric martingale MGF bound.
- Closed form, asymptotics, and finite comparison for `Gamma N`.
