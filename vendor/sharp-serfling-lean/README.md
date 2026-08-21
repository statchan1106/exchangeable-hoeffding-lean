# Lean 4 verification of the sharp Serfling inequality

This project formalizes *A Sharp Variance-Scale Refinement of Serfling's
Inequality* in Lean 4 and mathlib.  Finite probability spaces are represented
by explicit normalized finite sums, so the combinatorial identities and the
analytic bounds are checked directly by Lean's kernel.

The acceptance target is every named result and explicit auxiliary claim in
the 30-page manuscript `Sharp_Serfling (43).pdf`: the weighted
finite-population theorem, Serfling and exchangeable corollaries, sharp
centered-hypergeometric theorem, variational optimality, exact variance
identities, and the even/odd asymptotic statements.

That target is complete.  In particular, the development contains no
`sorry`, `admit`, project-defined axiom, `unsafe`, `implemented_by`, or
`opaque` declaration.  The audited final theorems use only Lean/mathlib's
ordinary logical foundations: `propext`, `Classical.choice`, and `Quot.sound`.

## Main entry points

- `SharpSerfling.FinitePopulation.finitePopulation_mgf`
- `SharpSerfling.FinitePopulation.finitePopulation_sharp_constant`
- `SharpSerfling.FinitePopulation.serfling_mgf`
- `SharpSerfling.FinitePopulation.serfling_tail`
- `SharpSerfling.FinitePopulation.serfling_lower_tail`
- `SharpSerfling.FinitePopulation.serfling_twoSided_tail`
- `SharpSerfling.FinitePopulation.weighted_exchangeable_mgf_centeredNorm`
- `SharpSerfling.FinitePopulation.weighted_exchangeable_tail`
- `SharpSerfling.FinitePopulation.exchangeable_sharp_constant`
- `SharpSerfling.FinitePopulation.weighted_exchangeable_mgf_centeredNorm_inLaw`
- `SharpSerfling.FinitePopulation.exchangeableInLaw_Cstar_sharp_constant`
- `SharpSerfling.FinitePopulation.statistic_variance_eq_rho_mul_populationVariance`
- `SharpSerfling.Hypergeometric.sharp_mgf`
- `SharpSerfling.Hypergeometric.sharp_constant`
- `SharpSerfling.Hypergeometric.actualVariance_eq_variance`
- `SharpSerfling.Hypergeometric.kappaStar_eq_kappa`
- `SharpSerfling.Hypergeometric.kappaStar_odd_attained`
- `SharpSerfling.Hypergeometric.tendsto_normalizedLogMgf_even_central`
- `SharpSerfling.FinitePopulation.exists_twoLevel_sliceMgf_maximizer`
- `SharpSerfling.exchangeableConstant_even_expansion`
- `SharpSerfling.exchangeableConstant_odd_expansion`
- `SharpSerfling.tendsto_nat_mul_exchangeableConstant_sub_one`
`TRACEABILITY.md` maps every named theorem, proposition, corollary, and lemma,
plus the manuscript's explicit variance, degeneracy, variational, and
asymptotic claims, to checked Lean declarations.

## Build and audit

```sh
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
rg -n '\b(sorry|admit)\b|^\s*axiom\b|\b(unsafe|implemented_by|opaque)\b' . \
  --glob '*.lean' --glob '!**/.lake/**'
```

No incomplete theorem is admitted into the source tree: work in progress is
tracked in `STATUS.md`, rather than represented by `sorry`, `admit`, or a
project-defined axiom.
