# Formalization Status

## Verified shape

The current Lean file deliberately avoids global `axiom` declarations.  The
unproved mathematical ingredients are fields of:

```lean
structure ProofObligations : Prop
```

This means importing the project does not silently extend Lean's trusted kernel
with new facts.  A complete formalization will eventually be an explicit
inhabitant of `ProofObligations`.

## What is already useful

The project already gives a machine-readable proof architecture:

- exact definitions of the centered weighted statistic;
- exact definition of exchangeability as invariance under coordinate
  permutations;
- exact definition of the finite-population inflation factor `Gamma`;
- exact statement of the paper's main theorem as a conditional Lean theorem;
- a checklist of all major lemmas needed to remove the conditional interface.

## Near-term proof tasks

### Projection algebra

```lean
ProofObligations.centeredWeightedSum_eq_dot_proj
ProofObligations.sum_projOnePerp_eq_zero
```

These should be the first serious formalization targets.  They are finite-sum
identities over `Fin N`, and proving them will validate the key centering
translation from the paper.

### Endpoint computation

```lean
Gamma 2 = 2
epsilonBarber 2 = 1
```

Together with:

```lean
lemma_4_6_gamma_eq_barber_two_from_values
```

this gives a small but complete verified endpoint of Lemma 4.6.

### Hamming slice API

The definitions

```lean
sliceSubsets
sliceAverage
elemSym
sliceFunctional
```

are present, but they need supporting lemmas about cardinality, uniform averages,
and elementary symmetric polynomials.

## Research-level obligations

These are mathematically deeper and should probably be formalized after the
finite algebra layer is stable:

- Hoeffding's lemma for bounded mean-zero random variables;
- the Lagrange/Rolle sign lemma;
- the three-coordinate extremizer lemma;
- the two-level reduction on Hamming slices;
- the hypergeometric martingale MGF bound;
- asymptotics and comparison for `Gamma_N`.
