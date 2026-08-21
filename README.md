# A sharper Hoeffding bound for exchangeable random variables

This repository contains a kernel-checked formalization of the paper
[*A Sharper Hoeffding Bound for Weighted Sums of Exchangeable Random Variables*](https://arxiv.org/abs/2608.04900)
by [Seongchan Lee](https://statchan1106.github.io/) and
[Ilmun Kim](https://ilmunk.github.io/index.html).

The formal development covers the main moment-generating-function inequality,
its confidence form, the explicit inflation factor and its closed forms, the
comparison with the earlier harmonic-number coefficient, the rate lower bound,
the exact variational characterization, and the structural lemmas used in the
paper.

## Start here

- [Project blueprint](BLUEPRINT.md) explains the mathematics, the declaration
  hierarchy, and the exact paper-to-Lean correspondence.
- [Project-page overview](docs/index.html) gives the theorem, its meaning, and
  the paper's three proof steps without technical overload.
- [Proof blueprint](docs/proof.html) follows the paper's three-step argument,
  displays its dependency graph, and pairs each proof move with a Lean
  certificate.
- [Declaration map](docs/declarations.html) is a searchable dictionary from
  mathematical roles to formal declaration names.
- [Declaration audit](TRACEABILITY.md) is the compact theorem-by-theorem
  checklist.

The public exposition is organized by declaration names and mathematical
roles, so readers do not need to know the source layout in advance.

## Main formal statement

For a bounded exchangeable vector \(X=(X_1,\ldots,X_N)\in[-1,1]^N\), weights
\(w\in\mathbb R^n\), and the centered zero-padded vector
\(P_{\mathbf 1^\perp}\widetilde w\), the declaration `theorem_2_1_mgf`
establishes the logarithmic form

\[
\log \mathbb E\exp\!\left\{\lambda\sum_{i=1}^n
w_i(X_i-\bar X_N)\right\}
\le \frac{\lambda^2}{2}\,\Gamma_N
\left\|P_{\mathbf 1^\perp}\widetilde w\right\|_2^2.
\]

The declaration `corollary_2_2` gives the corresponding confidence bound.

## Build and trust audit

From the project root:

```sh
lake build
lake env lean AxiomAudit.lean
rg -n '\b(sorry|admit)\b|^\s*axiom\b|\b(unsafe|implemented_by)\b' . \
  --glob '*.lean' --glob '!**/.lake/**'
```

The axiom audit is designed to expose the logical assumptions of every public
paper result. The expected output contains only Lean/mathlib's standard logical
foundations: `propext`, `Classical.choice`, and `Quot.sound`.

## Formalization architecture

Paper-specific declarations use the namespace
`SharpSerfling.ExchangeableHoeffding`. The project also reuses a neighboring,
kernel-checked foundation for finite-population symmetrization,
hypergeometric MGFs, two-level reduction, and exact optimal constants. The
blueprint explicitly distinguishes the paper's mathematical reading order from
the shorter dependency path used by the final Lean theorem.
