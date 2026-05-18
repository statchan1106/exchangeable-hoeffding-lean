# Exchangeable Hoeffding in Lean 4

This repository hosts a Lean 4 companion project for Seongchan Lee and Ilmun
Kim, *A Sharper Hoeffding Bound for Weighted Sums of Exchangeable Random
Variables*.

The project explores how Lean can make the structure of a modern statistical
proof explicit.  The current Lean development avoids global axioms: the hard
mathematical ingredients are collected in an explicit interface,
`ExchangeableHoeffding.ProofObligations`, and the main theorem is derived
conditionally from that interface.

## Blueprint Site

GitHub Pages:

https://statchan1106.github.io/exchangeable-hoeffding-lean/

The static preview source is in:

```text
testlean/blueprint/web/index.html
```

The Lean blueprint source is in:

```text
testlean/blueprint/src/content.tex
```

## Lean Entry Point

```lean
import Testlean.ExchangeableHoeffding.NoGlobalAxioms
```

Core theorem:

```lean
ExchangeableHoeffding.theorem_2_1
```

## Current Status

The project currently provides:

- Lean definitions for exchangeability, boundedness, centering, projection, and
  the finite-population inflation factor `Gamma`;
- a no-global-axiom proof-obligation interface;
- a conditional Lean statement of the main exchangeable Hoeffding MGF bound;
- a blueprint-style web page mapping paper statements to Lean names.
