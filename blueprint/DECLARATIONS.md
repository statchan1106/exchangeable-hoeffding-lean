# Paper-to-Lean declaration audit

This page maps the paper's notation and numbered results to the declarations checked by Lean. All unqualified declarations below lie in `SharpSerfling.ExchangeableHoeffding`.

## Notation dictionary

| Paper notation | Lean declaration or expression | Mathematical role |
|---|---|---|
| $\widetilde w$ | `SharpSerfling.FinitePopulation.zeroPad hn w` | extend the first $n$ weights by zero to $N$ coordinates |
| $P_{\mathbf1^\perp}\widetilde w$ | `SharpSerfling.FinitePopulation.centeredWeight hn w` | subtract the average of the padded weights |
| $\lVert P_{\mathbf1^\perp}\widetilde w\rVert_2^2$ | `sqNorm (centeredWeight hn w)` | squared Euclidean norm of the centered weight vector |
| exchangeability | `SharpSerfling.FinitePopulation.IsExchangeableInLaw μ X` | equality of pushforward laws under every coordinate permutation |
| $\mathbb E e^{\lambda\sum_iw_i(X_i-\bar X_N)}$ | `exchangeableMgf μ hn X w lam` | MGF of the centered weighted contrast |
| $\sum_{\ell=N-s}^{N-1}\ell^{-2}$ | `inverseSquareTail N s` | the same finite sum stored in reverse order |
| $B_{N,m}$ | `martingaleFactor N m` | coefficient in the hypergeometric MGF bound |
| $\Gamma_N$ | `Gamma N` | explicit inflation factor |
| $H_N,\epsilon_N$ | `harmonicNumber N`, `barberEpsilon N` | comparison coefficient from the earlier bound |
| $\mathcal V_N$ | `variationalConstant N` | exact hypergeometric variational supremum |

## Numbered results

Paper labels and Lean declaration numbers agree throughout this table.

| Paper item | Lean declaration(s) | Exact formal content |
|---|---|---|
| Theorem 1 | `theorem_1_mgf`, `Gamma_isCoefficient` | logarithmic MGF inequality; also an affine-normalized strengthening over every interval $[a,b]$ |
| One-sided exponential form | `theorem_1_upperTail` | Chernoff bound at an arbitrary positive threshold |
| Corollary 1 | `corollary_1` | confidence-parameter form for $0<\delta<1$, with the necessary hypothesis $P_{\mathbf1^\perp}\widetilde w\ne0$ for the displayed weak-tail event |
| Definition and maximizer of $\Gamma_N$ | `Gamma`, `gammaTerm_mono_step`, `gammaTerm_mono`, `Gamma_eq_lastTerm` | literal finite maximum and proof that it occurs at $s=\lfloor N/2\rfloor$ |
| Parity closed forms | `Gamma_closedForm_even`, `Gamma_closedForm_odd` | the two displayed formulas in Theorem 1 |
| $\Gamma_N=1+3/(2N)+O(N^{-2})$ | `Gamma_even_expansion_bound`, `Gamma_odd_expansion_bound`, `Gamma_asymptotic` | quantitative parity bounds followed by the filter-based big-O statement |
| Lemma 5 | `lemma_5`, `lemma_5_eq_two` | strict inequality for $N\ge3$, equality for $N=2$ |
| Proposition 1 | `varianceLowerConstant`, `varianceLowerConstant_le_exact`, `proposition_1` | parity-dependent lower bound for every valid uniform coefficient |
| Remark 1 | `paperNormalizedLogMgf`, `variationalConstant`, `remark_1_variational` | literal paper normalization and equality with the exact optimal coefficient |
| Lemma 1 | `lemma_1_hoeffding` | Hoeffding's lemma on an arbitrary probability space |
| Lemma 2 | `lemma_2_hermite_sign` | positive Hermite weighted-derivative sum for three ordered roots |
| Lemma 3 | `lemma_3_three_coordinate` | every global constrained maximizer has a repeated coordinate |
| Proposition 2 | `proposition_2_two_level` | existence of a slice-MGF maximizer with at most two coordinate values |
| Lemma 4 | `sampleVarianceFactor_le_martingaleFactor`, `lemma_4_hypergeometric` | centered hypergeometric log-MGF bound with the paper's $B_{N,m}$ |

## Two proof graphs, kept distinct

The mathematical reading order in the paper is

```text
exchangeability → Hamming slice → two-level extremizer
                → hypergeometric MGF → Γ_N → Theorem 1 → Corollary 1
```

Every numbered structural input in this route has a checked Lean declaration.
The final theorem, however, is closed through the stronger
[Sharp Serfling finite-population result](https://github.com/statchan1106/sharp-serfling-lean):

```text
weighted_exchangeable_mgf_centeredNorm_inLaw
  + kappa_le_one
  + Gamma_lower_variance
  → sharpCoefficient_le_Gamma
  → theorem_1_mgf
  → theorem_1_upperTail
  → corollary_1
```

Thus the structural lemmas are not falsely presented as direct kernel
dependencies of `theorem_1_mgf`. They formalize the paper-facing proof
architecture, while the exported theorem uses a shorter, stronger certificate.

The formal main theorem also records coordinate measurability and pointwise
boundedness explicitly. The confidence corollary includes a nonzero projected
weight hypothesis: without it, the weak event at the zero threshold is certain
and cannot be bounded by $\delta<1$.

## Trust boundary

`AxiomAudit.lean` prints the axioms of every public result listed above. The
project additionally scans for `sorry`, `admit`, project-defined axioms,
`unsafe`, and `implemented_by`. The expected trust boundary is exactly the
standard logical foundation reported by Lean/mathlib.
