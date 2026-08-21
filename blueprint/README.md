# Proof blueprint

This document follows the labels printed in the paper: Theorem 1, Corollary 1,
Proposition 1, Remark 1, Lemmas 1--5, Proposition 2, and equations (1)--(2).
The corresponding Lean declarations use the same result numbers.

## What the theorem says

Let $X_1,\ldots,X_N\in[-1,1]$ be exchangeable and write

$$
\bar X_N=\frac1N\sum_{j=1}^N X_j,
\qquad
\widetilde w=(w_1,\ldots,w_n,0,\ldots,0)\in\mathbb R^N.
$$

The relevant part of the weights is their projection away from the constant
direction,

$$
P_{\mathbf1^\perp}\widetilde w
=\widetilde w-\frac{\mathbf1^\top\widetilde w}{N}\mathbf1.
$$

The declaration `centeredWeight hn w` is exactly this vector, while
`sqNorm (centeredWeight hn w)` is its squared Euclidean norm. The main theorem
`theorem_1_mgf` proves

$$
\log \mathbb E\exp\!\left\{
\lambda\sum_{i=1}^n w_i(X_i-\bar X_N)
\right\}
\le
\frac{\lambda^2}{2}\Gamma_N
\lVert P_{\mathbf1^\perp}\widetilde w\rVert_2^2.
\tag{Theorem 1}
$$

Because the MGF is positive, this logarithmic statement is equivalent to the
exponential display in the paper.

## The explicit inflation factor

The reverse-indexed finite sum is

$$
\operatorname{inverseSquareTail}(N,s)
=\sum_{j=0}^{s-1}\frac1{(N-1-j)^2}
=\sum_{\ell=N-s}^{N-1}\frac1{\ell^2}.
$$

The declarations `gammaTerm` and `Gamma` literally encode

$$
\gamma_{N,s}
=\frac{N(N-s)}s\sum_{\ell=N-s}^{N-1}\frac1{\ell^2},
\qquad
\Gamma_N=\max_{1\le s\le\lfloor N/2\rfloor}\gamma_{N,s}.
$$

The chain

```text
inverseSquareTail_upper_half
  → inverseSquareTail_upper_for_monotonicity
  → gammaTerm_mono_step
  → gammaTerm_mono
  → Gamma_eq_lastTerm
```

proves that the maximum occurs at $s=\lfloor N/2\rfloor$. The declarations
`Gamma_closedForm_even` and `Gamma_closedForm_odd` then give

$$
\Gamma_N=
\begin{cases}
N\displaystyle\sum_{\ell=N/2}^{N-1}\ell^{-2},
&N\text{ even},\\[1.1em]
\dfrac{N(N+1)}{N-1}
\displaystyle\sum_{\ell=(N+1)/2}^{N-1}\ell^{-2},
&N\text{ odd}.
\end{cases}
\tag{Γ}
$$

Finally, `Gamma_asymptotic` states in filter notation that

$$
\Gamma_N=1+\frac{3}{2N}+O(N^{-2}).
$$

It is supported by explicit bounds on the even and odd subsequences, not by an
informal appeal to a Taylor expansion.

## Paper proof: the recommended reading order

### 1. Symmetry removes the ambient probability law

`IsExchangeableInLaw μ X` says that every coordinate permutation has the same
pushforward law. After centering the weights, the problem becomes a symmetric
finite-population MGF problem. This is the formal counterpart of the first
reduction in Section 3.

### 2. Cube extremizers become Hamming slices

Convexity reduces the bounded population to sign vectors. Conditioning on the
number $k$ of positive signs produces a uniform $k$-subset $S_k$. The
paper's central slice estimate is

$$
\log\mathbb E_{S_k}
\exp\!\left\{\sum_{i\in S_k}y_i\right\}
\le \frac{\Gamma_N}{8}\lVert y\rVert_2^2,
\qquad \sum_{i=1}^Ny_i=0.
\tag{1}
$$

The finite exponential subset average is represented by `sliceMgf N K y`.

### 3. A high-dimensional extremizer has two levels

The paper's Lemma 2 is certified by `lemma_2_hermite_sign`; it proves the
positive derivative identity used to rule out a three-distinct-coordinate
local maximum. Paper Lemma 3 is certified by
`lemma_3_three_coordinate`, which packages the constrained
three-coordinate conclusion. Paper Proposition 2 is certified by
`proposition_2_two_level`, giving a global maximizer on

$$
\left\{y\in\mathbb R^N:
\sum_i y_i=0,\ \lVert y\rVert_2^2=\rho^2\right\}
$$

with at most two coordinate values.

If the first value occurs $m$ times and $d=\alpha-\beta$, centering and the
radius constraint force

$$
\alpha=\frac{N-m}{N}d,
\qquad
\beta=-\frac mN d,
\qquad
d^2=\rho^2\frac{N}{m(N-m)}.
\tag{2}
$$

### 4. The two-level problem is hypergeometric

For a uniform $k$-subset, let

$$
H=|S_k\cap A|\sim\operatorname{Hypergeometric}(N,k,m),
\qquad \mathbb EH=\frac{km}{N}.
$$

The subset sum becomes $d(H-km/N)$. With
$s=m\wedge(N-m)$, `martingaleFactor N m` is

$$
B_{N,m}=(N-s)^2\sum_{\ell=N-s}^{N-1}\ell^{-2}.
$$

The paper's Lemma 4 is certified by `lemma_4_hypergeometric`, which proves

$$
\log\mathbb E e^{t(H-km/N)}
\le \frac{t^2}{8}B_{N,m}.
\tag{Lemma 4}
$$

Together with (2) and the definition of $\Gamma_N$, this is the
one-dimensional estimate that closes the paper's slice argument.

### 5. Chernoff optimization gives the confidence bound

`theorem_1_upperTail` proves the arbitrary-threshold form

$$
\Pr\{Y\ge u\}
\le \exp\!\left\{-\frac{u^2}
{2\Gamma_N\lVert P_{\mathbf1^\perp}\widetilde w\rVert_2^2}\right\}.
$$

Substituting

$$
u=\lVert P_{\mathbf1^\perp}\widetilde w\rVert_2
\sqrt{2\Gamma_N\log(1/\delta)}
$$

gives `corollary_1`.

The checked confidence statement assumes
$P_{\mathbf1^\perp}\widetilde w\ne0$. This is a necessary guard for the
paper's displayed weak inequality: if the projected weight is zero, the event
at the zero threshold is $\{0\ge0\}$, which has probability one. Replacing
the event by a strict upper tail would make the degenerate case automatic.

## Actual kernel dependency of the main theorem

The formal development also contains a stronger exact coefficient
$\kappa_NN/(N-1)$. The exported Theorem 1 is closed through that result:

```text
weighted_exchangeable_mgf_centeredNorm_inLaw
      │
      ├── kappa_le_one
      └── Gamma_lower_variance
              │
              ▼
      sharpCoefficient_le_Gamma
              │
              ▼
        theorem_1_mgf
              │
              ▼
     theorem_1_upperTail
              │
              ▼
         corollary_1
```

This is intentionally distinguished from the paper's explanatory route. The
numbered Section 4 lemmas are all formalized, but they are not claimed to be
direct kernel dependencies of `theorem_1_mgf`. The stronger certificate
compresses the final proof while preserving the literal paper statements as
independently checked interfaces.

## Rate optimality and the exact variational constant

Define $C_N^\star$ to be the smallest coefficient that works uniformly.
Paper Proposition 1 is certified by `proposition_1`, which proves

$$
C_N^\star\ge
\begin{cases}
\dfrac N{N-1},&N\text{ even},\\[0.8em]
\dfrac{N+1}{N},&N\text{ odd}.
\end{cases}
$$

The exact variational quantity is encoded literally by
`paperNormalizedLogMgf`, `paperVariationalValues`, and `variationalConstant`:

$$
\mathcal V_N=
\max_{\substack{1\le k\le N-1\\1\le m\le N-1}}
\frac{8N}{m(N-m)}
\sup_{t\ne0}\frac{\psi_{N,k,m}(t)}{t^2},
$$

where

$$
\psi_{N,k,m}(t)
=\log\mathbb E\exp\!\left\{
t\left(H_{N,k,m}-\frac{km}{N}\right)\right\}.
$$

Paper Remark 1 is certified by `remark_1_variational`, which identifies
$\mathcal V_N$ with the exact optimal coefficient. The proof treats odd
populations by an explicit nonzero tilt and even populations by the small-tilt
limit.

## Comparison with the earlier coefficient

With

$$
H_N=\sum_{j=1}^N\frac1j,
\qquad
\epsilon_N=\frac{H_N-1}{N-H_N},
$$

Paper Lemma 5 is certified by `lemma_5`, which proves
$\Gamma_N<1+\epsilon_N$ for $N\ge3$, and by `lemma_5_eq_two`, which
proves equality at $N=2$. The formal proof uses a
half-integer telescoping estimate for the inverse-square tail, splits by
parity, handles the stable range algebraically, and checks the remaining
finite cases exactly.

## Three useful reading passes

1. **Statement pass:** `centeredWeight` → `Gamma` → `theorem_1_mgf` →
   `corollary_1`.
2. **Mechanism pass:** `lemma_1_hoeffding` → `lemma_2_hermite_sign` →
   `lemma_3_three_coordinate` → `proposition_2_two_level` →
   `lemma_4_hypergeometric`.
3. **Sharpness pass:** `Gamma_eq_lastTerm` → parity closed forms →
   `Gamma_asymptotic` → `lemma_5` → `proposition_1` →
   `remark_1_variational`.

## Verification boundary

The project checks all exported paper declarations with the kernel and prints
their axioms. It also searches for proof placeholders and unsafe escape
hatches. The expected audit contains no project-defined axiom and reports only
the standard logical foundations inherited from Lean/mathlib.
