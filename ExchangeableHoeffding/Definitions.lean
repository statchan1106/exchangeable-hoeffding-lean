import SharpSerfling.FinitePopulation.OptimalityLaw
import SharpSerfling.Hypergeometric.Variational

namespace SharpSerfling.ExchangeableHoeffding

open scoped BigOperators

/-- The inverse-square tail appearing in Lemma 4, indexed from the
right endpoint: `j = 0` is the term `(N-1)⁻²`. -/
noncomputable def inverseSquareTail (N s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range s, 1 / (((N - 1 - j : ℕ) : ℝ) ^ 2)

/-- The martingale coefficient `B_{N,m}` of Lemma 4. -/
noncomputable def martingaleFactor (N m : ℕ) : ℝ :=
  let s := min m (N - m)
  ((N - s : ℕ) : ℝ) ^ 2 * inverseSquareTail N s

/-- A single term in the finite maximization defining `Γ_N`. -/
noncomputable def gammaTerm (N s : ℕ) : ℝ :=
  (N : ℝ) * (N - s : ℕ) / (s : ℝ) * inverseSquareTail N s

/-- The inflation factor `Γ_N` from Theorem 1, as its literal finite
maximum over `1 ≤ s ≤ floor(N/2)`.  It is set to zero outside `N ≥ 2`. -/
noncomputable def Gamma (N : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    (Finset.Icc 1 (N / 2)).sup'
      (by
        refine ⟨1, ?_⟩
        simp
        omega)
      (gammaTerm N)
  else 0

/-- Barber's harmonic number `H_N`. -/
noncomputable def harmonicNumber (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, 1 / ((j + 1 : ℕ) : ℝ)

/-- Barber's inflation excess `ε_N = (H_N-1)/(N-H_N)`. -/
noncomputable def barberEpsilon (N : ℕ) : ℝ :=
  (harmonicNumber N - 1) / ((N : ℝ) - harmonicNumber N)

/-- The parity-dependent variance lower bound from Proposition 1. -/
noncomputable def varianceLowerConstant (N : ℕ) : ℝ :=
  if Even N then (N : ℝ) / ((N : ℝ) - 1)
  else ((N : ℝ) + 1) / (N : ℝ)

/-- The normalized log-MGF ratio used in Remark 1. -/
noncomputable def paperNormalizedLogMgf (N K m : ℕ) (t : ℝ) : ℝ :=
  8 * (N : ℝ) * Real.log (Hypergeometric.mgf N K m t) /
    (((m : ℝ) * ((N : ℝ) - (m : ℝ))) * t ^ 2)

/-- The literal set of ratios in the hypergeometric optimization of Remark 1. -/
def paperVariationalValues (N : ℕ) : Set ℝ :=
  {x | ∃ K m : ℕ, 1 ≤ K ∧ K ≤ N - 1 ∧ 1 ≤ m ∧ m ≤ N - 1 ∧
      ∃ t : ℝ, t ≠ 0 ∧ x = paperNormalizedLogMgf N K m t}

/-- The variational constant `V_N` of Remark 1. -/
noncomputable def variationalConstant (N : ℕ) : ℝ :=
  sSup (paperVariationalValues N)

end SharpSerfling.ExchangeableHoeffding
