import Testlean.Exchangeable_Hoeffding_ver2.Basic

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace ExchangeableHoeffding

/-! ## Hypergeometric objects -/

/-- Hypergeometric probability mass function. -/
def hypergeomPMF (N K m r : ℕ) : ℝ :=
  ((Nat.choose K r * Nat.choose (N - K) (m - r)) : ℝ) /
    ((Nat.choose N m) : ℝ)

/-- MGF of the centered hypergeometric count `H - mK/N`. -/
def hypergeomMgf (N K m : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1),
    hypergeomPMF N K m r *
      Real.exp (t * ((r : ℝ) - (m : ℝ) * (K : ℝ) / (N : ℝ)))

/-- The factor `B_{N,m}` from Lemma 4.5. -/
def hypergeomB (N m : ℕ) : ℝ :=
  let s : ℕ := Nat.min m (N - m)
  (((N - s : ℕ) : ℝ) ^ 2) *
    (∑ ℓ ∈ Finset.Icc (N - s) (N - 1), (1 : ℝ) / ((ℓ : ℝ) ^ 2))

/-- Proof obligations for the hypergeometric MGF step. -/
structure HypergeometricProofObligations : Prop where
  lemma_4_1_hoeffding :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Z : Ω → ℝ) (a b θ : ℝ)
      (hmean : (∫ ω, Z ω ∂μ) = 0)
      (hbdd : ∀ᵐ ω ∂μ, a ≤ Z ω ∧ Z ω ≤ b),
      (∫ ω, Real.exp (θ * Z ω) ∂μ) ≤
        Real.exp ((θ ^ 2) * ((b - a) ^ 2) / 8)

  lemma_4_5_hypergeom_mgf :
    ∀ {N K m : ℕ} (hN : 1 ≤ N)
      (hK : K ≤ N) (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) (t : ℝ),
      Real.log (hypergeomMgf N K m t) ≤
        (t ^ 2 / 8) * hypergeomB N m

end ExchangeableHoeffding
