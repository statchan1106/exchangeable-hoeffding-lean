import Testlean.ExchangeableHoeffding.Basic

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace ExchangeableHoeffding

/-! ## Hypergeometric sampling objects -/

/-- Hypergeometric probability mass function. -/
def hypergeomPMF (N K m r : ℕ) : ℝ :=
  ((Nat.choose K r * Nat.choose (N - K) (m - r)) : ℝ) /
    ((Nat.choose N m) : ℝ)

/-- Moment generating function of the centered hypergeometric count. -/
def hypergeomMgf (N K m : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1),
    hypergeomPMF N K m r *
      Real.exp (t * ((r : ℝ) - (m : ℝ) * (K : ℝ) / (N : ℝ)))

/-- The finite-sampling factor used by the hypergeometric MGF estimate. -/
def hypergeomB (N m : ℕ) : ℝ :=
  let s : ℕ := Nat.min m (N - m)
  (((N - s : ℕ) : ℝ) ^ 2) *
    (∑ ℓ ∈ Finset.Icc (N - s) (N - 1), (1 : ℝ) / ((ℓ : ℝ) ^ 2))

/-- Hoeffding's lemma in the exact normalization used by the sampling argument.

The measurability hypothesis is explicit here.  In the paper it is part of the
usual phrase “real random variable”; spelling it out prevents a hidden analytic
assumption from entering the formal statement. -/
theorem bounded_centered_mgf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (a b t : ℝ)
    (hmeas : AEMeasurable Z μ)
    (hmean : (∫ ω, Z ω ∂μ) = 0)
    (hbdd : ∀ᵐ ω ∂μ, a ≤ Z ω ∧ Z ω ≤ b) :
    (∫ ω, Real.exp (t * Z ω) ∂μ) ≤
      Real.exp ((t ^ 2) * ((b - a) ^ 2) / 8) := by
  have hsubgaussian :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hmeas (by simpa [Set.mem_Icc] using hbdd) hmean
  change ProbabilityTheory.mgf Z μ t ≤ _
  calc
    _ ≤ Real.exp
        ((↑(((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ) * t ^ 2 / 2) :=
      hsubgaussian.mgf_le t
    _ = Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
      congr 1
      simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm]
      rw [Real.norm_eq_abs, div_pow, sq_abs]
      norm_num
      ring

/-- The genuinely project-specific analytic input still required for the
hypergeometric sampling-without-replacement argument. -/
structure HypergeometricAnalyticInputs : Prop where

  hypergeometric_mgf_bound :
    ∀ {N K m : ℕ} (hN : 1 ≤ N)
      (hK : K ≤ N) (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) (t : ℝ),
      Real.log (hypergeomMgf N K m t) ≤
        (t ^ 2 / 8) * hypergeomB N m

end ExchangeableHoeffding
