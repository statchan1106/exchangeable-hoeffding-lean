import ExchangeableHoeffding.Main
import ExchangeableHoeffding.GammaClosedForm

namespace SharpSerfling.ExchangeableHoeffding

open SharpSerfling.FinitePopulation

/-- Coefficient predicate for the paper's affine-invariant bounded-range
normalization.  Specializing `a=-1`, `b=1` gives exactly the statement of
Theorem 1. -/
def ExchangeableHoeffdingCoefficient (N : ℕ) (C : ℝ) : Prop :=
  ExchangeableInLawCoefficient N C

/-- `Γ_N` is a valid coefficient, now stated uniformly over every interval
`[a,b]`; this is the affine-normalized strengthening of Theorem 1. -/
theorem Gamma_isCoefficient {N : ℕ} (hN : 2 ≤ N) :
    ExchangeableHoeffdingCoefficient N (Gamma N) := by
  intro Ω mΩ μ hμ n hn a b X hXmeas hX hEx w lam
  have hsharp := weighted_exchangeable_mgf_centeredNorm_inLaw
    μ hN hn X hXmeas hX hEx w lam
  have hcoeff := sharpCoefficient_le_Gamma hN
  calc
    Real.log (exchangeableMgf μ hn X w lam) ≤
        lam ^ 2 * (b - a) ^ 2 / 8 *
          (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
            sqNorm (centeredWeight hn w) := hsharp
    _ ≤ lam ^ 2 * (b - a) ^ 2 / 8 * Gamma N *
          sqNorm (centeredWeight hn w) := by
      gcongr
      exact sqNorm_nonneg _

/-- The exact optimal coefficient supplied by the stronger Sharp-Serfling
development. -/
theorem optimalCoefficient_exact {N : ℕ} (hN : 2 ≤ N) :
    ExchangeableHoeffdingCoefficient N
        (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) ∧
      ∀ C : ℝ, ExchangeableHoeffdingCoefficient N C →
        SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) ≤ C := by
  exact exchangeableInLaw_Cstar_sharp_constant hN

theorem varianceLowerConstant_le_exact {N : ℕ} (hN : 2 ≤ N) :
    varianceLowerConstant N ≤
      SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) := by
  by_cases hEven : Even N
  · rw [varianceLowerConstant, if_pos hEven,
      SharpSerfling.kappa_of_even hEven, one_mul]
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    have hN3 : 3 ≤ N := by
      rcases hOdd with ⟨q, hq⟩
      omega
    have hk := SharpSerfling.Hypergeometric.kappa_odd_lower hN3 hOdd
    have hNR : (0 : ℝ) < (N : ℝ) := by positivity
    have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
      exact sub_pos.mpr (by exact_mod_cast (show 1 < N by omega))
    rw [varianceLowerConstant, if_neg hEven]
    calc
      ((N : ℝ) + 1) / (N : ℝ) ≤
          (1 - 1 / (2 * (N : ℝ) ^ 2)) * (N : ℝ) /
            ((N : ℝ) - 1) := by
        rw [div_le_div_iff₀ hNR hNm1]
        field_simp [ne_of_gt hNR]
        nlinarith [sq_nonneg ((N : ℝ) - 2)]
      _ ≤ SharpSerfling.kappa N * (N : ℝ) /
          ((N : ℝ) - 1) := by
        apply div_le_div_of_nonneg_right _ hNm1.le
        exact mul_le_mul_of_nonneg_right hk hNR.le

/-- **Proposition 1.**  Every coefficient valid uniformly for bounded
exchangeable laws obeys the parity-dependent variance lower bound. -/
theorem proposition_1 {N : ℕ} (hN : 2 ≤ N) {C : ℝ}
    (hC : ExchangeableHoeffdingCoefficient N C) :
    varianceLowerConstant N ≤ C := by
  exact (varianceLowerConstant_le_exact hN).trans
    ((optimalCoefficient_exact hN).2 C hC)

end SharpSerfling.ExchangeableHoeffding
