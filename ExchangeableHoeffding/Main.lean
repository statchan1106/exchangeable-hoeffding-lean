import ExchangeableHoeffding.GammaBasic

namespace SharpSerfling.ExchangeableHoeffding

open MeasureTheory
open SharpSerfling.FinitePopulation

/-- The parity-sharp hypergeometric multiplier never exceeds the universal
Hoeffding multiplier. -/
theorem kappa_le_one {N : ℕ} (hN : 2 ≤ N) :
    SharpSerfling.kappa N ≤ 1 := by
  by_cases hEven : Even N
  · rw [SharpSerfling.kappa_of_even hEven]
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨q, hq⟩
    exact SharpSerfling.Hypergeometric.kappa_odd_upper (by omega) ⟨q, hq⟩

/-- The exact coefficient already proved in the Sharp-Serfling development is
bounded by the explicit `Γ_N` used in Theorem 1. -/
theorem sharpCoefficient_le_Gamma {N : ℕ} (hN : 2 ≤ N) :
    SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) ≤ Gamma N := by
  have hratio : 0 ≤ (N : ℝ) / ((N : ℝ) - 1) := by
    have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
      exact sub_pos.mpr (by exact_mod_cast (show 1 < N by omega))
    positivity
  calc
    SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) =
        SharpSerfling.kappa N * ((N : ℝ) / ((N : ℝ) - 1)) := by ring
    _ ≤ 1 * ((N : ℝ) / ((N : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right (kappa_le_one hN) hratio
    _ = (N : ℝ) / ((N : ℝ) - 1) := one_mul _
    _ ≤ Gamma N := Gamma_lower_variance hN

/-- **Theorem 1 (MGF statement).**  This uses the standard
equality-of-pushforward-laws definition of finite exchangeability.  The
zero-padded and centered weight vector is `centeredWeight hn w`. -/
theorem theorem_1_mgf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ}
    (hN : 2 ≤ N) (hn : n ≤ N) (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, (-1 : ℝ) ≤ X ω j ∧ X ω j ≤ 1)
    (hEx : IsExchangeableInLaw μ X) (w : Fin n → ℝ) (lam : ℝ) :
    Real.log (exchangeableMgf μ hn X w lam) ≤
      lam ^ 2 / 2 * Gamma N * sqNorm (centeredWeight hn w) := by
  have hsharp := weighted_exchangeable_mgf_centeredNorm_inLaw
    μ hN hn X hXmeas hX hEx w lam
  have hcoeff := sharpCoefficient_le_Gamma hN
  calc
    Real.log (exchangeableMgf μ hn X w lam) ≤
        lam ^ 2 * ((1 : ℝ) - (-1 : ℝ)) ^ 2 / 8 *
          (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
            sqNorm (centeredWeight hn w) := hsharp
    _ = lam ^ 2 / 2 *
          (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
            sqNorm (centeredWeight hn w) := by ring
    _ ≤ lam ^ 2 / 2 * Gamma N * sqNorm (centeredWeight hn w) := by
      gcongr
      exact sqNorm_nonneg _

/-- The exponential one-sided tail form obtained from Theorem 1. -/
theorem theorem_1_upperTail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ}
    (hN : 2 ≤ N) (hn : n ≤ N) (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, (-1 : ℝ) ≤ X ω j ∧ X ω j ≤ 1)
    (hEx : IsExchangeableInLaw μ X) (w : Fin n → ℝ)
    (hw : centeredWeight hn w ≠ fun _ ↦ 0) {u : ℝ} (hu : 0 < u) :
    exchangeableUpperTail μ hn X w u ≤
      Real.exp (-u ^ 2 /
        (2 * Gamma N * sqNorm (centeredWeight hn w))) := by
  have htail := weighted_exchangeable_tail_inLaw
    μ hN hn X hXmeas hX hEx w hw hu
  have hsharpPos : 0 <
      SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) := by
    have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
      exact sub_pos.mpr (by exact_mod_cast (show 1 < N by omega))
    exact div_pos (mul_pos (SharpSerfling.kappa_pos hN) (by positivity)) hNm1
  have hnormPos : 0 < sqNorm (centeredWeight hn w) :=
    sqNorm_pos_of_ne_zero hw
  have hdenSharp : 0 <
      2 * (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
        sqNorm (centeredWeight hn w) := by positivity
  have hdenGamma : 0 <
      2 * Gamma N * sqNorm (centeredWeight hn w) := by
    exact mul_pos (mul_pos (by norm_num) (Gamma_pos hN)) hnormPos
  have hdenLe :
      2 * (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
          sqNorm (centeredWeight hn w) ≤
        2 * Gamma N * sqNorm (centeredWeight hn w) := by
    gcongr
    exact sharpCoefficient_le_Gamma hN
  calc
    exchangeableUpperTail μ hn X w u ≤
        Real.exp (-2 * u ^ 2 /
          (((1 : ℝ) - (-1 : ℝ)) ^ 2 *
            (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
              sqNorm (centeredWeight hn w))) := htail
    _ = Real.exp (-u ^ 2 /
          (2 * (SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1)) *
            sqNorm (centeredWeight hn w))) := by congr 1 <;> ring
    _ ≤ Real.exp (-u ^ 2 /
          (2 * Gamma N * sqNorm (centeredWeight hn w))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg u) hdenSharp hdenLe

/-- **Corollary 1.**  The paper's confidence-parameter form of the
one-sided tail bound. -/
theorem corollary_1
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N n : ℕ}
    (hN : 2 ≤ N) (hn : n ≤ N) (X : Ω → Fin N → ℝ)
    (hXmeas : ∀ j, StronglyMeasurable (fun ω ↦ X ω j))
    (hX : ∀ ω j, (-1 : ℝ) ≤ X ω j ∧ X ω j ≤ 1)
    (hEx : IsExchangeableInLaw μ X) (w : Fin n → ℝ)
    (hw : centeredWeight hn w ≠ fun _ ↦ 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    exchangeableUpperTail μ hn X w
        (Real.sqrt (sqNorm (centeredWeight hn w)) *
          Real.sqrt (2 * Gamma N * Real.log (1 / δ))) ≤ δ := by
  have hnormPos : 0 < sqNorm (centeredWeight hn w) :=
    sqNorm_pos_of_ne_zero hw
  have hratio : 1 < (1 : ℝ) / δ := by
    rw [one_lt_div hδ0]
    exact hδ1
  have hlog : 0 < Real.log ((1 : ℝ) / δ) := Real.log_pos hratio
  have hfactor : 0 < 2 * Gamma N * Real.log ((1 : ℝ) / δ) := by
    exact mul_pos (mul_pos (by norm_num) (Gamma_pos hN)) hlog
  let u := Real.sqrt (sqNorm (centeredWeight hn w)) *
    Real.sqrt (2 * Gamma N * Real.log (1 / δ))
  have hu : 0 < u := by
    dsimp [u]
    exact mul_pos (Real.sqrt_pos.2 hnormPos) (Real.sqrt_pos.2 hfactor)
  have htail := theorem_1_upperTail
    μ hN hn X hXmeas hX hEx w hw hu
  have huSq : u ^ 2 = sqNorm (centeredWeight hn w) *
      (2 * Gamma N * Real.log (1 / δ)) := by
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt hnormPos.le, Real.sq_sqrt hfactor.le]
  have hden : 0 < 2 * Gamma N * sqNorm (centeredWeight hn w) := by
    exact mul_pos (mul_pos (by norm_num) (Gamma_pos hN)) hnormPos
  calc
    exchangeableUpperTail μ hn X w u ≤
        Real.exp (-u ^ 2 /
          (2 * Gamma N * sqNorm (centeredWeight hn w))) := htail
    _ = Real.exp (-Real.log (1 / δ)) := by
      congr 1
      rw [huSq]
      field_simp [ne_of_gt (Gamma_pos hN), ne_of_gt hnormPos]
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < (1 : ℝ) / δ)]
      field_simp

end SharpSerfling.ExchangeableHoeffding
