import ExchangeableHoeffding.Hypergeometric

namespace SharpSerfling.ExchangeableHoeffding

open MeasureTheory ProbabilityTheory
open SharpSerfling.FinitePopulation

/-- **Lemma 4.1 (Hoeffding's lemma).**  Integral form on an arbitrary
probability space. -/
theorem lemma_4_1_hoeffding
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hZmeas : AEMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, Z ω ∈ Set.Icc a b)
    (hmean : ∫ ω, Z ω ∂μ = 0) (theta : ℝ) :
    (∫ ω, Real.exp (theta * Z ω) ∂μ) ≤
      Real.exp (theta ^ 2 * (b - a) ^ 2 / 8) := by
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := Z) hZmeas hZ hmean
  have hbound := hsub.mgf_le theta
  rw [ProbabilityTheory.mgf] at hbound
  convert hbound using 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat]
  rw [Real.nnnorm_of_nonneg (sub_nonneg.mpr hab)]
  simp only [NNReal.coe_mk]
  ring

/-- **Lemma 4.2 (Hermite sign lemma),** with the three distinct nodes
written in increasing order (the paper's unordered statement is obtained by
relabeling). -/
theorem lemma_4_2_hermite_sign {h : ℝ → ℝ} (hh : ContDiff ℝ 5 h)
    {x₁ x₂ x₃ : ℝ} (h12 : x₁ < x₂) (h23 : x₂ < x₃)
    (hz1 : h x₁ = 0) (hz2 : h x₂ = 0) (hz3 : h x₃ = 0)
    (hfive : ∀ x, 0 < iteratedDeriv 5 h x) :
    0 < deriv h x₁ / (((x₁ - x₂) * (x₁ - x₃)) ^ 2) +
      deriv h x₂ / (((x₂ - x₁) * (x₂ - x₃)) ^ 2) +
      deriv h x₃ / (((x₃ - x₁) * (x₃ - x₂)) ^ 2) := by
  exact SharpSerfling.Analysis.hermite_weighted_deriv_pos
    hh h12 h23 hz1 hz2 hz3 hfive

/-- **Lemma 4.3 (three-coordinate section), strict/maximizer form.**
Every global maximizer supplied to the theorem has two equal coordinates;
the underlying result also proves that three distinct coordinates cannot be
a maximizer. -/
theorem lemma_4_3_three_coordinate
    {A B x₁ x₂ x₃ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : 0 < A + B)
    (hmax : ∀ u v z : ℝ,
      u + v + z = x₁ + x₂ + x₃ →
      u ^ 2 + v ^ 2 + z ^ 2 = x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 →
      SharpSerfling.Analysis.expPair A B u +
          SharpSerfling.Analysis.expPair A B v +
          SharpSerfling.Analysis.expPair A B z ≤
        SharpSerfling.Analysis.expPair A B x₁ +
          SharpSerfling.Analysis.expPair A B x₂ +
          SharpSerfling.Analysis.expPair A B x₃) :
    x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃ := by
  exact SharpSerfling.Analysis.threePoint_globalMax_has_duplicate
    hA hB hAB hmax

/-- **Proposition 4.4 (two-level maximizer).**  `sliceMgf` is the
elementary-symmetric exponential mean; taking `Real.log` does not change its
maximizers because it is positive and strictly increasing. -/
theorem proposition_4_4_two_level
    {N K : ℕ} (hN : 2 ≤ N) (hK0 : 1 ≤ K) (hKN : K ≤ N - 1)
    {rhoSq : ℝ} (hrho : 0 ≤ rhoSq) {y : Fin N → ℝ}
    (hy : y ∈ centeredSphere N rhoSq) :
    ∃ z ∈ centeredSphere N rhoSq,
      (∀ x ∈ centeredSphere N rhoSq, sliceMgf N K x ≤ sliceMgf N K z) ∧
        HasAtMostTwoValues z := by
  exact exists_twoLevel_sliceMgf_maximizer hN hK0 hKN hrho hy

end SharpSerfling.ExchangeableHoeffding
