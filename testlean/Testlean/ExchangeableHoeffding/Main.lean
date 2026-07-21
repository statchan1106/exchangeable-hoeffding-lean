import Testlean.ExchangeableHoeffding.Basic
import Testlean.ExchangeableHoeffding.Gamma
import Testlean.ExchangeableHoeffding.HammingSlice
import Testlean.ExchangeableHoeffding.Hypergeometric
import Testlean.ExchangeableHoeffding.ThreePoint

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace ExchangeableHoeffding

/-! ## Main bounds and sharpness objects -/

/-- A constant is admissible when it uniformly gives the target MGF estimate. -/
def AdmissibleConstant (N : ℕ) (C : ℝ) : Prop :=
  ∀ (n : ℕ) (hn : n ≤ N) (μ : Measure (Fin N → ℝ)),
    IsProbabilityMeasure μ → Exchangeable μ → BoundedByOne μ →
      ∀ (w : Fin n → ℝ) (lam : ℝ),
        (∫ x, Real.exp (lam * centeredWeightedSum hn w x) ∂μ) ≤
          Real.exp (((lam ^ 2) / 2) * C * normSq (projOnePerp (zeroPad hn w)))

/-- The universal lower bound for an admissible replacement constant. -/
def optimalLowerBound (N : ℕ) : ℝ :=
  if Even N then (N : ℝ) / ((N - 1 : ℕ) : ℝ)
  else ((N + 1 : ℕ) : ℝ) / (N : ℝ)

/-- Euclidean norm derived from the squared norm. -/
def l2Norm {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  Real.sqrt (normSq a)

/-- The threshold in the one-sided concentration estimate. -/
def tailThreshold {n N : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) (δ : ℝ) : ℝ :=
  l2Norm (projOnePerp (zeroPad hn w)) *
    Real.sqrt (2 * Gamma N * Real.log (1 / δ))

/-- Bounded coordinates make every exponential linear statistic integrable. -/
lemma integrable_exp_mul_dot_of_bounded {N : ℕ}
    (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ] (hBd : BoundedByOne μ)
    (a : Fin N → ℝ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * dot a x)) μ := by
  refine ProbabilityTheory.integrable_exp_mul_of_mem_Icc
    (a := -(∑ i : Fin N, |a i|)) (b := ∑ i : Fin N, |a i|)
    (measurable_dot a).aemeasurable ?_
  filter_upwards [hBd] with x hx
  have habs := abs_dot_le_sum_abs a x hx
  exact (abs_le.mp habs)

/-- Analytic inputs still required to close the main probability argument. -/
structure MainAnalyticInputs : Prop where
  zero_sum_mgf_bound :
    ∀ {N : ℕ} (hN : 2 ≤ N)
      (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
      (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
      (a : Fin N → ℝ) (ha : ∑ i : Fin N, a i = 0) (lam : ℝ),
      (∫ x, Real.exp (lam * dot a x) ∂μ) ≤
        Real.exp (((lam ^ 2) / 2) * Gamma N * normSq a)

  admissible_constant_bound :
    ∀ {N : ℕ} (hN : 2 ≤ N) {C : ℝ}
      (hC : AdmissibleConstant N C), optimalLowerBound N ≤ C

/-- The centered exchangeable MGF estimate follows from its zero-sum form. -/
theorem exchangeable_mgf_bound (H : MainAnalyticInputs)
    {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
    (w : Fin n → ℝ) (lam : ℝ) :
    (∫ x, Real.exp (lam * centeredWeightedSum hn w x) ∂μ) ≤
      Real.exp (((lam ^ 2) / 2) * Gamma N * normSq (projOnePerp (zeroPad hn w))) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hN
  have hsum : ∑ i : Fin N, projOnePerp (zeroPad hn w) i = 0 :=
    sum_projOnePerp_eq_zero hNpos (zeroPad hn w)
  exact H.zero_sum_mgf_bound hN μ hEx hBd
      (projOnePerp (zeroPad hn w)) hsum lam

/-- The one-sided concentration inequality is derived from the MGF theorem by
the sub-Gaussian Chernoff bound; it is not an independent analytic input. -/
theorem exchangeable_tail_bound_from_mgf (H : MainAnalyticInputs)
    {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
    (w : Fin n → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hne : normSq (projOnePerp (zeroPad hn w)) ≠ 0) :
    μ.real {x | tailThreshold hn w δ ≤ centeredWeightedSum hn w x} ≤ δ := by
  let a : Fin N → ℝ := projOnePerp (zeroPad hn w)
  have hnorm_nonneg : 0 ≤ normSq a := normSq_nonneg a
  have hnorm_pos : 0 < normSq a := lt_of_le_of_ne hnorm_nonneg (by simpa [a] using hne.symm)
  have hGamma_pos : 0 < Gamma N := Gamma_pos hN
  let c : NNReal :=
    ⟨Gamma N * normSq a, mul_nonneg hGamma_pos.le hnorm_nonneg⟩
  have hsubgaussian :
      ProbabilityTheory.HasSubgaussianMGF
        (fun x => centeredWeightedSum hn w x) c μ := by
    refine
      { integrable_exp_mul := ?_
        mgf_le := ?_ }
    · intro t
      simpa [centeredWeightedSum, a] using
        integrable_exp_mul_dot_of_bounded μ hBd a t
    · intro t
      have hmgf := exchangeable_mgf_bound H hN hn μ hEx hBd w t
      change ProbabilityTheory.mgf (fun x => centeredWeightedSum hn w x) μ t ≤ _
      calc
        _ ≤ Real.exp (((t ^ 2) / 2) * Gamma N * normSq a) := by
          simpa [ProbabilityTheory.mgf, a] using hmgf
        _ = Real.exp ((c : ℝ) * t ^ 2 / 2) := by
          congr 1
          simp only [c, NNReal.coe_mk]
          ring
  have hlog_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hδ0).mpr (by simpa using hδ1)
  have hsqrt_arg_nonneg : 0 ≤ 2 * Gamma N * Real.log (1 / δ) := by positivity
  have hthreshold_nonneg : 0 ≤ tailThreshold hn w δ := by
    unfold tailThreshold l2Norm
    positivity
  have hthreshold_sq :
      tailThreshold hn w δ ^ 2 =
        2 * (Gamma N * normSq a) * Real.log (1 / δ) := by
    unfold tailThreshold l2Norm
    rw [mul_pow, Real.sq_sqrt hnorm_nonneg,
      Real.sq_sqrt hsqrt_arg_nonneg]
    simp only [a]
    ring
  calc
    μ.real {x | tailThreshold hn w δ ≤ centeredWeightedSum hn w x}
        ≤ Real.exp (-(tailThreshold hn w δ) ^ 2 / (2 * c)) :=
      hsubgaussian.measure_ge_le hthreshold_nonneg
    _ = Real.exp (-Real.log (1 / δ)) := by
      congr 1
      rw [hthreshold_sq]
      simp only [c, NNReal.coe_mk]
      field_simp [ne_of_gt hGamma_pos, ne_of_gt hnorm_pos]
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / δ)]
      field_simp

/-- The one-sided tail bound exported from the named analytic input. -/
theorem exchangeable_tail_bound (H : MainAnalyticInputs)
    {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
    (w : Fin n → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hne : normSq (projOnePerp (zeroPad hn w)) ≠ 0) :
    μ.real {x | tailThreshold hn w δ ≤ centeredWeightedSum hn w x} ≤ δ :=
  exchangeable_tail_bound_from_mgf H hN hn μ hEx hBd w hδ0 hδ1 hne

/-- The sharp universal lower bound exported from the named analytic input. -/
theorem admissible_constant_lower_bound (H : MainAnalyticInputs)
    {N : ℕ} (hN : 2 ≤ N) {C : ℝ}
    (hC : AdmissibleConstant N C) :
    optimalLowerBound N ≤ C :=
  H.admissible_constant_bound hN hC

end ExchangeableHoeffding
