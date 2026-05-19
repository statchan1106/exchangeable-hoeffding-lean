import Testlean.Exchangeable_Hoeffding_ver2.Basic
import Testlean.Exchangeable_Hoeffding_ver2.Gamma
import Testlean.Exchangeable_Hoeffding_ver2.HammingSlice
import Testlean.Exchangeable_Hoeffding_ver2.Hypergeometric
import Testlean.Exchangeable_Hoeffding_ver2.ThreePoint

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace ExchangeableHoeffding

/-! ## Admissible constants and lower bound object -/

/-- A constant `C` is admissible if it can replace `Γ_N` in Theorem 2.1 uniformly. -/
def AdmissibleConstant (N : ℕ) (C : ℝ) : Prop :=
  ∀ (n : ℕ) (hn : n ≤ N) (μ : Measure (Fin N → ℝ)),
    IsProbabilityMeasure μ → Exchangeable μ → BoundedByOne μ →
      ∀ (w : Fin n → ℝ) (lam : ℝ),
        (∫ x, Real.exp (lam * centeredWeightedSum hn w x) ∂μ) ≤
          Real.exp (((lam ^ 2) / 2) * C * normSq (projOnePerp (zeroPad hn w)))

/-- The lower bound for any admissible replacement constant in Proposition 2.3. -/
def optimalLowerBound (N : ℕ) : ℝ :=
  if Even N then (N : ℝ) / ((N - 1 : ℕ) : ℝ)
  else ((N + 1 : ℕ) : ℝ) / (N : ℝ)

/-- Euclidean norm derived from `normSq`. -/
def l2Norm {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  Real.sqrt (normSq a)

/-- The threshold appearing in Corollary 2.2. -/
def tailThreshold {n N : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) (δ : ℝ) : ℝ :=
  l2Norm (projOnePerp (zeroPad hn w)) *
    Real.sqrt (2 * Gamma N * Real.log (1 / δ))

/-- High-level proof obligations used to derive the main theorem. -/
structure MainProofObligations : Prop where
  theorem_2_1_zero_sum :
    ∀ {N : ℕ} (hN : 2 ≤ N)
      (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
      (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
      (a : Fin N → ℝ) (ha : ∑ i : Fin N, a i = 0) (lam : ℝ),
      (∫ x, Real.exp (lam * dot a x) ∂μ) ≤
        Real.exp (((lam ^ 2) / 2) * Gamma N * normSq a)

  corollary_2_2 :
    ∀ {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N)
      (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
      (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
      (w : Fin n → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (hne : normSq (projOnePerp (zeroPad hn w)) ≠ 0),
      μ {x | tailThreshold hn w δ ≤ centeredWeightedSum hn w x} ≤ ENNReal.ofReal δ

  proposition_2_3 :
    ∀ {N : ℕ} (hN : 2 ≤ N) {C : ℝ}
      (hC : AdmissibleConstant N C), optimalLowerBound N ≤ C

/-- Theorem 2.1 derived from the zero-sum MGF statement and the projection identity. -/
theorem theorem_2_1 (P : MainProofObligations) {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
    (w : Fin n → ℝ) (lam : ℝ) :
    (∫ x, Real.exp (lam * centeredWeightedSum hn w x) ∂μ) ≤
      Real.exp (((lam ^ 2) / 2) * Gamma N * normSq (projOnePerp (zeroPad hn w))) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hN
  have hsum : ∑ i : Fin N, projOnePerp (zeroPad hn w) i = 0 :=
    sum_projOnePerp_eq_zero hNpos (zeroPad hn w)
  exact P.theorem_2_1_zero_sum hN μ hEx hBd
      (projOnePerp (zeroPad hn w)) hsum lam

/-- Corollary 2.2 exported from the high-level proof interface. -/
theorem corollary_2_2 (P : MainProofObligations) {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
    (w : Fin n → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hne : normSq (projOnePerp (zeroPad hn w)) ≠ 0) :
    μ {x | tailThreshold hn w δ ≤ centeredWeightedSum hn w x} ≤ ENNReal.ofReal δ :=
  P.corollary_2_2 hN hn μ hEx hBd w hδ0 hδ1 hne

/-- The optimality lower bound exported from the high-level interface. -/
theorem optimal_lower_bound (P : MainProofObligations) {N : ℕ} (hN : 2 ≤ N) {C : ℝ}
    (hC : AdmissibleConstant N C) :
    optimalLowerBound N ≤ C :=
  P.proposition_2_3 hN hC

end ExchangeableHoeffding
