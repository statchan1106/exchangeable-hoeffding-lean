import Testlean.Exchangeable_Hoeffding_ver2.Basic

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace ExchangeableHoeffding

/-! ## Three-coordinate reduction objects -/

/-- The three-coordinate constrained objective from Lemma 4.3. -/
def threeObjective (A B : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  A * (∑ i : Fin 3, Real.exp (x i)) +
    B * (∑ i : Fin 3, Real.exp (-(x i)))

/-- The constraint set `u + v + z = s`, `u² + v² + z² = q`. -/
def ThreeSphereSection (s q : ℝ) (x : Fin 3 → ℝ) : Prop :=
  (∑ i : Fin 3, x i = s) ∧ (∑ i : Fin 3, (x i) ^ 2 = q)

/-- At least two coordinates agree. -/
def HasDuplicateCoordinate {N : ℕ} (x : Fin N → ℝ) : Prop :=
  ∃ i j : Fin N, i ≠ j ∧ x i = x j

/-- Analytic proof obligations for the three-coordinate reduction. -/
structure ThreePointProofObligations : Prop where
  lemma_4_2_lagrange_sign :
    ∀ (h : ℝ → ℝ) (x1 x2 x3 : ℝ)
      (hC5 : ContDiff ℝ 5 h)
      (hd12 : x1 ≠ x2) (hd13 : x1 ≠ x3) (hd23 : x2 ≠ x3)
      (hz1 : h x1 = 0) (hz2 : h x2 = 0) (hz3 : h x3 = 0)
      (hpos : ∀ t,
        min x1 (min x2 x3) < t → t < max x1 (max x2 x3) →
          0 < iteratedDeriv 5 h t),
      let p : ℝ → ℝ := fun t => (t - x1) * (t - x2) * (t - x3)
      0 < deriv h x1 / (deriv p x1) ^ 2 +
          deriv h x2 / (deriv p x2) ^ 2 +
          deriv h x3 / (deriv p x3) ^ 2

  lemma_4_3_no_three_distinct_max :
    ∀ {A B s q : ℝ}
      (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
      (hq : s ^ 2 / 3 < q) (x : Fin 3 → ℝ)
      (hx : ThreeSphereSection s q x)
      (hmax : ∀ y : Fin 3 → ℝ,
        ThreeSphereSection s q y → threeObjective A B y ≤ threeObjective A B x),
      HasDuplicateCoordinate x

end ExchangeableHoeffding
