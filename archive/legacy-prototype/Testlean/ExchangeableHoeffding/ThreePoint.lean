import Testlean.ExchangeableHoeffding.Basic

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace ExchangeableHoeffding

/-! ## Three-coordinate extremizer objects -/

/-- The three-coordinate constrained objective. -/
def threeObjective (A B : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  A * (∑ i : Fin 3, Real.exp (x i)) +
    B * (∑ i : Fin 3, Real.exp (-(x i)))

/-- The constraint set with fixed coordinate sum and squared norm. -/
def ThreeSphereSection (s q : ℝ) (x : Fin 3 → ℝ) : Prop :=
  (∑ i : Fin 3, x i = s) ∧ (∑ i : Fin 3, (x i) ^ 2 = q)

/-- At least two coordinates agree. -/
def HasDuplicateCoordinate {N : ℕ} (x : Fin N → ℝ) : Prop :=
  ∃ i j : Fin N, i ≠ j ∧ x i = x j

/-- The reciprocal Lagrange weights for three distinct roots sum to zero. -/
lemma lagrange_tangent_sum_zero {x1 x2 x3 : ℝ}
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3) :
    1 / ((x1 - x2) * (x1 - x3)) +
        1 / ((x2 - x1) * (x2 - x3)) +
        1 / ((x3 - x1) * (x3 - x2)) = 0 := by
  have h21 : x2 - x1 ≠ 0 := sub_ne_zero.mpr h12.symm
  have h31 : x3 - x1 ≠ 0 := sub_ne_zero.mpr h13.symm
  have h32 : x3 - x2 ≠ 0 := sub_ne_zero.mpr h23.symm
  have h12' : x1 - x2 ≠ 0 := sub_ne_zero.mpr h12
  have h13' : x1 - x3 ≠ 0 := sub_ne_zero.mpr h13
  have h23' : x2 - x3 ≠ 0 := sub_ne_zero.mpr h23
  field_simp
  ring

/-- The reciprocal Lagrange weights are also orthogonal to the root vector. -/
lemma lagrange_tangent_weighted_sum_zero {x1 x2 x3 : ℝ}
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3) :
    x1 / ((x1 - x2) * (x1 - x3)) +
        x2 / ((x2 - x1) * (x2 - x3)) +
        x3 / ((x3 - x1) * (x3 - x2)) = 0 := by
  have h21 : x2 - x1 ≠ 0 := sub_ne_zero.mpr h12.symm
  have h31 : x3 - x1 ≠ 0 := sub_ne_zero.mpr h13.symm
  have h32 : x3 - x2 ≠ 0 := sub_ne_zero.mpr h23.symm
  have h12' : x1 - x2 ≠ 0 := sub_ne_zero.mpr h12
  have h13' : x1 - x3 ≠ 0 := sub_ne_zero.mpr h13
  have h23' : x2 - x3 ≠ 0 := sub_ne_zero.mpr h23
  field_simp
  ring

/-- Analytic inputs still required for the three-coordinate reduction. -/
structure ThreePointAnalyticInputs : Prop where
  three_root_derivative_sign :
    ∀ (h : ℝ → ℝ) (x1 x2 x3 : ℝ)
      (hC5 : ContDiff ℝ 5 h)
      (hd12 : x1 ≠ x2) (hd13 : x1 ≠ x3) (hd23 : x2 ≠ x3)
      (hz1 : h x1 = 0) (hz2 : h x2 = 0) (hz3 : h x3 = 0)
      (hpos : ∀ t,
        min x1 (min x2 x3) < t ∧ t < max x1 (max x2 x3) →
          0 < iteratedDeriv 5 h t),
      let p : ℝ → ℝ := fun t => (t - x1) * (t - x2) * (t - x3)
      0 < deriv h x1 / (deriv p x1) ^ 2 +
          deriv h x2 / (deriv p x2) ^ 2 +
          deriv h x3 / (deriv p x3) ^ 2

  maximizer_has_duplicate_coordinate :
    ∀ {A B s q : ℝ}
      (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
      (hq : s ^ 2 / 3 < q) (x : Fin 3 → ℝ)
      (hx : ThreeSphereSection s q x)
      (hmax : ∀ y : Fin 3 → ℝ,
        ThreeSphereSection s q y → threeObjective A B y ≤ threeObjective A B x),
      HasDuplicateCoordinate x

end ExchangeableHoeffding
