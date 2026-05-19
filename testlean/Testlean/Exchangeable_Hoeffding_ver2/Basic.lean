import Mathlib

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace ExchangeableHoeffding

/-! ## Basic finite-dimensional definitions -/

/-- Dot product on `Fin N → ℝ`. -/
def dot {N : ℕ} (a x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, a i * x i

/-- Squared Euclidean norm on `Fin N → ℝ`. -/
def normSq {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (a i) ^ 2

/-- Finite-population average of an `N`-vector. -/
def avg {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, x i) / (N : ℝ)

/-- Orthogonal projection onto the hyperplane perpendicular to the all-ones vector. -/
def projOnePerp {N : ℕ} (z : Fin N → ℝ) : Fin N → ℝ :=
  fun i => z i - (∑ j : Fin N, z j) / (N : ℝ)

/-- Zero-pad a vector indexed by `Fin n` into a vector indexed by `Fin N`. -/
def zeroPad {n N : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) : Fin N → ℝ :=
  fun i => if hi : i.val < n then w ⟨i.val, hi⟩ else 0

/--
The centered weighted sum in Theorem 2.1.

For Lean, we use the projected dot-product form as the definition.
-/
def centeredWeightedSum {n N : ℕ} (hn : n ≤ N)
    (w : Fin n → ℝ) (x : Fin N → ℝ) : ℝ :=
  dot (projOnePerp (zeroPad hn w)) x

/-- The projection onto the all-ones orthogonal complement has zero coordinate sum. -/
lemma sum_projOnePerp_eq_zero {N : ℕ} (hN : 0 < N) (z : Fin N → ℝ) :
    ∑ i : Fin N, projOnePerp z i = 0 := by
  classical
  unfold projOnePerp
  let S : ℝ := ∑ j : Fin N, z j
  have hNreal : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  calc
    ∑ i : Fin N, (z i - (∑ j : Fin N, z j) / (N : ℝ))
        = (∑ i : Fin N, z i) -
            ∑ i : Fin N, (∑ j : Fin N, z j) / (N : ℝ) := by
          rw [Finset.sum_sub_distrib]
    _ = S - (N : ℝ) * (S / (N : ℝ)) := by
          simp [S]
    _ = S - S := by
          field_simp [hNreal]
    _ = 0 := by
          ring

/-! ## Exchangeability and boundedness -/

/-- Coordinate permutation of an `N`-vector. -/
def permute {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => x (σ i)

/-- Exchangeability of the law of an `N`-vector. -/
def Exchangeable {N : ℕ} (μ : Measure (Fin N → ℝ)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), Measure.map (permute σ) μ = μ

/-- Exchangeability directly gives invariance under coordinate permutations. -/
theorem exchangeability_supports_symmetrization {N : ℕ} {μ : Measure (Fin N → ℝ)}
    (hμ : Exchangeable μ) (σ : Equiv.Perm (Fin N)) :
    Measure.map (permute σ) μ = μ :=
  hμ σ

/-- Almost-sure boundedness by `[-1, 1]` in every coordinate. -/
def BoundedByOne {N : ℕ} (μ : Measure (Fin N → ℝ)) : Prop :=
  ∀ᵐ x ∂μ, ∀ i : Fin N, (-1 : ℝ) ≤ x i ∧ x i ≤ 1

end ExchangeableHoeffding
