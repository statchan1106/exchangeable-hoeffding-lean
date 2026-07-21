import Mathlib

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace ExchangeableHoeffding

/-! ## Finite-dimensional definitions and identities -/

/-- Dot product on a finite real vector space. -/
def dot {N : ℕ} (a x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, a i * x i

/-- Squared Euclidean norm on a finite real vector space. -/
def normSq {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (a i) ^ 2

/-- Finite-population average of a vector. -/
def avg {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, x i) / (N : ℝ)

/-- Orthogonal projection onto the hyperplane perpendicular to the all-ones vector. -/
def projOnePerp {N : ℕ} (z : Fin N → ℝ) : Fin N → ℝ :=
  fun i => z i - (∑ j : Fin N, z j) / (N : ℝ)

/-- Zero-pad a vector indexed by `Fin n` into a vector indexed by `Fin N`. -/
def zeroPad {n N : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) : Fin N → ℝ :=
  fun i => if hi : i.val < n then w ⟨i.val, hi⟩ else 0

/-- The centered weighted statistic, expressed as a projected dot product. -/
def centeredWeightedSum {n N : ℕ} (hn : n ≤ N)
    (w : Fin n → ℝ) (x : Fin N → ℝ) : ℝ :=
  dot (projOnePerp (zeroPad hn w)) x

/-- A fixed dot product is a measurable random variable on finite-dimensional
Euclidean space. -/
lemma measurable_dot {N : ℕ} (a : Fin N → ℝ) :
    Measurable (fun x : Fin N → ℝ => dot a x) := by
  unfold dot
  fun_prop

/-- Pointwise bound for a linear statistic on the coordinate cube. -/
lemma abs_dot_le_sum_abs {N : ℕ} (a x : Fin N → ℝ)
    (hx : ∀ i : Fin N, -1 ≤ x i ∧ x i ≤ 1) :
    |dot a x| ≤ ∑ i : Fin N, |a i| := by
  unfold dot
  calc
    |∑ i : Fin N, a i * x i| ≤ ∑ i : Fin N, |a i * x i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, |a i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hxi : |x i| ≤ 1 := abs_le.mpr (hx i)
      nlinarith [abs_nonneg (a i)]

/-- A squared norm is nonnegative. -/
lemma normSq_nonneg {N : ℕ} (a : Fin N → ℝ) : 0 ≤ normSq a := by
  unfold normSq
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Zero-padding preserves the coordinate sum. -/
lemma sum_zeroPad {n N : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) :
    ∑ i : Fin N, zeroPad hn w i = ∑ i : Fin n, w i := by
  classical
  let f : ℕ → ℝ := fun i => if hi : i < n then w ⟨i, hi⟩ else 0
  have hleft : (∑ i : Fin N, zeroPad hn w i) = ∑ i : Fin N, f i.val := by
    apply Fintype.sum_congr
    intro i
    simp [f, zeroPad]
  have hright : (∑ i : Fin n, w i) = ∑ i : Fin n, f i.val := by
    apply Fintype.sum_congr
    intro i
    simp [f, i.isLt]
  rw [hleft, hright, Fin.sum_univ_eq_sum_range f N, Fin.sum_univ_eq_sum_range f n]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro i hiN hin
  simp only [Finset.mem_range] at hiN hin
  simp [f, not_lt.mp hin]

/-- A dot product with a zero-padded vector reduces to the original coordinates. -/
lemma dot_zeroPad {n N : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) (x : Fin N → ℝ) :
    dot (zeroPad hn w) x = ∑ i : Fin n, w i * x (Fin.castLE hn i) := by
  classical
  let f : ℕ → ℝ := fun i =>
    if hi : i < n then w ⟨i, hi⟩ * x (Fin.castLE hn ⟨i, hi⟩) else 0
  have hleft : (∑ i : Fin N, zeroPad hn w i * x i) = ∑ i : Fin N, f i.val := by
    apply Fintype.sum_congr
    intro i
    by_cases hi : i.val < n
    · simp [f, zeroPad, hi]
    · simp [f, zeroPad, hi]
  have hright : (∑ i : Fin n, w i * x (Fin.castLE hn i)) =
      ∑ i : Fin n, f i.val := by
    apply Fintype.sum_congr
    intro i
    simp only [f, dif_pos i.isLt]
  unfold dot
  rw [hleft, hright, Fin.sum_univ_eq_sum_range f N, Fin.sum_univ_eq_sum_range f n]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro i hiN hin
  simp only [Finset.mem_range] at hiN hin
  simp [f, not_lt.mp hin]

/-- The projected statistic is exactly the paper's centered weighted sum. -/
theorem centeredWeightedSum_eq_centered_coordinates {n N : ℕ} (hn : n ≤ N)
    (w : Fin n → ℝ) (x : Fin N → ℝ) :
    centeredWeightedSum hn w x =
      ∑ i : Fin n, w i * (x (Fin.castLE hn i) - avg x) := by
  classical
  have hdot : (∑ i : Fin N, zeroPad hn w i * x i) =
      ∑ i : Fin n, w i * x (Fin.castLE hn i) := by
    simpa [dot] using dot_zeroPad hn w x
  unfold centeredWeightedSum dot projOnePerp avg
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [hdot, sum_zeroPad]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

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

/-- A zero-sum vector is fixed by projection. -/
lemma projOnePerp_eq_self {N : ℕ} (z : Fin N → ℝ)
    (hz : ∑ i : Fin N, z i = 0) : projOnePerp z = z := by
  funext i
  simp [projOnePerp, hz]

/-- The projection is idempotent whenever the population is nonempty. -/
lemma projOnePerp_idempotent {N : ℕ} (hN : 0 < N) (z : Fin N → ℝ) :
    projOnePerp (projOnePerp z) = projOnePerp z :=
  projOnePerp_eq_self _ (sum_projOnePerp_eq_zero hN z)

/-! ## Exchangeability and boundedness -/

/-- Coordinate permutation of a finite vector. -/
def permute {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => x (σ i)

/-- Exchangeability of the law of a finite vector. -/
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
