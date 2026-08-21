import Testlean.ExchangeableHoeffding.Basic
import Testlean.ExchangeableHoeffding.Gamma
import Testlean.ExchangeableHoeffding.Hypergeometric
import Testlean.ExchangeableHoeffding.ThreePoint

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace ExchangeableHoeffding

/-! ## Hamming slices and elementary symmetric polynomials -/

/-- The collection of all `k`-subsets of `Fin N`. -/
def sliceSubsets (N k : ℕ) : Finset (Finset (Fin N)) := by
  classical
  exact Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)

/-- The slice is the usual fixed-cardinality powerset of the population. -/
lemma sliceSubsets_eq_powersetCard (N k : ℕ) :
    sliceSubsets N k = (Finset.univ : Finset (Fin N)).powersetCard k := by
  classical
  ext S
  simp [sliceSubsets, Finset.mem_powersetCard]

/-- The Hamming slice has the binomial cardinality used in its normalization. -/
lemma card_sliceSubsets (N k : ℕ) :
    (sliceSubsets N k).card = Nat.choose N k := by
  rw [sliceSubsets_eq_powersetCard, Finset.card_powersetCard]
  simp

/-- Average of a real-valued function over the uniform Hamming slice. -/
def sliceAverage {N : ℕ} (k : ℕ) (f : Finset (Fin N) → ℝ) : ℝ :=
  (∑ S ∈ sliceSubsets N k, f S) / ((Nat.choose N k) : ℝ)

/-- Averaging the constant one function over a nonempty slice gives one. -/
lemma sliceAverage_one {N k : ℕ} (hk : k ≤ N) :
    sliceAverage (N := N) k (fun _ => (1 : ℝ)) = 1 := by
  classical
  unfold sliceAverage
  rw [Finset.sum_const, nsmul_eq_mul, card_sliceSubsets]
  have hchoose : Nat.choose N k ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hk)
  field_simp

/-- Elementary symmetric polynomial. -/
def elemSym {N : ℕ} (k : ℕ) (z : Fin N → ℝ) : ℝ :=
  ∑ S ∈ sliceSubsets N k, ∏ i ∈ S, z i

/-- The Hamming-slice log-MGF functional. -/
def sliceFunctional {N : ℕ} (k : ℕ) (y : Fin N → ℝ) : ℝ :=
  Real.log (elemSym k (fun i => Real.exp (y i)) / ((Nat.choose N k) : ℝ))

/-- A vector has at most two distinct coordinate values. -/
def AtMostTwoValues {N : ℕ} (y : Fin N → ℝ) : Prop :=
  ∃ α β : ℝ, ∀ i : Fin N, y i = α ∨ y i = β

/-- The zero-sum sphere section. -/
def SphereSection {N : ℕ} (ρ : ℝ) (y : Fin N → ℝ) : Prop :=
  (∑ i : Fin N, y i = 0) ∧ normSq y = ρ ^ 2

/-- A vector with one value on a coordinate set and another on its complement. -/
def twoLevelVector {N : ℕ} (A : Finset (Fin N)) (α β : ℝ) : Fin N → ℝ :=
  fun i => if i ∈ A then α else β

/-- Coordinate sum of a two-level vector. -/
lemma sum_twoLevelVector {N : ℕ} (A : Finset (Fin N)) (α β : ℝ) :
    (∑ i : Fin N, twoLevelVector A α β i) =
      (A.card : ℝ) * α + ((N - A.card : ℕ) : ℝ) * β := by
  classical
  have hparts :
      A.card + (Finset.univ.filter fun i : Fin N => i ∉ A).card = N := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin N))) (fun i => i ∈ A))
  have hcard : (Finset.univ.filter fun i : Fin N => i ∉ A).card = N - A.card := by
    omega
  unfold twoLevelVector
  rw [Finset.sum_ite]
  simp [hcard]

/-- Squared norm of a two-level vector. -/
lemma normSq_twoLevelVector {N : ℕ} (A : Finset (Fin N)) (α β : ℝ) :
    normSq (twoLevelVector A α β) =
      (A.card : ℝ) * α ^ 2 + ((N - A.card : ℕ) : ℝ) * β ^ 2 := by
  classical
  have hparts :
      A.card + (Finset.univ.filter fun i : Fin N => i ∉ A).card = N := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin N))) (fun i => i ∈ A))
  have hcard : (Finset.univ.filter fun i : Fin N => i ∉ A).card = N - A.card := by
    omega
  unfold normSq twoLevelVector
  simp_rw [ite_pow]
  rw [Finset.sum_ite]
  simp [hcard]

/-- The centered two-level vector parameterized by the gap between its values. -/
def centeredTwoLevelVector {N : ℕ} (A : Finset (Fin N)) (d : ℝ) : Fin N → ℝ :=
  twoLevelVector A
    ((((N - A.card : ℕ) : ℝ) / (N : ℝ)) * d)
    (-((A.card : ℝ) / (N : ℝ)) * d)

/-- The paper's two-level parameterization has zero coordinate sum. -/
lemma sum_centeredTwoLevelVector {N : ℕ} (hN : 0 < N)
    (A : Finset (Fin N)) (d : ℝ) :
    ∑ i : Fin N, centeredTwoLevelVector A d i = 0 := by
  rw [centeredTwoLevelVector, sum_twoLevelVector]
  have hcard : A.card ≤ N := by simpa using A.card_le_univ
  rw [Nat.cast_sub hcard]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- Squared norm in the paper's centered two-level parameterization. -/
lemma normSq_centeredTwoLevelVector {N : ℕ} (hN : 0 < N)
    (A : Finset (Fin N)) (d : ℝ) :
    normSq (centeredTwoLevelVector A d) =
      ((A.card : ℝ) * ((N - A.card : ℕ) : ℝ) / (N : ℝ)) * d ^ 2 := by
  rw [centeredTwoLevelVector, normSq_twoLevelVector]
  have hcard : A.card ≤ N := by simpa using A.card_le_univ
  rw [Nat.cast_sub hcard]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- Sum of a two-level vector over an arbitrary coordinate subset. -/
lemma sum_twoLevelVector_on {N : ℕ} (S A : Finset (Fin N)) (α β : ℝ) :
    (∑ i ∈ S, twoLevelVector A α β i) =
      ((S.filter fun i => i ∈ A).card : ℝ) * α +
        ((S.filter fun i => i ∉ A).card : ℝ) * β := by
  classical
  unfold twoLevelVector
  rw [Finset.sum_ite]
  simp

/-- A centered two-level slice sum is a centered intersection count. -/
lemma sum_centeredTwoLevelVector_on {N : ℕ} (hN : 0 < N)
    (S A : Finset (Fin N)) (d : ℝ) :
    (∑ i ∈ S, centeredTwoLevelVector A d i) =
      d * (((S.filter fun i => i ∈ A).card : ℝ) -
        (S.card : ℝ) * (A.card : ℝ) / (N : ℝ)) := by
  classical
  rw [centeredTwoLevelVector, sum_twoLevelVector_on]
  have hparts :
      (S.filter fun i => i ∈ A).card +
          (S.filter fun i => i ∉ A).card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun i => i ∈ A)
  have hcomp :
      (S.filter fun i => i ∉ A).card =
        S.card - (S.filter fun i => i ∈ A).card := by omega
  rw [hcomp, Nat.cast_sub (Finset.card_filter_le _ _)]
  have hcard : A.card ≤ N := by simpa using A.card_le_univ
  rw [Nat.cast_sub hcard]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- The exponential slice average is exactly the normalized elementary
symmetric polynomial used in the variational formulation. -/
lemma sliceAverage_exp_sum_eq_elemSym {N : ℕ} (k : ℕ) (y : Fin N → ℝ) :
    sliceAverage k (fun S => Real.exp (∑ i ∈ S, y i)) =
      elemSym k (fun i => Real.exp (y i)) / ((Nat.choose N k) : ℝ) := by
  classical
  unfold sliceAverage elemSym
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  exact Real.exp_sum S y

/-- The two definitions of the Hamming-slice log-MGF coincide. -/
lemma sliceFunctional_eq_log_sliceAverage {N : ℕ} (k : ℕ) (y : Fin N → ℝ) :
    sliceFunctional k y =
      Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, y i))) := by
  unfold sliceFunctional
  rw [sliceAverage_exp_sum_eq_elemSym]

/-- Analytic inputs still required for the Hamming-slice reduction. -/
structure SliceAnalyticInputs : Prop where
  two_level_extremizer :
    ∀ {N k : ℕ} (hN : 2 ≤ N)
      (hk0 : 1 ≤ k) (hkN : k ≤ N - 1) {ρ : ℝ} (hρ : 0 < ρ),
      ∃ y : Fin N → ℝ,
        SphereSection ρ y ∧ AtMostTwoValues y ∧
          ∀ z : Fin N → ℝ,
            SphereSection ρ z → sliceFunctional k z ≤ sliceFunctional k y

  slice_mgf_bound :
    ∀ {N k : ℕ} (hN : 2 ≤ N)
      (hk0 : 1 ≤ k) (hkN : k ≤ N - 1)
      (y : Fin N → ℝ) (hy : ∑ i : Fin N, y i = 0),
      Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, y i))) ≤
        (Gamma N / 8) * normSq y

end ExchangeableHoeffding
