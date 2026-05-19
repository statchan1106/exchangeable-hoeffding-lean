import Testlean.Exchangeable_Hoeffding_ver2.Basic
import Testlean.Exchangeable_Hoeffding_ver2.Gamma
import Testlean.Exchangeable_Hoeffding_ver2.Hypergeometric
import Testlean.Exchangeable_Hoeffding_ver2.ThreePoint

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace ExchangeableHoeffding

/-! ## Hamming slices and elementary symmetric polynomials -/

/-- The collection of all `k`-subsets of `Fin N`. -/
def sliceSubsets (N k : ℕ) : Finset (Finset (Fin N)) := by
  classical
  exact Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)

/-- Average of a real-valued function over the uniform Hamming slice. -/
def sliceAverage {N : ℕ} (k : ℕ) (f : Finset (Fin N) → ℝ) : ℝ :=
  (∑ S ∈ sliceSubsets N k, f S) / ((Nat.choose N k) : ℝ)

/-- Elementary symmetric polynomial `e_k(z_1, …, z_N)`. -/
def elemSym {N : ℕ} (k : ℕ) (z : Fin N → ℝ) : ℝ :=
  ∑ S ∈ sliceSubsets N k, ∏ i ∈ S, z i

/-- The functional `F_{N,k}` from Proposition 4.4. -/
def sliceFunctional {N : ℕ} (k : ℕ) (y : Fin N → ℝ) : ℝ :=
  Real.log (elemSym k (fun i => Real.exp (y i)) / ((Nat.choose N k) : ℝ))

/-- A vector has at most two distinct coordinate values. -/
def AtMostTwoValues {N : ℕ} (y : Fin N → ℝ) : Prop :=
  ∃ α β : ℝ, ∀ i : Fin N, y i = α ∨ y i = β

/-- The sphere section `{∑ y_i = 0, ||y||₂ = ρ}` written using `normSq`. -/
def SphereSection {N : ℕ} (ρ : ℝ) (y : Fin N → ℝ) : Prop :=
  (∑ i : Fin N, y i = 0) ∧ normSq y = ρ ^ 2

/-- Proof obligations for the Hamming-slice reduction. -/
structure SliceProofObligations : Prop where
  proposition_4_4 :
    ∀ {N k : ℕ} (hN : 2 ≤ N)
      (hk0 : 1 ≤ k) (hkN : k ≤ N - 1) {ρ : ℝ} (hρ : 0 ≤ ρ),
      ∃ y : Fin N → ℝ,
        SphereSection ρ y ∧ AtMostTwoValues y ∧
          ∀ z : Fin N → ℝ,
            SphereSection ρ z → sliceFunctional k z ≤ sliceFunctional k y

  slice_inequality :
    ∀ {N k : ℕ} (hN : 2 ≤ N)
      (hk0 : 1 ≤ k) (hkN : k ≤ N - 1)
      (y : Fin N → ℝ) (hy : ∑ i : Fin N, y i = 0),
      Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, y i))) ≤
        (Gamma N / 8) * normSq y

end ExchangeableHoeffding
