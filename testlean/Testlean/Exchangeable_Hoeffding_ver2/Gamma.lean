import Testlean.Exchangeable_Hoeffding_ver2.Basic

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open Filter Asymptotics

namespace ExchangeableHoeffding

/-! ## The inflation factor `Γ_N` and Barber's factor -/

/-- The term in the definition of `Γ_N`, indexed by `s`. -/
def gammaTerm (N s : ℕ) : ℝ :=
  ((N : ℝ) * ((N - s : ℕ) : ℝ) / (s : ℝ)) *
    (∑ ℓ ∈ Finset.Icc (N - s) (N - 1), (1 : ℝ) / ((ℓ : ℝ) ^ 2))

/-- The finite-population inflation factor `Γ_N`. -/
def Gamma (N : ℕ) : ℝ := by
  classical
  let S : Finset ℝ := (Finset.Icc 1 (N / 2)).image (fun s => gammaTerm N s)
  exact if h : S.Nonempty then S.max' h else 0

/-- Harmonic number `H_N = ∑_{j=1}^N 1/j`. -/
def harmonic (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ)

/-- Barber's inflation parameter `ε_N = (H_N - 1)/(N - H_N)`. -/
def epsilonBarber (N : ℕ) : ℝ :=
  (harmonic N - 1) / ((N : ℝ) - harmonic N)

/-- Closed-form version of `Γ_N`, split by parity. -/
def GammaClosed (N : ℕ) : ℝ :=
  if Even N then
    (N : ℝ) *
      (∑ ℓ ∈ Finset.Icc (N / 2) (N - 1), (1 : ℝ) / ((ℓ : ℝ) ^ 2))
  else
    ((N : ℝ) * ((N + 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) *
      (∑ ℓ ∈ Finset.Icc ((N + 1) / 2) (N - 1),
        (1 : ℝ) / ((ℓ : ℝ) ^ 2))

/-- Direct finite calculation: `Γ₂ = 2`. -/
lemma gamma_two : Gamma 2 = 2 := by
  classical
  unfold Gamma
  simp [gammaTerm]

/-- Direct finite calculation: `H₂ = 3/2`. -/
lemma harmonic_two : harmonic 2 = (3 : ℝ) / 2 := by
  unfold harmonic
  rw [Finset.sum_Icc_succ_top]
  · rw [Finset.sum_Icc_succ_top]
    · norm_num
    · norm_num
  · norm_num

/-- Direct finite calculation: `ε₂ = 1`. -/
lemma epsilonBarber_two : epsilonBarber 2 = 1 := by
  unfold epsilonBarber
  rw [harmonic_two]
  norm_num

/-- Endpoint comparison: at `N = 2`, the two inflation factors agree. -/
theorem gamma_eq_barber_two :
    Gamma 2 = 1 + epsilonBarber 2 := by
  rw [gamma_two, epsilonBarber_two]
  norm_num

/-- Proof obligations about the explicit inflation factor `Γ_N`. -/
structure GammaProofObligations : Prop where
  gamma_eq_closed :
    ∀ {N : ℕ} (hN : 2 ≤ N), Gamma N = GammaClosed N

  gamma_asymptotic :
    (fun N : ℕ => Gamma N - (1 + 3 / (2 * (N : ℝ))))
      =O[atTop] (fun N : ℕ => (1 : ℝ) / ((N : ℝ) ^ 2))

  gamma_lt_barber_from_three :
    ∀ {N : ℕ} (hN : 3 ≤ N), Gamma N < 1 + epsilonBarber N

/-- The finite-sample Barber comparison for every `N ≥ 3`. -/
theorem gamma_lt_barber (P : GammaProofObligations) {N : ℕ} (hN : 3 ≤ N) :
    Gamma N < 1 + epsilonBarber N :=
  P.gamma_lt_barber_from_three hN

end ExchangeableHoeffding
