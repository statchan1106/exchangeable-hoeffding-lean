import Testlean.ExchangeableHoeffding.Basic

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open Filter Asymptotics

namespace ExchangeableHoeffding

/-! ## The finite-population inflation factor -/

/-- The term in the definition of `Gamma`, indexed by `s`. -/
def gammaTerm (N s : ℕ) : ℝ :=
  ((N : ℝ) * ((N - s : ℕ) : ℝ) / (s : ℝ)) *
    (∑ ℓ ∈ Finset.Icc (N - s) (N - 1), (1 : ℝ) / ((ℓ : ℝ) ^ 2))

/-- The finite-population inflation factor. -/
def Gamma (N : ℕ) : ℝ := by
  classical
  let S : Finset ℝ := (Finset.Icc 1 (N / 2)).image (fun s => gammaTerm N s)
  exact if h : S.Nonempty then S.max' h else 0

/-- Harmonic number `H_N = ∑_{j=1}^N 1/j`. -/
def harmonic (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ)

/-- Barber's inflation parameter `(H_N - 1)/(N - H_N)`. -/
def epsilonBarber (N : ℕ) : ℝ :=
  (harmonic N - 1) / ((N : ℝ) - harmonic N)

/-- Closed form of the inflation factor, split by parity. -/
def GammaClosed (N : ℕ) : ℝ :=
  if Even N then
    (N : ℝ) *
      (∑ ℓ ∈ Finset.Icc (N / 2) (N - 1), (1 : ℝ) / ((ℓ : ℝ) ^ 2))
  else
    ((N : ℝ) * ((N + 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) *
      (∑ ℓ ∈ Finset.Icc ((N + 1) / 2) (N - 1),
        (1 : ℝ) / ((ℓ : ℝ) ^ 2))

/-- Every term entering the finite-population factor is nonnegative. -/
lemma gammaTerm_nonneg (N s : ℕ) : 0 ≤ gammaTerm N s := by
  unfold gammaTerm
  positivity

/-- The finite-population inflation factor is nonnegative for every population
size, including the empty indexing cases built into its total definition. -/
lemma Gamma_nonneg (N : ℕ) : 0 ≤ Gamma N := by
  classical
  unfold Gamma
  dsimp only
  split_ifs with h
  · let S : Finset ℝ :=
      (Finset.Icc 1 (N / 2)).image (fun s => gammaTerm N s)
    have hmem : S.max' h ∈ S := Finset.max'_mem S h
    rcases Finset.mem_image.mp hmem with ⟨s, hs, heq⟩
    rw [← heq]
    exact gammaTerm_nonneg N s
  · exact le_rfl

/-- The first admissible term is strictly positive once the population has at
least two elements. -/
lemma gammaTerm_one_pos {N : ℕ} (hN : 2 ≤ N) : 0 < gammaTerm N 1 := by
  unfold gammaTerm
  have hNm1nat : 0 < N - 1 := by omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hN)
  have hNm1real : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hNm1nat
  simp only [Nat.cast_one, div_one]
  rw [show N - 1 = N - 1 by rfl]
  simp only [Finset.Icc_self, one_div, Finset.sum_singleton, gt_iff_lt]
  positivity

/-- The inflation factor is strictly positive in the range used by the main
theorem. -/
lemma Gamma_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Gamma N := by
  classical
  unfold Gamma
  let S : Finset ℝ :=
    (Finset.Icc 1 (N / 2)).image (fun s => gammaTerm N s)
  have hhalf : 1 ≤ N / 2 := by omega
  have hone : 1 ∈ Finset.Icc 1 (N / 2) := by simp [hhalf]
  have hmem : gammaTerm N 1 ∈ S := Finset.mem_image.mpr ⟨1, hone, rfl⟩
  have hS : S.Nonempty := ⟨gammaTerm N 1, hmem⟩
  rw [dif_pos hS]
  exact lt_of_lt_of_le (gammaTerm_one_pos hN) (Finset.le_max' S _ hmem)

/-- Direct finite calculation at the smallest admissible population size. -/
lemma gamma_two : Gamma 2 = 2 := by
  classical
  unfold Gamma
  simp [gammaTerm]

/-- Direct finite calculation of the second harmonic number. -/
lemma harmonic_two : harmonic 2 = (3 : ℝ) / 2 := by
  unfold harmonic
  rw [Finset.sum_Icc_succ_top]
  · rw [Finset.sum_Icc_succ_top]
    · norm_num
    · norm_num
  · norm_num

/-- Direct finite calculation of Barber's factor at the endpoint. -/
lemma epsilonBarber_two : epsilonBarber 2 = 1 := by
  unfold epsilonBarber
  rw [harmonic_two]
  norm_num

/-- At the endpoint, the two inflation factors agree. -/
theorem gamma_eq_barber_two :
    Gamma 2 = 1 + epsilonBarber 2 := by
  rw [gamma_two, epsilonBarber_two]
  norm_num

/-- Analytic inputs still required for the general inflation-factor analysis. -/
structure GammaAnalyticInputs : Prop where
  closed_formula :
    ∀ {N : ℕ} (hN : 2 ≤ N), Gamma N = GammaClosed N

  asymptotic_expansion :
    (fun N : ℕ => Gamma N - (1 + 3 / (2 * (N : ℝ))))
      =O[atTop] (fun N : ℕ => (1 : ℝ) / ((N : ℝ) ^ 2))

  strict_barber_comparison :
    ∀ {N : ℕ} (hN : 3 ≤ N), Gamma N < 1 + epsilonBarber N

/-- The strict comparison follows from the named general comparison input. -/
theorem gamma_strictly_improves_barber (H : GammaAnalyticInputs)
    {N : ℕ} (hN : 3 ≤ N) :
    Gamma N < 1 + epsilonBarber N :=
  H.strict_barber_comparison hN

end ExchangeableHoeffding
