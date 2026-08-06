import Testlean.ExchangeableHoeffding.Gamma

noncomputable section

open scoped BigOperators

namespace ExchangeableHoeffding

/-! ## Closed analysis of the finite-population inflation factor

This module proves the maximizing index, the parity-dependent closed formula,
the quantitative second-order expansion, and the strict comparison with the
harmonic inflation factor.  The asymptotic theorem is obtained from an
explicit midpoint-telescoping error bound rather than an unformalized appeal
to Euler--Maclaurin summation. -/

lemma inv_sq_lt_telescope {ell : ℕ} (hell : 1 ≤ ell) :
    (1 : ℝ) / (ell : ℝ) ^ 2 <
      1 / ((ell : ℝ) - 1 / 2) - 1 / ((ell : ℝ) + 1 / 2) := by
  have hx : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hxm : 0 < (ell : ℝ) - 1 / 2 := by linarith
  have hxp : 0 < (ell : ℝ) + 1 / 2 := by linarith
  have hden : 0 < (ell : ℝ) ^ 2 - 1 / 4 := by
    nlinarith [sq_nonneg ((ell : ℝ) - 1)]
  have htel :
      1 / ((ell : ℝ) - 1 / 2) - 1 / ((ell : ℝ) + 1 / 2) =
        1 / ((ell : ℝ) ^ 2 - 1 / 4) := by
    rw [div_sub_div _ _ (ne_of_gt hxm) (ne_of_gt hxp)]
    congr 1 <;> ring
  rw [htel]
  apply one_div_lt_one_div_of_lt
  · exact hden
  · norm_num

lemma telescope_sum_Icc {N r : ℕ} (hrN : r < N) :
    (∑ ell ∈ Finset.Icc r (N - 1),
        (1 / ((ell : ℝ) - 1 / 2) - 1 / ((ell : ℝ) + 1 / 2))) =
      1 / ((r : ℝ) - 1 / 2) - 1 / ((N : ℝ) - 1 / 2) := by
  have hNm1 : N - 1 + 1 = N := by omega
  rw [← Finset.Ico_add_one_right_eq_Icc r (N - 1), hNm1]
  rw [Finset.sum_Ico_eq_sum_range]
  let f : ℕ → ℝ := fun i => 1 / (((r + i : ℕ) : ℝ) - 1 / 2)
  have hterm : ∀ i : ℕ,
      1 / (((r + i : ℕ) : ℝ) - 1 / 2) -
          1 / (((r + i : ℕ) : ℝ) + 1 / 2) = f i - f (i + 1) := by
    intro i
    simp only [f, Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  simp_rw [hterm]
  rw [Finset.sum_range_sub']
  simp only [f, Nat.add_zero]
  have hrle : r ≤ N := Nat.le_of_lt hrN
  rw [Nat.add_sub_of_le hrle]

lemma reciprocal_square_sum_le {N r : ℕ} (hr : 1 ≤ r) (hrN : r < N) :
    (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) ≤
      1 / ((r : ℝ) - 1 / 2) - 1 / ((N : ℝ) - 1 / 2) := by
  calc
    (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) ≤
        ∑ ell ∈ Finset.Icc r (N - 1),
          (1 / ((ell : ℝ) - 1 / 2) - 1 / ((ell : ℝ) + 1 / 2)) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact (inv_sq_lt_telescope (hr.trans (Finset.mem_Icc.mp hell).1)).le
    _ = 1 / ((r : ℝ) - 1 / 2) - 1 / ((N : ℝ) - 1 / 2) :=
      telescope_sum_Icc hrN

lemma reciprocal_square_sum_lt {N r : ℕ} (hr : 1 ≤ r) (hrN : r < N) :
    (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) <
      1 / ((r : ℝ) - 1 / 2) - 1 / ((N : ℝ) - 1 / 2) := by
  calc
    (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) <
        ∑ ell ∈ Finset.Icc r (N - 1),
          (1 / ((ell : ℝ) - 1 / 2) - 1 / ((ell : ℝ) + 1 / 2)) := by
      apply Finset.sum_lt_sum
      · intro ell hell
        exact (inv_sq_lt_telescope (hr.trans (Finset.mem_Icc.mp hell).1)).le
      · refine ⟨r, ?_, inv_sq_lt_telescope hr⟩
        simp
        omega
    _ = 1 / ((r : ℝ) - 1 / 2) - 1 / ((N : ℝ) - 1 / 2) :=
      telescope_sum_Icc hrN

lemma reciprocal_square_sum_le_ratio {N r : ℕ} (hr : 2 ≤ r) (hrN : r < N) :
    (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) ≤
      ((N - r : ℕ) : ℝ) / ((N : ℝ) * ((r - 1 : ℕ) : ℝ)) := by
  have hrle : r ≤ N := Nat.le_of_lt hrN
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrN_R : (r : ℝ) < (N : ℝ) := by exact_mod_cast hrN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hrhalf : (0 : ℝ) < (r : ℝ) - 1 / 2 := by linarith
  have hNhalf : (0 : ℝ) < (N : ℝ) - 1 / 2 := by linarith
  have hrsub : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hden1 : 0 < ((r : ℝ) - 1 / 2) * ((N : ℝ) - 1 / 2) := by
    exact mul_pos hrhalf hNhalf
  have hden2 : 0 < (N : ℝ) * ((r : ℝ) - 1) := by
    exact mul_pos hNpos hrsub
  have htel :
      1 / ((r : ℝ) - 1 / 2) - 1 / ((N : ℝ) - 1 / 2) =
        ((N : ℝ) - (r : ℝ)) /
          (((r : ℝ) - 1 / 2) * ((N : ℝ) - 1 / 2)) := by
    rw [div_sub_div _ _ (ne_of_gt hrhalf) (ne_of_gt hNhalf)]
    congr 1
    ring
  calc
    (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) ≤
        1 / ((r : ℝ) - 1 / 2) - 1 / ((N : ℝ) - 1 / 2) :=
      reciprocal_square_sum_le hr1 hrN
    _ = ((N : ℝ) - (r : ℝ)) /
          (((r : ℝ) - 1 / 2) * ((N : ℝ) - 1 / 2)) := htel
    _ ≤ ((N : ℝ) - (r : ℝ)) / ((N : ℝ) * ((r : ℝ) - 1)) := by
      rw [div_le_div_iff₀ hden1 hden2]
      have hnum : 0 ≤ (N : ℝ) - (r : ℝ) := by linarith
      nlinarith
    _ = ((N - r : ℕ) : ℝ) / ((N : ℝ) * ((r - 1 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hrle, Nat.cast_sub (by omega : 1 ≤ r)]
      norm_num

lemma reciprocal_square_sum_pred {N r : ℕ} (hr : 2 ≤ r) (hrN : r < N) :
    (∑ ell ∈ Finset.Icc (r - 1) (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) =
      (1 : ℝ) / ((r - 1 : ℕ) : ℝ) ^ 2 +
        ∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2 := by
  have hNm1 : N - 1 + 1 = N := by omega
  rw [← Finset.Ico_add_one_right_eq_Icc (r - 1) (N - 1),
    ← Finset.Ico_add_one_right_eq_Icc r (N - 1), hNm1]
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ r)] using
    (Finset.sum_eq_sum_Ico_succ_bot (by omega : r - 1 < N)
      (fun ell : ℕ => ((ell : ℝ) ^ 2)⁻¹))

/-- The part of `gammaTerm` that depends on the complementary index `r = N-s`. -/
def gammaCore (N r : ℕ) : ℝ :=
  ((r : ℝ) / ((N - r : ℕ) : ℝ)) *
    (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2)

lemma gammaCore_le_pred {N r : ℕ} (hr : 2 ≤ r) (hrN : r < N) :
    gammaCore N r ≤ gammaCore N (r - 1) := by
  have hrle : r ≤ N := Nat.le_of_lt hrN
  have hr1 : 1 ≤ r := by omega
  have hNrpos : 0 < N - r := Nat.sub_pos_of_lt hrN
  have hNr1pos : 0 < N - (r - 1) := by omega
  have hrm1pos : 0 < r - 1 := by omega
  let S : ℝ := ∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2
  have hS : S ≤ ((N - r : ℕ) : ℝ) /
      ((N : ℝ) * ((r - 1 : ℕ) : ℝ)) := by
    simpa [S] using reciprocal_square_sum_le_ratio hr hrN
  rw [gammaCore, gammaCore, reciprocal_square_sum_pred hr hrN]
  change ((r : ℝ) / ((N - r : ℕ) : ℝ)) * S ≤
    (((r - 1 : ℕ) : ℝ) / ((N - (r - 1) : ℕ) : ℝ)) *
      ((1 : ℝ) / ((r - 1 : ℕ) : ℝ) ^ 2 + S)
  have hNrR : (0 : ℝ) < ((N - r : ℕ) : ℝ) := by exact_mod_cast hNrpos
  have hNr1R : (0 : ℝ) < ((N - (r - 1) : ℕ) : ℝ) := by exact_mod_cast hNr1pos
  have hrm1R : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by exact_mod_cast hrm1pos
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < r) hrle)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [div_le_div_iff₀ hNrR hNr1R]
  have hcastNr : ((N - r : ℕ) : ℝ) = (N : ℝ) - (r : ℝ) := Nat.cast_sub hrle
  have hcastRm : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    simpa using Nat.cast_sub hr1
  have hcastNrm : ((N - (r - 1) : ℕ) : ℝ) =
      (N : ℝ) - ((r : ℝ) - 1) := by
    rw [Nat.cast_sub (by omega : r - 1 ≤ N), hcastRm]
  rw [hcastNr, hcastRm] at hS
  rw [hcastNr, hcastRm, hcastNrm]
  norm_num at hS ⊢
  have hden : 0 < (N : ℝ) * ((r : ℝ) - 1) := mul_pos hNR (by linarith)
  rw [le_div_iff₀ hden] at hS
  have hrsubR : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hSN : S * (N : ℝ) ≤ ((N : ℝ) - (r : ℝ)) / ((r : ℝ) - 1) := by
    rw [le_div_iff₀ hrsubR]
    nlinarith [hS]
  have halgebra :
      ((r : ℝ) - 1) * (1 / ((r : ℝ) - 1) ^ 2 + S) *
            ((N : ℝ) - (r : ℝ)) -
          (r : ℝ) * S * ((N : ℝ) - ((r : ℝ) - 1)) =
        ((N : ℝ) - (r : ℝ)) / ((r : ℝ) - 1) - S * (N : ℝ) := by
    field_simp [ne_of_gt hrsubR]
    ring
  simp only [one_div] at halgebra hSN ⊢
  linarith [halgebra, hSN]

lemma gammaTerm_eq_mul_gammaCore {N s : ℕ} (hs : s ≤ N) :
    gammaTerm N s = (N : ℝ) * gammaCore N (N - s) := by
  unfold gammaTerm gammaCore
  rw [Nat.sub_sub_self hs]
  ring

lemma gammaCore_antitone {N r₀ r : ℕ}
    (hr₀ : 2 ≤ r₀) (hrr₀ : r₀ ≤ r) (hrN : r < N) :
    gammaCore N r ≤ gammaCore N r₀ := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      rcases eq_or_lt_of_le hrr₀ with hEq | hlt
      · subst r
        exact le_rfl
      · have hr : 2 ≤ r := le_trans hr₀ hrr₀
        exact (gammaCore_le_pred hr hrN).trans
          (ih (r - 1) (by omega) (by omega) (by omega))

lemma gammaTerm_le_half {N s : ℕ} (hN : 3 ≤ N)
    (hs0 : 1 ≤ s) (hsN : s ≤ N / 2) :
    gammaTerm N s ≤ gammaTerm N (N / 2) := by
  have hhalfN : N / 2 ≤ N := Nat.div_le_self N 2
  rw [gammaTerm_eq_mul_gammaCore (le_trans hsN hhalfN),
    gammaTerm_eq_mul_gammaCore hhalfN]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  apply gammaCore_antitone
  · omega
  · omega
  · omega

lemma Gamma_eq_gammaTerm_half {N : ℕ} (hN : 3 ≤ N) :
    Gamma N = gammaTerm N (N / 2) := by
  classical
  unfold Gamma
  let S : Finset ℝ :=
    (Finset.Icc 1 (N / 2)).image (fun s => gammaTerm N s)
  have hhalf : 1 ≤ N / 2 := by omega
  have hhalf_mem : N / 2 ∈ Finset.Icc 1 (N / 2) := by simp [hhalf]
  have hvalue_mem : gammaTerm N (N / 2) ∈ S :=
    Finset.mem_image.mpr ⟨N / 2, hhalf_mem, rfl⟩
  have hS : S.Nonempty := ⟨_, hvalue_mem⟩
  rw [dif_pos hS]
  apply (Finset.max'_eq_iff S hS (gammaTerm N (N / 2))).2
  constructor
  · exact hvalue_mem
  · intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨s, hs, rfl⟩
    exact gammaTerm_le_half hN (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2

theorem Gamma_eq_closed {N : ℕ} (hN : 2 ≤ N) : Gamma N = GammaClosed N := by
  by_cases hN2 : N = 2
  · subst N
    rw [gamma_two]
    norm_num [GammaClosed]
  · have hN3 : 3 ≤ N := by omega
    rw [Gamma_eq_gammaTerm_half hN3]
    by_cases hEven : Even N
    · rw [GammaClosed, if_pos hEven]
      unfold gammaTerm
      have hsub : N - N / 2 = N / 2 := by
        rcases hEven with ⟨M, hM⟩
        omega
      rw [hsub]
      have hhalfpos : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < N / 2)
      field_simp [ne_of_gt hhalfpos]
    · rw [GammaClosed, if_neg hEven]
      unfold gammaTerm
      have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
      rcases hOdd with ⟨M, hM⟩
      subst N
      have hhalf : (2 * M + 1) / 2 = M := by omega
      have hsub : (2 * M + 1) - (2 * M + 1) / 2 =
          ((2 * M + 1) + 1) / 2 := by omega
      have hupper : ((2 * M + 1) + 1) / 2 = M + 1 := by omega
      have hNm1 : (2 * M + 1) - 1 = 2 * M := by omega
      have hMpos : (0 : ℝ) < (M : ℝ) := by
        exact_mod_cast (by omega : 0 < M)
      rw [hsub, hhalf, hupper, hNm1]
      field_simp [ne_of_gt hMpos]
      push_cast
      ring

lemma harmonic_seven : harmonic 7 = (363 : ℝ) / 140 := by
  norm_num [harmonic, Finset.sum_Icc_succ_top]

lemma harmonic_ge_five_halves {N : ℕ} (hN : 7 ≤ N) :
    (5 : ℝ) / 2 < harmonic N := by
  have hsubset : Finset.Icc 1 7 ⊆ Finset.Icc 1 N := by
    intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have hmono : harmonic 7 ≤ harmonic N := by
    unfold harmonic
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j hjN hj7
    positivity
  rw [harmonic_seven] at hmono
  norm_num at hmono ⊢
  linarith

lemma Gamma_lt_even_upper {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) :
    Gamma N <
      2 * (N : ℝ) ^ 2 /
        (((N : ℝ) - 1) * (2 * (N : ℝ) - 1)) := by
  rw [Gamma_eq_closed hN, GammaClosed, if_pos hEven]
  rcases hEven with ⟨M, hM⟩
  subst N
  simp only [← two_mul] at hN ⊢
  have hM : 1 ≤ M := by omega
  have hsum := reciprocal_square_sum_lt
    (N := 2 * M) (r := M) hM (by omega : M < 2 * M)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  calc
    ((2 * M : ℕ) : ℝ) *
        (∑ ell ∈ Finset.Icc ((2 * M) / 2) (2 * M - 1),
          (1 : ℝ) / (ell : ℝ) ^ 2) <
      ((2 * M : ℕ) : ℝ) *
        (1 / ((M : ℝ) - 1 / 2) - 1 / (((2 * M : ℕ) : ℝ) - 1 / 2)) := by
      simpa [show (2 * M) / 2 = M by omega] using
        mul_lt_mul_of_pos_left hsum (by positivity : (0 : ℝ) < ((2 * M : ℕ) : ℝ))
    _ = 2 * (((2 * M : ℕ) : ℝ) ^ 2) /
        ((((2 * M : ℕ) : ℝ) - 1) *
          (2 * ((2 * M : ℕ) : ℝ) - 1)) := by
      push_cast
      have h2m1 : (0 : ℝ) < -1 + (M : ℝ) * 2 := by nlinarith
      have h4m1 : (0 : ℝ) < -1 + (M : ℝ) * 4 := by nlinarith
      have hprod : (0 : ℝ) < 1 - (M : ℝ) * 6 + (M : ℝ) ^ 2 * 8 := by
        nlinarith [mul_pos h2m1 h4m1]
      ring_nf
      field_simp [ne_of_gt hMpos, ne_of_gt h2m1, ne_of_gt h4m1,
        ne_of_gt hprod]
      ring_nf
      apply mul_left_cancel₀ (ne_of_gt h4m1)
      field_simp [ne_of_gt h4m1]
      ring

lemma Gamma_lt_odd_upper {N : ℕ} (hN : 3 ≤ N) (hOdd : Odd N) :
    Gamma N < 2 * ((N : ℝ) + 1) / (2 * (N : ℝ) - 1) := by
  have hNotEven : ¬ Even N := Nat.not_even_iff_odd.mpr hOdd
  rw [Gamma_eq_closed (by omega), GammaClosed, if_neg hNotEven]
  rcases hOdd with ⟨M, hM⟩
  subst N
  have hM : 1 ≤ M := by omega
  have hsum := reciprocal_square_sum_lt
    (N := 2 * M + 1) (r := M + 1) (by omega) (by omega)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hhalf : (2 * M + 1 + 1) / 2 = M + 1 := by omega
  have hNm1 : 2 * M + 1 - 1 = 2 * M := by omega
  rw [hhalf, hNm1]
  let C : ℝ :=
    ((2 * M + 1 : ℕ) : ℝ) * ((2 * M + 2 : ℕ) : ℝ) /
      ((2 * M : ℕ) : ℝ)
  change C * (∑ ell ∈ Finset.Icc (M + 1) (2 * M),
      (1 : ℝ) / (ell : ℝ) ^ 2) < _
  calc
    C * (∑ ell ∈ Finset.Icc (M + 1) (2 * M),
          (1 : ℝ) / (ell : ℝ) ^ 2) <
      C *
        (1 / (((M + 1 : ℕ) : ℝ) - 1 / 2) -
          1 / (((2 * M + 1 : ℕ) : ℝ) - 1 / 2)) := by
      apply mul_lt_mul_of_pos_left hsum
      dsimp [C]
      positivity
    _ = 2 * (((2 * M + 1 : ℕ) : ℝ) + 1) /
        (2 * ((2 * M + 1 : ℕ) : ℝ) - 1) := by
      dsimp [C]
      push_cast
      have h2mp1 : (0 : ℝ) < 1 + (M : ℝ) * 2 := by positivity
      have h4mp1 : (0 : ℝ) < 1 + (M : ℝ) * 4 := by positivity
      ring_nf
      field_simp [ne_of_gt hMpos, ne_of_gt h2mp1, ne_of_gt h4mp1]
      ring_nf

lemma harmonic_lt_natCast {N : ℕ} (hN : 2 ≤ N) : harmonic N < (N : ℝ) := by
  unfold harmonic
  have hle : ∀ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) ≤ 1 := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hj).1
    exact (div_le_one (by positivity : (0 : ℝ) < (j : ℝ))).mpr hj1
  have hstrict : ∃ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) < 1 := by
    refine ⟨2, ?_, by norm_num⟩
    simp
    omega
  calc
    (∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ)) <
        ∑ _j ∈ Finset.Icc 1 N, (1 : ℝ) :=
      Finset.sum_lt_sum hle hstrict
    _ = (N : ℝ) := by
      simp [Nat.card_Icc]

lemma one_add_epsilonBarber {N : ℕ} (hN : 2 ≤ N) :
    1 + epsilonBarber N =
      ((N : ℝ) - 1) / ((N : ℝ) - harmonic N) := by
  have hden : (0 : ℝ) < (N : ℝ) - harmonic N := by
    linarith [harmonic_lt_natCast hN]
  unfold epsilonBarber
  field_simp [ne_of_gt hden]
  ring

lemma even_upper_lt_barber_ratio {N : ℕ} (hN : 7 ≤ N) :
    2 * (N : ℝ) ^ 2 /
        (((N : ℝ) - 1) * (2 * (N : ℝ) - 1)) <
      ((N : ℝ) - 1) / ((N : ℝ) - harmonic N) := by
  have hNR : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hHlow := harmonic_ge_five_halves hN
  have hHhigh := harmonic_lt_natCast (by omega : 2 ≤ N)
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < 2 * (N : ℝ) - 1 := by linarith
  have hden1 : 0 < ((N : ℝ) - 1) * (2 * (N : ℝ) - 1) :=
    mul_pos hN1 hN2
  have hden2 : 0 < (N : ℝ) - harmonic N := by linarith
  rw [div_lt_div_iff₀ hden1 hden2]
  nlinarith

lemma odd_upper_lt_barber_ratio {N : ℕ} (hN : 7 ≤ N) :
    2 * ((N : ℝ) + 1) / (2 * (N : ℝ) - 1) <
      ((N : ℝ) - 1) / ((N : ℝ) - harmonic N) := by
  have hNR : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hHlow := harmonic_ge_five_halves hN
  have hHhigh := harmonic_lt_natCast (by omega : 2 ≤ N)
  have hden1 : 0 < 2 * (N : ℝ) - 1 := by linarith
  have hden2 : 0 < (N : ℝ) - harmonic N := by linarith
  rw [div_lt_div_iff₀ hden1 hden2]
  nlinarith

lemma gamma_strictly_improves_barber_large {N : ℕ} (hN : 7 ≤ N) :
    Gamma N < 1 + epsilonBarber N := by
  rw [one_add_epsilonBarber (by omega : 2 ≤ N)]
  by_cases hEven : Even N
  · exact (Gamma_lt_even_upper (by omega) hEven).trans
      (even_upper_lt_barber_ratio hN)
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    exact (Gamma_lt_odd_upper (by omega) hOdd).trans
      (odd_upper_lt_barber_ratio hN)

lemma gamma_strictly_improves_barber_small {N : ℕ}
    (hN3 : 3 ≤ N) (hN6 : N ≤ 6) :
    Gamma N < 1 + epsilonBarber N := by
  rw [Gamma_eq_closed (by omega)]
  interval_cases N <;>
    norm_num [GammaClosed, epsilonBarber, harmonic,
      Finset.sum_Icc_succ_top]

theorem gamma_strictly_improves_barber {N : ℕ} (hN : 3 ≤ N) :
    Gamma N < 1 + epsilonBarber N := by
  by_cases hN6 : N ≤ 6
  · exact gamma_strictly_improves_barber_small hN hN6
  · exact gamma_strictly_improves_barber_large (by omega)

/-- Error of the midpoint telescoping majorant for one reciprocal square. -/
def midpointError (ell : ℕ) : ℝ :=
  (1 / ((ell : ℝ) - 1 / 2) - 1 / ((ell : ℝ) + 1 / 2)) -
    1 / (ell : ℝ) ^ 2

lemma midpointError_nonneg {ell : ℕ} (hell : 1 ≤ ell) :
    0 ≤ midpointError ell := by
  unfold midpointError
  linarith [inv_sq_lt_telescope hell]

lemma midpointError_le {ell : ℕ} (hell : 1 ≤ ell) :
    midpointError ell ≤ (1 : ℝ) / (3 * (ell : ℝ) ^ 4) := by
  have hx : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hx0 : (0 : ℝ) < (ell : ℝ) := by linarith
  have hxm : 0 < (ell : ℝ) - 1 / 2 := by linarith
  have hxp : 0 < (ell : ℝ) + 1 / 2 := by linarith
  have hsq : 0 < (ell : ℝ) ^ 2 - 1 / 4 := by
    nlinarith [sq_nonneg ((ell : ℝ) - 1)]
  have htel :
      1 / ((ell : ℝ) - 1 / 2) - 1 / ((ell : ℝ) + 1 / 2) =
        1 / ((ell : ℝ) ^ 2 - 1 / 4) := by
    rw [div_sub_div _ _ (ne_of_gt hxm) (ne_of_gt hxp)]
    congr 1 <;> ring
  have hformula : midpointError ell =
      1 / (4 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2 - 1 / 4)) := by
    unfold midpointError
    rw [htel, div_sub_div _ _ (ne_of_gt hsq) (pow_ne_zero 2 (ne_of_gt hx0))]
    field_simp [ne_of_gt hx0, ne_of_gt hsq]
    ring
  rw [hformula]
  have hden1 : 0 < 4 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2 - 1 / 4) := by
    positivity
  have hden2 : 0 < 3 * (ell : ℝ) ^ 4 := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith [sq_nonneg ((ell : ℝ) ^ 2 - 1)]

/-- Telescoping midpoint approximation to a finite reciprocal-square sum. -/
def midpointSum (N r : ℕ) : ℝ :=
  1 / ((r : ℝ) - 1 / 2) - 1 / ((N : ℝ) - 1 / 2)

lemma midpointSum_sub_sum_eq {N r : ℕ} (hrN : r < N) :
    midpointSum N r -
        (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) =
      ∑ ell ∈ Finset.Icc r (N - 1), midpointError ell := by
  rw [midpointSum, ← telescope_sum_Icc hrN]
  unfold midpointError
  simp only [Finset.sum_sub_distrib]

lemma midpointSum_error_bounds {N r : ℕ} (hr : 1 ≤ r) (hrN : r < N) :
    0 ≤ midpointSum N r -
        (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) ∧
      midpointSum N r -
          (∑ ell ∈ Finset.Icc r (N - 1), (1 : ℝ) / (ell : ℝ) ^ 2) ≤
        ((N - r : ℕ) : ℝ) / (3 * (r : ℝ) ^ 4) := by
  rw [midpointSum_sub_sum_eq hrN]
  constructor
  · exact Finset.sum_nonneg fun ell hell =>
      midpointError_nonneg (hr.trans (Finset.mem_Icc.mp hell).1)
  · calc
      (∑ ell ∈ Finset.Icc r (N - 1), midpointError ell) ≤
          ∑ _ell ∈ Finset.Icc r (N - 1),
            ((1 : ℝ) / (3 * (r : ℝ) ^ 4)) := by
        apply Finset.sum_le_sum
        intro ell hell
        have hrEll : r ≤ ell := (Finset.mem_Icc.mp hell).1
        have hell1 : 1 ≤ ell := hr.trans hrEll
        refine (midpointError_le hell1).trans ?_
        apply one_div_le_one_div_of_le
        · positivity
        · have hcast : (r : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hrEll
          gcongr
      _ = ((N - r : ℕ) : ℝ) / (3 * (r : ℝ) ^ 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : (Finset.Icc r (N - 1)).card = N - r := by
          simp [Nat.card_Icc]
          omega
        rw [hcard]
        ring

lemma gamma_expansion_error_even_index (M : ℕ) (hM : 1 ≤ M) :
    |Gamma (2 * M) - (1 + 3 / (2 * ((2 * M : ℕ) : ℝ)))| ≤
      100 / (((2 * M : ℕ) : ℝ) ^ 2) := by
  let S : ℝ :=
    ∑ ell ∈ Finset.Icc M (2 * M - 1), (1 : ℝ) / (ell : ℝ) ^ 2
  let T : ℝ := midpointSum (2 * M) M
  let E : ℝ := T - S
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hErr := midpointSum_error_bounds (N := 2 * M) (r := M) hM (by omega)
  have hE0 : 0 ≤ E := by simpa [E, T, S] using hErr.1
  have hEupper : E ≤ ((2 * M - M : ℕ) : ℝ) / (3 * (M : ℝ) ^ 4) := by
    simpa [E, T, S] using hErr.2
  have hGamma : Gamma (2 * M) = ((2 * M : ℕ) : ℝ) * S := by
    rw [Gamma_eq_closed (by omega), GammaClosed,
      if_pos (show Even (2 * M) by exact ⟨M, by omega⟩)]
    simp only [show (2 * M) / 2 = M by omega]
    rfl
  let D : ℝ := ((2 * M : ℕ) : ℝ) * T -
    (1 + 3 / (2 * ((2 * M : ℕ) : ℝ)))
  have hDformula : D =
      (14 * (M : ℝ) - 3) /
        (4 * (M : ℝ) * (2 * (M : ℝ) - 1) * (4 * (M : ℝ) - 1)) := by
    dsimp [D, T, midpointSum]
    push_cast
    have h2m1 : (0 : ℝ) < 2 * (M : ℝ) - 1 := by
      have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have h4m1 : (0 : ℝ) < 4 * (M : ℝ) - 1 := by linarith
    field_simp [ne_of_gt hMpos, ne_of_gt h2m1, ne_of_gt h4m1]
    ring_nf
    have h4norm : -1 + (M : ℝ) * 4 ≠ 0 := by nlinarith
    apply mul_left_cancel₀ h4norm
    field_simp [h4norm]
    ring
  have hD0 : 0 ≤ D := by
    rw [hDformula]
    have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hnum : (0 : ℝ) ≤ 14 * (M : ℝ) - 3 := by linarith
    have h2m1 : (0 : ℝ) < 2 * (M : ℝ) - 1 := by linarith
    have h4m1 : (0 : ℝ) < 4 * (M : ℝ) - 1 := by linarith
    exact div_nonneg hnum (mul_nonneg (mul_nonneg (by positivity) h2m1.le) h4m1.le)
  have hDupper : D ≤ 10 / (M : ℝ) ^ 2 := by
    rw [hDformula]
    have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have h2m1 : (0 : ℝ) < 2 * (M : ℝ) - 1 := by linarith
    have h4m1 : (0 : ℝ) < 4 * (M : ℝ) - 1 := by linarith
    have hden : 0 < 4 * (M : ℝ) * (2 * (M : ℝ) - 1) *
        (4 * (M : ℝ) - 1) := mul_pos (mul_pos (by positivity) h2m1) h4m1
    have hM2 : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMpos
    rw [div_le_div_iff₀ hden hM2]
    nlinarith [sq_nonneg ((M : ℝ) - 1)]
  have hCEupper : ((2 * M : ℕ) : ℝ) * E ≤ 10 / (M : ℝ) ^ 2 := by
    have hcast : ((2 * M - M : ℕ) : ℝ) = (M : ℝ) := by
      congr 1
      omega
    rw [hcast] at hEupper
    calc
      ((2 * M : ℕ) : ℝ) * E ≤
          ((2 * M : ℕ) : ℝ) * ((M : ℝ) / (3 * (M : ℝ) ^ 4)) := by
        exact mul_le_mul_of_nonneg_left hEupper (by positivity)
      _ = 2 / (3 * (M : ℝ) ^ 2) := by
        push_cast
        field_simp [ne_of_gt hMpos]
      _ ≤ 10 / (M : ℝ) ^ 2 := by
        have hden1 : 0 < 3 * (M : ℝ) ^ 2 := by positivity
        have hden2 : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMpos
        rw [div_le_div_iff₀ hden1 hden2]
        nlinarith
  have hdecomp :
      Gamma (2 * M) - (1 + 3 / (2 * ((2 * M : ℕ) : ℝ))) =
        D - ((2 * M : ℕ) : ℝ) * E := by
    rw [hGamma]
    dsimp [D, E]
    ring
  rw [hdecomp, abs_le]
  constructor
  · have hscale : 10 / (M : ℝ) ^ 2 ≤
        100 / (((2 * M : ℕ) : ℝ) ^ 2) := by
      push_cast
      have hM2 : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMpos
      rw [div_le_div_iff₀ hM2 (by positivity : (0 : ℝ) < (2 * (M : ℝ)) ^ 2)]
      nlinarith
    nlinarith
  · have hscale : 10 / (M : ℝ) ^ 2 ≤
        100 / (((2 * M : ℕ) : ℝ) ^ 2) := by
      push_cast
      have hM2 : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMpos
      rw [div_le_div_iff₀ hM2 (by positivity : (0 : ℝ) < (2 * (M : ℝ)) ^ 2)]
      nlinarith
    have hCE0 : 0 ≤ ((2 * M : ℕ) : ℝ) * E :=
      mul_nonneg (by positivity) hE0
    nlinarith

lemma gamma_expansion_error_odd_index (M : ℕ) (hM : 1 ≤ M) :
    |Gamma (2 * M + 1) - (1 + 3 / (2 * ((2 * M + 1 : ℕ) : ℝ)))| ≤
      100 / (((2 * M + 1 : ℕ) : ℝ) ^ 2) := by
  let S : ℝ :=
    ∑ ell ∈ Finset.Icc (M + 1) (2 * M), (1 : ℝ) / (ell : ℝ) ^ 2
  let T : ℝ := midpointSum (2 * M + 1) (M + 1)
  let E : ℝ := T - S
  let C : ℝ :=
    ((2 * M + 1 : ℕ) : ℝ) * ((2 * M + 2 : ℕ) : ℝ) /
      ((2 * M : ℕ) : ℝ)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hErr := midpointSum_error_bounds
    (N := 2 * M + 1) (r := M + 1) (by omega) (by omega)
  have hE0 : 0 ≤ E := by simpa [E, T, S] using hErr.1
  have hEupper : E ≤
      ((2 * M + 1 - (M + 1) : ℕ) : ℝ) /
        (3 * ((M + 1 : ℕ) : ℝ) ^ 4) := by
    simpa [E, T, S] using hErr.2
  have hOdd : Odd (2 * M + 1) := ⟨M, rfl⟩
  have hGamma : Gamma (2 * M + 1) = C * S := by
    rw [Gamma_eq_closed (by omega), GammaClosed,
      if_neg (Nat.not_even_iff_odd.mpr hOdd)]
    simp only [show (2 * M + 1 + 1) / 2 = M + 1 by omega,
      show 2 * M + 1 - 1 = 2 * M by omega]
    rfl
  have hCT : C * T =
      4 * ((M : ℝ) + 1) / (4 * (M : ℝ) + 1) := by
    dsimp [C, T, midpointSum]
    push_cast
    field_simp [ne_of_gt hMpos]
    ring_nf
    have h2norm : 1 + (M : ℝ) * 2 ≠ 0 := by positivity
    have h4norm : 1 + (M : ℝ) * 4 ≠ 0 := by positivity
    apply mul_left_cancel₀ (mul_ne_zero h2norm h4norm)
    field_simp [h2norm, h4norm]
    ring
  let D : ℝ := C * T -
    (1 + 3 / (2 * ((2 * M + 1 : ℕ) : ℝ)))
  have hDformula : D =
      3 / ((4 * (M : ℝ) + 1) * (4 * (M : ℝ) + 2)) := by
    dsimp only [D]
    rw [hCT]
    push_cast
    field_simp
    ring
  have hD0 : 0 ≤ D := by
    rw [hDformula]
    positivity
  have hDupper : D ≤ 10 / (M : ℝ) ^ 2 := by
    rw [hDformula]
    have hden1 : 0 < (4 * (M : ℝ) + 1) * (4 * (M : ℝ) + 2) := by positivity
    have hden2 : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMpos
    rw [div_le_div_iff₀ hden1 hden2]
    nlinarith
  have hCEupper : C * E ≤ 10 / (M : ℝ) ^ 2 := by
    have hcount : ((2 * M + 1 - (M + 1) : ℕ) : ℝ) = (M : ℝ) := by
      congr 1
      omega
    rw [hcount] at hEupper
    calc
      C * E ≤ C * ((M : ℝ) / (3 * ((M + 1 : ℕ) : ℝ) ^ 4)) := by
        apply mul_le_mul_of_nonneg_left hEupper
        dsimp [C]
        positivity
      _ = ((2 * (M : ℝ) + 1) / (3 * ((M : ℝ) + 1) ^ 3)) := by
        dsimp [C]
        push_cast
        field_simp [ne_of_gt hMpos, ne_of_gt (by positivity : (0 : ℝ) < (M : ℝ) + 1)]
      _ ≤ 10 / (M : ℝ) ^ 2 := by
        have hden1 : 0 < 3 * ((M : ℝ) + 1) ^ 3 := by positivity
        have hden2 : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMpos
        rw [div_le_div_iff₀ hden1 hden2]
        nlinarith [sq_nonneg ((M : ℝ) - 1),
          mul_nonneg (sq_nonneg (M : ℝ)) (show (0 : ℝ) ≤ (M : ℝ) by positivity)]
  have hdecomp :
      Gamma (2 * M + 1) - (1 + 3 / (2 * ((2 * M + 1 : ℕ) : ℝ))) =
        D - C * E := by
    rw [hGamma]
    dsimp [D, E]
    ring
  rw [hdecomp, abs_le]
  constructor
  · have hscale : 10 / (M : ℝ) ^ 2 ≤
        100 / (((2 * M + 1 : ℕ) : ℝ) ^ 2) := by
      push_cast
      have hden1 : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMpos
      have hden2 : 0 < (2 * (M : ℝ) + 1) ^ 2 := by positivity
      rw [div_le_div_iff₀ hden1 hden2]
      have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith [sq_nonneg ((M : ℝ) - 1)]
    nlinarith
  · have hscale : 10 / (M : ℝ) ^ 2 ≤
        100 / (((2 * M + 1 : ℕ) : ℝ) ^ 2) := by
      push_cast
      have hden1 : 0 < (M : ℝ) ^ 2 := sq_pos_of_pos hMpos
      have hden2 : 0 < (2 * (M : ℝ) + 1) ^ 2 := by positivity
      rw [div_le_div_iff₀ hden1 hden2]
      have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith [sq_nonneg ((M : ℝ) - 1)]
    have hCE0 : 0 ≤ C * E := by
      apply mul_nonneg _ hE0
      dsimp [C]
      positivity
    nlinarith

theorem gamma_expansion_error {N : ℕ} (hN : 3 ≤ N) :
    |Gamma N - (1 + 3 / (2 * (N : ℝ)))| ≤
      100 / ((N : ℝ) ^ 2) := by
  by_cases hEven : Even N
  · rcases hEven with ⟨M, hM⟩
    subst N
    have hMpos : 1 ≤ M := by omega
    simpa [two_mul] using gamma_expansion_error_even_index M hMpos
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨M, hM⟩
    subst N
    exact gamma_expansion_error_odd_index M (by omega)

theorem gamma_asymptotic_expansion :
    (fun N : ℕ => Gamma N - (1 + 3 / (2 * (N : ℝ))))
      =O[Filter.atTop] (fun N : ℕ => (1 : ℝ) / ((N : ℝ) ^ 2)) := by
  refine Asymptotics.IsBigO.of_bound 100 <|
    Filter.eventually_atTop.mpr ⟨3, fun N hN => ?_⟩
  have hpoint := gamma_expansion_error hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / ((N : ℝ) ^ 2))]
  simpa [mul_div_assoc] using hpoint

/-- A closed constructor for the inflation-factor analysis package. -/
def gammaAnalyticInputs : GammaAnalyticInputs where
  closed_formula := Gamma_eq_closed
  asymptotic_expansion := gamma_asymptotic_expansion
  strict_barber_comparison := gamma_strictly_improves_barber

end ExchangeableHoeffding
