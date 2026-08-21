import ExchangeableHoeffding.GammaClosedForm

namespace SharpSerfling.ExchangeableHoeffding

/-- The harmonic number is strictly below `N` once `N ≥ 2`; this makes
Barber's denominator positive. -/
theorem harmonicNumber_lt_nat {N : ℕ} (hN : 2 ≤ N) :
    harmonicNumber N < (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [harmonicNumber, Finset.sum_range_succ]
  | succ N hN ih =>
      have hterm : 1 / (((N + 1 : ℕ) : ℝ)) ≤ 1 := by
        have hcast : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ N + 1 by omega)
        exact (div_le_one (by exact_mod_cast (show 0 < N + 1 by omega) :
          (0 : ℝ) < ((N + 1 : ℕ) : ℝ))).2 hcast
      rw [harmonicNumber, Finset.sum_range_succ]
      change harmonicNumber N + 1 / (((N + 1 : ℕ) : ℝ)) < ((N + 1 : ℕ) : ℝ)
      simpa only [Nat.cast_add, Nat.cast_one] using add_lt_add_of_lt_of_le ih hterm

theorem one_add_barberEpsilon {N : ℕ} (hN : 2 ≤ N) :
    1 + barberEpsilon N =
      ((N : ℝ) - 1) / ((N : ℝ) - harmonicNumber N) := by
  have hden : (N : ℝ) - harmonicNumber N ≠ 0 :=
    ne_of_gt (sub_pos.mpr (harmonicNumber_lt_nat hN))
  unfold barberEpsilon
  field_simp [hden]
  ring

/-- Monotonicity of the finite harmonic sums. -/
theorem harmonicNumber_mono {M N : ℕ} (hMN : M ≤ N) :
    harmonicNumber M ≤ harmonicNumber N := by
  unfold harmonicNumber
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN)
  intro i hiN hiM
  positivity

theorem harmonicNumber_ge_five_halves {N : ℕ} (hN : 7 ≤ N) :
    (5 / 2 : ℝ) ≤ harmonicNumber N := by
  have hmono := harmonicNumber_mono hN
  have h7 : harmonicNumber 7 = (363 / 140 : ℝ) := by
    norm_num [harmonicNumber, Finset.sum_range_succ]
  rw [h7] at hmono
  exact (by norm_num : (5 / 2 : ℝ) ≤ 363 / 140).trans hmono

theorem Gamma_le_even_rational {N : ℕ} (hN : 2 ≤ N)
    (hEven : Even N) :
    Gamma N ≤ 2 * (N : ℝ) ^ 2 /
      (((N : ℝ) - 1) * (2 * (N : ℝ) - 1)) := by
  rcases hEven with ⟨q, rfl⟩
  have hq : 0 < q := by omega
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have htail := inverseSquareTail_upper_half
    (N := q + q) (s := (q + q) / 2) (by omega)
  have hhalf : (q + q) / 2 = q := by omega
  rw [hhalf] at htail
  rw [Gamma_closedForm_even (by omega) ⟨q, rfl⟩, hhalf]
  calc
    ((q + q : ℕ) : ℝ) * inverseSquareTail (q + q) q ≤
        ((q + q : ℕ) : ℝ) *
          (1 / (((q + q : ℕ) : ℝ) - (q : ℝ) - 1 / 2) -
            1 / (((q + q : ℕ) : ℝ) - 1 / 2)) := by
      gcongr
    _ = 2 * ((q + q : ℕ) : ℝ) ^ 2 /
        ((((q + q : ℕ) : ℝ) - 1) *
          (2 * ((q + q : ℕ) : ℝ) - 1)) := by
      have hA : (0 : ℝ) <
          ((q + q : ℕ) : ℝ) - (q : ℝ) - 1 / 2 := by
        push_cast
        linarith
      have hB : (0 : ℝ) < ((q + q : ℕ) : ℝ) - 1 / 2 := by
        push_cast
        linarith
      rw [div_sub_div (1 : ℝ) (1 : ℝ) hA.ne' hB.ne']
      norm_num only [Nat.cast_add]
      field_simp [hA.ne', hB.ne', show (q : ℝ) ≠ 0 by positivity,
        show ((q + q : ℕ) : ℝ) - 1 ≠ 0 by
          push_cast; nlinarith,
        show 2 * ((q + q : ℕ) : ℝ) - 1 ≠ 0 by
          push_cast; nlinarith]
      ring

theorem Gamma_le_odd_rational {N : ℕ} (hN : 3 ≤ N)
    (hOdd : Odd N) :
    Gamma N ≤ 2 * ((N : ℝ) + 1) / (2 * (N : ℝ) - 1) := by
  rcases hOdd with ⟨q, rfl⟩
  have hq : 0 < q := by omega
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have htail := inverseSquareTail_upper_half
    (N := 2 * q + 1) (s := (2 * q + 1) / 2) (by omega)
  have hhalf : (2 * q + 1) / 2 = q := by omega
  rw [hhalf] at htail
  rw [Gamma_closedForm_odd (by omega) ⟨q, by omega⟩, hhalf]
  calc
    (((2 * q + 1 : ℕ) : ℝ) * (((2 * q + 1 : ℕ) : ℝ) + 1) /
          (((2 * q + 1 : ℕ) : ℝ) - 1)) *
        inverseSquareTail (2 * q + 1) q ≤
      (((2 * q + 1 : ℕ) : ℝ) * (((2 * q + 1 : ℕ) : ℝ) + 1) /
          (((2 * q + 1 : ℕ) : ℝ) - 1)) *
        (1 / (((2 * q + 1 : ℕ) : ℝ) - (q : ℝ) - 1 / 2) -
          1 / (((2 * q + 1 : ℕ) : ℝ) - 1 / 2)) := by
        apply mul_le_mul_of_nonneg_left htail
        have hden : (0 : ℝ) < (((2 * q + 1 : ℕ) : ℝ) - 1) := by
          push_cast
          linarith
        positivity
    _ = 2 * (((2 * q + 1 : ℕ) : ℝ) + 1) /
          (2 * ((2 * q + 1 : ℕ) : ℝ) - 1) := by
      have hA : (0 : ℝ) <
          ((2 * q + 1 : ℕ) : ℝ) - (q : ℝ) - 1 / 2 := by
        push_cast
        linarith
      have hB : (0 : ℝ) < ((2 * q + 1 : ℕ) : ℝ) - 1 / 2 := by
        push_cast
        linarith
      rw [div_sub_div (1 : ℝ) (1 : ℝ) hA.ne' hB.ne']
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      field_simp [hA.ne', hB.ne', show (q : ℝ) ≠ 0 by positivity,
        show ((2 * q + 1 : ℕ) : ℝ) - 1 ≠ 0 by
          push_cast; nlinarith,
        show 2 * ((2 * q + 1 : ℕ) : ℝ) - 1 ≠ 0 by
          push_cast; nlinarith,
        show 1 + (q : ℝ) * 6 + (q : ℝ) ^ 2 * 8 ≠ 0 by positivity,
        show 1 + (q : ℝ) * 4 ≠ 0 by positivity]
      field_simp [show 2 * (2 * (q : ℝ) + 1) - 1 ≠ 0 by nlinarith,
        show 2 * (2 * (q : ℝ) + 1 - (q : ℝ)) - 1 ≠ 0 by nlinarith]
      ring

theorem lemma_5_large {N : ℕ} (hN : 7 ≤ N) :
    Gamma N < 1 + barberEpsilon N := by
  have hH := harmonicNumber_ge_five_halves hN
  have hden : 0 < (N : ℝ) - harmonicNumber N :=
    sub_pos.mpr (harmonicNumber_lt_nat (by omega))
  rw [one_add_barberEpsilon (by omega)]
  by_cases hEven : Even N
  · apply lt_of_le_of_lt (Gamma_le_even_rational (by omega) hEven)
    rw [div_lt_div_iff₀ ?_ hden]
    · have hNR : (7 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [mul_nonneg (sq_nonneg ((N : ℝ))) (sub_nonneg.mpr hH)]
    · have hNR : (7 : ℝ) ≤ N := by exact_mod_cast hN
      exact mul_pos (by linarith) (by linarith)
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    apply lt_of_le_of_lt (Gamma_le_odd_rational (by omega) hOdd)
    rw [div_lt_div_iff₀ ?_ hden]
    · have hNR : (7 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
        (sub_nonneg.mpr hH)]
    · have hNR : (7 : ℝ) ≤ N := by exact_mod_cast hN
      linarith

/-- **Lemma 5.**  Strict improvement over Barber for every `N ≥ 3`. -/
theorem lemma_5 {N : ℕ} (hN : 3 ≤ N) :
    Gamma N < 1 + barberEpsilon N := by
  by_cases hlarge : 7 ≤ N
  · exact lemma_5_large hlarge
  · interval_cases N
    all_goals
      rw [Gamma_eq_lastTerm (by omega)]
      norm_num [gammaTerm, inverseSquareTail, barberEpsilon,
        harmonicNumber, Finset.sum_range_succ]

theorem lemma_5_eq_two : Gamma 2 = 1 + barberEpsilon 2 := by
  norm_num [Gamma, gammaTerm, inverseSquareTail, barberEpsilon,
    harmonicNumber, Finset.sum_range_succ]

end SharpSerfling.ExchangeableHoeffding
