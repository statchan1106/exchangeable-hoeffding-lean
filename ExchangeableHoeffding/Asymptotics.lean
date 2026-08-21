import ExchangeableHoeffding.GammaClosedForm
import Mathlib.Analysis.Asymptotics.Lemmas

namespace SharpSerfling.ExchangeableHoeffding

open Filter Topology Asymptotics

/-- A term in the half-integer telescoping approximation to `ℓ⁻²`. -/
noncomputable def halfStep (ell : ℕ) : ℝ :=
  1 / ((ell : ℝ) - 1 / 2) - 1 / ((ell : ℝ) + 1 / 2)

noncomputable def halfError (ell : ℕ) : ℝ :=
  halfStep ell - 1 / (ell : ℝ) ^ 2

/-- The half-integer approximation error is positive and fourth order. -/
theorem halfError_bounds {ell : ℕ} (hell : 1 ≤ ell) :
    0 ≤ halfError ell ∧ halfError ell ≤ 1 / (ell : ℝ) ^ 4 := by
  have hx : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hx0 : (0 : ℝ) < (ell : ℝ) := by positivity
  have hxm : (0 : ℝ) < (ell : ℝ) - 1 / 2 := by linarith
  have hxp : (0 : ℝ) < (ell : ℝ) + 1 / 2 := by linarith
  have hd : (0 : ℝ) < (ell : ℝ) ^ 2 - 1 / 4 := by nlinarith
  have hstep : halfStep ell = 1 / ((ell : ℝ) ^ 2 - 1 / 4) := by
    unfold halfStep
    rw [div_sub_div (1 : ℝ) (1 : ℝ) hxm.ne' hxp.ne']
    congr 1 <;> ring
  have hformula : halfError ell =
      1 / (4 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2 - 1 / 4)) := by
    unfold halfError
    rw [hstep, div_sub_div (1 : ℝ) (1 : ℝ) hd.ne'
      (pow_ne_zero 2 hx0.ne')]
    field_simp [hx0.ne', hxm.ne', hxp.ne', hd.ne']
    ring
  rw [hformula]
  constructor
  · positivity
  · rw [div_le_div_iff₀
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hx0)) hd)
      (pow_pos hx0 4)]
    nlinarith [sq_nonneg ((ell : ℝ) ^ 2 - 1)]

/-- The half-steps telescope exactly over the inverse-square tail's index
range. -/
theorem sum_halfStep {N s : ℕ} (hsN : s ≤ N - 1) :
    ∑ j ∈ Finset.range s, halfStep (N - 1 - j) =
      1 / ((N : ℝ) - (s : ℝ) - 1 / 2) -
        1 / ((N : ℝ) - 1 / 2) := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hih := ih (by omega : s ≤ N - 1)
      have hcast : ((N - 1 - s : ℕ) : ℝ) =
          (N : ℝ) - (s : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : s ≤ N - 1),
          Nat.cast_sub (by omega : 1 ≤ N)]
        push_cast
        ring
      rw [Finset.sum_range_succ, hih]
      unfold halfStep
      rw [hcast]
      push_cast
      ring

theorem telescoping_sub_tail_eq_sum_error {N s : ℕ} (hsN : s ≤ N - 1) :
    (1 / ((N : ℝ) - (s : ℝ) - 1 / 2) -
        1 / ((N : ℝ) - 1 / 2)) - inverseSquareTail N s =
      ∑ j ∈ Finset.range s, halfError (N - 1 - j) := by
  rw [← sum_halfStep hsN]
  unfold inverseSquareTail halfError
  rw [← Finset.sum_sub_distrib]

/-- Quantitative accumulated remainder. -/
theorem telescoping_error_bound {N s : ℕ} (hs0 : 1 ≤ s)
    (hsN : s ≤ N - 1) :
    0 ≤ (1 / ((N : ℝ) - (s : ℝ) - 1 / 2) -
        1 / ((N : ℝ) - 1 / 2)) - inverseSquareTail N s ∧
      (1 / ((N : ℝ) - (s : ℝ) - 1 / 2) -
          1 / ((N : ℝ) - 1 / 2)) - inverseSquareTail N s ≤
        (s : ℝ) / ((N - s : ℕ) : ℝ) ^ 4 := by
  have hNs : 1 ≤ N - s := by omega
  rw [telescoping_sub_tail_eq_sum_error hsN]
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    apply (halfError_bounds (ell := N - 1 - j) (by
      have hj' : j < s := Finset.mem_range.mp hj
      omega)).1
  · calc
      ∑ j ∈ Finset.range s, halfError (N - 1 - j) ≤
          ∑ _j ∈ Finset.range s, 1 / (((N - s : ℕ) : ℝ) ^ 4) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j < s := Finset.mem_range.mp hj
        have hell : 1 ≤ N - 1 - j := by omega
        calc
          halfError (N - 1 - j) ≤ 1 / (((N - 1 - j : ℕ) : ℝ) ^ 4) :=
            (halfError_bounds hell).2
          _ ≤ 1 / (((N - s : ℕ) : ℝ) ^ 4) := by
            have hcast : (((N - s : ℕ) : ℝ)) ≤
                ((N - 1 - j : ℕ) : ℝ) := by exact_mod_cast (by omega : N - s ≤ N - 1 - j)
            have hpos : (0 : ℝ) < ((N - s : ℕ) : ℝ) := by positivity
            apply one_div_le_one_div_of_le (pow_pos hpos 4)
            exact pow_le_pow_left₀ (by positivity) hcast 4
      _ = (s : ℝ) / (((N - s : ℕ) : ℝ) ^ 4) := by
        simp [div_eq_mul_inv]

/-- Quantitative even-parity version of the expansion. -/
theorem Gamma_even_expansion_bound {q : ℕ} (hq : 0 < q) :
    |Gamma (2 * q) - (1 + 3 / (2 * ((2 * q : ℕ) : ℝ)))| ≤
      4 / (q : ℝ) ^ 2 := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
  let P : ℝ := 1 / (((2 * q : ℕ) : ℝ) - (q : ℝ) - 1 / 2) -
    1 / (((2 * q : ℕ) : ℝ) - 1 / 2)
  let e : ℝ := P - inverseSquareTail (2 * q) q
  have herr := telescoping_error_bound (N := 2 * q) (s := q)
    (by omega) (by omega)
  have hsub : 2 * q - q = q := by omega
  rw [hsub] at herr
  have he0 : 0 ≤ e := by simpa [e, P] using herr.1
  have heU : e ≤ (q : ℝ) / (q : ℝ) ^ 4 := by
    simpa [e, P] using herr.2
  let E : ℝ := 2 * (((2 * q : ℕ) : ℝ) ^ 2) /
    ((((2 * q : ℕ) : ℝ) - 1) *
      (2 * ((2 * q : ℕ) : ℝ) - 1))
  let B : ℝ := 1 + 3 / (2 * ((2 * q : ℕ) : ℝ))
  have hEP : ((2 * q : ℕ) : ℝ) * P = E := by
    dsimp [P, E]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hA : (0 : ℝ) < 2 * (q : ℝ) - (q : ℝ) - 1 / 2 := by linarith
    have hB : (0 : ℝ) < 2 * (q : ℝ) - 1 / 2 := by linarith
    rw [div_sub_div (1 : ℝ) (1 : ℝ) hA.ne' hB.ne']
    field_simp [show (q : ℝ) ≠ 0 by positivity,
      show 2 * (q : ℝ) - 1 ≠ 0 by nlinarith,
      show 4 * (q : ℝ) - 1 ≠ 0 by nlinarith]
    field_simp [show 2 ^ 2 * (q : ℝ) - 1 ≠ 0 by nlinarith,
      show 2 * (q : ℝ) * (2 - 1) - 1 ≠ 0 by nlinarith]
    ring
  have hGamma : Gamma (2 * q) = E - ((2 * q : ℕ) : ℝ) * e := by
    rw [Gamma_closedForm_even (by omega) ⟨q, by omega⟩]
    have hhalf : 2 * q / 2 = q := by omega
    rw [hhalf]
    dsimp [e]
    rw [mul_sub, hEP]
    ring
  have hdEq : E - B =
      (14 * (q : ℝ) - 3) /
        (4 * (q : ℝ) * (2 * (q : ℝ) - 1) * (4 * (q : ℝ) - 1)) := by
    have hEsimp : E = 8 * (q : ℝ) ^ 2 /
        ((2 * (q : ℝ) - 1) * (4 * (q : ℝ) - 1)) := by
      dsimp [E]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      congr 1 <;> ring
    have hBsimp : B = 1 + 3 / (4 * (q : ℝ)) := by
      dsimp [B]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      congr 2 <;> ring
    rw [hEsimp, hBsimp]
    field_simp [show (q : ℝ) ≠ 0 by positivity,
      show 2 * (q : ℝ) - 1 ≠ 0 by nlinarith,
      show 4 * (q : ℝ) - 1 ≠ 0 by nlinarith]
    have hD : ((q : ℝ) * 2 - 1) * ((q : ℝ) * 4 - 1) ≠ 0 :=
      mul_ne_zero (by nlinarith) (by nlinarith)
    have hinv := inv_mul_cancel₀ hD
    simp only [div_eq_mul_inv]
    nlinarith [hinv]
  have hd0 : 0 ≤ E - B := by
    rw [hdEq]
    apply div_nonneg (by nlinarith)
    exact mul_nonneg (mul_nonneg (by positivity) (by nlinarith)) (by nlinarith)
  have hdU : E - B ≤ 2 / (q : ℝ) ^ 2 := by
    rw [hdEq]
    have hden : 0 < 4 * (q : ℝ) * (2 * (q : ℝ) - 1) *
        (4 * (q : ℝ) - 1) := by
      exact mul_pos (mul_pos (by positivity) (by nlinarith)) (by nlinarith)
    rw [div_le_div_iff₀ hden (sq_pos_of_pos hq0)]
    have hpoly : 0 ≤ 50 * (q : ℝ) ^ 2 - 45 * (q : ℝ) + 8 := by
      nlinarith [mul_nonneg hq0.le (sub_nonneg.mpr hqR)]
    nlinarith [mul_nonneg hq0.le hpoly]
  have hloss0 : 0 ≤ ((2 * q : ℕ) : ℝ) * e :=
    mul_nonneg (by positivity) he0
  have hlossU : ((2 * q : ℕ) : ℝ) * e ≤ 2 / (q : ℝ) ^ 2 := by
    calc
      ((2 * q : ℕ) : ℝ) * e ≤
          ((2 * q : ℕ) : ℝ) * ((q : ℝ) / (q : ℝ) ^ 4) := by
        gcongr
      _ = 2 / (q : ℝ) ^ 2 := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        field_simp [hq0.ne']
  rw [hGamma]
  rw [show E - ((2 * q : ℕ) : ℝ) * e -
      (1 + 3 / (2 * ((2 * q : ℕ) : ℝ))) =
        (E - B) - ((2 * q : ℕ) : ℝ) * e by dsimp [B]; ring]
  rw [show 4 / (q : ℝ) ^ 2 =
      2 / (q : ℝ) ^ 2 + 2 / (q : ℝ) ^ 2 by ring]
  rw [abs_le]
  constructor <;> linarith

/-- Quantitative odd-parity version of the expansion. -/
theorem Gamma_odd_expansion_bound {q : ℕ} (hq : 0 < q) :
    |Gamma (2 * q + 1) -
        (1 + 3 / (2 * ((2 * q + 1 : ℕ) : ℝ)))| ≤
      11 / (q : ℝ) ^ 2 := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
  let P : ℝ := 1 / (((2 * q + 1 : ℕ) : ℝ) - (q : ℝ) - 1 / 2) -
    1 / (((2 * q + 1 : ℕ) : ℝ) - 1 / 2)
  let e : ℝ := P - inverseSquareTail (2 * q + 1) q
  have herr := telescoping_error_bound (N := 2 * q + 1) (s := q)
    (by omega) (by omega)
  have hsub : 2 * q + 1 - q = q + 1 := by omega
  rw [hsub] at herr
  have he0 : 0 ≤ e := by simpa [e, P] using herr.1
  have heU : e ≤ (q : ℝ) / ((q + 1 : ℕ) : ℝ) ^ 4 := by
    simpa [e, P] using herr.2
  let A : ℝ := ((2 * q + 1 : ℕ) : ℝ) *
    (((2 * q + 1 : ℕ) : ℝ) + 1) /
      (((2 * q + 1 : ℕ) : ℝ) - 1)
  let E : ℝ := 2 * (((2 * q + 1 : ℕ) : ℝ) + 1) /
    (2 * ((2 * q + 1 : ℕ) : ℝ) - 1)
  let B : ℝ := 1 + 3 / (2 * ((2 * q + 1 : ℕ) : ℝ))
  have hAP : A * P = E := by
    dsimp [A, P, E]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    have hA : (0 : ℝ) < 2 * (q : ℝ) + 1 - (q : ℝ) - 1 / 2 := by linarith
    have hB : (0 : ℝ) < 2 * (q : ℝ) + 1 - 1 / 2 := by linarith
    rw [div_sub_div (1 : ℝ) (1 : ℝ) hA.ne' hB.ne']
    field_simp [show (q : ℝ) ≠ 0 by positivity,
      show 2 * (q : ℝ) + 1 ≠ 0 by positivity,
      show 4 * (q : ℝ) + 1 ≠ 0 by positivity]
    field_simp [show 2 * (2 * (q : ℝ) + 1) - 1 ≠ 0 by nlinarith,
      show 2 * (2 * (q : ℝ) + 1 - (q : ℝ)) - 1 ≠ 0 by nlinarith]
    ring
  have hGamma : Gamma (2 * q + 1) = E - A * e := by
    rw [Gamma_closedForm_odd (by omega) ⟨q, by omega⟩]
    have hhalf : (2 * q + 1) / 2 = q := by omega
    rw [hhalf]
    dsimp [e, A]
    rw [mul_sub, hAP]
    ring
  have hdEq : E - B = 3 /
      (2 * (((2 * q + 1 : ℕ) : ℝ)) *
        (2 * (((2 * q + 1 : ℕ) : ℝ)) - 1)) := by
    dsimp [E, B]
    have hN0 : (((2 * q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have h2N : 2 * (((2 * q + 1 : ℕ) : ℝ)) - 1 ≠ 0 := by
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      nlinarith
    field_simp [hN0, h2N]
    ring
  have hd0 : 0 ≤ E - B := by
    rw [hdEq]
    apply div_nonneg (by norm_num)
    exact mul_nonneg (by positivity) (by
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      nlinarith)
  have hdU : E - B ≤ 1 / (q : ℝ) ^ 2 := by
    rw [hdEq]
    have hden : 0 < 2 * (((2 * q + 1 : ℕ) : ℝ)) *
        (2 * (((2 * q + 1 : ℕ) : ℝ)) - 1) := by
      apply mul_pos (by positivity)
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      nlinarith
    rw [div_le_div_iff₀ hden (sq_pos_of_pos hq0)]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    nlinarith [sq_nonneg (q : ℝ)]
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hden : (0 : ℝ) < (((2 * q + 1 : ℕ) : ℝ) - 1) := by
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      nlinarith
    exact div_nonneg (mul_nonneg (by positivity) (by positivity)) hden.le
  have hloss0 : 0 ≤ A * e := mul_nonneg hA0 he0
  have hlossU : A * e ≤ 10 / (q : ℝ) ^ 2 := by
    calc
      A * e ≤ A * ((q : ℝ) / ((q + 1 : ℕ) : ℝ) ^ 4) := by
        gcongr
      _ ≤ 10 / (q : ℝ) ^ 2 := by
        dsimp [A]
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
        have hden1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
        rw [show 2 * (q : ℝ) + 1 - 1 = 2 * (q : ℝ) by ring]
        field_simp [hq0.ne', hden1.ne']
        have hpoly : 0 ≤ 8 * (q : ℝ) ^ 3 + 29 * (q : ℝ) ^ 2 +
            30 * (q : ℝ) + 10 := by positivity
        nlinarith [mul_nonneg hden1.le hpoly]
  rw [hGamma]
  rw [show E - A * e - (1 + 3 / (2 * ((2 * q + 1 : ℕ) : ℝ))) =
      (E - B) - A * e by dsimp [B]; ring]
  rw [show 11 / (q : ℝ) ^ 2 =
      1 / (q : ℝ) ^ 2 + 10 / (q : ℝ) ^ 2 by ring]
  rw [abs_le]
  constructor <;> linarith

/-- The paper's asymptotic statement in Lean's filter-based `IsBigO`
notation: `Γ_N = 1 + 3/(2N) + O(N⁻²)`. -/
theorem Gamma_asymptotic :
    (fun N : ℕ ↦ Gamma N - (1 + 3 / (2 * (N : ℝ)))) =O[atTop]
      (fun N : ℕ ↦ 1 / (N : ℝ) ^ 2) := by
  apply IsBigO.of_bound 100
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
  simp only [Real.norm_eq_abs]
  by_cases hEven : Even N
  · rcases hEven with ⟨q, rfl⟩
    have hq : 0 < q := by omega
    have h := Gamma_even_expansion_bound hq
    rw [abs_of_pos (by positivity : 0 < 1 / (((q + q : ℕ) : ℝ) ^ 2))]
    calc
      |Gamma (q + q) - (1 + 3 / (2 * ((q + q : ℕ) : ℝ)))| ≤
          4 / (q : ℝ) ^ 2 := by simpa [two_mul] using h
      _ = 16 * (1 / (((q + q : ℕ) : ℝ) ^ 2)) := by
        norm_num only [Nat.cast_add]
        field_simp [show (q : ℝ) ≠ 0 by positivity]
        ring
      _ ≤ 100 * (1 / (((q + q : ℕ) : ℝ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨q, rfl⟩
    have hq : 0 < q := by omega
    have h := Gamma_odd_expansion_bound hq
    rw [abs_of_pos (by positivity : 0 < 1 / (((2 * q + 1 : ℕ) : ℝ) ^ 2))]
    calc
      |Gamma (2 * q + 1) -
          (1 + 3 / (2 * ((2 * q + 1 : ℕ) : ℝ)))| ≤
          11 / (q : ℝ) ^ 2 := h
      _ ≤ 100 * (1 / (((2 * q + 1 : ℕ) : ℝ) ^ 2)) := by
        have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
        field_simp [show (q : ℝ) ≠ 0 by positivity,
          show ((2 * q + 1 : ℕ) : ℝ) ≠ 0 by positivity]
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
        nlinarith [sq_nonneg ((q : ℝ) - 1)]

end SharpSerfling.ExchangeableHoeffding
