import ExchangeableHoeffding.GammaBasic

namespace SharpSerfling.ExchangeableHoeffding

/-- Half-integer telescoping upper bound used in the paper to control an
inverse-square tail. -/
theorem inverseSquareTail_upper_half {N s : ℕ} (hsN : s ≤ N - 1) :
    inverseSquareTail N s ≤
      1 / ((N : ℝ) - (s : ℝ) - 1 / 2) -
        1 / ((N : ℝ) - 1 / 2) := by
  induction s with
  | zero => simp [inverseSquareTail]
  | succ s ih =>
      have hsN' : s ≤ N - 1 := by omega
      have hih := ih hsN'
      have hNlarge : s + 2 ≤ N := by omega
      have hlower : (0 : ℝ) < (N : ℝ) - (s : ℝ) - 3 / 2 := by
        have hcast : (s : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hNlarge
        linarith
      have hmiddle : (0 : ℝ) < (N : ℝ) - (s : ℝ) - 1 / 2 := by
        linarith
      have hupper : (0 : ℝ) < (N : ℝ) - 1 / 2 := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        linarith
      let ell : ℝ := (N : ℝ) - (s : ℝ) - 1
      have hell : 1 ≤ ell := by
        dsimp [ell]
        have : (s : ℝ) + 2 ≤ N := by exact_mod_cast hNlarge
        linarith
      have hellm : 0 < ell - 1 / 2 := by linarith
      have hellp : 0 < ell + 1 / 2 := by linarith
      have hell0 : 0 < ell := lt_of_lt_of_le (by norm_num) hell
      have hterm : 1 / ell ^ 2 ≤
          1 / (ell - 1 / 2) - 1 / (ell + 1 / 2) := by
        have hd : 0 < ell ^ 2 - 1 / 4 := by nlinarith [sq_nonneg ell]
        calc
          1 / ell ^ 2 ≤ 1 / (ell ^ 2 - 1 / 4) := by
            rw [div_le_div_iff₀ (sq_pos_of_pos hell0) hd]
            nlinarith
          _ = 1 / (ell - 1 / 2) - 1 / (ell + 1 / 2) := by
            rw [show ell ^ 2 - 1 / 4 =
              (ell - 1 / 2) * (ell + 1 / 2) by ring]
            rw [div_sub_div (1 : ℝ) (1 : ℝ)
              (ne_of_gt hellm) (ne_of_gt hellp)]
            congr 1
            ring
      have hrec : inverseSquareTail N (s + 1) = inverseSquareTail N s +
          1 / (((N - 1 - s : ℕ) : ℝ) ^ 2) := by
        simp [inverseSquareTail, Finset.sum_range_succ]
      have hcast : ((N - 1 - s : ℕ) : ℝ) = ell := by
        dsimp [ell]
        rw [Nat.cast_sub (by omega : s ≤ N - 1),
          Nat.cast_sub (by omega : 1 ≤ N)]
        push_cast
        ring
      rw [hrec, hcast]
      calc
        inverseSquareTail N s + 1 / ell ^ 2 ≤
            (1 / ((N : ℝ) - (s : ℝ) - 1 / 2) -
              1 / ((N : ℝ) - 1 / 2)) +
                (1 / (ell - 1 / 2) - 1 / (ell + 1 / 2)) :=
          add_le_add hih hterm
        _ = 1 / ((N : ℝ) - ((s + 1 : ℕ) : ℝ) - 1 / 2) -
              1 / ((N : ℝ) - 1 / 2) := by
          dsimp [ell]
          push_cast
          ring

/-- On the range relevant to `Γ_N`, the inverse-square tail is small
enough to make consecutive `gammaTerm`s monotone. -/
theorem inverseSquareTail_upper_for_monotonicity
    {N s : ℕ} (hN : 2 ≤ N) (hs0 : 1 ≤ s)
    (hsHalf : s + 1 ≤ N / 2) :
    inverseSquareTail N s ≤
      (s : ℝ) / ((N : ℝ) * ((N : ℝ) - (s : ℝ) - 1)) := by
  have hsN : s ≤ N - 1 := by omega
  have htel := inverseSquareTail_upper_half hsN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hA : (0 : ℝ) < (N : ℝ) - (s : ℝ) - 1 / 2 := by
    have hcast : (2 : ℝ) * ((s : ℝ) + 1) ≤ (N : ℝ) := by
      exact_mod_cast (show 2 * (s + 1) ≤ N by omega)
    linarith
  have hB : (0 : ℝ) < (N : ℝ) - 1 / 2 := by linarith
  have hC : (0 : ℝ) < (N : ℝ) - (s : ℝ) - 1 := by
    have hcast : (s : ℝ) + 2 ≤ (N : ℝ) := by
      exact_mod_cast (show s + 2 ≤ N by omega)
    linarith
  have hA2 : -1 + (N : ℝ) * 2 - (s : ℝ) * 2 ≠ 0 := by
    nlinarith
  have hB2 : -1 + (N : ℝ) * 2 ≠ 0 := by nlinarith
  calc
    inverseSquareTail N s ≤
        1 / ((N : ℝ) - (s : ℝ) - 1 / 2) -
          1 / ((N : ℝ) - 1 / 2) := htel
    _ = (s : ℝ) /
        (((N : ℝ) - (s : ℝ) - 1 / 2) *
          ((N : ℝ) - 1 / 2)) := by
      rw [div_sub_div (1 : ℝ) (1 : ℝ)
        (ne_of_gt hA) (ne_of_gt hB)]
      congr 1
      ring
    _ ≤ (s : ℝ) /
        ((N : ℝ) * ((N : ℝ) - (s : ℝ) - 1)) := by
      apply div_le_div_of_nonneg_left (by positivity) ?_ ?_
      · exact mul_pos hNpos hC
      · nlinarith [show (0 : ℝ) ≤ s by positivity]

/-- Consecutive terms in the finite maximization defining `Γ_N` are
nondecreasing up to `floor(N/2)`. -/
theorem gammaTerm_mono_step {N s : ℕ} (hN : 2 ≤ N)
    (hs0 : 1 ≤ s) (hsHalf : s + 1 ≤ N / 2) :
    gammaTerm N s ≤ gammaTerm N (s + 1) := by
  have htail := inverseSquareTail_upper_for_monotonicity hN hs0 hsHalf
  have hsN : s + 1 ≤ N - 1 := by omega
  have hrec : inverseSquareTail N (s + 1) = inverseSquareTail N s +
      1 / (((N - 1 - s : ℕ) : ℝ) ^ 2) := by
    simp [inverseSquareTail, Finset.sum_range_succ]
  have hsPos : (0 : ℝ) < (s : ℝ) := by positivity
  have hs1Pos : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hNPos : (0 : ℝ) < (N : ℝ) := by positivity
  have hDPos : (0 : ℝ) < (N : ℝ) - (s : ℝ) - 1 := by
    have hcast : (s : ℝ) + 1 < (N : ℝ) := by
      exact_mod_cast (show s + 1 < N by omega)
    linarith
  have hcastD : ((N - 1 - s : ℕ) : ℝ) =
      (N : ℝ) - (s : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : s ≤ N - 1),
      Nat.cast_sub (by omega : 1 ≤ N)]
    push_cast
    ring
  unfold gammaTerm
  rw [hrec, hcastD, Nat.cast_sub (by omega : s ≤ N),
    Nat.cast_sub (by omega : s + 1 ≤ N)]
  push_cast
  have hnonneg : 0 ≤
      (N : ℝ) / (((s : ℝ) + 1) * ((N : ℝ) - (s : ℝ) - 1)) -
        (N : ℝ) ^ 2 / ((s : ℝ) * ((s : ℝ) + 1)) *
          inverseSquareTail N s := by
    have hcoef : 0 ≤
        (N : ℝ) ^ 2 / ((s : ℝ) * ((s : ℝ) + 1)) := by positivity
    have hmul := mul_le_mul_of_nonneg_left htail hcoef
    have hle :
      (N : ℝ) ^ 2 / ((s : ℝ) * ((s : ℝ) + 1)) *
          inverseSquareTail N s ≤
        (N : ℝ) /
          (((s : ℝ) + 1) * ((N : ℝ) - (s : ℝ) - 1)) := by
      calc
        (N : ℝ) ^ 2 / ((s : ℝ) * ((s : ℝ) + 1)) *
            inverseSquareTail N s ≤
          (N : ℝ) ^ 2 / ((s : ℝ) * ((s : ℝ) + 1)) *
            ((s : ℝ) /
              ((N : ℝ) * ((N : ℝ) - (s : ℝ) - 1))) := hmul
        _ = (N : ℝ) /
            (((s : ℝ) + 1) * ((N : ℝ) - (s : ℝ) - 1)) := by
          field_simp [ne_of_gt hsPos, ne_of_gt hs1Pos, ne_of_gt hNPos,
            ne_of_gt hDPos]
    linarith
  rw [← sub_nonneg]
  convert hnonneg using 1
  field_simp [ne_of_gt hsPos, ne_of_gt hs1Pos, ne_of_gt hNPos,
    ne_of_gt hDPos]
  ring

theorem gammaTerm_mono {N s t : ℕ} (hN : 2 ≤ N)
    (hs0 : 1 ≤ s) (hst : s ≤ t) (htHalf : t ≤ N / 2) :
    gammaTerm N s ≤ gammaTerm N t := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih =>
      exact (ih (by omega)).trans
        (gammaTerm_mono_step hN (hs0.trans hst) (by omega))

/-- The finite maximum in Theorem 1 is attained at
`s = floor(N/2)`. -/
theorem Gamma_eq_lastTerm {N : ℕ} (hN : 2 ≤ N) :
    Gamma N = gammaTerm N (N / 2) := by
  have hhalf0 : 1 ≤ N / 2 := by omega
  rw [Gamma, dif_pos hN]
  apply le_antisymm
  · apply Finset.sup'_le
    intro s hs
    have hs' : 1 ≤ s ∧ s ≤ N / 2 := by simpa using hs
    exact gammaTerm_mono hN hs'.1 hs'.2 le_rfl
  · exact Finset.le_sup' (gammaTerm N) (by simp [hhalf0])

/-- Even-parity closed form from Theorem 1.  The sum
`inverseSquareTail N (N/2)` is the paper's sum over
`ℓ = N/2, ..., N-1`, stored in reverse order. -/
theorem Gamma_closedForm_even {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) :
    Gamma N = (N : ℝ) * inverseSquareTail N (N / 2) := by
  rcases hEven with ⟨q, rfl⟩
  have hq : 0 < q := by omega
  rw [Gamma_eq_lastTerm (by omega)]
  unfold gammaTerm
  have hhalf : (q + q) / 2 = q := by omega
  have hsub : q + q - q = q := by omega
  rw [hhalf, hsub]
  apply congrArg (fun c : ℝ ↦ c * inverseSquareTail (q + q) q)
  field_simp [show (q : ℝ) ≠ 0 by positivity]

/-- Odd-parity closed form from Theorem 1, again with the inverse-square
sum stored in reverse order. -/
theorem Gamma_closedForm_odd {N : ℕ} (hN : 2 ≤ N) (hOdd : Odd N) :
    Gamma N =
      (N : ℝ) * ((N : ℝ) + 1) / ((N : ℝ) - 1) *
        inverseSquareTail N (N / 2) := by
  rcases hOdd with ⟨q, rfl⟩
  have hq : 0 < q := by omega
  rw [Gamma_eq_lastTerm (by omega)]
  unfold gammaTerm
  have hhalf : (2 * q + 1) / 2 = q := by omega
  have hsub : 2 * q + 1 - q = q + 1 := by omega
  rw [hhalf, hsub]
  apply congrArg (fun c : ℝ ↦ c * inverseSquareTail (2 * q + 1) q)
  push_cast
  field_simp [show (q : ℝ) ≠ 0 by positivity]
  ring

end SharpSerfling.ExchangeableHoeffding
