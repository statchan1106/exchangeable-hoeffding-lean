import ExchangeableHoeffding.Definitions

namespace SharpSerfling.ExchangeableHoeffding

open scoped BigOperators

theorem gammaTerm_le_Gamma {N s : ℕ} (hN : 2 ≤ N)
    (hs0 : 1 ≤ s) (hsN : s ≤ N / 2) :
    gammaTerm N s ≤ Gamma N := by
  rw [Gamma, dif_pos hN]
  exact Finset.le_sup' (gammaTerm N) (by simp [hs0, hsN])

theorem inverseSquareTail_pos {N s : ℕ} (hs0 : 0 < s)
    (hsN : s ≤ N - 1) : 0 < inverseSquareTail N s := by
  unfold inverseSquareTail
  apply Finset.sum_pos'
  · intro j hj
    positivity
  · refine ⟨0, by simp [hs0], ?_⟩
    have hN1 : 1 ≤ N - 1 := hs0.trans_le hsN
    have : 0 < (N - 1 : ℕ) := by omega
    positivity

/-- A sharp elementary lower bound on the inverse-square tail. -/
theorem inverseSquareTail_lower {N s : ℕ} (hs0 : 1 ≤ s)
    (hsN : s ≤ N - 1) :
    (s : ℝ) / (((N : ℝ) - 1) * ((N : ℝ) - (s : ℝ))) ≤
      inverseSquareTail N s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs : s = 0
      · subst s
        have hN2 : 2 ≤ N := by omega
        have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ N)]
          norm_num
        norm_num [inverseSquareTail]
        rw [hcast]
        simp only [pow_two, mul_inv]
        exact le_rfl
      · have hspos : 1 ≤ s := by omega
        have hsN' : s ≤ N - 1 := by omega
        have hih := ih hspos hsN'
        have hrec : inverseSquareTail N (s + 1) = inverseSquareTail N s +
            1 / (((N - 1 - s : ℕ) : ℝ) ^ 2) := by
          simp [inverseSquareTail, Finset.sum_range_succ]
        have hNs : s ≤ N - 2 := by omega
        have hNpos : (0 : ℝ) < (N : ℝ) := by
          exact_mod_cast (show 0 < N by omega)
        have hNm1pos : (0 : ℝ) < (N : ℝ) - 1 := by
          exact sub_pos.mpr (by exact_mod_cast (show 1 < N by omega))
        have hNsubSpos : (0 : ℝ) < (N : ℝ) - s := by
          exact sub_pos.mpr (by exact_mod_cast (show s < N by omega))
        have hNsubSuccpos : (0 : ℝ) < (N : ℝ) - (s + 1) := by
          exact sub_pos.mpr (by exact_mod_cast (show s + 1 < N by omega))
        have hcast : ((N - 1 - s : ℕ) : ℝ) = (N : ℝ) - (s + 1 : ℕ) := by
          rw [Nat.cast_sub (by omega : s ≤ N - 1), Nat.cast_sub (by omega : 1 ≤ N)]
          push_cast
          ring
        rw [hrec, hcast]
        calc
          ((s + 1 : ℕ) : ℝ) /
                (((N : ℝ) - 1) * ((N : ℝ) - ((s + 1 : ℕ) : ℝ))) =
              (s : ℝ) / (((N : ℝ) - 1) * ((N : ℝ) - (s : ℝ))) +
                (N : ℝ) /
                  (((N : ℝ) - 1) * ((N : ℝ) - (s + 1 : ℕ)) *
                    ((N : ℝ) - (s : ℝ))) := by
            field_simp [ne_of_gt hNm1pos, ne_of_gt hNsubSpos,
              ne_of_gt hNsubSuccpos]
            push_cast
            ring
          _ ≤ inverseSquareTail N s +
                (N : ℝ) /
                  (((N : ℝ) - 1) * ((N : ℝ) - (s + 1 : ℕ)) *
                    ((N : ℝ) - (s : ℝ))) := by gcongr
          _ ≤ inverseSquareTail N s +
                1 / ((N : ℝ) - (s + 1 : ℕ)) ^ 2 := by
            have hfrac :
                (N : ℝ) /
                    (((N : ℝ) - 1) * ((N : ℝ) - (s + 1 : ℕ)) *
                      ((N : ℝ) - (s : ℝ))) ≤
                  1 / ((N : ℝ) - (s + 1 : ℕ)) ^ 2 := by
              norm_num only [Nat.cast_add, Nat.cast_one]
              rw [div_le_div_iff₀
                (mul_pos (mul_pos hNm1pos hNsubSuccpos) hNsubSpos)
                (sq_pos_of_pos hNsubSuccpos)]
              nlinarith
            exact add_le_add_right hfrac _
          _ = inverseSquareTail N s +
                1 / (((N : ℝ) - (s + 1 : ℕ)) ^ 2) := rfl

theorem gammaTerm_lower_variance {N s : ℕ} (hN : 2 ≤ N)
    (hs0 : 1 ≤ s) (hsN : s ≤ N - 1) :
    (N : ℝ) / ((N : ℝ) - 1) ≤ gammaTerm N s := by
  have htail := inverseSquareTail_lower hs0 hsN
  have hsR : (0 : ℝ) < s := by positivity
  have hNsub : (0 : ℝ) < (N : ℝ) - (s : ℝ) := by
    have hsltR : (s : ℝ) < N := by exact_mod_cast (show s < N by omega)
    linarith
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  unfold gammaTerm
  have hcast : ((N - s : ℕ) : ℝ) = (N : ℝ) - s := by
    rw [Nat.cast_sub (by omega : s ≤ N)]
  rw [hcast]
  calc
    (N : ℝ) / ((N : ℝ) - 1) =
        (N : ℝ) * ((N : ℝ) - s) / (s : ℝ) *
          ((s : ℝ) / (((N : ℝ) - 1) * ((N : ℝ) - s))) := by
      field_simp [ne_of_gt hsR, ne_of_gt hNsub, ne_of_gt hNm1]
    _ ≤ (N : ℝ) * ((N : ℝ) - s) / (s : ℝ) * inverseSquareTail N s := by
      gcongr

theorem Gamma_lower_variance {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) / ((N : ℝ) - 1) ≤ Gamma N := by
  have hhalf0 : 1 ≤ N / 2 := by omega
  have hhalfN : N / 2 ≤ N - 1 := by omega
  exact (gammaTerm_lower_variance hN hhalf0 hhalfN).trans
    (gammaTerm_le_Gamma hN hhalf0 le_rfl)

theorem Gamma_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Gamma N := by
  have hNR : (0 : ℝ) < N := by positivity
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hratio : 0 < (N : ℝ) / ((N : ℝ) - 1) := div_pos hNR hNm1
  exact hratio.trans_le (Gamma_lower_variance hN)

end SharpSerfling.ExchangeableHoeffding
