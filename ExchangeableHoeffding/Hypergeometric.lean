import ExchangeableHoeffding.GammaBasic

namespace SharpSerfling.ExchangeableHoeffding

open SharpSerfling.Hypergeometric

/-- The martingale factor of Lemma 4.5 dominates the usual
finite-population variance factor. -/
theorem sampleVarianceFactor_le_martingaleFactor
    {N m : ℕ} (hN : 2 ≤ N) (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) :
    (m : ℝ) * ((N : ℝ) - (m : ℝ)) / ((N : ℝ) - 1) ≤
      martingaleFactor N m := by
  let s := min m (N - m)
  have hmN' : m ≤ N := by omega
  have hs0 : 1 ≤ s := by
    dsimp [s]
    apply le_min hm0
    omega
  have hsN : s ≤ N - 1 := by
    dsimp [s]
    exact (min_le_left _ _).trans hmN
  have htail := inverseSquareTail_lower hs0 hsN
  have hsLeN : s ≤ N := by omega
  have hNsPos : (0 : ℝ) < (N : ℝ) - (s : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast (show s < N by omega))
  have hNm1Pos : (0 : ℝ) < (N : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast (show 1 < N by omega))
  have hproduct :
      (m : ℝ) * ((N : ℝ) - (m : ℝ)) =
        (s : ℝ) * ((N : ℝ) - (s : ℝ)) := by
    by_cases hmHalf : m ≤ N - m
    · have hs : s = m := min_eq_left hmHalf
      rw [hs]
    · have hs : s = N - m := min_eq_right (by omega : N - m ≤ m)
      rw [hs, Nat.cast_sub hmN']
      ring
  have hmul := mul_le_mul_of_nonneg_left htail
    (sq_nonneg ((N : ℝ) - (s : ℝ)))
  unfold martingaleFactor
  dsimp only
  rw [show min m (N - m) = s by rfl, Nat.cast_sub hsLeN]
  calc
    (m : ℝ) * ((N : ℝ) - (m : ℝ)) / ((N : ℝ) - 1) =
        ((N : ℝ) - (s : ℝ)) ^ 2 *
          ((s : ℝ) /
            (((N : ℝ) - 1) * ((N : ℝ) - (s : ℝ)))) := by
      rw [hproduct]
      field_simp [ne_of_gt hNm1Pos, ne_of_gt hNsPos]
    _ ≤ ((N : ℝ) - (s : ℝ)) ^ 2 * inverseSquareTail N s := hmul

/-- **Lemma 4.5.**  Logarithmic MGF bound for a centered
hypergeometric random variable, in the exact `B_{N,m}` notation of the
paper.  The existing universal bound is slightly stronger; the preceding
lemma verifies the coefficient comparison. -/
theorem lemma_4_5_hypergeometric
    {N K m : ℕ} (hN : 2 ≤ N) (hK : K ≤ N)
    (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) (t : ℝ) :
    Real.log (mgf N K m t) ≤ t ^ 2 / 8 * martingaleFactor N m := by
  have huniv := log_mgf_le_universal hN hK (by omega : m ≤ N) t
  have hfactor := sampleVarianceFactor_le_martingaleFactor hN hm0 hmN
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast (show 1 < N by omega)))
  unfold SharpSerfling.hypergeomScale at huniv
  calc
    Real.log (mgf N K m t) ≤
        ((m : ℝ) * ((N : ℝ) - (m : ℝ)) /
          (8 * ((N : ℝ) - 1))) * t ^ 2 := huniv
    _ = t ^ 2 / 8 *
        ((m : ℝ) * ((N : ℝ) - (m : ℝ)) / ((N : ℝ) - 1)) := by
      field_simp [hNm1]
    _ ≤ t ^ 2 / 8 * martingaleFactor N m := by
      gcongr

end SharpSerfling.ExchangeableHoeffding
