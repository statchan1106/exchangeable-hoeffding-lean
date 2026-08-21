import ExchangeableHoeffding.Optimality
import SharpSerfling.Hypergeometric.SmallTilt

namespace SharpSerfling.ExchangeableHoeffding

open Filter Topology
open SharpSerfling.Hypergeometric

/-- Conversion between the paper's normalization and the normalization of
the existing hypergeometric variational theorem. -/
theorem paperNormalizedLogMgf_eq {N K m : ℕ} (hN : 2 ≤ N)
    (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) {t : ℝ} (ht : t ≠ 0) :
    paperNormalizedLogMgf N K m t =
      ((N : ℝ) / ((N : ℝ) - 1)) * normalizedLogMgf N K m t := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hmLt : m < N := by omega
  have hNmR : (N : ℝ) - (m : ℝ) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hmLt))
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast (show 1 < N by omega)))
  unfold paperNormalizedLogMgf normalizedLogMgf SharpSerfling.hypergeomScale
  field_simp [hmR, hNmR, hNm1, ht]

theorem paperVariationalValues_nonempty {N : ℕ} (hN : 2 ≤ N) :
    (paperVariationalValues N).Nonempty := by
  refine ⟨paperNormalizedLogMgf N 1 1 1, 1, 1, by omega, by omega,
    by omega, by omega, 1, one_ne_zero, rfl⟩

theorem paperVariationalValues_bddAbove {N : ℕ} (hN : 2 ≤ N) :
    BddAbove (paperVariationalValues N) := by
  refine ⟨SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1), ?_⟩
  rintro x ⟨K, m, hK0, hKN, hm0, hmN, t, ht, rfl⟩
  have hnorm := normalizedLogMgf_le_kappa hN (by omega : K ≤ N)
    hm0 hmN ht
  rw [paperNormalizedLogMgf_eq hN hm0 hmN ht]
  have hratio : 0 ≤ (N : ℝ) / ((N : ℝ) - 1) := by
    have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
      exact sub_pos.mpr (by exact_mod_cast (show 1 < N by omega))
    exact (div_pos (by positivity) hNm1).le
  calc
    (N : ℝ) / ((N : ℝ) - 1) * normalizedLogMgf N K m t ≤
        (N : ℝ) / ((N : ℝ) - 1) * SharpSerfling.kappa N :=
      mul_le_mul_of_nonneg_left hnorm hratio
    _ = SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) := by ring

theorem variationalConstant_le_exact {N : ℕ} (hN : 2 ≤ N) :
    variationalConstant N ≤
      SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) := by
  unfold variationalConstant
  apply csSup_le (paperVariationalValues_nonempty hN)
  rintro x ⟨K, m, hK0, hKN, hm0, hmN, t, ht, rfl⟩
  have hnorm := normalizedLogMgf_le_kappa hN (by omega : K ≤ N)
    hm0 hmN ht
  rw [paperNormalizedLogMgf_eq hN hm0 hmN ht]
  have hratio : 0 ≤ (N : ℝ) / ((N : ℝ) - 1) := by
    have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
      exact sub_pos.mpr (by exact_mod_cast (show 1 < N by omega))
    exact (div_pos (by positivity) hNm1).le
  calc
    (N : ℝ) / ((N : ℝ) - 1) * normalizedLogMgf N K m t ≤
        (N : ℝ) / ((N : ℝ) - 1) * SharpSerfling.kappa N :=
      mul_le_mul_of_nonneg_left hnorm hratio
    _ = SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) := by ring

theorem variationalConstant_eq_exact_odd {q : ℕ} (hq : 0 < q) :
    variationalConstant (2 * q + 1) =
      SharpSerfling.kappa (2 * q + 1) *
        ((2 * q + 1 : ℕ) : ℝ) /
          (((2 * q + 1 : ℕ) : ℝ) - 1) := by
  let t := 2 * oddLogIncrement (2 * q + 1)
  have ht : t ≠ 0 := by
    dsimp [t]
    exact mul_ne_zero (by norm_num) (ne_of_gt (oddLogIncrement_pos (by omega)))
  have hm : paperNormalizedLogMgf (2 * q + 1) q 1 t ∈
      paperVariationalValues (2 * q + 1) := by
    refine ⟨q, 1, by omega, by omega, by omega, by omega, t, ht, rfl⟩
  apply le_antisymm (variationalConstant_le_exact (by omega))
  have hle := le_csSup (paperVariationalValues_bddAbove (by omega)) hm
  rw [paperNormalizedLogMgf_eq (by omega) (by omega) (by omega) ht,
    normalizedLogMgf_odd_witness hq] at hle
  calc
    SharpSerfling.kappa (2 * q + 1) * ((2 * q + 1 : ℕ) : ℝ) /
          (((2 * q + 1 : ℕ) : ℝ) - 1) =
        ((2 * q + 1 : ℕ) : ℝ) /
          (((2 * q + 1 : ℕ) : ℝ) - 1) *
            SharpSerfling.kappa (2 * q + 1) := by ring
    _ ≤ variationalConstant (2 * q + 1) := hle

theorem variationalConstant_eq_exact_even {q : ℕ} (hq : 0 < q) :
    variationalConstant (2 * q) =
      SharpSerfling.kappa (2 * q) * ((2 * q : ℕ) : ℝ) /
        (((2 * q : ℕ) : ℝ) - 1) := by
  have hN : 2 ≤ 2 * q := by omega
  have hlimNorm := tendsto_normalizedLogMgf_even_central hq
    (m := 1) (by omega) (by omega)
  let c : ℝ := ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1)
  have hlimScaled := hlimNorm.const_mul c
  have hlimPaper : Tendsto (paperNormalizedLogMgf (2 * q) q 1)
      (nhdsWithin 0 {0}ᶜ) (nhds c) := by
    have heq : (fun t ↦ c * normalizedLogMgf (2 * q) q 1 t) =ᶠ[
        nhdsWithin 0 {0}ᶜ] paperNormalizedLogMgf (2 * q) q 1 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      exact (paperNormalizedLogMgf_eq hN (by omega) (by omega) ht0).symm
    simpa only [mul_one] using hlimScaled.congr' heq
  have hevent : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ,
      paperNormalizedLogMgf (2 * q) q 1 t ≤ variationalConstant (2 * q) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    apply le_csSup (paperVariationalValues_bddAbove hN)
    exact ⟨q, 1, by omega, by omega, by omega, by omega, t, ht0, rfl⟩
  have hlower : c ≤ variationalConstant (2 * q) :=
    le_of_tendsto hlimPaper hevent
  apply le_antisymm (variationalConstant_le_exact hN)
  rw [SharpSerfling.kappa_of_even ⟨q, by omega⟩, one_mul]
  change c ≤ variationalConstant (2 * q)
  exact hlower

/-- **Remark 2.4.**  The literal hypergeometric supremum `V_N` is the
exact optimal exchangeable coefficient. -/
theorem remark_2_4_variational {N : ℕ} (hN : 2 ≤ N) :
    variationalConstant N =
      SharpSerfling.kappa N * (N : ℝ) / ((N : ℝ) - 1) := by
  by_cases hEven : Even N
  · rcases hEven with ⟨q, rfl⟩
    simpa [two_mul] using variationalConstant_eq_exact_even (q := q) (by omega)
  · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨q, rfl⟩
    exact variationalConstant_eq_exact_odd (by omega)

end SharpSerfling.ExchangeableHoeffding
