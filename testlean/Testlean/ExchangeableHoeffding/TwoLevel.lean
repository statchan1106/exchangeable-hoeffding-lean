import Testlean.ExchangeableHoeffding.HammingSlice

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace ExchangeableHoeffding

theorem samplingMgf_indicator_eq_hypergeomMgf
    {N : ℕ} (A : Finset (Fin N)) (m : ℕ) (t : ℝ) :
    samplingMgf (Finset.univ : Finset (Fin N)) m
        (fun i => if i ∈ A then (1 : ℝ) else 0) t =
      hypergeomMgf N A.card m t := by
  rw [hypergeomMgf_eq_pmf_sum (by simpa using A.card_le_univ) t]
  let Q : Finset (Fin N) := Finset.univ \ A
  have hAsub : A ⊆ (Finset.univ : Finset (Fin N)) := Finset.subset_univ A
  have hdisj : Disjoint A Q := by
    rw [Finset.disjoint_left]
    intro x hxA hxQ
    exact (Finset.mem_sdiff.mp hxQ).2 hxA
  have hunion : A ∪ Q = (Finset.univ : Finset (Fin N)) :=
    Finset.union_sdiff_of_subset hAsub
  have hQcard : Q.card = N - A.card := by
    change (Finset.univ \ A).card = N - A.card
    rw [Finset.card_sdiff_of_subset hAsub, Finset.card_univ, Fintype.card_fin]
  have hgroup := samplingMgf_indicator_partition A Q hdisj m t
  rw [hunion, hQcard] at hgroup
  simp only [Finset.card_univ, Fintype.card_fin] at hgroup
  rw [hgroup]
  unfold hypergeomPMF
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Nat.cast_mul]
  ring

theorem sliceAverage_exp_centeredTwoLevelVector_eq_hypergeomMgf
    {N : ℕ} (hN : 0 < N) (k : ℕ) (A : Finset (Fin N)) (d : ℝ) :
    sliceAverage k
        (fun S => Real.exp (∑ i ∈ S, centeredTwoLevelVector A d i)) =
      hypergeomMgf N A.card k d := by
  rw [← samplingMgf_indicator_eq_hypergeomMgf A k d]
  unfold sliceAverage samplingMgf
  rw [sliceSubsets_eq_powersetCard]
  simp only [Finset.card_univ, Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
  rw [sum_centeredTwoLevelVector_on hN]
  unfold finiteMean
  have hindicator :
      (∑ x ∈ (Finset.univ : Finset (Fin N)),
          if x ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
    simp
  rw [hindicator]
  simp only [Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [hScard]
  have hfilter : ((S.filter fun i => i ∈ A).card : ℝ) =
      (∑ x ∈ S, if x ∈ A then (1 : ℝ) else 0) := by
    have hset : (S.filter fun i => i ∈ A) = S ∩ A := by
      ext i
      simp
    rw [hset]
    simp
  rw [hfilter]
  ring

lemma gammaTerm_le_Gamma
    {N s : ℕ} (hs0 : 1 ≤ s) (hsHalf : s ≤ N / 2) :
    gammaTerm N s ≤ Gamma N := by
  classical
  unfold Gamma
  let T : Finset ℝ :=
    (Finset.Icc 1 (N / 2)).image (fun r => gammaTerm N r)
  have hs : s ∈ Finset.Icc 1 (N / 2) := by simp [hs0, hsHalf]
  have hmem : gammaTerm N s ∈ T := Finset.mem_image.mpr ⟨s, hs, rfl⟩
  have hT : T.Nonempty := ⟨gammaTerm N s, hmem⟩
  rw [dif_pos hT]
  exact Finset.le_max' T _ hmem

lemma hypergeomB_eq_gammaTerm_mul_normFactor
    {N m : ℕ} (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) :
    hypergeomB N m = gammaTerm N (Nat.min m (N - m)) *
      ((m : ℝ) * ((N - m : ℕ) : ℝ) / (N : ℝ)) := by
  have hmN' : m ≤ N := by omega
  have hNnat : 0 < N := by omega
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat.ne'
  have hm0' : (m : ℝ) ≠ 0 := by positivity
  have hNm0 : ((N - m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < N - m))
  by_cases hsmall : m ≤ N - m
  · simp only [hypergeomB, Nat.min_eq_left hsmall]
    unfold gammaTerm
    field_simp [hN0, hm0', hNm0]
  · have hlarge : N - m ≤ m := by omega
    simp only [hypergeomB, Nat.min_eq_right hlarge]
    unfold gammaTerm
    have hsub : N - (N - m) = m := by omega
    rw [hsub]
    field_simp [hN0, hm0', hNm0]

theorem hypergeomB_le_Gamma_mul_normFactor
    {N m : ℕ} (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) :
    hypergeomB N m ≤ Gamma N *
      ((m : ℝ) * ((N - m : ℕ) : ℝ) / (N : ℝ)) := by
  let s := Nat.min m (N - m)
  have hs0 : 1 ≤ s := by
    exact le_min hm0 (by omega)
  have hmN' : m ≤ N := by omega
  have hsHalf : s ≤ N / 2 := by
    have hsm : s ≤ m := Nat.min_le_left _ _
    have hscomp : s ≤ N - m := Nat.min_le_right _ _
    omega
  have hterm := gammaTerm_le_Gamma hs0 hsHalf
  have hfactor : 0 ≤ (m : ℝ) * ((N - m : ℕ) : ℝ) / (N : ℝ) := by positivity
  rw [hypergeomB_eq_gammaTerm_mul_normFactor hm0 hmN]
  exact mul_le_mul_of_nonneg_right hterm hfactor

theorem log_sliceAverage_centeredTwoLevelVector_le
    {N k : ℕ} (hN : 2 ≤ N) (hk : k ≤ N)
    (A : Finset (Fin N)) (hA0 : 1 ≤ A.card) (hAN : A.card ≤ N - 1)
    (d : ℝ) :
    Real.log (sliceAverage k
        (fun S => Real.exp (∑ i ∈ S, centeredTwoLevelVector A d i))) ≤
      (Gamma N / 8) * normSq (centeredTwoLevelVector A d) := by
  rw [sliceAverage_exp_centeredTwoLevelVector_eq_hypergeomMgf (by omega)]
  rw [hypergeomMgf_symm (by simpa using A.card_le_univ) hk d]
  calc
    Real.log (hypergeomMgf N k A.card d) ≤
        (d ^ 2 / 8) * hypergeomB N A.card :=
      hypergeometric_mgf_bound hk (by simpa using A.card_le_univ) d
    _ ≤ (Gamma N / 8) * normSq (centeredTwoLevelVector A d) := by
      rw [normSq_centeredTwoLevelVector (by omega)]
      have hB := hypergeomB_le_Gamma_mul_normFactor hA0 hAN
      nlinarith [sq_nonneg d]

lemma eq_centeredTwoLevelVector_of_atMostTwoValues
    {N : ℕ} (hN : 0 < N) (y : Fin N → ℝ)
    (hy : ∑ i : Fin N, y i = 0) (htwo : AtMostTwoValues y) :
    ∃ (A : Finset (Fin N)) (d : ℝ), y = centeredTwoLevelVector A d := by
  classical
  rcases htwo with ⟨a, b, hab⟩
  let A : Finset (Fin N) := Finset.univ.filter fun i => y i = a
  have hyrep : y = twoLevelVector A a b := by
    funext i
    by_cases hi : i ∈ A
    · have hya : y i = a := (Finset.mem_filter.mp hi).2
      simp [twoLevelVector, hi, hya]
    · have hyna : y i ≠ a := by
        intro hya
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hya⟩)
      have hyb : y i = b := (hab i).resolve_left hyna
      simp [twoLevelVector, hi, hyb]
  have hcard : A.card ≤ N := by simpa using A.card_le_univ
  have hsum : (A.card : ℝ) * a + ((N - A.card : ℕ) : ℝ) * b = 0 := by
    rw [← sum_twoLevelVector]
    rw [← hyrep]
    exact hy
  rw [Nat.cast_sub hcard] at hsum
  have hNreal : (N : ℝ) ≠ 0 := by positivity
  have ha : a = ((N - A.card : ℕ) : ℝ) / (N : ℝ) * (a - b) := by
    rw [Nat.cast_sub hcard]
    field_simp
    nlinarith
  have hb : b = -((A.card : ℝ) / (N : ℝ) * (a - b)) := by
    field_simp
    nlinarith
  refine ⟨A, a - b, ?_⟩
  rw [hyrep]
  unfold centeredTwoLevelVector
  funext i
  by_cases hi : i ∈ A
  · simp [twoLevelVector, hi, ← ha]
  · simp [twoLevelVector, hi, ← hb]

theorem slice_mgf_bound_of_atMostTwoValues
    {N k : ℕ} (hN : 2 ≤ N) (hk0 : 1 ≤ k) (hkN : k ≤ N - 1)
    (y : Fin N → ℝ) (hy : ∑ i : Fin N, y i = 0)
    (htwo : AtMostTwoValues y) :
    Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, y i))) ≤
      (Gamma N / 8) * normSq y := by
  classical
  rcases eq_centeredTwoLevelVector_of_atMostTwoValues (by omega) y hy htwo with
    ⟨A, d, rfl⟩
  have hk : k ≤ N := by omega
  by_cases hA0 : A.card = 0
  · have hA : A = ∅ := Finset.card_eq_zero.mp hA0
    have hzero : centeredTwoLevelVector A d = fun _ => 0 := by
      funext i
      simp [centeredTwoLevelVector, twoLevelVector, hA]
    rw [hzero]
    have havg : sliceAverage k
        (fun S : Finset (Fin N) => Real.exp (∑ i ∈ S, (0 : ℝ))) = 1 := by
      simpa using (sliceAverage_one (N := N) hk)
    rw [havg]
    simp [normSq]
  · by_cases hAN : A.card = N
    · have hA : A = (Finset.univ : Finset (Fin N)) := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ A)
        simp [hAN]
      have hzero : centeredTwoLevelVector A d = fun _ => 0 := by
        funext i
        simp [centeredTwoLevelVector, twoLevelVector, hA]
      rw [hzero]
      have havg : sliceAverage k
          (fun S : Finset (Fin N) => Real.exp (∑ i ∈ S, (0 : ℝ))) = 1 := by
        simpa using (sliceAverage_one (N := N) hk)
      rw [havg]
      simp [normSq]
    · apply log_sliceAverage_centeredTwoLevelVector_le hN hk A
        (Nat.one_le_iff_ne_zero.mpr hA0)
      have hcard : A.card ≤ N := by simpa using A.card_le_univ
      omega

theorem slice_mgf_bound_from_two_level_extremizer
    {N k : ℕ} (hN : 2 ≤ N) (hk0 : 1 ≤ k) (hkN : k ≤ N - 1)
    (hext : ∀ {ρ : ℝ} (hρ : 0 < ρ),
      ∀ z : Fin N → ℝ,
        SphereSection ρ z →
          ∃ y : Fin N → ℝ,
            SphereSection ρ y ∧ AtMostTwoValues y ∧
              sliceFunctional k z ≤ sliceFunctional k y)
    (z : Fin N → ℝ) (hz : ∑ i : Fin N, z i = 0) :
    Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, z i))) ≤
      (Gamma N / 8) * normSq z := by
  classical
  by_cases hnorm : normSq z = 0
  · have hz0 : z = fun _ => 0 := by
      funext i
      have hsum : ∑ j : Fin N, z j ^ 2 = 0 := by
        simpa [normSq] using hnorm
      have hall :=
        (Fintype.sum_eq_zero_iff_of_nonneg
          (fun j : Fin N => sq_nonneg (z j))).mp hsum
      exact sq_eq_zero_iff.mp (by simpa using congrFun hall i)
    rw [hz0]
    have hk : k ≤ N := by omega
    have havg : sliceAverage k
        (fun S : Finset (Fin N) => Real.exp (∑ i ∈ S, (0 : ℝ))) = 1 := by
      simpa using (sliceAverage_one (N := N) hk)
    rw [havg]
    simp [normSq]
  · have hnormPos : 0 < normSq z :=
      lt_of_le_of_ne (normSq_nonneg z) (Ne.symm hnorm)
    let ρ : ℝ := Real.sqrt (normSq z)
    have hρ : 0 < ρ := Real.sqrt_pos.2 hnormPos
    have hzSphere : SphereSection ρ z := by
      refine ⟨hz, ?_⟩
      dsimp only [ρ]
      rw [Real.sq_sqrt (normSq_nonneg z)]
    rcases hext hρ z hzSphere with ⟨y, hySphere, htwo, hle⟩
    have hle' :
        Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, z i))) ≤
          Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, y i))) := by
      simpa only [sliceFunctional_eq_log_sliceAverage] using hle
    calc
      Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, z i))) ≤
          Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, y i))) := hle'
      _ ≤ (Gamma N / 8) * normSq y :=
        slice_mgf_bound_of_atMostTwoValues hN hk0 hkN y hySphere.1 htwo
      _ = (Gamma N / 8) * normSq z := by rw [hySphere.2, hzSphere.2]

/-- Once the extremizer reduction is supplied, all remaining finite-sampling
and two-level estimates assemble into the full slice MGF inequality. -/
theorem SliceAnalyticInputs.slice_mgf_bound (H : SliceAnalyticInputs)
    {N k : ℕ} (hN : 2 ≤ N) (hk0 : 1 ≤ k) (hkN : k ≤ N - 1)
    (z : Fin N → ℝ) (hz : ∑ i : Fin N, z i = 0) :
    Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, z i))) ≤
      (Gamma N / 8) * normSq z := by
  apply slice_mgf_bound_from_two_level_extremizer hN hk0 hkN
      (fun {ρ} hρ y hy => ?_) z hz
  rcases H.two_level_extremizer hN hk0 hkN hρ with ⟨w, hwSphere, htwo, hmax⟩
  exact ⟨w, hwSphere, htwo, hmax y hy⟩

end ExchangeableHoeffding
