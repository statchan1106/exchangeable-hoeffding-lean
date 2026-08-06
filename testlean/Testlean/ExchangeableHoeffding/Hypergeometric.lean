import Testlean.ExchangeableHoeffding.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Vandermonde

set_option linter.unusedVariables false

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace ExchangeableHoeffding

/-! ## Hypergeometric sampling and finite-population martingales -/

/-- Hypergeometric probability mass function. -/
def hypergeomPMF (N K m r : ℕ) : ℝ :=
  ((Nat.choose K r * Nat.choose (N - K) (m - r)) : ℕ) /
    ((Nat.choose N m) : ℕ)

/-- The finite-sampling factor used by the hypergeometric MGF estimate. -/
def hypergeomB (N m : ℕ) : ℝ :=
  let s : ℕ := Nat.min m (N - m)
  (((N - s : ℕ) : ℝ) ^ 2) *
    (∑ ell ∈ Finset.Icc (N - s) (N - 1), (1 : ℝ) / ((ell : ℝ) ^ 2))

/-- Hoeffding's lemma in the exact normalization used by the sampling argument. -/
theorem bounded_centered_mgf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (a b t : ℝ)
    (hmeas : AEMeasurable Z μ)
    (hmean : (∫ ω, Z ω ∂μ) = 0)
    (hbdd : ∀ᵐ ω ∂μ, a ≤ Z ω ∧ Z ω ≤ b) :
    (∫ ω, Real.exp (t * Z ω) ∂μ) ≤
      Real.exp ((t ^ 2) * ((b - a) ^ 2) / 8) := by
  have hsubgaussian :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hmeas (by simpa [Set.mem_Icc] using hbdd) hmean
  change ProbabilityTheory.mgf Z μ t ≤ _
  calc
    _ ≤ Real.exp
        ((↑(((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ) * t ^ 2 / 2) :=
      hsubgaussian.mgf_le t
    _ = Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
      congr 1
      simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm]
      rw [Real.norm_eq_abs, div_pow, sq_abs]
      norm_num
      ring

lemma hypergeomPMF_nonneg (N K m r : ℕ) : 0 ≤ hypergeomPMF N K m r := by
  unfold hypergeomPMF
  positivity

/-- Interchanging the number of successes and the sample size leaves the
hypergeometric mass unchanged on the common support. -/
theorem hypergeomPMF_symm
    {N K m r : ℕ} (hK : K ≤ N) (hm : m ≤ N)
    (hrK : r ≤ K) (hrm : r ≤ m) :
    hypergeomPMF N K m r = hypergeomPMF N m K r := by
  by_cases hsupport : m - r ≤ N - K
  · have hsupport' : K - r ≤ N - m := by omega
    have hrem : N - K - (m - r) = N - m - (K - r) := by omega
    unfold hypergeomPMF
    simp only [Nat.cast_mul]
    rw [Nat.cast_choose ℝ hrK, Nat.cast_choose ℝ hrm,
      Nat.cast_choose ℝ hsupport, Nat.cast_choose ℝ hsupport',
      Nat.cast_choose ℝ hm, Nat.cast_choose ℝ hK]
    have hfac (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hfac]
    rw [hrem]
  · have hsupport' : N - m < K - r := by omega
    unfold hypergeomPMF
    rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hsupport),
      Nat.choose_eq_zero_of_lt hsupport']
    simp

theorem sum_hypergeomPMF
    {N K m : ℕ} (hK : K ≤ N) (hm : m ≤ N) :
    ∑ r ∈ Finset.range (m + 1), hypergeomPMF N K m r = 1 := by
  have hv := Nat.add_choose_eq K (N - K) m
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have hKN : K + (N - K) = N := Nat.add_sub_of_le hK
  rw [hKN] at hv
  have hchoose : (Nat.choose N m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hm))
  have hvReal : (Nat.choose N m : ℝ) =
      ∑ r ∈ Finset.range (m + 1),
        (Nat.choose K r : ℝ) * (Nat.choose (N - K) (m - r) : ℝ) := by
    exact_mod_cast hv
  unfold hypergeomPMF
  rw [← Finset.sum_div]
  simp_rw [Nat.cast_mul]
  rw [← hvReal]
  field_simp

def finiteMean {α : Type*} [DecidableEq α]
    (U : Finset α) (z : α → ℝ) : ℝ :=
  (∑ x ∈ U, z x) / (U.card : ℝ)

def samplingMgf {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (z : α → ℝ) (t : ℝ) : ℝ :=
  (∑ S ∈ U.powersetCard m,
      Real.exp (t * ((∑ x ∈ S, z x) - (m : ℝ) * finiteMean U z))) /
    ((Nat.choose U.card m) : ℝ)

def smallSamplingB (N m : ℕ) : ℝ :=
  (((N - m : ℕ) : ℝ) ^ 2) *
    ∑ ell ∈ Finset.Icc (N - m) (N - 1), (1 : ℝ) / ((ell : ℝ) ^ 2)

@[simp]
lemma smallSamplingB_zero (N : ℕ) : smallSamplingB N 0 = 0 := by
  cases N <;> simp [smallSamplingB]

lemma smallSamplingB_step
    (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) :
    smallSamplingB N m =
      ((((N - m : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) ^ 2) +
        smallSamplingB (N - 1) (m - 1) := by
  have hlower : N - m ≤ N - 1 := by omega
  have hinterval :
      Finset.Icc (N - m) (N - 1) =
        insert (N - 1) (Finset.Icc (N - m) (N - 2)) := by
    ext ell
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨hlo, hhi⟩
      by_cases htop : ell = N - 1
      · exact Or.inl htop
      · exact Or.inr ⟨hlo, by omega⟩
    · rintro (rfl | ⟨hlo, hhi⟩)
      · exact ⟨hlower, le_rfl⟩
      · exact ⟨hlo, by omega⟩
  have hnotmem : N - 1 ∉ Finset.Icc (N - m) (N - 2) := by
    intro h
    have := (Finset.mem_Icc.mp h).2
    omega
  have hNm : (N - 1) - (m - 1) = N - m := by omega
  have hNtop : (N - 1) - 1 = N - 2 := by omega
  have hN1 : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N - 1 ≠ 0)
  unfold smallSamplingB
  rw [hNm, hNtop, hinterval, Finset.sum_insert hnotmem]
  field_simp [hN1]

lemma centered_sum_insert_decomposition
    {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (z : α → ℝ) (x : α) (T : Finset α)
    (hxU : x ∈ U) (hxT : x ∉ T) (hN : 2 ≤ U.card)
    (hm : 1 ≤ m) (hmN : m ≤ U.card) :
    (∑ i ∈ insert x T, z i) - (m : ℝ) * finiteMean U z =
      ((∑ i ∈ T, z i) - ((m - 1 : ℕ) : ℝ) * finiteMean (U.erase x) z) +
        ((((U.card - m : ℕ) : ℝ) / ((U.card - 1 : ℕ) : ℝ)) *
          (z x - finiteMean U z)) := by
  have hcard : (U.erase x).card = U.card - 1 := by
    rw [Finset.card_erase_of_mem hxU]
  have hsum : (∑ i ∈ U.erase x, z i) = (∑ i ∈ U, z i) - z x := by
    rw [← Finset.sum_erase_add _ _ hxU]
    ring
  have hN0 : (U.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : U.card ≠ 0)
  have hN1 : ((U.card - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : U.card - 1 ≠ 0)
  have hNne : (U.card : ℝ) ≠ 1 := by
    exact_mod_cast (by omega : U.card ≠ 1)
  have hNsub : (U.card : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hNne
  rw [Finset.sum_insert hxT]
  unfold finiteMean
  rw [hcard, hsum]
  rw [Nat.cast_sub hm, Nat.cast_sub hmN,
    Nat.cast_sub (by omega : 1 ≤ U.card)]
  field_simp [hN0, hN1, hNsub]
  ring

theorem finite_uniform_hoeffding
    {α : Type*} [Fintype α] [Nonempty α]
    (z : α → ℝ) (a b t : ℝ)
    (hmean : (∑ x, z x) / (Fintype.card α : ℝ) = 0)
    (hbdd : ∀ x, a ≤ z x ∧ z x ≤ b) :
    (∑ x, Real.exp (t * z x)) / (Fintype.card α : ℝ) ≤
      Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  letI : MeasurableSpace α := ⊤
  let μ : MeasureTheory.Measure α := (PMF.uniformOfFintype α).toMeasure
  have hmean' : (∫ x, z x ∂μ) = 0 := by
    rw [PMF.integral_eq_sum]
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, smul_eq_mul]
    rw [← Finset.mul_sum]
    simpa [div_eq_mul_inv, mul_comm] using hmean
  have hbdd' : ∀ᵐ x ∂μ, a ≤ z x ∧ z x ≤ b := Filter.Eventually.of_forall hbdd
  have h := bounded_centered_mgf μ z a b t
    (measurable_of_finite z).aemeasurable hmean' hbdd'
  rw [PMF.integral_eq_sum] at h
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul] at h
  rw [← Finset.mul_sum] at h
  simpa [div_eq_mul_inv, mul_comm] using h

theorem sampling_outer_mgf_bound
    {α : Type*} [DecidableEq α]
    (U : Finset α) (z : α → ℝ) (t c : ℝ)
    (hU : U.Nonempty) (hc : 0 ≤ c)
    (hbdd : ∀ x ∈ U, (0 : ℝ) ≤ z x ∧ z x ≤ 1) :
    (∑ x ∈ U, Real.exp (t * (c * (z x - finiteMean U z)))) /
        (U.card : ℝ) ≤
      Real.exp (t ^ 2 * c ^ 2 / 8) := by
  let ⟨x0, hx0⟩ := hU
  letI : Nonempty ↥U := ⟨⟨x0, hx0⟩⟩
  let w : (↥U) → ℝ := fun x => c * (z x - finiteMean U z)
  let a : ℝ := -c * finiteMean U z
  let b : ℝ := c * (1 - finiteMean U z)
  have hcard : Fintype.card (↥U) = U.card := Fintype.card_coe U
  have hcard0 : (U.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hU)
  have hsum : (∑ x : ↥U, z x) = ∑ x ∈ U, z x := by
    simpa only [Finset.univ_eq_attach] using
      (Finset.sum_attach U fun x => z x)
  have hmean : (∑ x : ↥U, w x) / (Fintype.card (↥U) : ℝ) = 0 := by
    simp only [w, hcard]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    unfold finiteMean
    field_simp [hcard0]
    ring
  have hbounds : ∀ x : ↥U, a ≤ w x ∧ w x ≤ b := by
    intro x
    have hx := hbdd x x.property
    constructor <;> dsimp [a, b, w] <;> nlinarith
  have h := finite_uniform_hoeffding w a b t hmean hbounds
  simp only [hcard, w, a, b] at h
  have hsumexp :
      (∑ x : ↥U, Real.exp (t * (c * (z x - finiteMean U z)))) =
        ∑ x ∈ U, Real.exp (t * (c * (z x - finiteMean U z))) := by
    simpa only [Finset.univ_eq_attach] using
      (Finset.sum_attach U fun x => Real.exp (t * (c * (z x - finiteMean U z))))
  rw [hsumexp] at h
  convert h using 1
  ring_nf

theorem sum_first_then_rest
    {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (f : Finset α → ℝ) (hm : 1 ≤ m) :
    (∑ x ∈ U, ∑ T ∈ (U.erase x).powersetCard (m - 1), f (insert x T)) =
      (m : ℝ) * ∑ S ∈ U.powersetCard m, f S := by
  let L : Finset (Sigma fun _x : α => Finset α) :=
    U.sigma fun x => (U.erase x).powersetCard (m - 1)
  let R : Finset (Sigma fun _S : Finset α => α) :=
    (U.powersetCard m).sigma fun S => S
  have hleft :
      (∑ x ∈ U, ∑ T ∈ (U.erase x).powersetCard (m - 1), f (insert x T)) =
        ∑ z ∈ L, f (insert z.1 z.2) := by
    simp only [L, Finset.sum_sigma']
  have hright :
      (m : ℝ) * ∑ S ∈ U.powersetCard m, f S =
        ∑ z ∈ R, f z.1 := by
    calc
      (m : ℝ) * ∑ S ∈ U.powersetCard m, f S =
          ∑ S ∈ U.powersetCard m, (m : ℝ) * f S := by rw [Finset.mul_sum]
      _ = ∑ S ∈ U.powersetCard m, ∑ _x ∈ S, f S := by
        apply Finset.sum_congr rfl
        intro S hS
        have hcard : S.card = m := (Finset.mem_powersetCard.mp hS).2
        simp [hcard]
      _ = ∑ z ∈ R, f z.1 := by
        simpa only [R] using
          (Finset.sum_sigma' (U.powersetCard m) (fun S => S) (fun S _x => f S))
  rw [hleft, hright]
  let forward : (Sigma fun _x : α => Finset α) →
      (Sigma fun _S : Finset α => α) :=
    fun z => ⟨insert z.1 z.2, z.1⟩
  let backward : (Sigma fun _S : Finset α => α) →
      (Sigma fun _x : α => Finset α) :=
    fun z => ⟨z.2, z.1.erase z.2⟩
  apply Finset.sum_bij' (fun z _ => forward z) (fun z _ => backward z)
  · rintro ⟨x, T⟩ h
    simp only [L, Finset.mem_sigma] at h
    rcases h with ⟨hxU, hT⟩
    have hTsub : T ⊆ U.erase x := (Finset.mem_powersetCard.mp hT).1
    have hxT : x ∉ T := fun hx => (Finset.notMem_erase x U) (hTsub hx)
    have hTcard : T.card = m - 1 := (Finset.mem_powersetCard.mp hT).2
    have hcard : (insert x T).card = m := by
      rw [Finset.card_insert_of_notMem hxT, hTcard]
      omega
    simp only [R, Finset.mem_sigma]
    exact ⟨Finset.mem_powersetCard.mpr ⟨by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyT
      · exact hxU
      · exact (Finset.erase_subset x U) (hTsub hyT), hcard⟩,
      Finset.mem_insert_self x T⟩
  · rintro ⟨S, x⟩ h
    simp only [R, Finset.mem_sigma] at h
    rcases h with ⟨hS, hxS⟩
    have hSsub : S ⊆ U := (Finset.mem_powersetCard.mp hS).1
    have hScard : S.card = m := (Finset.mem_powersetCard.mp hS).2
    simp only [L, Finset.mem_sigma]
    refine ⟨hSsub hxS, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · intro y hy
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, hSsub (Finset.mem_erase.mp hy).2⟩
    · rw [Finset.card_erase_of_mem hxS, hScard]
  · rintro ⟨x, T⟩ h
    simp only [L, Finset.mem_sigma] at h
    rcases h with ⟨hxU, hT⟩
    have hTsub : T ⊆ U.erase x := (Finset.mem_powersetCard.mp hT).1
    have hxT : x ∉ T := fun hx => (Finset.notMem_erase x U) (hTsub hx)
    simp [backward, forward, hxT]
  · rintro ⟨S, x⟩ h
    simp only [R, Finset.mem_sigma] at h
    rcases h with ⟨hS, hxS⟩
    simp [backward, forward, Finset.insert_erase hxS]
  · rintro ⟨x, T⟩ h
    rfl

theorem samplingMgf_step
    {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (z : α → ℝ) (t : ℝ)
    (hN : 2 ≤ U.card) (hm : 1 ≤ m) (hmN : m ≤ U.card) :
    samplingMgf U m z t =
      (1 / (U.card : ℝ)) *
        ∑ x ∈ U,
          Real.exp (t *
            ((((U.card - m : ℕ) : ℝ) / ((U.card - 1 : ℕ) : ℝ)) *
              (z x - finiteMean U z))) *
            samplingMgf (U.erase x) (m - 1) z t := by
  let c : ℝ := ((U.card - m : ℕ) : ℝ) / ((U.card - 1 : ℕ) : ℝ)
  let f : Finset α → ℝ := fun S =>
    Real.exp (t * ((∑ i ∈ S, z i) - (m : ℝ) * finiteMean U z))
  have hdouble := sum_first_then_rest U m f hm
  have hdouble' :
      (∑ x ∈ U,
          Real.exp (t * (c * (z x - finiteMean U z))) *
            ∑ T ∈ (U.erase x).powersetCard (m - 1),
              Real.exp (t *
                ((∑ i ∈ T, z i) - ((m - 1 : ℕ) : ℝ) *
                  finiteMean (U.erase x) z))) =
        (m : ℝ) * ∑ S ∈ U.powersetCard m, f S := by
    calc
      _ = ∑ x ∈ U, ∑ T ∈ (U.erase x).powersetCard (m - 1),
          f (insert x T) := by
        apply Finset.sum_congr rfl
        intro x hxU
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        have hTsub : T ⊆ U.erase x := (Finset.mem_powersetCard.mp hT).1
        have hxT : x ∉ T := fun hx => (Finset.notMem_erase x U) (hTsub hx)
        simp only [f]
        rw [centered_sum_insert_decomposition U m z x T hxU hxT hN hm hmN]
        simp only [c, Real.exp_add, mul_add]
        rw [mul_comm]
      _ = _ := hdouble
  have hchoose :
      U.card * Nat.choose (U.card - 1) (m - 1) = Nat.choose U.card m * m := by
    have hNrec : U.card - 1 + 1 = U.card := by omega
    have hmrec : m - 1 + 1 = m := by omega
    simpa only [hNrec, hmrec] using
      Nat.add_one_mul_choose_eq (U.card - 1) (m - 1)
  have hchoose0 : (Nat.choose U.card m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hmN))
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hN0 : (U.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : U.card ≠ 0)
  have hrest : m - 1 ≤ U.card - 1 := by omega
  have hchooseRest0 : (Nat.choose (U.card - 1) (m - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hrest))
  have hinner : ∀ x ∈ U,
      samplingMgf (U.erase x) (m - 1) z t =
        (∑ T ∈ (U.erase x).powersetCard (m - 1),
            Real.exp (t * ((∑ i ∈ T, z i) - ((m - 1 : ℕ) : ℝ) *
              finiteMean (U.erase x) z))) /
          (Nat.choose (U.card - 1) (m - 1) : ℝ) := by
    intro x hx
    unfold samplingMgf
    rw [Finset.card_erase_of_mem hx]
  change
    (∑ S ∈ U.powersetCard m, f S) / (Nat.choose U.card m : ℝ) =
      (1 / (U.card : ℝ)) *
        ∑ x ∈ U,
          Real.exp (t *
            ((((U.card - m : ℕ) : ℝ) / ((U.card - 1 : ℕ) : ℝ)) *
              (z x - finiteMean U z))) *
            samplingMgf (U.erase x) (m - 1) z t
  have hsumInner :
      (∑ x ∈ U,
          Real.exp (t *
            ((((U.card - m : ℕ) : ℝ) / ((U.card - 1 : ℕ) : ℝ)) *
              (z x - finiteMean U z))) *
            samplingMgf (U.erase x) (m - 1) z t) =
        ∑ x ∈ U,
          Real.exp (t *
            ((((U.card - m : ℕ) : ℝ) / ((U.card - 1 : ℕ) : ℝ)) *
              (z x - finiteMean U z))) *
            ((∑ T ∈ (U.erase x).powersetCard (m - 1),
                Real.exp (t * ((∑ i ∈ T, z i) - ((m - 1 : ℕ) : ℝ) *
                  finiteMean (U.erase x) z))) /
              (Nat.choose (U.card - 1) (m - 1) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hinner x hx]
  have hfactor :
      (∑ x ∈ U,
          Real.exp (t *
            ((((U.card - m : ℕ) : ℝ) / ((U.card - 1 : ℕ) : ℝ)) *
              (z x - finiteMean U z))) *
            ((∑ T ∈ (U.erase x).powersetCard (m - 1),
                Real.exp (t * ((∑ i ∈ T, z i) - ((m - 1 : ℕ) : ℝ) *
                  finiteMean (U.erase x) z))) /
              (Nat.choose (U.card - 1) (m - 1) : ℝ))) =
        (∑ x ∈ U,
            Real.exp (t *
              ((((U.card - m : ℕ) : ℝ) / ((U.card - 1 : ℕ) : ℝ)) *
                (z x - finiteMean U z))) *
              ∑ T ∈ (U.erase x).powersetCard (m - 1),
                Real.exp (t * ((∑ i ∈ T, z i) - ((m - 1 : ℕ) : ℝ) *
                  finiteMean (U.erase x) z))) /
          (Nat.choose (U.card - 1) (m - 1) : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hsumInner]
  rw [hfactor]
  change
    (∑ S ∈ U.powersetCard m, f S) / (Nat.choose U.card m : ℝ) =
      (1 / (U.card : ℝ)) *
        ((∑ x ∈ U,
            Real.exp (t * (c * (z x - finiteMean U z))) *
              ∑ T ∈ (U.erase x).powersetCard (m - 1),
                Real.exp (t * ((∑ i ∈ T, z i) - ((m - 1 : ℕ) : ℝ) *
                  finiteMean (U.erase x) z))) /
          (Nat.choose (U.card - 1) (m - 1) : ℝ))
  rw [hdouble']
  have hchooseReal :
      (U.card : ℝ) * (Nat.choose (U.card - 1) (m - 1) : ℝ) =
        (Nat.choose U.card m : ℝ) * (m : ℝ) := by
    exact_mod_cast hchoose
  field_simp [hchoose0, hchooseRest0, hm0, hN0]
  linear_combination
    (∑ S ∈ U.powersetCard m, f S) * hchooseReal

theorem samplingMgf_le_smallSamplingB
    {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (z : α → ℝ) (t : ℝ)
    (hm : m ≤ U.card / 2)
    (hbdd : ∀ x ∈ U, (0 : ℝ) ≤ z x ∧ z x ≤ 1) :
    samplingMgf U m z t ≤
      Real.exp ((t ^ 2 / 8) * smallSamplingB U.card m) := by
  induction m generalizing U with
  | zero => simp [samplingMgf]
  | succ m ih =>
      have hm0 : 1 ≤ m + 1 := by omega
      have hmN : m + 1 ≤ U.card := by omega
      have hN : 2 ≤ U.card := by omega
      have hU : U.Nonempty := Finset.card_pos.mp (by omega)
      let c : ℝ :=
        ((U.card - (m + 1) : ℕ) : ℝ) / ((U.card - 1 : ℕ) : ℝ)
      have hc : 0 ≤ c := by positivity
      have hstep := samplingMgf_step U (m + 1) z t hN hm0 hmN
      have hinner : ∀ x ∈ U,
          samplingMgf (U.erase x) m z t ≤
            Real.exp ((t ^ 2 / 8) * smallSamplingB (U.card - 1) m) := by
        intro x hx
        have hcard : (U.erase x).card = U.card - 1 :=
          Finset.card_erase_of_mem hx
        have hmSmall : m ≤ (U.erase x).card / 2 := by
          rw [hcard]
          omega
        have hbddErase : ∀ y ∈ U.erase x, (0 : ℝ) ≤ z y ∧ z y ≤ 1 := by
          intro y hy
          exact hbdd y (Finset.erase_subset x U hy)
        simpa only [hcard] using ih (U.erase x) hmSmall hbddErase
      have hsum :
          (∑ x ∈ U,
              Real.exp (t * (c * (z x - finiteMean U z))) *
                samplingMgf (U.erase x) m z t) ≤
            ∑ x ∈ U,
              Real.exp (t * (c * (z x - finiteMean U z))) *
                Real.exp ((t ^ 2 / 8) * smallSamplingB (U.card - 1) m) := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hinner x hx) (Real.exp_pos _).le
      have houter := sampling_outer_mgf_bound U z t c hU hc hbdd
      rw [hstep]
      change
        (1 / (U.card : ℝ)) *
            ∑ x ∈ U,
              Real.exp (t * (c * (z x - finiteMean U z))) *
                samplingMgf (U.erase x) m z t ≤ _
      calc
        _ ≤ (1 / (U.card : ℝ)) *
            ∑ x ∈ U,
              Real.exp (t * (c * (z x - finiteMean U z))) *
                Real.exp ((t ^ 2 / 8) * smallSamplingB (U.card - 1) m) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = Real.exp ((t ^ 2 / 8) * smallSamplingB (U.card - 1) m) *
            ((∑ x ∈ U, Real.exp (t * (c * (z x - finiteMean U z)))) /
              (U.card : ℝ)) := by
          rw [← Finset.sum_mul]
          ring
        _ ≤ Real.exp ((t ^ 2 / 8) * smallSamplingB (U.card - 1) m) *
            Real.exp (t ^ 2 * c ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left houter (Real.exp_pos _).le
        _ = Real.exp ((t ^ 2 / 8) * smallSamplingB U.card (m + 1)) := by
          rw [← Real.exp_add, smallSamplingB_step U.card (m + 1) hN hm0 hmN]
          simp only [c]
          rw [Nat.add_sub_cancel]
          congr 1
          ring

lemma centered_sum_complement
    {α : Type*} [DecidableEq α]
    (U S : Finset α) (m : ℕ) (z : α → ℝ)
    (hSsub : S ⊆ U) (hScard : S.card = m) (hU : U.Nonempty) :
    (∑ i ∈ U \ S, z i) - ((U.card - m : ℕ) : ℝ) * finiteMean U z =
      -((∑ i ∈ S, z i) - (m : ℝ) * finiteMean U z) := by
  have hmU : m ≤ U.card := by
    rw [← hScard]
    exact Finset.card_le_card hSsub
  have hcard0 : (U.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hU)
  rw [Finset.sum_sdiff_eq_sub hSsub, Nat.cast_sub hmU]
  unfold finiteMean
  field_simp [hcard0]
  ring

theorem samplingMgf_complement
    {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (z : α → ℝ) (t : ℝ)
    (hmU : m ≤ U.card) :
    samplingMgf U m z t = samplingMgf U (U.card - m) z (-t) := by
  by_cases hUempty : U = ∅
  · subst U
    have hm : m = 0 := by simpa using hmU
    subst m
    simp [samplingMgf]
  have hU : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUempty
  let leftTerm : Finset α → ℝ := fun S =>
    Real.exp (t * ((∑ i ∈ S, z i) - (m : ℝ) * finiteMean U z))
  let rightTerm : Finset α → ℝ := fun S =>
    Real.exp ((-t) *
      ((∑ i ∈ S, z i) - ((U.card - m : ℕ) : ℝ) * finiteMean U z))
  have hsum :
      (∑ S ∈ U.powersetCard m, leftTerm S) =
        ∑ T ∈ U.powersetCard (U.card - m), rightTerm T := by
    apply Finset.sum_bij'
      (fun S _ => U \ S) (fun T _ => U \ T)
    · intro S hS
      have hSdata := Finset.mem_powersetCard.mp hS
      exact Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset,
        by rw [Finset.card_sdiff_of_subset hSdata.1, hSdata.2]⟩
    · intro T hT
      have hTdata := Finset.mem_powersetCard.mp hT
      refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, ?_⟩
      rw [Finset.card_sdiff_of_subset hTdata.1, hTdata.2]
      omega
    · intro S hS
      have hSsub := (Finset.mem_powersetCard.mp hS).1
      exact Finset.sdiff_sdiff_eq_self hSsub
    · intro T hT
      have hTsub := (Finset.mem_powersetCard.mp hT).1
      exact Finset.sdiff_sdiff_eq_self hTsub
    · intro S hS
      have hSdata := Finset.mem_powersetCard.mp hS
      simp only [leftTerm, rightTerm]
      rw [centered_sum_complement U S m z hSdata.1 hSdata.2 hU]
      congr 1
      ring
  unfold samplingMgf
  change (∑ S ∈ U.powersetCard m, leftTerm S) / (Nat.choose U.card m : ℝ) =
    (∑ T ∈ U.powersetCard (U.card - m), rightTerm T) /
      (Nat.choose U.card (U.card - m) : ℝ)
  rw [hsum, Nat.choose_symm hmU]

theorem samplingMgf_le_hypergeomB
    {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (z : α → ℝ) (t : ℝ)
    (hmU : m ≤ U.card)
    (hbdd : ∀ x ∈ U, (0 : ℝ) ≤ z x ∧ z x ≤ 1) :
    samplingMgf U m z t ≤
      Real.exp ((t ^ 2 / 8) * hypergeomB U.card m) := by
  by_cases hmSmall : m ≤ U.card / 2
  · have hs : Nat.min m (U.card - m) = m := by
      apply Nat.min_eq_left
      omega
    have h := samplingMgf_le_smallSamplingB U m z t hmSmall hbdd
    simpa [hypergeomB, smallSamplingB, hs] using h
  · have hcompSmall : U.card - m ≤ U.card / 2 := by omega
    have hbddComp := hbdd
    have h := samplingMgf_le_smallSamplingB U (U.card - m) z (-t)
      hcompSmall hbddComp
    rw [samplingMgf_complement U m z t hmU]
    have hs : Nat.min m (U.card - m) = U.card - m := by
      apply Nat.min_eq_right
      omega
    simpa [hypergeomB, smallSamplingB, hs] using h

theorem samplingMgf_pos
    {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (z : α → ℝ) (t : ℝ) (hmU : m ≤ U.card) :
    0 < samplingMgf U m z t := by
  have hsets : (U.powersetCard m).Nonempty :=
    Finset.powersetCard_nonempty.mpr hmU
  have hsum : 0 <
      ∑ S ∈ U.powersetCard m,
        Real.exp (t * ((∑ x ∈ S, z x) - (m : ℝ) * finiteMean U z)) := by
    exact Finset.sum_pos (fun _ _ => Real.exp_pos _) hsets
  have hchoose : 0 < (Nat.choose U.card m : ℝ) := by
    exact_mod_cast Nat.choose_pos hmU
  unfold samplingMgf
  positivity

theorem log_samplingMgf_le_hypergeomB
    {α : Type*} [DecidableEq α]
    (U : Finset α) (m : ℕ) (z : α → ℝ) (t : ℝ)
    (hmU : m ≤ U.card)
    (hbdd : ∀ x ∈ U, (0 : ℝ) ≤ z x ∧ z x ≤ 1) :
    Real.log (samplingMgf U m z t) ≤ (t ^ 2 / 8) * hypergeomB U.card m := by
  have hpos := samplingMgf_pos U m z t hmU
  have hmgf := samplingMgf_le_hypergeomB U m z t hmU hbdd
  calc
    Real.log (samplingMgf U m z t) ≤
        Real.log (Real.exp ((t ^ 2 / 8) * hypergeomB U.card m)) :=
      Real.log_le_log hpos hmgf
    _ = (t ^ 2 / 8) * hypergeomB U.card m := Real.log_exp _

/-- MGF of the centered count obtained by uniformly sampling an `m`-subset
from a population whose first `K` entries are one and whose remaining entries
are zero. -/
def hypergeomMgf (N K m : ℕ) (t : ℝ) : ℝ :=
  samplingMgf (Finset.univ : Finset (Fin N)) m
    (fun i => if i.val < K then (1 : ℝ) else 0) t

theorem hypergeometric_mgf_bound
    {N K m : ℕ} (hK : K ≤ N) (hm : m ≤ N) (t : ℝ) :
    Real.log (hypergeomMgf N K m t) ≤
      (t ^ 2 / 8) * hypergeomB N m := by
  unfold hypergeomMgf
  have h := log_samplingMgf_le_hypergeomB
    (Finset.univ : Finset (Fin N)) m
    (fun i => if i.val < K then (1 : ℝ) else 0) t
    (by simpa using hm) (by
      intro i hi
      dsimp
      split_ifs <;> norm_num)
  simpa using h

/-- A closed compatibility bundle for the project-level dependency graph. -/
structure HypergeometricAnalyticInputs : Prop where
  hypergeometric_mgf_bound :
    ∀ {N K m : ℕ} (hN : 1 ≤ N)
      (hK : K ≤ N) (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) (t : ℝ),
      Real.log (hypergeomMgf N K m t) ≤
        (t ^ 2 / 8) * hypergeomB N m

/-- The finite sampling martingale supplies every formerly named
hypergeometric analytic input. -/
def hypergeometricAnalyticInputs : HypergeometricAnalyticInputs where
  hypergeometric_mgf_bound := by
    intro N K m hN hK hm0 hmN t
    exact hypergeometric_mgf_bound hK (by omega) t

/-! ## Identification with the classical hypergeometric mass function -/

/-- Partition a fixed-cardinality subset into its success and failure parts.
This is the finite bijection behind the hypergeometric mass formula. -/
theorem sum_powersetCard_partition
    {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hdisj : Disjoint P Q) (m : ℕ) (f : ℕ → ℝ) :
    (∑ S ∈ (P ∪ Q).powersetCard m, f ((S ∩ P).card)) =
      ∑ r ∈ Finset.range (m + 1),
        (Nat.choose P.card r : ℝ) * (Nat.choose Q.card (m - r) : ℝ) * f r := by
  let R : Finset (Sigma fun _r : ℕ => Finset α × Finset α) :=
    (Finset.range (m + 1)).sigma fun r =>
      (P.powersetCard r) ×ˢ (Q.powersetCard (m - r))
  have hright :
      (∑ r ∈ Finset.range (m + 1),
          (Nat.choose P.card r : ℝ) * (Nat.choose Q.card (m - r) : ℝ) * f r) =
        ∑ z ∈ R, f z.1 := by
    rw [show (∑ z ∈ R, f z.1) =
        ∑ r ∈ Finset.range (m + 1),
          ∑ p ∈ (P.powersetCard r) ×ˢ (Q.powersetCard (m - r)), f r by
      simpa only [R] using
        (Finset.sum_sigma' (Finset.range (m + 1))
          (fun r => (P.powersetCard r) ×ˢ (Q.powersetCard (m - r)))
          (fun r _ => f r)).symm]
    apply Finset.sum_congr rfl
    intro r hr
    simp [Finset.card_product]
  rw [hright]
  let forward : Finset α → Sigma fun _r : ℕ => Finset α × Finset α :=
    fun S => ⟨(S ∩ P).card, (S ∩ P, S ∩ Q)⟩
  let backward : (Sigma fun _r : ℕ => Finset α × Finset α) → Finset α :=
    fun z => z.2.1 ∪ z.2.2
  apply Finset.sum_bij' (fun S _ => forward S) (fun z _ => backward z)
  · intro S hS
    have hSdata := Finset.mem_powersetCard.mp hS
    have hAcard : (S ∩ P).card ≤ m := by
      rw [← hSdata.2]
      exact Finset.card_le_card Finset.inter_subset_left
    have hsplit : S ∩ P ∪ S ∩ Q = S := by
      apply Finset.Subset.antisymm
      · exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
      · intro x hx
        rcases Finset.mem_union.mp (hSdata.1 hx) with hxP | hxQ
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxP⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxQ⟩)
    have hABdisj : Disjoint (S ∩ P) (S ∩ Q) :=
      Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisj
    have hBcard : (S ∩ Q).card = m - (S ∩ P).card := by
      have hc := Finset.card_union_of_disjoint hABdisj
      rw [hsplit, hSdata.2] at hc
      omega
    simp only [R, Finset.mem_sigma, forward, Finset.mem_product]
    exact ⟨Finset.mem_range.mpr (by omega),
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, rfl⟩,
        Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hBcard⟩⟩⟩
  · rintro ⟨r, A, B⟩ h
    simp only [R, Finset.mem_sigma, Finset.mem_product] at h
    rcases h with ⟨hr, hA, hB⟩
    have hAdata := Finset.mem_powersetCard.mp hA
    have hBdata := Finset.mem_powersetCard.mp hB
    have hABdisj : Disjoint A B := Disjoint.mono hAdata.1 hBdata.1 hdisj
    refine Finset.mem_powersetCard.mpr ⟨Finset.union_subset
      (hAdata.1.trans Finset.subset_union_left)
      (hBdata.1.trans Finset.subset_union_right), ?_⟩
    rw [Finset.card_union_of_disjoint hABdisj, hAdata.2, hBdata.2]
    have hrlt := Finset.mem_range.mp hr
    omega
  · intro S hS
    have hSdata := Finset.mem_powersetCard.mp hS
    apply Finset.Subset.antisymm
    · exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
    · intro x hx
      rcases Finset.mem_union.mp (hSdata.1 hx) with hxP | hxQ
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxP⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxQ⟩)
  · rintro ⟨r, A, B⟩ h
    simp only [R, Finset.mem_sigma, Finset.mem_product] at h
    rcases h with ⟨hr, hA, hB⟩
    have hAdata := Finset.mem_powersetCard.mp hA
    have hBdata := Finset.mem_powersetCard.mp hB
    have hAP : (A ∪ B) ∩ P = A := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxA | hxB, hxP⟩
        · exact hxA
        · exact (Finset.disjoint_left.mp hdisj hxP (hBdata.1 hxB)).elim
      · intro hxA
        exact ⟨Or.inl hxA, hAdata.1 hxA⟩
    have hBQ : (A ∪ B) ∩ Q = B := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxA | hxB, hxQ⟩
        · exact (Finset.disjoint_left.mp hdisj (hAdata.1 hxA) hxQ).elim
        · exact hxB
      · intro hxB
        exact ⟨Or.inr hxB, hBdata.1 hxB⟩
    have hfirst : ((A ∪ B) ∩ P).card = r := by rw [hAP, hAdata.2]
    apply Sigma.ext hfirst
    exact heq_of_eq (Prod.ext hAP hBQ)
  · intro S hS
    rfl

/-- The subset-sampling definition expands into the usual binomial-coefficient
formula for a two-level population. -/
theorem samplingMgf_indicator_partition
    {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hdisj : Disjoint P Q) (m : ℕ) (t : ℝ) :
    samplingMgf (P ∪ Q) m (fun x => if x ∈ P then (1 : ℝ) else 0) t =
      (∑ r ∈ Finset.range (m + 1),
          (Nat.choose P.card r : ℝ) * (Nat.choose Q.card (m - r) : ℝ) *
            Real.exp (t *
              ((r : ℝ) - (m : ℝ) * (P.card : ℝ) / ((P ∪ Q).card : ℝ)))) /
        (Nat.choose (P ∪ Q).card m : ℝ) := by
  have hmean :
      finiteMean (P ∪ Q) (fun x => if x ∈ P then (1 : ℝ) else 0) =
        (P.card : ℝ) / ((P ∪ Q).card : ℝ) := by
    unfold finiteMean
    congr 1
    simp
  have hsums : ∀ S : Finset α,
      (∑ x ∈ S, if x ∈ P then (1 : ℝ) else 0) = ((S ∩ P).card : ℝ) := by
    intro S
    simp
  unfold samplingMgf
  rw [hmean]
  simp_rw [hsums]
  congr 1
  let f : ℕ → ℝ := fun r => Real.exp (t *
    ((r : ℝ) - (m : ℝ) * (P.card : ℝ) / ((P ∪ Q).card : ℝ)))
  calc
    (∑ S ∈ (P ∪ Q).powersetCard m,
        Real.exp (t * ((S ∩ P).card - (m : ℝ) *
          ((P.card : ℝ) / ((P ∪ Q).card : ℝ))))) =
        ∑ S ∈ (P ∪ Q).powersetCard m, f ((S ∩ P).card) := by
      apply Finset.sum_congr rfl
      intro S hS
      simp only [f]
      congr 1
      ring
    _ = _ := sum_powersetCard_partition P Q hdisj m f

/-- The canonical set of success coordinates. -/
def initialSuccessSet (N K : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => i.val < K

/-- The first `K` coordinates form a copy of `Fin K`. -/
def initialSuccessEquiv {N K : ℕ} (hK : K ≤ N) :
    Fin K ≃ ↥(initialSuccessSet N K) where
  toFun i := ⟨Fin.castLE hK i, by simp [initialSuccessSet, i.isLt]⟩
  invFun i := ⟨i.val.val, (Finset.mem_filter.mp i.property).2⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

theorem card_initialSuccessSet {N K : ℕ} (hK : K ≤ N) :
    (initialSuccessSet N K).card = K := by
  have hcard := Fintype.card_congr (initialSuccessEquiv hK)
  simpa using hcard.symm

/-- The finite-subset MGF is exactly the MGF obtained from `hypergeomPMF`. -/
theorem hypergeomMgf_eq_pmf_sum
    {N K m : ℕ} (hK : K ≤ N) (t : ℝ) :
    hypergeomMgf N K m t =
      ∑ r ∈ Finset.range (m + 1),
        hypergeomPMF N K m r *
          Real.exp (t * ((r : ℝ) - (m : ℝ) * (K : ℝ) / (N : ℝ))) := by
  let P : Finset (Fin N) := initialSuccessSet N K
  let Q : Finset (Fin N) := Finset.univ \ P
  have hPsub : P ⊆ (Finset.univ : Finset (Fin N)) := Finset.subset_univ P
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    exact (Finset.mem_sdiff.mp hxQ).2 hxP
  have hunion : P ∪ Q = (Finset.univ : Finset (Fin N)) :=
    Finset.union_sdiff_of_subset hPsub
  have hPcard : P.card = K := by
    simpa only [P] using card_initialSuccessSet hK
  have hQcard : Q.card = N - K := by
    change (Finset.univ \ P).card = N - K
    rw [Finset.card_sdiff_of_subset hPsub, Finset.card_univ,
      Fintype.card_fin, hPcard]
  have hindicator :
      (fun i : Fin N => if i ∈ P then (1 : ℝ) else 0) =
        (fun i : Fin N => if i.val < K then (1 : ℝ) else 0) := by
    funext i
    simp [P, initialSuccessSet]
  have hgroup := samplingMgf_indicator_partition P Q hdisj m t
  rw [hunion, hindicator, hPcard, hQcard] at hgroup
  simp only [Finset.card_univ, Fintype.card_fin] at hgroup
  unfold hypergeomMgf
  rw [hgroup]
  unfold hypergeomPMF
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Nat.cast_mul]
  ring

/-- The centered hypergeometric MGF is symmetric in the number of successes
and the sample size. This is the probabilistic transpose symmetry used for
two-level vectors on a Hamming slice. -/
theorem hypergeomMgf_symm
    {N K m : ℕ} (hK : K ≤ N) (hm : m ≤ N) (t : ℝ) :
    hypergeomMgf N K m t = hypergeomMgf N m K t := by
  rw [hypergeomMgf_eq_pmf_sum hK t, hypergeomMgf_eq_pmf_sum hm t]
  by_cases hKm : K ≤ m
  · calc
      (∑ r ∈ Finset.range (m + 1),
          hypergeomPMF N K m r *
            Real.exp (t * ((r : ℝ) - (m : ℝ) * (K : ℝ) / (N : ℝ)))) =
          ∑ r ∈ Finset.range (K + 1),
            hypergeomPMF N K m r *
              Real.exp (t * ((r : ℝ) - (m : ℝ) * (K : ℝ) / (N : ℝ))) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro r hrBig hrSmall
        have hrK : K < r := by
          simp only [Finset.mem_range] at hrBig hrSmall
          omega
        unfold hypergeomPMF
        rw [Nat.choose_eq_zero_of_lt hrK]
        simp
      _ = ∑ r ∈ Finset.range (K + 1),
            hypergeomPMF N m K r *
              Real.exp (t * ((r : ℝ) - (K : ℝ) * (m : ℝ) / (N : ℝ))) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrK : r ≤ K := by
          simp only [Finset.mem_range] at hr
          omega
        rw [hypergeomPMF_symm hK hm hrK (hrK.trans hKm)]
        ring_nf
  · have hmK : m ≤ K := Nat.le_of_not_ge hKm
    calc
      (∑ r ∈ Finset.range (m + 1),
          hypergeomPMF N K m r *
            Real.exp (t * ((r : ℝ) - (m : ℝ) * (K : ℝ) / (N : ℝ)))) =
          ∑ r ∈ Finset.range (m + 1),
            hypergeomPMF N m K r *
              Real.exp (t * ((r : ℝ) - (K : ℝ) * (m : ℝ) / (N : ℝ))) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrm : r ≤ m := by
          simp only [Finset.mem_range] at hr
          omega
        rw [hypergeomPMF_symm hK hm (hrm.trans hmK) hrm]
        ring_nf
      _ = ∑ r ∈ Finset.range (K + 1),
            hypergeomPMF N m K r *
              Real.exp (t * ((r : ℝ) - (K : ℝ) * (m : ℝ) / (N : ℝ))) := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro r hrBig hrSmall
        have hrm : m < r := by
          simp only [Finset.mem_range] at hrBig hrSmall
          omega
        unfold hypergeomPMF
        rw [Nat.choose_eq_zero_of_lt hrm]
        simp

end ExchangeableHoeffding
