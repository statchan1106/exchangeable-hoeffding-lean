import Mathlib

set_option linter.unusedVariables false
/-!
# Exchangeable Hoeffding formalization without global axioms

This file is a safer version of the previous skeleton: it contains no global
`axiom` declarations and no proof holes.  Instead, the deep mathematical ingredients
are collected in the structure `ProofObligations`.  The exported theorem
`theorem_2_1` is then proved conditionally from these obligations.

This does **not** finish the full formal proof of the paper, but it prevents the
Lean environment from trusting unproved global constants.  To complete the
formalization, instantiate `ProofObligations` by proving each field.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace ExchangeableHoeffding

/-- Dot product on `Fin N → ℝ`. -/
def dot {N : ℕ} (a x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, a i * x i

/-- Squared Euclidean norm on `Fin N → ℝ`. -/
def normSq {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (a i) ^ 2

/-- Finite-population average of an `N`-vector. -/
def avg {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, x i) / (N : ℝ)

/-- Orthogonal projection onto the hyperplane perpendicular to the all-ones vector. -/
def projOnePerp {N : ℕ} (z : Fin N → ℝ) : Fin N → ℝ :=
  fun i => z i - (∑ j : Fin N, z j) / (N : ℝ)

/-- Zero-pad a vector indexed by `Fin n` into a vector indexed by `Fin N`. -/
def zeroPad {n N : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) : Fin N → ℝ :=
  fun i => if hi : i.val < n then w ⟨i.val, hi⟩ else 0

/-- The centered weighted sum in Theorem 2.1. -/
def centeredWeightedSum {n N : ℕ} (hn : n ≤ N)
    (w : Fin n → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin n, w i * (x (Fin.castLE hn i) - avg x)

/-- Coordinate permutation of an `N`-vector. -/
def permute {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => x (σ i)

/-- Exchangeability of the law of an `N`-vector. -/
def Exchangeable {N : ℕ} (μ : Measure (Fin N → ℝ)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), Measure.map (permute σ) μ = μ

/-- Almost-sure boundedness by `[-1, 1]` in every coordinate. -/
def BoundedByOne {N : ℕ} (μ : Measure (Fin N → ℝ)) : Prop :=
  ∀ᵐ x ∂μ, ∀ i : Fin N, (-1 : ℝ) ≤ x i ∧ x i ≤ 1

/-- The term in the definition of `Γ_N`, indexed by `s`. -/
def gammaTerm (N s : ℕ) : ℝ :=
  ((N : ℝ) * ((N - s : ℕ) : ℝ) / (s : ℝ)) *
    (∑ ℓ ∈ Finset.Icc (N - s) (N - 1), (1 : ℝ) / ((ℓ : ℝ) ^ 2))

/-- The finite-population inflation factor `Γ_N` from Theorem 2.1. -/
def Gamma (N : ℕ) : ℝ := by
  classical
  let S : Finset ℝ := (Finset.Icc 1 (N / 2)).image (fun s => gammaTerm N s)
  exact if h : S.Nonempty then S.max' h else 0

/-- Harmonic number `H_N = ∑_{j=1}^N 1/j`. -/
def harmonic (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ)

/-- Barber's inflation parameter `ε_N = (H_N - 1)/(N - H_N)`. -/
def epsilonBarber (N : ℕ) : ℝ :=
  (harmonic N - 1) / ((N : ℝ) - harmonic N)

/-- Closed-form version of `Γ_N`, split by parity. -/
def GammaClosed (N : ℕ) : ℝ :=
  if Even N then
    (N : ℝ) *
      (∑ ℓ ∈ Finset.Icc (N / 2) (N - 1), (1 : ℝ) / ((ℓ : ℝ) ^ 2))
  else
    ((N : ℝ) * ((N + 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) *
      (∑ ℓ ∈ Finset.Icc ((N + 1) / 2) (N - 1),
        (1 : ℝ) / ((ℓ : ℝ) ^ 2))

/-- Euclidean norm derived from `normSq`. -/
def l2Norm {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  Real.sqrt (normSq a)

/-- The threshold appearing in Corollary 2.2. -/
def tailThreshold {n N : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) (δ : ℝ) : ℝ :=
  l2Norm (projOnePerp (zeroPad hn w)) *
    Real.sqrt (2 * Gamma N * Real.log (1 / δ))

/-! ## Hamming slices and elementary symmetric polynomials -/

/-- The collection of all `k`-subsets of `Fin N`. -/
def sliceSubsets (N k : ℕ) : Finset (Finset (Fin N)) := by
  classical
  exact Finset.univ.filter (fun S : Finset (Fin N) => S.card = k)

/-- Average of a real-valued function over the uniform Hamming slice. -/
def sliceAverage {N : ℕ} (k : ℕ) (f : Finset (Fin N) → ℝ) : ℝ :=
  (∑ S ∈ sliceSubsets N k, f S) / ((Nat.choose N k) : ℝ)

/-- Elementary symmetric polynomial `e_k(z_1, …, z_N)`. -/
def elemSym {N : ℕ} (k : ℕ) (z : Fin N → ℝ) : ℝ :=
  ∑ S ∈ sliceSubsets N k, ∏ i ∈ S, z i

/-- The functional `F_{N,k}` from Proposition 4.4. -/
def sliceFunctional {N : ℕ} (k : ℕ) (y : Fin N → ℝ) : ℝ :=
  Real.log (elemSym k (fun i => Real.exp (y i)) / ((Nat.choose N k) : ℝ))

/-- A vector has at most two distinct coordinate values. -/
def AtMostTwoValues {N : ℕ} (y : Fin N → ℝ) : Prop :=
  ∃ α β : ℝ, ∀ i : Fin N, y i = α ∨ y i = β

/-- The sphere section `{∑ y_i = 0, ||y||₂ = ρ}` written using `normSq`. -/
def SphereSection {N : ℕ} (ρ : ℝ) (y : Fin N → ℝ) : Prop :=
  (∑ i : Fin N, y i = 0) ∧ normSq y = ρ ^ 2

/-- Hypergeometric probability mass function. -/
def hypergeomPMF (N K m r : ℕ) : ℝ :=
  ((Nat.choose K r * Nat.choose (N - K) (m - r)) : ℝ) /
    ((Nat.choose N m) : ℝ)

/-- MGF of the centered hypergeometric count `H - mK/N`. -/
def hypergeomMgf (N K m : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1),
    hypergeomPMF N K m r *
      Real.exp (t * ((r : ℝ) - (m : ℝ) * (K : ℝ) / (N : ℝ)))

/-- The factor `B_{N,m}` from Lemma 4.5. -/
def hypergeomB (N m : ℕ) : ℝ :=
  let s : ℕ := Nat.min m (N - m)
  (((N - s : ℕ) : ℝ) ^ 2) *
    (∑ ℓ ∈ Finset.Icc (N - s) (N - 1), (1 : ℝ) / ((ℓ : ℝ) ^ 2))

/-- The three-coordinate constrained objective from Lemma 4.3. -/
def threeObjective (A B : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  A * (∑ i : Fin 3, Real.exp (x i)) +
    B * (∑ i : Fin 3, Real.exp (-(x i)))

/-- The constraint set `u + v + z = s`, `u² + v² + z² = q`. -/
def ThreeSphereSection (s q : ℝ) (x : Fin 3 → ℝ) : Prop :=
  (∑ i : Fin 3, x i = s) ∧ (∑ i : Fin 3, (x i) ^ 2 = q)

/-- At least two coordinates agree. -/
def HasDuplicateCoordinate {N : ℕ} (x : Fin N → ℝ) : Prop :=
  ∃ i j : Fin N, i ≠ j ∧ x i = x j

/-- A constant `C` is admissible if it can replace `Γ_N` in Theorem 2.1 uniformly. -/
def AdmissibleConstant (N : ℕ) (C : ℝ) : Prop :=
  ∀ (n : ℕ) (hn : n ≤ N) (μ : Measure (Fin N → ℝ)),
    IsProbabilityMeasure μ → Exchangeable μ → BoundedByOne μ →
      ∀ (w : Fin n → ℝ) (lam : ℝ),
        (∫ x, Real.exp (lam * centeredWeightedSum hn w x) ∂μ) ≤
          Real.exp (((lam ^ 2) / 2) * C * normSq (projOnePerp (zeroPad hn w)))

/-- The lower bound for any admissible replacement constant in Proposition 2.3. -/
def optimalLowerBound (N : ℕ) : ℝ :=
  if Even N then (N : ℝ) / ((N - 1 : ℕ) : ℝ)
  else ((N + 1 : ℕ) : ℝ) / (N : ℝ)

/-! ## Explicit proof-obligation interface -/

open Filter Asymptotics

/-- The mathematical obligations that still need formal proofs.

Keeping these as fields rather than global axioms means importing this file does
not add any unproved facts to the kernel.  A complete formalization is an
inhabitant of this structure.
-/
structure ProofObligations : Prop where
  centeredWeightedSum_eq_dot_proj :
    ∀ {n N : ℕ} (hn : n ≤ N) (w : Fin n → ℝ) (x : Fin N → ℝ),
      centeredWeightedSum hn w x = dot (projOnePerp (zeroPad hn w)) x
  sum_projOnePerp_eq_zero :
    ∀ {N : ℕ} (_hN : 0 < N) (z : Fin N → ℝ),
      ∑ i : Fin N, projOnePerp z i = 0
  theorem_2_1_zero_sum :
    ∀ {N : ℕ} (hN : 2 ≤ N)
      (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
      (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
      (a : Fin N → ℝ) (ha : ∑ i : Fin N, a i = 0) (lam : ℝ),
      (∫ x, Real.exp (lam * dot a x) ∂μ) ≤
        Real.exp (((lam ^ 2) / 2) * Gamma N * normSq a)
  corollary_2_2 :
    ∀ {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N)
      (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
      (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
      (w : Fin n → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (hne : normSq (projOnePerp (zeroPad hn w)) ≠ 0),
      μ {x | tailThreshold hn w δ ≤ centeredWeightedSum hn w x} ≤ ENNReal.ofReal δ
  proposition_4_4 :
    ∀ {N k : ℕ} (hN : 2 ≤ N)
      (hk0 : 1 ≤ k) (hkN : k ≤ N - 1) {ρ : ℝ} (hρ : 0 ≤ ρ),
      ∃ y : Fin N → ℝ,
        SphereSection ρ y ∧ AtMostTwoValues y ∧
          ∀ z : Fin N → ℝ, SphereSection ρ z → sliceFunctional k z ≤ sliceFunctional k y
  slice_inequality :
    ∀ {N k : ℕ} (hN : 2 ≤ N)
      (hk0 : 1 ≤ k) (hkN : k ≤ N - 1)
      (y : Fin N → ℝ) (hy : ∑ i : Fin N, y i = 0),
      Real.log (sliceAverage k (fun S => Real.exp (∑ i ∈ S, y i))) ≤
        (Gamma N / 8) * normSq y
  lemma_4_5_hypergeom_mgf :
    ∀ {N K m : ℕ} (hN : 1 ≤ N)
      (hK : K ≤ N) (hm0 : 1 ≤ m) (hmN : m ≤ N - 1) (t : ℝ),
      Real.log (hypergeomMgf N K m t) ≤ (t ^ 2 / 8) * hypergeomB N m
  lemma_4_1_hoeffding :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Z : Ω → ℝ) (a b θ : ℝ)
      (hmean : (∫ ω, Z ω ∂μ) = 0)
      (hbdd : ∀ᵐ ω ∂μ, a ≤ Z ω ∧ Z ω ≤ b),
      (∫ ω, Real.exp (θ * Z ω) ∂μ) ≤
        Real.exp ((θ ^ 2) * ((b - a) ^ 2) / 8)
  lemma_4_2_lagrange_sign :
    ∀ (h : ℝ → ℝ) (x1 x2 x3 : ℝ)
      (hC5 : ContDiff ℝ 5 h)
      (hd12 : x1 ≠ x2) (hd13 : x1 ≠ x3) (hd23 : x2 ≠ x3)
      (hz1 : h x1 = 0) (hz2 : h x2 = 0) (hz3 : h x3 = 0)
      (hpos : ∀ t,
        min x1 (min x2 x3) < t → t < max x1 (max x2 x3) →
          0 < iteratedDeriv 5 h t),
      let p : ℝ → ℝ := fun t => (t - x1) * (t - x2) * (t - x3)
      0 < deriv h x1 / (deriv p x1) ^ 2 +
          deriv h x2 / (deriv p x2) ^ 2 +
          deriv h x3 / (deriv p x3) ^ 2
  lemma_4_3_three_coordinate :
    ∀ {A B s q : ℝ}
      (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
      (hq : s ^ 2 / 3 ≤ q),
      ∃ x : Fin 3 → ℝ,
        ThreeSphereSection s q x ∧ HasDuplicateCoordinate x ∧
          ∀ y : Fin 3 → ℝ,
            ThreeSphereSection s q y → threeObjective A B y ≤ threeObjective A B x
  lemma_4_3_no_three_distinct_max :
    ∀ {A B s q : ℝ}
      (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
      (hq : s ^ 2 / 3 < q) (x : Fin 3 → ℝ)
      (hx : ThreeSphereSection s q x)
      (hmax : ∀ y : Fin 3 → ℝ,
        ThreeSphereSection s q y → threeObjective A B y ≤ threeObjective A B x),
      HasDuplicateCoordinate x
  gamma_eq_closed :
    ∀ {N : ℕ} (hN : 2 ≤ N), Gamma N = GammaClosed N
  gamma_asymptotic :
    (fun N : ℕ => Gamma N - (1 + 3 / (2 * (N : ℝ))))
      =O[atTop] (fun N : ℕ => (1 : ℝ) / ((N : ℝ) ^ 2))
  lemma_4_6_gamma_lt_barber :
    ∀ {N : ℕ} (hN : 3 ≤ N), Gamma N < 1 + epsilonBarber N
  proposition_2_3 :
    ∀ {N : ℕ} (hN : 2 ≤ N) {C : ℝ}
      (hC : AdmissibleConstant N C), optimalLowerBound N ≤ C

/-! ## Derived results from the proof-obligation interface -/

/-- Theorem 2.1 derived from the reduced zero-sum statement and deterministic
projection identities. -/
theorem theorem_2_1 (P : ProofObligations) {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hEx : Exchangeable μ) (hBd : BoundedByOne μ)
    (w : Fin n → ℝ) (lam : ℝ) :
    (∫ x, Real.exp (lam * centeredWeightedSum hn w x) ∂μ) ≤
      Real.exp (((lam ^ 2) / 2) * Gamma N * normSq (projOnePerp (zeroPad hn w))) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hN
  have hsum : ∑ i : Fin N, projOnePerp (zeroPad hn w) i = 0 :=
    P.sum_projOnePerp_eq_zero hNpos (zeroPad hn w)
  have hred := P.theorem_2_1_zero_sum hN μ hEx hBd
      (projOnePerp (zeroPad hn w)) hsum lam
  simpa [P.centeredWeightedSum_eq_dot_proj hn w] using hred

/-- Endpoint comparison can be exported as a derived theorem when `Γ₂ = 2` and
`ε₂ = 1` have been verified as finite calculations.  We keep it separate from
`ProofObligations` because it is intentionally local and computational. -/
theorem lemma_4_6_gamma_eq_barber_two_from_values
    (hΓ : Gamma 2 = 2) (hε : epsilonBarber 2 = 1) :
    Gamma 2 = 1 + epsilonBarber 2 := by
  rw [hΓ, hε]
  norm_num

end ExchangeableHoeffding
