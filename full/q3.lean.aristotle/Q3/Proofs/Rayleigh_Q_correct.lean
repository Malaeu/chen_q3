/-
Rayleigh-Q Identification — CORRECTED VERSION
==============================================

The OLD formula was WRONG:
  (2*M+1) * RQ((T_M[P_A] - T_P^(M)), basis0) = Q(Φ_{B,t})

Problem: Multiplying by (2M+1) affects both arch and prime parts!
  (2M+1) * [∫ P_A - (1/(2M+1)) * prime_term] = (2M+1) * arch_term - prime_term ≠ Q

CORRECT formula uses UNNORMALIZED vectors:
  RQ((T_M[P_A] - T_P_unnorm), basis0) = arch_term - prime_term = Q(Φ)

No (2M+1) multiplier needed!

Key lemmas:
1. prime_vec_unnorm(i0) = 1 (because fourier_index(i0) = 0, exp(0) = 1)
2. T_P_comp_unnorm[i0,i0] = Σ w_Q(n) * φ(ξ_n) = prime_term_finite(K, Φ)
3. Periodization: ∫_{-1/2}^{1/2} P_A(θ) dθ = arch_term(Φ)
4. Correct identity: RQ(ToeplitzFourier(P_A) - T_P_comp_unnorm, basis0) = Q_finite(K, Φ)

Integration: 2026-01-17 Rayleigh_Q_correct (fix normalization mismatch)
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_Fourier
import A3_FLOOR_v22_stage4_floor

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate

set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.RayleighQCorrect

/-! ## Basis Setup (same as before) -/

/-- The index M is valid in Fin (2*M+1). -/
lemma M_lt_2M_add_1 (M : ℕ) : M < 2 * M + 1 := by omega

/-- Canonical middle index i0 = M in Fin (2*M+1). -/
def i0 (M : ℕ) : Fin (2 * M + 1) := ⟨M, M_lt_2M_add_1 M⟩

/-- Basis vector: 1 at position M, 0 elsewhere.
    Represents the constant polynomial p ≡ 1 in Fourier basis. -/
def basis0 (M : ℕ) : Fin (2 * M + 1) → ℝ :=
  fun i => if i.val = M then (1 : ℝ) else 0

/-- basis0 has unit squared norm. -/
theorem basis0_norm_sq (M : ℕ) :
    (∑ i : Fin (2 * M + 1), (basis0 M i) ^ 2) = 1 := by
  have h_zero : ∀ i : Fin (2 * M + 1), i ≠ i0 M → (basis0 M i) ^ 2 = 0 := by
    intro i hi
    simp only [basis0]
    have : i.val ≠ M := fun heq => hi (Fin.ext heq)
    simp [this]
  have h_one : (basis0 M (i0 M)) ^ 2 = 1 := by simp [basis0, i0]
  rw [Finset.sum_eq_single (i0 M)]
  · exact h_one
  · intro b _ hb; exact h_zero b hb
  · intro h; exfalso; exact h (Finset.mem_univ _)

/-- basis0 is nonzero. -/
theorem basis0_ne_zero (M : ℕ) : basis0 M ≠ 0 := by
  intro h
  have : basis0 M (i0 M) = 0 := by rw [h]; rfl
  simp [basis0, i0] at this

/-! ## Unnormalized Vector Properties -/

/-- At i0, the Fourier index is 0. -/
lemma fourier_index_i0 (M : ℕ) : Q3.fourier_index M (i0 M) = 0 := by
  simp [Q3.fourier_index, i0]

/-- At i0, UNNORMALIZED prime_vec evaluates to 1 (not 1/√(2M+1)!).
    This is because exp(-2πi·0·ξ) = exp(0) = 1. -/
lemma prime_vec_unnorm_i0 (M : ℕ) (ξ : ℝ) :
    Q3.prime_vec_unnorm M ξ (i0 M) = 1 := by
  unfold Q3.prime_vec_unnorm
  simp only [fourier_index_i0]
  simp only [Int.cast_zero, neg_zero, zero_mul, mul_zero, Complex.exp_zero]

/-- Conjugate of prime_vec_unnorm at i0 is also 1. -/
lemma prime_vec_unnorm_i0_conj (M : ℕ) (ξ : ℝ) :
    conj (Q3.prime_vec_unnorm M ξ (i0 M)) = 1 := by
  rw [prime_vec_unnorm_i0]
  simp [map_one]

/-! ## T_P_comp_unnorm Diagonal at i0 -/

/-- Finite prime term over nodes in [-K, K]. -/
def prime_term_finite (K B t : ℝ) [Fintype (Q3.Nodes K)] : ℝ :=
  ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)

/-- KEY LEMMA: T_P_comp_unnorm[i0,i0] = prime_term_finite.
    Unlike T_P_comp, there's NO 1/(2M+1) factor!

    Proof: At i0, prime_vec_unnorm(i0) = exp(0) = 1 (from fourier_index(i0) = 0).
    So T_P_comp_unnorm[i0,i0] = Σ_n w_Q(n) * φ(ξ_n) * |1|² = prime_term_finite. -/
lemma T_P_comp_unnorm_diag_i0 (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    (Q3.T_P_comp_unnorm K B t M (i0 M) (i0 M)).re = prime_term_finite K B t := by
  -- Key: prime_vec_unnorm M ξ (i0 M) = 1, so the product simplifies
  sorry

/-- Real version: T_P_comp_unnorm_real[i0,i0] = prime_term_finite. -/
lemma T_P_comp_unnorm_real_diag_i0 (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    Q3.T_P_comp_unnorm_real K B t M (i0 M) (i0 M) = prime_term_finite K B t := by
  unfold Q3.T_P_comp_unnorm_real
  exact T_P_comp_unnorm_diag_i0 K B t M

/-! ## Periodization Lemma -/

/-- The window function w from A3_FLOOR equals Q3.fejer_heat_window. -/
lemma w_eq_fejer_heat_window (B t ξ : ℝ) :
    w B t ξ = Q3.fejer_heat_window B t ξ := by
  -- Both are: max 0 (1 - |ξ| / B) * exp(-4π²t·ξ²)
  rfl

/-- The kernel g from A3_FLOOR: g = a · w = a · fejer_heat_window. -/
lemma g_eq_a_mul_window (B t ξ : ℝ) :
    g B t ξ = Q3.a ξ * Q3.fejer_heat_window B t ξ := by
  unfold g
  rw [w_eq_fejer_heat_window]

/-! ### Finite Sum Approach to Periodization

Key insight: w(B,t,ξ) = 0 when |ξ| > B (compact support).
Therefore g(B,t,θ+m) = 0 when |θ+m| > B.

For θ ∈ [-1/2, 1/2]:
  |θ+m| ≥ |m| - |θ| ≥ |m| - 1/2

So if |m| > B + 1/2, then |θ+m| > B, hence g(θ+m) = 0.

This means the infinite sum ∑'_m g(θ+m) is actually FINITE:
only terms with |m| ≤ ⌈B⌉ + 1 contribute.

For B_min = 3: only m ∈ {-4,-3,-2,-1,0,1,2,3,4} contribute.
-/

/-- Window w has support in [-B, B]: w(B,t,ξ) = 0 when |ξ| > B. -/
lemma w_support (B t ξ : ℝ) (hB : B > 0) (hξ : |ξ| > B) : w B t ξ = 0 := by
  simp only [w]
  have h : 1 - |ξ| / B < 0 := by
    rw [sub_neg]
    exact (one_lt_div hB).mpr hξ
  simp only [max_eq_left_of_lt h, zero_mul]

/-- g has support in [-B, B]: g(B,t,ξ) = 0 when |ξ| > B. -/
lemma g_support (B t ξ : ℝ) (hB : B > 0) (hξ : |ξ| > B) : g B t ξ = 0 := by
  simp only [g, w_support B t ξ hB hξ, mul_zero]

/-- For θ ∈ [-1/2, 1/2] and |m| > B + 1/2, we have g(θ+m) = 0.

Proof sketch: |θ + m| ≥ |m| - |θ| ≥ |m| - 1/2 > B (reverse triangle inequality).
-/
lemma g_zero_large_m (B t θ : ℝ) (m : ℤ) (hB : B > 0)
    (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hm : (|m| : ℝ) > B + 1/2) :
    g B t (θ + m) = 0 := by
  apply g_support B t _ hB
  -- Proof: |θ + m| ≥ |m| - |θ| ≥ |m| - 1/2 > B (reverse triangle)
  -- Elementary but tedious cast arithmetic
  sorry

/-- The cutoff index: N = ⌈B⌉ + 1 suffices. -/
def periodization_cutoff (B : ℝ) : ℕ := Nat.ceil B + 1

/-- For |m| > periodization_cutoff, g(θ+m) = 0.

Proof: |m| > periodization_cutoff ≥ B + 1 > B + 1/2, then use g_zero_large_m.
-/
lemma g_zero_beyond_cutoff (B t θ : ℝ) (m : ℤ) (hB : B > 0)
    (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hm : periodization_cutoff B < |m|.toNat) :
    g B t (θ + m) = 0 := by
  apply g_zero_large_m B t θ m hB hθ
  -- Proof: |m| > periodization_cutoff B = ⌈B⌉ + 1 ≥ B + 1 > B + 1/2
  -- Elementary Nat→ℝ cast arithmetic
  sorry

/-- The tsum over ℤ equals a finite sum when terms vanish outside [-N, N]. -/
lemma tsum_eq_finite_sum_g (B t θ : ℝ) (hB : B > 0)
    (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    ∑' (m : ℤ), g B t (θ + m) =
      ∑ m ∈ Finset.Icc (-(periodization_cutoff B : ℤ)) (periodization_cutoff B),
        g B t (θ + m) := by
  -- The tsum equals the finite sum because all terms outside [-N, N] are zero
  -- Uses: tsum_eq_sum + g_zero_beyond_cutoff
  apply tsum_eq_sum
  intro m hm
  apply g_zero_beyond_cutoff B t θ m hB hθ
  -- Need: periodization_cutoff B < |m|.toNat from m ∉ Finset.Icc
  simp only [Finset.mem_Icc, not_and_or, not_le] at hm
  -- Elementary: m < -N or m > N implies |m| > N
  sorry

/-- Periodization: ∫_{-1/2}^{1/2} P_A(θ) dθ = arch_term(Φ_{B,t})

Proof via finite sum:
1. P_A is a finite sum (g vanishes for large |m|)
2. Integral of finite sum = sum of integrals
3. Each ∫_{-1/2}^{1/2} g(θ+m) dθ = ∫_{m-1/2}^{m+1/2} g(ξ) dξ (change of vars)
4. Sum over disjoint intervals = ∫_ℝ g(ξ) dξ (covers support of g)
5. 2π ∫ g = 2π ∫ a·w = ∫ a*·w = arch_term(w)
-/
theorem periodization_lemma (B t : ℝ) (hB : B > 0) (ht : t > 0) :
    ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ = Q3.arch_term (Q3.fejer_heat_window B t) := by
  -- P_A(θ) = 2π · ∑'_m g(θ+m) = 2π · (finite sum)
  -- ∫ P_A = 2π · ∫ (finite sum) = 2π · Σ ∫ g(θ+m)
  -- Each ∫_{-1/2}^{1/2} g(θ+m) dθ = ∫_{m-1/2}^{m+1/2} g(ξ) dξ
  -- Sum over m covers [-B-1/2, B+1/2] ⊇ [-B, B] = support(g)
  -- So Σ_m ∫ g(θ+m) = ∫_ℝ g = ∫_ℝ a·w
  -- Therefore ∫ P_A = 2π ∫_ℝ a·w = ∫_ℝ (2π·a)·w = ∫_ℝ a*·w = arch_term(w)
  sorry  -- Finite sum manipulation + interval decomposition

/-! ## Toeplitz Diagonal = Arch Term -/

/-- Toeplitz diagonal entry for P_A equals periodized integral.
    At diagonal (i=j), the Fourier coefficient is the 0-th coefficient = ∫ P_A(θ) dθ. -/
lemma ToeplitzFourier_P_A_diag (M : ℕ) (B t : ℝ) :
    RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) (i0 M) (i0 M) =
      ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ := by
  -- At i0, fourier_index = M - M = 0, so the Toeplitz entry is ∫ P_A(θ) · exp(0) dθ = ∫ P_A(θ) dθ
  simp only [RayleighFourier.ToeplitzMatrix_Fourier_real]
  -- This requires unfolding ToeplitzEntry and showing that at diagonal the exp factor is 1
  sorry

/-- Combining: Toeplitz[i0,i0] = arch_term(Φ). -/
theorem ToeplitzFourier_P_A_diag_eq_arch (M : ℕ) (B t : ℝ) (hB : B > 0) (ht : t > 0) :
    RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) (i0 M) (i0 M) =
      Q3.arch_term (Q3.fejer_heat_window B t) := by
  rw [ToeplitzFourier_P_A_diag]
  exact periodization_lemma B t hB ht

/-! ## CORRECTED Rayleigh-Q Identification -/

/-- Quadratic form of A at basis0 equals the diagonal entry A[i0, i0]. -/
theorem quadForm_basis0 (M : ℕ) (A : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    (∑ i, ∑ j, basis0 M i * A i j * basis0 M j) = A (i0 M) (i0 M) := by
  have h_inner : ∀ i : Fin (2 * M + 1),
      (∑ j, basis0 M i * A i j * basis0 M j) =
        if i = i0 M then A (i0 M) (i0 M) else 0 := by
    intro i
    split_ifs with hi
    · subst hi
      rw [Finset.sum_eq_single (i0 M)]
      · simp [basis0, i0]
      · intro b _ hb
        have : b.val ≠ M := fun heq => hb (Fin.ext heq)
        simp [basis0, this]
      · intro h; exfalso; exact h (Finset.mem_univ _)
    · have : i.val ≠ M := fun heq => hi (Fin.ext heq)
      simp [basis0, this]
  simp_rw [h_inner]
  rw [Finset.sum_ite_eq']
  simp

/-- Rayleigh quotient at basis0 = diagonal entry. -/
theorem rayleigh_basis0 (M : ℕ) (A : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    Q3.RayleighQuotient A (basis0 M) = A (i0 M) (i0 M) := by
  simp only [Q3.RayleighQuotient]
  rw [quadForm_basis0, basis0_norm_sq]
  simp

/-- Rayleigh quotient of (A - B) at basis0. -/
theorem rayleigh_basis0_sub (M : ℕ)
    (A B : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    Q3.RayleighQuotient (A - B) (basis0 M) =
      A (i0 M) (i0 M) - B (i0 M) (i0 M) := by
  rw [rayleigh_basis0]
  simp [Matrix.sub_apply]

/-- Finite Q functional over nodes in [-K, K]. -/
def Q_finite (K B t : ℝ) [Fintype (Q3.Nodes K)] : ℝ :=
  Q3.arch_term (Q3.fejer_heat_window B t) - prime_term_finite K B t

/-- MAIN THEOREM: Correct Rayleigh-Q Identification (without (2M+1) multiplier!)

RQ(ToeplitzFourier(P_A) - T_P_comp_unnorm, basis0) = Q_finite(K, Φ_{B,t})

This is CORRECT because:
- Toeplitz[i0,i0] = ∫ P_A = arch_term (by periodization)
- T_P_comp_unnorm[i0,i0] = prime_term_finite (no 1/(2M+1) factor!)
- RQ at basis0 just extracts the diagonal
- So RQ = arch_term - prime_term = Q_finite ✓

NO (2M+1) multiplier needed!
-/
theorem rayleigh_Q_identification_correct (K B t : ℝ) (M : ℕ)
    (hK : K > 0) (hB : B > 0) (ht : t > 0) [Fintype (Q3.Nodes K)] :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) -
         Q3.T_P_comp_unnorm_real K B t M)
        (basis0 M) =
      Q_finite K B t := by
  rw [rayleigh_basis0_sub]
  unfold Q_finite
  congr 1
  · exact ToeplitzFourier_P_A_diag_eq_arch M B t hB ht
  · exact T_P_comp_unnorm_real_diag_i0 K B t M

/-! ## Connection to Full Q Functional

For the full Q(Φ) = arch_term(Φ) - Σ_{n≥2} w_Q(n)·Φ(ξ_n), we have:
  Q_finite(K, B, t) = Q(Φ_{B,t}) + tail_error

where tail_error = Σ_{n: |ξ_n| > K} w_Q(n)·Φ(ξ_n) → 0 as K → ∞.

For large enough K (depending on B), the tail is exactly 0 because
Φ_{B,t} has support in [-B, B] ⊂ [-K, K].
-/

/-- When K ≥ B, all nodes with Φ(ξ_n) ≠ 0 are captured. -/
lemma Q_finite_eq_Q_large_K (K B t : ℝ) (hK : K ≥ B) (hB : B > 0) (ht : t > 0)
    [Fintype (Q3.Nodes K)] :
    Q_finite K B t = Q3.Q (Q3.fejer_heat_window B t) := by
  -- fejer_heat_window B t has support in [-B, B]
  -- For n with |ξ_n| > K ≥ B, we have Φ(ξ_n) = 0
  -- So prime_term_finite = prime_term
  sorry

end Q3.Proofs.RayleighQCorrect

end
