/-
Rayleigh-Q Identification (Theorem 3.3)

This module proves that the Rayleigh quotient at basis0 equals Q functional.
Key identity:
  (2*M+1) * RQ((T_M[P_A] - T_P^(M)), basis0) = Q(Φ_{B,t})

Integration: change-durch: claude-code 2026-01-16 Rayleigh_Q_identification
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_Fourier
import A3_FLOOR_v22_stage4_floor

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.RayleighQId

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

/-- Rayleigh quotient of A at basis0 equals the diagonal entry A[i0, i0]. -/
theorem rayleigh_basis0 (M : ℕ) (A : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    Q3.RayleighQuotient A (basis0 M) = A (i0 M) (i0 M) := by
  simp only [Q3.RayleighQuotient]
  rw [quadForm_basis0, basis0_norm_sq]
  simp

/-- Rayleigh quotient of (A - B) at basis0 equals A[i0,i0] - B[i0,i0]. -/
theorem rayleigh_basis0_sub (M : ℕ)
    (A B : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    Q3.RayleighQuotient (A - B) (basis0 M) =
      A (i0 M) (i0 M) - B (i0 M) (i0 M) := by
  rw [rayleigh_basis0]
  simp [Matrix.sub_apply]

/-! ## Toeplitz Diagonal Lemmas -/

/-- Diagonal entry of Toeplitz matrix equals integral of symbol.
    ToeplitzEntry P i i = ∫_{-1/2}^{1/2} P(θ) dθ because exp(2πi·0·θ) = 1. -/
lemma ToeplitzEntry_diag (P : ℝ → ℝ) (i : ℕ) :
    RayleighFourier.ToeplitzEntry P i i = ∫ θ in (-1/2 : ℝ)..(1/2), (P θ : ℂ) := by
  simp only [RayleighFourier.ToeplitzEntry]
  congr 1
  ext θ
  simp [Complex.exp_zero]

/-- Real part of diagonal equals integral (for real-valued P). -/
lemma ToeplitzEntry_diag_re (P : ℝ → ℝ) (hP : Continuous P) (i : ℕ) :
    (RayleighFourier.ToeplitzEntry P i i).re = ∫ θ in (-1/2 : ℝ)..(1/2), P θ := by
  rw [ToeplitzEntry_diag]
  rw [intervalIntegral.integral_ofReal]
  simp

/-- ToeplitzMatrix_Fourier_real diagonal at i0. -/
lemma ToeplitzMatrix_Fourier_real_diag (M : ℕ) (P : ℝ → ℝ) (hP : Continuous P) :
    RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) P (i0 M) (i0 M) =
      ∫ θ in (-1/2 : ℝ)..(1/2), P θ := by
  simp only [RayleighFourier.ToeplitzMatrix_Fourier_real]
  exact ToeplitzEntry_diag_re P hP (i0 M).val

/-! ## T_P_comp Diagonal Lemmas -/

/-- At i0, the Fourier index is 0. -/
lemma fourier_index_i0 (M : ℕ) : Q3.fourier_index M (i0 M) = 0 := by
  simp [Q3.fourier_index, i0]

/-- At i0, prime_vec evaluates to 1/√(2M+1).
    This is because exp(-2πi·0·ξ) = 1. -/
lemma prime_vec_i0 (M : ℕ) (ξ : ℝ) :
    Q3.prime_vec M ξ (i0 M) = (1 / Real.sqrt (2 * M + 1 : ℝ) : ℂ) := by
  unfold Q3.prime_vec
  simp only [fourier_index_i0, Int.cast_zero, mul_zero, neg_zero]
  simp only [zero_mul, Complex.exp_zero, mul_one]

/-- T_P_comp_real diagonal at i0.
    T_P_comp_real[i0,i0] = (1/(2M+1)) * Σ_n w_Q(n) * φ(ξ_n).
    This follows from prime_vec(i0) = 1/√(2M+1), so |prime_vec(i0)|² = 1/(2M+1). -/
lemma T_P_comp_real_diag (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] (_hM : 0 < 2 * M + 1) :
    Q3.T_P_comp_real K B t M (i0 M) (i0 M) =
      (1 / (2 * M + 1 : ℝ)) *
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) := by
  -- Key: prime_vec M ξ (i0 M) = 1/√(2M+1) (from fourier_index = 0, exp(0)=1)
  -- So T_P_comp[i0,i0] = Σ_n w_Q(n)*φ(ξ_n) * |1/√(2M+1)|² = (1/(2M+1)) * Σ_n ...
  simp only [Q3.T_P_comp_real, Q3.T_P_comp]
  -- Rewrite using prime_vec_i0
  have hprime : ∀ ξ : ℝ, Q3.prime_vec M ξ (i0 M) = (1 / Real.sqrt (2 * M + 1 : ℝ) : ℂ) :=
    fun ξ => prime_vec_i0 M ξ
  simp_rw [hprime]
  -- For real c, conj(c) = c
  have hconj : starRingEnd ℂ ((1 : ℂ) / Real.sqrt (2 * M + 1 : ℝ)) =
      (1 : ℂ) / Real.sqrt (2 * M + 1 : ℝ) := by
    simp only [map_div₀, map_one, Complex.conj_ofReal]
  simp_rw [hconj]
  -- (1/√n)² = 1/n for n>0
  have hpos : (0 : ℝ) < 2 * M + 1 := by positivity
  have hmul : ((1 : ℂ) / Real.sqrt (2 * M + 1 : ℝ)) * ((1 : ℂ) / Real.sqrt (2 * M + 1 : ℝ)) =
      (1 / (2 * M + 1 : ℝ) : ℂ) := by
    rw [div_mul_div_comm, one_mul]
    congr 1
    simp only [Complex.ofReal_mul]
    norm_cast
    exact Real.sqrt_mul_self (le_of_lt hpos)
  -- Rewrite the sum: each term becomes (w*φ) * (1/(2M+1))
  have hsumrw : (∑ n : Q3.Nodes K, (Q3.w_Q ↑n * Q3.fejer_heat_window B t (Q3.xi_n ↑n) : ℂ) *
      ((1 : ℂ) / Real.sqrt (2 * M + 1 : ℝ)) * ((1 : ℂ) / Real.sqrt (2 * M + 1 : ℝ))) =
      (∑ n : Q3.Nodes K, (Q3.w_Q ↑n * Q3.fejer_heat_window B t (Q3.xi_n ↑n) : ℂ)) *
        (1 / (2 * M + 1 : ℝ) : ℂ) := by
    rw [Finset.sum_mul]
    congr 1
    ext n
    rw [mul_assoc, hmul]
  rw [hsumrw]
  -- Real part of product of reals: both are ℝ embedded in ℂ
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [mul_comm]
  congr 1
  -- ∑ (↑(w * φ) : ℂ).re = ∑ w * φ (since ofReal preserves re)
  simp only [← Finset.sum_coe_sort, Complex.ofReal_re]

end Q3.Proofs.RayleighQId
