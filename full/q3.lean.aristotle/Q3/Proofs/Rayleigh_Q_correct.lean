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
  simp only [Q3.T_P_comp_unnorm]
  -- Show each term equals just the weight times window (with separate casts)
  have h_eq : ∀ n : Q3.Nodes K,
      ((Q3.w_Q n : ℝ) : ℂ) * ((Q3.fejer_heat_window B t (Q3.xi_n n) : ℝ) : ℂ) *
        Q3.prime_vec_unnorm M (Q3.xi_n n) (i0 M) *
        conj (Q3.prime_vec_unnorm M (Q3.xi_n n) (i0 M)) =
      ((Q3.w_Q n : ℝ) : ℂ) * ((Q3.fejer_heat_window B t (Q3.xi_n n) : ℝ) : ℂ) := by
    intro n
    rw [prime_vec_unnorm_i0]
    simp [map_one]
  conv_lhs => rw [Finset.sum_congr rfl (fun n _ => h_eq n)]
  -- Now: (∑ n, (w_Q n : ℂ) * (fejer_heat_window B t (xi_n n) : ℂ)).re = prime_term_finite
  simp only [prime_term_finite]
  -- Real sum of real-cast values is the real sum
  rw [Complex.re_sum]
  congr 1
  ext n
  simp [Complex.ofReal_mul, Complex.mul_re]

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
  -- Reverse triangle: |θ + m| ≥ |m| - |θ|
  -- From hθ: |θ| ≤ 1/2, so |θ + m| ≥ |m| - 1/2 > B
  have hθ_abs : |θ| ≤ 1/2 := by
    rw [abs_le]
    constructor
    · have h1 := hθ.1
      linarith
    · exact hθ.2
  -- Use abs_sub_abs_le_abs_sub(m, -θ): |m| - |-θ| ≤ |m - (-θ)| = |m + θ|
  -- Since |-θ| = |θ|, this gives |m| - |θ| ≤ |m + θ|
  have h_rev_tri : |θ + ↑m| ≥ |(↑m : ℝ)| - |θ| := by
    have key : |(↑m : ℝ)| - |-θ| ≤ |↑m - (-θ)| := abs_sub_abs_le_abs_sub _ _
    simp only [abs_neg, sub_neg_eq_add] at key
    calc |(↑m : ℝ)| - |θ| ≤ |↑m + θ| := key
      _ = |θ + ↑m| := by ring_nf
  -- Chain: |θ + m| ≥ |m| - |θ| ≥ |m| - 1/2 > B
  have hm_real : |(↑m : ℝ)| = (|m| : ℝ) := by
    rw [← Int.cast_abs]
  calc |θ + ↑m| ≥ |(↑m : ℝ)| - |θ| := h_rev_tri
    _ ≥ |(↑m : ℝ)| - 1/2 := by linarith
    _ = (|m| : ℝ) - 1/2 := by rw [hm_real]
    _ > B := by linarith

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
  -- Step 1: |m|.toNat > periodization_cutoff B implies real cast inequality
  have h1 : (periodization_cutoff B : ℝ) < (|m|.toNat : ℝ) := Nat.cast_lt.mpr hm
  -- Step 2: |m|.toNat as real = |(m : ℝ)| (the real absolute value)
  -- Key: Int.cast_abs gives |↑m| = ↑|m| for m : ℤ
  have h2 : (|m|.toNat : ℝ) = |(↑m : ℝ)| := by
    have hab : |m| ≥ 0 := abs_nonneg m
    -- Int.toNat_of_nonneg: 0 ≤ n → ↑(Int.toNat n) = n (as Int)
    have hcast : (|m|.toNat : ℤ) = |m| := Int.toNat_of_nonneg hab
    -- Int.cast_abs: |↑m| = ↑|m| for real cast
    have hint_cast_abs : |(↑m : ℝ)| = ((|m| : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
    -- Chain: |m|.toNat → Int cast → Real cast
    calc (|m|.toNat : ℝ) = ((|m|.toNat : ℤ) : ℝ) := by norm_cast
      _ = ((|m| : ℤ) : ℝ) := by rw [hcast]
      _ = |(↑m : ℝ)| := hint_cast_abs.symm
  -- Step 3: periodization_cutoff = Nat.ceil B + 1 ≥ B + 1
  have h3 : (periodization_cutoff B : ℝ) ≥ B + 1 := by
    simp only [periodization_cutoff]
    have hceil : (Nat.ceil B : ℝ) ≥ B := Nat.le_ceil B
    have hadd : ((Nat.ceil B + 1 : ℕ) : ℝ) = (Nat.ceil B : ℝ) + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
    linarith
  -- Combine: |m| > periodization_cutoff ≥ B + 1 > B + 1/2
  -- h1: periodization_cutoff B < |m|.toNat as ℝ
  -- Here |m| is Int.abs m : ℤ, and .toNat gives ℕ
  -- Since Int.abs m ≥ 0, (Int.abs m).toNat = Int.natAbs m
  have h4 : (|m|.toNat : ℝ) = |(↑m : ℝ)| := by
    -- |m|.toNat = Int.natAbs m (since abs ≥ 0)
    -- Int.abs m = Int.natAbs m as ℤ (both are ≥0)
    -- .toNat of nonneg Int = that Int as ℕ
    have habs_eq : |m|.toNat = m.natAbs := by
      -- |m| : ℤ is nonneg, so .toNat = |m| as ℕ
      -- |m| = (natAbs m : ℤ) by Int.abs_eq_natAbs
      simp only [Int.abs_eq_natAbs, Int.toNat_natCast]
    rw [habs_eq]
    -- Now: (Int.natAbs m : ℝ) = |(↑m : ℝ)|
    -- Nat.cast_natAbs: (m.natAbs : ℝ) = (|m| : ℤ → ℝ)
    -- Int.cast_abs: |(↑m : ℝ)| = (|m| : ℤ → ℝ)
    -- Combine: (m.natAbs : ℝ) = (|m| : ℝ) = |(↑m : ℝ)|
    rw [← Int.cast_abs]
    exact @Nat.cast_natAbs ℝ _ m
  rw [h4] at h1
  -- Now h1: (periodization_cutoff B : ℝ) < |(↑m : ℝ)|
  -- h3: (periodization_cutoff B : ℝ) ≥ B + 1 > B + 1/2
  -- So |(↑m : ℝ)| > B + 1/2
  linarith

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
  -- hm : m < -(N : ℤ) ∨ (N : ℤ) < m where N = periodization_cutoff B
  -- Goal: N < |m|.toNat
  -- Key: |m|.toNat = m.natAbs (via Int.abs_eq_natAbs + toNat)
  have h_eq : |m|.toNat = m.natAbs := by
    simp only [Int.abs_eq_natAbs, Int.toNat_natCast]
  rw [h_eq]
  -- Now need: periodization_cutoff B < m.natAbs
  -- From hm: either m < -(N : ℤ) or (N : ℤ) < m
  -- In either case, |m| > N, so m.natAbs > N
  cases hm with
  | inl h_neg =>
    -- m < -(N : ℤ), so m ≤ 0 and -m > N
    have hneg : m ≤ 0 := by
      have hN : (periodization_cutoff B : ℤ) ≥ 0 := Int.natCast_nonneg _
      linarith
    have hposm : -m ≥ 0 := neg_nonneg.mpr hneg
    have h1 : (periodization_cutoff B : ℤ) < -m := by linarith
    -- ((-m).natAbs : ℤ) = -m by Int.natAbs_of_nonneg since -m ≥ 0
    have h2 : ((-m).natAbs : ℤ) = -m := Int.natAbs_of_nonneg hposm
    -- (-m).natAbs = m.natAbs by Int.natAbs_neg
    have h3 : (-m).natAbs = m.natAbs := Int.natAbs_neg m
    -- So (m.natAbs : ℤ) = -m
    have h4 : (m.natAbs : ℤ) = -m := by rw [← h3, h2]
    -- (N : ℤ) < -m = (m.natAbs : ℤ)
    have h5 : (periodization_cutoff B : ℤ) < (m.natAbs : ℤ) := by rw [h4]; exact h1
    exact Nat.cast_lt.mp h5
  | inr h_pos =>
    -- (N : ℤ) < m, so m ≥ 0 and m > N
    have hpos : m ≥ 0 := by
      have hN : (periodization_cutoff B : ℤ) ≥ 0 := Int.natCast_nonneg _
      linarith
    have h1 : (periodization_cutoff B : ℤ) < m := h_pos
    -- (m.natAbs : ℤ) = m by Int.natAbs_of_nonneg since m ≥ 0
    have h2 : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hpos
    -- (N : ℤ) < m = (m.natAbs : ℤ)
    have h3 : (periodization_cutoff B : ℤ) < (m.natAbs : ℤ) := by rw [h2]; exact h1
    exact Nat.cast_lt.mp h3

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
  -- At i0, the index is M, so i - j = M - M = 0, and exp(0) = 1
  simp only [RayleighFourier.ToeplitzMatrix_Fourier_real, RayleighFourier.ToeplitzEntry]
  -- i0 M has value M as ℕ
  have h_val : (i0 M : ℕ) = M := rfl
  -- Show the exp factor is 1 when i = j = M
  have h_exp : ∀ θ : ℝ, Complex.exp (2 * Real.pi * Complex.I * ((M : ℂ) - (M : ℂ)) * (θ : ℂ)) = 1 := by
    intro θ
    simp only [sub_self, mul_zero, zero_mul, Complex.exp_zero]
  -- The integral becomes ∫ (P_A θ : ℂ) * 1, and .re of that is ∫ P_A θ
  simp_rw [h_val, h_exp, mul_one]
  -- (∫ (P_A θ : ℂ)).re = ∫ P_A θ for real-valued P_A
  -- Use: re (∫ f : ℂ) = ∫ re f when f is real-valued
  have h_re_eq : ∀ θ : ℝ, ((P_A B t θ : ℝ) : ℂ).re = P_A B t θ := fun θ => Complex.ofReal_re _
  -- Goal: (∫ θ, ↑(P_A θ)).re = ∫ θ, P_A θ
  -- This requires showing the integral commutes with re
  sorry  -- Needs integrability argument for interval integral

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
