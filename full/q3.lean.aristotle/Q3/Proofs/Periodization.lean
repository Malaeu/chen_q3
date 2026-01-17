/-
Periodization Lemmas (Lean-friendly, no dominated convergence)
==============================================================

Key insight: g B t has compact support in [-B,B], so the periodization
sum ∑' n : ℤ, g(θ + n) is actually FINITE for θ ∈ [-1/2, 1/2].

This avoids the heavy `integral_tsum_of_summable_integral_norm` machinery
which causes 600+ second compile times.

Strategy:
1. Lemma 1: tsum = Finset.sum (pointwise on torus)
2. Lemma 2: ∫ (periodization) = ∫_ℝ f (via finite sum + substitution)

Integration: change-durch: claude-code 2026-01-17 Periodization
Based on: Proshka analysis of Rayleigh_Q_identification bottleneck
-/

import Q3.Axioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral

set_option linter.mathlibStandardSet false

open scoped BigOperators Real
open MeasureTheory intervalIntegral

noncomputable section

namespace Q3.Proofs.Periodization

/-! ## Definitions from Rayleigh_Q_identification -/

/-- The window function w(ξ) = max(0, 1 - |ξ|/B) · exp(-4π²tξ²) -/
def w (B t : ℝ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)

/-- The kernel g = a · w where a = a_star/(2π) -/
def g (B t : ℝ) (ξ : ℝ) : ℝ :=
  Q3.a ξ * w B t ξ

/-! ## Lemma 1: Support bound implies g(θ+n) = 0 for large |n| -/

/-- The window w is zero when |ξ| > B. -/
lemma w_eq_zero_of_abs_gt (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) :
    w B t ξ = 0 := by
  simp only [w]
  have h1 : 1 - |ξ| / B < 0 := by
    have : 1 < |ξ| / B := by rw [one_lt_div hB]; exact h
    linarith
  rw [max_eq_left (le_of_lt h1)]
  ring

/-- The kernel g is zero when |ξ| > B. -/
lemma g_eq_zero_of_abs_gt (B t ξ : ℝ) (hB : 0 < B) (h : B < |ξ|) :
    g B t ξ = 0 := by
  simp only [g, w_eq_zero_of_abs_gt B t ξ hB h, mul_zero]

/-- Support of g is contained in [-B, B]. -/
lemma g_support_subset (B t : ℝ) (hB : 0 < B) :
    Function.support (fun ξ => g B t ξ) ⊆ Set.Icc (-B) B := by
  intro ξ hξ
  simp only [Function.mem_support] at hξ
  by_contra h
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  have habs : B < |ξ| := by
    cases h with
    | inl hl =>
      have h1 : ξ < 0 := by linarith
      rw [abs_of_neg h1]; linarith
    | inr hr =>
      have h1 : 0 < ξ := by linarith
      rw [abs_of_pos h1]; linarith
  exact hξ (g_eq_zero_of_abs_gt B t ξ hB habs)

/-! ## Key lemma: For θ ∈ [-1/2, 1/2] and large |n|, we have g(θ+n) = 0 -/

/-- Choose N such that for |n| > N and θ ∈ [-1/2, 1/2], we have g(θ+n) = 0.
    We use N = ⌈B + 1/2⌉ which ensures |θ + n| > B when |n| > N. -/
lemma g_shift_eq_zero_of_large_n (B t : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, ∀ θ : ℝ, θ ∈ Set.Icc (-(1/2 : ℝ)) (1/2) →
      ∀ n : ℤ, (N : ℝ) < |n| → g B t (θ + n) = 0 := by
  classical
  refine ⟨Nat.ceil (B + 1/2) + 1, ?_⟩
  intro θ hθ n hn
  apply g_eq_zero_of_abs_gt B t (θ + n) hB
  -- Need: B < |θ + n|
  -- From: θ ∈ [-1/2, 1/2], |n| > N = ⌈B + 1/2⌉ + 1
  -- Triangle ineq: |θ + n| ≥ |n| - |θ| ≥ N - 1/2 > B
  -- Key: if |n| > N and |θ| ≤ 1/2, then |θ + n| > B
  -- Technical: requires careful cast handling ℕ → ℤ → ℝ
  sorry

/-! ## Lemma 2: tsum = Finset.sum on the torus -/

/-- On θ ∈ [-1/2, 1/2], the periodization tsum equals a finite sum.
    Key insight: g has compact support, so only finitely many terms are nonzero. -/
lemma tsum_periodize_eq_finset_sum (B t : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, ∀ θ : ℝ, θ ∈ Set.Icc (-(1/2 : ℝ)) (1/2) →
      (∑' n : ℤ, g B t (θ + n)) = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, g B t (θ + n) := by
  obtain ⟨N, hN⟩ := g_shift_eq_zero_of_large_n B t hB
  refine ⟨N, ?_⟩
  intro θ hθ
  -- Terms outside [-N, N] are zero, so tsum = finite sum
  -- Uses tsum_eq_sum: ∑' f = ∑ s f when f vanishes outside s
  have hz : ∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) N → g B t (θ + n) = 0 := by
    intro n hn
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    have h_abs : (N : ℝ) < |(n : ℝ)| := by
      cases hn with
      | inl hl =>
        have h1 : (n : ℝ) < -(N : ℝ) := by exact_mod_cast hl
        rw [abs_of_neg (by linarith : (n : ℝ) < 0)]; linarith
      | inr hr =>
        have h1 : (N : ℝ) < n := by exact_mod_cast hr
        rw [abs_of_pos (by linarith : 0 < (n : ℝ))]; linarith
    -- Need (N : ℝ) < |n| but hN expects (N : ℝ) < |(n : ℤ)|
    -- These are the same: |n| for n : ℤ when cast to ℝ
    have h_cast : (N : ℝ) < |n| := by
      simp only [Int.cast_abs]; exact h_abs
    exact hN θ hθ n h_cast
  exact tsum_eq_sum hz

/-! ## Lemma 3: Interval integral of periodization equals integral over ℝ -/

/-- Periodization integral over [-1/2, 1/2] equals integral over ℝ.
    This is the Lean-friendly version that avoids dominated convergence.

    The key steps:
    1. tsum = finite sum (by compact support)
    2. ∫ (finite sum) = finite sum of ∫ (swap is free)
    3. Each ∫_{-1/2}^{1/2} g(θ+n) dθ = ∫_{n-1/2}^{n+1/2} g(x) dx (substitution)
    4. The unit intervals partition ℝ, so sum = ∫_ℝ g -/
lemma intervalIntegral_periodize_eq_integral (B t : ℝ) (hB : 0 < B)
    (hcont : Continuous (fun ξ => g B t ξ))
    (hint : Integrable (fun ξ => g B t ξ)) :
    (∫ θ in (-(1/2 : ℝ))..(1/2), ∑' n : ℤ, g B t (θ + n)) = ∫ x, g B t x := by
  -- This is the main result: avoid dominated convergence by using finite sums
  -- See detailed proof sketch in docstring
  -- Implementation uses:
  -- - tsum_periodize_eq_finset_sum (finite reduction)
  -- - intervalIntegral.integral_finset_sum (swap)
  -- - intervalIntegral.integral_comp_add_right (substitution)
  -- - Integrable.hasSum_intervalIntegral (partition)
  sorry

end Q3.Proofs.Periodization
