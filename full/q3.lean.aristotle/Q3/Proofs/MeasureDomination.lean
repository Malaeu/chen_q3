/-
Q3 Formalization: Measure Domination via Neighborhoods
=======================================================

This file explores the "disjoint neighborhood" approach to measure domination:
  Σ w_Q(n) · Φ(ξ_n) ≤ ∫ a*(ξ) · Φ(ξ) dξ

Key insight: The approach works for truncated sums but NOT for all n, because:
- Prime gap: gap_n = ξ_{n+1} - ξ_n ≈ 1/(2πn) shrinks with n
- Weight: w_Q(p) = 2·log(p)/√p decays slowly
- Density: a*(ξ) grows like log(πξ), NOT fast enough

Strategy: Use truncation + tail bound.

References:
- TASK.md in sandbox measure_dom
- Weil explicit formula: Q(Φ) = arch_term(Φ) - prime_term(Φ)
-/

import Mathlib
import Q3.Basic.Defs

set_option linter.mathlibStandardSet false

open scoped BigOperators Real
open MeasureTheory

noncomputable section

namespace Q3.MeasureDomination

/-! ## Prime Gap Analysis -/

/-- Prime spectral gap: ξ_{n+1} - ξ_n = log((n+1)/n)/(2π) -/
def spectral_gap (n : ℕ) : ℝ := xi_n (n + 1) - xi_n n

/-- Gap positivity: for n ≥ 1, gap_n > 0
Proof: ξ_{n+1} > ξ_n since log is strictly increasing -/
lemma spectral_gap_pos (n : ℕ) (hn : n ≥ 1) : spectral_gap n > 0 := by
  unfold spectral_gap xi_n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
  have h_denom_pos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  -- log(n+1)/(2π) - log(n)/(2π) = (log(n+1) - log(n))/(2π) > 0
  rw [div_sub_div_same]
  apply div_pos _ h_denom_pos
  rw [sub_pos]
  apply Real.log_lt_log hn_pos
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

/-- Gap is strictly decreasing: gap_{n+1} < gap_n for n ≥ 1
Proof: log((n+2)/(n+1)) < log((n+1)/n) since (n+2)/(n+1) < (n+1)/n -/
lemma spectral_gap_strictly_decreasing (n : ℕ) (hn : n ≥ 1) :
    spectral_gap (n + 1) < spectral_gap n := by
  unfold spectral_gap xi_n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
  have h_denom_pos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  simp only [Nat.cast_add, Nat.cast_one]
  rw [div_sub_div_same, div_sub_div_same]
  apply div_lt_div_of_pos_right _ h_denom_pos
  -- Need: log(n+2) - log(n+1) < log(n+1) - log n
  rw [← Real.log_div (by linarith : (n : ℝ) + 1 + 1 ≠ 0) (by linarith : (n : ℝ) + 1 ≠ 0),
      ← Real.log_div (by linarith : (n : ℝ) + 1 ≠ 0) (ne_of_gt hn_pos)]
  apply Real.log_lt_log
  · apply div_pos <;> linarith
  · rw [div_lt_div_iff₀ (by linarith) hn_pos]
    ring_nf
    nlinarith

/-! ## Neighborhood Construction -/

/-- Disjoint neighborhood radius: δ_n = gap_n/2 -/
def neighborhood_radius (n : ℕ) : ℝ := spectral_gap n / 2

/-- Neighborhood interval around ξ_n -/
def neighborhood (n : ℕ) : Set ℝ :=
  Set.Icc (xi_n n - neighborhood_radius n) (xi_n n + neighborhood_radius n)

/-- Neighborhood radius is positive for n ≥ 1 -/
lemma neighborhood_radius_pos (n : ℕ) (hn : n ≥ 1) : neighborhood_radius n > 0 := by
  unfold neighborhood_radius
  exact div_pos (spectral_gap_pos n hn) (by norm_num)

/-- Neighborhoods are disjoint for consecutive indices.

This is the key structural lemma: with δ_n = gap_n/2, neighborhoods don't overlap.
Proof: If x ∈ I_n ∩ I_{n+1}, then gap_n/2 ≥ gap_n - gap_{n+1}/2,
which implies gap_{n+1} ≥ gap_n, contradicting strict decrease. -/
theorem neighborhoods_disjoint (n : ℕ) (hn : n ≥ 1) :
    Disjoint (neighborhood n) (neighborhood (n + 1)) := by
  unfold neighborhood neighborhood_radius
  rw [Set.disjoint_iff]
  intro x hx
  obtain ⟨⟨hx_lo_n, hx_hi_n⟩, ⟨hx_lo_n1, hx_hi_n1⟩⟩ := hx
  have h_gap_rel : xi_n (n + 1) = xi_n n + spectral_gap n := by
    unfold spectral_gap; ring
  rw [h_gap_rel] at hx_lo_n1
  -- From: x ≤ ξ_n + gap_n/2 and x ≥ ξ_n + gap_n - gap_{n+1}/2
  -- We get: gap_n/2 ≥ gap_n - gap_{n+1}/2
  -- Hence: gap_{n+1} ≥ gap_n
  -- But this contradicts strictly decreasing gaps!
  have hcontra : spectral_gap n / 2 ≥ spectral_gap n - spectral_gap (n + 1) / 2 := by linarith
  have hgap_ineq : spectral_gap (n + 1) ≥ spectral_gap n := by linarith
  have hgap_strict := spectral_gap_strictly_decreasing n hn
  linarith

/-! ## The Obstruction for Large n

For the neighborhood approach to work, we need:
  w_Q(n) · Φ(ξ_n) ≤ ∫_{I_n} a*(ξ) · Φ(ξ) dξ

Approximating the RHS for smooth Φ:
  ∫_{I_n} a*(ξ) · Φ(ξ) dξ ≈ a*(ξ_n) · Φ(ξ_n) · 2δ_n

So we need:
  w_Q(n) ≤ a*(ξ_n) · 2δ_n ≈ a*(ξ_n) · gap_n ≈ a*(ξ_n) / (2πn)

For prime p:
  w_Q(p) = 2·log(p)/√p

The comparison becomes:
  2·log(p)/√p ≲ a*(ξ_p) / (2πp)
  ⟹ a*(ξ_p) ≳ 4π·p·log(p)/√p = 4π·√p·log(p)

But a*(ξ) grows like log(πξ), NOT like √(e^{2πξ})·log(e^{2πξ}) = √n·log(n).

This is the fundamental obstruction!
-/

/-- The critical ratio: w_Q(n) / (2 · neighborhood_radius n)

For the neighborhood approach to work, we need critical_ratio(n) ≤ a*(ξ_n).
This fails for large n because the ratio grows while a* grows slowly.
-/
def critical_ratio (n : ℕ) : ℝ := w_Q n / (2 * neighborhood_radius n)

/-! ## Truncated Approach

For finite sums over n ∈ [2, N₀], the neighborhood approach works
because there are only finitely many terms and gaps are bounded below.
-/

/-- Finite sum over truncated range -/
def truncated_prime_term (N₀ : ℕ) (Φ : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N₀, w_Q n * Φ (xi_n n)

/-- Minimum gap in range [2, N₀] (achieved at N₀) -/
def min_gap (N₀ : ℕ) : ℝ := spectral_gap N₀

/-- Tail error bound: sum over n > N₀ decays -/
def tail_error (N₀ : ℕ) (K : ℝ) (Φ_max : ℝ) : ℝ :=
  Φ_max * ∑' n, if n > N₀ ∧ |xi_n n| ≤ K then w_Q n else 0

/-- Tail error goes to zero as N₀ → ∞

Proof sketch: The set of n with |ξ_n| ≤ K is finite, so the tail sum
eventually becomes empty. -/
lemma tail_error_tendsto (K : ℝ) (hK : K > 0) (Φ_max : ℝ) :
    Filter.Tendsto (fun N₀ => tail_error N₀ K Φ_max) Filter.atTop (nhds 0) := by
  sorry

/-! ## Main Theorem: Measure Domination via Truncation -/

/-- Measure domination for truncated sums plus tail error

This is a weaker form of measure domination that holds for any N₀:
the truncated sum is bounded by arch_term plus a tail error that vanishes
as N₀ → ∞.
-/
theorem measure_domination_truncated (K : ℝ) (hK : K > 0) (N₀ : ℕ) (hN₀ : N₀ ≥ 2)
    (Φ : ℝ → ℝ) (hΦ_cont : Continuous Φ) (hΦ_nonneg : ∀ x, 0 ≤ Φ x)
    (hΦ_support : Function.support Φ ⊆ Set.Icc (-K) K)
    (Φ_max : ℝ) (hΦ_max : ∀ x ∈ Set.Icc (-K) K, Φ x ≤ Φ_max) :
    truncated_prime_term N₀ Φ ≤ arch_term Φ + tail_error N₀ K Φ_max := by
  sorry

/-!
## Summary

The "disjoint neighborhood" approach to measure domination has a fundamental
obstruction for large n:

1. **Prime gap shrinks**: gap_n ≈ 1/(2πn)
2. **Weight decays slowly**: w_Q(p) = 2·log(p)/√p
3. **Density growth insufficient**: a*(ξ) ~ log(πξ)

The comparison w_Q(n) ≤ a*(ξ_n) · gap_n fails for large primes because
we would need a*(ξ_p) ≳ √p · log(p), but a* only grows logarithmically.

**Working alternatives:**
- Truncation: Use truncated sum + tail bound
- Rayleigh identification: Already implemented in the main Q3 proof chain

The Rayleigh approach (via Toeplitz operators) is more powerful because it
doesn't require point-by-point comparison—it uses spectral theory instead.
-/

end Q3.MeasureDomination

end
