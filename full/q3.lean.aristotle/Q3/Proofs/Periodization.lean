/-
Periodization Lemmas (Lean-Friendly)
====================================

This file provides LIGHTWEIGHT periodization lemmas that AVOID the heavy
`integral_tsum_of_summable_integral_norm` machinery which causes OOM.

KEY INSIGHT (from Proshka analysis):
- g B t has compact support in [-B, B]
- On θ ∈ [-1/2, 1/2], the periodization sum ∑' n, g(θ+n) is FINITE
- This means: no dominated convergence needed, just Finset.sum + linearity

PROOF STATUS: ALL PROOFS COMPLETE ✓
No sorries, no axioms (except standard Mathlib axioms).

Reference: docs/PERIODIZATION_INSIGHT.md
-/

import Mathlib

open scoped BigOperators Real
open MeasureTheory intervalIntegral Set Finset

set_option linter.unusedVariables false

namespace Q3.Proofs.Periodization

/-! ## Lemma 1: Outside large |n|, g(θ+n) = 0

For θ ∈ [-1/2, 1/2] and |n| > B + 1, we have |θ + n| > B,
so g(θ+n) = 0 by compact support.

**Mathematical proof:**
- θ ∈ [-1/2, 1/2] implies |θ| ≤ 1/2
- |n| > ⌈B+1⌉ implies |n| ≥ B + 1
- Triangle inequality: |θ + n| ≥ |n| - |θ| ≥ (B+1) - 1/2 > B
- By compact support hypothesis: f(θ + n) = 0
-/

/-- If f has support in [-B, B], then for |n| large enough and θ ∈ [-1/2, 1/2],
    f(θ + n) = 0. The cutoff is N = ⌈B + 1⌉. -/
lemma support_implies_finite_periodization
    {f : ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hsupp : ∀ x, B < |x| → f x = 0) :
    ∃ N : ℕ, ∀ θ ∈ Icc (-(1/2 : ℝ)) (1/2),
      ∀ n : ℤ, (N : ℝ) < |n| → f (θ + n) = 0 := by
  use Nat.ceil (B + 1)
  intro θ hθ n hn
  apply hsupp
  -- Need: B < |θ + (n : ℝ)|
  have hθ_abs : |θ| ≤ 1/2 := abs_le.mpr ⟨hθ.1, hθ.2⟩
  have hN_ge : B + 1 ≤ (Nat.ceil (B + 1) : ℝ) := Nat.le_ceil (B + 1)
  -- Convert |n| to real absolute value
  have hn_real : (Nat.ceil (B + 1) : ℝ) < |(n : ℝ)| := by
    simp only [Int.cast_abs] at hn
    exact hn
  -- Triangle inequality: |θ + n| ≥ |n| - |θ|
  have htri : |(n : ℝ)| - |θ| ≤ |θ + (n : ℝ)| := by
    have h := abs_sub_abs_le_abs_sub (n : ℝ) (-θ)
    simp only [sub_neg_eq_add, abs_neg] at h
    have heq : |θ + (n : ℝ)| = |(n : ℝ) + θ| := by ring_nf
    linarith
  -- Chain: B < B + 1/2 ≤ ⌈B+1⌉ - 1/2 < |n| - 1/2 ≤ |n| - |θ| ≤ |θ + n|
  linarith

/-! ## Lemma 2: tsum = Finset.sum when outside is zero -/

/-- Convert tsum to Finset.sum when terms outside the set are zero. -/
lemma tsum_eq_finset_sum_of_outside_zero
    (f : ℤ → ℝ) (S : Finset ℤ)
    (hz : ∀ n, n ∉ S → f n = 0) :
    (∑' n : ℤ, f n) = ∑ n ∈ S, f n :=
  tsum_eq_sum (fun n hn => hz n hn)

/-! ## Lemma 3: Periodization on torus = Finset.sum -/

/-- On the fundamental domain [-1/2, 1/2], periodization is finite.
    Also returns the bound B + 1 ≤ N for use in later proofs. -/
lemma periodization_eq_finset_sum
    {f : ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hsupp : ∀ x, B < |x| → f x = 0) :
    ∃ N : ℕ, (B + 1 ≤ N) ∧ ∀ θ ∈ Icc (-(1/2 : ℝ)) (1/2),
      (∑' n : ℤ, f (θ + n)) = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, f (θ + n) := by
  -- Use N = ⌈B + 1⌉ directly to preserve the bound
  let N := Nat.ceil (B + 1)
  use N
  constructor
  · exact Nat.le_ceil (B + 1)
  · -- Get the support property
    have hN : ∀ θ ∈ Icc (-(1/2 : ℝ)) (1/2), ∀ n : ℤ, (N : ℝ) < |n| → f (θ + n) = 0 := by
      intro θ hθ n hn
      apply hsupp
      have hθ_abs : |θ| ≤ 1/2 := abs_le.mpr ⟨hθ.1, hθ.2⟩
      have hN_ge : B + 1 ≤ (N : ℝ) := Nat.le_ceil (B + 1)
      -- Bridge: (|n| : ℝ) = |(n : ℝ)|
      have hn' : (N : ℝ) < |(n : ℝ)| := by
        have habs_eq : ((|n| : ℤ) : ℝ) = |(n : ℝ)| := Int.cast_abs
        rw [← habs_eq]
        exact hn
      have htri : |(n : ℝ)| - |θ| ≤ |θ + (n : ℝ)| := by
        have h := abs_sub_abs_le_abs_sub (n : ℝ) (-θ)
        simp only [sub_neg_eq_add, abs_neg] at h
        have heq : |θ + (n : ℝ)| = |(n : ℝ) + θ| := by ring_nf
        linarith
      linarith
    intro θ hθ
    apply tsum_eq_finset_sum_of_outside_zero
    intro n hn
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    apply hN θ hθ n
    -- n ∉ Icc(-N, N) means n < -N or N < n, which gives |n| > N
    simp only [Int.cast_abs]
    rcases hn with h | h
    · -- Case: n < -(N : ℤ)
      have hn_neg : n < 0 := by omega
      rw [abs_of_neg (by exact_mod_cast hn_neg : (n : ℝ) < 0)]
      have : -n > (N : ℤ) := by omega
      calc (N : ℝ) < ((-n : ℤ) : ℝ) := by exact_mod_cast this
        _ = -(n : ℝ) := by push_cast; ring
    · -- Case: (N : ℤ) < n
      have hn_pos : 0 ≤ n := by omega
      rw [abs_of_nonneg (by exact_mod_cast hn_pos : 0 ≤ (n : ℝ))]
      exact_mod_cast h

/-! ## Lemma 4: Integral of periodization (NO dominated convergence!)

The key result: ∫_{-1/2}^{1/2} (∑' n, f(θ+n)) dθ = ∫_ℝ f(x) dx

**Mathematical proof:**
1. Replace tsum with Finset.sum using periodization_eq_finset_sum (pointwise)
2. Swap integral and finite sum (trivial linearity for Finset.sum)
3. Change of variables: ∫ f(θ+n) dθ = ∫_{n-1/2}^{n+1/2} f(x) dx
4. Sum of shifted unit intervals = integral over ℝ (by Integrable.hasSum_intervalIntegral)
5. Outside N, integrals vanish (compact support)

This AVOIDS `integral_tsum_of_summable_integral_norm` completely!
-/

/-- Integral of periodization equals integral over ℝ.
    NO dominated convergence needed - uses finite sum reduction.

    **PROOF NOTE:** Uses Mathlib's hasSum_intervalIntegral but avoids
    the heavy integral_tsum machinery by reducing to finite sums first. -/
theorem intervalIntegral_periodization_eq_integral
    {f : ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hsupp : ∀ x, B < |x| → f x = 0)
    (hint : Integrable f) :
    (∫ θ in (-(1/2 : ℝ))..(1/2), ∑' n : ℤ, f (θ + n)) = ∫ x, f x := by
  classical
  -- Step 1: Get finite reduction (N, bound, and finite sum property)
  obtain ⟨N, hN_bound, hN⟩ := periodization_eq_finset_sum hB hsupp
  let S := Finset.Icc (-(N : ℤ)) N

  -- Step 2: Rewrite integrand to Finset.sum (pointwise equal on interval)
  have step1 : (∫ θ in (-(1/2 : ℝ))..(1/2), ∑' n : ℤ, f (θ + n)) =
               ∫ θ in (-(1/2 : ℝ))..(1/2), ∑ n ∈ S, f (θ + n) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (-(1/2 : ℝ)) (1/2) := by
      simp only [Set.uIcc_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2)] at hθ
      exact hθ
    exact hN θ hθ'

  -- Step 3: Swap finite sum and integral
  have step2 : (∫ θ in (-(1/2 : ℝ))..(1/2), ∑ n ∈ S, f (θ + n)) =
               ∑ n ∈ S, ∫ θ in (-(1/2 : ℝ))..(1/2), f (θ + n) := by
    rw [intervalIntegral.integral_finset_sum]
    intro n _
    exact (hint.comp_add_right n).intervalIntegrable

  -- Step 4: Change of variables in each integral
  have step3 : ∑ n ∈ S, ∫ θ in (-(1/2 : ℝ))..(1/2), f (θ + n) =
               ∑ n ∈ S, ∫ x in (-(1/2 : ℝ) + n)..(1/2 + n), f x := by
    apply Finset.sum_congr rfl
    intro n _
    rw [← intervalIntegral.integral_comp_add_right]

  -- Step 5: Outside S, integrals vanish (compact support)
  have outside_zero : ∀ n : ℤ, n ∉ S →
      (∫ x in (-(1/2 : ℝ) + n)..(1/2 + n), f x) = 0 := by
    intro n hn
    -- f is zero on this interval because |x| > B for all x in the interval
    apply intervalIntegral.integral_zero_ae
    filter_upwards with x hx
    apply hsupp
    -- hx : x ∈ Ι (-(1/2) + n) (1/2 + n) = Set.uIoc (-(1/2) + n) (1/2 + n)
    simp only [Set.mem_uIoc] at hx
    -- hN_bound : B + 1 ≤ N (from periodization_eq_finset_sum)
    -- n ∉ S means n < -N or N < n
    simp only [S, Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with h | h
    · -- n < -(N : ℤ)
      have hn_bound : (n : ℝ) < -(N : ℝ) := by exact_mod_cast h
      have hx_upper : x ≤ (1/2 : ℝ) + n := by
        rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;> linarith
      have hx_neg : x < 0 := by linarith
      rw [abs_of_neg hx_neg]
      linarith
    · -- (N : ℤ) < n
      have hn_bound : (N : ℝ) < (n : ℝ) := by exact_mod_cast h
      have hx_lower : -(1/2 : ℝ) + n < x := by
        rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;> linarith
      have hx_pos : 0 < x := by linarith
      rw [abs_of_pos hx_pos]
      linarith

  -- Step 6: The HasSum from Mathlib
  have hsum : HasSum (fun n : ℤ => ∫ x in (-(1/2 : ℝ) + n)..(-(1/2 : ℝ) + n + 1), f x)
                     (∫ x, f x) := hint.hasSum_intervalIntegral (y := -(1/2 : ℝ))

  -- Step 7: Intervals match: [-1/2 + n, 1/2 + n] = [-1/2 + n, -1/2 + n + 1]
  have interval_eq : ∀ n : ℤ,
      (∫ x in (-(1/2 : ℝ) + n)..(1/2 + n), f x) =
      (∫ x in (-(1/2 : ℝ) + n)..(-(1/2 : ℝ) + n + 1), f x) := by
    intro n
    congr 1
    ring

  -- Combine all steps
  calc (∫ θ in (-(1/2 : ℝ))..(1/2), ∑' n : ℤ, f (θ + n))
      = ∫ θ in (-(1/2 : ℝ))..(1/2), ∑ n ∈ S, f (θ + n) := step1
    _ = ∑ n ∈ S, ∫ θ in (-(1/2 : ℝ))..(1/2), f (θ + n) := step2
    _ = ∑ n ∈ S, ∫ x in (-(1/2 : ℝ) + n)..(1/2 + n), f x := step3
    _ = ∑ n ∈ S, ∫ x in (-(1/2 : ℝ) + n)..(-(1/2 : ℝ) + n + 1), f x := by
        apply Finset.sum_congr rfl
        intro n _
        exact interval_eq n
    _ = ∑' n : ℤ, ∫ x in (-(1/2 : ℝ) + n)..(-(1/2 : ℝ) + n + 1), f x := by
        symm
        apply tsum_eq_finset_sum_of_outside_zero
        intro n hn
        rw [← interval_eq n]
        exact outside_zero n hn
    _ = ∫ x, f x := hsum.tsum_eq

end Q3.Proofs.Periodization
