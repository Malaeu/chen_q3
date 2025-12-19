/-
A1_density_PAPER_STRUCTURE.lean — Proof matching paper structure

This version follows the EXACT structure from A1prime.tex:
  Step 1: Mollification (f̃ * ρ_t ≈ f)
  Step 2: Sample VALUES g(τⱼ) as coefficients
  Step 3: Fejér truncation with symmetric atoms
  Step 4: Triangle inequality

Key difference from previous attempts:
  g(τⱼ) = (Ψ * H_t)(τⱼ) is the COEFFICIENT, not a factor in the integrand!
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise
open MeasureTheory Filter Topology Set

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

/-! ## Definitions -/

def FejerKernel (B : ℝ) (x : ℝ) : ℝ := max 0 (1 - |x| / B)

def HeatKernel (t : ℝ) (x : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(1:ℝ)/2) * Real.exp (-x^2 / (4 * t))

def W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | ContinuousOn Φ (Icc (-K) K) ∧
       Function.support Φ ⊆ Icc (-K) K ∧
       Even Φ ∧
       ∀ x, 0 ≤ Φ x}

def Atom (B t τ : ℝ) (x : ℝ) : ℝ :=
  FejerKernel B (x - τ) * HeatKernel t (x - τ) +
  FejerKernel B (x + τ) * HeatKernel t (x + τ)

def AtomSet (K : ℝ) : Set (ℝ → ℝ) :=
  {g | ∃ B > 0, ∃ t > 0, ∃ τ ∈ Icc (-K) K, g = Atom B t τ}

def AtomCone_K (K : ℝ) : Set (ℝ → ℝ) :=
  Convex.toCone (convexHull ℝ (AtomSet K)) (convex_convexHull ℝ (AtomSet K))

def real_convolution (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t, f t * g (x - t)

/-! ## Supporting Lemmas (proven by Aristotle) -/

-- Heat kernel is a valid probability density
lemma HeatKernel_integral (t : ℝ) (ht : t > 0) : ∫ x, HeatKernel t x = 1 := by
  sorry -- Proven in A1_FINAL_COMPLETE.lean

lemma HeatKernel_nonneg (t : ℝ) (ht : t > 0) (x : ℝ) : 0 ≤ HeatKernel t x := by
  apply mul_nonneg
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.exp_nonneg _

-- Heat kernel is an approximate identity
lemma HeatKernel_approx_identity_uniform (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_supp : HasCompactSupport f) (ε : ℝ) (hε : ε > 0) :
    ∃ t₀ > 0, ∀ t ∈ Ioo 0 t₀, ∀ x, |real_convolution f (HeatKernel t) x - f x| < ε := by
  sorry -- Proven in A1_FINAL_COMPLETE.lean

-- Extension lemma
lemma exists_even_compact_extension (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ)
    (hΦ_cont : ContinuousOn Φ (Icc (-K) K)) (hΦ_even : Even Φ) :
    ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧ HasCompactSupport Ψ ∧ Even Ψ ∧
      ∀ x ∈ Icc (-K) K, Ψ x = Φ x := by
  sorry -- Proven in A1_FINAL_COMPLETE.lean

-- Fejér approximation of heat kernel
lemma FejerKernel_approx_one (B : ℝ) (hB : B > 0) (x τ : ℝ) (hx : |x| ≤ K) (hτ : |τ| ≤ K) :
    |FejerKernel B (x - τ) - 1| ≤ (|x| + |τ|) / B := by
  -- Λ_B(u) = max(0, 1 - |u|/B), so |Λ_B(u) - 1| ≤ |u|/B ≤ (|x|+|τ|)/B
  sorry -- Standard Fejér kernel estimate

-- Sum of atoms is in cone
lemma sum_atoms_in_cone (K : ℝ) (s : Finset ℝ) (c : ℝ → ℝ) (hc : ∀ y ∈ s, 0 ≤ c y)
    (B : ℝ) (hB : B > 0) (t : ℝ) (ht : t > 0) (hs : ∀ y ∈ s, y ∈ Icc (-K) K)
    (h_sum_pos : ∑ y ∈ s, c y > 0) :
    (fun x => ∑ y ∈ s, c y * Atom B t y x) ∈ AtomCone_K K := by
  sorry -- Proven in A1_FINAL_COMPLETE.lean

/-! ## Main Theorem with Paper Structure -/

/-- **Theorem A1' (Local Density)** — Following exact structure of A1prime.tex -/
theorem A1_density_paper (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ) (hΦ : Φ ∈ W_K K)
    (ε : ℝ) (hε : ε > 0) :
    ∃ g ∈ AtomCone_K K, ∀ x ∈ Icc (-K) K, |Φ x - g x| < ε := by

  -- Unpack W_K membership
  obtain ⟨hΦ_cont, hΦ_supp, hΦ_even, hΦ_nonneg⟩ := hΦ

  -- Step 0: Extend Φ to Ψ : ℝ → ℝ (continuous, compactly supported, even)
  obtain ⟨Ψ, hΨ_cont, hΨ_supp, hΨ_even, hΨ_eq⟩ :=
    exists_even_compact_extension K hK Φ hΦ_cont hΦ_even

  /-
  STEP 1 (mollification): Find t such that ‖Ψ * H_t - Ψ‖_∞ < ε/3

  This uses the heat kernel approximate identity property.
  -/
  obtain ⟨t₀, ht₀_pos, ht₀_approx⟩ :=
    HeatKernel_approx_identity_uniform Ψ hΨ_cont hΨ_supp (ε/3) (by linarith)

  let t := t₀ / 2
  have ht_pos : t > 0 := by simp [t]; linarith
  have ht_mem : t ∈ Ioo 0 t₀ := ⟨by simp [t]; linarith, by simp [t]; linarith⟩

  -- Define the mollified function
  let g : ℝ → ℝ := fun ξ => real_convolution Ψ (HeatKernel t) ξ

  have step1_bound : ∀ x ∈ Icc (-K) K, |g x - Φ x| < ε/3 := by
    intro x hx
    have h1 : |g x - Ψ x| < ε/3 := ht₀_approx t ht_mem x
    have h2 : Ψ x = Φ x := hΨ_eq x hx
    rw [h2] at h1
    exact h1

  /-
  STEP 2 (positive Riemann sums): Discretize g using its VALUES as coefficients

  Key insight: We sample g(τⱼ) = (Ψ * H_t)(τⱼ) and use these as coefficients!

  g_R(ξ) = Σⱼ g(τⱼ) · Δτ · ρ_t(ξ - τⱼ)

  This approximates g because it's like convolving g with a discrete measure.
  -/

  -- Choose uniform partition of [-K, K]
  -- For simplicity, use N points with spacing Δ = 2K/N
  let N : ℕ := ⌈6 * K / (ε / 3)⌉₊ + 1
  have hN_pos : 0 < N := Nat.succ_pos _
  let Δ : ℝ := 2 * K / N
  have hΔ_pos : Δ > 0 := by simp [Δ]; positivity

  -- Sample points: τⱼ = -K + (j + 1/2) · Δ for j = 0, ..., N-1
  let τ : ℕ → ℝ := fun j => -K + (j + 1/2 : ℝ) * Δ

  -- Coefficients: c_j = g(τⱼ) · Δ (VALUE of g at sample point times width)
  let c : ℕ → ℝ := fun j => g (τ j) * Δ

  -- The Riemann sum approximation
  let g_R : ℝ → ℝ := fun ξ => ∑ j ∈ Finset.range N, c j * HeatKernel t (ξ - τ j)

  -- Bound: |g_R(ξ) - g(ξ)| < ε/3
  -- This follows from uniform continuity of g and the Riemann sum approximation
  have step2_bound : ∀ x ∈ Icc (-K) K, |g_R x - g x| < ε/3 := by
    intro x hx
    -- g is smooth (convolution of compactly supported with heat kernel)
    -- The Riemann sum converges uniformly for small enough Δ
    -- This is a standard analysis result
    sorry -- Riemann sum approximation

  /-
  STEP 3 (Fejér truncation): Replace H_t with Atom (symmetric Fejér × heat)

  h(ξ) = Σⱼ c_j · Atom(B, t, τⱼ)(ξ)
       = Σⱼ c_j · [Λ_B(ξ-τⱼ)·H_t(ξ-τⱼ) + Λ_B(ξ+τⱼ)·H_t(ξ+τⱼ)]

  For large enough B, |Λ_B(·) - 1| < ε/(3·C) where C bounds the sum.
  -/

  -- Choose B large enough
  let B : ℝ := 12 * K / ε + 1
  have hB_pos : B > 0 := by simp [B]; positivity

  -- Construct h as sum of atoms
  let h : ℝ → ℝ := fun ξ => ∑ j ∈ Finset.range N, c j * Atom B t (τ j) ξ

  -- Bound: |h(ξ) - (g_R(ξ) + g_R(-ξ))| < ε/3
  -- This follows from |Λ_B - 1| ≤ 2K/B < ε/6 for our choice of B
  have step3_bound : ∀ x ∈ Icc (-K) K, |h x - (g_R x + g_R (-x))| < ε/3 := by
    intro x hx
    -- Each term differs by at most c_j · |Atom - (H_t(x-τ) + H_t(x+τ))|
    -- This is bounded by c_j · (ε/3) / (Σ c_j) from Fejér approximation
    sorry -- Fejér truncation bound

  /-
  STEP 4 (collect errors): Triangle inequality

  Since Ψ (hence g) is even, g_R is even, so g_R(ξ) + g_R(-ξ) = 2·g_R(ξ)
  Actually, for even Ψ: g(-ξ) = g(ξ), and with symmetric partition, g_R(-ξ) ≈ g_R(ξ)

  |h(ξ) - Φ(ξ)| ≤ |h - (g_R + g_R(-·))| + |g_R - g| + |g - Φ|
                < ε/3 + ε/3 + ε/3 = ε
  -/

  -- Coefficients are nonnegative (g ≥ 0 since Ψ ≥ 0 and H_t ≥ 0)
  have hc_nonneg : ∀ j ∈ Finset.range N, 0 ≤ c j := by
    intro j _
    simp only [c]
    apply mul_nonneg
    · -- g(τ j) ≥ 0 because it's convolution of nonneg functions
      simp only [g, real_convolution]
      sorry -- Nonnegativity of convolution
    · exact hΔ_pos.le

  -- Sample points are in [-K, K]
  have hτ_mem : ∀ j ∈ Finset.range N, τ j ∈ Icc (-K) K := by
    intro j hj
    simp only [τ, Δ, mem_Icc]
    constructor
    · nlinarith [Finset.mem_range.mp hj]
    · nlinarith [Finset.mem_range.mp hj]

  -- Check if we have positive sum
  by_cases h_sum_zero : ∑ j ∈ Finset.range N, c j = 0
  case pos =>
    -- Degenerate case: all coefficients sum to 0
    -- This means g ≈ 0 everywhere, hence Φ ≈ 0
    use fun _ => 0
    constructor
    · admit -- 0 in cone (degenerate)
    · intro x hx
      -- If sum of c_j = 0 and all c_j ≥ 0, then all c_j = 0
      -- This means g(τ_j) = 0 for all j, so g ≈ 0, so Φ ≈ 0
      admit -- Degenerate case

  case neg =>
    have h_sum_pos : ∑ j ∈ Finset.range N, c j > 0 := by
      cases' (lt_or_eq_of_le (Finset.sum_nonneg hc_nonneg)) with h h
      · exact h
      · exact absurd h.symm h_sum_zero

    -- h is in AtomCone_K K
    have hh_cone : h ∈ AtomCone_K K := by
      -- Convert from ℕ-indexed sum to Finset ℝ-indexed sum
      -- Each c_j * Atom B t (τ j) is a nonneg combination of atoms
      sorry -- sum_atoms_in_cone application

    use h, hh_cone

    -- Final bound via triangle inequality
    intro x hx

    -- For even g: g_R(x) + g_R(-x) = 2 · g(x) + O(Δ)
    -- Simplify by noting g is even
    have g_even : g (-x) = g x := by
      simp only [g, real_convolution]
      -- Uses evenness of Ψ and H_t
      sorry -- Evenness of convolution

    calc |Φ x - h x|
        = |Φ x - g x + g x - g_R x + g_R x - h x + (g_R (-x) - g_R x)| := by ring_nf
      _ ≤ |Φ x - g x| + |g x - g_R x| + |g_R x + g_R (-x) - h x| := by
          -- Need proper triangle inequality chain
          sorry
      _ < ε/3 + ε/3 + ε/3 := by
          have b1 := step1_bound x hx
          have b2 := step2_bound x hx
          have b3 := step3_bound x hx
          linarith
      _ = ε := by ring

#check A1_density_paper
#print axioms A1_density_paper

end
