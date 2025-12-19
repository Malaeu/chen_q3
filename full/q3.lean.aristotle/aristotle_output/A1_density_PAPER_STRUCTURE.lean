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

-- Normalized even symmetrization: (1/2) factor so that Sym fixes even functions
-- "Scaling generators by a positive constant does not change the generated cone"
def Atom (B t τ : ℝ) (x : ℝ) : ℝ :=
  (1/2) * (FejerKernel B (x - τ) * HeatKernel t (x - τ) +
           FejerKernel B (x + τ) * HeatKernel t (x + τ))

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

-- Extension lemma (with nonnegativity preservation)
lemma exists_even_compact_extension_nonneg (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ)
    (hΦ_cont : ContinuousOn Φ (Icc (-K) K)) (hΦ_even : Even Φ) (hΦ_nonneg : ∀ x, 0 ≤ Φ x) :
    ∃ Ψ : ℝ → ℝ, Continuous Ψ ∧ HasCompactSupport Ψ ∧ Even Ψ ∧
      (∀ x, 0 ≤ Ψ x) ∧ ∀ x ∈ Icc (-K) K, Ψ x = Φ x := by
  -- Standard construction: Extend by 0 outside [-2K, 2K] with smooth bump
  -- Since Φ ≥ 0 and bump ≥ 0, the extension Ψ ≥ 0
  sorry -- Extension with nonnegativity (Tietze + smooth cutoff)

-- Extension lemma (without nonnegativity, for compatibility)
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

  -- Step 0: Extend Φ to Ψ : ℝ → ℝ (continuous, compactly supported, even, nonneg)
  obtain ⟨Ψ, hΨ_cont, hΨ_supp, hΨ_even, hΨ_nonneg, hΨ_eq⟩ :=
    exists_even_compact_extension_nonneg K hK Φ hΦ_cont hΦ_even hΦ_nonneg

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
  STEP 3 (Fejér truncation): Replace H_t with normalized Atom

  With normalized atom (1/2 factor), h approximates g_R^sym directly:
    h(ξ) = Σⱼ c_j · Atom(B, t, τⱼ)(ξ)
         = Σⱼ c_j · (1/2)[Λ_B(ξ-τⱼ)·H_t(ξ-τⱼ) + Λ_B(ξ+τⱼ)·H_t(ξ+τⱼ)]

  Define g_R^sym := (g_R(ξ) + g_R(-ξ))/2 (normalized even symmetrization).
  For large enough B, |Λ_B(·) - 1| ≤ 2K/B, so |h - g_R^sym| < ε/3.
  -/

  -- Define normalized symmetrization
  let g_R_sym : ℝ → ℝ := fun ξ => (g_R ξ + g_R (-ξ)) / 2

  -- Choose B large enough: need (2K/B) · C_f ≤ ε/3, so B ≥ 6KC_f/ε
  let B : ℝ := 12 * K / ε + 1
  have hB_pos : B > 0 := by simp [B]; positivity

  -- Construct h as sum of normalized atoms
  let h : ℝ → ℝ := fun ξ => ∑ j ∈ Finset.range N, c j * Atom B t (τ j) ξ

  -- Bound: |h(ξ) - g_R^sym(ξ)| < ε/3
  -- With normalized atom, this follows directly from |Λ_B - 1| ≤ 2K/B
  have step3_bound : ∀ x ∈ Icc (-K) K, |h x - g_R_sym x| < ε/3 := by
    intro x hx
    -- h = (1/2) Σ c_j [Λ_B·H_t(x-τ) + Λ_B·H_t(x+τ)]
    -- g_R_sym = (1/2)(Σ c_j H_t(x-τ) + Σ c_j H_t(-x-τ))
    -- Difference bounded by (1/2) · 2 · (2K/B) · Σ c_j ≤ ε/3
    sorry -- Fejér truncation bound (now cleaner with normalized atoms)

  -- g is even (convolution of even Ψ with even HeatKernel)
  have hg_even : ∀ x, g x = g (-x) := by
    intro x
    simp only [g, real_convolution]
    -- (Ψ * H_t)(x) = ∫ Ψ(y)·H_t(x-y) dy
    -- (Ψ * H_t)(-x) = ∫ Ψ(y)·H_t(-x-y) dy
    -- Substitution u = -y: = ∫ Ψ(-u)·H_t(-x+u) du = ∫ Ψ(u)·H_t(u-x) du
    -- Since Ψ even and H_t even, this equals original integral
    sorry -- Convolution of even functions is even

  -- Key: Sym is contractive and fixes even functions
  -- ‖g_R^sym - g‖ = ‖Sym(g_R) - Sym(g)‖ ≤ ‖g_R - g‖ < ε/3
  have sym_contractive : ∀ x ∈ Icc (-K) K, |g_R_sym x - g x| < ε/3 := by
    intro x hx
    simp only [g_R_sym]
    have hx_neg : -x ∈ Icc (-K) K := by simp only [mem_Icc] at hx ⊢; constructor <;> linarith
    have b2_x := step2_bound x hx        -- |g_R x - g x| < ε/3
    have b2_neg := step2_bound (-x) hx_neg  -- |g_R(-x) - g(-x)| < ε/3
    -- g is even: g(-x) = g(x)
    have h3 : g (-x) = g x := (hg_even x).symm
    -- So |g_R(-x) - g(-x)| = |g_R(-x) - g(x)|
    rw [h3] at b2_neg
    -- Also g(x) = (g(x) + g(-x))/2 since g(-x) = g(x)
    have hg_sym : g x = (g x + g (-x)) / 2 := by rw [h3]; ring
    rw [hg_sym, h3]
    -- Now bound |(g_R x + g_R(-x))/2 - (g x + g x)/2|
    have calc1 : |(g_R x + g_R (-x)) / 2 - (g x + g x) / 2| =
                 |((g_R x - g x) + (g_R (-x) - g x)) / 2| := by ring_nf
    rw [calc1]
    have h4 : |((g_R x - g x) + (g_R (-x) - g x)) / 2| ≤
              (|g_R x - g x| + |g_R (-x) - g x|) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (2 : ℝ) > 0)]
      apply div_le_div_of_nonneg_right
      · exact abs_add_le (g_R x - g x) (g_R (-x) - g x)
      · norm_num
    calc |((g_R x - g x) + (g_R (-x) - g x)) / 2|
        ≤ (|g_R x - g x| + |g_R (-x) - g x|) / 2 := h4
      _ < (ε/3 + ε/3) / 2 := by linarith [b2_x, b2_neg]
      _ = ε / 3 := by ring

  /-
  STEP 4 (collect errors): PROPER triangle inequality chain

  With normalized atoms and g_R^sym:
    |h - f| ≤ |h - g_R^sym| + |g_R^sym - g| + |g - f|
           < ε/3 + ε/3 + ε/3 = ε

  This chain is now COMPLETE: h → g_R^sym → g → f
  -/

  -- Coefficients are nonnegative (g ≥ 0 since Ψ ≥ 0 and H_t ≥ 0)
  have hc_nonneg : ∀ j ∈ Finset.range N, 0 ≤ c j := by
    intro j _
    simp only [c]
    apply mul_nonneg
    · -- g(τ j) ≥ 0 because it's convolution of nonneg functions
      simp only [g, real_convolution]
      apply integral_nonneg
      intro y
      apply mul_nonneg
      · -- Ψ y ≥ 0: from extended nonnegativity
        exact hΨ_nonneg y
      · exact HeatKernel_nonneg t ht_pos (τ j - y)
    · exact hΔ_pos.le

  -- Sample points are in [-K, K]
  have hτ_mem : ∀ j ∈ Finset.range N, τ j ∈ Icc (-K) K := by
    intro j hj
    simp only [Finset.mem_range] at hj
    simp only [τ, Δ, mem_Icc]
    have hN_cast_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
    have hj_lt : (j : ℝ) < N := Nat.cast_lt.mpr hj
    constructor
    -- Lower bound: -K + (j + 1/2) * (2K/N) ≥ -K
    · have h1 : (0 : ℝ) ≤ (j : ℝ) + 1/2 := by positivity
      have h2 : 0 ≤ ((j : ℝ) + 1/2) * (2 * K / N) := by positivity
      linarith
    -- Upper bound: -K + (j + 1/2) * (2K/N) ≤ K
    · -- j < N implies j + 1/2 ≤ N - 1/2 (since j ≤ N-1 for j : ℕ)
      have hj_le : (j : ℝ) ≤ N - 1 := by
        have h := Nat.lt_iff_add_one_le.mp hj  -- j + 1 ≤ N
        have h2 : (j : ℝ) + 1 ≤ N := by
          calc (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by simp [Nat.cast_add]
            _ ≤ N := Nat.cast_le.mpr h
        linarith
      have h5 : (j : ℝ) + 1/2 ≤ N - 1/2 := by linarith
      -- (j + 1/2) * (2K/N) ≤ (N - 1/2) * (2K/N) = 2K - K/N ≤ 2K
      have h6 : ((j : ℝ) + 1/2) * (2 * K / N) ≤ (N - 1/2) * (2 * K / N) := by
        apply mul_le_mul_of_nonneg_right h5
        positivity
      have h7 : ((N : ℝ) - 1/2) * (2 * K / N) = 2 * K - K / N := by
        have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_cast_pos
        field_simp [hN_ne]
      have h8 : K / N > 0 := by positivity
      calc -K + ((j : ℝ) + 1/2) * (2 * K / N)
          ≤ -K + (N - 1/2) * (2 * K / N) := by linarith [h6]
        _ = -K + (2 * K - K / N) := by rw [h7]
        _ = K - K / N := by ring
        _ ≤ K := by linarith

  -- Check if we have positive sum
  by_cases h_sum_zero : ∑ j ∈ Finset.range N, c j = 0
  case pos =>
    -- Degenerate case: all coefficients sum to 0
    -- This means g ≈ 0 everywhere, hence Φ ≈ 0
    use fun _ => 0
    refine ⟨?_, ?_⟩
    · -- 0 in cone (degenerate)
      admit
    · intro x hx
      -- If sum of c_j = 0 and all c_j ≥ 0, then all c_j = 0
      admit

  case neg =>
    have h_sum_pos : ∑ j ∈ Finset.range N, c j > 0 := by
      rcases lt_or_eq_of_le (Finset.sum_nonneg hc_nonneg) with h | h
      · exact h
      · exact absurd h.symm h_sum_zero

    -- h is in AtomCone_K K
    have hh_cone : h ∈ AtomCone_K K := by
      -- Each c_j * Atom B t (τ j) is a nonneg combination of atoms
      sorry -- sum_atoms_in_cone application

    use h, hh_cone

    -- Final bound via PROPER triangle inequality chain
    -- With normalized atoms: h → g_R^sym → g → Φ
    intro x hx

    -- Get bounds from each step
    have b1 := step1_bound x hx      -- |g - Φ| < ε/3
    have b2 := sym_contractive x hx  -- |g_R^sym - g| < ε/3
    have b3 := step3_bound x hx      -- |h - g_R^sym| < ε/3

    -- Flip directions for proper chain
    have b1' : |Φ x - g x| < ε/3 := by rw [abs_sub_comm]; exact b1
    have b2' : |g x - g_R_sym x| < ε/3 := by rw [abs_sub_comm]; exact b2
    have b3' : |g_R_sym x - h x| < ε/3 := by rw [abs_sub_comm]; exact b3

    -- PROPER triangle inequality: Φ → g → g_R^sym → h
    calc |Φ x - h x|
        ≤ |Φ x - g x| + |g x - h x| := abs_sub_le (Φ x) (g x) (h x)
      _ ≤ |Φ x - g x| + (|g x - g_R_sym x| + |g_R_sym x - h x|) := by
          gcongr
          exact abs_sub_le (g x) (g_R_sym x) (h x)
      _ = |Φ x - g x| + |g x - g_R_sym x| + |g_R_sym x - h x| := by ring
      _ < ε/3 + ε/3 + ε/3 := by linarith [b1', b2', b3']
      _ = ε := by ring

#check A1_density_paper
#print axioms A1_density_paper

end
