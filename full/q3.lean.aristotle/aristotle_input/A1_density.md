# A1' Density Theorem

## Setup

Let K > 0 be a real number (the "compact parameter").

Define:
- W_K = {Φ : ℝ → ℝ | ContinuousOn Φ [-K,K] ∧ support Φ ⊆ [-K,K] ∧ even Φ ∧ Φ ≥ 0}
- AtomCone_K = conical hull of Fejér×heat atoms Φ_{B,t,τ} with τ ∈ [-K,K]
- Fejér kernel: Λ_B(x) = (1 - |x|/B)_+
- Heat kernel: ρ_t(x) = (4πt)^{-1/2} exp(-x²/(4t))
- Atom: Φ_{B,t,τ}(ξ) = Λ_B(ξ-τ)·ρ_t(ξ-τ) + Λ_B(ξ+τ)·ρ_t(ξ+τ)

## Theorem (A1' Density)

For all K > 0, the cone AtomCone_K is dense in W_K in the uniform norm.

Formally: ∀ K > 0, ∀ Φ ∈ W_K, ∀ ε > 0, ∃ g ∈ AtomCone_K, sup_{x ∈ [-K,K]} |Φ(x) - g(x)| < ε

## Proof Sketch

The proof has 4 steps:

**Step 1 (Mollification):**
Given f ∈ W_K, convolve with heat kernel ρ_t. Since ρ_t is a positive approximate identity:
- For small enough t > 0: sup_{|ξ| ≤ K} |(f * ρ_t)(ξ) - f(ξ)| < ε/3
- Heat convolution preserves nonnegativity and evenness

**Step 2 (Positive Riemann Sums):**
Approximate the mollified function g = f * ρ_t by positive Riemann sums:
- Choose uniform partition -K = τ_0 < τ_1 < ... < τ_N = K
- Define g_R(ξ) = Σ_j g(τ_j*) · ρ_t(ξ - τ_j*) · Δτ
- For small mesh Δ: sup_{|ξ| ≤ K} |g_R(ξ) - g(ξ)| < ε/3

**Step 3 (Fejér Truncation):**
Replace exact Gaussians with Fejér-truncated versions:
- For |ξ|, |τ| ≤ K: |Λ_B(ξ-τ) - 1| ≤ 2K/B
- Choose B ≥ 6K/ε to get error < ε/3
- Define h using Φ_{B,t,τ_j*} atoms

**Step 4 (Collect Errors):**
By triangle inequality:
- |h(ξ) - f(ξ)| ≤ |h - g_R^sym| + |g_R - g| + |g - f| < ε
- h is in AtomCone_K by construction

## Key Lemmas Needed

1. Heat kernel is positive approximate identity: ∀ ε > 0, ∃ t > 0, ‖f * ρ_t - f‖_∞ < ε
2. Riemann sum convergence for continuous functions on compacts
3. Fejér kernel approximates 1 on compacts: |Λ_B(x) - 1| ≤ |x|/B for |x| ≤ B
4. Triangle inequality for uniform norm

## Lean Formalization Notes

The theorem signature in Lean 4 with Mathlib:

```lean
theorem A1_density_WK (K : ℝ) (hK : K > 0) :
    ∀ Φ ∈ W_K K, ∀ ε > 0,
      ∃ g ∈ AtomCone_K K,
        sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε
```

The proof requires:
- MeasureTheory.convolution for heat kernel convolution
- Topology.MetricSpace for uniform approximation
- Analysis.SpecialFunctions.Gaussian for ρ_t properties
