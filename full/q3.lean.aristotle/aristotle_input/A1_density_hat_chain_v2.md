# A1 Density via Hat-Chain (Power Combo Version)

## What to Prove

Two theorems:

1. **W_K_boundary_vanish**: Functions in W_K vanish at ±K
2. **A1_density_WK_hat**: AtomCone_K is dense in W_K

## Formal Statements

```lean
lemma W_K_boundary_vanish (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ) (hΦ : Φ ∈ W_K K) :
    Φ (-K) = 0 ∧ Φ K = 0 := by sorry

theorem A1_density_WK_hat (K : ℝ) (hK : K > 0) :
    ∀ Φ ∈ W_K K, ∀ ε > 0, ∃ g ∈ AtomCone_K K,
      sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε := by sorry
```

## Proof Sketch (CRITICAL)

### W_K_boundary_vanish:
1. W_K requires: `Continuous Φ` and `support Φ ⊆ [-K, K]`
2. Support ⊆ [-K, K] means Φ = 0 outside this interval
3. For x < -K: x ∉ support, so Φ x = 0
4. Take sequence xₙ → (-K)⁻, all have Φ(xₙ) = 0
5. By global continuity: Φ(-K) = lim Φ(xₙ) = 0
6. Same argument for K from the right

### A1_density_WK_hat:
1. Extract from Φ ∈ W_K: continuity, support, evenness, nonnegativity
2. Apply W_K_boundary_vanish → get Φ(-K) = 0 ∧ Φ(K) = 0
3. Apply `HatInterp.hat_interpolation_approx` with this boundary condition!
4. Get: n, τ grid, δ width, and approximation bound
5. Define g := ∑ᵢ Φ(τᵢ) * FejerKernel δ (x - τᵢ)
6. Show g ∈ AtomCone_K using margin condition |τᵢ| + δ ≤ K
7. Return the approximation bound

## Key Insight

The `HatInterp.hat_interpolation_approx` in HatInterpolation.lean REQUIRES boundary condition `f(-K) = 0 ∧ f(K) = 0`. This is why W_K_boundary_vanish must be proven first!

## Context Files Provided

- **formal_input_context**: A1_density.lean — contains W_K, AtomCone_K, FejerKernel definitions
- **context**: HatInterpolation.lean — contains PROVEN hat_interpolation_approx
- **context**: Axioms.lean — project axioms

Use the existing `HatInterp.hat_interpolation_approx` theorem directly!
