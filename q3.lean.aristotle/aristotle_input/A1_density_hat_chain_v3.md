# A1 Density via Hat-Chain (Stub Approach)

## What to Prove

Fill the two `sorry` in the formal_input_context file:

1. `W_K_boundary_vanish`: Functions in W_K vanish at ±K
2. `A1_density_WK_hat`: AtomCone_K is dense in W_K

## Proof Sketch

### W_K_boundary_vanish:

The key insight: `support Φ ⊆ [-K, K]` means Φ = 0 outside this interval.

1. Use `W_K_support` to get `support Φ ⊆ Icc (-K) K`
2. For any x < -K: x ∉ Icc (-K) K, so x ∉ support Φ, so Φ x = 0
3. Take sequence xₙ → (-K)⁻ with xₙ < -K. All have Φ(xₙ) = 0
4. Use `W_K_continuous` to get Continuous Φ
5. By continuity: Φ(-K) = lim Φ(xₙ) = 0
6. Same argument for K from the right (x > K)

### A1_density_WK_hat:

1. Given Φ ∈ W_K K, use W_K_* axioms to extract properties
2. Apply `W_K_boundary_vanish` to get Φ(-K) = 0 ∧ Φ(K) = 0
3. Apply `hat_interpolation_approx` — all hypotheses satisfied!
4. Get n, τ, δ with approximation bound
5. Define g := ∑ i, Φ (τ i) * FejerKernel δ (x - τ i)
6. Show g ∈ AtomCone_K using margin condition |τ i| + δ ≤ K
7. Return approximation bound

## Key Point

The `hat_interpolation_approx` axiom is ALREADY provided in the stub file.
Just apply it after establishing boundary condition!
