# Prove a_star ≥ c_star directly

## Goal
Prove that the archimedean kernel a*(ξ) = 2π·a(ξ) is bounded below by c_star = 11/10 for all ξ ∈ ℝ.

## Definition
```lean
def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * ξ)).re
def a_star (ξ : ℝ) : ℝ := 2 * Real.pi * a ξ
```

Mathematically:
$$a^*(\xi) = 2\pi \left( \log\pi - \mathrm{Re}\,\psi\left(\tfrac14 + i\pi\xi\right) \right)$$

## What to prove
```lean
theorem a_star_ge_c_star : ∀ ξ : ℝ, a_star ξ ≥ c_star
  where c_star = 11/10
```

## Known facts
- a_star is continuous (axiom a_star_continuous)
- a_star is even: a_star(-ξ) = a_star(ξ) (axiom a_star_even)
- a_star(ξ) > 0 for all ξ (axiom a_star_pos)
- a(ξ) is decreasing for ξ > 0 (from A3_FLOOR: strictAntiOn_a)

## Strategy hints
1. Use evenness to reduce to ξ ≥ 0
2. Use monotonicity: a is decreasing for ξ > 0
3. Show a(0) is the maximum
4. Compute or bound inf_{ξ} a_star(ξ)

## Key question
What is inf_{ξ ∈ ℝ} a_star(ξ)? Is it ≥ 11/10?

If a_star is decreasing for ξ > 0 and even, then:
- inf a_star = lim_{ξ→∞} a_star(ξ)

What is this limit? The digamma function ψ(1/4 + iπξ) as ξ → ∞...
