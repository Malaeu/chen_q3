# Relationship between a_star and P_A via periodization

## Goal
Understand and formalize the relationship between:
- a_star(ξ) = 2π·a(ξ) — the unwindowed archimedean kernel
- P_A(θ) = 2π·Σₘ g(θ+m) — the periodized windowed symbol

## Definitions
```lean
-- Archimedean kernel (unwindowed)
def a (ξ : ℝ) : ℝ := Real.log Real.pi - (digamma (1/4 + Complex.I * Real.pi * ξ)).re
def a_star (ξ : ℝ) : ℝ := 2 * Real.pi * a ξ

-- Window function (Fejér × heat)
def w (B t ξ : ℝ) : ℝ := max 0 (1 - |ξ|/B) * Real.exp(-4*π²*t*ξ²)

-- Windowed kernel
def g (B t ξ : ℝ) : ℝ := a ξ * w B t ξ

-- Periodized symbol
def P_A (B t θ : ℝ) : ℝ := 2 * Real.pi * ∑' (m : ℤ), g B t (θ + m)
```

## Key insight
P_A is NOT just a_star! It's a periodization with windowing:

$$P_A(B,t,\theta) = 2\pi \sum_{m \in \mathbb{Z}} a(\theta+m) \cdot w_{B,t}(\theta+m)$$

When B is small and t is small, the window localizes around θ, so:
- For |m| large, w(θ+m) ≈ 0 (cutoff by Fejér)
- Main contribution from m = 0 if θ ∈ [-1/2, 1/2]

## Question to answer
Is there a theorem of the form:

```lean
theorem P_A_ge_a_star_localized (B t θ : ℝ) (hθ : θ ∈ Set.Icc (-1/2) (1/2))
    (hB : B ≥ B_min) (ht : t = t_sym) :
    P_A B t θ ≥ a_star θ * (some_factor)
```

Or conversely, can we bound a_star in terms of P_A?

## What we know
- P_A B_min t_sym θ ≥ c_star = 11/10 (PROVEN in A3_FLOOR)
- a_star is the "main term" when window = 1

## Prove one of:
1. a_star(θ) ≤ P_A(B,t,θ) + error_term
2. P_A(B,t,θ) ≤ a_star(θ) under certain conditions
3. Rayleigh(Toeplitz(a_star)) relates to Rayleigh(Toeplitz(P_A))
