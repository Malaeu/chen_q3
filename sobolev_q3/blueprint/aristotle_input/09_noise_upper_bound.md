# Noise Upper Bound for Twin Prime Conjecture

## Goal
Prove that the integral over Minor Arcs is sublinear in X.

## Setup
Let X be a large positive real number. Let Q = X^{1/2}.
Define the Minor Arcs m as the complement of Major Arcs in [0, 1]:
m = [0, 1] \ M

Define the exponential sum:
S(α) = Σ_{p ≤ X} Λ(p) · e(pα)

where Λ is the von Mangoldt function and e(x) = exp(2πix).

## Target Theorem
```lean
theorem noise_upper_bound (X : ℝ) (hX : X > 0) (ε : ℝ) (hε : ε > 0) :
  |∫ α in MinorArcs X, Ψ α * |S X α|^2| ≤ ε * X
```

for any ε > 0 when X is sufficiently large.

## Proof Sketch

1. **Vinogradov Estimate**: On minor arcs, the exponential sum is bounded:
   For α ∈ m, |S(α)| ≤ X^{1-δ} for some δ > 0

   This is Vinogradov's fundamental lemma: exponential sums are small away from rationals.

2. **Parseval Identity**: By Parseval's theorem:
   ∫₀¹ |S(α)|² dα = Σ_{p ≤ X} Λ(p)² ≈ X log X

3. **Minor Arc Bound**: Using Hölder's inequality:
   |∫_m Ψ · |S|²| ≤ ||Ψ||_∞ · ∫_m |S|²
                   ≤ sup_{α ∈ m} |S(α)| · ∫_m |S|
                   ≤ X^{1-δ} · X^{1/2} · (log X)^C
                   = o(X)

4. **Sublinearity**: For any ε > 0, when X is large enough:
   |∫_m Ψ · |S|²| ≤ X^{1-δ/2} ≤ ε · X

## Key Lemmas Needed
- Vinogradov's estimate: sup_{α ∈ m} |S(α)| ≤ X / (log X)^A
- Parseval bound: ∫₀¹ |S(α)|² dα ≤ C · X log X
- Measure of minor arcs: |m| ≤ 1

## Context
The key insight: Minor arcs have small exponential sums because α is far from all rationals a/q with small q. This is where the "noise" in the circle method gets killed.
