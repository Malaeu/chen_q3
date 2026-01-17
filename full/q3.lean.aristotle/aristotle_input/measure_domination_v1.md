# Measure Domination: Prime Sum ≤ Arch Integral

## Goal
Prove that the discrete prime sum is bounded by the continuous archimedean integral:
$$\sum_{n \geq 2} w_Q(n) \cdot \Phi(\xi_n) \leq \int_{\mathbb{R}} a^*(\xi) \cdot \Phi(\xi) \, d\xi$$

## Context
- Test function: $\Phi(\xi) = \max(0, 1 - |\xi|/B) \cdot e^{-4\pi^2 t \xi^2}$ (Fejér × Gaussian)
- Prime nodes: $\xi_n = \frac{\log n}{2\pi}$ for $n \geq 2$
- Prime weights: $w_Q(n) = \frac{2 \Lambda(n)}{\sqrt{n}}$ where $\Lambda$ is von Mangoldt
- Archimedean density: $a^*(\xi) \geq 2\pi$ for $|\xi| \leq 1$

## Key Insight: Disjoint Neighborhoods
Prime nodes have gaps:
- $\xi_2 = \frac{\log 2}{2\pi} \approx 0.110$
- $\xi_3 = \frac{\log 3}{2\pi} \approx 0.175$
- Gap $\xi_3 - \xi_2 \approx 0.065$

For each prime node $\xi_n$, we can find a neighborhood of radius $\delta_n$ such that:
1. The neighborhoods are disjoint
2. The weight $w_Q(n) \cdot \Phi(\xi_n)$ is bounded by $\int_{\xi_n - \delta_n}^{\xi_n + \delta_n} a^*(\xi) \Phi(\xi) d\xi$

## Lean 4 Formalization

```lean
import Mathlib

open Real MeasureTheory Set BigOperators ArithmeticFunction

noncomputable section

/-! ## Definitions -/

/-- Prime node -/
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

/-- Von Mangoldt weight -/
def w_Q (n : ℕ) : ℝ := 2 * vonMangoldt n / Real.sqrt n

/-- Fejér-Heat test function -/
def Phi (B t ξ : ℝ) : ℝ := max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)

/-- Archimedean density lower bound -/
def a_star_lower : ℝ := 2 * Real.pi

/-! ## Gap between prime nodes -/

/-- Prime gap: distance between consecutive prime nodes -/
def prime_node_gap (n : ℕ) : ℝ := xi_n (n + 1) - xi_n n

/-- The gap is log((n+1)/n) / (2π) -/
lemma prime_node_gap_formula (n : ℕ) (hn : 1 ≤ n) :
    prime_node_gap n = Real.log ((n + 1) / n) / (2 * Real.pi) := by
  unfold prime_node_gap xi_n
  rw [Real.log_div (by positivity) (by positivity)]
  ring

/-- Gap is at least 1/(2πn) for n ≥ 2 -/
lemma prime_node_gap_lower (n : ℕ) (hn : 2 ≤ n) :
    prime_node_gap n ≥ 1 / (2 * Real.pi * n) := by
  sorry

/-! ## Main theorem -/

/-- Weight at node n is bounded by integral over neighborhood -/
lemma weight_bounded_by_neighborhood (n : ℕ) (hn : 2 ≤ n) (B t : ℝ) (hB : 1 ≤ B) (ht : 1 ≤ t) :
    w_Q n * Phi B t (xi_n n) ≤
      ∫ ξ in Icc (xi_n n - 1/(4*Real.pi*n)) (xi_n n + 1/(4*Real.pi*n)),
        a_star_lower * Phi B t ξ := by
  sorry

/-- Neighborhoods are disjoint -/
lemma neighborhoods_disjoint (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hmn : m < n) :
    Disjoint
      (Icc (xi_n m - 1/(4*Real.pi*m)) (xi_n m + 1/(4*Real.pi*m)))
      (Icc (xi_n n - 1/(4*Real.pi*n)) (xi_n n + 1/(4*Real.pi*n))) := by
  sorry

/-- MAIN: Prime sum ≤ Archimedean integral -/
theorem measure_domination (B t : ℝ) (hB : 3 ≤ B) (ht : 10 ≤ t) :
    ∑' n, w_Q n * Phi B t (xi_n n) ≤
      ∫ ξ in Icc (-B) B, a_star_lower * Phi B t ξ := by
  sorry
```

## Proof Strategy

### Step 1: Establish disjoint neighborhoods
For each prime node $\xi_n$, take neighborhood of radius $\delta_n = \frac{1}{4\pi n}$.
These are disjoint because the gap between consecutive nodes is $\geq \frac{1}{2\pi n}$.

### Step 2: Bound each term
Show that $w_Q(n) \cdot \Phi(\xi_n)$ is bounded by the integral of $a^* \cdot \Phi$ over the neighborhood.
This uses:
- $w_Q(n) = \frac{2\Lambda(n)}{\sqrt{n}} \leq \frac{2\log n}{\sqrt{n}}$
- $a^* \geq 2\pi$ on the neighborhood
- $\Phi$ is approximately constant on small neighborhoods

### Step 3: Sum over disjoint sets
Since neighborhoods are disjoint and all contained in $[-B, B]$:
$$\sum_n \int_{\text{nbhd}_n} a^* \cdot \Phi \leq \int_{[-B,B]} a^* \cdot \Phi$$

### Step 4: Conclude
Combining: $\sum_n w_Q(n) \Phi(\xi_n) \leq \int a^* \Phi$.

## Key Bounds Needed

| Quantity | Bound | Source |
|----------|-------|--------|
| $w_Q(n)$ | $\leq 2\log n / \sqrt{n}$ | Von Mangoldt |
| $a^*(\xi)$ | $\geq 2\pi$ for small $\xi$ | Archimedean density |
| $\delta_n$ | $= 1/(4\pi n)$ | Half the gap |
| $\int_{\delta_n} d\xi$ | $= 1/(2\pi n)$ | Interval length |
| $a^* \cdot 2\delta_n$ | $\geq 2$ | Product |

## Why This Works

The key is that $\frac{2\log n}{\sqrt{n}} \cdot 1 \ll 2\pi \cdot \frac{1}{2\pi n} \cdot \Phi(\xi_n)$?

Actually we need: $w_Q(n) \leq a^* \cdot 2\delta_n$ uniformly.

Check: $\frac{2\log n}{\sqrt{n}} \leq 2\pi \cdot \frac{1}{2\pi n} = \frac{1}{n}$?

This fails for small n! Need refined argument using $\Phi(\xi_n) \ll 1$ for large n.

## Refined Approach

Split into two regimes:
1. **Small n (n ≤ N₀)**: Use heat localization — $\Phi(\xi_n) \approx e^{-c \cdot t}$ is tiny
2. **Large n (n > N₀)**: Weight $w_Q(n) / n$ is small enough

The exponential decay from heat kernel saves the day.
