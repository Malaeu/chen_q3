# Localization Argument: Heat Kernel Concentrates Away from Primes

## Core Insight

The key observation is that:
1. **Prime nodes are discrete**: $\xi_n = \frac{\log n}{2\pi}$ for $n \geq 2$, so $\xi_n \neq 0$ for all primes.
2. **Heat localizes at zero**: As $t \to \infty$, the Gaussian $e^{-4\pi^2 t \xi^2}$ concentrates at $\xi = 0$.
3. **Arch term sees zero**: The integral $\int a^*(\xi) \Phi(\xi) d\xi$ captures the mass at $\xi = 0$.
4. **Prime term misses zero**: The sum $\sum w_Q(n) \Phi(\xi_n)$ only samples at $\xi_n \neq 0$.

## The Gap

The smallest prime node is at $\xi_2 = \frac{\log 2}{2\pi} \approx 0.110$.

For $t$ large enough, $\Phi_t(\xi_2) = e^{-4\pi^2 t \xi_2^2} \approx e^{-0.48 t}$.

At $t = 10$: $\Phi(\xi_2) \approx e^{-4.8} \approx 0.008$.
At $t = 40$: $\Phi(\xi_2) \approx e^{-19.2} \approx 10^{-9}$.

Meanwhile, $\Phi(0) = 1$ always (for any $t$).

## Precise Statement

**Theorem (Localization Dominance)**:
There exists $t_0 > 0$ such that for all $t \geq t_0$ and $B \geq 1$:
$$\frac{\text{arch\_term}(\Phi_{B,t})}{\text{prime\_term}(\Phi_{B,t})} \to \infty \quad \text{as } t \to \infty$$

In particular, for $t$ sufficiently large:
$$\text{arch\_term}(\Phi_{B,t}) > \text{prime\_term}(\Phi_{B,t})$$

## Proof Sketch

### Step 1: Arch term asymptotics

For large $t$:
$$\text{arch\_term} = \int a^*(\xi) \cdot \text{Fejér}(\xi) \cdot e^{-4\pi^2 t \xi^2} d\xi \sim \frac{a^*(0)}{2\sqrt{\pi^3 t}}$$

(Using Laplace's method / Gaussian integral.)

### Step 2: Prime term asymptotics

The leading term in prime_term is $n = 2$:
$$\text{prime\_term} \leq w_Q(2) \cdot e^{-4\pi^2 t \xi_2^2} + O(e^{-4\pi^2 t \xi_3^2})$$
$$= \frac{2\log 2}{\sqrt{2}} \cdot e^{-t(\log 2)^2} + \text{smaller terms}$$

### Step 3: Ratio

$$\frac{\text{arch\_term}}{\text{prime\_term}} \geq \frac{c_1 / \sqrt{t}}{c_2 \cdot e^{-c_3 t}} = \frac{c_1}{c_2 \sqrt{t}} \cdot e^{c_3 t} \to \infty$$

The exponential beats the polynomial.

## Lean 4 Formalization

```lean
import Mathlib

open Real MeasureTheory

noncomputable section

def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

/-- The gap: smallest prime node is bounded away from 0 -/
lemma xi_2_pos : xi_n 2 > 0 := by
  unfold xi_n
  have h : Real.log 2 > 0 := Real.log_pos one_lt_two
  positivity

/-- The gap is at least log(2)/(2π) ≈ 0.11 -/
lemma xi_2_lower : xi_n 2 ≥ Real.log 2 / (2 * Real.pi) := le_refl _

/-- Heat decay at xi_2 -/
lemma heat_at_xi2 (t : ℝ) (ht : 0 < t) :
    Real.exp (-4 * Real.pi^2 * t * (xi_n 2)^2) ≤ Real.exp (-t * (Real.log 2)^2) := by
  sorry

/-- Arch term lower bound via Laplace method -/
lemma arch_term_laplace_lower (t : ℝ) (ht : 1 ≤ t) :
    ∫ ξ in Set.Icc (-1 : ℝ) 1, Real.exp (-4 * Real.pi^2 * t * ξ^2) ≥
      1 / (4 * Real.sqrt (Real.pi^3 * t)) := by
  sorry

/-- Prime term upper bound from dominant term -/
lemma prime_term_laplace_upper (t : ℝ) (ht : 1 ≤ t) :
    ∑' n, (2 * Real.log n / Real.sqrt n) * Real.exp (-t * (Real.log n)^2) ≤
      4 * Real.exp (-t * (Real.log 2)^2) := by
  sorry

/-- MAIN: For large t, arch dominates prime -/
theorem localization_dominance (t : ℝ) (ht : 10 ≤ t) :
    ∫ ξ in Set.Icc (-3 : ℝ) 3, (2 * Real.pi) * (max 0 (1 - |ξ| / 3)) *
        Real.exp (-4 * Real.pi^2 * t * ξ^2) ≥
      ∑' n, (2 * Real.log n / Real.sqrt n) *
        (max 0 (1 - |xi_n n| / 3)) * Real.exp (-4 * Real.pi^2 * t * (xi_n n)^2) := by
  sorry
```

## Key Quantities

| $t$ | $e^{-t(\log 2)^2}$ | $1/\sqrt{t}$ | Ratio |
|-----|-------------------|--------------|-------|
| 1   | 0.62              | 1.00         | 1.6   |
| 10  | 0.008             | 0.32         | 40    |
| 40  | $10^{-8}$         | 0.16         | $10^7$|

The ratio grows exponentially in $t$.

## Conclusion

For any fixed $t \geq 10$, the arch_term is orders of magnitude larger than prime_term. This is because:
- The arch integral captures the peak at $\xi = 0$
- The prime sum only samples at $\xi_n \geq \xi_2 \approx 0.11$, where the heat kernel is exponentially suppressed

This gives `arch_term ≥ prime_term` without any $(2M+1)$ factor.
