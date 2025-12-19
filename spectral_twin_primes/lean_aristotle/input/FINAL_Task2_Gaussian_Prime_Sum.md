# Task 2: Gaussian-Weighted Prime Sum

## Context

This lemma bounds sums over primes with Gaussian weights.
Needed for Task 1 (Gaussian Minor Suppression).

## Setup

- $\xi_p = \frac{\log p}{2\pi}$ — spectral coordinate of prime $p$
- $D > 0$ — threshold for minor region
- $t > 0$ — heat kernel parameter

## Theorem (Gaussian Prime Sum)

$$\sum_{\substack{p \leq A \\ \xi_p \geq D}} e^{-\xi_p^2/(4t)} \leq C \cdot \frac{A}{\log A} \cdot e^{-D^2/(4t)} \cdot \frac{D}{\sqrt{t}}$$

## Proof Sketch

**Step 1: Change of variables**

Let $\xi = \frac{\log x}{2\pi}$, so $x = e^{2\pi\xi}$ and $dx = 2\pi e^{2\pi\xi} d\xi$.

The condition $\xi_p \geq D$ means $p \geq e^{2\pi D}$.

**Step 2: Prime counting via PNT**

By PNT: $\pi(x) \sim \frac{x}{\log x}$

For primes in range $[e^{2\pi D}, A]$:
$$\#\{p : D \leq \xi_p \leq \xi_A\} \sim \frac{A}{\log A} - \frac{e^{2\pi D}}{2\pi D}$$

**Step 3: Integral comparison**

$$\sum_{\substack{p \leq A \\ \xi_p \geq D}} e^{-\xi_p^2/(4t)} \approx \int_D^{\xi_A} e^{-\xi^2/(4t)} \cdot \frac{d\pi(e^{2\pi\xi})}{d\xi} d\xi$$

Using $\frac{d\pi(x)}{dx} \approx \frac{1}{\log x}$:
$$\approx \int_D^{\xi_A} e^{-\xi^2/(4t)} \cdot \frac{2\pi e^{2\pi\xi}}{2\pi\xi} d\xi$$

**Step 4: Gaussian integral bound**

$$\int_D^{\infty} e^{-\xi^2/(4t)} d\xi = \sqrt{\pi t} \cdot \text{erfc}\left(\frac{D}{2\sqrt{t}}\right)$$

For large $D/\sqrt{t}$:
$$\text{erfc}(x) \leq \frac{e^{-x^2}}{x\sqrt{\pi}}$$

So:
$$\int_D^{\infty} e^{-\xi^2/(4t)} d\xi \leq \frac{\sqrt{t}}{D} \cdot e^{-D^2/(4t)}$$

**Step 5: Combine**

$$\sum_{\substack{p \leq A \\ \xi_p \geq D}} e^{-\xi_p^2/(4t)} \leq C \cdot \frac{A}{\log A} \cdot \frac{\sqrt{t}}{D} \cdot e^{-D^2/(4t)}$$

Actually: $\frac{D}{\sqrt{t}} \cdot e^{-D^2/(4t)}$ comes from the tail bound.

## Expected Lean Formalization

```lean
import Mathlib

open Real MeasureTheory Finset Nat ArithmeticFunction

/-- Spectral coordinate -/
noncomputable def xi (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

/-- Gaussian weight on minor primes -/
theorem gaussian_prime_sum (A D t : ℝ) (hA : 1 < A) (hD : 0 < D) (ht : 0 < t) :
  ∑ p in (range ⌊A⌋₊).filter (fun p => p.Prime ∧ xi p ≥ D),
    Real.exp (-xi p ^ 2 / (4 * t)) ≤
      C * (A / Real.log A) * Real.exp (-D^2 / (4 * t)) * (D / Real.sqrt t) := by
  sorry

/-- Asymptotic version using PNT -/
theorem gaussian_prime_sum_asymptotic (D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
  ∃ C > 0, ∀ᶠ A in Filter.atTop,
    ∑ p in (range ⌊A⌋₊).filter (fun p => p.Prime ∧ xi p ≥ D),
      Real.exp (-xi p ^ 2 / (4 * t)) ≤
        C * (A / Real.log A) * Real.exp (-D^2 / (4 * t)) := by
  sorry
```

## Dependencies

- Prime Number Theorem: π(x) ~ x/log x
- Complementary error function bounds
- Integration by parts / Abel summation
