# Task 1: Gaussian Minor Suppression

## Context

This is the KEY lemma for Q3 → MAS → TPC chain.
It proves that functions supported on minor region have exponentially small contribution.

## Setup

We work in RKHS $H_t$ with heat kernel:
$$k_t(\xi, \eta) = e^{-(\xi - \eta)^2/(4t)}$$

Spectral coordinates: $\xi_n = \frac{\log n}{2\pi}$

Prime weights: $w(n) = \frac{\Lambda(n)}{\sqrt{n}}$

Minor region: $\{|\xi| \geq D\}$ for some buffer $D > 0$.

## Theorem (Gaussian Minor Suppression)

For any $f \in H_t$ with $\|f\|_{H_t} \leq 1$ and $\text{supp}(f) \subseteq \{|\xi| \geq D\}$:

$$\left|\sum_{n \leq A} w(n) \cdot f(\xi_n)\right| \leq C \cdot \frac{A}{\log A} \cdot e^{-D^2/(4t)}$$

## Proof Sketch

**Step 1: RKHS evaluation bound**

By reproducing property of RKHS:
$$|f(\xi)| = |\langle f, k_t(\cdot, \xi) \rangle_{H_t}| \leq \|f\|_{H_t} \cdot \|k_t(\cdot, \xi)\|_{H_t}$$

Since $\|k_t(\cdot, \xi)\|_{H_t} = \sqrt{k_t(\xi, \xi)} = 1$, we get $|f(\xi)| \leq 1$.

**Step 2: Kernel decay on minor**

For $\xi$ in minor region ($|\xi| \geq D$) and $\eta$ in major region ($|\eta| \leq D/2$):
$$|k_t(\xi, \eta)| \leq e^{-|\xi - \eta|^2/(4t)} \leq e^{-(D/2)^2/(4t)} = e^{-D^2/(16t)}$$

**Step 3: RKHS norm control**

Functions supported on minor have controlled RKHS norm:
$$\|f\|_{H_t}^2 = \iint f(\xi) \overline{f(\eta)} k_t^{-1}(\xi, \eta) d\xi d\eta$$

The inverse kernel $k_t^{-1}$ grows for separated points.

**Step 4: Prime sum bound**

$$\left|\sum_{n \leq A} w(n) f(\xi_n)\right| \leq \sum_{n \leq A} |w(n)| \cdot |f(\xi_n)|$$

For $\xi_n$ in minor region with $\|f\|_{H_t} \leq 1$:
$$|f(\xi_n)| \leq C \cdot e^{-\text{dist}(\xi_n, \text{major})^2/(4t)}$$

**Step 5: Summation over primes**

By PNT, $\sum_{p \leq A} 1 \sim A/\log A$.
Combined with Gaussian decay gives the result.

## Expected Lean Formalization

```lean
/-- Heat kernel -/
noncomputable def k_t (t ξ η : ℝ) : ℝ := Real.exp (-(ξ - η)^2 / (4 * t))

/-- Spectral coordinate -/
noncomputable def xi (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

/-- Prime weight -/
noncomputable def w (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- Minor region indicator -/
def in_minor (D ξ : ℝ) : Prop := |ξ| ≥ D

/-- Gaussian Minor Suppression Theorem -/
theorem gaussian_minor_suppression
    (t D A : ℝ) (ht : 0 < t) (hD : 0 < D) (hA : 1 < A)
    (f : ℝ → ℂ) (hf_norm : ‖f‖ ≤ 1)
    (hf_supp : ∀ ξ, |ξ| < D → f ξ = 0) :
  ‖∑ n in Finset.range ⌊A⌋₊, w n * f (xi n)‖ ≤
    C * (A / Real.log A) * Real.exp (-D^2 / (4 * t)) := by
  sorry
```

## Dependencies

- RKHS theory (reproducing property)
- Heat kernel properties
- Prime Number Theorem (π(A) ~ A/log A)
