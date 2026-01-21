# Task 3: Fourier-Minor Arc Equivalence

## Context

This lemma bridges RKHS/Fourier minor decomposition with circle method minor arcs.
It shows that high Fourier frequencies correspond to minor arc contributions.

## Setup

**Exponential sum:**
$$S_X(\alpha) = \sum_{n \leq X} \Lambda(n) e(n\alpha)$$

**Circle-minor arcs:**
$$\mathfrak{m} = \left\{\alpha \in [0,1] : \left|\alpha - \frac{a}{q}\right| > \frac{1}{qQ} \text{ for all } q \leq Q, \gcd(a,q)=1\right\}$$

**Fourier-minor (high frequencies):**
$$I_{\min} = \{k \in \mathbb{Z} : |k| \geq K_0\}$$

## Theorem (Fourier-Minor Equivalence)

For $K_0 = X^{1/3}$ and $Q = X^{1/3}$:

$$\int_{\mathfrak{m}} |S_X(\alpha)|^2 d\alpha \leq C \cdot \sum_{|k| \geq K_0} |\hat{S}_X(k)|^2 + O(X^{1+\varepsilon})$$

where $\hat{S}_X(k)$ is the $k$-th Fourier coefficient of $S_X$.

## Proof Sketch

**Step 1: Parseval on full circle**

$$\int_0^1 |S_X(\alpha)|^2 d\alpha = \sum_{k \in \mathbb{Z}} |\hat{S}_X(k)|^2 = \sum_{n \leq X} \Lambda(n)^2$$

**Step 2: Major arc structure**

On major arcs around $a/q$, the sum $S_X(\alpha)$ is well-approximated by:
$$S_X(\alpha) \approx \frac{\mu(q)}{\phi(q)} \sum_{n \leq X} e(n\beta)$$
where $\alpha = a/q + \beta$.

This contributes mainly to low Fourier modes $|k| \lesssim q \leq Q$.

**Step 3: Minor arc = high frequency**

By exclusion, minor arcs carry the high frequency content:
$$\int_{\mathfrak{m}} |S_X(\alpha)|^2 d\alpha \approx \sum_{|k| \geq K_0} |\hat{S}_X(k)|^2$$

**Step 4: Indicator Fourier bound**

The indicator $\mathbf{1}_{\mathfrak{m}}$ has Fourier coefficients:
$$|\hat{\mathbf{1}}_{\mathfrak{m}}(n)| \leq C \cdot \min\left(1, \frac{Q}{|n|}\right)$$

This is because minor arcs are the complement of $O(Q^2)$ intervals of size $O(1/Q^2)$.

## Expected Lean Formalization

```lean
import Mathlib

open Real Complex MeasureTheory Finset

/-- Exponential function e(x) = exp(2πix) -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- Exponential sum S_X(α) -/
noncomputable def S (X : ℕ) (α : ℝ) : ℂ :=
  ∑ n in range X, (ArithmeticFunction.vonMangoldt n : ℂ) * e (n * α)

/-- Minor arcs definition -/
def minor_arcs (Q : ℝ) : Set ℝ :=
  {α ∈ Set.Icc 0 1 | ∀ q ≤ Q, ∀ a, Nat.Coprime a q → |α - a/q| > 1/(q*Q)}

/-- Fourier coefficient of S_X -/
noncomputable def S_hat (X : ℕ) (k : ℤ) : ℂ :=
  ∫ α in Set.Icc 0 1, S X α * e (-k * α)

/-- Minor arc integral bounded by high Fourier modes -/
theorem fourier_minor_equivalence (X : ℕ) (K₀ Q : ℝ)
    (hK : K₀ = X^(1/3 : ℝ)) (hQ : Q = X^(1/3 : ℝ)) :
  ∫ α in minor_arcs Q, Complex.normSq (S X α) ≤
    C * ∑' k : {k : ℤ // |k| ≥ K₀}, Complex.normSq (S_hat X k) + X^(1 + ε) := by
  sorry

/-- Minor arc indicator Fourier decay -/
theorem minor_indicator_fourier_decay (Q : ℝ) (n : ℤ) (hn : n ≠ 0) :
  ‖∫ α in minor_arcs Q, e (n * α)‖ ≤ C * min 1 (Q / |n|) := by
  sorry
```

## Dependencies

- Parseval identity (already proved in LARGE_SIEVE_v2)
- Major arc approximation
- Vinogradov mean value theorem (optional, for sharper bounds)
