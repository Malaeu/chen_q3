# D3-Lock Repair: Model vs Empirical Expectation

## Context

This is a CRITICAL repair from Formal Audit Document 25.
The original D3-lock had a logical flaw: using empirical expectation creates a tautology.

## The Problem

**WRONG (empirical expectation):**
$$\mathbb{E}_{\text{emp}}[f] = \frac{1}{|I_K|} \sum_{n \in I_K} f(\alpha_n)$$

This makes $\sum_{n \in I_K} (f(\alpha_n) - \mathbb{E}_{\text{emp}}[f]) = 0$ IDENTICALLY.
No information content!

## The Repair

**CORRECT (model expectation):**
$$\mathbb{E}_{\text{model},A}[f] = \int_{-K}^{K} f(x) \cdot \rho_A(x) \, dx$$

where $\rho_A(x)$ is the DETERMINISTIC density from the archimedean symbol $P_A$.

Key insight: $\rho_A$ comes from the Toeplitz operator $T_M[P_A]$, NOT from prime data!

## Setup

Let:
- $P_A : \mathbb{T} \to \mathbb{R}$ be the archimedean symbol (Fejér × heat kernel)
- $\rho_A(x)$ be the induced density on $[-K, K]$ via inverse Fourier transform
- $L_A(f) = \sum_{n \in I_K} w_n \cdot f(\alpha_n)$ be the prime functional

## Theorem (D3-Lock Repaired)

For $f \in H$ with $\|f\|_H \leq 1$:
$$|L_A(f) - \mathbb{E}_{\text{model},A}[f] \cdot \|v\|^2| \leq C(K) \cdot \delta_A$$

where:
- $\delta_A \to 0$ as $A \to \infty$
- $C(K)$ depends only on the cutoff $K$
- $\|v\|^2 = \sum_{n \in I_K} w_n^2$ is the total prime weight

## Proof Sketch

**Step 1: Rewrite prime sum**

$$L_A(f) = \sum_{n \in I_K} w_n \cdot f(\alpha_n)$$

**Step 2: Model expectation from symbol**

From Toeplitz theory, the archimedean symbol $P_A$ induces:
$$\mathbb{E}_{\text{model},A}[f] = \langle f, \mu_A \rangle_H$$

where $\mu_A \in H$ is the Riesz representer of the model functional.

**Step 3: Apply spectral gap**

By Q3 spectral gap on $V_K$:
$$|L_A(f) - \mathbb{E}_{\text{model},A}[f] \cdot \|v\|^2| \leq \|H|_{V_K}\| \cdot \|f\|_H \cdot \|v\|$$

**Step 4: Error bound**

Since $\|H|_{V_K}\|$ is controlled by the Q3 gap:
$$\text{error} \leq C(K) \cdot \delta_A$$

where $\delta_A = o(1/(\log A)^2)$.

## Key Distinction

| Aspect | Empirical (WRONG) | Model (CORRECT) |
|--------|-------------------|-----------------|
| Definition | Average over primes | Integral over density |
| Data source | Prime locations | Toeplitz symbol |
| Sum property | $\sum(f - \mathbb{E}) = 0$ | $\sum(f - \mathbb{E}) \neq 0$ in general |
| Information | None (tautology) | Real constraint |

## Expected Lean Formalization

```lean
/-- Model expectation from archimedean density -/
noncomputable def E_model (A K : ℝ) (f : ℝ → ℂ) (rho_A : ℝ → ℝ) : ℂ :=
  ∫ x in Icc (-K) K, f x * rho_A x

/-- D3-Lock Repaired: prime functional approximated by model -/
theorem D3_lock_repaired (A K : ℝ) (f : H) (hf : ‖f‖ ≤ 1)
    (rho_A : ℝ → ℝ) (delta_A : ℝ) (hdelta : delta_A > 0) :
  |L_A f - E_model A K f rho_A * v_norm_sq| ≤ C_K * delta_A := by
  sorry
```

## Dependencies

- Q3 spectral gap (axiom from paper)
- Toeplitz operator theory
- Riesz representation in RKHS
