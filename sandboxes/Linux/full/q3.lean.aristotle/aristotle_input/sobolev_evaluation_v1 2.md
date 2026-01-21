# Sobolev Embedding: Bounded Evaluation Functionals

## Goal
In Sobolev space $H^s$ with $s > 1/2$, point evaluation is a bounded linear functional:
$$|f(\xi)| \leq C_s \cdot \|f\|_{H^s}$$

with $C_s$ **independent of the discretization parameter**.

## Context
The $(2M+1)$ factor problem arises because in $L^2(\mathbb{T}_N)$:
- Evaluation functional has norm $\sqrt{N}$ where $N = 2M+1$
- This gives $|f(\xi)| \leq \sqrt{N} \|f\|_{L^2}$

In Sobolev $H^s$ with $s > 1/2$:
- Evaluation functional has norm $O(1)$
- This gives $|f(\xi)| \leq C_s \|f\|_{H^s}$ with $C_s$ independent of $N$

## Sobolev Space Background

### Definition
$$H^s(\mathbb{R}) = \{f : \|f\|_{H^s}^2 = \int_{\mathbb{R}} |\hat{f}(k)|^2 (1 + |k|^2)^s \, dk < \infty\}$$

### Sobolev Embedding Theorem
For $s > 1/2$:
- $H^s(\mathbb{R}) \hookrightarrow C^0_b(\mathbb{R})$ (continuous bounded functions)
- The embedding constant is $C_s \sim 1/\sqrt{2s - 1}$

### Point Evaluation
For $f \in H^s$ with $s > 1/2$:
$$|f(\xi)| = \left| \int e^{2\pi i k \xi} \hat{f}(k) \, dk \right| \leq \int |\hat{f}(k)| \, dk$$

By Cauchy-Schwarz:
$$\int |\hat{f}(k)| dk = \int |\hat{f}(k)| (1+|k|^2)^{s/2} \cdot (1+|k|^2)^{-s/2} dk$$
$$\leq \|f\|_{H^s} \cdot \left( \int (1+|k|^2)^{-s} dk \right)^{1/2}$$

The second integral converges iff $s > 1/2$.

## Lean 4 Formalization

```lean
import Mathlib

open Real MeasureTheory Set BigOperators FourierTransform

noncomputable section

/-! ## Sobolev Norm -/

/-- Sobolev weight -/
def sobolev_weight (s k : ℝ) : ℝ := (1 + k^2) ^ s

/-- Sobolev weight is positive -/
lemma sobolev_weight_pos (s k : ℝ) : 0 < sobolev_weight s k := by
  unfold sobolev_weight
  positivity

/-- Sobolev norm squared (for f with Fourier transform f_hat) -/
def sobolev_norm_sq (s : ℝ) (f_hat : ℝ → ℂ) : ℝ :=
  ∫ k, ‖f_hat k‖^2 * sobolev_weight s k

/-! ## Key Integral -/

/-- The integral ∫ (1+k²)^{-s} dk converges for s > 1/2 -/
lemma sobolev_integral_converges (s : ℝ) (hs : s > 1/2) :
    ∫ k : ℝ, (1 + k^2)^(-s) < ⊤ := by
  sorry

/-- Explicit bound: ∫ (1+k²)^{-s} dk ≤ π/√(s - 1/2) for s > 1/2 -/
lemma sobolev_integral_bound (s : ℝ) (hs : s > 1/2) :
    ∫ k : ℝ, (1 + k^2)^(-s) ≤ Real.pi / Real.sqrt (s - 1/2) := by
  sorry

/-! ## Sobolev Embedding -/

/-- Sobolev embedding constant -/
def C_sobolev (s : ℝ) : ℝ := Real.sqrt (Real.pi / (s - 1/2))

/-- Embedding constant is finite for s > 1/2 -/
lemma C_sobolev_finite (s : ℝ) (hs : s > 1/2) : C_sobolev s < ⊤ := by
  unfold C_sobolev
  have h : s - 1/2 > 0 := by linarith
  positivity

/-- MAIN: Sobolev embedding theorem -/
theorem sobolev_embedding (s : ℝ) (hs : s > 1/2) (f_hat : ℝ → ℂ)
    (hf : sobolev_norm_sq s f_hat < ⊤) (ξ : ℝ) :
    ‖∫ k, Complex.exp (2 * Real.pi * Complex.I * k * ξ) * f_hat k‖ ≤
      C_sobolev s * Real.sqrt (sobolev_norm_sq s f_hat) := by
  sorry

/-! ## Application to Prime Sum -/

/-- Prime node -/
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

/-- Von Mangoldt weight -/
def w_Q (n : ℕ) : ℝ := 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- Evaluation at prime nodes is bounded -/
theorem prime_evaluation_bounded (s : ℝ) (hs : s > 1/2) (f_hat : ℝ → ℂ)
    (hf : sobolev_norm_sq s f_hat < ⊤) (n : ℕ) (hn : 2 ≤ n) :
    ‖∫ k, Complex.exp (2 * Real.pi * Complex.I * k * xi_n n) * f_hat k‖^2 ≤
      (C_sobolev s)^2 * sobolev_norm_sq s f_hat := by
  sorry

/-- Sum over prime nodes with weights -/
theorem prime_sum_sobolev_bound (s : ℝ) (hs : s > 1/2) (f_hat : ℝ → ℂ)
    (hf : sobolev_norm_sq s f_hat < ⊤) :
    ∑' n, w_Q n * ‖∫ k, Complex.exp (2 * Real.pi * Complex.I * k * xi_n n) * f_hat k‖^2 ≤
      (∑' n, w_Q n) * (C_sobolev s)^2 * sobolev_norm_sq s f_hat := by
  sorry

/-! ## Comparison with L² -/

/-- In L², evaluation has norm √N on N-dimensional space -/
lemma L2_evaluation_norm (N : ℕ) (hN : 0 < N) :
    ∃ v : Fin N → ℂ, ‖v‖ = 1 ∧ |∑ k, v k| = Real.sqrt N := by
  sorry

/-- In H^s (s > 1/2), evaluation has norm C_s independent of discretization -/
lemma Hs_evaluation_norm (s : ℝ) (hs : s > 1/2) :
    ∀ N : ℕ, ∀ (f : ℝ → ℂ) (hf : sobolev_norm_sq s (fun k => f k) < ⊤),
      |f 0| ≤ C_sobolev s * Real.sqrt (sobolev_norm_sq s (fun k => f k)) := by
  sorry
```

## Proof Strategy

### Step 1: Integral Convergence
Show $\int (1+k^2)^{-s} dk < \infty$ for $s > 1/2$.

Compute directly:
$$\int_{-\infty}^{\infty} (1+k^2)^{-s} dk = \frac{\sqrt{\pi} \cdot \Gamma(s - 1/2)}{\Gamma(s)}$$

For $s$ slightly above $1/2$: $\sim \pi / \sqrt{s - 1/2}$.

### Step 2: Cauchy-Schwarz Application
For $f$ with Fourier transform $\hat{f}$:
$$|f(\xi)| = \left| \int e^{2\pi i k\xi} \hat{f}(k) dk \right|$$

Write $\hat{f}(k) = \hat{f}(k) (1+k^2)^{s/2} \cdot (1+k^2)^{-s/2}$:
$$\leq \left( \int |\hat{f}(k)|^2 (1+k^2)^s dk \right)^{1/2} \cdot \left( \int (1+k^2)^{-s} dk \right)^{1/2}$$
$$= \|f\|_{H^s} \cdot C_s$$

### Step 3: No N-dependence
The bound $|f(\xi)| \leq C_s \|f\|_{H^s}$ has **no dependence on discretization**.

Compare to $L^2(\mathbb{T}_N)$ where $|f(\xi)| \leq \sqrt{N} \|f\|_{L^2}$.

### Step 4: Application
For the prime sum:
$$\sum_n w_Q(n) |f(\xi_n)|^2 \leq C_s^2 \cdot \|f\|_{H^s}^2 \cdot \sum_n w_Q(n)$$

The factor $\sum w_Q(n)$ is bounded (weight_sum_bound theorem).

## Key Point: Where Does (2M+1) Go?

In $L^2(\mathbb{T}_N)$:
- Basis: $\{e^{2\pi i k \theta}\}_{k=-M}^{M}$
- Evaluation: $f(\xi) = \sum_k c_k e^{2\pi i k \xi}$
- Norm: $|f(\xi)| \leq \sqrt{\sum |c_k|^2} \cdot \sqrt{2M+1} = \|f\| \cdot \sqrt{N}$

In $H^s$ (continuous parameter):
- "Basis": Fourier integral
- Evaluation: $f(\xi) = \int \hat{f}(k) e^{2\pi i k \xi} dk$
- Norm: $|f(\xi)| \leq \|f\|_{H^s} \cdot C_s$

The $(2M+1)$ factor is an **artifact of discrete L² geometry**, not a fundamental constraint.

## Compatibility with Heat Kernel

Our test function $\Phi(ξ) = \text{Fejér} \times e^{-4\pi^2 t \xi^2}$ is in $H^s$ for any $s$:
- Gaussian has Fourier transform that decays like $e^{-c k^2}$
- This beats any polynomial weight $(1+k^2)^s$

So the Sobolev approach is compatible with our heat kernel choice.

## Trade-offs

| Approach | Pro | Con |
|----------|-----|-----|
| L² discrete | Standard Toeplitz theory | (2M+1) factor |
| H^s continuous | No N-dependence | Reformulate Toeplitz |

## Conclusion

Switching to Sobolev geometry eliminates the $(2M+1)$ factor at the cost of reformulating the Rayleigh quotient. The evaluation bound becomes $O(1)$ instead of $O(\sqrt{N})$.
