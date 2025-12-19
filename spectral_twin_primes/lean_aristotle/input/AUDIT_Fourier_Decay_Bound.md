# Fourier Decay Bound for Archimedean Symbol

## Context

From Formal Audit Document 23: The Toeplitz symbol has controlled Fourier decay.
This is essential for buffer suppression.

## Setup

The archimedean symbol is:
$$P_A(\theta) = F_N(\theta) \cdot G_t(\theta)$$

where:
- $F_N(\theta) = \frac{1}{N} \left(\frac{\sin(N\theta/2)}{\sin(\theta/2)}\right)^2$ is Fejér kernel
- $G_t(\theta) = e^{-t(1 - \cos\theta)}$ is heat kernel on circle

Fourier expansion:
$$P_A(\theta) = \sum_{k \in \mathbb{Z}} A_k \cdot e^{ik\theta}$$

## Theorem (Fourier Decay)

For $|k| \geq 1$:
$$|A_k| \leq \frac{C_{\text{tail}}}{k^2}$$

where $C_{\text{tail}}$ depends on $N$ and $t$ but is bounded for fixed parameters.

## Proof

**Step 1: Fejér kernel coefficients**

The Fejér kernel has coefficients:
$$[\hat{F}_N]_k = \begin{cases} 1 - |k|/N & \text{if } |k| < N \\ 0 & \text{if } |k| \geq N \end{cases}$$

**Step 2: Heat kernel coefficients**

The heat kernel on circle has coefficients:
$$[\hat{G}_t]_k = e^{-t} \cdot I_k(t)$$

where $I_k(t)$ is modified Bessel function. For large $|k|$:
$$|I_k(t)| \leq \frac{(t/2)^{|k|}}{|k|!} \leq \frac{C}{|k|^{|k|/2}}$$

**Step 3: Convolution bound**

Since $P_A = F_N * G_t$ in Fourier space:
$$A_k = \sum_{j} [\hat{F}_N]_j \cdot [\hat{G}_t]_{k-j}$$

**Step 4: Decay estimate**

For $|k| \geq N$:
- Fejér contributes 0 for $|j| \geq N$
- Heat kernel contributes exponential decay for $|k-j|$ large

Result:
$$|A_k| \leq C_1 \cdot e^{-c_2 |k|} + C_3/|k|^2 \leq C_{\text{tail}}/k^2$$

## Explicit Buffer Formula

From Document 23, the explicit buffer width:
$$\Delta(K, \varepsilon) = 1 + \left\lceil \frac{2 C_{\text{tail}}}{\varepsilon} \right\rceil$$

This ensures:
$$\sum_{|k| \geq m + \Delta} |A_k| \leq \varepsilon$$

## Expected Lean Formalization

```lean
/-- Fourier coefficients of archimedean symbol -/
noncomputable def A_coeff (N : ℕ) (t : ℝ) (k : ℤ) : ℂ := sorry

/-- Tail constant -/
noncomputable def C_tail (N : ℕ) (t : ℝ) : ℝ := sorry

/-- Fourier Decay Theorem -/
theorem fourier_decay (N : ℕ) (t : ℝ) (ht : 0 < t) (k : ℤ) (hk : k ≠ 0) :
  ‖A_coeff N t k‖ ≤ C_tail N t / k^2 := by
  sorry

/-- Buffer formula -/
noncomputable def buffer_width (K : ℝ) (eps : ℝ) (N : ℕ) (t : ℝ) : ℕ :=
  1 + Nat.ceil (2 * C_tail N t / eps)

/-- Buffer suppression from decay -/
theorem buffer_from_decay (N : ℕ) (t : ℝ) (m : ℕ) (eps : ℝ) (heps : 0 < eps) :
  let Δ := buffer_width K eps N t
  ∑' k : {k : ℤ // |k| ≥ m + Δ}, ‖A_coeff N t k‖ ≤ eps := by
  sorry
```

## Connection to Buffer Suppression

The Fourier decay directly implies:
$$\|H_{mM}\| \leq w_{\max} \cdot \sum_{|k| \geq \Delta} |A_k| \leq w_{\max} \cdot C_{\text{tail}}/\Delta$$

Choose $\Delta$ large enough to make this $\leq \varepsilon$.

## Dependencies

- Fejér kernel properties (Mathlib)
- Modified Bessel function bounds
- Convolution in Fourier space
