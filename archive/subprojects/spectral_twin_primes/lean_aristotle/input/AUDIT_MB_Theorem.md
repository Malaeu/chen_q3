# MB Theorem: Minor Model Bias

## Context

From Formal Audit Document 25: MB is a THEOREM, not a hypothesis.
This proves that model expectation is small on minor arcs.

## Setup

Let:
- $H$ be the RKHS with heat kernel
- $H_{\text{minor}} = \{f \in H : \text{supp}(\hat{f}) \subseteq \text{minor arcs}\}$
- $\mathbb{E}_{\text{model},A}(f) = \langle f, \mu_A \rangle_H$ where $\mu_A$ is Riesz representer
- $P_{\text{minor}} : H \to H_{\text{minor}}$ be the orthogonal projection

## Theorem (Minor Model Bias)

$$\sup_{f \in H_{\text{minor}}, \|f\|_H \leq 1} |\mathbb{E}_{\text{model},A}(f)| \leq c \cdot \delta_A$$

## Equivalent Formulation (Riesz)

Since $\mathbb{E}_{\text{model},A}(f) = \langle f, \mu_A \rangle_H$:
$$(MB) \iff \|P_{\text{minor}} \mu_A\|_H \leq c \cdot \delta_A$$

## Proof Path 1: Gaussian/RKHS

**Key mechanism:** Heat factor $e^{-4\pi^2 t \xi^2}$ in kernel $\Phi_{B,t}$.

**Step 1:** The model density $\mu_A$ is essentially:
$$\mu_A(x) \sim \int P_A(\theta) \cdot K_t(x, \theta) \, d\theta$$

**Step 2:** On minor arcs (high frequency), $|\xi| \geq m + \Delta$:
$$|\hat{\mu}_A(\xi)| \leq C \cdot e^{-4\pi^2 t (m + \Delta)^2}$$

**Step 3:** The projection onto minor:
$$\|P_{\text{minor}} \mu_A\|^2 = \int_{|\xi| \geq m + \Delta} |\hat{\mu}_A(\xi)|^2 \, d\xi$$

**Step 4:** For buffer $D \geq 2\sqrt{t \cdot \log(1/\delta_A)}$:
$$\|P_{\text{minor}} \mu_A\| \leq c \cdot \delta_A$$

## Proof Path 2: Toeplitz/Fourier

**Key mechanism:** Fourier decay $|A_k| \leq C/k^2$.

**Step 1:** The archimedean symbol has Fourier coefficients:
$$P_A(\theta) = \sum_k A_k \cdot e^{ik\theta}$$

**Step 2:** For $|k| \geq m + \Delta$ (minor frequencies):
$$|A_k| \leq C_{\text{tail}} / k^2$$

**Step 3:** Summing over minor arcs:
$$\sum_{|k| \geq m + \Delta} |A_k| \leq C_{\text{tail}} \cdot \sum_{k \geq m + \Delta} 1/k^2 \leq C_{\text{tail}} / (m + \Delta)$$

**Step 4:** For $\Delta \geq C/\delta_A$:
$$\text{minor contribution} \leq c \cdot \delta_A$$

## Corollary: ξ-minor pseudorandomness

Combining D3-lock repair with MB theorem:

For $f \in H_{\text{minor}}$ with $\|f\|_H \leq 1$:
$$|L_A(f)| \leq |L_A(f) - \mathbb{E}_{\text{model},A}(f)| + |\mathbb{E}_{\text{model},A}(f)|$$
$$\leq C(K) \cdot \delta_A + c \cdot \delta_A = (C(K) + c) \cdot \delta_A$$

## Expected Lean Formalization

```lean
/-- Projection onto minor subspace -/
def P_minor (H_minor : Submodule ℂ H) : H →L[ℂ] H :=
  orthogonalProjection H_minor

/-- MB Theorem: Model expectation is small on minor arcs -/
theorem MB_theorem (A K : ℝ) (mu_A : H) (H_minor : Submodule ℂ H)
    (delta_A : ℝ) (c : ℝ) (hc : 0 < c) :
  ‖P_minor H_minor mu_A‖ ≤ c * delta_A := by
  sorry

/-- ξ-minor pseudorandomness -/
theorem xi_minor_pseudorandom (A K : ℝ) (f : H) (hf : f ∈ H_minor) (hnorm : ‖f‖ ≤ 1)
    (delta_A : ℝ) :
  |L_A f| ≤ (C_K + c) * delta_A := by
  -- Triangle inequality + D3-lock + MB
  sorry
```

## Dependencies

- Heat kernel Fourier transform
- Toeplitz symbol Fourier coefficients
- D3-lock repair (for corollary)
