# T0: Guinand-Weil Normalization Crosswalk

## Overview
This file formalizes the normalization conventions that connect our repository's Q functional to the classical Guinand-Weil functional. These are foundational definitions and change-of-variables lemmas.

## Definitions

### Fourier Transform Convention
We use the unitary normalization:
$$\widehat{\varphi}(\xi) = \int_{\mathbb{R}} \varphi(t) e^{-2\pi i t \xi} dt$$

### Spectral Coordinates
- Repository frequency axis: $\xi \in \mathbb{R}$
- Guinand-Weil frequency axis: $\eta = 2\pi\xi$
- Prime nodes: $\xi_n = \frac{\log n}{2\pi}$ for $n \geq 2$

### Archimedean Density
$$a(\xi) := \log\pi - \Re\psi\left(\frac{1}{4} + i\pi\xi\right)$$
$$a^*(\xi) := 2\pi \cdot a(\xi)$$

where $\psi$ is the digamma function.

### Prime Weights
$$w(n) := \frac{2\Lambda(n)}{\sqrt{n}}$$

where $\Lambda$ is the von Mangoldt function.

### Q Functional
$$Q(\varphi) := \int_{\mathbb{R}} a^*(\xi) \varphi(\xi) d\xi - \sum_{n \geq 2} w(n) \varphi(\xi_n)$$

---

## Proposition T0' (Guinand-Weil Matching)

**Statement:**
Under the unitary Fourier convention, the repository normalization $Q(\varphi)$ matches the classical Guinand-Weil functional after the change of variables $\eta = 2\pi\xi$:
$$Q(\varphi) = Q_{\mathrm{GW}}(\varphi_{\mathrm{GW}}) \text{ with } \eta = 2\pi\xi, \, d\eta = 2\pi d\xi$$

**Proof Sketch:**
Make the substitution $\eta = 2\pi\xi$ in all frequency integrals. By evenness of $\varphi$, the sine parts vanish and the cosine parts coincide. The Jacobian $d\eta = 2\pi d\xi$ is absorbed by the fixed normalization.

---

## Lemma T0 (Q Normalization Crosswalk)

**Statement:**
Let $\varphi_{\mathrm{GW}} \in C_c(\mathbb{R})$ be even and nonnegative. Define:
1. The Guinand-Weil functional:
$$Q_{\mathrm{GW}}(\varphi_{\mathrm{GW}}) := \int_{\mathbb{R}} \left(\log\pi - \Re\psi\left(\frac{1}{4} + \frac{i\eta}{2}\right)\right) \varphi_{\mathrm{GW}}(\eta) d\eta - \sum_{n \geq 2} \frac{\Lambda(n)}{\sqrt{n}} \left(\varphi_{\mathrm{GW}}(\log n) + \varphi_{\mathrm{GW}}(-\log n)\right)$$

2. The repository functional with $\varphi(\xi) := \varphi_{\mathrm{GW}}(2\pi\xi)$:
$$Q(\varphi) := \int_{\mathbb{R}} a^*(\xi) \varphi(\xi) d\xi - \sum_{n \geq 2} w(n) \varphi(\xi_n)$$

Then $Q(\varphi) = Q_{\mathrm{GW}}(\varphi_{\mathrm{GW}})$.

**Proof:**
1. For the archimedean integral: Change variables $\eta = 2\pi\xi$, so $d\eta = 2\pi d\xi$ and $\psi(\frac{1}{4} + \frac{i\eta}{2}) = \psi(\frac{1}{4} + i\pi\xi)$. This gives:
$$\int_{\mathbb{R}} \left(\log\pi - \Re\psi\left(\frac{1}{4} + \frac{i\eta}{2}\right)\right) \varphi_{\mathrm{GW}}(\eta) d\eta = \int_{\mathbb{R}} 2\pi a(\xi) \varphi(\xi) d\xi = \int_{\mathbb{R}} a^*(\xi) \varphi(\xi) d\xi$$

2. For the prime sum: Since $\varphi_{\mathrm{GW}}(\pm\log n) = \varphi(\pm\xi_n)$ and $\varphi$ is even:
$$\sum_{n \geq 2} \frac{\Lambda(n)}{\sqrt{n}} \left(\varphi_{\mathrm{GW}}(\log n) + \varphi_{\mathrm{GW}}(-\log n)\right) = \sum_{n \geq 2} \frac{2\Lambda(n)}{\sqrt{n}} \varphi(\xi_n) = \sum_{n \geq 2} w(n) \varphi(\xi_n)$$

3. Combining: $Q(\varphi) = Q_{\mathrm{GW}}(\varphi_{\mathrm{GW}})$.

---

## Lemma T0-Invariance (Normalization Invariance)

**Statement:**
Different choices of Fourier-transform normalizations and node indexing yield equivalent formulations of the Weil positivity criterion. Specifically:

(a) Switching from unitary normalization $\widehat{\Phi}(\xi) = \int \Phi(x) e^{-2\pi i x\xi} dx$ to the measure $\widehat{\Phi}'(\eta) = \int \Phi(x) e^{-i\eta x} dx$ with $\eta = 2\pi\xi$ induces the density rescaling $a^*(\xi) = 2\pi a(\xi)$ and preserves the form of $Q$.

(b) Replacing the node sequence $\xi_n = \log n / (2\pi)$ by $\pm\log n / (2\pi)$ preserves the symmetry of the sampling operator.

(c) The quadratic form $Q(\varphi)$ defined via the Guinand-Weil convention coincides with $Q_{\mathrm{GW}}(\varphi_{\mathrm{GW}})$ when test functions are converted via the measure factor.

**Conclusion:** The positivity of $Q$ is independent of these technical choices.

**Proof:**
Each rescaling is a linear change of variable that preserves the spectral gap and compact-by-compact structure. The node-symmetry $\pm\log n/(2\pi)$ is built into the Guinand-Weil formalism. The measure conversion $a^*(\xi) = 2\pi a(\xi)$ follows from the Jacobian of $\eta = 2\pi\xi$.

---

## Expected Lean Output

```lean
-- Definitions
noncomputable def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

noncomputable def archimedean_density (ξ : ℝ) : ℝ :=
  Real.log Real.pi - (Complex.digamma (1/4 + Complex.I * Real.pi * ξ)).re

noncomputable def archimedean_density_star (ξ : ℝ) : ℝ :=
  2 * Real.pi * archimedean_density ξ

noncomputable def prime_weight (n : ℕ) : ℝ :=
  2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n

-- Proposition T0': Guinand-Weil matching
theorem T0_GW_matching (φ : ℝ → ℝ) (hφ_even : ∀ x, φ x = φ (-x)) :
  Q φ = Q_GW (fun η => φ (η / (2 * Real.pi)))

-- Lemma T0: Q normalization crosswalk
theorem T0_Q_crosswalk (φ_GW : ℝ → ℝ) (hφ_even : ∀ x, φ_GW x = φ_GW (-x))
    (hφ_nonneg : ∀ x, 0 ≤ φ_GW x) (hφ_compact : HasCompactSupport φ_GW) :
  Q (fun ξ => φ_GW (2 * Real.pi * ξ)) = Q_GW φ_GW

-- Lemma: Normalization invariance
theorem T0_normalization_invariance :
  ∀ φ : ℝ → ℝ, (Q φ ≥ 0 ↔ Q_GW (fun η => φ (η / (2 * Real.pi))) ≥ 0)
```
