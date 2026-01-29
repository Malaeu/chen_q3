# A2: Lipschitz Control of Q on Compacts

## Overview
This file formalizes the Lipschitz continuity of the Guinand-Weil functional Q on compact windows. This is essential for the compact-by-compact transfer strategy.

## Definitions

### Spectral Coordinates
$$\xi_n := \frac{\log n}{2\pi}$$

### Prime Weights (evenized)
$$w_Q(n) := \frac{2\Lambda(n)}{\sqrt{n}}$$

### Archimedean Density
$$a(\xi) := \log\pi - \Re\psi\left(\frac{1}{4} + i\pi\xi\right)$$

### Q Functional
$$Q(\Phi) := \int_{-R}^{R} a(\xi)\Phi(\xi)d\xi - \sum_{\xi_n \in K} w_Q(n)\Phi(\xi_n)$$

---

## Lemma Q-local-finite (Local Finiteness of Prime Sampler)

**Statement:**
Fix $K > 0$. For every even $\Phi \in C_c(\mathbb{R})$ with $\operatorname{supp}\Phi \subset [-K, K]$, the prime part of $Q$,
$$\sum_{n \geq 2} \frac{2\Lambda(n)}{\sqrt{n}} \Phi(\xi_n)$$
is a finite sum: only finitely many terms are non-zero.

**Proof:**
If $\operatorname{supp}\Phi \subset [-K, K]$, then $\Phi(\xi_n) = 0$ whenever $|\xi_n| > K$. The inequality $|\xi_n| \leq K$ is equivalent to $n \leq \lfloor e^{2\pi K} \rfloor$, so only finitely many indices contribute. The minimum spacing of active nodes is:
$$\delta_K := \min_{m \neq n} |\xi_m - \xi_n| \geq \frac{1}{2\pi(\lfloor e^{2\pi K} \rfloor + 1)}$$

---

## Corollary A2-Lip (Lipschitz Continuity on Compact Window)

**Statement:**
Let $\Phi_1, \Phi_2 \in C_c([-K, K])$ be even. Then:
$$|Q(\Phi_1) - Q(\Phi_2)| \leq \|a^*\|_{L^\infty([-K,K])} \cdot 2K \cdot \|\Phi_1 - \Phi_2\|_\infty + \left(\sum_{\xi_n \in [-K,K]} \frac{2\Lambda(n)}{\sqrt{n}}\right) \|\Phi_1 - \Phi_2\|_\infty$$

In particular, $Q$ is Lipschitz on $C_c([-K, K])$ with this explicit constant.

**Proof:**
The Archimedean term is continuous in $\Phi$ in $L^1([-K, K])$ because $a^*$ is bounded on the compact. The prime term is a finite sum of point evaluations by Lemma Q-local-finite. The bound follows by estimating each piece separately.

---

## Lemma A2 (Main Lipschitz Lemma)

**Statement:**
Fix a compact $K = [-R, R]$. For even nonnegative $\Phi$ supported in $K$, the functional $Q$ is Lipschitz on $C^+_{\mathrm{even}}(K)$ in $\|\cdot\|_\infty$:
$$|Q(\Phi_1) - Q(\Phi_2)| \leq \left(\|a\|_{L^1(K)} + \sum_{\xi_n \in K} |w(n)|\right) \|\Phi_1 - \Phi_2\|_\infty$$

Additionally, if a construction uses Fejér×heat with small leakage outside $K$, then after a cutoff $n \leq N$ the tail satisfies:
$$\mathrm{Tail}(t; N) := \sum_{\xi_n \notin K, n > N} w_Q(n)\Phi(\xi_n) \ll \frac{e^{-t(\log N)^2}}{t}, \quad (t \downarrow 0)$$

**Proof (3 Steps):**

**Step 1 (Archimedean bound):**
$$\left|\int_{-R}^{R} a(\xi)(\Phi_1 - \Phi_2)(\xi)d\xi\right| \leq \|a\|_{L^1(K)} \|\Phi_1 - \Phi_2\|_\infty$$

**Step 2 (Prime sum bound):** Since $\{\xi_n \in K\}$ is finite ($n \leq e^{2\pi R}$):
$$\left|\sum_{\xi_n \in K} w_Q(n)(\Phi_1 - \Phi_2)(\xi_n)\right| \leq \left(\sum_{\xi_n \in K} w_Q(n)\right) \|\Phi_1 - \Phi_2\|_\infty$$

**Step 3 (Tail estimate):** For the tail, note $\Phi(\xi) \leq e^{-4\pi^2 t \xi^2}$ and $\xi_n = \frac{\log n}{2\pi}$, hence:
$$\sum_{n > N} w_Q(n)\Phi(\xi_n) \leq \sum_{n > N} \frac{2\log n}{\sqrt{n}} e^{-t(\log n)^2}$$

Estimating the sum by an integral with $y = \log n$:
$$\sum_{n > N} \frac{\log n}{\sqrt{n}} e^{-t(\log n)^2} \leq C \int_{\log N}^{\infty} y e^{-ty^2} e^{-y/2} dy \ll \frac{e^{-t(\log N)^2}}{t}$$

---

## Corollary A2-Explicit (Explicit Lipschitz Modulus)

**Statement:**
Fix $K = [-R, R]$ and set:
$$L_Q(K) := \|a\|_{L^1(K)} + \sum_{\xi_n \in K} \frac{2\Lambda(n)}{\sqrt{n}}$$

Then for all even, nonnegative $\Phi_1, \Phi_2 \in C_c(K)$:
$$|Q(\Phi_1) - Q(\Phi_2)| \leq L_Q(K) \|\Phi_1 - \Phi_2\|_\infty$$

**Proof:**
Combine Corollary A2-Lip with the evenization convention $w(n) = 2\Lambda(n)/\sqrt{n}$. The tail clause follows from Lemma A2.

---

## Expected Lean Output

```lean
-- Definitions
noncomputable def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

noncomputable def w_Q (n : ℕ) : ℝ :=
  2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n

-- Lemma: Local finiteness
theorem Q_local_finite (K : ℝ) (hK : K > 0) (Φ : ℝ → ℝ)
    (hΦ_supp : ∀ x, |x| > K → Φ x = 0) :
    {n : ℕ | n ≥ 2 ∧ Φ (xi_n n) ≠ 0}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc 2 (Nat.floor (Real.exp (2 * Real.pi * K))))
  intro n ⟨hn, hΦn⟩
  constructor
  · exact hn
  · by_contra h
    push_neg at h
    have : |xi_n n| > K := by
      simp [xi_n]
      sorry -- logarithm bound
    exact hΦn (hΦ_supp _ this)

-- Corollary: Lipschitz bound
theorem A2_lipschitz (K : ℝ) (hK : K > 0)
    (Φ₁ Φ₂ : ℝ → ℝ)
    (hΦ₁_supp : ∀ x, |x| > K → Φ₁ x = 0)
    (hΦ₂_supp : ∀ x, |x| > K → Φ₂ x = 0)
    (hΦ₁_even : ∀ x, Φ₁ x = Φ₁ (-x))
    (hΦ₂_even : ∀ x, Φ₂ x = Φ₂ (-x)) :
    |Q Φ₁ - Q Φ₂| ≤ L_Q K * ‖Φ₁ - Φ₂‖_∞ := by
  sorry -- Combine archimedean and prime bounds

-- Theorem: Tail estimate
theorem A2_tail_bound (t N : ℝ) (ht : t > 0) (hN : N > 1) (K : ℝ)
    (Φ : ℝ → ℝ) (hΦ_decay : ∀ ξ, Φ ξ ≤ Real.exp (-4 * Real.pi^2 * t * ξ^2)) :
    ∃ C > 0, ∑' n : {n : ℕ | xi_n n ∉ Set.Icc (-K) K ∧ n > N},
      w_Q n * Φ (xi_n n) ≤ C * Real.exp (-t * (Real.log N)^2) / t := by
  sorry -- Integral comparison
```
