# A3: Toeplitz-Symbol Bridge (Main)

## Overview
This file formalizes the Toeplitz-symbol bridge (A3), which connects the analytical symbol estimates to the discrete Toeplitz matrix framework via Szegő-Böttcher theory. This is the central technical piece of the proof.

## Definitions

### Smoothed Symbol
$$P_A(\theta) = (a * K_{t_{\mathrm{sym}}})(\theta)$$

where $K_t(\theta) = t^{-1} K(\theta/t)$ is a scaled mollifier.

### Total Variation
$$\TV(a) = \|Da\|(\mathbb{T})$$

### Lipschitz Seminorm
$$\Lip(f) = \sup_{x \neq y} \frac{|f(x) - f(y)|}{|x - y|}$$

### Modulus of Continuity
$$\omega_f(h) = \sup_{|x - y| \leq h} |f(x) - f(y)|$$

---

## Lemma A3.BV-to-Lip (BV ⟹ Lipschitz under Convolution)

**Statement:**
Let $a \in \BV(\mathbb{T})$ with periodic extension. For every $t > 0$ the smoothed profile $a_t := a * K_t$ satisfies:
$$\|a_t\|_{L^\infty} \leq \|a\|_{L^\infty}$$
$$\|a_t'\|_{L^\infty} \leq \frac{\|K'\|_{L^1}}{t} \TV(a)$$
$$\Lip(a_t) \leq \frac{\|K'\|_{L^1}}{t} \TV(a)$$

In particular $P_A \in \Lip(1)$ with the same bound at $t = t_{\mathrm{sym}}$.

**Proof:**
Standard convolution estimates yield $\|a * K_t\|_\infty \leq \|a\|_\infty$. Since $(a * K_t)' = a * K_t'$, the variation identity $\|Da\|(\mathbb{T}) = \TV(a)$ implies:
$$\|(a * K_t)'\|_\infty \leq \TV(a) \|K_t'\|_{L^1} = \frac{\TV(a) \|K'\|_{L^1}}{t}$$

---

## Lemma A3.Sup-Bounds (Uniform Bounds for Smoothed Symbol)

**Statement:**
Under the assumptions of Lemma A3.BV-to-Lip:
$$\|P_A\|_{L^\infty} \leq \|a\|_{L^\infty}$$
$$\|P_A'\|_{L^\infty} \leq \frac{\|K'\|_{L^1}}{t_{\mathrm{sym}}} \TV(a)$$
$$\omega_{P_A}(h) \leq \frac{\|K'\|_{L^1}}{t_{\mathrm{sym}}} \TV(a) \cdot h$$

**Proof:**
Immediate from Lemma A3.BV-to-Lip.

---

## Lemma A3.Two-Scale (Two-Scale Selection and Arch Floor Preservation)

**Statement:**
Assume $P_A = a * K_{t_{\mathrm{sym}}}$ with $a \in \BV(\mathbb{T})$ and let $\Gamma \subset \mathbb{T}$ be the arc from the trace-cap hypothesis. There exists $t_{\mathrm{sym}} > 0$ small enough such that:
$$\min_{\theta \in \Gamma} P_A(\theta) \geq \frac{1}{2} \min_{\theta \in \Gamma} a(\theta) =: c_{0,\Gamma} > 0$$

Moreover, for any $t_{\mathrm{rkhs}} \geq t_{\mathrm{sym}}$ the RKHS kernel associated to $t_{\mathrm{rkhs}}$ enjoys a uniform floor $c_0(K_{t_{\mathrm{rkhs}}}) \geq c_* > 0$ independent of the Toeplitz size.

**Proof:**
Since $a * K_t \to a$ uniformly as $t \to 0$, small $t_{\mathrm{sym}}$ preserves the positive floor on $\Gamma$. The RKHS floor follows from explicit Gram estimates; choosing $t_{\mathrm{rkhs}} \geq t_{\mathrm{sym}}$ keeps the same positivity budget.

---

## Lemma A3.Lip-Floor (Lipschitz Symbol with Positive Floor ⟹ A3 Prerequisites)

**Statement:**
Let $P_A \in \Lip(1)$ with $\min_{\mathbb{T}} P_A \geq c_0 > 0$. Then the Toeplitz operator $T_{P_A}$ satisfies:
$$T_{P_A} \succeq c_0 \cdot I$$
$$\|T_{P_A}\|_{\mathrm{op}} \leq \|P_A\|_{L^\infty}$$

In particular, once $\rho_K \geq \|P_A\|_{L^\infty}$ the A3-lock positivity and boundedness hypotheses hold.

**Proof:**
For any $f$ with $\|f\|_2 = 1$:
$$\langle T_{P_A} f, f \rangle = \int_{\mathbb{T}} P_A(\theta) |f(\theta)|^2 d\theta \geq c_0$$
Hence $T_{P_A} \succeq c_0 I$. The $\|P_A\|_\infty$ bound is immediate from the Rayleigh quotient.

---

## Lemma A3.Cap-Combine (Combining with Trace-Cap)

**Statement:**
Suppose $P_A$ is constructed as above and the RKHS/trace-cap estimate $\|T_{P_A}\|_{\mathrm{op}} \leq \rho_K$ holds. Then $T_{P_A}$ simultaneously satisfies the positivity floor and the operator-norm bound required by A3-lock.

**Proof:**
Apply Lemmas A3.Two-Scale and A3.Lip-Floor, together with the stated trace-cap inequality.

---

## Lemma A3-Constructive-Schedule (Parameter Recipe)

**Statement:**
Fix $\kappa \in (0, 1)$. There exists $r_0 \in (0, 1)$ such that $m_{r_0} > 0$. For each $K > 0$ set:
$$B(K) := \left\lceil \frac{K}{1 - \kappa} \right\rceil, \qquad r(K) := \min\left\{\frac{K}{2}, r_0\right\}$$

Define:
$$A_K := 2m_{r(K)} r(K) \left(1 - \frac{r(K)}{B(K)}\right)$$
$$B_K^{(1)} := \frac{M_{B(K)}}{4\pi^2 r(K)}$$
$$D_K := \pi \|K'\|_{L^1(\mathbb{T})} \TV(a)$$

For $\theta > 0$:
$$F_K(\theta) := e^{-4\pi^2\theta}\left(A_K - \frac{B_K^{(1)}}{\theta}\right) - \frac{D_K}{\theta}$$

Let $\theta_1(K) := \max\{1, 2B_K^{(1)}/A_K\}$ and $\theta_2(K)$ be the smallest positive solution of:
$$\frac{4D_K}{A_K} = \theta e^{-4\pi^2\theta}$$

Set:
$$\theta^*(K) := \max\{\theta_1(K), \theta_2(K)\}$$
$$t_{\mathrm{sym}}(K) := \frac{\theta^*(K)}{r(K)^2}$$
$$c_{\mathrm{arch}}(K) := \underline{A}_0(B(K), r(K), t_{\mathrm{sym}}(K)) - \pi L_A(B(K), t_{\mathrm{sym}}(K))$$

Finally:
$$M_0(K) := \left\lceil \frac{2\pi C_{\mathrm{SB}} L_A(B(K), t_{\mathrm{sym}}(K))}{c_{\mathrm{arch}}(K)} \right\rceil$$
$$t_{\mathrm{rkhs}}^*(K) := \frac{1}{8\pi^2}\left(\frac{1}{2} + \frac{4e^{1/4}}{c_{\mathrm{arch}}(K)}\right)$$

Then $c_{\mathrm{arch}}(K) > 0$, and the triple $(B(K), t_{\mathrm{sym}}(K), t_{\mathrm{rkhs}}^*(K))$ satisfies (A3.1)–(A3.3).

**Proof:**
Lemma A3-core-lower-bound gives the expression for $\underline{A}_0$. The condition $\theta \geq \theta_1(K)$ makes the expression in parentheses $\geq A_K/2$. At $\theta_2(K)$ we balance exponential and polynomial terms. At $\theta^* = \max\{\theta_1, \theta_2\}$:
$$F_K(\theta^*) \geq \frac{A_K}{4} e^{-4\pi^2\theta^*}$$
Hence $c_{\mathrm{arch}}(K) \geq \frac{1}{4} A_K e^{-4\pi^2\theta^*(K)} > 0$, establishing (A3.1). Proposition A3-M0 yields (A3.2), and Proposition A3-prime-cap provides (A3.3).

---

## Theorem A3 (A3 Bridge Inequality) — MAIN THEOREM

**Statement:**
Let $K > 0$ and let $(B, t_{\mathrm{sym}}, t_{\mathrm{rkhs}})$ satisfy (A3.1)–(A3.3). Then for every $M \geq M_0(K)$:
$$\lambda_{\min}(T_M[P_A] - T_P) \geq \frac{c_{\mathrm{arch}}(K)}{4} > 0$$

and the associated Fejér×heat test functions satisfy:
$$Q(\Phi_{B,t}) \geq 0$$

**Proof:**
Items (A3.1)–(A3.3) supply the hypotheses of Theorem A3-mixed-margin with $c_0(K) = c_{\mathrm{arch}}(K)$. The theorem yields the stated operator inequality. Lemma A3-model-space combined with Theorem A3-Rayleigh-identification converts the matrix margin into $Q(\Phi_{B,t}) \geq 0$.

---

## Expected Lean Output

```lean
-- Definitions
variable (a : ℝ → ℝ) (K : C(ℝ, ℝ)) -- mollifier

noncomputable def smoothed_symbol (t : ℝ) : ℝ → ℝ :=
  fun θ => ∫ x, a x * K.1 ((θ - x) / t) / t

noncomputable def total_variation (a : ℝ → ℝ) : ℝ := sorry -- BV norm

-- Lemma: BV to Lipschitz
theorem A3_BV_to_Lip (a : ℝ → ℝ) (ha_bv : total_variation a < ⊤)
    (K : C(ℝ, ℝ)) (hK_int : ∫ x, K x = 1) (t : ℝ) (ht : t > 0) :
    let a_t := smoothed_symbol a K t
    ‖a_t‖_∞ ≤ ‖a‖_∞ ∧
    LipschitzWith (‖K'‖_L1 / t * total_variation a) a_t := by
  sorry

-- Lemma: Lipschitz symbol with floor implies positivity
theorem A3_Lip_Floor (P_A : ℝ → ℝ) (hLip : LipschitzWith L P_A)
    (hFloor : ∀ θ, c₀ ≤ P_A θ) (hc₀ : c₀ > 0) :
    ∀ v : EuclideanSpace ℝ (Fin M), ‖v‖ = 1 →
      c₀ ≤ ⟪toeplitz_matrix P_A M v, v⟫ := by
  sorry

-- Main Theorem A3
theorem A3_bridge_inequality (K : ℝ) (hK : K > 0)
    (B t_sym t_rkhs : ℝ)
    (hA3_1 : c_arch K > 0)  -- positive floor
    (hA3_2 : M ≥ M₀ K)      -- discretization threshold
    (hA3_3 : ‖T_P‖ ≤ c_arch K / 4)  -- prime cap
    :
    λ_min (T_M P_A - T_P) ≥ c_arch K / 4 ∧
    Q (Φ_Bt B t_sym) ≥ 0 := by
  sorry

-- Corollary: Q nonnegativity on compact
theorem A3_Q_nonneg_on_compact (K : ℝ) (hK : K > 0)
    (Φ : ℝ → ℝ) (hΦ_supp : ∀ x, |x| > K → Φ x = 0)
    (hΦ_fejer_heat : is_fejer_heat Φ (B K) (t_sym K)) :
    Q Φ ≥ 0 := by
  exact (A3_bridge_inequality K hK _ _ _ _ _ _).2
```
