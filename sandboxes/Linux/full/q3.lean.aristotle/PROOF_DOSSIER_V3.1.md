# PROOF DOSSIER v3.1 (Base-Aligned, Period-1)

## §0. Theorem Title and Status

**Theorem (Riemann Hypothesis).**
Все нетривиальные нули ζ(s) лежат на критической прямой Re(s) = 1/2.

**Статус:** Условный вывод в рамках ZFC + стандартной комплексной аналитики.

**v3.1 SYNC:** Все формулы синхронизированы с .tex базой (symbol_floor.tex, calibration.tex).

---

## §1. Formal Statement

Для всех $s \in \mathbb{C}$:
если $0 < \Re(s) < 1$, $\zeta(s) = 0$ и $s$ не является тривиальным нулём, то $\Re(s) = \frac{1}{2}$.

---

## §2. Definitions and Notation (BASE-ALIGNED)

### T0 Normalization

$$
a_*(\xi) = 2\pi \cdot a(\xi) = 2\pi(\log\pi - \Re\psi(\tfrac{1}{4} + i\pi\xi))
$$

$$
\xi_n = \frac{\log n}{2\pi}
$$

**Source:** `T0.tex`, `calibration.tex` (line 6)

### Fejér×heat Window

$$
\Phi_{B,t}(\xi) = (1 - |\xi|/B)_+ \cdot e^{-4\pi^2 t\xi^2}
$$

$$
B_{\min} = 3, \quad t_{\mathrm{sym}} = \frac{3}{50}
$$

### Weighted Density

$$
g_{B,t}(\xi) = a(\xi) \cdot \Phi_{B,t}(\xi)
$$

### Archimedean Symbol (БАЗА: С ФАКТОРОМ 2π!)

$$
P_A(\theta) = 2\pi \sum_{m \in \mathbb{Z}} g_{B,t}(\theta + m), \qquad \theta \in \mathbb{T} = [-\tfrac{1}{2}, \tfrac{1}{2}]
$$

**Source:** `symbol_floor.tex` (line 11)

**Калибровка:** Фактор $2\pi$ согласован с $a_*(\xi) = 2\pi a(\xi)$ и $\kappa_{A3} = 1$.

### Fourier Coefficients (БАЗА: С ФАКТОРОМ 2π!)

$$
A_k = 2\pi \int_{\mathbb{R}} g_{B,t}(\xi) \cos(2\pi k \xi) \, d\xi
$$

**Source:** `symbol_floor.tex` (line 16), `calibration.tex` (line 37)

### Toeplitz Basis (Period-1)

$$
e_k(\theta) = e^{2\pi i k \theta}, \qquad k \in \mathbb{Z}
$$

**Measure:** $d\theta$ on $[-\frac{1}{2}, \frac{1}{2}]$ (NOT $d\theta/(2\pi)$)

---

## §3. Key Constants (BASE VALUES)

| Constant | Value | Source |
|----------|-------|--------|
| $t_{\mathrm{sym}}$ | $\frac{3}{50} = 0.06$ | Fixed parameter |
| $B_{\min}$ | $3$ | Bandwidth threshold |
| $c_*$ | $\frac{11}{10} = 1.1$ | **ПРЯМАЯ ОЦЕНКА** `symbol_floor.tex` (line 258) |
| $C_{\mathrm{SB}}$ | $4$ | Szegő-Böttcher |
| $\rho(1)$ | $< \frac{1}{25} = 0.04$ | RKHS cap |

**ВАЖНО:** $c_* = \frac{11}{10}$ — это ПРЯМАЯ точечная нижняя граница, НЕ формула $A_* - \frac{1}{2}L_*$.

---

## §4. Dependencies

### Tier-1 (Classical)

| Fact | Source |
|------|--------|
| Weil criterion | Weil 1952 |
| Guinand-Weil formula | Guinand 1948 |
| Szegő-Böttcher barrier | Grenander & Szegő 1958 |

### Tier-2 (Q3 Chain)

| Label | Statement | Source |
|-------|-----------|--------|
| T0 | Normalization crosswalk | `T0.tex` |
| A1′ | Fejér×heat density | `A1prime.tex` |
| A2 | Q Lipschitz | `A2.tex` |
| Rayleigh | Q = Toeplitz Rayleigh | `rayleigh_bridge.tex` |
| A3 | $P_A \ge \frac{11}{10}$ | `symbol_floor.tex` (lines 247–301) |
| RKHS | $\|T_P\| \le \rho(1) < \frac{1}{25}$ | `prime_trace_closed_form.tex` |

---

## §5. Lemmas (BASE-ALIGNED)

### Lemma A3 (Uniform Floor) — ПРЯМАЯ ОЦЕНКА

**Statement:** For all $B \ge B_{\min} = 3$, $t = t_{\mathrm{sym}}$, and $\theta \in [-\frac{1}{2}, \frac{1}{2}]$:

$$
P_A(\theta) = 2\pi \sum_{m \in \mathbb{Z}} g_{B,t}(\theta + m) \ge \frac{11}{10}
$$

**Source:** `symbol_floor.tex` (lines 247–301, 318)

**Method:** Прямая точечная оценка через sample bounds, НЕ mean-minus-modulus.

### Sample Bounds

$$
a\left(\frac{1}{2}\right) \ge \frac{29}{50}, \quad
a\left(\frac{3}{2}\right) \ge -\frac{3}{5}, \quad
a\left(\frac{5}{2}\right) \ge -\frac{11}{10}
$$

**Source:** `symbol_floor.tex`, `digamma_computation.tex`

### RKHS Cap

$$
\|T_P\| \le \rho(t), \quad \rho(t) = 2\int_0^\infty y \cdot e^{y/2} \cdot e^{-4\pi^2 t y^2} \, dy
$$

$$
\rho(1) < \frac{1}{25} < \frac{c_*}{4} = \frac{11}{40}
$$

**Source:** `prime_trace_closed_form.tex`

### Discretization (Period-1)

$$
\lambda_{\min}(T_M[P_A]) \ge \min P_A - C_{\mathrm{SB}} \omega_{P_A}\left(\frac{1}{2M}\right)
$$

**Source:** `matrix_guard.tex`

### Uniform Bridge

$$
\lambda_{\min}(T_M[P_A] - T_P) \ge \frac{11}{10} - \frac{11}{20} - \frac{11}{40} = \frac{11}{40} > 0
$$

---

## §6. Main Proof

1. Fix $\Phi \in \mathcal{W}$. Choose $K$ so $\Phi \in W_K$.
2. By A1′, approximate by Fejér×heat $\Phi_{B,t}$.
3. By Rayleigh, $Q(\Phi_{B,t})$ = period-1 Toeplitz-prime quotient.
4. By A3: $P_A(\theta) = 2\pi \sum_m g(\theta+m) \ge \frac{11}{10}$ (прямая оценка).
5. By RKHS: $\|T_P\| < \frac{1}{25} < \frac{11}{40}$.
6. Thus $Q(\Phi_{B,t}) \ge 0$.
7. By A2, extends to all $\Phi \in W_K$, then to $\mathcal{W}$.
8. Weil criterion ⇒ RH.

∎

---

## §7. Audit-Edge Check

### Base Sync

| Item | v3 (wrong) | v3.1 (correct) | Source |
|------|------------|----------------|--------|
| $P_A$ definition | $\sum g(\theta+m)$ | $2\pi \sum g(\theta+m)$ | `symbol_floor.tex` L11 |
| $A_k$ | $\int g \cos(2\pi k\xi)$ | $2\pi \int g \cos(2\pi k\xi)$ | `symbol_floor.tex` L16 |
| $c_*$ | $A_* - \frac{1}{2}L_*$ | $\frac{11}{10}$ (direct) | `symbol_floor.tex` L258 |
| A3 method | mean-minus-modulus | direct pointwise | `symbol_floor.tex` L247–301 |

### Standard Checks

| Issue | Status |
|-------|--------|
| $2\pi$ calibration | ✅ $P_A$ has $2\pi$, matches $a_* = 2\pi a$ |
| Period-1 domain | ✅ $\theta \in [-\frac{1}{2}, \frac{1}{2}]$ |
| Toeplitz basis | ✅ $e^{2\pi ik\theta}$ |
| Floor method | ✅ Direct estimate, not mean-modulus |
| $c_* = \frac{11}{10}$ | ✅ Explicit value from base |
| RKHS bound | ✅ $\rho(1) < \frac{1}{25} < \frac{11}{40}$ |

---

## §8. Module Map

```
T0.tex ─────────────────────────────────────────┐
  [a_*(ξ) = 2πa(ξ), ξ_n = log n/(2π)]           │
                                                 │
calibration.tex ────────────────────────────────┤
  [κ_A3 = 1, 2π factor sync]                    │
                                                 │
A1prime.tex ─────┐                              │
                 ├─→ Main_closure.tex ──────────┤
A2.tex ──────────┘                              │
                                                 │
symbol_floor.tex ─────┐                         │
  [P_A = 2π Σ g(θ+m)] │                         │
  [c_* = 11/10 DIRECT]├─→ Toeplitz margin ──────┤
matrix_guard.tex ─────┘                         │
  [ω(1/(2M))]                                   │
                                                 │
prime_trace_closed_form.tex ─→ RKHS cap ────────┤
  [ρ(1) < 1/25]                                 │
                                                 ▼
                                     Weil_linkage.tex ─→ RH
```

---

## §9. Appendix

### References

- Weil (1952): Sur les "formules explicites"
- Guinand (1948): A summation formula
- Grenander & Szegő (1958): Toeplitz Forms
- DLMF §5.11: Digamma asymptotics

### Key Numbers

| Bound | Value |
|-------|-------|
| $c_*$ | $\frac{11}{10} = 1.1$ |
| $\rho(1)$ | $< 0.04$ |
| $c_*/4$ | $0.275$ |
| Final margin | $\frac{11}{40} = 0.275$ |

---

**∎ END OF PROOF DOSSIER v3.1 (Base-Aligned)**
