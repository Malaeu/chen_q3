# PROOF DOSSIER (v2.1, с точными ссылками на модули)

## §0. Theorem Title and Status

**RH.** Все нетривиальные нули ζ(s) лежат на линии Re(s) = 1/2.

**Статус:** Условный вывод из модулей T0+A1′+A2+A3+RKHS+Weil (в рамках ZFC + классическая аналитика).

---

## §1. Formal Statement

Для всех $s \in \mathbb{C}$: если $0 < \Re(s) < 1$ и $\zeta(s) = 0$ (нетривиальный ноль), то $\Re(s) = 1/2$.

---

## §2. Definitions and Notation (как в базе)

### Weil cone
$\mathcal{W} = \bigcup_{K>0} \mathcal{W}_K$, где $\mathcal{W}_K$ — чётные, неотрицательные, компактно-поддержанные окна на $[-K, K]$.

**См.** `scope_notation.tex`

### Нормировка Q (T0)

$$
Q(\Phi) = \int a_*(\xi) \Phi(\xi) \, d\xi - \sum_{n \ge 2} \frac{2\Lambda(n)}{\sqrt{n}} \Phi(\xi_n)
$$

где:
- $a_*(\xi) = 2\pi(\log\pi - \Re\psi(\frac{1}{4} + i\pi\xi))$
- $\xi_n = \frac{\log n}{2\pi}$

**См.** `T0.tex`, `A2.tex`

### Fejér×heat окно

$$
\Phi_{B,t}(\xi) = (1 - |\xi|/B)_+ \cdot e^{-4\pi^2 t\xi^2}, \quad B \ge 3, \ t = 3/50
$$

**См.** `symbol_floor.tex`

### Символ

$$
g_{B,t}(\xi) = a(\xi) \Phi_{B,t}(\xi)
$$

$$
P_A(\theta) = 2\pi \sum_{m \in \mathbb{Z}} g_{B,t}(\theta + m) \quad \text{на } \mathbb{T} = \mathbb{R}/\mathbb{Z}
$$

**См.** `symbol_floor.tex`

---

## §3. Dependencies (модули из текста)

### Классика (Tier-1)

| Факт | Источник |
|------|----------|
| Weil criterion | `Weil_linkage.tex` |
| Guinand–Weil нормировка | `T0.tex` |
| Szegő–Böttcher barrier | `matrix_guard.tex` |

### Q3-модули (Tier-2)

| Модуль | Файл |
|--------|------|
| A1′ плотность | `A1prime.tex` |
| A2 липшицевость Q | `A2.tex` |
| Rayleigh identification | `rayleigh_bridge.tex` |
| A3 uniform floor | `symbol_floor.tex` |
| RKHS cap $\rho(t)$, $\rho(1) < 1/25$ | `prime_trace_closed_form.tex` + `prime_norm_leq_rho.tex` |
| Main closure | `Main_closure.tex` |

---

## §4. Proof Plan

1. Локализация $\Phi \in \mathcal{W}_K$
2. Приближение Fejér×heat (A1′)
3. Rayleigh-идентификация $Q(\Phi_{B,t})$
4. A3: floor $c_*$ + SB-модуль
5. RKHS cap $\|T_P\| \le \rho(1)$
6. $Q(\Phi_{B,t}) \ge 0$
7. A2 перенос на $\mathcal{W}_K$, затем на $\mathcal{W}$
8. Weil criterion ⇒ RH

---

## §5. Lemmas (с ссылками)

### Uniform floor
$$
P_A(\theta) \ge c_* = \frac{11}{10} \quad \forall \theta \in \mathbb{T}
$$
**Источник:** `symbol_floor.tex` (Lemma `lem:uniform-arch-floor`)

### Sample bounds
$$
a\left(\frac{1}{2}\right) \ge \frac{29}{50}, \quad
a\left(\frac{3}{2}\right) \ge -\frac{3}{5}, \quad
a\left(\frac{5}{2}\right) \ge -\frac{11}{10}
$$
**Источник:** `symbol_floor.tex` + `digamma_computation.tex`

### Rayleigh identification
**Источник:** `rayleigh_bridge.tex`

### SB barrier
$$
\lambda_{\min}(T_M[P_A]) \ge \min P_A - C_{\mathrm{SB}} \omega_{P_A}(1/(2M))
$$
**Источник:** `matrix_guard.tex`

### Uniform prime cap
$$
\|T_P\| \le \rho(t), \quad \rho(1) < \frac{1}{25}
$$
**Источник:** `prime_trace_closed_form.tex`

### A1′ density
**Источник:** `A1prime.tex`

### A2 continuity
**Источник:** `A2.tex`

### Main closure
**Источник:** `Main_closure.tex`

---

## §6. Main Proof (с ссылками)

1. Для $\Phi \in \mathcal{W}$ выбираем $K$ с поддержкой в $[-K, K]$.
   **→** `Main_closure.tex`

2. A1′ даёт приближение Fejér×heat.
   **→** `A1prime.tex`

3. Rayleigh-идентификация переводит $Q(\Phi_{B,t})$ в Toeplitz-форму.
   **→** `rayleigh_bridge.tex`

4. A3: floor $c_*$ + SB-модуль.
   **→** `symbol_floor.tex`, `matrix_guard.tex`

5. RKHS cap: $\|T_P\| \le \rho(1) < 1/25 < c_*/4$.
   **→** `prime_trace_closed_form.tex`, `symbol_floor.tex`

6. Итог: $Q(\Phi_{B,t}) \ge 0$, A2 переносит на $\mathcal{W}_K$, затем на $\mathcal{W}$.
   **→** `A2.tex`, `Main_closure.tex`

7. Weil criterion ⇒ RH.
   **→** `Weil_linkage.tex`

∎

---

## §7. Audit Notes (по базе)

| Check | Status |
|-------|--------|
| Legacy-K рецепты в main chain | ❌ Нет |
| JSON-таблицы как посылки | ❌ Нет |
| Нормировка Q синхронизирована с T0 | ✅ Да |
| wmax+sqrt S_K(t) в main chain | ❌ Нет (только в RKHS-ветке) |
| a(0)>4 from series | ❌ Нет (заменено на sample bounds) |

---

## §8. Module Map

```
T0.tex ──────────────────────────────────────┐
                                              │
A1prime.tex ─────┐                            │
                 ├─→ Main_closure.tex ────────┤
A2.tex ──────────┘                            │
                                              │
symbol_floor.tex ─────┐                       │
                      ├─→ Toeplitz margin ────┤
matrix_guard.tex ─────┘                       │
                                              │
prime_trace_closed_form.tex ─→ RKHS cap ──────┤
                                              │
                                              ▼
                                   Weil_linkage.tex ─→ RH
```

---

**∎ END OF PROOF DOSSIER v2.1**
