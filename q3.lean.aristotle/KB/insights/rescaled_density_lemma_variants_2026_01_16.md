---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Rescaled Density Lemma: Three Variants

**Date**: 2026-01-16
**Status**: Key insight for (2M+1) factor elimination
**Context**: After Heat Localization insight, exploring algebraic approaches

---

## Problem Statement

В `rayleigh_Q_identification` торчит множитель `(2M+1)`:
```
(2M+1) * ∫ P_A dθ - Σ w(n)Φ(ξ_n) ≥ 0
```

Нужно: `arch_term ≥ prime_term` где:
- `arch_term = ∫ a*(ξ) Φ(ξ) dξ`
- `prime_term = Σ w_Q(n) Φ(ξ_n)`

---

## Variant A: Measure Domination (Direct Bound)

### Idea
Доказать напрямую: сумма по prime nodes ≤ интеграл от arch density.

### Statement
```
Σ_{n≥2} w_Q(n) · Φ(ξ_n) ≤ ∫ a*(ξ) · Φ(ξ) dξ
```

### Approach
1. **Point-to-density bound**: Каждый терм w_Q(n)·Φ(ξ_n) оценить через интеграл a*(ξ)·Φ(ξ) по окрестности ξ_n
2. **Disjoint neighborhoods**: Окрестности prime nodes не пересекаются (prime gap!)
3. **Sum ≤ integral**: Сумма по непересекающимся окрестностям ≤ полный интеграл

### Key Lemma Needed
```lean
lemma prime_weight_dominated_by_arch_density (n : ℕ) (hn : 2 ≤ n) :
    w_Q n ≤ ∫ ξ in Set.Icc (xi_n n - δ) (xi_n n + δ), a_star ξ
```

### Difficulty
- Нужно показать что `w_Q(n) = 2·Λ(n)/√n` достаточно мало по сравнению с `a*(ξ)` на интервале размера δ
- `a*(ξ) ~ 2π` около ξ=0, но падает при больших ξ
- Зависит от точной формы `a*(ξ)`

---

## Variant B: Carleson/Sampling in RKHS

### Idea
В RKHS с воспроизводящим ядром K_t sampling bounded:
```
|f(ξ_n)|² ≤ ‖f‖² · K_t(ξ_n, ξ_n)
```

### Statement
Для f в RKHS с heat kernel:
```
Σ w(n) |f(ξ_n)|² ≤ C · ‖f‖²_RKHS
```

### RKHS Setup
- Kernel: `K_t(ξ, η) = exp(-2π²t(ξ-η)²)` (heat kernel)
- RKHS norm: `‖f‖² = ∫∫ f(ξ)·f(η)·K_t(ξ,η)⁻¹ dξdη` (inverse kernel integral)
- Evaluation: `|f(ξ)|² ≤ ‖f‖² · K_t(ξ,ξ) = ‖f‖²` (diagonal = 1)

### Carleson Condition
Мера `μ = Σ w(n) δ_{ξ_n}` — Carleson для RKHS если:
```
∫ |f|² dμ ≤ C · ‖f‖²_RKHS для всех f ∈ RKHS
```

### Key Insight
- Prime nodes разрежены (gap ~ log(n)/n)
- Heat RKHS "smooth" — evaluation bounded
- Carleson constant зависит от density of sampling points

### Difficulty
- Нужно явно вычислить Carleson constant для prime nodes
- Связать с arch_term через dual formulation

---

## Variant C: Sobolev Geometry Change

### Idea
В Соболеве H^s при s > 1/2 evaluation functionals bounded:
```
|f(ξ)| ≤ C_s · ‖f‖_{H^s}
```

### Statement
Заменить L² геометрию на H^s:
```
‖evaluation at ξ‖_{(H^s)*} = O(1)  (не O(√N))
```

### Sobolev Setup
- H^s norm: `‖f‖_{H^s}² = ∫ |f̂(k)|² (1+|k|²)^s dk`
- For s > 1/2: H^s ⊂ C^0 (Sobolev embedding)
- Evaluation: `|f(ξ)| ≤ C_s ‖f‖_{H^s}` with C_s ~ 1/√(2s-1)

### Application
Если перейти от L² к H^s:
- Toeplitz оператор остаётся bounded
- Evaluation имеет O(1) норму, не O(√(2M+1))
- Factor (2M+1) не появляется!

### Key Lemma Needed
```lean
lemma sobolev_evaluation_bound (s : ℝ) (hs : s > 1/2) (ξ : ℝ) :
    ∀ f ∈ H^s, |f(ξ)| ≤ C_s * ‖f‖_{H^s}
```

### Difficulty
- Нужно переформулировать весь Rayleigh quotient в H^s
- Toeplitz operator может иметь другие spectral properties в H^s
- Связь с исходной RH formulation через Weil

---

## Comparison Table

| Variant | Approach | Key Tool | Difficulty |
|---------|----------|----------|------------|
| A | Direct bound | Measure comparison | Need a*(ξ) explicit form |
| B | RKHS sampling | Carleson measures | Compute Carleson const |
| C | Sobolev geometry | Embedding theorem | Reformulate everything |

---

## Recommended Strategy

1. **Try Variant A first** — наиболее прямой, если получится показать w_Q(n) ≤ ∫ a*
2. **Variant B as backup** — стандартная техника RKHS
3. **Variant C for future** — требует переработки архитектуры

---

## Connection to Heat Localization

Все три варианта совместимы с Heat Localization insight:
- A: Φ(ξ_n) экспоненциально мало → sum small
- B: RKHS kernel концентрируется → sampling stable
- C: Sobolev embedding не зависит от localization

Heat Localization даёт количественный аргумент (exp decay), а эти варианты — структурный (алгебраический bound).

---

## References

- Carleson measures: Seip "Interpolation and Sampling in Spaces of Analytic Functions"
- Sobolev embedding: Adams-Fournier "Sobolev Spaces"
- RKHS theory: Paulsen-Raghupathi "Introduction to RKHS"
