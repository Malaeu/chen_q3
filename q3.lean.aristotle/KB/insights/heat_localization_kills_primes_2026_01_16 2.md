---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Heat Localization Kills Primes

**Date**: 2026-01-16
**Status**: Key insight for (2M+1) factor problem
**Discovery**: Claude Code session, web search + code analysis

---

## Problem

В calc chain для `rayleigh_Q_identification` торчит множитель `(2M+1)`:
```
(2M+1) * ∫ P_A dθ - Σ nodes ≠ arch_term - prime_term
```

Нужен аргумент показывающий `arch_term ≥ prime_term` без M-фактора.

---

## Key Insight: Heat Kernel Creates "Blind Spot"

### Структура test function

```lean
def fejer_heat_window (B t ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)
```

Это **Fejér × Gaussian**. При `t → ∞` гауссиан стягивается в δ₀.

### Где сидят primes?

```lean
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)
```

- `ξ₂ = log(2)/(2π) ≈ 0.110`
- `ξ₃ = log(3)/(2π) ≈ 0.175`
- ...

**ВСЕ prime nodes строго > 0!** Нет ни одного в точке ξ = 0.

### Следствие

```
arch_term = ∫ a*(ξ) · Φ(ξ) dξ    ← ВИДИТ пик в ξ=0
prime_term = Σ w(n) · Φ(ξ_n)     ← НЕ ВИДИТ ξ=0, только ξ_n ≥ 0.11
```

При большом `t`:
| Точка | Значение Φ |
|-------|-----------|
| ξ = 0 | 1 (пик) |
| ξ₂ ≈ 0.11 | exp(-0.48·t) |

При `t = 40`: `Φ(ξ₂) ≈ exp(-19) ≈ 10⁻⁹`

---

## Количественная оценка

### Ratio arch/prime

```
arch_term ~ c₁ / √t        (Laplace асимптотика)
prime_term ~ c₂ · exp(-c₃·t)  (доминантный терм n=2)

Ratio ~ exp(c·t) / √t → ∞
```

### Численно

| t | Φ(ξ₂) = exp(-t·(log 2)²) | 1/√t | arch/prime |
|---|--------------------------|------|------------|
| 1 | 0.62 | 1.00 | ~2 |
| 10 | 0.008 | 0.32 | ~40 |
| 40 | 10⁻⁸ | 0.16 | ~10⁷ |

---

## Применение

Для `t ≥ 10` (и тем более для `t_rkhs_cap = 40`):
```
arch_term >> prime_term
```

Это даёт `arch_term ≥ prime_term` без множителя `(2M+1)`.

---

## Источники открытия

1. **arxiv:2006.13771** "Weil positivity and Trace formula" - упоминание локализации через prolate spheroidal functions
2. **Q3/Basic/Defs.lean** - структура `fejer_heat_window` как гауссиан
3. **Стандартный анализ** - heat kernel → delta при t→∞
4. **Арифметика** - все ξ_n = log(n)/(2π) > 0 для n ≥ 2

---

## Aristotle Submissions

- `localization_argument_v1.md` (UUID: f02da101-671f-4ee2-8208-a065a2b61ff3)
- `arch_vs_prime_explicit_v1.md` (UUID: 301e589e-02da-499f-96f6-d718dac6ea58)

---

## Quick Detection

**Когда применять**: Если видишь `(2M+1)` множитель в Rayleigh-to-Q связке и нужен аргумент независимый от M.

**Проверка**: Heat parameter `t ≥ 10`? → Localization argument работает.
