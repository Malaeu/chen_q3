# Proshka Analysis: a_star Crisis Resolution

**Date:** 2026-01-15
**Status:** CRITICAL ARCHITECTURAL FIX NEEDED

## Executive Summary

**ДВА БАГА найдено:**

1. **`a_star_pos` — ЛОЖНАЯ АКСИОМА!**
   - `a*(ξ) → -∞` при `|ξ| → ∞`
   - Доказательство: стандартная асимптотика digamma `ψ(z) ≈ log(z)`
   - Аксиома `a_star_pos : ∀ ξ, a_star ξ > 0` **МАТЕМАТИЧЕСКИ НЕВОЗМОЖНА**

2. **Неправильный символ + неправильный Toeplitz в chain!**
   - Chain использует `a_star` (без floor)
   - A3_FLOOR доказывает floor для `P_A` (другая функция!)
   - `ToeplitzMatrix` в Lean = sampling `P(π(i-j)/M)`
   - Нужен Toeplitz по Fourier коэффициентам `T[i,j] = P̂(i-j)`

## Математика (кратко)

### Почему a_star НЕ имеет floor

```
a(ξ) = log π - Re ψ(1/4 + iπξ)

При |ξ| → ∞:
  ψ(z) ≈ log(z)  (стандартная асимптотика)
  Re ψ(1/4 + iπξ) ≈ log(π|ξ|)

Тогда:
  a(ξ) = log π - log(π|ξ|) = -log|ξ| → -∞
  a*(ξ) = 2π·a(ξ) → -∞
```

### Почему P_A ИМЕЕТ floor

```
P_A(θ) = 2π · Σₘ a(θ+m) · w_{B,t}(θ+m)

Окно w_{B,t} = Fejér × heat локализует:
- Для |m| большого: w(θ+m) ≈ 0
- Периодизация обрезает хвост!
- A3_FLOOR доказывает: P_A ≥ c* = 11/10
```

### Два разных Toeplitz

| Тип | Определение | В проекте |
|-----|-------------|-----------|
| **Fourier** | `T[i,j] = ∫ P(θ) e^{-2πi(i-j)θ} dθ` | `rayleigh_v1.lean` ✅ |
| **Sampling** | `T[i,j] = P(π(i-j)/M)` | `Q3/Axioms.lean` ❌ |

Rayleigh bound `⟨Tv,v⟩ ≥ min(P)·‖v‖²` работает **только для Fourier**!

## План фикса

### 1. Удалить `a_star_pos` из chain
- Не использовать в main proof
- Можно оставить для локальных bounds на компактах

### 2. Заменить символ `a_star` → `P_A` в A3 bridge
```lean
-- БЫЛО (неправильно):
h_rayleigh_lower_bound : RayleighQuotient (ToeplitzMatrix M a_star) v ≥ c_star

-- ДОЛЖНО БЫТЬ:
h_rayleigh_lower_bound : RayleighQuotient (ToeplitzFourier M P_A) v ≥ c_star
```

### 3. Использовать `rayleigh_v1.lean` (уже proven!)
- Он использует `ToeplitzEntry` (Fourier коэффициенты)
- Уже доказывает Rayleigh ≥ min(P) для любого P

### 4. Wire together
- `P_A_ge_c_star` (A3_FLOOR) → floor
- `rayleigh_lower_bound` (rayleigh_v1) → Toeplitz Rayleigh
- `weight_sum_le_rho_one` (RKHS_cap) → prime cap
- Вычесть → положительность

## Файлы для изменения

| Файл | Изменение |
|------|-----------|
| `Q3/Axioms.lean` | Убрать/пометить `a_star_pos` |
| `Q3/AxiomsTheorems.lean` | Переписать `A3_bridge_rayleigh` |
| `Q3/Proofs/A3_bridge_rayleigh_first.lean` | Использовать P_A + ToeplitzEntry |

## Статус активов

| Актив | Статус | Использовать |
|-------|--------|--------------|
| `P_A_ge_c_star` | ✅ PROVEN | Да |
| `rayleigh_lower_bound` (v1) | ✅ PROVEN | Да |
| `weight_sum_le_rho_one` | ✅ PROVEN | Да |
| `ToeplitzEntry` | ✅ Fourier | Да |
| `ToeplitzMatrix` | ❌ Sampling | Нет |
| `a_star_pos` | ❌ FALSE | Удалить |

---

*Analysis by Proshka, formatted by Claude, 2026-01-15*
