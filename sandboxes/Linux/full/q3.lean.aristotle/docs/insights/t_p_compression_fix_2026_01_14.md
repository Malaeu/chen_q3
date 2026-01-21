# КРИТИЧЕСКОЕ ИСПРАВЛЕНИЕ: T_P Compression (2026-01-14)

### Insight: Два РАЗНЫХ определения T_P

**Как было в нашем Axioms.lean (НЕПРАВИЛЬНО):**
```lean
T_P i j = sqrt(w_RKHS i) * sqrt(w_RKHS j) * exp(-(ξᵢ - ξⱼ)²/4t)
-- Direct indexing: i,j ∈ Fin M напрямую дают ξᵢ, ξⱼ
-- Проблема: норма растёт с M → uniform t невозможен
```

**Как в Q3 tex / rayleigh_bridge.tex (ПРАВИЛЬНО):**
```lean
T_P^{(M)} i j = ∑ n : Nodes K, w_Q n * Φ_{B,t}(ξₙ) * v_n[i] * v_n[j]
-- Rank-one compression: T_P^{(M)} = ι_M* T_P ι_M
-- v_n[i] = cos(2πk·ξₙ) — проекция на Фурье-базис P_M
-- Норма ≤ ||T_P|| (compression inequality) → uniform t ВОЗМОЖЕН
```

### Ключевое различие

| Аспект | Direct indexing (V1/V4) | Compression (Q3 tex) |
|--------|-------------------------|----------------------|
| Размер | M × M, зависит от M | M × M, но сумма по Nodes K |
| Норма при M → ∞ | → ∞ | ≤ ||T_P|| (bounded!) |
| Uniform t | ❌ Невозможен | ✅ Возможен |

### Почему V1/V4 не закрыли uniform t

V1/V4 доказали `∀M ∃t(M)` для **direct indexing** версии.
Это слабее чем `∃t ∀M≥M₀` из Q3.

Для uniform t нужен **компрессионный аргумент**:
```
||T_P^{(M)}|| ≤ ||T_P|| (compression of self-adjoint operator)
```

### V1/V4 статус

- ✅ `w_RKHS_le_w_max` — универсально полезно
- ✅ `S_off_tendsto_zero` — универсально полезно
- ⚠️ `T_P_norm_lt_three_quarters_c_star` — sanity check, но на неправильном T_P

### Следующий шаг

Переписать T_P в Axioms.lean на compression-версию:
```lean
def T_P_matrix (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :=
  fun i j => ∑ n : Nodes K,
    w_Q n * Phi_Bt B t (xi_n n) * v_n M (xi_n n) i * v_n M (xi_n n) j
```

Нужен мост: w_Q vs w_RKHS, Gaussian vs rank-one

---
