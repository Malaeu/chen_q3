---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# RKHS Cap Implementation (2026-01-15)

### Insight: t_rkhs_cap must be large for compression decay

**Факт:** при `xi_n = log n / (2π)` имеем
```
exp(-4π² t · xi_n^2) = exp(-t (log n)^2)
```
При `t=1` вклад от `n=2` уже ≈ `exp(-(log 2)^2) ≈ 0.6185`, поэтому `ρ(1) < 1/25`
невозможно при нашей нормировке. Решение — фиксировать **большой** `t`:

```
def t_rkhs_cap : ℝ := 40
```

**Реализация (DONE):** `Q3/Proofs/RKHS_cap_rayleigh.lean`
- `weight_sum_le_rho_one` — весовая сумма ≤ 1/25 через `n^-10` и диадическое разбиение.
- `rkhs_cap_rayleigh_tcap` — Rayleigh cap с `t_rkhs_cap`.
- `A3_bridge_rayleigh_from_weight_sum` — готовый glue для A3.

**Правило:** t_rkhs_cap должен быть **в числителе** (`exp(-t (log n)^2)`), значит t берём **большое**.

---
