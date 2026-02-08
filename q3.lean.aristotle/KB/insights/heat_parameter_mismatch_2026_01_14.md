---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# ⚠️ КРИТИЧНО: Два разных heat parameter! (2026-01-14, Прошка)

### Insight: t_sym ≠ t_rkhs

В Q3 используются **ДВА РАЗНЫХ** heat parameter:

| Параметр | Значение | Где используется | Зачем |
|----------|----------|------------------|-------|
| `t_sym` | 3/50 = 0.06 | Symbol P_A, A3_FLOOR | Arch smoothing |
| `t_rkhs` | 1 | Prime operator cap | RKHS bound |

**Критическое следствие:**
```
ρ(t_sym = 0.06) ≈ 0.95   ← БОЛЬШОЕ, не годится!
ρ(t_rkhs = 1)   < 1/25   ← маленькое ✅
```

### Почему M₀ не нужен

```
Нужно для A3_bridge: ||T_P|| ≤ c*/4 = 0.275
Имеем при t_rkhs=1: ρ(1) < 1/25 = 0.04

0.04 << 0.275 ✅

Разница Toeplitz - T_P ≥ c* - 0.04 ≈ 1.06 >> c*/4
```

M₀ был нужен для SB-дискретизации. С Rayleigh-first он не нужен.

### Правило

**ВСЕГДА проверять какой t используется:**
- Для symbol/arch → t_sym = 3/50
- Для prime cap → t_rkhs = 1

**НЕ путать!** V1/V4 использовали один t для всего — это ошибка.

---
