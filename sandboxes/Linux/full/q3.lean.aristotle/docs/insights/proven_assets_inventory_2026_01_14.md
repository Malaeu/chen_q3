# Proven Assets Inventory

### Insight: Что уже доказано (2026-01-14)

**Полные доказательства (0 sorry):**

| Файл | Теорема | Применение |
|------|---------|------------|
| `rayleigh_v1.lean` | rayleigh_lower_bound | Toeplitz/||v||² ≥ min(P) |
| `A3_FLOOR_*.lean` | P_A(θ) ≥ c* = 11/10 | Lower bound на symbol |
| `Q3/Proofs/RKHS_cap_rayleigh.lean` | weight_sum_le_rho_one | RKHS cap (t_rkhs_cap=40) |

**Backup Strategy для A3_bridge:**

Если Aristotle застрянет, manual wiring:
```lean
-- Step 1: Toeplitz bound (from rayleigh_v1.lean)
have h_toep : Toeplitz_form / ||v||² ≥ c* :=
  rayleigh_lower_bound M hM P_A hP_cont c* hA3_FLOOR v hv

-- Step 2: RKHS bound for small t (new lemma needed)
have h_rkhs : RKHS_form / ||v||² ≤ 3*c*/4 :=
  RKHS_norm_small_t t ht_small M v

-- Step 3: Combine
linarith
```

**Ключевой gap:** Нужна lemma `RKHS_norm_small_t` показывающая что
для достаточно маленького t, ||T_P|| ≤ 3c*/4.

---
