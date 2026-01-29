# V1 SURPRISE: Real T_P bounds proven! (2026-01-14)

### Insight: V1 доказал ключевые леммы для real T_P

**Файл:** `aristotle_output/A3_bridge_closure_v1.lean` (project 4c2ed336)

Думали что V1 застрял, но он завершился и доказал важные вещи:

| Lemma | Статус | Значение |
|-------|--------|----------|
| `w_RKHS_le_w_max` | ✅ | w_RKHS(n) ≤ w_max = 2/e |
| `w_max_lt_three_quarters_c_star` | ✅ | **w_max < 3c*/4** (0.7358 < 0.825) |
| `T_P_tendsto_zero_of_ne` | ✅ | T_P(i,j,t) → 0 as t → 0 for i≠j |
| `exists_t_max_row_sum_le_for_M` | ✅ | **∀ M, ∃ t > 0: ||T_P|| ≤ 3c*/4** |

### КРИТИЧЕСКИЙ НЮАНС: t зависит от M!

V1 comment:
> "operator norm of T_P is unbounded for fixed t as M grows"

**Что доказано:** Для каждого ФИКСИРОВАННОГО M существует t(M) такое что ||T_P(t(M))|| ≤ 3c*/4.

**Что требует аксиома:** UNIFORM t для всех M ≥ M₀.

**Вопрос к Прошке:** Достаточно ли t(M) или нужен uniform t? Как A3_bridge используется в T5_Transfer?

### Переиспользуемые леммы из V1

Эти леммы можно wire напрямую в Q3:
- `w_RKHS_le_w_max` — matches `Q3.w_RKHS_le_w_max` в Defs.lean
- `w_max_lt_three_quarters_c_star` — новый результат!
- `T_P_tendsto_zero_of_ne` — off-diagonal decay

---
