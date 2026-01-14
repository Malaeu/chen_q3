# Project Insights

Важные находки которые нельзя забывать.

---

## Aristotle Strategy

### Insight: Pure Informal > Sandbox

**Дата:** 2026-01-14

**Эксперимент:** Отправили одну задачу (Rayleigh lower bound) двумя способами:
- V1: pure informal markdown
- V2: sandbox с готовыми сигнатурами

**Результат:**
- V1: **ПОЛНОЕ доказательство**, 0 sorry
- V2: только helper lemmas, main theorem sorry

**Причина:** Sandbox заставляет Aristotle работать с ФИКСИРОВАННЫМИ сигнатурами.
Если сигнатура не оптимальна — он застревает.
Pure informal даёт свободу ПЕРЕФОРМУЛИРОВАТЬ теорему как удобнее.

**Правило:** Для сложных теорем использовать pure informal, sandbox только для
простых/изолированных лемм.

---

## A3 Bridge Mathematics

### Insight: RKHS bound недостаточен "из коробки"

**Дата:** 2026-01-14

**Проблема:**
```
A3_bridge требует: (Toeplitz - RKHS) / ||v||² ≥ c*/4

Наивный подход:
- Toeplitz / ||v||² ≥ c* = 1.1 (из Rayleigh + A3_FLOOR)
- RKHS / ||v||² ≤ ρ (из RKHS_contraction)
- Разница ≥ c* - ρ

Но RKHS_contraction.lean даёт:
  ρ = (1 + w_max)/2 = (1 + 2/e)/2 ≈ 0.868

Нужно: c* - ρ ≥ c*/4
       1.1 - ρ ≥ 0.275
       ρ ≤ 0.825

Но 0.868 > 0.825 — НЕ СХОДИТСЯ!
```

**Решение:** Не использовать готовый ρ из RKHS_contraction!

Вместо этого: ВЫБРАТЬ t большое так чтобы ||T_P(t)|| ≤ c*/4 напрямую.

При t → ∞:
- Heat kernel exp(-(ξᵢ-ξⱼ)²/(4t)) → 0 для i≠j
- Off-diagonal terms → 0
- ||T_P|| можно сделать сколь угодно малым

**Математика:**
```
||T_P|| ≤ w_max * (1 + S(t))

где S(t) = ∑_{k≠0} exp(-δ²k²/(4t)) → 0 при t → ∞

Нужно: w_max * (1 + S(t)) ≤ c*/4 = 0.275
       0.735 * (1 + S(t)) ≤ 0.275

Это достижимо при достаточно большом t!
```

**Правило:** Для A3_bridge нужен СВОЙ выбор t, не из RKHS_contraction.

---

## Key Constants Reference

| Constant | Value | Decimal | Source |
|----------|-------|---------|--------|
| c* | 11/10 | 1.1 | A3_FLOOR |
| c*/4 | 11/40 | 0.275 | A3_bridge target |
| 3c*/4 | 33/40 | 0.825 | Max RKHS bound |
| w_max | 2/e | 0.735 | RKHS weight bound |
| ρ (RKHS) | (1+2/e)/2 | 0.868 | RKHS_contraction.lean |

**Warning:** ρ = 0.868 > 3c*/4 = 0.825, поэтому готовый ρ НЕ подходит!

---

## File Organization

### Insight: aristotle_input/ structure

- `*_v1.md`, `*_v2.md` — версии одного запроса
- `project_ids.txt` — трекинг UUID проектов
- Pure informal файлы работают лучше чем sandbox

### Insight: aristotle_output/ naming

- `rayleigh_v1.lean` — winner (полное доказательство)
- `rayleigh_v2.lean` — backup (только helpers)
- Коммитить оба, в commit message указывать какой winner

---

*Обновляй этот файл когда находишь новые insights!*
