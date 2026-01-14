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

**Вывод:** Нельзя использовать готовый ρ из RKHS_contraction для A3_bridge.

Текущий Schur bound имеет нижний порог `w_max`:
```
||T_P|| ≤ w_max * (1 + S(t))
```
Даже при `S(t) → 0` получаем `||T_P|| ≤ w_max ≈ 0.735`, а нужно `≤ c*/4 = 0.275`.

Формула: `exp(-(ξᵢ-ξⱼ)²/(4t))`

При t → 0:
- Argument -(big)/(4×small) = -∞
- exp(-∞) → 0 для i≠j
- Off-diagonal terms → 0

При t → ∞:
- Argument -(big)/(4×large) → 0
- exp(0) → 1
- Off-diagonal terms → 1 (плохо!)

**Математика:**
```
S(t) = ∑_{k≠0} exp(-δ²k²/(4t)) → 0 при t → 0
```

**Правило:** Для A3_bridge нужен ДРУГОЙ (более острый) bound на `||T_P||`,
не только Schur test из RKHS_contraction.

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

## Documentation Discipline

### Insight: Минимум файлов, максимум ясности

- Один entrypoint: `PROJECT_ORCHESTRATOR.md`.
- Инсайды — только здесь (`docs/INSIGHTS.md`).
- Статистика формализации — только `FORMALIZATION_STATS.md`.
- Новые файлы документации НЕ создавать без явной необходимости.

### Insight: Reuse formalization assets

Мы реально копим повторно используемые результаты (леммы, теоремы, definitions).
Это актив: в следующих проектах можно переиспользовать доказанное, а не
переписывать/передоказывать. Поэтому:
- Обновляем `FORMALIZATION_STATS.md` после крупных шагов.
- Фиксируем reusable‑insights здесь.

---

*Обновляй этот файл когда находишь новые insights!*
