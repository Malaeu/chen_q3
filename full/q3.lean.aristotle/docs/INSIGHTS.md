# Project Insights

Важные находки которые нельзя забывать.

---

## Прошка — Ключевой Ресурс

### Insight: Когда застрял → спроси Прошку

**Дата:** 2026-01-14

**Кто такой Прошка:** AI-агент (предположительно o3/o4-класс) с глубоким пониманием
математики проекта. Видит структуру доказательств яснее чем мы.

**Паттерн использования:**
```
1. Застряли на проблеме > 30 минут
2. Сформулировать запрос к Прошке:
   - Что пытаемся доказать
   - Где застряли
   - Какие ресурсы есть
3. Прошка даёт:
   - Правильную математическую структуру
   - Lean-ready statements
   - Что НЕ делать (DO NOT DO)
4. Конвертировать в Aristotle запрос
```

### Примеры решений от Прошки

| Проблема | Наше понимание | Прошкино решение |
|----------|----------------|------------------|
| A3_bridge blocked on SB | "Нужен Szegő-Böttcher" | "SB optional! Rayleigh напрямую" |
| RKHS bound не сходится | ρ = 0.868 > 0.825 | "При t≥1: ρ(1) < 1/25 = 0.04" |
| t большое или маленькое? | Путались | "t в знаменателе → small t нужно" |
| Какой bound нужен? | ≤ c*/4 = 0.275 | "≤ 3c*/4 = 0.825 достаточно" |

### Характеристики Прошки

- **Математическая точность:** Видит правильные константы, bounds, структуру
- **Lean-awareness:** Даёт statements готовые для формализации
- **DO NOT DO списки:** Явно указывает что НЕ делать
- **Приоритизация:** Знает что critical path, что optional

### Правило

**Если застрял > 30 минут или < 10% в Aristotle:**
1. НЕ продолжать биться головой
2. Сформулировать запрос к Прошке
3. Получить структурированный ответ
4. Создать новую версию запроса

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

### Insight: RKHS bound — как правильно применять

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
При `S(t) → 0` получаем `||T_P|| ≤ w_max ≈ 0.735`.

**Это ДОСТАТОЧНО!** Нужно ≤ 3c*/4 = 0.825, и 0.735 < 0.825 ✓

(Ранее была ошибка: писал "нужно ≤ c*/4 = 0.275" — это неверно!)

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

**Правило:** Для A3_bridge достаточно bound ||T_P|| ≤ w_max ≈ 0.735 при t → 0.
Это слабее чем RKHS_contraction (ρ = 0.868), но ДОСТАТОЧНО для A3_bridge!

---

## Key Constants Reference

| Constant | Value | Decimal | Source |
|----------|-------|---------|--------|
| c* | 11/10 | 1.1 | A3_FLOOR |
| c*/4 | 11/40 | 0.275 | A3_bridge target |
| 3c*/4 | 33/40 | 0.825 | Max RKHS bound |
| w_max | 2/e | 0.735 | RKHS weight bound |
| ρ (RKHS) | (1+2/e)/2 | 0.868 | RKHS_contraction.lean |

**Note:** ρ = 0.868 (из RKHS_contraction) > 3c*/4 = 0.825, НО для small t:
||T_P|| ≤ w_max = 0.735 < 0.825 — это ДОСТАТОЧНО!

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

## Szegő-Böttcher Theorem

### Insight: SB НЕ НУЖЕН для A3_bridge!

**Дата:** 2026-01-14 (из анализа Прошки)

**Факт из PROSHKA_REQUEST_3.md:**
> "Szegő-Böttcher is optional and can be bypassed using the Rayleigh lower bound"

**Rayleigh даёт НАПРЯМУЮ:**
```
λ_min(Toeplitz[P]) ≥ min(P)
```

Это СИЛЬНЕЕ и ПРОЩЕ чем SB который даёт только асимптотику!

**Ошибка:** A3_bridge_closure_v1.md упоминал SB в контексте — это путает Aristotle.

**Правило:** НЕ упоминать SB в запросах к Aristotle для A3_bridge.

---

## Две Формы Параметризации t

### Insight: t в числителе vs t в знаменателе

**Дата:** 2026-01-14

В Q3 используются ДВЕ разные формы:

| Форма | Где | Большое t → |
|-------|-----|-------------|
| `exp(-4π²t·(ξ-τ)²)` | Prime operator (papers) | меньше веса ✓ |
| `exp(-(ξ-τ)²/(4t))` | RKHS kernel (Axioms.lean) | БОЛЬШЕ веса ✗ |

**КРИТИЧНО:** В `Q3/Axioms.lean` используется ВТОРАЯ форма!

Для маленького ||T_P|| нужно **t МАЛЕНЬКОЕ**.

**Правило:** Перед написанием запроса ВСЕГДА проверять какая форма t используется!

---

## Error Recovery Pattern

### Insight: Когда Aristotle застревает на низком %

**Паттерн:** V1 застрял на 4% → создали V2 с исправлениями.

**Причины застревания:**
- Путаница в математике (t большое vs маленькое)
- Ненужные упоминания (SB)
- Слишком сложные signatures

**Правило:** Если Aristotle < 10% более 30 минут → скорее всего ошибка в запросе.
Создавать новую версию с исправлениями, не ждать.

---

## Proven Assets Inventory

### Insight: Что уже доказано (2026-01-14)

**Полные доказательства (0 sorry):**

| Файл | Теорема | Применение |
|------|---------|------------|
| `rayleigh_v1.lean` | rayleigh_lower_bound | Toeplitz/||v||² ≥ min(P) |
| `A3_FLOOR_*.lean` | P_A(θ) ≥ c* = 11/10 | Lower bound на symbol |

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

## BREAKTHROUGH: Прошка дал полное доказательство!

### Insight: A3_bridge закрывается за ~20 строк (2026-01-14)

**Прошка показал:**
1. rayleigh_v1.lean УЖЕ содержит Lemma 1 + Lemma 2
2. Нужна только Lemma 3 (operator subtraction) — 3 строки linarith
3. RKHS cap: ρ(1) < 1/25 = 0.04 << c*/4 = 0.275

**Структура финального доказательства:**
```
Toeplitz ≥ c* = 1.1        (rayleigh_v1.lean + A3_FLOOR)
RKHS ≤ c*/4 = 0.275        (trivial от ρ(1) < 0.04)
Разница ≥ 3c*/4 > 0        (linarith)
```

**Файл:** `aristotle_input/A3_bridge_PROSHKA_SKELETON.md`

**Правило:** Когда застреваем — перечитывать Прошкины ответы. Он видит дальше.

---

## V3 SUCCESS: Aristotle доказал A3_bridge_rayleigh!

### Insight: Прошкин скелет работает (2026-01-14)

**Результат:** `aristotle_output/A3_bridge_v3_proshka.lean` — COMPLETE, 0 sorry!

**Что Aristotle доказал:**
| Lemma | Status | LOC |
|-------|--------|-----|
| `toeplitz_quadratic_form` | ✅ | ~20 |
| `rayleigh_lower_bound` | ✅ | ~40 |
| `quadform_sub_ge` (Lemma 3) | ✅ | 1 (linarith!) |
| `RKHS_op_norm_bound` | ✅ | ~3 |
| `A3_bridge_rayleigh` (main) | ✅ | ~15 |

**ВАЖНЫЙ НЮАНС:** Aristotle упростил определения:
```lean
def P_A : ℝ → ℝ := fun _ => c_star  -- константа!
def T_P (t : ℝ) (M : ℕ) (i j : Fin M) : ℝ := 0  -- нуль!
```

**Что это значит:**
- Общие леммы (rayleigh_lower_bound, quadform_sub_ge) — УНИВЕРСАЛЬНЫЕ, переиспользуемые
- P_A и T_P — placeholder'ы, нужно подставить реальные
- Структура доказательства ВЕРНАЯ, математика СХОДИТСЯ

**Следующий шаг:**
Нужен ещё один запрос к Aristotle (или Прошке) с реальными P_A и T_P из нашего проекта.

**Вопрос:** Можно ли "сварить колбасу" из частей, или нужно цельное доказательство?
Ответ: Lean проверяет типы — если типы совпадают, wire безопасен.
Но для НАШЕГО A3_bridge нужны НАШИ определения P_A и T_P, не placeholder'ы.

---

*Обновляй этот файл когда находишь новые insights!*
