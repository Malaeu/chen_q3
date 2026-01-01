# Project Workflow for Q3

This file is the main project workflow; Aristotle is only one tool in the loop.

## Aristotle Integration: Principles

Aristotle берёт **informal математику** (markdown с LaTeX) и генерирует **Lean 4 код**.

**Ключевое правило:** НЕ ссылаться на номера лемм/теорем из LaTeX файлов!
Aristotle не знает про `lem:uniform-arch-floor` или `Theorem 8.17'`.
Нужно давать **полные формулировки** в самом .md файле.

---

## Project Workflow (Decision Loop)

This is the full project loop; Aristotle is only one tool in it.

1. Read the current status:
   - `PROOF_MAP_NEW_KERNEL.md`
   - `A3_FLOOR_ROADMAP.md`
2. Pick the next lemma or step to close.
3. Decide: manual proof vs Aristotle.
   - If short/standard and local, prefer manual.
   - If long/tactical or needs many sublemmas, send to Aristotle.
4. If sending to Aristotle:
   - Prepare the input file, submit it, and keep working in parallel.
   - Try to close the lemma manually while Aristotle runs.
5. When a lemma is closed:
   - Check the lemma file in Lean (`lake env lean <file>`).
   - Integrate into the main Lean project and recheck compile.
6. Record the result:
   - Re-import into DB (`aristotle_db/parse_lean.py`).
   - Update `PROOF_MAP_NEW_KERNEL.md` (status + file link).
   - Update `A3_FLOOR_ROADMAP.md` (advance the active step).
   - If specs changed, update `PROSHKA_REQUEST_3.md` and DB.

This loop repeats until the roadmap is complete.

---

## Структура входного файла

```markdown
# Название теоремы/модуля

## Definitions (Lean код)
```lean
-- Все определения которые нужны
def foo : Type := ...
```

## Theorem Statement
```lean
theorem my_theorem : ... := by sorry
```

## Proof Outline
**Step 1:** Описание шага на естественном языке
**Step 2:** ...

## Key Lemmas (если нужны промежуточные)
```lean
lemma helper1 : ... := by sorry
lemma helper2 : ... := by sorry
```

## Numerical Bounds (если есть конкретные числа)
- constant_1 ≥ 1.5
- constant_2 ≤ 0.06
```

---

## Типы входных файлов

### 1. Definitions Only (T0)
Только определения, без теорем. Aristotle проверит что Lean принимает.

### 2. Single Theorem
Одна теорема с доказательством. Лучший вариант - Aristotle фокусируется.

### 3. Theorem Chain
Несколько связанных лемм → главная теорема. Риск: budget exceeded.

### 4. Axiom-Based
Предыдущие результаты как `axiom`, доказываем только новое.

---

## Работа с аксиомами (ВАЖНО!)

Когда модуль A доказан, для модуля B его результат становится аксиомой:

```lean
-- В модуле B:
-- Это было доказано в модуле A
axiom result_from_A : ∀ x, P x

-- Теперь доказываем новое
theorem new_result : Q := by
  have h := result_from_A ...
  sorry
```

**Паттерн:**
1. Модуль A: доказать `theorem foo : P`
2. Модуль B: объявить `axiom foo : P`, использовать для `theorem bar : Q`

---

## Команды

```bash
# Активация окружения
cd /Users/emalam/Documents/GitHub/chen_q3
source .venv/bin/activate

# Проверить статус всех проектов
# NOTE: project_ids.txt живёт в aristotle_input/
python ~/.claude/skills/aristotle/scripts/status.py

# Отправить новый файл
python ~/.claude/skills/aristotle/scripts/submit.py problem.md

# Мониторинг (каждые 5 минут)
python ~/.claude/skills/aristotle/scripts/watch.py <project_id> --interval 300

# Скачать результат
python ~/.claude/skills/aristotle/scripts/download.py <project_id>

# Итерация (V2 с контекстом V1)
python ~/.claude/skills/aristotle/scripts/iterate.py <project_id> original.md
```

---

## Итеративный процесс

```
V1: Отправляем → Ждём COMPLETE/FAILED
         ↓
    Скачиваем результат
         ↓
    Анализируем: что доказано? где sorry?
         ↓
V2: Добавляем доказанное + hints где застрял
         ↓
    Повторяем 3-6 раз
```

### Шаблон V2:

```markdown
# Theorem V2

## Previously Proven (from V1)
```lean
-- Это Aristotle доказал в V1
theorem helper1 : ... := by
  <proof from V1>
```

## Still Needed
```lean
theorem main_goal : ... := by sorry
```

## Hints
- В V1 застрял на шаге X
- Попробуй использовать lemma Y из Mathlib
```

---

## Организация файлов

```
q3.lean.aristotle/
├── aristotle_input/           # Входные .md файлы
│   ├── A3_FLOOR_v3.md
│   ├── A3_FLOOR_v6.md
│   ├── A3_FLOOR_v8.md
│   ├── A3_FLOOR_v9.md         # legacy, wrong sign
│   ├── A3_FLOOR_v10.md        # correct sign, real defs
│   ├── A3_FLOOR_v11.md        # next iteration (if needed)
│   ├── Q3_FULL_BRIDGE.md
│   └── PROSHKA_REQUEST_3.md   # specs/invariants
│
├── aristotle_output/          # Результаты от Aristotle
│   ├── T0_aristotle.lean
│   ├── A3_aristotle.lean
│   └── ...
│
├── proven/                    # Проверенные доказательства
│   ├── T0.lean
│   ├── A3.lean
│   └── ...
│
├── project_ids.txt            # UUID'ы проектов (mirror of aristotle_input/project_ids.txt)
├── PROJECT_WORKFLOW.md        # Этот файл
└── PROOF_MAP.md               # План модулей
```

---

## Трекинг статуса (обязательный шаг)

После закрытия леммы/модуля **всегда** обновляем три источника статуса:

1. **DB (канонический источник):**
   - `aristotle_db/parse_lean.py import ...` для новых/изменённых файлов.
2. **PROOF_MAP_NEW_KERNEL.md (карта доказательств):**
   - отметить леммы как `proven/in_progress/todo`;
   - проставить ссылки на файлы и версии.
3. **A3_FLOOR_ROADMAP.md (пошаговый план):**
   - закрыть завершённый этап;
   - обозначить следующий активный шаг.

Если меняются инварианты/спеки — обновить `PROSHKA_REQUEST_3.md`
и заново занести спецификации в DB.

---

## Разница между ROADMAP и PROOF_MAP

- **A3_FLOOR_ROADMAP.md** — последовательность шагов (stage-план),
  отвечает на вопрос **"что делаем дальше"**.
- **PROOF_MAP_NEW_KERNEL.md** — карта доказательств и статусов лемм,
  отвечает на вопрос **"что уже закрыто и в каких файлах"**.

DB `aristotle_proofs.db` — источник истины по леммам и статусам,
а ROADMAP/PROOF_MAP — человеческие summaries.

Archive (legacy / old chain):
```
q3.lean.aristotle/archive/
├── input/                     # Старые A3_FLOOR версии и legacy-запросы
├── output/                    # Старые Aristotle результаты
├── lean/                      # Старые цепочки A3_FLOOR (v3-v9 и т.п.)
└── docs/                      # Черновые заметки
```

---

## Частые ошибки

| Ошибка | Причина | Решение |
|--------|---------|---------|
| "not a Lean file" | Забыл INFORMAL | `project_input_type=ProjectInputType.INFORMAL` |
| Budget exceeded | Слишком большой scope | Разбей на модули |
| Ссылка на лемму | Aristotle не знает LaTeX | Дай полную формулировку |
| sorry остались | Не хватило времени | Итерация V2 с hints |

---

## Советы

1. **Один модуль = один фокус.** Не мешать A3 floor с RKHS cap.

2. **Числа явно.** Вместо "существует c_*" писать "c_* := 11/10".

3. **Mathlib imports.** Aristotle знает Mathlib. Указывай какие леммы использовать.

4. **Proof outline важен.** Aristotle следует твоему плану.

5. **Не торопись с V2.** Дождись полного завершения V1.

---

## Типичный workflow для Q3 (NEW_KERNEL)

```
Stage 1:
  ├── A3_FLOOR_v3/v6/v8 (trigamma + deriv foundations)
  └── Fix sign invariants from PROSHKA_REQUEST_3.md

Stage 2:
  ├── A3_FLOOR_v10 (deriv_digamma_eq_trigamma)
  └── deriv_a_neg + strictAntiOn_a (correct sign)

Stage 3:
  ├── numerical bounds for a(1/2), a(3/2), a(5/2), w, tail
  └── feed into A3 floor bound c_* = 11/10
```
