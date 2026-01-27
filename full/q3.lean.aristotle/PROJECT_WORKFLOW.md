# Project Workflow for Q3

Entry point: `PROJECT_ORCHESTRATOR.md` (status + next steps).
This file documents the workflow only.

This file is the main project workflow; Aristotle is only one tool in the loop.

## Aristotle Integration: Principles

Aristotle берёт **informal математику** (markdown с LaTeX) и генерирует **Lean 4 код**.

**Ключевое правило:** НЕ ссылаться на номера лемм/теорем из LaTeX файлов!
Aristotle не знает про `lem:uniform-arch-floor` или `Theorem 8.17'`.
Нужно давать **полные формулировки** в самом .md файле.

**ОБЯЗАТЕЛЬНО: Review перед отправкой!**
1. Создать `.md` файл в `aristotle_input/`
2. **ПОКАЗАТЬ пользователю** для проверки
3. Дождаться OK или правок
4. Только после OK → отправлять в Aristotle

НЕ отправлять автоматически! Пользователь должен видеть запрос.

---

## Aristotle CLI/TUI — важные правила (обновлено 2026‑01‑27)

### 1) Несовместимость флагов

В версии `aristotlelib >= 0.7.0`:
- **нельзя** использовать `--no-validate-lean-project`, если включены авто‑импорты.
- Ошибка выглядит так:
  ```
  AssertionError: validate_lean_project must be True when auto_add_imports is True
  ```

**Вывод:** если используем авто‑импорты, **валидация обязательна**.

### 2) Проблема “outermost project root”

Aristotle ищет **самый внешний** Lean‑root.  
На этой машине есть `lakefile.toml` и `lean-toolchain` в `/Users/emalam`, поэтому
CLI думает, что **root = /Users/emalam** → и не видит `Q3.Basic.Defs`, `Q3.Axioms`:

```
ERROR - Could not resolve import 'Q3.Basic.Defs'
```

**Вывод:** CLI с auto‑imports здесь ломается.

### 3) Канонический обход (Python API, без auto‑imports)

**Рекомендуемый способ запуска** для Q3:
- `auto_add_imports=False`
- `validate_lean_project=False`
- `context_file_paths` = транзитивные импорты от **правильного root**

Мини‑шаблон (Mac):
```python
from pathlib import Path
from aristotlelib import Project
from aristotlelib.local_file_utils import gather_file_imports
import asyncio

ROOT = Path("/Users/emalam/Documents/GitHub/chen_q3/sandboxes/projekt_2/full/q3.lean.aristotle")
INPUT = ROOT / "Q3/Proofs/QSpec.lean"

deps = gather_file_imports(INPUT, project_root=ROOT)
context = [str(p) for p in deps] + [
    str(ROOT / "ACTIVE/aristotle_queue/<task>/PROMPT.txt"),
    str(ROOT / "ACTIVE/aristotle_queue/<task>/NODE_BRIEF.md"),
]

async def main():
    pid = await Project.prove_from_file(
        input_file_path=INPUT,
        auto_add_imports=False,
        context_file_paths=context,
        validate_lean_project=False,
        wait_for_completion=False,
        output_file_path=ROOT / "aristotle_output/<task>_aristotle.lean",
    )
    print(pid)

asyncio.run(main())
```

Linux путь менять на `/mnt/hdd01/Soft/GitHub/chen_q3/...`.

---

### 4) Официальные TUI‑режимы и поведение (docs)

**4 режима:**
1. **Fill sorries in a Lean file** — основной режим для DAG‑узлов с `sorry`.
2. **Upload math text** — формализация из естественного языка/документов.
3. **Prompt Aristotle** — свободный промпт на английском (можно приложить Lean‑файл).
4. **View recent attempts** — история попыток/статусы.

**Важно про режим 1 (Fill sorries):**
- Aristotle видит **только транзитивные импорты** указанного файла.
- **Импорты сам не добавляет.**
- **Меняет только указанный файл.**
- **Definitions/data не модифицирует** по умолчанию.

**Selective filling:** если нужно закрыть только часть дыр,
замени остальные `sorry` на `admit` — тогда Aristotle не будет тратить бюджет.

---

### 5) “PROVIDED SOLUTION” (инъекция proof‑sketch)

Aristotle читает **английский скетч** только из **комментария над теоремой**,
помеченного `PROVIDED SOLUTION`.

**Важно:**
- Комментарии **внутри** блока `by` **не читаются**.
- Чем короче и структурнее скетч, тем лучше.

---

### 6) Контрпримеры и отрицания (disprove mode)

Если формулировка ложная, Aristotle может:
- оставить комментарий с **контрпримером**,
- или выдать **доказательство отрицания**.

В таких случаях он может вставить служебный тактик `negate_state`.
Это **сигнал “REFORMULATE”**, а не “дожимать доказательство”.

---

## FRI‑style taint propagation (ERROR bubble‑up)

**Цель:** если в листьях есть `sorry` или контрпример, автоматически “портить”
все зависимые узлы, чтобы не тратить ресурсы на верхний слой.

**Команды:**
```bash
./scripts/numeric_sanity_check.py --write-back   # optional: mark BROKEN on FAIL
./scripts/build_taint_graph.py                   # propagate SORRY/TAINTED/BROKEN
./scripts/build_proof_graph.py                   # reflect statuses in main graph
```

**Правило планировщика:** работать **только** с нижними `SORRY` (без SORRY‑deps).

---

## DAG‑loop (автоматизация очереди)

Добавлен генератор очереди:
```
python full/q3.lean.aristotle/scripts/aristotle_dag_loop.py --refresh --print-next 10
```

Он создаёт:
- `ACTIVE/ARISTOTLE_QUEUE.json` + `ACTIVE/ARISTOTLE_QUEUE.md`
- `ACTIVE/aristotle_queue/<task>/PROMPT.txt`
- `ACTIVE/aristotle_queue/<task>/NODE_BRIEF.md`

**Смысл:** агенты берут top‑задачи из очереди и отправляют в Aristotle
через Python API (см. шаблон выше).

---

## Project Workflow (Decision Loop)

This is the full project loop; Aristotle и Прошка — ключевые инструменты.

### Escape Hatch: Когда застрял → Прошка

**ПРАВИЛО:** Если застрял > 30 минут ИЛИ Aristotle < 10% долго:
1. НЕ продолжать биться головой
2. Сформулировать запрос к Прошке (o3/o4-класс)
3. Прошка даёт: правильную математику, Lean statements, DO NOT DO
4. Создать новый Aristotle запрос по Прошкиному скелету

**Пример (A3_bridge 2026-01-14):**
- Мы: "Нужен Szegő-Böttcher, bound не сходится"
- Прошка: "SB optional! Rayleigh напрямую, ρ(1)<1/25, всё сходится"
- Результат: V3 запрос по Прошкиному скелету

---

### Main Loop

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
   - Run `./scripts/check_axioms.sh` (includes the docs link check).
6. Record the result:
   - Re-import into DB (`aristotle_db/parse_lean.py`).
   - Update `PROOF_MAP_NEW_KERNEL.md` (status + file link).
   - Update `A3_FLOOR_ROADMAP.md` (advance the active step).
   - Update `FORMALIZATION_STATS.md` via `./scripts/update_formalization_stats.sh`.
   - Update `docs/INSIGHTS.md` (reusable insights, no new docs).
   - If specs changed, update `docs/PROJECT_SPECS.md` and DB.

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

# Отправить новый файл (informal markdown)
aristotle prove-from-file --informal --no-validate-lean-project --no-wait problem.md

# Проверить статус проекта (Python API)
python3 - <<'PY'
import asyncio
from aristotlelib import Project

async def main():
    p = await Project.from_id("<project_id>")
    print(p.status, p.percent_complete)

asyncio.run(main())
PY

# Скачать результат (Python API)
python3 - <<'PY'
import asyncio
from aristotlelib import Project

async def main():
    p = await Project.from_id("<project_id>")
    path = await p.get_solution("aristotle_output/<project_id>-output.lean")
    print("Downloaded:", path)

asyncio.run(main())
PY
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
│   └── docs/PROJECT_SPECS.md   # specs/invariants
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

Если меняются инварианты/спеки — обновить `docs/PROJECT_SPECS.md`
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

6. **Застрял → Прошка.** Если Aristotle < 10% более 30 мин — запроси Прошку.

7. **Pure informal > sandbox.** Для сложных теорем informal даёт свободу переформулировать.

---

## Типичный workflow для Q3 (NEW_KERNEL)

```
Stage 1:
  ├── A3_FLOOR_v3/v6/v8 (trigamma + deriv foundations)
  └── Fix sign invariants from docs/PROJECT_SPECS.md

Stage 2:
  ├── A3_FLOOR_v10 (deriv_digamma_eq_trigamma)
  └── deriv_a_neg + strictAntiOn_a (correct sign)

Stage 3:
  ├── numerical bounds for a(1/2), a(3/2), a(5/2), w, tail
  └── feed into A3 floor bound c_* = 11/10
```
