# Project Workflow for Q3

Entry point: `PROJECT_ORCHESTRATOR.md` (status + next steps).
This file documents the workflow only.

This file is the main project workflow; Aristotle is only one tool in the loop.
Canonical Aristotle rules live in `ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md`.

## Native subagents

If native Codex subagents are used, they must still respect the existing Q3
control-plane:

- orchestrator remains the main local session;
- subagents must enter through `SESSION_ENTRY.md` and the active
  `PHASE_MONITOR.md` or `SPRINT_MONITOR.md`;
- all parallel math work still flows through
  `ACTIVE/AGENT_PROTOCOL.md` plus `request node -> report file`;
- custom project-scoped agents live in `.codex/agents/`;
- subagents are for parallelization, not for replacing the file-based source of
  truth.

Current CLI note:

- interactive Codex is the preferred place for native subagent spawning;
- in local non-interactive `codex exec`, custom-agent files are visible, but
  explicit custom-agent selection is not yet fully ergonomic/reliable;
- if needed, run a second narrow `codex exec` worker, take its final payload
  from stdout or `--output-last-message`, and let the main orchestrator write
  the `report.md` itself instead of relying on child write-back.

## Aristotle Integration: Principles

Aristotle берёт **informal математику** (markdown с LaTeX) и генерирует **Lean 4 код**.
Полный гайд и актуальные правила: `ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md` (single source).

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

Мини‑шаблон (path‑agnostic):
```python
from pathlib import Path
from aristotlelib import Project
from aristotlelib.local_file_utils import gather_file_imports
import asyncio

ROOT = Path.cwd().resolve()
if not (ROOT / "Q3").is_dir():
    if (ROOT / "q3.lean.aristotle").is_dir():
        ROOT = (ROOT / "q3.lean.aristotle").resolve()
    elif (ROOT / "full" / "q3.lean.aristotle").is_dir():
        ROOT = (ROOT / "full" / "q3.lean.aristotle").resolve()
    else:
        raise RuntimeError("Set ROOT to your q3.lean.aristotle directory")
INPUT = ROOT / "Q3/Proofs/QSpec.lean"

deps = gather_file_imports(INPUT, project_root=ROOT)
context = [str(p) for p in deps] + [
    str(ROOT / "ACTIVE/aristotle/queue/<task>/PROMPT.txt"),
    str(ROOT / "ACTIVE/aristotle/queue/<task>/NODE_BRIEF.md"),
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
python3 q3.lean.aristotle/scripts/aristotle_dag_loop.py --refresh --print-next 10
```

Он создаёт:
- `ACTIVE/aristotle/ARISTOTLE_QUEUE.json` + `ACTIVE/aristotle/ARISTOTLE_QUEUE.md`
- `ACTIVE/aristotle/queue/<task>/PROMPT.txt`
- `ACTIVE/aristotle/queue/<task>/NODE_BRIEF.md`

**Смысл:** агенты берут top‑задачи из очереди и отправляют в Aristotle
через Python API (см. шаблон выше).

---

## Project Workflow (Decision Loop)

This is the full project loop; Aristotle и Прошка — ключевые инструменты.

## Route-kill protocol

Если активная доказательная ветка упирается не во временный technical blocker,
а в настоящий математический тупик, мы больше не зависаем в мета-разговорах.
Делаем ровно это:

1. формулируем точный **kill statement**:
   какая именно theorem-shape ломается и при каком obstruction;
2. записываем это как **kill certificate** в текущий theorem artifact и в
   `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md`;
3. помечаем ветку как `killed` или `rejected` в route registry с pointer на
   exact file/lemma/obstruction;
4. откатываемся к последней реальной развилке из
   `PROJECT_ORCHESTRATOR.md`;
5. активируем следующий лучший живой путь без повторного обсуждения уже
   убитой theorem-shape.

Жёсткое правило:

- убитая ветка остаётся в истории как доказанный тупик;
- её нельзя тихо воскресить без нового explicit obstruction-killer;
- если в route graph есть следующая живая ветка, идём в неё сразу.

## Address numbering / branch coordinates

В проекте адреса вида `D2g29b` надо читать не как “просто номер”, а как
координату внутри дерева доказательства.

Каноническое чтение:

```text
D2g29b
= route D -> layer 2 -> subbranch g -> packet 29 -> subpacket b
```

То есть это **адресная нумерация дерева доказательства**.

### Operational rules

1. Каждый новый нетривиальный theorem-packet получает адрес родителя, а не
   свободное имя сбоку.
2. Дети всегда наследуют адресный префикс родителя.
3. Если parent-node killed, то его subtree killed по умолчанию тоже.

### Kill inheritance

Если killed `D2g`, то по умолчанию killed и все его потомки:

```text
D2g1, D2g2, ..., D2g29, D2g29a, D2g29b, ...
```

Продолжать их как live branch нельзя, пока не сделано одно из двух:

1. rollback к последней живой развилке и переход в sibling-ветку;
2. explicit reopen с новым obstruction-killer и явной записью в route-kill /
   route-reopen history.

### Why this matters

- route-kill чистит не один файл, а целое поддерево;
- live burden локализуется сразу по адресу;
- можно строить дерево идей и смотреть кластеры близкой математики по веткам;
- semantic recall становится быстрее, потому что поиск идёт по соседним
  адресам, а не “по теме вообще”.

Protocol rule:

- в `PHASE_MONITOR`, `PROJECT_ORCHESTRATOR`, request nodes и `docs/INSIGHTS.md`
  новые живые шаги надо именовать адресами дерева;
- killed address трактуется как killed subtree, если не записано обратное.

Это не означает “перебирать бесконечно все мыслимые пути”.
Это означает: честно прорабатывать **все явные живые ветки** текущего
compiled route graph проекта, пока одна не доведена до RH или не убита
строгим certificate.

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
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
source .venv/bin/activate

# Безопасность:
# - НЕ передавай ARISTOTLE_API_KEY через аргументы CLI (утечёт в history/logs).
# - Держи ключ в переменной окружения (например, ~/.bashrc) и просто `source ...`.

# Отправить новый файл (markdown / tex / txt / lean)
aristotle formalize problem.md

# Проверить статус проекта (Python API)
python3 - <<'PY'
import asyncio
from aristotlelib.project import Project

async def main():
    p = await Project.from_id("<project_id>")
    print(p.status, p.percent_complete)

asyncio.run(main())
PY

# Скачать результат (CLI; сохраняем tar.gz архив)
aristotle result <project_id> --wait \
  --destination aristotle_output/<project_id>.tar.gz

# Или скачать результат (Python API)
python3 - <<'PY'
import asyncio
from aristotlelib.project import Project

async def main():
    p = await Project.from_id("<project_id>")
    path = await p.get_solution("aristotle_output/<project_id>.tar.gz")
    print("Downloaded:", path)

asyncio.run(main())
PY

# Распаковать архив и получить output.lean
mkdir -p aristotle_output/<project_id>
tar -xzf aristotle_output/<project_id>.tar.gz -C aristotle_output/<project_id>
```

### После скачивания (обязательная проверка)

`exact?` больше не считаем автоматическим браком. Браком считаем только
`sorry`/`admit`; `exact?` остаётся advisory-сигналом и допускается, если файл
компилируется в реальном проектном контексте.

```bash
# Жёсткие дырки: sorry/admit
rg -n "sorry|admit" aristotle_output/<project_id>/output.lean

# Advisory only: exact?
rg -n "exact\\?" aristotle_output/<project_id>/output.lean || true

# Быстрая компиляция в проекте (если интегрируем)
lake env lean <file>
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
