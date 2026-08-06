# SESSION_START_MAP — полная карта старта сессии

Рабочий файл для пошагового разбора. Часть A — дословный отчёт Кодекса, часть B — сверка с
кернелом (уже даёт находку), часть C — каркас, который заполняется по шагам.

**Область:** снято с **Linux**-тела 2026-08-06. Mac-версия **не снята** — там другой
конфиг (`sandbox_mode`, `notify`, встроенный браузер), и порядок может отличаться.
Не переносить выводы на Mac без отдельной проверки.

---

## Часть A — как Codex сам описал свой старт (verbatim, 2026-08-06, Linux)

Сохранено дословно как артефакт самоописания: важно именно то, что он **считает** своим
порядком, а не то, что записано в правилах.

```text
Корень репозитория: /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean

ОБЯЗАТЕЛЬНЫЙ ПОРЯДОК КАЖДОЙ СЕССИИ
1. AGENTS.md — тонкий bootstrap-указатель.
2. docs/CODEX_CONTROL.md — читать полностью; проверить единственность, STATUS: ACTIVE, Spine wiring.
3. SESSION_ENTRY.md — читать полностью; определяет условную ветку задачи.
4. Прочитать task-specific state по правилам ниже.
5. Затем общий project state строго в таком порядке:
   5.1 q3.lean.aristotle/PROJECT_ORCHESTRATOR.md
   5.2 IMPLEMENTATION_PLAN.md
   5.3 q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md
   5.4 q3.lean.aristotle/docs/INSIGHTS.md
6. Прочитать текущий generated Spine: orchestrator/state/SPINE_VIEW.md
7. Выполнить strict validation без записи:
   python3 orchestrator/spine.py --strict --reason session-start --stdout
8. Проверить branch, worktree, runtime/chat handle и физический site baton:
   orchestrator/state/CHANNEL_RUNTIME.json · git branch --show-current
   git status --short --branch · task-local handoff/baton, если существует.

ЕСЛИ ЗАДАЧА ПРО ROUTE B (до generic monitors):
1. …/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json
2. …/ROUTE_B_EXECUTION_CONTROL.md
3. …/ROUTE_B_STATE.md
4. …/bus/BUS_PROTOCOL.md
5. физическую папку …/bus
6. routeb_status.py --check
Исполнима только минимальная физическая goal без answer. Если её нет: NO_OPEN_BUS_GOAL / STOP.

ЕСЛИ ЗАДАЧА ПРО PSD/Step33:
1. ACTIVE/PSD_STEP33_MONITOR.md
2. указанный там request: ACTIVE/requests/step33_bootstrap/node.md
3. указанный report: …/report.md
4. все пути из поля current_artifact
Сейчас monitor: status ACTIVE, current_step_id Step33A.1 — но читается только для PSD/Step33.

ЕСЛИ ЗАДАЧА ПРО H1/PO3/H-bridge:
1. ACTIVE/PHASE_MONITOR.md
2. если ACTIVE — current_artifact, worker_request, worker_report
Сейчас PARKED_CLOSED, работой не управляет.

GENERIC SPRINT:
- ACTIVE/SPRINT_MONITOR.md — operational source только при status ACTIVE. Сейчас DONE_CLOSED.

ДОПОЛНИТЕЛЬНЫЕ УСЛОВНЫЕ ФАЙЛЫ
stalled loop / route-review: COGNITIVE_KERNEL.md · COGNITIVE_OPERATORS.md · ACTIVE/COGNITIVE_GOVERNOR.md
embeddings:                  docs/EMBEDDING_INGEST_WORKFLOW.md
Oracle:                      ACTIVE/pipeline/RESEARCH_ORACLE.md · oracle_questions/INDEX.md ·
                             oracle_questions/BY_ADDRESS.md · docs/insights/h1_po3_route_ladder_2026_04_19.md
Aristotle:                   ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md · aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md

Если control отсутствует, не ACTIVE, дублирован или strict validation падает — работа не
начинается: CODEX_CONTROL_UNAVAILABLE_OR_AMBIGUOUS.
```

---

## Часть B — сверка с кернелом: первая находка

`docs/CODEX_CONTROL.md` §3 «Session bootstrap and disk-wins selection» описывает **пять**
шагов общими словами:

```text
1. Read the active executor control completely.
2. Read SESSION_ENTRY.md, the task-specific physical state, and the current generated Spine view.
3. Run strict control/runtime validation.
4. Inspect Git branch, worktree, and site baton.
5. Select work from physical on-disk state.
```

**Расхождение:** шаг 5 отчёта — «общий project state строго в таком порядке» из четырёх
файлов — **в кернеле отсутствует полностью**. Кернел знает только «task-specific physical
state»; про `PROJECT_ORCHESTRATOR`, `IMPLEMENTATION_PLAN`, `PAPER_MAINLINE_TRACKER` там нет
ни слова.

При этом три из четырёх файлов этого шага мертвы:

| Файл шага 5 | Последняя правка |
|---|---|
| `PROJECT_ORCHESTRATOR.md` | 2026-07-10 |
| `IMPLEMENTATION_PLAN.md` | **2026-04-27** |
| `PAPER_MAINLINE_TRACKER.md` | **2026-03-15** |
| `INSIGHTS.md` | 2026-08-06 (живой) |

То есть исполнитель на каждом старте читает четыре файла, которых нет в его собственном
каноническом кернеле, и три из них показывают состояние проекта весенней давности.

Откуда шаг взялся: почти наверняка из раздела `SINGLE ENTRY POINT` старого `CLAUDE.md`
(схлопнут в указатель 2026-08-06) либо из `SESSION_ENTRY.md` (не менялся с января).

---

## Часть C — каркас пошагового разбора

Заполняется по одному шагу за раз. Для каждого: зачем нужен, что на входе, что на выходе,
чем это уже покрыто у Прошки/Мифоса, можно ли заменить или интегрировать.

| # | Шаг | Зачем | Вход | Выход | Дубль у Прошки/Мифоса | Вердикт |
|---|---|---|---|---|---|---|
| 1 | `AGENTS.md` | | | | | |
| 2 | `CODEX_CONTROL.md` | | | | | |
| 3 | `SESSION_ENTRY.md` | | | | | |
| 4 | task-specific state | | | | | |
| 5.1 | `PROJECT_ORCHESTRATOR.md` | | | | | |
| 5.2 | `IMPLEMENTATION_PLAN.md` | | | | | |
| 5.3 | `PAPER_MAINLINE_TRACKER.md` | | | | | |
| 5.4 | `INSIGHTS.md` | | | | | |
| 6 | `SPINE_VIEW.md` | | | | | |
| 7 | strict validation | | | | | |
| 8 | branch / worktree / runtime / baton | | | | | |
| RB.1–6 | ветка Route B | | | | | |
| PSD.1–4 | ветка Step33 | | | | | |
| H1.1–2 | ветка PHASE | | | | | |
| SPR | sprint monitor | | | | | |
| C.1–3 | cognitive | | | | | |
| C.4 | embeddings | | | | | |
| C.5–8 | oracle | | | | | |
| C.9–10 | aristotle | | | | | |

**Метод разбора одного шага:** прочитать сам файл → его дату и активность → есть ли то же
самое в системном промпте Прошки (`PROSHKA_SYSTEM_PROMPT_v2.md`) или в кернеле Мифоса
(`PROJECT_INSTRUCTIONS_v3_arsenal.md`) → чем заменяется в текущем пайплайне → вердикт:
оставить / слить / заморозить / переписать.

**Что уже известно** (из `ENTRY_SPEC.md` и `CONDITIONAL_CONTOURS.md`): даты и активность по
всем файлам, состояние условных контуров, что мигрировано в `knowledge.db`. Эти данные
переносить сюда не нужно — на них ссылаться.
