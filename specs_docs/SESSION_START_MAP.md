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

## Часть C — вердикты по шагам

Разбор выполнен 2026-08-06 пятью параллельными read-only проходами по непересекающимся
срезам. **Полный материал с номерами строк и цитатами:
`specs_docs/SESSION_START_AUDIT_2026-08-06.md`** (временный файл, стирается после разбора).
Ниже — только вердикты.

| # | Шаг | Дубль у Прошки/Мифоса | Вердикт | Почему |
|---|---|---|---|---|
| 1 | `AGENTS.md` | нет | **оставить** | 12 строк, актуален, своей политики ноль |
| 2 | `CODEX_CONTROL.md` | да, 4 намеренных (§1.2 аудита) | **оставить** | единственный описывает август 2026; дубли — две стороны контракта. Риск: три копии тегов без генератора |
| 3 | `SESSION_ENTRY.md` | нет; конфликт правила застоя | **переписать** | 21 macOS-путь, два разных «текущих фронтира», указатель на мёртвую шину. Но селектор монитора и приоритет источников — только тут |
| 4 | task-specific state | — | см. RB / PSD / H1 / SPR | |
| 5.1 | `PROJECT_ORCHESTRATOR.md` | нет | **переписать до ~150 строк** | «живая стена» на запаркованном мониторе; леджер решений обрывается 2026-03-08; себя ставит выше `CODEX_CONTROL`, о котором не знает |
| 5.2 | `IMPLEMENTATION_PLAN.md` | нет | **заморозить, убрать из чтения** | 101 день без правок; ACTIVE-задача на `PARKED_CLOSED`; verify с macOS-путём; verify, который не пройдёт никогда |
| 5.3 | `PAPER_MAINLINE_TRACKER.md` | нет | **слить нужное, заморозить** | 144 дня; расходится с оркестратором в том, что такое активный пакет H1. Взять Notation Contract + Section-To-Gate Map |
| 5.4 | `INSIGHTS.md` | нет | **оставить как запись, убрать из чтения** | база строже: 1784 записи, 12 колонок против 4 полей текста. Навигационный блок — пустой заголовок; дописывание идёт со строки 50 764 |
| 6 | `SPINE_VIEW.md` | нет | **слить в 7** | те же байты, что stdout шага 7; закоммиченная копия снята с Мака и расходится с локальной реальностью |
| 7 | strict validation | нет | **оставить, переименовать ярлык** | `validate_p9a()` безусловна; `--strict` даёт одну проверку + квитанцию. `--stdout` не пишет, `--refresh` пишет |
| 8 | branch / worktree / runtime / baton | нет | **рантайм и git оставить, baton заморозить** | `CHANNEL_RUNTIME.json` — единственный носитель handle, писателя в коде нет, протухание не ловится. `find -iname "*baton*"` → ноль файлов |
| RB.1–6 | ветка Route B | нет | **оставить, переписать список файлов** | живая шина `docs/routeB_bus/`, в порядке указана замороженная с 12.07. Арбитр зелёный и на две цели позади |
| RB.4–5 | `BUS_PROTOCOL.md` + `bus/` | нет | **заморозить — после перенаправления `BUS_DIR`** | все три его правила нарушены всеми 14 сегодняшними ответами; ни одна цель на него не ссылается |
| PSD.1–4 | ветка Step33 | нет | **заморозить, сперва починив статус** | единственный монитор, врущий `ACTIVE`; 4,69 МБ / 143 000 строк; 0 коммитов за 30 дней |
| H1.1–2 | ветка PHASE | нет | **заморозить** | честно `PARKED_CLOSED`. Сохранить `kill_writeback` и `rollback_target_if_killed`. Прекратить дописывать в него заметки Route B |
| SPR | sprint monitor | нет | **убрать из порядка** | `DONE_CLOSED`; перенести 6 правил «старта новой сессии» в спеку входа |
| C.1–3 | cognitive | триггер дублирован исполнимо в `spine.stall_decision` + §10 | **ядро+операторы слить, губернатора оставить** | `COGNITIVE_OPERATORS.md` — единственный дом определений `escape_operator`. Губернатор — единственный носитель 7 ловушек и единственный, кого грузят скрипты |
| C.4 | embeddings | нет | **переписать в 10 строк** | правило продвижения заметок — только здесь; без него сырые дампы отравят выдачу оракула |
| C.5–7 | oracle | нет | **индексы оставить, прозу заморозить** | карточки живые до 2026-08-05; 117 адресов, замены в базе нет |
| C.8 | лестница `h1_po3_route_ladder` | нет | **понизить** | словарь адресов нужен, но фронт запаркован — перенести в триггер возобновления H1/PO3 |
| C.9 | `ARISTOTLE_WORKFLOW.md` | нет | **переписать** | вреден как написан: шаг 4 — macOS venv, на Linux падает сразу |
| C.10 | `ARISTOTLE_PROMPT_GUIDELINES.md` | нет | **оставить** | эмпирика семи вариантов, от версии Lean не зависит |

**Сквозные находки** (детали — §0 аудита):

1. **Корень.** Кернел §3 делегирует `SESSION_ENTRY.md` и никогда не проверяет, что тот
   предписывает. Квартет шага 5 — неаудированный подпункт, восходящий к одной строке
   леджера от 2026-03-07.
2. **Три ложных зелёных:** `routeb_status.py --check` = `OK` на протухших данных;
   `P9_STRICT_PASS` называется не тем; `IMPLEMENTATION_PLAN.md:24` — verify, который
   не может пройти никогда.
3. **Одно правило — несколько версий:** порог застоя ×3, словарь операторов ×2,
   контракт шапки ответа шины ×3, порядок квартета ×3 (два из них — в одном файле).
4. **Цена честного старта** ≈ 8 МБ / 200 000 строк, актуальна меньше десятой части.
