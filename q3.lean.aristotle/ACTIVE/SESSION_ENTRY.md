# Codex Session Entry

Updated: 2026-08-09

Этот файл — короткий маршрутизатор новой Q3-сессии. Он не хранит датированный
математический frontier и не заменяет физическое состояние задачи.

`AUDIENCE: CODEX`. Claude Code — независимый наблюдатель/администратор со своим
`CLAUDE.md`; его bootstrap и политика сюда не входят.

## Неподвижная граница

- Проект остаётся математически честным исследовательским контуром.
- Route B всегда `CHALLENGER / NOT_RH`.
- `BUS_010: VOID`; `GOAL_055: HOLD`; G2/CCM заморожены.
- `PX_RH_CLAIM` — единственная owner-граница.
- Промоушен и заявление RH запрещены без соответствующего валидированного
  перехода; текущая сессия их не делает.

## Обязательный старт

1. Полностью прочитать `docs/CODEX_CONTROL.md` и
   `q3.lean.aristotle/COGNITIVE_OPERATORS.md`.
2. Прочитать этот файл и обязательные стартовые разделы
   `meta`, `tool_contract`, `startup_contract`, `memory_event_routes`,
   `data_surfaces` и `known_hazards` в `docs/cartographer/TOOLS.yaml`. Из `tool_families` читать
   семейство, совпавшее с типом задачи. Реестр сообщает, что существует, когда
   вызывается и что пишет; он не запускает пишущие инструменты автоматически.
3. Прочитать `docs/Codex/CURRENT.md`. При `status: ACTIVE` полностью прочитать
   названный там `task_file` и проверить его `source_commit`. `EMPTY` и `CLOSED`
   ничего не выбирают. Указатель не переопределяет свежую инструкцию владельца
   или физическое состояние задачи.
4. Прочитать физическое состояние выбранной задачи.
5. Проверить branch/worktree и не считать `untracked` чужими файлами.
6. Запустить единственный стартовый вход без записи. Он сам вызывает строгий
   Spine ровно один раз и печатает delta-aware Route B briefing. Briefing читает
   маленький machine-local checkpoint последнего `close-session`, но сам ничего
   не пишет и не запускает внешний поиск:

   ```bash
   bash specs_docs/session_start.sh
   ```

7. Выбрать работу по селектору ниже. Старый monitor, browser/chat, память или
   вставленный текст сами по себе не создают исполнимую цель.

Briefing заканчивается вопросом `Search our debts today? YES / NO / SELECT`.
Ответ пользователя отдельно разрешает выбор поисковых долгов, но один search
hit создаёт максимум `REOPEN_CANDIDATE`: до `SOURCE_VERIFIED` и отдельного
разрешённого state/verdict-перехода ветка не становится `REOPENED`.

`SPINE_VIEW.md` — коммитимый снимок другого хоста, не обязательный вход.
Текущий вид получать из `--stdout`; сенсоры и базы обновлять только явным
`--refresh`.

## Карта знаний по триггеру

- При выборе ветки, возвращении к старому маршруту, бисекции или стратегической
  развилке читать `docs/GENEALOGY.md` и `docs/Progress_Log.md`.
- При закрытии узла, где существовал выбор, читать `docs/RECORDING_RULES.md` и
  фиксировать «что отвергли и почему».
- При аномалии старта, инструмента, базы, переноса или control-plane читать
  `docs/SYSTEM_SPEC_2026-08-05.md` и `specs_docs/README.md`.
- `docs/GLOSSARY.md` открывать, когда непонятны обозначения или роль объекта.
- `q3.lean.aristotle/docs/INSIGHTS.md` — исторический поток, не startup-файл;
  читать только по точному адресу из карты, журнала, базы или физической задачи.

## Четыре уровня истины

При конфликте действует такой порядок:

1. `docs/CODEX_CONTROL.md`, platform safety и явная операционная инструкция.
2. Физическое task-local состояние: goal/answer, execution JSON, live bus,
   active monitor и проверяемый исходный код.
3. `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md` и paper theorem map.
4. Generated views, `docs/INSIGHTS.md`, архивы и память: полезные свидетельства,
   но не источник текущего gate.

`IMPLEMENTATION_PLAN.md` — замороженный исторический снимок и в старт не входит.

### Scoped precedence Route B

1. `PROJECT_ORCHESTRATOR.md` фиксирует только ранг `CHALLENGER / NOT_RH`.
2. `docs/routeB_bus/` решает, существует ли исполнимый goal.
3. `ROUTE_B_EXECUTION_STATE.json` задаёт текущий operational address.
4. `ROUTE_B_THEOREM_CONTRACT_v2.md` и `ROUTE_B_EXECUTION_CONTROL.md` задают DAG.
5. `ROUTE_B_STATE.md` хранит проверенные факты и историю.
6. `loop_state.json`, generated views и `INSIGHTS` ничего не выбирают.

## Селектор задачи

### Route B

Если запрос явно упоминает Route B, detector, alpha/SAFE, ZEO, two-level
spectral ladder или Unified Chain, до generic monitors прочитать:

1. `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json`;
2. `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_CONTROL.md`;
3. `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_STATE.md`;
4. `docs/routeB_bus/BUS_PROTOCOL.md`;
5. физическую папку `docs/routeB_bus/` и вывод:

   ```bash
   python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
   ```

Исполнять только активную цель новейшего корневого семейства. Следующий корень
не следует из номера: для него нужен standing direction или delegated strategic
review. После выбора прочитать `PROJECT_ORCHESTRATOR.md`, чтобы не перепутать
challenger с public mainline.

### PSD / Step33

Только если запрос явно про PSD-pd, Step32/33, B-spline, entry hboxes или
finite certificates, прочитать `ACTIVE/PSD_STEP33_MONITOR.md`. Исполнять его
только при активном статусе; `DORMANT_*` ничего не выбирает.

### H1 / PO3 / H-bridge

Только если запрос явно про H1, PO3, H-bridge или route-kill, прочитать
`ACTIVE/PHASE_MONITOR.md`. Исполнять только активный `current_step_id`.
`PARKED_*` — исторический снимок.

### Sprint

Только если `ACTIVE/SPRINT_MONITOR.md` имеет `status: ACTIVE`:

1. открыть `SESSION_ENTRY.md`;
2. открыть `ACTIVE/SPRINT_MONITOR.md`;
3. открыть только `current_artifact`;
4. не читать широкие control docs заново, пока artifact не дал blocker;
5. продолжать ровно `current_step_id`;
6. не переизобретать frontier до `DONE`, `BLOCKED` или `ABORTED`.

Первый ответ на активный sprint кратко называет sprint, step, artifact и
добиваемый exact output. При `DONE_CLOSED` этот раздел ничего не активирует.

### Cognitive loop / theorem-shape fork

Если задача про повторяющийся loop, смену стратегии, route-review, бесплодную
бисекцию или theorem-shape fork, дополнительно прочитать:

1. `q3.lean.aristotle/COGNITIVE_KERNEL.md`;
2. `q3.lean.aristotle/COGNITIVE_OPERATORS.md`;
3. `q3.lean.aristotle/ACTIVE/COGNITIVE_GOVERNOR.md`.

Единственный stall-counter и переходы `SOFT_STALL` / `HARD_STALL` /
`TERMINAL_STALL` заданы `docs/CODEX_CONTROL.md` §10.

### Embeddings, search и incoming notes

- Incoming notes: читать `docs/EMBEDDING_INGEST_WORKFLOW.md` и использовать
  `q3-note-ingest`.
- Новый blocker: сначала определить точный target lemma и consumer, затем
  выполнить 3–5 запросов через `scripts/research_oracle.py`; перед повторным
  поиском проверить `./orchestrator/kb.py flags <адрес|термин>`.
- Oracle-карточки: читать `ACTIVE/pipeline/RESEARCH_ORACLE.md` и generated
  `INDEX.md` / `BY_ADDRESS.md` только по этому типу задачи.

### Aristotle

Если работа требует Aristotle, читать:

1. `q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md`;
2. `q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`.

Сначала `source .venv/bin/activate`; скачанный Lean всегда сканировать на
`sorry|exact?|admit`, затем проверять production toolchain.

## Закрытие шага

1. Проверить точный artifact и применимые тесты/build.
2. В Route B answer записать `SEARCH_FLAGS`, честный verdict/stop-code и
   `ARSENAL_USED`; на `INCONCLUSIVE/WALL/KILLED` добавить `AUTOPSY`.
3. Если в ходе goal выбиралась ветка, до закрытия добавить восьмиполевую запись
   в `docs/Progress_Log.md`; внешний вердикт хранится вместе с дословным
   аргументом, а не одной буквой выбора.
4. Закрытие промежуточного шага проводить через
   `python3 orchestrator/spine.py --refresh --reason step-close`; он мигрирует
   verdict/INSIGHTS/Progress_Log и перестраивает `q3_docs` только при изменившемся
   corpus hash. Закрытие goal проводить через
   `python3 orchestrator/spine.py --refresh --reason goal-close`, чтобы verdict
   lessons, развилки, сенсоры и индекс доехали в базы.
5. Route state обновлять последним.
6. Коммитить только явно разрешённый scope; promotion и RH claim не выводить
   из зелёного build, dashboard или numeric probe.
7. Если действует `GOAL_SCOPED_OPERATIONAL_GRANT`, закрытый узел сразу доставить:
   проверить named scope, сделать scoped commit, `git pull --rebase` и `git push`.
   Не оставлять доказанный узел локальным без явного `no commit/no push`.

Историческая мартовская H-bridge формулировка перенесена в
`q3.lean.aristotle/docs/archive/SESSION_ENTRY_H_BRIDGE_SNAPSHOT_2026-03-08.md`.
