# CODEX TASK — автономный runner цепи целей, 2026-08-13

> **Не стартовое задание.** `CURRENT.md` на него не указывает и указывать не должен,
> пока владелец не решит иначе. Это записка для тела на Маке: отдать Codex, проверить,
> что работает, и **удалить файл**, когда `AUTOPILOT_000` закроется. В проектную память
> не заводится — план, который выполнят и сотрут, там был бы мусором.
>
> **Происхождение.** Первая редакция плана написана наблюдателем на Linux 13 августа,
> отвергнута вердиктом Прошки того же дня как автоматизация отчётности вместо работы.
> Вердикт целиком: `docs/routeB_bus/proshka/PROSHKA_VERDICT_AUTONOMOUS_GOAL_RUNNER_2026-08-13.md`.
> Ниже — вторая редакция, переписанная по семи починкам вердикта.
>
> **Порядок:** только `AUTOPILOT_000`. Остальные семь этапов записаны, чтобы был виден
> маршрут, и **не разрешены** этим файлом.

---

# AutonomousGoalRunner: детерминированный супервизор цепи целей

## Контекст

Первая редакция этого плана чинила память событий и на этом останавливалась. Вердикт
Прошки от 13 августа: `MEMORY CYCLES ARE SOUND; AUTONOMOUS GOAL CHAIN IS STILL MISSING`.

```
memory_plumbing     RATIFIED_WITH_REPAIRS
unattended_operation REJECTED
reason              A5_DEFERS_TO_OWNER_AND_NO_GOAL_ADVANCE_CONTROLLER_EXISTS
```

Возражение бьёт в корень. План кончался брифингом и развилкой, где решение снова принимал
владелец. По действующему контролю **вся математика, кроме `PX_RH_CLAIM`, уже делегирована
Codex и Прошке**, и возврат владельцу выбора вне этой единственной границы считается
отказом контроля, а не осторожностью.

Формулировка вердикта, которую надо держать перед глазами: **это автоматизирует
отчётность, а не работу**.

Отсутствующий объект назван точно:

```
AutonomousGoalRunner
```

Детерминированный супервизор: выбирает ровно одну физическую цель, запускает под неё один
Codex `/goal`, следит за внутренними циклами, закрывает цель и механически переходит к
следующей source-locked цели. Математику он **не решает** — он двигает байты и состояния.

## Замок терминологии

Прежняя редакция писала «фаза = goal». Это столкновение имён `[C04]`: математическая фаза
уже определена **шестипольным** `phase_key`, и номер цели из сравнения фаз намеренно
исключён — несколько целей могут принадлежать одной фазе и одному живому чату Прошки.

```
MATHEMATICAL_PHASE   шестипольный phase_key; может содержать много целей
GOAL_RUN             один NNN_*.goal.md → NNN_*.answer.md; ровно один Codex /goal
```

`phase == goal` допустимо как разговорное описание `GOAL_RUN` и **запрещено** как имя в
схеме или контроле.

## Что признано верным и сохраняется

| элемент | что делает |
|---|---|
| `record-attempt` | обязательная durable-запись каждого зарегистрированного цикла |
| `record-insight` | только с provenance-ссылками; без родословной не пишется |
| `step-close` | лёгкий refresh после каждого шага |
| `verdict-intake` | миграция вердикта сразу, а не при закрытии цели |
| `docs/TOOLS.md` | генерируемый инвентарь из канонического `TOOLS.yaml` |
| знаменатель миграции | источник / база / не мигрировано, печатать **всегда** |
| без новой таблицы | `journal_entry.kind` — открытое текстовое поле, этого хватает |

## Семь починок к первой редакции

**1 · `A5` «выбор владельца» — убито.** Заменяется автоматической таблицей решений:

```
локальный next_target однозначен   → Codex продолжает сам
нужен theorem-shape fork           → bounded exploration
нужен стратегический вердикт       → одна same-chat call к Прошке
Прошка вернула TRY_/KILL_/RUN_     → Codex применяет
нужна ширина вариантов             → Мифос, только как optional breadth lane
PX_RH_CLAIM                        → стоп, владелец
неясное физическое состояние       → fail-closed, не угадывать
```

**2 · `SESSION_OPEN` не заводится.** В манифесте уже есть `SESSION_START` с
зарегистрированным `codex-session-start`. Параллельное событие создаст две конкурирующие
семантики. **Расширять существующее.** Так же `EXTERNAL_VERDICT` превращается в исполнимый
intake-маршрут, а не дублируется соседним `VERDICT_INTAKE`.

**3 · `git fetch` не прячется внутрь строгого старта.** `session_start.sh` объявлен
строго read-only; `git fetch` меняет refs и является отдельным сетевым действием. Порядок:

```
SYNC_PREFLIGHT    зарегистрированный сетевой инструмент, с operational grant
→ SESSION_START   строго read-only
→ GOAL_SELECT
```

**4 · `step-close` сейчас НЕ лёгкий — проверено диском.** `spine.py:1550-1565`: при
**любом** `--refresh` запускаются `sensors.refresh`, `refresh_q3_docs.py` и
`semantic_index_plants.py`; на `goal-close` gated только дополнительные миграторы. Простое
добавление повода тянуло бы весь дорогой хвост. Нужна явная таблица диспетчеризации:

```
verdict-intake → kb_migrate_verdicts → validate_p9a
step-close     → kb_migrate_verdicts, kb_migrate_journal,
                 kb_migrate_progress_log → validate_p9a
goal-close     → существующий полный конвейер + sensors + индексы
                 + inventory + atoms → validate_p9a
неизвестный повод записи → fail closed
```

**5 · Свободный `--extra KEY=VALUE` не несёт управления.** Для заметок годится, для
машины состояний нет. Поля, критичные для контроллера, закрыты и валидируются:

```
cycle_index · registered_prediction · cheapest_killer
blocker_fingerprint_before · blocker_fingerprint_after
delta_id | NONE · progress_class · cognitive_operator · next_action
```

`--extra` остаётся **неавторитетным приложением**.

**6 · Повтор точной попытки идемпотентен.** Мой тест «второй одинаковый `--id`
отвергается» защищал от коллизий и ломал восстановление после падения:

```
тот же id + тот же canonical payload hash → ALREADY_RECORDED, exit 0
тот же id + другой payload                → ATTEMPT_ID_COLLISION, exit nonzero
```

Иначе после падения между `record-attempt` и `step-close` runner не сможет продолжить.

**7 · Порядок работ перевёрнут.** Не начинать с `record-attempt`. Сначала закрыть контракт
control/state/selector. Иначе получится идеальная память о системе, которая всё ещё ждёт
клика после каждой цели.

## Архитектура

Официальный Codex `/goal` держит один долгий objective до проверяемого условия остановки —
он и есть **двигатель внутри одной цели**, но не планировщик цепи. Он не является
каноническим селектором, распределителем номеров шины, демоном миграции, межцелевым
замком и журналом восстановления. Для последовательности целей нужен внешний слой.

```
┌──────────────────────────────────────────────────────────┐
│ детерминированный супервизор: orchestrator/goal_runner.py│
│ математику не решает; читает состояние, запускает, ждёт  │
└──────────────────────────────────────────────────────────┘
                          │
SYNC_PREFLIGHT → SESSION_START → SELECT_EXACT_GOAL
                          │
                  ОДИН Codex /goal
                          │
ASK_SHELF → EXECUTE → VALIDATE → RECORD_ATTEMPT → STEP_CLOSE
                          │
               ┌──────────┴──────────┐
           продолжить            цель готова
               │                     │
               └─── петля            GOAL_CLOSE
                                     │
                          NEXT_GOAL_SPEC / Прошка
                          ┌──────────┴──────────┐
                    отчеканить след.        жёсткий стоп
```

**Транспорт не строится заново.** `orchestrator/CONDUCTOR.md` уже содержит машину
состояний, возобновление с диска, `queue/`, `inbox/`, сбор из браузера и ритм; `relay.py`
разбирает маркеры `[->CODEX] [->PROSHKA] [->ARISTOTLE] [->WAIT] [->YLSHA]`. Переиспользуем
транспорт и определение завершения, **заменяем устаревший слой решений** текущим
`CODEX_CONTROL`: математику решают Codex и Прошка, супервизор двигает состояния.

## `GOAL_RUNTIME.json`

```json
{
  "schema": "q3_goal_run.v1",
  "goal_run_id": "GOAL058-20260813T120000Z",
  "goal_file": "docs/routeB_bus/058_x.goal.md",
  "goal_sha256": "...",
  "source_commit": "40hex",
  "answer_file": "docs/routeB_bus/058_x.answer.md",
  "mathematical_phase_key_sha256": "...",
  "state": "RUNNING",
  "cycle_index": 3,
  "stall_counter": 1,
  "last_attempt_id": "ATTEMPT_GOAL058_003",
  "next_target": "ExactNextLemma",
  "next_action": "CONTINUE_STEP",
  "operational_grant_id": "AUTOPILOT_GRANT_001",
  "lease": { "holder": "CODEX_MAC", "heartbeat_at": "2026-08-13T12:00:00+02:00" }
}
```

`lease` — замок единственного писателя. Без него два процесса после `git fetch` возьмут
одну цель одновременно. Файл рантайма **не является** источником доказательной истины:
канон остаётся в goal/answer, живой шине, execution state и проверяемом коде.

## Машина состояний

```
BOOTSTRAP   строгая валидация упала     → STOPPED_FAIL_CLOSED
            прошла                      → SELECTING

SELECTING   ровно одна исполнимая цель  → RUNNING
            несколько                   → AMBIGUOUS_GOAL_SET
            нет + есть NEXT_GOAL_SPEC   → MINTING
            нет + нужен вердикт         → REQUESTING_PROSHKA
            нет + нет источника         → NEXT_GOAL_SPEC_MISSING

RUNNING     шаг прошёл, цель открыта    → RUNNING
            шаг упал, починка есть      → RUNNING
            неопределённо               → BOUNDED_EXPLORATION
            жёсткий застой              → REQUESTING_PROSHKA
            условие успеха выполнено    → CLOSING

CLOSING     любой гейт упал             → CLOSE_RETRY_PENDING
            все прошли                  → CLOSED

CLOSED      NEXT_GOAL_SPEC той же фазы  → MINTING
            смена phase_key             → VALIDATE_PHASE_TRANSITION
            PX_RH_CLAIM                 → STOP_OWNER_REQUIRED
            продолжения нет             → STOPPED_CLEAN
```

## Ограниченная автономия `[C12]`

Пределы заданы числами, не зависящими от результата:

```
3 цикла без подтверждённой дельты   → SOFT_STALL
6 циклов без дельты                 → одна same-chat проверка Прошкой
12 циклов всего                     → закрыть эпизод: KILL / TRY / RUN / точный блокер
смена phase_key                     → закрыть контекст GOAL_RUN и валидировать переход
PX_RH_CLAIM                         → обязательная остановка на владельце
```

Совпадает с действующим cycle comparator, ничего нового не вводится.

## Обязательные жёсткие остановки

```
PX_RH_CLAIM · AMBIGUOUS_PHYSICAL_GOAL_SET
PHASE_KEY_CHANGE_WITHOUT_VALIDATED_TRANSITION · MISSING_OPERATIONAL_GRANT
DESTRUCTIVE_OR_PUBLICATION_ACTION · PAID_EXTERNAL_CALL
STRICT_VALIDATION_FAILURE · TWELVE_CYCLE_BUDGET_EXHAUSTED
```

## Как рождается следующая цель `[C09]`

Codex **не сочиняет** следующую цель после результата. Каждый закрытый ответ обязан нести
машинный блок:

```
NEXT_ACTION: CONTINUE_SAME_PHASE | REQUEST_STRATEGIC_REVIEW | STOP
NEXT_GOAL_SPEC:
  target_id · exact_statement_or_task · terminal_consumer
  source_objects · required_inputs · forbidden_shortcuts
  validation · success_condition · failure_code
PHASE_KEY_CHANGE: false
```

`goal_mint.py` только валидирует блок, проверяет адреса источников, механически берёт
следующий свободный номер по протоколу шины, пишет цель и записывает SHA и провенанс.
Теорему он не выбирает. Блока нет — вызывается Прошка или runner останавливается.

**Главный риск, названный вердиктом:** если Codex сам создаёт следующую цель, он начнёт
подгонять маршрут под только что увиденный результат. Поэтому автоматическая чеканка
разрешена **только** из заранее валидированного `NEXT_GOAL_SPEC` или из оперативного
`TRY_/KILL_/RUN_` того же живого чата. Свободное «я думаю, дальше надо…» входом не является.

## Порядок работ — одна цель на этап

```
AUTOPILOT_000  контракт control/runtime: GOAL_RUN ≠ MATHEMATICAL_PHASE,
               operational grant, схема состояния, селектор, четыре закладки.
               Писателя в базу ЕЩЁ НЕТ.
AUTOPILOT_001  record-attempt с закрытыми полями контроллера и идемпотентностью
               по хешу payload; record-insight с провенансом и дедупликацией.
AUTOPILOT_002  разделение поводов refresh; read-only migration_census.py
               с явными счётчиками источник / база / не мигрировано.
AUTOPILOT_003  генерация docs/TOOLS.md; брифинг состояния и выбранной цели.
               Брифинг НЕ выбирает — селектор уже выбрал.
AUTOPILOT_004  runner вхолостую: sense, lock, select, печать точных действий.
               Ни диспетча Codex, ни записей кроме эфемерного тестового состояния.
AUTOPILOT_005  одна живая цель в теневом режиме: Codex /goal исполняет,
               человек не рулит, runner останавливается перед commit/push
               и печатает полную расписку.
AUTOPILOT_006  закрыть, отчеканить, продвинуться: полный closeout,
               commit/push в пределах одного гранта, чеканка следующей цели
               из валидированного NEXT_GOAL_SPEC, запуск следующего /goal.
AUTOPILOT_007  служба и восстановление: launchd на macOS, systemd --user на Linux,
               heartbeat аренды, точный повтор после kill -9 между переходами.
```

## Первый шаг: `AUTOPILOT_000`

Определить операционный контракт `GOAL_RUN`, **не переопределяя** шестипольную
математическую фазу.

**Производит ровно пять вещей:**

```
docs/Codex/AUTOPILOT_GOAL_RUN_CONTRACT.md
orchestrator/goal_runtime.py
orchestrator/tests/test_goal_runtime.py
минимальное валидированное обновление docs/cartographer/TOOLS.yaml
предложенный патч версии CODEX_CONTROL — без молчаливого ослабления
  существующих полномочий и защит
```

**Поведение селектора:**

```
ровно одна исполнимая цель      → выбрать
больше одной                    → AUTOPILOT_AMBIGUOUS_GOAL_SET
нет + валидный NEXT_GOAL_SPEC   → MINT_READY, чеканки пока нет
нет + нет спеки                 → AUTOPILOT_NEXT_GOAL_SPEC_MISSING
смена phase_key                 → PHASE_TRANSITION_REQUIRED
PX_RH_CLAIM                     → OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM
```

**Четыре закладки:**

```
P1  две разные цели с одинаковым шестипольным ключом остаются ОДНОЙ фазой
P2  две исполнимые цели → отказ, fail closed
P3  NEXT_GOAL_SPEC, выбранный после результата и без провенанса источника, отвергается
P4  PX_RH_CLAIM не может продвинуться автоматически
```

**Запрещено на этом шаге:**

```
никакой реализации record-attempt
никакой автоматической чеканки цели
никакого git fetch внутри session_start.sh
никакой развилки владельца вне PX_RH_CLAIM
никакого алиаса phase=goal
никаких правок живых математических целей
```

## Проверка `AUTOPILOT_000`

```bash
python3 -m pytest orchestrator/tests/test_goal_runtime.py -q
python3 orchestrator/goal_runtime.py --selftest
python3 -c "from orchestrator import spine; print(spine.validate_tool_manifest())"
bash specs_docs/session_start.sh
```

```
SUCCESS  GOAL_RUN_CONTRACT_VALIDATED_WITH_FOUR_PLANTS
FAILURE  AUTOPILOT_CONTROL_OR_SELECTOR_GAP
```

Каждый новый инструмент несёт **десять** полей контракта — `spine.py:776-779`, и
`writes: true` при `approval: NONE` **падает** (`spine.py:818`). Ошибка 12 августа была
ровно здесь: проверен `yaml.safe_load` вместо валидатора.

## Зарегистрированные предсказания

```
P-AUTO-1  план в прежнем виде остановится на A5 или после B6      CONFIRMED BY SOURCE AUDIT
P-AUTO-2  после контракта GOAL_RUN первый реальный блокер —
          не запись попытки, а чеканка цели, грант или
          неоднозначность физического состояния                    ЗАРЕГИСТРИРОВАНО
P-AUTO-3  буквальное phase=goal сломает шестипольную семантику
          и переиспользование живого чата                          CONFIRMED BY TYPE AUDIT
```

## Что убито этим вердиктом

```
A5 owner-choice
буквальное phase = goal
git fetch внутри read-only старта
допущение, что step-close уже лёгкий          ← проверено диском, spine.py:1550-1565
семантика контроллера в невалидируемых extras
дублирующие имена событий
свободное автоматическое изобретение целей
```

## Замок §18 — остаётся неразрешённым

Держатель записи — `CODEX`, читатель — `CLAUDE_CODE`, и §18.3 запрещает читателю запускать
`kb_migrate_*.py`. 13 августа я его запустил. Предложенный патч `CODEX_CONTROL` в
`AUTOPILOT_000` обязан либо признать линуксовое тело исполнителем явно, либо оставить
запрет — но разночтения быть не должно, и автономный runner упрётся в это первым.
