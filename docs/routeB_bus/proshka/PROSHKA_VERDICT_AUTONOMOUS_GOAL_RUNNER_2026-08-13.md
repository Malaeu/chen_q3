# STATUS: CONDITIONAL — MEMORY CYCLES ARE SOUND; AUTONOMOUS GOAL CHAIN IS STILL MISSING
```yaml
PRIMARY: BUILD_AUTONOMOUS_GOAL_RUNNER_V1
PRIMARY_COUNT: 1

PLAN_AS_WRITTEN:
  memory_plumbing: RATIFIED_WITH_REPAIRS
  unattended_operation: REJECTED
  reason: A5_DEFERS_TO_OWNER_AND_NO_GOAL_ADVANCE_CONTROLLER_EXISTS

TERMINOLOGY_LOCK:
  mathematical_phase: SIX_FIELD_PHASE_KEY
  codex_execution_unit: GOAL_RUN
  one_goal_file_per_codex_goal: true
  phase_equals_goal: false

DECISION_AUTHORITY:
  non_px_rh_math: CODEX_PLUS_PROSHKA
  owner_fork_outside_px_rh: FORBIDDEN
  px_rh_claim: OWNER_ONLY

AUTONOMY_ARCHITECTURE:
  supervisor: DETERMINISTIC_GOAL_RUNNER
  inside_goal: CODEX_GOAL_MODE
  strategic_gate: SAME_CHAT_PROSHKA_TRY_KILL_RUN
  optional_breadth_lane: MYTHOS_ON_NAMED_FORK_ONLY
  durable_truth: PHYSICAL_GOAL_ANSWER_STATE_PLUS_KNOWLEDGE_DB

REQUIRED_HARD_STOPS:
  - PX_RH_CLAIM
  - AMBIGUOUS_PHYSICAL_GOAL_SET
  - PHASE_KEY_CHANGE_WITHOUT_VALIDATED_TRANSITION
  - MISSING_OPERATIONAL_GRANT
  - DESTRUCTIVE_OR_PUBLICATION_ACTION
  - PAID_EXTERNAL_CALL
  - STRICT_VALIDATION_FAILURE
  - TWELVE_CYCLE_BUDGET_EXHAUSTED

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C12_BOUNDED_POTENTIAL_EXCLUSION

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIMED: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

NEXT_LOCAL_TARGET: AUTOPILOT_000_GOAL_RUN_CONTRACT_AND_SELECTOR
SUCCESS: GOAL_RUN_CONTRACT_VALIDATED_WITH_FOUR_PLANTS
FAILURE: AUTOPILOT_CONTROL_OR_SELECTOR_GAP
```

## VERDICT

Твой план правильно чинит **память событий**: отдельная запись попытки, provenance для инсайта, `step-close`, `verdict-intake`, генерация инвентаря и знаменатели миграции. Это надо сохранить. Но в текущем виде он не даёт режим «Codex работает без моего управления». Он заканчивается брифингом и развилкой, где решение снова принимает владелец. fileciteturn0file0

Это противоречит активному control: все математические решения, кроме финального `PX_RH_CLAIM`, уже делегированы **Codex + Proshka**; возврат `owner choose A/B` вне этой единственной границы считается control failure. citeturn265654view1

Точный недостающий объект:

\[
\boxed{\texttt{AutonomousGoalRunner}}
\]

**AutonomousGoalRunner** — детерминированный supervisor, который выбирает ровно одну физическую цель, запускает для неё один Codex `/goal`, контролирует внутренние циклы, закрывает goal и механически переходит к следующему source-locked goal.

## ROUTE MAP

### Что оставить без изменения идеи

1. **`record-attempt`** — обязательная durable-запись каждого зарегистрированного цикла.
2. **`record-insight`** — только с provenance-ссылками.
3. **`step-close`** — лёгкий refresh после каждого шага.
4. **`verdict-intake`** — миграция вердикта сразу после появления на диске.
5. **`docs/TOOLS.md`** — generated inventory из canonical `TOOLS.yaml`.
6. **migration denominator** — источник / база / не мигрировано, всегда печатать.
7. **без новой таблицы** — это допустимо: `journal_entry.kind` уже является открытым текстовым полем для `insight`, `result`, `in_progress` и других типов. citeturn399021view3

### Что надо убить или переименовать

#### 1. `ФАЗА = GOAL` — semantic collision **[C04]**

В проекте **математическая фаза** уже определена шестипольным `phase_key`. Номер goal специально исключён из сравнения фаз: несколько goals могут принадлежать одной фазе и одному living Proshka chat. citeturn265654view1

Поэтому вводим два разных термина:

```text
MATHEMATICAL_PHASE
  = six-field phase_key;
  может содержать много goals.

GOAL_RUN
  = один NNN_*.goal.md → NNN_*.answer.md;
  ровно один Codex /goal.
```

Фраза «для Codex одна фаза — goal» остаётся допустимой только как разговорное описание **GOAL_RUN**, но не как имя в schema или control.

#### 2. A5 «выбор владельца» — KILL

Этот шаг надо удалить полностью. Автоматическая таблица решений:

```text
локальный next_target однозначен
  → Codex продолжает сам;

нужен theorem-shape fork
  → bounded exploration;

нужен strategic verdict
  → одна same-chat Proshka call;

Proshka вернул TRY_/KILL_/RUN_
  → Codex применяет результат;

нужна ширина вариантов
  → Mythos вызывается автоматически только как optional breadth lane;

PX_RH_CLAIM
  → стоп и владелец;

неясное физическое состояние
  → fail-closed, не угадывать.
```

#### 3. `SESSION_OPEN` дублирует существующий `SESSION_START`

В manifest уже есть `SESSION_START`; в нём уже зарегистрирован `codex-session-start`. Новый параллельный event создаст две конкурирующие семантики. Расширяй существующий event, не создавай `SESSION_OPEN`. Аналогично существующий `EXTERNAL_VERDICT` надо превратить в исполнимый intake-route, а не заводить соседний `VERDICT_INTAKE`. citeturn279031view0

#### 4. `git fetch` нельзя прятать внутрь read-only session start

`session_start.sh` прямо объявлен строго read-only. `git fetch` меняет `.git` refs и является отдельным network-write действием. citeturn977859view1

Правильный порядок:

```text
SYNC_PREFLIGHT       # registered network tool, с operational grant
→ SESSION_START      # строго read-only
→ GOAL_SELECT
```

#### 5. `spine.py --refresh --reason step-close` сейчас не является лёгким

Текущий код запускает sensors, semantic-index refresh и plants при любом `--refresh`; только дополнительные миграторы gated на `goal-close`. Значит простое добавление `reason=step-close` всё равно запустит дорогой полный refresh. citeturn555857view1

Нужна явная dispatch-таблица:

```text
reason = verdict-intake
  → kb_migrate_verdicts
  → validate_p9a

reason = step-close
  → kb_migrate_verdicts
  → kb_migrate_journal
  → kb_migrate_progress_log
  → validate_p9a

reason = goal-close
  → existing full pipeline
  → sensors + indexes + inventory + atoms
  → validate_p9a

unknown write reason
  → fail closed
```

#### 6. Свободный `--extra KEY=VALUE` нельзя использовать для управления

Для заметок он нормален. Для state machine — нет. Controller-critical поля должны быть закрытыми и валидируемыми:

```text
cycle_index
registered_prediction
cheapest_killer
blocker_fingerprint_before
blocker_fingerprint_after
delta_id | NONE
progress_class
cognitive_operator
next_action
```

`--extra` остаётся только non-authoritative appendix.

#### 7. Повтор точной попытки должен быть idempotent

Тест «второй одинаковый `--id` отвергается» хорош против коллизий, но плох для crash recovery. Правило должно быть:

```text
тот же id + тот же canonical payload hash
  → ALREADY_RECORDED, exit 0;

тот же id + другой payload
  → ATTEMPT_ID_COLLISION, exit nonzero.
```

Иначе после падения между `record-attempt` и `step-close` runner не сможет безопасно продолжить.

## REPAIRED ARCHITECTURE

Официальный Codex `/goal` уже подходит для одного долгого objective с verifiable stopping condition и может работать независимо много часов. Codex CLI также рассчитан на repeatable non-interactive automation. Поэтому `/goal` должен быть внутренним двигателем одного goal, а не scheduler всей цепочки. citeturn698286search1turn698286search5

```text
┌──────────────────────────────────────────────────────────────┐
│ deterministic supervisor: orchestrator/goal_runner.py       │
│ не решает математику; читает state, запускает, проверяет     │
└──────────────────────────────────────────────────────────────┘
                            │
                            ▼
SYNC_PREFLIGHT → SESSION_START → SELECT_EXACT_GOAL
                            │
                            ▼
                SET ONE CODEX /goal
                            │
                            ▼
ASK_SHELF → EXECUTE → VALIDATE → RECORD_ATTEMPT → STEP_CLOSE
                            │
                 ┌──────────┴──────────┐
                 │                     │
             continue              goal complete
                 │                     │
                 └────── loop          ▼
                                  GOAL_CLOSE
                                      │
                                      ▼
                         NEXT_GOAL_SPEC / Proshka
                                      │
                         ┌────────────┴────────────┐
                         ▼                         ▼
                   mint next goal             hard stop
```

Существующий `CONDUCTOR.md` уже содержит event-driven state machine, disk resume, queue/inbox, browser harvest и cadence. Не строй второй transport stack. Переиспользуй transport и completion-detection, но замени устаревшую decision layer текущим `CODEX_CONTROL`: математические решения принимает Codex+Proshka, а supervisor только перемещает байты и состояния. citeturn399021view0turn399021view1

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
  "lease": {
    "holder": "CODEX_MAC",
    "heartbeat_at": "2026-08-13T12:00:00+02:00"
  }
}
```

**Lease** — single-writer lock. Без него два процесса после `git fetch` могут одновременно взять один goal.

Файл runtime не является proof truth. Canonical truth остаётся в goal/answer, live bus, execution state и проверяемом коде.

## STATE MACHINE

```text
BOOTSTRAP
  ├─ strict fail                         → STOPPED_FAIL_CLOSED
  └─ pass                                → SELECTING

SELECTING
  ├─ ровно один executable goal          → RUNNING
  ├─ несколько executable goals          → AMBIGUOUS_GOAL_SET
  ├─ goal нет + есть NEXT_GOAL_SPEC       → MINTING
  ├─ goal нет + нужен strategic decision  → REQUESTING_PROSHKA
  └─ goal нет + нет source               → NEXT_GOAL_SPEC_MISSING

RUNNING
  ├─ step passed, goal open               → RUNNING
  ├─ step failed, repair exists           → RUNNING
  ├─ inconclusive                         → BOUNDED_EXPLORATION
  ├─ hard stall                           → REQUESTING_PROSHKA
  └─ success condition met                → CLOSING

CLOSING
  ├─ answer/semantic/build/migration fail → CLOSE_RETRY_PENDING
  └─ all gates pass                       → CLOSED

CLOSED
  ├─ same-phase NEXT_GOAL_SPEC            → MINTING
  ├─ phase-key change                     → VALIDATE_PHASE_TRANSITION
  ├─ PX_RH_CLAIM                          → STOP_OWNER_REQUIRED
  └─ no continuation                      → STOPPED_CLEAN
```

## BOUNDED AUTONOMY **[C12]**

Автономия должна быть ограничена числами, независимыми от результата:

```text
3 cycles without validated delta
  → SOFT_STALL;

6 cycles without validated delta
  → one same-chat Proshka review;

12 cycles total
  → close episode with KILL / TRY / RUN / exact blocker;

phase-key change
  → close old GOAL_RUN context and validate transition;

PX_RH_CLAIM
  → mandatory owner stop.
```

Это уже соответствует действующему cycle comparator. citeturn265654view1

## HOW THE NEXT GOAL IS CREATED **[C09]**

Codex не должен сочинять следующий bus goal после результата.

Каждый закрытый answer обязан иметь machine block:

```yaml
NEXT_ACTION: CONTINUE_SAME_PHASE | REQUEST_STRATEGIC_REVIEW | STOP
NEXT_GOAL_SPEC:
  target_id:
  exact_statement_or_task:
  terminal_consumer:
  source_objects:
  required_inputs:
  forbidden_shortcuts:
  validation:
  success_condition:
  failure_code:
PHASE_KEY_CHANGE: false
```

`goal_mint.py` только:

1. валидирует этот block;
2. проверяет source addresses;
3. механически выбирает следующий свободный номер по bus protocol;
4. пишет goal;
5. записывает SHA и provenance.

Он не выбирает theorem. Если block отсутствует, вызывается Proshka или runner останавливается. Это сохраняет precommit и не превращает automation в post-hoc route fitting.

## IMPLEMENTATION AS ONE GOAL PER STAGE

### `AUTOPILOT_000` — control and runtime contract

```text
GOAL_RUN ≠ MATHEMATICAL_PHASE.
Define autonomous operational grant, state schema, selector and four plants.
No DB writer yet.
```

### `AUTOPILOT_001` — attempt and insight writers

```text
record-attempt with closed controller fields and exact-payload idempotency.
record-insight with provenance and deduplication.
```

### `AUTOPILOT_002` — refresh reasons and migration census

```text
partition verdict-intake / step-close / goal-close pipelines.
add read-only migration_census.py with explicit source/db/unmigrated counts.
```

### `AUTOPILOT_003` — inventory and briefing

```text
generate docs/TOOLS.md.
brief current state and selected goal.
brief does not choose; selector already chose.
```

### `AUTOPILOT_004` — dry-run goal runner

```text
sense, lock, select, print exact actions.
No Codex dispatch and no writes except ephemeral test state.
```

### `AUTOPILOT_005` — one live goal in shadow mode

```text
one real goal;
Codex /goal executes;
human does not steer;
runner stops before commit/push and prints complete receipt.
```

### `AUTOPILOT_006` — close, mint and advance

```text
close goal;
run full closeout;
commit/push within one bounded grant;
mint next goal from validated NEXT_GOAL_SPEC;
start next Codex /goal.
```

### `AUTOPILOT_007` — service and crash recovery

```text
macOS launchd;
Linux systemd --user;
lease heartbeat;
exact replay after kill -9 between every transition.
```

## STRONGEST ATTACK

> Если Codex сам создаёт следующий goal, он начнёт подгонять маршрут под только что увиденный результат.

Да. Это главный риск. Поэтому automatic mint разрешён только из заранее валидированного `NEXT_GOAL_SPEC` или из operative `TRY_/KILL_/RUN_` того же living Proshka phase. Любой свободный «я думаю, дальше надо...» не является входом для mint. **[C09]**

Второе возражение:

> `/goal` уже автономный. Зачем supervisor?

`/goal` удерживает один objective до stopping condition; он не является canonical selector, bus allocator, migration daemon, cross-goal lock или crash-recovery journal. Для последовательности goals нужен внешний детерминированный слой. Это следует и из официальной модели: `/goal` управляет durable objective внутри run, тогда как CLI предназначен для repeatable automation. citeturn698286search1turn698286search5

## FINAL PROPOSAL

Выбранный путь:

\[
\boxed{
\text{existing transport}
+
\texttt{AutonomousGoalRunner}
+
\text{one Codex /goal per GOAL_RUN}
}
\]

Не начинай с `record-attempt`. Сначала закрой **control/state/selector contract**. Иначе получишь идеальную память о системе, которая всё ещё ждёт твоего клика после каждого goal.

### Registered predictions

```text
P-AUTO-1:
  CONFIRMED BY SOURCE AUDIT.
  План как написан остановится на A5 или после B6, потому что owner-choice
  и goal-advance controller отсутствуют.

P-AUTO-2:
  REGISTERED.
  После GOAL_RUN contract первый реальный blocker будет не запись попытки,
  а goal mint / operational grant / physical-goal ambiguity.

P-AUTO-3:
  CONFIRMED BY TYPE AUDIT.
  Буквальное phase=goal сломает six-field phase semantics и living-chat reuse.
```

## CODEX DIRECTIVE

```text
/goal Close AUTOPILOT_000_GOAL_RUN_CONTRACT_AND_SELECTOR.

Read first:
  docs/CODEX_CONTROL.md
  q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md
  docs/cartographer/TOOLS.yaml
  docs/Codex/CURRENT.md
  orchestrator/CONDUCTOR.md
  /mnt/data/Pasted text.txt if available; otherwise use the owner-provided plan.

Task:
Define the operational GOAL_RUN contract without redefining the six-field
mathematical phase.

Produce only:
  1. docs/Codex/AUTOPILOT_GOAL_RUN_CONTRACT.md
  2. orchestrator/goal_runtime.py
  3. orchestrator/tests/test_goal_runtime.py
  4. the minimum validated update to docs/cartographer/TOOLS.yaml
  5. a proposed CODEX_CONTROL version bump patch, but do not silently weaken
     existing authority or safety gates.

Required selector behavior:
  - exactly one executable physical goal -> select;
  - more than one -> AUTOPILOT_AMBIGUOUS_GOAL_SET;
  - no goal + valid NEXT_GOAL_SPEC -> MINT_READY, no mint yet;
  - no goal + no spec -> AUTOPILOT_NEXT_GOAL_SPEC_MISSING;
  - phase-key change -> PHASE_TRANSITION_REQUIRED;
  - PX_RH_CLAIM -> OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM.

Required plants:
  P1. Two different goal numbers with identical six-field phase key remain
      one mathematical phase.
  P2. Two executable goals fail closed.
  P3. NEXT_GOAL_SPEC chosen after outcome but lacking source provenance is rejected.
  P4. PX_RH_CLAIM cannot advance automatically.

Forbidden:
  - no record-attempt implementation yet;
  - no automatic goal mint yet;
  - no git fetch inside session_start.sh;
  - no owner A/B fork outside PX_RH_CLAIM;
  - no phase=goal field alias;
  - no edits to live mathematical goals.

Validation:
  python3 -m pytest orchestrator/tests/test_goal_runtime.py -q
  python3 orchestrator/goal_runtime.py --selftest
  python3 - <<'PY'
  from orchestrator import spine
  print(spine.validate_tool_manifest())
  PY
  bash specs_docs/session_start.sh

Success:
  GOAL_RUN_CONTRACT_VALIDATED_WITH_FOUR_PLANTS

Failure:
  AUTOPILOT_CONTROL_OR_SELECTOR_GAP

Report:
  exact files;
  exact tests and stdout;
  control assumptions added;
  plants fate;
  next smallest goal.
```

## META CLOSEOUT

**Что стало меньше?**

«Автоматизировать Codex» сжалось до одного отсутствующего объекта:

\[
\boxed{\texttt{AutonomousGoalRunner}}
\]

и его первого локального замка:

\[
\boxed{\texttt{GOAL\_RUN\_CONTRACT\_AND\_SELECTOR}}
\]

**Что убито?**

- A5 owner-choice;
- literal `phase = goal`;
- `git fetch` внутри read-only startup;
- assumption that `step-close` is already lightweight;
- controller semantics in unvalidated `--extra`;
- duplicate event names;
- free-form automatic goal invention.

**Что нельзя повторять?**

Нельзя строить сначала writers и briefings, оставляя выбор и advance на потом. Это автоматизирует отчётность, а не работу.

**Следующий дешёвый decisive test:**

Four-plant selector selftest до любой записи в `knowledge.db`.

```yaml
iteration:
  target: unattended_codex_by_goal
  status: PROGRESS
  failed_strategy: briefing_plus_owner_choice
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: GOAL_RUN_CONTRACT_AND_SELECTOR
  invariant_learned: mathematical phase and operational goal run are different objects
  forbidden_future_move: encode controller-critical state in free-form extras or owner forks
  next_decisive_test: four-plant read-only selector selftest
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
