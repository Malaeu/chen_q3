# STATUS: CONDITIONAL — THREE_BODY_LOOP РАТИФИЦИРОВАН ПОСЛЕ РЕМОНТА; ТЕКУЩИЙ CODEX_GRANT НЕ АКТИВИРОВАТЬ
```yaml
PRIMARY: TRY_CODEX_AUTONOMY_LEASE_V1_AFTER_CONTROL_V9_REPAIR
PRIMARY_COUNT: 1

REQUEST:
  ID: REQ-2026-08-21-O
  STATUS_AT_REVIEW: OPEN
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_GIT_BLOB: 062cc6f9930d6804bccbdee2cef39ab3c3d0ed9d

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: c673bef14f3f54ede44e806654056facb9d2efe3
  REQUEST_LAST_CHANGE_COMMIT: 2eb919a0c60f89d01ab39e048dcc7065523cf4e4
  DESIGN_PATH: docs/THREE_BODY_LOOP_DESIGN.md
  DESIGN_GIT_BLOB: 7c30c0053d3ffaa7121b72a347d0c4e4ebc2478c
  CONTROL_PATH: docs/CODEX_CONTROL.md
  CONTROL_VERSION: 8
  CONTROL_GIT_BLOB: b04bfe6e795fbec832dbf9c443cc6dd7a8a6b96b
  SUPPLIER_CONTRACT_PATH: docs/routeB_bus/SUPPLIER_CONTRACT.md
  SUPPLIER_CONTRACT_GIT_BLOB: 0c595527b3a35bf9598a7bd1465dcc74b55c3e76
  AUDIT_REPAIR_COMMIT: d5b28a09af46c97169b8c218d5ccbba2b70f5cf3

DECISION:
  THREE_BODY_ROLE_SPLIT: RATIFIED
  RETURN_PATH_BY_STABLE_REQUEST_ID: RATIFIED_AFTER_BLOB_BINDING
  CURRENT_CODEX_GRANT_AS_WRITTEN: REJECTED
  ACTIVATION_NOW: FORBIDDEN
  REQUIRED_CONTROL_VERSION: 9
  AGENTS_MD_CHANGE: FORBIDDEN
  SECOND_POLICY_KERNEL: FORBIDDEN
  CODEX_CONTROL_REMAINS_SINGLE_SOURCE_OF_TRUTH: true

Q1_C1_AUTONOMOUS_PUSH:
  KERNEL_GATE_ALONE: INSUFFICIENT
  SOURCE_PUSH: ALLOW_ONLY_AS_SEMANTICALLY_QUARANTINED
  DOWNSTREAM_CONSUMPTION_BEFORE_INDEPENDENT_SEMANTIC_GATE: FORBIDDEN
  MAX_KERNEL_GREEN_AWAITING_SEMANTIC_REVIEW: 1

Q2_C3_REQUEST_CHANNEL:
  NONEMPTY_TRIED_ALONE: INSUFFICIENT
  ONE_OPEN_REQUEST_PER_PHASE_BLOCKER: REQUIRED
  BLOCKER_FINGERPRINT: REQUIRED
  EXISTING_STALL_BUDGET_REUSED: true
  REQUEST_BODY_IMMUTABLE: true
  LIFECYCLE_STATE: [OPEN, IN_REVIEW, ANSWERED, DROPPED]

Q3_CODEX_TRIGGER:
  RESUME_LAST: REJECTED_FOR_AUTOMATION
  EXACT_SESSION_ID: REQUIRED
  EXCLUSIVE_WRITER_LOCK: REQUIRED
  IDEMPOTENCY_NONCE: REQUIRED
  EXPLICIT_WORKDIR_BRANCH_TASK_PIN: REQUIRED
  OUTPUT_SCHEMA_AND_FINAL_FILE: REQUIRED
  UNATTENDED_SANDBOX: WORKSPACE_WRITE

Q4_PRIORITY:
  POLICY: SAFETY_THEN_INFLIGHT_THEN_ORIGIN_NEUTRAL_FIFO
  OLDER_OPEN_REQUEST_MAY_BE_OVERTAKEN_BY_NEW_CODEX_REQ: false
  CLAIMED_IN_REVIEW_REQUEST_MAY_BE_PREEMPTED: false
  LINUX_OWNS_TRANSPORT_AND_BATCHING: true
  DIRECT_CODEX_TO_PROSHKA: forbidden

GRANT_SHAPE:
  NAME: CODEX_AUTONOMY_LEASE_V1
  BOUND_TO:
    - control_version
    - branch
    - worktree
    - writer_lock
    - phase_key_hash
    - current_task_path_and_blob
    - allowed_paths
    - explicit_expiry_or_revocation
  GLOBAL_PERMANENT_GRANT: forbidden
  PX_RH_CLAIM: forbidden
  ROUTE_PROMOTION: forbidden
  POLICY_EDITS: forbidden
  PAID_OR_DESTRUCTIVE_ACTIONS: forbidden

MANDATORY_PLANTS:
  - UNINHABITED_ANTECEDENT_REPLAY
  - KERNEL_GREEN_NOT_SEMANTICALLY_ADMITTED
  - WRONG_LAST_SESSION
  - DUPLICATE_TRIGGER
  - DROP_CLAIM_RACE
  - REQUEST_ID_BLOB_DRIFT
  - WRITER_LOCK_COLLISION
  - OLDER_REQUEST_PRIORITY

REGISTERED_PREDICTIONS:
  P_O_1: "The uninhabited-antecedent plant blocks a kernel-green theorem before downstream consumption."
  P_O_2: "Pinned SESSION_ID plus an exclusive lock removes wrong-session and duplicate-run ambiguity."
  P_O_3: "Fingerprint and one-open gates cut judge traffic without blocking genuine fatal walls."
  P_O_4: "The first implementation defect will be lifecycle or writer-lock state, not Codex CLI output parsing."

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C12_BOUNDED_POTENTIAL_EXCLUSION

SCOPE: ABSTRACT
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### Главный вердикт

Архитектура из трёх тел правильная:

```text
Codex     → пишет и проверяет Lean;
Linux     → держит браузер, транспорт, независимый аудит и расписание;
Прошка    → судит только настоящие стены;
владелец  → задаёт операционные границы, CURRENT.md и PX_RH_CLAIM.
```

Она устраняет ручное погоняние, не смешивая роли. Но предложенный `CODEX_GRANT` пока опасно отождествляет три разных факта:

```text
Lean kernel принял proof term;
source можно запушить;
математическое утверждение можно считать закрытым и использовать дальше.
```

Это три разных гейта. Прецедент `d5b28a09...` является прямым falsifier: все механические проверки прошли, но theorem-контракт требовал глобальную `Continuous`, недостижимую для production `Icc.indicator`-мод с ненулевыми endpoint-значениями. Импликация была корректной, а её несущая посылка — ложной для нужного объекта. `[ABSTRACT][PAPER]`

Поэтому:

\[
\boxed{
\text{kernel-green разрешает карантинный push, но не semantic admission.}
}
\]

`[ABSTRACT][CONDITIONAL]`

---

## Q1 — достаточен ли C1 для автономного пуша?

### Ответ: для записи source — почти да; для продолжения доказательной цепи — нет

Нужны три состояния:

```text
SOURCE_WRITTEN
→ KERNEL_GREEN
→ SEMANTICALLY_ADMITTED(scope = ...)
```

**`SOURCE_WRITTEN`** означает только, что байты и квитанции доехали.

**`KERNEL_GREEN`** означает, что Lean принял proof term, build прошёл, `sorryAx` отсутствует и axiom profile соответствует контракту.

**`SEMANTICALLY_ADMITTED`** означает, что независимое Linux-тело сверило theorem с точным task, source object, terminal consumer, нормировкой, областью, кванторами и `CLOSES/OPENS`. Только этот статус разрешает downstream-узлу потреблять theorem в заявленном scope. `[ABSTRACT][CONDITIONAL]`

### Обязательный semantic gate после C1

Для каждого нового или усиленного load-bearing входа source record обязан содержать:

```yaml
HYPOTHESIS_PROVENANCE:
  <hypothesis>:
    class: SOURCE_FIELD | EXACT_FIT_SUPPLIER | NEW_OPEN_OBLIGATION
    source_or_supplier:
    exact_type:
    consumer:
    production_inhabitant_or_plant:
```

Правила:

1. `SOURCE_FIELD` сверяется с exact source object.
2. `EXACT_FIT_SUPPLIER` проходит существующий `supplier_preflight.py`.
3. `NEW_OPEN_OBLIGATION` обязана появиться в `OPENS`; она не может тихо считаться закрытой.
4. Для receiver/bridge нужен либо exact production inhabitant, либо plant, показывающий достижимость antecedent на нужном классе.
5. Если antecedent не имеет source/supplier/inhabitant, результат классифицируется только как abstract conditional receiver и не закрывает source-specific node.

Именно этот гейт поймал бы ложную глобальную `Continuous`: supplier существовал только для `ContinuousOn` на `Icc`, а production inhabitant глобальную continuity не удовлетворял. Это применение **C10**: kernel проверил удобную импликацию, но consumer требовал другой, реально обитаемый объект. `[ABSTRACT][PAPER]` **[C10]**

### Карантинный барьер

Разрешается один push `KERNEL_GREEN`, ожидающий независимого semantic gate. Пока он не принят:

```text
Codex не строит theorem, который зависит от этого commit;
Linux не отмечает source-specific gap закрытым;
Spine/ledger не повышает статус;
следующий математический node не стартует.
```

Лимит:

```text
MAX_KERNEL_GREEN_AWAITING_SEMANTIC_REVIEW = 1
```

Иначе автономный контур может быстро построить пять корректных theorem поверх одной ложной посылки. `[ABSTRACT][CONDITIONAL]`

### Ремонт C4

`statement нетронут` необходимо, но недостаточно. Tactical repair означает буквально:

```text
proof body / tactics only;
statement unchanged;
hypotheses unchanged;
imports unchanged;
definitions unchanged;
public surface unchanged;
source object and consumer unchanged;
не более двух попыток.
```

После второго красного гейта — стоп и wall report. Это сохраняет NIGHT_GRANT-границу и не позволяет «тактически» подменить theorem. `[ABSTRACT][CONDITIONAL]`

---

## Q2 — превратится ли C3 в канал спама?

### Ответ: да, если оставить только непустой `TRIED`

Строку `TRIED` можно заполнить двумя слабыми попытками. Это не доказывает, что локальные способы исчерпаны.

Новый канал не должен изобретать отдельную политику. Он обязан переиспользовать уже действующие объекты `phase_key`, `blocker_fingerprint`, `PROGRESS_DELTA` и stall budget из `CODEX_CONTROL`. `[ABSTRACT][PAPER]`

### Eligibility для `CODEX_REQ`

Запрос допустим только в одном из случаев:

```text
A. FATAL / source identity ambiguity / trust defect:
   немедленный wall;

B. HARD_STALL:
   шесть зарегистрированных no-delta cycles на одном blocker fingerprint;

C. operative review gate:
   ровно тот случай, который текущий CODEX_CONTROL уже разрешает.
```

Обязательные поля:

```yaml
CODEX_REQ:
PHASE_KEY_HASH:
BLOCKER_FINGERPRINT:
SOURCE_OBJECT:
TERMINAL_CONSUMER:
WALL:
TRIED:
ASK_SHELF_RECEIPT:
CHEAPEST_KILLER_RUN:
PROGRESS_DELTAS:
NEED:
BLOCKS:
REQUEST_BLOB:
SOURCE_COMMIT:
```

Ограничения:

```text
один OPEN/IN_REVIEW request на (phase_key, blocker_fingerprint);
один outstanding CODEX_REQ на живую Codex-сессию;
повтор с тем же fingerprint запрещён без нового validated delta;
одна exploration review на phase/blocker, как уже задано control v8.
```

Это не новый произвольный счётчик. Это reuse существующего bounded-exploration budget. Принцип **C12** выполняется: количество запросов ограничено независимо от того, насколько долго агент переименовывает одну стену. `[ABSTRACT][CONDITIONAL]` **[C12]**

### В текущей схеме не хватает состояния `IN_REVIEW`

Три состояния `OPEN / ANSWERED / DROPPED` имеют race:

```text
Linux прочитал OPEN и отправил судье;
Codex в ту же минуту нашёл обход и записал DROPPED.
```

Судья уже работает вхолостую.

Нужен жизненный цикл:

```text
OPEN → IN_REVIEW → ANSWERED
  └──────────────→ DROPPED
```

После `IN_REVIEW` Codex не может ставить `DROPPED`; он может записать `RESOLVED_LOCALLY_AFTER_CLAIM`, но review завершается и получает честный score.

### Request body неизменяем; state — отдельный CAS-объект

Нельзя переписывать уже запушенный `CODEX_REQ_*.md`: supplier contract делает pushed artifacts append-only.

Использовать:

```text
CODEX_REQ_<id>.md                 immutable body
CODEX_REQ_STATE_<id>.yaml        small mutable lifecycle object
CODEX_ANSWER_<id>.md              immutable answer
```

`CODEX_REQ_STATE` обновляется compare-and-swap по предыдущему blob. Linux сначала атомарно меняет `OPEN → IN_REVIEW`, затем отправляет запрос. Codex может сделать `OPEN → DROPPED` только до claim. Конфликт обновления одного state-файла останавливает обе стороны и требует pull/re-evaluation. `[ABSTRACT][CONDITIONAL]`

### Одного ID недостаточно

Ответ обязан связывать:

```yaml
ANSWERS_REQ:
REQUEST_BLOB:
REQUEST_SOURCE_COMMIT:
PHASE_KEY_HASH:
BLOCKER_FINGERPRINT:
VERDICT_PATH:
VERDICT_BLOB:
DECISION:
NEXT_NODE:
FORBIDDEN:
ANSWER_SCHEMA_VERSION:
```

Идентификатор без request blob допускает тихую замену текста под тем же ID. Это прямой **C09**-дефект: объект должен быть зафиксирован до исхода, а не после появления ответа. `[ABSTRACT][CONDITIONAL]` **[C09]**

---

## Q3 — есть ли щель в `codex exec resume --last`?

### Ответ: да. `--last` нельзя использовать как production identity

Официальный Codex CLI позволяет продолжить либо конкретный `SESSION_ID`, либо наиболее свежую сессию через `--last`; `--last` выбирает most recent session в текущем working directory. Поэтому он удобен вручную, но не является устойчивым идентификатором в трёхтельном контуре. `[ABSTRACT][PAPER]`

Если в одном workdir запускалась другая non-interactive или interactive сессия, «последняя» может быть не той, что владеет текущим task. Факт, что `--last` scoped по cwd, уменьшает риск, но не убирает его.

Обязательная команда:

```bash
codex exec resume "$CODEX_SESSION_ID" \
  -C "$REPO" \
  --sandbox workspace-write \
  --json \
  --output-schema "$SCHEMA" \
  -o "$FINAL_REPLY" \
  "<typed follow-up containing REQ_ID, answer blob and task pin>"
```

Официальная документация также подтверждает, что `-o` пишет финальное сообщение в файл, `--output-schema` валидирует его форму, а `--json` выдаёт machine-readable events. Для unattended local work она рекомендует `--sandbox workspace-write` и предупреждает не использовать `--yolo` вне отдельной hardened sandbox. `[ABSTRACT][PAPER]`

### `pgrep -f "codex --yolo"` — не lock

Он имеет два дефекта:

1. ловит только конкретное написание команды и пропускает другие Codex-процессы;
2. между проверкой и запуском существует race.

Нужен один exclusive launcher lock, удерживаемый весь runtime:

```yaml
LOCK:
  worktree:
  branch:
  writer_body:
  pid:
  process_start_time:
  codex_session_id:
  task_path:
  task_blob:
  phase_key_hash:
  base_head:
  run_id:
  trigger_nonce:
```

Рекомендуемый механизм на Linux:

```text
flock или atomic mkdir;
stale recovery только после проверки PID + start time;
никаких двух writer bodies в одном worktree;
Linux пишет answer/task только после передачи write lock.
```

### Exactly-once trigger

Каждый wake event несёт:

```text
RUN_ID
TRIGGER_NONCE
SOURCE_EVENT_COMMIT
ANSWER_BLOB
```

Watcher хранит последний consumed event. Повторная доставка того же push/notification становится no-op. Изменившийся `HEAD`, task blob, phase hash или control version до запуска означает stop, а не «продолжить по памяти». `[ABSTRACT][CONDITIONAL]`

---

## Q4 — приоритет CODEX_REQ против Linux REQ

### Ответ: отдельной привилегированной очереди для Codex не создавать

Приоритет:

```text
P0  integrity/safety stop:
    receipt mismatch, red gate, writer-lock collision, rebase conflict,
    control drift, PX_RH/policy boundary.
    Это не запрос судье; контур останавливается.

P1  уже IN_REVIEW:
    завершить transport и return path; не прерывать его новым вопросом.

P2  все ранее OPEN судейские запросы:
    origin-neutral FIFO по immutable creation commit/time.
    Старый Linux/owner REQ не обгоняется новым CODEX_REQ.

P3  новые eligible CODEX_REQ и Linux REQ:
    Linux объединяет 2–4 связанных wall-items в один same-chat batch,
    сохраняя каждый request ID и выдавая отдельный CODEX_ANSWER на каждый ID.
```

То есть источник запроса не даёт приоритет. Приоритет создают безопасность, уже начатый transport и возраст. Это согласуется с текущим протоколом очереди: OPEN-запросы разбираются от старшего к младшему. `[ABSTRACT][PAPER]`

Codex никогда не обращается к Прошке напрямую. Linux остаётся единственным transport owner и решает batching, но не меняет математический payload запроса без ссылки на исходный request blob. `[ABSTRACT][CONDITIONAL]`

---

## Дополнительная обязательная правка — не вечный грант, а bounded lease

Текущий `CODEX_CONTROL v8` знает `GOAL_SCOPED_OPERATIONAL_GRANT`. Предложенный глобальный бессрочный `CODEX_GRANT` шире этого объекта и поэтому не может быть активирован как side document.

Ремонт:

```yaml
CODEX_AUTONOMY_LEASE_V1:
  grant_id:
  control_version: 9
  branch:
  worktree:
  writer_lock_holder: CODEX
  phase_key_hash:
  current_task_path:
  current_task_blob:
  allowed_paths:
  activation_commit:
  expires_on:
    - phase_key_change
    - current_task_pin_change
    - control_version_change
    - writer_lock_reassignment
    - explicit_owner_revoke
    - explicit_time_or_node_budget
```

Lease снимает per-action OK внутри одного bounded package, но не снимает границы:

```text
PX_RH_CLAIM;
route promotion;
main merge / force push;
global policy edits;
CURRENT.md;
paid, destructive or publication actions;
direct Proshka transport.
```

`[ABSTRACT][CONDITIONAL]`

Количество действий должно быть ограничено заранее. Это применение **C12**; бессрочный self-renewing grant превращает fail-closed loop в самостоятельную власть. `[ABSTRACT][CONDITIONAL]` **[C12]**

---

## Один policy kernel

После ратификации operative semantics живёт только в:

```text
docs/CODEX_CONTROL.md  CONTROL_VERSION: 9
```

`AGENTS.md` остаётся thin pointer. `THREE_BODY_LOOP_DESIGN.md` остаётся rationale/design record и не становится вторым действующим policy kernel. Иначе через месяц два текста будут «одинаковы» только после грубого forgetful view, а различаться на жизненно важных state transitions. Это точное применение **C04**. `[ABSTRACT][CONDITIONAL]` **[C04]**

## FINAL PROPOSAL

### Выбранный маршрут

\[
\boxed{
\texttt{CODEX\_AUTONOMY\_LEASE\_V1}
+
\texttt{SEMANTIC\_QUARANTINE}
+
\texttt{PINNED\_SESSION\_TRIGGER}
}
\]

Архитектура трёх тел ратифицирована. Текущий текст `CODEX_GRANT` не ратифицирован и не действует.

### Самый дешёвый решающий тест

До запуска реального Lean-node выполнить восемь plants на временной ветке/фикстуре:

1. **`UNINHABITED_ANTECEDENT_REPLAY`**  
   Kernel-green theorem с ложной production-посылкой должен остаться `KERNEL_GREEN`, но не получить `SEMANTICALLY_ADMITTED`.

2. **`KERNEL_GREEN_NOT_SEMANTICALLY_ADMITTED`**  
   Попытка следующего task потребить quarantined theorem обязана падать.

3. **`WRONG_LAST_SESSION`**  
   Две сессии в одном cwd; launcher обязан продолжить pinned ID, а не последнюю.

4. **`DUPLICATE_TRIGGER`**  
   Один push/event доставлен дважды; стартует ровно один run.

5. **`DROP_CLAIM_RACE`**  
   Codex и Linux одновременно меняют OPEN; возможен ровно один legal transition.

6. **`REQUEST_ID_BLOB_DRIFT`**  
   Ответ с верным ID и неверным request blob отклоняется.

7. **`WRITER_LOCK_COLLISION`**  
   Linux и Codex одновременно хотят write lock; проходит ровно один.

8. **`OLDER_REQUEST_PRIORITY`**  
   Новый CODEX_REQ не обгоняет более старый OPEN REQ.

Pass только если все восемь растений действительно сначала могут быть посажены как нарушения и затем отсекаются control v9. `[ABSTRACT][CONDITIONAL]`

### Наиболее вероятный первый отказ

```text
DROP_CLAIM_RACE
или
WRITER_LOCK_COLLISION
```

Потому что математические роли разведены лучше, чем operational state machine.

## STRONGEST ATTACK

Самое сильное возражение:

> «У нас уже три тела и независимый аудит. Зачем ещё semantic quarantine?»

Потому что три имени не дают трёх независимых ключей. Если Linux только проверяет квитанции Codex и автоматически пишет `ANSWERED`, контур остаётся одним телом с курьером.

Независимость существует только если Linux повторно читает:

```text
source theorem;
точный task;
source object;
terminal consumer;
все новые hypotheses;
CLOSES/OPENS;
production inhabitant или exact supplier.
```

Именно это отсутствовало в трёхдневном эпизоде. Kernel был зелёным, receipts были правильными, а source-specific смысл был ложным. `[ABSTRACT][PAPER]`

Если независимый semantic audit невозможно автоматизировать для конкретного node, самый сильный честный результат — автономная запись **карантинного** source, а не автономное математическое продвижение. Это слабейшая безопасная формулировка гранта.

## CODEX DIRECTIVE

```text
HOLD_CODEX_GRANT_REQ_2026_08_21_O

Do not activate C1-C4 from THREE_BODY_LOOP_DESIGN.md.
Continue under the current per-action / goal-scoped control.

After an explicit owner command authorizes the global-control edit, the sole
next control transaction is:

  CODEX_CONTROL_V9_THREE_BODY_LEASE_AND_SEMANTIC_QUARANTINE

Scope:
  - edit docs/CODEX_CONTROL.md exactly once and increment CONTROL_VERSION 8→9;
  - keep AGENTS.md unchanged;
  - implement the request-state schema, pinned-session launcher and exclusive lock;
  - add and run the eight mandatory plants;
  - do not include a mathematical Lean node in the same transaction;
  - do not activate the lease until strict control validation and every plant pass.

Validation:
  ./orchestrator/spine.py --strict --stdout --reason session-start
  ./specs_docs/session_start.sh
  run the registered targeted control tests and all eight new plants

Success:
  CONTROL_V9_THREE_BODY_LOOP_ALL_PLANTS_GREEN

Failure:
  CODEX_GRANT_CONTROL_V9_OR_PLANT_MISMATCH
```

## META CLOSEOUT

**Что стало меньше?**

«Можно ли дать Codex автономию?» сжато до трёх точных механизмов:

```text
semantic quarantine;
pinned exactly-once trigger;
bounded autonomy lease.
```

**Что убито?**

- kernel-green как semantic proof;
- `TRIED` как единственный request gate;
- `resume --last` как session identity;
- `pgrep` как mutual-exclusion lock;
- ID без request blob;
- три состояния без `IN_REVIEW`;
- бессрочный глобальный grant;
- два параллельных policy kernels.

**Что нельзя пробовать снова?**

Не запускать loop сначала, а lifecycle и semantic gate «дописать по факту». Это повторит тот же post-hoc ремонт, который уже поймал аудит. `[ABSTRACT][CONDITIONAL]` **[C09]**

**Текущий smallest named gap:**

```text
CODEX_CONTROL_V9_THREE_BODY_LEASE_AND_SEMANTIC_QUARANTINE
```

**Следующий cheapest decisive test:**

```text
UNINHABITED_ANTECEDENT_REPLAY
```

Если новый control не ловит ровно тот класс дефекта, ради которого создаётся второе тело, весь grant не нужен.

**Fate of registered predictions:**

```text
P_O_1..P_O_4: REGISTERED, not yet tested.
No retroactive repair authorized.
```

**Memory entry:**

```yaml
iteration:
  target: REQ-2026-08-21-O / CODEX_GRANT review
  status: PROGRESS
  failed_strategy: KERNEL_GATE_AS_SEMANTIC_GATE
  cognitive_operator_used: UNIT_AUDIT
  new_gap_name: CODEX_CONTROL_V9_THREE_BODY_LEASE_AND_SEMANTIC_QUARANTINE
  invariant_learned: push permission and semantic admission are different powers
  forbidden_future_move: consume a self-gated commit before independent semantic review
  next_decisive_test: UNINHABITED_ANTECEDENT_REPLAY
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
