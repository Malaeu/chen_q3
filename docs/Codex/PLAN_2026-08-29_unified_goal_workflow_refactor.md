# PLAN: единый goal workflow без второго оркестратора

**Дата:** 2026-08-29  
**Статус:** PLAN / NOT_IMPLEMENTED  
**Основание:** прямая инструкция владельца спроектировать полный workflow-refactor.  
**Реализует:**
`TASK_2026-08-28_goal_lifecycle_contract.md` и
`TASK_2026-08-28_workflow_closure_refactor.md`.

## 1. Результат

Владелец формулирует один гол. Codex получает из существующих источников
точный исполнимый scope, выбирает минимальный набор зарегистрированных
инструментов, выполняет работу, проверяет результат и проводит все обязательные
переходы закрытия. Владелец не напоминает вручную про каталог, VOI, Lean gate,
индексы, assembly-долг, статью, Proshka batch, protocol и dirty-tree split.

Новая система **не становится шестым владельцем состояния**. Единственный новый
runtime является stateless-планировщиком и исполнителем переходов. Он читает
канонические источники и вызывает существующие инструменты; математическую
истину, phase, goal, authority, commit и push он не изобретает.

## 2. Проверенный baseline 2026-08-29

- `TOOLS.yaml`: 7 семейств, 48 tool contracts, 41 `ENABLED`, 16 event routes.
- Файловый census: 415 постоянных `TOOL`, 192 one-shot probe, 37 tests,
  9 migrations. Эти 653 файла нельзя превращать в одинаково видимые команды.
- В `orchestrator/`: 33 Python-модуля; в `scripts/`: 9 `check_*.sh`.
- Есть read-only startup, selector, event writers и Spine refresh reasons.
- Нет `session_close`, `phase_close`, `workflow_runtime` и общего dependency
  registry.
- `goal_runtime.py` является селектором, не исполнителем жизненного цикла.
- `spine.py` уже маршрутизирует `verdict-intake`, `step-close`, `goal-close` и
  `semantic-index-refresh`, но `goal-close` всегда запускает широкий фиксированный
  список и не вычисляет минимальное замыкание изменённых входов.
- Детектор staleness для `RouteB/*.lean -> inventory_RouteB.json` уже существует
  в `session_start.sh` §10 и основан на Git, не на mtime.
- Свежий запуск `goal_runtime.py --json` занял **68.41 s**.
- Свежий `session_start.sh` дошёл до `P9_STRICT_PASS` примерно за **184 s**.
- Причина hot path проверена по коду: для каждого
  `CODEX_REQ_STATE_*.yaml` `validate_request_file_binding()` перебирает всю
  first-parent историю и запускает отдельный `git rev-parse` на каждый commit.
  Сейчас это 2 request-state файла × 3039 commits, то есть до ~6078 Git-процессов
  за один gate. Тот же repository gate вызывают несколько front doors.
- Semantic index receipt был успешно перестроен, но последующая общая validation
  снова попала в тот же исторический scan. Значит embeddings и request-history
  validation должны иметь раздельные fingerprints и раздельные receipts.
- На baseline общий session audit всё ещё сообщает два housekeeping-долга:
  один непрожатый verdict и один файл в `docs/_inbox`. Они не маскируются как
  чистый старт.

## 3. Что остаётся единственным источником истины

| Роль | Канонический источник | Новый runtime делает |
|---|---|---|
| authority и policy | `docs/CODEX_CONTROL.md` + strict Spine | только проверяет |
| physical goal и phase | bus, `goal_runtime.py`, `CHANNEL_RUNTIME.json` | только выбирает через существующий selector |
| инструменты | `docs/cartographer/TOOLS.yaml` | строит минимальный tool slice |
| математические события | `goal_events.py`, `knowledge.db`, task artifacts | вызывает существующих writers |
| derived artifacts | новый artifact DAG | вычисляет staleness и repair closure |
| проверки | Lean и существующие `check_*.sh` | вызывает, не переписывает |
| Proshka | существующий living-chat/repo protocol | только формирует eligible batch |
| commit/push | Codex под действующим operational grant | runtime сам не коммитит и не пушит |

`docs/orchestrator/BOOTSTRAP_PROMPT.md` сейчас untracked и описывает ещё одного
«оркестратора» со своей bootstrap-политикой. Он не является входом этого плана,
не становится control surface и не удаляется молча.

## 4. Единый логический цикл

```text
INTAKE
  -> START_GATE
  -> NARROWING
  -> PLAN
  -> EXECUTE
  -> VERIFY
  -> CLOSE_NODE
  -> REVIEW_BATCH? (только 2-4 реальных blocker)
  -> CLOSE_PHASE?
  -> CLOSE_SESSION
  -> DELIVERY? (только по operational grant)
```

### INTAKE

Допустимы только существующие авторитетные формы:

1. открытый physical Route B goal;
2. source-locked `docs/Codex` task;
3. точная owner-инструкция как operational scope, если Control уже позволяет
   её материализацию.

Произнесённый гол не подменяет physical mathematical goal. В первой версии
runtime показывает, к какому каноническому объекту он его привязал. Если для
полностью автоматической материализации owner-intent потребуется новая
семантика authority, это отдельный Control-version decision после shadow-mode,
а не скрытая часть рефакторинга.

### START_GATE

Один вызов startup front door. Результат сохраняется как immutable receipt,
привязанный к:

- `HEAD`;
- hash релевантного worktree scope;
- Control version/hash;
- `TOOLS.yaml` hash;
- artifact-DAG hash;
- machine semantic receipt identity;
- request-ledger identity.

Внутри одного run одинаковый receipt переиспользуется. Разные front doors не
повторяют один и тот же gate.

### NARROWING

В порядке цены:

1. `ask.sh` и секция `СТЫКОВКИ`;
2. `kb.py ask/flags`;
3. semantic/elaborated lookup и `supplier_preflight` для точной Lean-цели;
4. внешний поиск только после локального полного shelf miss;
5. VOI receipt с `ПРОЧТЕНИЯ`, `ЗОНД`, `ЕСЛИ_A`, `ЕСЛИ_B`.

Runtime не делает все запросы всегда. Он выбирает минимальный необходимый
префикс и прекращает narrowing, когда uncertainty уже снята.

### PLAN

Read-only команда печатает machine-readable execution envelope:

```yaml
schema: q3_workflow_plan.v1
goal_binding: {}
authority_receipt: {}
input_fingerprint: {}
selected_tools: []
derived_dirty: []
verification_gates: []
manual_debts: []
expected_writes: []
foreign_dirty_paths: []
hold_conditions: []
```

Каждый selected tool обязан ссылаться на существующий tool id, trigger,
mode, writes, authority и validation. Не зарегистрированный инструмент
исполняться не может.

### EXECUTE и VERIFY

Runtime вызывает старые executors и фиксирует exit code, duration, input/output
hashes и changed paths. Текст лога не заменяет exit code. Независимые read-only
probes могут идти параллельно; writers и gates с общими inputs идут по DAG.

### CLOSE_NODE / CLOSE_PHASE / CLOSE_SESSION

- `close-node`: kernel/source gate, `CLOSES`/`OPENS`, минимальный repair closure,
  article/assembly/insight/card debt.
- `close-phase`: repair closure, существующие gates, verdict migration,
  blueprint regeneration, debt report; fail closed при несогласованности.
- `close-session`: repair fixable artifacts, проверка изменённого scope,
  session protocol skeleton, split own/foreign dirty paths; без commit/push.

## 5. Artifact DAG: один детектор, три потребителя

Новый data-only файл:

`docs/cartographer/DERIVED_ARTIFACTS.yaml`

Он не дублирует tool contracts. Он хранит только зависимости и доказательство
freshness:

```yaml
artifacts:
  - id: routeb-inventory
    inputs: [q3.lean.aristotle/Q3/Proofs/RouteB/**/*.lean]
    output: docs/cartographer/inventory_RouteB.json
    generator_tool: routeb-inventory
    validator: CONTENT_AND_GIT_HASH
    atomic_publish: true
    cost_tier: CHEAP
    authority: DERIVED_NOT_PROOF
```

Обязательные поля каждой записи:

- input selector и output paths;
- generator tool id из `TOOLS.yaml`;
- proof-grade fingerprint algorithm;
- validator и atomic-publication rule;
- cost tier и host capability;
- authoritative/manual boundary;
- downstream consumers.

Три потребителя используют один evaluator:

- session start: report only;
- session close: repair fixable;
- phase close: repair, gate, fail on residual inconsistency.

Первый probe покрывает ровно inventory, atoms и `NEEDS_CARDS`. Если хотя бы для
одного нет доказательного freshness criterion, блок A возвращает `HOLD` и
дальнейшая автоматика на догадках не строится.

## 6. Rollout по блокам

### Block 0 — baseline и hot-path repair

1. Добавить timing/command-count plants для selector и strict startup.
2. Заменить `commits × requests` subprocess loop на доказательно эквивалентную
   проверку первого появления blob одним bounded Git query на request.
3. Ввести in-run memoization repository gate по точному fingerprint.
4. Не кэшировать PASS между изменившимися HEAD/worktree/control/request inputs.

**Gate:** тот же verdict на adversarial history plants; selector cold ≤ 5 s,
warm ≤ 2 s; strict startup p95 ≤ 15 s на неизменном дереве. Если платформенный
разброс выше, бюджет корректируется только по сохранённому baseline report.

### Block A — dependency registry и evaluator

Реализовать data registry, `status` и `affected-by`. Перенести §10 startup на
общий evaluator без изменения read-only поведения.

**Gate:** stale fixture непуст; fresh fixture пуст; два последовательных
прохода дают ноль работы и ноль diff.

### Block B — `session_close`

Минимальный repair closure, changed-scope validation, protocol skeleton и
own/foreign dirty split. Собственным считается только path из execution envelope
или явного grant; остальные paths докладываются отдельно и не блокируют как
«наши».

**Gate:** foreign edits не изменены и не staged; residual inconsistency даёт
ненулевой exit; второй run no-op.

### Block C — `phase_close`

Одна точка входа вызывает существующие gates в зарегистрированном порядке.
Она не копирует их правила. После repair идут gates, verdict migration,
blueprint и отчёт.

**Gate:** один сломанный gate останавливает downstream publish; повторный
зелёный run no-op.

### Block D — видимый manual debt

Печатать адресный debt ledger для:

- kernel-green, но assembly не отражает closure;
- missing insight;
- source без card;
- неполная branch-decision запись.

Runtime не выставляет `READY` по regex и не сочиняет insight.

**Gate:** planted debt всегда видим; пустой debt report возможен только при
машинно подтверждённой пустоте.

### Block E — Lean build coverage

Измерить объединённую Lake target, затем решить `Q3.+`/отдельный RouteB target.
До измерения `lakefile.toml` не менять. Changed-module validation использует
import closure, phase close сохраняет полный coverage gate.

**Gate:** новый RouteB-модуль не может остаться вне любого CI/build target.

### Block F — unified `workflow_runtime`

Добавить один stateless front door:

```bash
python3 orchestrator/workflow_runtime.py plan
python3 orchestrator/workflow_runtime.py run --through close-node
python3 orchestrator/workflow_runtime.py close-phase
python3 orchestrator/workflow_runtime.py close-session
```

Он компилирует lifecycle из существующих источников, не создаёт второй selector,
runtime state или policy kernel.

**Gate:** shadow-mode план совпадает с ручным исполнением на трёх реальных
закрытиях; затем старые front doors остаются callable, но документация ведёт к
одной точке входа.

## 7. Набор обязательных adversarial tests

1. История >3000 commits и несколько request-state: число Git subprocesses O(R),
   не O(R×H).
2. Изменён request blob при прежнем HEAD receipt: cache invalidated, fail closed.
3. Изменён Control/TOOLS/DAG hash: полный replan.
4. Dirty Lean file: inventory closure dirty даже при чистом committed history.
5. Сломанный/пустой generator output: старый output не публикуется.
6. Частичный writer failure: downstream не запускается, статус не зелёный.
7. Два одинаковых close runs: второй `executed_actions=[]`, Git diff пуст.
8. Чужие dirty paths: не изменены, не staged, перечислены отдельно.
9. Mac/Linux: одинаковый logical plan; различается только допустимый host
   executor. Ни один host не притворяется authority другого.
10. Semantic receipt от другого machine/commit: historical only, не PASS.
11. Assembly/insight debt: видим, но не auto-resolved.
12. Proshka: 0 вызовов на ordinary close; batch только 2-4 blocker и только
    после локального narrowing.
13. Никаких автоматических commit, push, publication, promotion или
    `PX_RH_CLAIM`.

## 8. Метрики результата

Сохраняются в derived observability, не в новом authority state:

- startup и selector p50/p95;
- Git subprocess count на gate;
- tool calls per goal;
- duplicate gate executions per run;
- executed/skipped derived actions;
- second-run work count и diff count;
- manual owner interventions per closed node;
- stale artifacts after phase close;
- assembly/insight/card debt size;
- routed ENABLED tool contracts и orphan live tools;
- Proshka calls per ordinary close и per blocker batch.

Три итоговых acceptance criteria:

1. ноль ручных шагов от kernel-green до свежего каталога;
2. manual semantic debt всегда адресно видим;
3. повторный close делает ноль работы и не создаёт diff.

## 9. HOLD-границы

Немедленный `HOLD`, а не эвристическое продолжение, если:

- для derived artifact нет proof-grade freshness criterion;
- generator не atomic/idempotent;
- physical goal неоднозначен или отсутствует source binding;
- required tool не зарегистрирован, `BROKEN` или недоступен на host;
- expected writes пересекаются с чужими dirty paths;
- требуется математическое суждение: assembly truth, insight content,
  theorem-shape promotion;
- proposed owner-intent materialization меняет authority semantics;
- требуется publication, destructive action, paid external call или
  `PX_RH_CLAIM` без отдельной authority.

## 10. Commit discipline и отчётность rollout

Каждый блок получает отдельный report `DONE` или `HOLD`, `CLOSES`, `OPENS`,
timings, tests и exact changed paths. Один scoped commit на завершённый блок;
никакого blanket staging. Runtime не выполняет Git delivery сам. Codex может
сделать scoped commit/push только по действующему operational grant.

Порядок неизменен: **0 → A → B → C → D → E → F**. Следующий блок не начинается,
если предыдущий вернул `HOLD`, кроме независимого read-only исследования,
явно названного в его report.

