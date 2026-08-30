# Q3 cross-host operator card: workflow and tool inventory

```yaml
schema: q3_cross_host_operator_card.v1
status: CANONICAL_OPERATOR_CARD
audience: [OWNER, CODEX_MAC, CODEX_LINUX]
canonical_branch: rh_clean
control: docs/CODEX_CONTROL.md
tool_manifest: docs/cartographer/TOOLS.yaml
workflow_front_door: orchestrator/workflow_runtime.py
inventory_snapshot_date: 2026-08-30
registered_tools: 54
route_promotion_authorized: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Зачем существует эта карточка

Владелец работает с одним Q3-проектом с двух рабочих мест: дома на Mac и на
работе на Linux. Репозиторий, physical bus, control, tool manifest, semantic
state и математический frontier общие. Хост меняет только способ исполнения
некоторых системных операций; он не создаёт вторую очередь, вторую карту или
вторую математическую истину.

Карточка отвечает на четыре вопроса:

1. откуда Codex узнаёт, что делать;
2. в каком порядке вызываются инструменты;
3. когда нужен Proshka, semantic admission, карта или публикационный blueprint;
4. что различается между Mac и Linux.

Текущий математический шаг в карточке намеренно не заморожен. Его каждый раз
выбирают живой physical goal, goal selector и Route-B execution state.

## 2. Единственный рабочий loop

```text
OWNER INTENT
  -> STRICT STARTUP
  -> EXACT PHYSICAL GOAL
  -> LOCAL SHELVES AND KNOWLEDGE
  -> SUPPLIER PREFLIGHT
  -> ONE PRECOMMITTED PROOF OR TEST CYCLE
  -> KERNEL AND AXIOM GATE
  -> SEMANTIC ADMISSION, ONLY WHEN REQUIRED
  -> STEP OR GOAL CLOSE
  -> INVENTORY, ATOMS, MAP AND PUBLICATION BLUEPRINT
  -> SCOPED COMMIT, REBASE AND PUSH
  -> SELECT THE NEXT PHYSICAL GOAL
```

### 2.1 Startup

На обоих хостах вход одинаковый:

```bash
cd /path/to/rh_lean_01_2026
git rev-parse --show-toplevel
git branch --show-current
bash specs_docs/session_start.sh
python3 orchestrator/workflow_runtime.py plan
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```

Красный startup запрещает математику. Разрешён только узкий ремонт
воспроизводимого control/tool defect. Зелёный plan не маскирует красный gate.
Тот же вход печатает delta-aware Route B briefing, ранжирует reopenable
`RESEARCH_DEBT` и предлагает выбрать, искать ли сегодня долг или потратить один
исследовательский цикл Прошки; внешний поиск и отправка автоматически не запускаются.

`research-debt-challenge` — read-only генератор. Он строит byte-stable пакет с
обязательным novelty requirement и разрешёнными исходами, но не меняет очередь,
не отправляет сообщение, не создаёт verdict и не открывает маршрут.

### 2.2 Выбор и narrowing

Один run привязывается ровно к одному OPEN physical goal или к source-locked
Codex task. Порядок поиска дешёвый-к-дорогому:

1. ask-shelf;
2. kb-query и search flags;
3. semantic retrieval и supplier-preflight для точной Lean-цели;
4. внешний paper/source search только после локального miss;
5. Aristotle только для точного source-locked theorem contract;
6. Proshka только на разрешённом review trigger.

Поисковое совпадение остаётся кандидатом до EXACT_FIT. Отсутствие нельзя
объявлять до полного preflight.

### 2.3 Выполнение и закрытие

Codex выполняет один заранее названный proof/test cycle. Затем проверяются
точный artifact, Lean kernel, axioms и применимые plants. При закрытии шага
пишется attempt event; reusable insight пишется только при наличии нового
переиспользуемого знания. Goal close обновляет CLOSES/OPENS, assembly и
минимальное замыкание производных артефактов.

Если менялись RouteB sources, обновляются inventory и atoms. При изменении
топологии проверяется MAP coverage. При изменении proof registry, assembly или
EnvDump обновляется publication blueprint. Blueprint не является публикацией и
не даёт proof authority.

После зелёного owned delta Codex сам делает scoped commit, pull --rebase и push.
Чужие dirty paths не входят в staged scope.

### 2.4 Постоянная операционная авторизация владельца

Владелец заранее авторизует Codex на обоих хостах выполнять без отдельного
повторного вопроса все обычные обратимые действия внутри уже выбранного Q3
scope:

- создавать и обновлять source-locked request/task/receipt артефакты;
- делать scoped commit, pull --rebase --autostash и push в `rh_clean`;
- отправлять разрешённый byte-exact запрос Прошке в тот же living phase chat;
- забирать, проверять и мигрировать verdict commit;
- передавать Linux-телу точный scoped baton или запрос, когда Linux действительно
  является нужным executor или независимым auditor;
- запускать зарегистрированные read-only поиски, gates, plants, Lean validation,
  semantic refresh и разрешённые close transactions.

Отдельный вопрос владельцу нужен только если действие меняет заданный scope или
authority: `PX_RH_CLAIM`, новый phase key/chat, удаление или необратимое действие,
секрет/credential, финансовое действие, неизвестная внешняя сторона либо
действительно обязательная safety-confirmation активного host runtime. Такая
внешняя safety-confirmation не должна превращаться в репозиторный owner-click и
не меняет математический pipeline.

## 3. Когда вызывается Proshka

Обычное закрытие goal делает ноль вызовов к Proshka. Review разрешён для:

- стратегических MINT, PROMOTION, FRONT_CHANGE или FATAL;
- одного EXPLORATION_REVIEW после шести зарегистрированных no-delta cycles;
- PX_RH_CLAIM_REVIEW, который всегда остаётся owner boundary.

Один неизменный six-field phase key использует один living chat. Перед отправкой
Codex создаёт byte-exact UTF-8 .txt, проверяет hash и запускает workflow-runtime
review-plan. Он сам прикрепляет один файл и отправляет короткую инструкцию в тот
же чат. План отправки не является receipt: доставка установлена только после
наблюдения sent message и natural reasoning start. Повторная отправка для
IN_REVIEW или ANSWERED запрещена.

`REVIEW_DISPATCH_READY` вместе с `STATUS: OPEN` является постоянной
репозиторной авторизацией current Codex body на same-chat upload/send. Codex не
просит у владельца отдельное подтверждение решения, commit, push или отправки.
Если активная UI-платформа всё же навязывает обязательную action-time
confirmation, это внешняя safety-граница платформы; Codex не дублирует её
собственным вопросом и продолжает сразу после подтверждения.

После verdict commit выполняются fetch, безопасный rebase/autostash, проверка
request/verdict binding и verdict migration. KILL закрывает названную
репрезентацию, а не автоматически весь математический goal.

## 4. Три разных semantic-контура

### 4.1 Semantic index

q3_docs — retrieval-only индекс. Он помогает найти определения, источники,
suppliers и прошлые решения. Его результат не является доказательством. Corpus
или receipt drift даёт SEMANTIC_INDEX_CORPUS_STALE; после разрешённого refresh
strict startup запускается заново.

### 4.2 Semantic quarantine и attestation

Load-bearing Lean input проходит отдельную цепь:

```text
SOURCE_WRITTEN -> KERNEL_GREEN -> external attestation -> SEMANTICALLY_ADMITTED
```

semantic-attestation-broker только находит внешний receipt и не выпускает его.
semantic-admit материализует переход для exact entry и exact attestation через
three_body_loop. Допуск ограничен перечисленными scopes и не означает закрытие
Goal 058, Route B или RH.

### 4.3 Knowledge spine

knowledge.db, Progress_Log, verdict migration и Spine projections хранят kills,
moves, branch decisions, attempts и проверенные связи. Это каноническая
проектная память, но не Lean kernel и не semantic attestation.

## 5. Различия Mac и Linux

| Операция | Mac | Linux |
|---|---|---|
| Канонический repo/branch | тот же rh_clean | тот же rh_clean |
| Startup, selector, runtime | одинаковые команды | одинаковые команды |
| Lean | обычный lake/lean | перед lake/lean удалить LD_LIBRARY_PATH |
| Existing semantic admission | signed offline verification по умолчанию | внешний broker/auditor path |
| Emergency existing-admission startup | tracked-receipt fallback только по явному owner enable; не создаёт новый admission | неприменимо |
| Новый semantic admission | Codex не выпускает auditor receipt | независимый Linux auditor выпускает receipt; materialization остаётся exact-scope transition |
| Commit prefix | [MacOS][rh_clean] | [Linux-Codex][rh_clean] |
| Proshka | тот же living phase chat | тот же living phase chat |

Linux-команды Lean:

```bash
env -u LD_LIBRARY_PATH lake build <target>
env -u LD_LIBRARY_PATH lake env lean <file>.lean
```

Mac emergency fallback применяется только для уже admitted entry и только по
точной owner-инструкции:

```bash
Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK=1 bash specs_docs/session_start.sh
```

Он не заменяет подпись, не создаёт новый admission и не переносится на Linux.

## 6. Decision table

| Наблюдение | Действие |
|---|---|
| startup red | остановить математику; ремонтировать только названный control defect |
| plan READY и exact goal выбран | выполнить narrowing и один proof/test cycle |
| shelf candidate найден | supplier-preflight; использовать только при EXACT_FIT |
| шесть no-delta cycles | собрать blocker fingerprint и разрешённый exploration review |
| Proshka request OPEN и review-plan ready | current Codex body доставляет exact attachment в living chat |
| scoped commit/push или same-chat Proshka delivery | выполнять автономно по постоянной owner authorization |
| request IN_REVIEW или ANSWERED | не отправлять повторно |
| Lean KERNEL_GREEN, admission требуется | ждать независимый receipt; downstream использование запрещено |
| SEMANTICALLY_ADMITTED | использовать только точные admitted scopes |
| theorem/goal действительно закрыт | close transaction, карта/blueprint, scoped delivery |
| foreign dirty paths | сохранить; не stage и не commit |
| PX_RH_CLAIM | остановиться на owner authority boundary |

## 7. Зарегистрированный инвентарь

Единственный routable inventory — docs/cartographer/TOOLS.yaml. На снимке
2026-08-30 зарегистрировано 54 инструмента: 47 ENABLED, 6 AVAILABLE и 1 DEGRADED.
Сотни вспомогательных scripts, tests и one-shot probes на диске не становятся
автоматически routable: для рождения инструмента нужен полный manifest contract.

Следующий machine-readable список проверяется plant против manifest и не может
молча разойтись с ним.

```yaml registered_tool_ids
- codex-session-start
- routeb-session-briefing
- routeb-session-checkpoint
- research-debt-challenge
- knowledge-spine-strict
- knowledge-spine-goal-close
- knowledge-spine-step-close
- migration-census
- routeb-status
- goal-run-selector
- workflow-runtime
- workflow-session-close
- workflow-phase-close
- three-body-loop
- w5-budget-probe
- edge-slope-probe
- r2-coefficient-identity-probe
- semantic-attestation-broker
- semantic-admit
- codex-watch-read-only
- ask-shelf
- supplier-preflight
- kb-query
- kb-canonical-write
- progress-log-migrator
- route058-migrator
- research-oracle
- q3-docs-refresh
- semantic-preflight
- goal-event-writer
- property-descent
- routeb-inventory
- atom-index
- map-coverage
- comparator-lite
- lean-env-dump
- atom-describe
- foreign-atom-bridge
- constructor-probes
- cheap-closure-finder
- depgraph-roof-cone
- blueprint-skeleton-generator
- cartographer-brief
- cartographer-loaders
- observability-summary
- observability-refresh
- tool-census
- lean-validation
- aristotle
- paper-ingest
- proshka-context-pack
- packet-build
- packet-ingest
- task-specific-generators
```

Живой census:

```bash
python3 orchestrator/tools_census.py
```

Статус конкретного инструмента, trigger, write scope, authority и validation
всегда читаются из текущего manifest, а не из этого датированного снимка.

## 8. Неизменяемые границы

- Один repo, один branch, одна physical bus и одна project memory для обоих хостов.
- Plan не является исполнением.
- Search result не является supplier.
- Kernel green не является semantic admission.
- Semantic admission не является математическим goal close.
- Map coverage не доказывает актуальность математики.
- Publication blueprint не является внешней публикацией.
- Ни один green gate не означает Route promotion или RH.
- PX_RH_CLAIM остаётся единственной owner-only границей.
