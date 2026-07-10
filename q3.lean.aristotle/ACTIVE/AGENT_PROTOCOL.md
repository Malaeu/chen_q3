# Parallel Agent Protocol

## Purpose

Этот файл фиксирует один и тот же loop для параллельного агента в активной
phase/sprint работе.

Идея простая:

- **оркестратор** всегда один: локальный основной агент в текущей сессии;
- **второй агент** меняется по задаче, но protocol не меняется;
- оба агента читают одни и те же общие опорные файлы;
- коммуникация идёт не через свободный чат-хаос, а через
  `request node -> worker summary -> orchestrator ingest -> canonical report`.

## Native subagent mode

Теперь у проекта есть и нативный Codex subagent слой.

Project-scoped agent config:

- `.codex/config.toml`
- `.codex/agents/q3-worker.toml`
- `.codex/agents/q3-researcher.toml`
- `.codex/agents/q3-lean-worker.toml`
- supporting app playbook:
  `q3.lean.aristotle/docs/insights/codex_app_subagent_playbook_2026_03_16.md`

Это не новый workflow, а тот же самый loop в более удобной форме:

- нативный subagent не заменяет request/report contract;
- он просто снимает ручной prompt boilerplate;
- source of truth всё равно остаётся file-based.
- `q3_worker` не является shell-командой или отдельным бинарём; это profile
  layer для нативного Codex subagent запуска внутри app / interactive CLI.

Рекомендуемое соответствие:

- `q3_worker` = theorem/block worker по active request node;
- `q3_researcher` = semantic search + source synthesis по одному blocker-у;
- `q3_lean_worker` = Aristotle/Lean integration worker.

### Current reliability note

Observed on local `codex-cli 0.98.0`:

- project-scoped agent files in `.codex/agents/` are visible and usable as
  configuration assets;
- but non-interactive `codex exec` does not expose a simple explicit
  `--agent <name>` selector;
- plain-language prompts like `Spawn q3_worker ...` are therefore not yet a
  fully reliable way to force native custom-agent delegation.

Operational consequence:

- preferred native custom-agent usage = interactive Codex app / interactive CLI;
- reliable non-interactive fallback = launch a second `codex exec` process with
  the exact worker contract in the prompt, but let the child return its result
  through stdout / `--output-last-message`, and then let the orchestrator write
  the final `report.md`.

Short version:

- app / interactive CLI first;
- file-based request/report loop stays canonical;
- use the playbook note for Mac-native launch details and pasteable prompts.

## External sidecar agent mode

External local-first research agents (for example EurekaClaw) are allowed only
as sidecars under the same request/report discipline.

Rules:

- they are auxiliary workers, not orchestrators;
- they may read the active request plus explicitly listed supporting files;
- they must return drafts, surveys, or candidate theorem packets only;
- they must not mutate canonical monitors or Lean artifacts directly;
- every useful result must still be ingested by the local orchestrator into the
  normal file-based source of truth.

If an external sidecar maintains its own memory/skill system, that memory is
treated as auxiliary cache, not as canonical project state.

## Roles

### 1. Orchestrator

Обязан:

- держать активный `ACTIVE/PHASE_MONITOR.md` или `ACTIVE/SPRINT_MONITOR.md`
  как operational single source of truth;
- создавать текущий request node для второго агента;
- принимать его report и переводить результат в local sprint state;
- решать, что идёт в source-of-truth, а что остаётся candidate.

### 2. Worker agent

Обязан:

- не переизобретать frontier;
- не менять mainline contract;
- читать только минимальный набор файлов;
- по умолчанию возвращать узкий результат оркестратору, а не строить
  дополнительную CLI-обвязку;
- если делает новые артефакты, перечислить их в summary/report.

Direct child-write в `report.md` теперь считается не дефолтом, а специальным
режимом только если родитель явно этого хочет и среда ведёт себя стабильно.

## Minimal read set for worker agent

Worker agent читает ровно это:

1. `q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`
2. `q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`, если он существует и `ACTIVE`
3. `q3.lean.aristotle/ACTIVE/SPRINT_MONITOR.md`, если phase-monitor неактивен,
   а sprint-monitor активен
4. `q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md`
5. текущий request node из `q3.lean.aristotle/ACTIVE/requests/.../node.md`
6. только те supporting files, которые перечислены в request node

Route B exception: если задача про detector/alpha/SAFE/ZEO или
`routeB_twolevel_spectral_ladder`, старый `node.md` не является current
request. Worker читает:

1. `ROUTE_B_EXECUTION_STATE.json`;
2. `ROUTE_B_EXECUTION_CONTROL.md`;
3. `bus/BUS_PROTOCOL.md`;
4. физический минимальный `NNN_*.goal.md` без matching answer и только
   перечисленные в нём supporting files.

Если unanswered goal отсутствует, worker возвращает `NO_OPEN_BUS_GOAL` и
ничего не исполняет. Ни worker, ни orchestrator-Codex не создают следующий
Route B goal.

Если blocker не возник, worker agent не должен заново перечитывать весь
control-plane.

То же правило действует и для нативных subagents.

## File contract

### Orchestrator writes

- active state:
  `q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`
  or
  `q3.lean.aristotle/ACTIVE/SPRINT_MONITOR.md`
- current request:
  `q3.lean.aristotle/ACTIVE/requests/<request_id>/node.md`
- source-of-truth updates after ingest:
  `SESSION_ENTRY.md`, `IMPLEMENTATION_PLAN.md`, `docs/INSIGHTS.md`, etc.

### Worker default output

- concise theorem-shaped summary in the parent thread
- optional artifacts, if parent explicitly asked for them

## Addressed proof-tree discipline

Theorem packets и route branches адресуются как узлы дерева, а не как
свободные имена.

Пример:

```text
D2g29b = route D -> layer 2 -> subbranch g -> packet 29 -> subpacket b
```

Это координата ветки.

### Consequences

1. Новый узел либо продолжает родительский адрес, либо явно открывает sibling.
2. Killed parent means killed subtree by default.
3. Возврат в killed descendants без explicit reopen reason запрещён.

### Worker rule

Если request node говорит, что killed `D2g`, worker не должен продолжать
`D2g29` или `D2g29b` как будто ветка жива. Нужен либо rollback к живой
развилке, либо explicit obstruction-killer для reopen.

### Orchestrator canonical write-back

- canonical report:
  `q3.lean.aristotle/ACTIVE/requests/<request_id>/report.md`
- optional source-of-truth updates:
  usually `q3.lean.aristotle/docs/insights/<artifact>.md`,
  `docs/INSIGHTS.md`, and monitor files

## Request node schema

Every active request node must contain:

- `Status`
- `Source`
- `Phase/Sprint link`
- `Why we are here`
- `Exact task`
- `Required deliverables`
- `Supporting files`
- `Non-goals`
- `Write-back contract`

The write-back contract names the canonical target file for the orchestrator.
It does not force the native worker to do direct child-write by default.

## Report schema

Every worker report must contain:

- `Status`
- `What I read`
- `What I claim`
- `Exact deliverables created or updated`
- `Open questions / blockers`
- `Recommended next step for orchestrator`

## Startup response contract for worker

Первое сообщение worker agent должно быть коротким:

```text
Активная фаза/спринт видна, беру request <request_id>.
Читаю request node и указанные supporting files, результат возвращаю коротким
summary; канонический report оформит оркестратор.
Если blocker не возникнет, остальные control docs не трогаю.
```

## Orchestrator ingest rule

После получения worker report orchestrator делает ровно это:

1. проверяет report и новые артефакты;
2. обновляет активный `PHASE_MONITOR.md` или `SPRINT_MONITOR.md` first;
3. если worker фактически убил theorem shape, записывает kill certificate в
   `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md`;
3a. если killed node имеет потомков по адресной нумерации, это считается
    killed subtree, пока нет explicit reopen;
4. коротко логирует synthesis в `docs/INSIGHTS.md`;
5. только потом меняет `IMPLEMENTATION_PLAN.md` / `SESSION_ENTRY.md`, если
   реально изменилась стадия работы.

## Prompt template for the worker

Ниже pasteable prompt. Его можно кидать почти без изменений; менять надо
только request path и supporting files.

```text
Ты второй агент внутри active phase/sprint в repo
/Users/emalam/Documents/GitHub/rh_lean_01_2026.

Работай не как оркестратор, а как worker agent.

Протокол:
1. Прочитай только:
   - q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md
   - q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md if active
   - q3.lean.aristotle/ACTIVE/SPRINT_MONITOR.md if no active phase monitor
   - q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
   - <REQUEST_NODE>
2. Потом прочитай только supporting files, перечисленные в request node.
3. Не пересобирай общий frontier и не предлагай новую RH-архитектуру.
4. Не делай rank/basis hunt как theorem content.
5. Верни узкий theorem-shaped результат в финальном сообщении.
6. Не запускай дополнительные CLI-обвязки и не пиши в файлы сам, если это не
   запрошено явно.
7. Если создаёшь новые артефакты, перечисли точные пути в summary.

Твоя задача сейчас:
<ONE_SENTENCE_TASK>
```

## Prompt template for native subagents

Если используем нативный subagent workflow, parent prompt должен быть таким же
узким:

```text
Spawn q3_worker for the active request node
q3.lean.aristotle/ACTIVE/requests/<request_id>/node.md.
Have it read the request node, the files it lists, and return a concise
theorem-shaped summary to the parent thread.
Do not let it re-map the whole project.
The parent orchestrator will write the canonical report.md.
```

Для research pass:

```text
Spawn q3_researcher for blocker <blocker_name>.
Have it use the active monitor plus the request node, run the local oracle and
one external sanity-check, and return the synthesis to the parent thread.
```

Для Lean/Aristotle:

```text
Spawn q3_lean_worker for lemma <lemma_name>.
Have it follow the Aristotle workflow exactly, keep the request narrow, and
report compile status plus any hole-free extracted lemmas.
```

## Reliable fallback runner

When native custom-agent selection is not deterministic enough in
non-interactive CLI, use this fallback:

```text
codex exec --dangerously-bypass-approvals-and-sandbox -C <repo> "
Ты worker agent внутри active phase/sprint ...
<same narrow worker contract, but return the payload in the final message>
"
```

This is still a real second Codex process.
It is acceptable as long as:

- the read set stays narrow;
- the child does not re-map the whole project;
- the child returns payload through stdout / final message;
- the orchestrator writes the designated `report.md` after ingesting that
  payload.

## Persona note

Можно добавить persona-строку вроде “ты сильный operator theorist”, но это
вторично.

Не надо строить prompt вокруг “ты Перельман / ты Терренс Тао”.
Это почти всегда хуже, чем короткий operational prompt плюс точный request
node.
