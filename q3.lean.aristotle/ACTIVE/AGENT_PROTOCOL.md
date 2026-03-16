# Parallel Agent Protocol

## Purpose

Этот файл фиксирует один и тот же loop для параллельного агента в активной
phase/sprint работе.

Идея простая:

- **оркестратор** всегда один: локальный основной агент в текущей сессии;
- **второй агент** меняется по задаче, но protocol не меняется;
- оба агента читают одни и те же общие опорные файлы;
- коммуникация идёт не через свободный чат-хаос, а через
  `request node -> report file -> orchestrator ingest`.

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
- писать результат в заранее заданный report file;
- если делает новые артефакты, перечислить их в report.

## Minimal read set for worker agent

Worker agent читает ровно это:

1. `q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md`
2. `q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`, если он существует и `ACTIVE`
3. `q3.lean.aristotle/ACTIVE/SPRINT_MONITOR.md`, если phase-monitor неактивен,
   а sprint-monitor активен
4. `q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md`
5. текущий request node из `q3.lean.aristotle/ACTIVE/requests/.../node.md`
6. только те supporting files, которые перечислены в request node

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

### Worker writes

- report:
  `q3.lean.aristotle/ACTIVE/requests/<request_id>/report.md`
- optional artifacts:
  usually `q3.lean.aristotle/docs/insights/<artifact>.md`

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
Читаю request node и указанные supporting files, результат пишу в report.md.
Если blocker не возникнет, остальные control docs не трогаю.
```

## Orchestrator ingest rule

После получения worker report orchestrator делает ровно это:

1. проверяет report и новые артефакты;
2. обновляет активный `PHASE_MONITOR.md` или `SPRINT_MONITOR.md` first;
3. коротко логирует synthesis в `docs/INSIGHTS.md`;
4. только потом меняет `IMPLEMENTATION_PLAN.md` / `SESSION_ENTRY.md`, если
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
5. Пиши результат в:
   <REPORT_FILE>
6. Если создаёшь новые артефакты, перечисли точные пути в report.

Твоя задача сейчас:
<ONE_SENTENCE_TASK>
```

## Prompt template for native subagents

Если используем нативный subagent workflow, parent prompt должен быть таким же
узким:

```text
Spawn q3_worker for the active request node
q3.lean.aristotle/ACTIVE/requests/<request_id>/node.md.
Have it read the request node, the files it lists, and write only to
q3.lean.aristotle/ACTIVE/requests/<request_id>/report.md.
Do not let it re-map the whole project.
```

Для research pass:

```text
Spawn q3_researcher for blocker <blocker_name>.
Have it use the active monitor plus the request node, run the local oracle and
one external sanity-check, and write the synthesis only to the report file.
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
- the orchestrator writes the designated `report.md` after ingesting the child
  output.

## Persona note

Можно добавить persona-строку вроде “ты сильный operator theorist”, но это
вторично.

Не надо строить prompt вокруг “ты Перельман / ты Терренс Тао”.
Это почти всегда хуже, чем короткий operational prompt плюс точный request
node.
