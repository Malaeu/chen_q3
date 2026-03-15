# Parallel Agent Protocol

## Purpose

Этот файл фиксирует один и тот же loop для параллельного агента в активном
спринте.

Идея простая:

- **оркестратор** всегда один: локальный основной агент в текущей сессии;
- **второй агент** меняется по задаче, но protocol не меняется;
- оба агента читают одни и те же общие опорные файлы;
- коммуникация идёт не через свободный чат-хаос, а через
  `request node -> report file -> orchestrator ingest`.

## Roles

### 1. Orchestrator

Обязан:

- держать `ACTIVE/SPRINT_MONITOR.md` как operational single source of truth;
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
2. `q3.lean.aristotle/ACTIVE/SPRINT_MONITOR.md`
3. `q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md`
4. текущий request node из `q3.lean.aristotle/ACTIVE/requests/.../node.md`
5. только те supporting files, которые перечислены в request node

Если blocker не возник, worker agent не должен заново перечитывать весь
control-plane.

## File contract

### Orchestrator writes

- sprint state:
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
- `Sprint link`
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
Спринт активен, беру request <request_id>.
Читаю request node и указанные supporting files, результат пишу в report.md.
Если blocker не возникнет, остальные control docs не трогаю.
```

## Orchestrator ingest rule

После получения worker report orchestrator делает ровно это:

1. проверяет report и новые артефакты;
2. обновляет `ACTIVE/SPRINT_MONITOR.md` first;
3. коротко логирует synthesis в `docs/INSIGHTS.md`;
4. только потом меняет `IMPLEMENTATION_PLAN.md` / `SESSION_ENTRY.md`, если
   реально изменилась стадия спринта.

## Prompt template for the worker

Ниже pasteable prompt. Его можно кидать почти без изменений; менять надо
только request path и supporting files.

```text
Ты второй агент внутри active sprint в repo
/Users/emalam/Documents/GitHub/rh_lean_01_2026.

Работай не как оркестратор, а как worker agent.

Протокол:
1. Прочитай только:
   - q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md
   - q3.lean.aristotle/ACTIVE/SPRINT_MONITOR.md
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

## Persona note

Можно добавить persona-строку вроде “ты сильный operator theorist”, но это
вторично.

Не надо строить prompt вокруг “ты Перельман / ты Терренс Тао”.
Это почти всегда хуже, чем короткий operational prompt плюс точный request
node.
