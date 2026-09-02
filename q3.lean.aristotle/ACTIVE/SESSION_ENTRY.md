# Codex Session Entry

Updated: 2026-09-02

Этот файл — короткий маршрутизатор. Политика живёт только в
`docs/CODEX_CONTROL.md`; физическое состояние и source pins выбирают работу.

## Неподвижная граница

- Route B: `CHALLENGER_NOT_RH`.
- `PX_RH_CLAIM: NOT_MADE`.
- Единственная owner-only математическая граница — `PX_RH_CLAIM`.
- Generated views, память, старый monitor и browser/chat сами работу не выбирают.
- Исторические v9 receipts сохраняют исходную идентичность, но не создают новую
  v10 authority.

## Единственный обязательный старт

1. Полностью прочитать `docs/CODEX_CONTROL.md` и этот короткий маршрутизатор.
2. Запустить:

   ```bash
   python3 orchestrator/workflow_runtime.py plan
   ```

Это единственный канонический front door. Он читает control, Git/worktree,
physical bus, `docs/Codex/CURRENT.md`, runtime state и scoped node registry в
одном read epoch. Он ничего не пишет, не запускает Lean, не вызывает внешних
агентов и не выбирает theorem/consumer за исполнителя.

`docs/cartographer/TOOLS.yaml` валидируется самим plan и читается исполнителем
только после plan, причём лишь для выбранного tool family. Полный
`q3.lean.aristotle/COGNITIVE_OPERATORS.md` читается только при настоящей
математической развилке или strategy trigger, а не на каждом startup.

`bash specs_docs/session_start.sh` — только ручной legacy-диагностический
wrapper. Не запускать его дополнительно при обычном входе и не считать его
вторым источником истины.

## Как читать plan

Сначала выдать владельцу короткий battle brief:

- live goal и verified frontier;
- exact node/source/theorem/consumer pins;
- статус consumer contract и следующего joint;
- один настоящий blocker;
- own/foreign dirty split;
- следующий разрешённый action.

`FATAL` останавливает работу. `HOLD` означает адресный недостающий контракт,
review или validation receipt; его нельзя маскировать зелёным общим статусом.
Если `THEOREM` или `TERMINAL_CONSUMER` не выбраны, сначала связать exact edge —
математика ещё не запускается.

## Селектор

Physical Route B goal с `STATUS: OPEN` старше task pointer. Исполняется ровно
один goal. `PAUSED_RESTORABLE` не исполняется. Если открытых целей несколько,
goal/state/source pin расходятся, либо relevant foreign dirty path пересекает
scope, остановиться fail closed.

При отсутствии physical goal допустим только `docs/Codex/CURRENT.md` со
`status: ACTIVE`, одним `task_file` и точным latest-changing `source_commit`.
`EMPTY` и `CLOSED` ничего не выбирают. Следующий номер не угадывать: новый goal
требует validated source-locked `NEXT_GOAL_SPEC`.

Для Route B plan обязан совпасть с:

- `docs/routeB_bus/`;
- `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json`;
- `orchestrator/state/CHANNEL_RUNTIME.json`;
- `orchestrator/state/NODE_REGISTRY_V10.json`.

`PROJECT_ORCHESTRATOR.md` задаёт ранг route, но не operational address.

## Proof loop

Работать только по карте plan:

```text
contract -> suppliers -> preflight -> bridge -> Lean -> close -> recompute
```

Перед отсутствием, внешним поиском или созданием объекта — `ask.sh`. После
точной Lean-цели — `scripts/supplier_preflight.py`. Fast miss не является
отсутствием. Только `EXACT_FIT` закрывает reuse target. `COMPLETE_ABSENCE`
разрешает лишь последующее решение о создании, не потребление.

Поиск по альтернативным названиям начинается с executable
`q3_search_intent.v1`: exact goal/consumer, смысловая поверхность, канонические
термины, типизированные alias hypotheses и false friends. Preflight сам строит
3–5 первичных запросов и не более одного feedback batch. Интернет-публикации
возвращаются только как metadata candidates; название или похожий abstract не
являются semantic fit. `DISCOVERY` ничего не допускает, `ADMISSION` всё равно
требует exact declaration и `EXACT_FIT`.

Exact execution edge — одна тройка `node + theorem + consumer`. Unselected edge
остаётся `HOLD`. После закрытия узла повторно запустить `workflow_runtime.py
plan`; старый план не переносить вперёд.

## Scoped semantic gate

- `HELPER` допускает ноль reviews только при полном отсутствии semantic
  triggers.
- `SEMANTIC_BRIDGE` требует один non-self exact-payload review.
- `ROOF_CHANGE` требует owner signoff и второй non-self review.
- `CANDIDATE` может пройти isolated compile, но не потребляться.
- Исторический `HISTORICAL_V9_UNMAPPED` остаётся `HOLD`.
- Kernel-green без admission не является supplier authority.

Deep gate проверяет exact edge, source/consumer blobs, полный relevant import
closure, toolchain, elaborated types, стандартные axioms, semantic/validation
digests, lock и неизменность read epoch.

## Review и транспорт

Обычный goal close делает ноль вызовов к Прошке. Review разрешён только своим
control gate и только в одном living chat неизменной six-field phase key.
Substantive request передаётся одним byte-exact UTF-8 `.txt`; controlling body
в composer не вставляется. `review-plan` обязан связать attachment bytes,
SHA-256, request commit/ID, boundary ID и short instruction. Plan не является
delivery receipt: нужны наблюдаемые sent message, exact file tile и natural
reasoning start.

Исторический `orchestrator/three_body_loop.py` — ручной v9 compatibility tool.
Не использовать его как startup front door, не создавать через него новые v9
requests/admissions/leases и не переносить v9 receipt в native v10 admission.

## Закрытие

Исполнение идёт через зарегистрированный runtime:

```bash
python3 orchestrator/workflow_runtime.py run --through close-node \
  --owned-path <path> --attempt-payload <q3_goal_attempt.v1.json>
```

Добавить остальные exact arguments, которые потребует plan. Узел закрыт только
после kernel/source gate, `CLOSES`/`OPENS`, applicable review/admission,
branch-decision, AUTOPSY/insight/card debt, assembly/publication debt и
минимального derived repair closure. Manual semantic debt докладывается с
адресами и не зеленеет автоматически.

После verified close:

1. повторить `workflow_runtime.py plan`;
2. запустить применимый `close-session` или `close-phase`;
3. проверить exact owned diff и relevant tests;
4. по действующему goal-scoped grant сделать scoped commit, rebase и push;
5. foreign dirty paths не stage и не изменять.

Route promotion, publication и `PX_RH_CLAIM` из закрытия не следуют.
Goal terminalization пишет рядом `<stem>.goal-close.json` перед переводом
`STATUS: OPEN -> CLOSED`; phase transition пишет `<stem>.phase-close.json`
только после новой six-field phase key и зелёного phase-close. Результаты
`CLOSE_RETRY_PENDING`, `GOAL_TERMINALIZE_PENDING` и
`GOAL_CLOSE_DELIVERY_PENDING` требуют повторного plan, а не ручного обхода.

## Дополнительные карты только по триггеру

- Развилка/возврат: `docs/GENEALOGY.md`, `docs/Progress_Log.md`,
  `docs/RECORDING_RULES.md`.
- Аномалия control/tool/database: `docs/SYSTEM_SPEC_2026-08-05.md` и
  `specs_docs/README.md`.
- Aristotle: `q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md` и
  `q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`.
- PSD/Step33: только active `ACTIVE/PSD_STEP33_MONITOR.md`.
- H1/PO3: только active `ACTIVE/PHASE_MONITOR.md`.
- Sprint: только `ACTIVE/SPRINT_MONITOR.md` со `status: ACTIVE`.

Dormant, parked и closed monitors ничего не выбирают.
