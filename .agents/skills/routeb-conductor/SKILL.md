---
name: routeb-conductor
description: >
  Ведёт текущую Route B петлю по физической шине и Control v9: выбирает ровно
  один goal, проверяет runtime-plan, маршрутизирует локальную работу и
  source-locked review lifecycle, закрывает каталоги/карту/blueprint и scoped
  delivery. Триггеры: «продолжай петлю», «что на шине», «забери вердикт»,
  «route b», «кондуктор», восстановление после перезапуска.
---

# Route B conductor — актуальный транспорт

Эта skill является транспортом, а не отдельным policy kernel, селектором или
математическим судьёй. При любом расхождении текущий
`docs/CODEX_CONTROL.md`, физическая шина и строгие gates старше этой инструкции.

## Вход

Полностью прочитай канонический bootstrap, затем:

```bash
bash specs_docs/session_start.sh
python3 orchestrator/workflow_runtime.py plan
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```

`orchestrator/state/state.json`, старые conductor queues, browser composer state
и исторические мониторы не являются текущим resume authority. Точный адрес
дают один `OPEN` physical goal, `goal_runtime.py`, execution state и
`CHANNEL_RUNTIME.json`.

Красный startup останавливает математику. Воспроизводимый control/tool defect
ремонтируется первым в точном owner scope; его нельзя маскировать зелёным
планом.

## Боевой бриф и proof loop

`workflow_runtime.py plan` обязан содержать `logical_plan.proof_loop` со schema
`q3_proof_loop.v1`. Это machine-readable operating card, а не новый policy
kernel. В начале каждой сессии сначала выдай владельцу короткий battle brief:

- сколько канатов закрыто и открыто;
- live physical goal и verified frontier;
- связан ли exact consumer contract;
- статус следующего joint и один настоящий blocker;
- математический маршрут текущего joint, если он уже связан.

Не пересказывай полную служебную диагностику до этого брифа. При
`next_joint.status = BLOCKED` не начинай математику и не выдумывай адрес. При
`CONTRACT_REQUIRED` используй physical goal, `brief.py`, `cheap.py`, assembly и
consumer-first contract, чтобы выбрать один допустимый joint; текстовый кандидат
не становится supplier до `EXACT_FIT`. При `READY_FOR_PREFLIGHT` запускай один
precommitted proof cycle. После закрытия узла заново запусти runtime-plan и
потребляй пересчитанный `proof_loop`, а не старую очередь.

Кратчайший доказуемый путь минимизирует ожидаемую стоимость честного закрытия:
proof difficulty, semantic gap, Lean formalization cost, dependency risk и
unverified assumptions. Число теорем само по себе не является стоимостью.

## Один цикл

1. Привяжи owner scope к одному physical goal или source-locked Codex task.
2. Используй runtime-plan для exact goal, owned scope, expected writes,
   fingerprints, derived status и scoped assembly debt.
3. Перед утверждением отсутствия, внешним поиском или созданием объекта запускай
   `ask.sh`; после точной Lean-цели запускай `supplier_preflight.py`. Совпадение
   остаётся кандидатом до `EXACT_FIT`.
4. Выполни один precommitted proof/test cycle. Странность запиши до объяснения;
   развилку — в момент выбора.
5. Закрой результат через attempt/optional insight event, kernel/axiom gate,
   derived closure и session close.
6. При настоящем завершении узла обнови `CLOSES`/`OPENS`, scoped assembly,
   картографию и publication blueprint. Затем commit только owned paths,
   `pull --rebase --autostash` и push в рамках goal-scoped grant.
7. Только после доставленного close selector выбирает следующий physical goal
   или валидирует source-locked `NEXT_GOAL_SPEC`.

`workflow_runtime.py run --through close-node` требует точные `--owned-path`,
`--attempt-payload` и kernel gate для owned Lean. Новый объект дополнительно
требует `--query`; supplier candidate/target передаются парой.

## Proshka

Обычное goal close делает ноль вызовов. Review разрешён только для:

- стратегического `MINT`, `PROMOTION`, `FRONT_CHANGE` или `FATAL`;
- одного `EXPLORATION_REVIEW` после шести зарегистрированных no-delta циклов;
- `PX_RH_CLAIM_REVIEW`, который всегда возвращает owner boundary.

До review локально отработай фазу до реальной стены и собери 2–4 связанных
блокера. Один unchanged six-field phase key использует один living chat.

Judge transport выполняет текущее активное Codex-тело на любом поддержанном
host через тот же living chat. Перед отправкой запусти `workflow_runtime.py
review-plan` с exact attachment, request commit, request ID, boundary ID и
ожидаемым SHA-256. Только queue status `OPEN` допускает dispatch;
`IN_REVIEW`/`ANSWERED` запрещают повторную отправку.
При `REVIEW_DISPATCH_READY` самостоятельно прикрепи ровно один byte-exact UTF-8
`.txt`, сверь file tile и отправь каноническую короткую инструкцию. Отдельный
репозиторный owner click/OK не требуется; если активный browser runtime требует
обязательное action-time safety confirmation, исполни эту внешнюю границу и не
пытайся обходить её другим UI-инструментом. Вставка controlling request в
composer и открытие нового чата запрещены. `review-plan` не является delivery
receipt; доставка установлена только после наблюдения sent message и начала
natural reasoning. Ответ
принимается только с exact source commit, blob, verdict path/blob и operative
`TRY_`, `KILL_`, `RUN_` либо `OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM`.

После нового `[Proshka]` commit: fetch, безопасный rebase/autostash, проверка
request/verdict binding, затем `verdict-intake` или phase-close migration.
Непрожатый verdict делает полки неполными и блокирует продолжение.

## Карта и публикация

`MAP.md` хранит устойчивую топологию и запреты, но не текущий следующий шаг.
Живой адрес: `routeb_status.py`, physical goal, `brief.py`, `cheap.py` и assembly.
`MAP_COVERAGE.md` доказывает только файловое покрытие, не семантическую
актуальность карты.

Когда меняются RouteB sources, закрывающий DAG обновляет inventory и atoms;
после добавления/переименования — MAP coverage; после assembly/proof-registry/
EnvDump изменений — publication blueprint. Blueprint является внутренним
скелетом и не даёт proof authority. Цитирование публикации отдельно требует
source verification, usage card/PDF/REFERENCES/bib validation. Внешняя
публикация всегда отдельная owner-authorized action.

## Стопы

- Не использовать `orchestrator/state/state.json` как resume authority.
- Не вставлять controlling request в browser composer, не открывать новый чат и
  не выдумывать repository-level подтверждение поверх обязательной host policy.
- Не называть plan исполнением, `KERNEL_GREEN` semantic admission или RH.
- Не трогать foreign dirty paths, force-push, main merge, Route promotion или
  `PX_RH_CLAIM` без их точной отдельной authority.
- Не запускать Aristotle без точного source-locked theorem contract и
  применимой Aristotle skill.
