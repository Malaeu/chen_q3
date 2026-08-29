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

Control v9: Linux единолично владеет batching и judge transport. Прямая
Mac/Codex→Proshka отправка, вставка controlling request в composer и открытие
нового чата запрещены. Запрос — byte-exact UTF-8 attachment и canonical
request/state CAS lifecycle; ответ принимается только с exact source commit,
blob, verdict path/blob и operative `TRY_`, `KILL_`, `RUN_` либо
`OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM`.

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
- Не писать в browser composer и не обходить Linux judge transport.
- Не называть plan исполнением, `KERNEL_GREEN` semantic admission или RH.
- Не трогать foreign dirty paths, force-push, main merge, Route promotion или
  `PX_RH_CLAIM` без их точной отдельной authority.
- Не запускать Aristotle без точного source-locked theorem contract и
  применимой Aristotle skill.
