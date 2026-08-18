# ОТВЕТ 014a — PROSHKA_CHANNEL_WRITE_SCOPE (расширение канала 014 на запись)

`PROSHKA_CHANNEL_WRITE_SCOPE_EXTENDED`

Надстройка над `014_proshka_github_channel`. Гол 014 и его ответ **не
редактируются** — закрытый гол правится новым артефактом, а не правкой. Этот файл
задаёт действующую границу; при расхождении с §«Границы записи» ответа 014
действует то, что записано здесь.

## Что изменилось и почему

Гол 014 (2026-07-27) настраивал канал на **чтение**: Прошка читает материалы сам
через GitHub-коннектор, вместо ручных архивов. Ограничение «ничего за пределами
`docs/routeB_bus/` не трогать» стояло там по одной причине — в `docs/` лежат
личные архивы владельца, и зеркало в `docs/routeB_bus/` строили именно чтобы по
остальному `docs/` никто не ходил.

С 2026-08-17 Прошка пишет в репозиторий сам, включая `.lean`. Первым таким
коммитом был `9cc3e01b`. До 2026-08-18 это происходило вне записанного правила:
его протокол отдавал всю запись Codex'у, а ответ 014 ограничивал его шиной.

## Действующая граница записи

Разрешено ровно три места:

```text
docs/routeB_bus/**
q3.lean.aristotle/Q3/Proofs/RouteB/**
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/**
```

Запрещено:

```text
ROUTE_B_STATE.md, STATE.json      состояние ставит проверяющее тело, не автор
docs/routeB_bus/BUS_010*          BUS_010_VOID
чужой закрытый вердикт            CLOSED_GOAL_IMMUTABLE — только новый артефакт
AGENTS.md, docs/CODEX_CONTROL.md,
SESSION_ENTRY.md, CLAUDE.md       цепи исполнителя и наблюдателя
docs/** вне routeB_bus            личные архивы владельца — ограничение 014
                                  сохраняется дословно
всё прочее вне Route B            спрашивать
```

Ограничение гола 014 на личные архивы **не отменено и не ослаблено**. Расширение
касается только Lean-дерева Route B и каталога запросов — того, чего в 014 не
было вовсе.

## Почему это безопасно

Прошка не может проверить то, что пишет: у него нет Lean-toolchain. Поэтому его
запись даёт статус `SOURCE_WRITTEN` и никогда `PROVED`; ядро спрашивает
Linux-тело и возвращает вывод с профилем аксиом. Три узла подряд показали, что
это не формальность: источник приезжал с точными квитанциями и не компилировался,
неся `sorryAx`.

Состояние он не ставит — `ROUTE_B_STATE.md` закрыт для него, запись делает тот,
кто прогнал гейт.

## Ссылки

```text
контракт канала   docs/routeB_bus/014_proshka_github_channel.answer.md
протокол судьи    docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
                  разделы DIRECT REPO WRITE (W1-W8)
гейт-артефакты    docs/routeB_bus/LINUX_GATE_SAME_FAMILY_GROUND_TRIAL_COMPOSITION_CORE_2026-08-18.md
                  docs/routeB_bus/LINUX_GATE_COFINAL_SOURCE_RESIDUAL_GAP_TRANSFORM_TAIL_BUDGET_2026-08-18.md
```

`CHALLENGER_NOT_RH · BUS_010_VOID · ROUTE_PROMOTION=false · RH_CLAIM=false`
