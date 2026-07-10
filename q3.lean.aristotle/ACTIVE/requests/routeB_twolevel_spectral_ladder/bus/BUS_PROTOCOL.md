# BUS_PROTOCOL — файловая шина Mythos ⇄ Codex (goal bus)

Path: q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/bus/
Version: v2, 2026-07-10. Owner: Ылша. Writers: Mythos (goals), Codex (answers).

## Именование

- Гол от Mythos:   `NNN_short_name.goal.md`   (NNN = 001, 002, ... строго по порядку)
- Ответ Codex:     `NNN_short_name.answer.md` (то же NNN и имя)
- Наличие `.answer.md` = гол закрыт. Никаких других маркеров не нужно.

## Правила Mythos

1. Пишет голы только в эту папку, только со следующим свободным NNN.
2. Каждый гол содержит REGISTERED-прогнозы ДО запуска (K6) и FINAL STEP.
3. Никогда не редактирует `.answer.md` и чужие файлы шины.
4. После ответа Codex: скорборд HIT/MISS, вскрытия, следующий гол NNN+1.

## Правила Codex

1. Исполняет ТОЛЬКО наименьший NNN без ответа; по одному голу за раз.
2. Ответ строго в формате MYTHOS_PROSHKA_HANDOFF + секция ACTIONS LOG
   (files+sha256, script+args, datasets+sha256, git status/diff).
   Отсутствие ACTIONS LOG = ответ REJECTED независимо от содержания.
3. После записи `.answer.md` — STOP. Следующий гол сам не выбирает,
   ждёт появления нового `.goal.md`.
4. Файлы `.goal.md` не редактирует. Дисциплина гейтов — по
   docs/MYTHOS_KERNEL_PROTOCOL.md (READ-ONLY, sha-пин в STATE).
5. Guardrails всех голов: NOT_RH, no Phase 2, no QW-formula changes,
   no packet-definition changes, Q3 mainline untouched — если гол
   явно не говорит иначе.

## Протокол пробуждения (wake)

- Mythos не имеет демона: его будит Ылша ОДНИМ словом «го» в чате.
  По «го» Mythos: читает bus/ с диска → скорит новый answer → пишет
  следующий goal → короткий статус + карта.
- Codex-сторона: Ылша настраивает вотчер/цикл на появление новых
  `.goal.md` (fswatch или ручной запуск) — зона Ылши.

## Текущая очередь выводится с диска

Статическая roadmap-таблица больше не является источником истины: она однажды
застряла на `001`, когда физическая шина уже ушла дальше.

Operational rule:

```text
active = smallest NNN with goal and without matching answer
if active is absent: NO_OPEN_BUS_GOAL / STOP
next free NNN is a number only, not a selected theorem gate
```

Текущий snapshot после Bus 008: пары `001..008` закрыты, active goal
отсутствует, следующий свободный номер `009`. `PO-0` остаётся открыт из-за
`ZEO_EXPORT_AMBIGUOUS` и `R13_SOURCE_MISSING`; 009 не становится задачей, пока
Mythos не создаст физический immutable goal.

Машинная проверка:

```bash
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```

Current address и proof-compiler DAG:

- `../ROUTE_B_EXECUTION_STATE.json`;
- `../ROUTE_B_EXECUTION_CONTROL.md`.
