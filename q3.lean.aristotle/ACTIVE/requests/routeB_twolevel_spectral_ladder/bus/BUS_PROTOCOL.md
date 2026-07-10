# BUS_PROTOCOL — файловая шина Mythos ⇄ Codex (goal bus)

Path: q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/bus/
Version: v1, 2026-07-07. Owner: Ылша. Writers: Mythos (goals), Codex (answers).

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

## Текущая очередь (roadmap, обновляет Mythos)

- 001 CombMeanValueFalsifier (F1/F2, почти ноль цены) — АКТИВЕН
- 002 (резерв) TAIL_RETURN_PROBE J=3000..5000 — средняя цена, по решению
- Параллельно вне шины: адверсарный прогон PEN_3_1_3 Прошкой (через Ылшу)
