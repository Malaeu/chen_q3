# BUS_PROTOCOL — файловая шина Mythos ⇄ Codex (goal bus)

Path: q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/bus/
Version: v3, 2026-07-11. Owner: Ылша. Writers: Mythos (goals), Codex (answers).

Owner authorization (2026-07-11): `OWNER_AUTHORIZED_AUTORUN`.
The owner explicitly removed the unconditional post-answer STOP for the
recursive Lamport master compiler. This authorization changes scheduling only;
it does not promote Route B, close a mathematical obligation, or relax
`NOT_RH`/axiom/circularity rules.

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
3. После записи `.answer.md` Codex завершает и валидирует текущую bus-
   транзакцию. В обычном `MANUAL_BUS` режиме затем действует STOP. В режиме
   `OWNER_AUTHORIZED_AUTORUN`, если физического unanswered goal нет, Codex
   переходит к первому допустимому листу рекурсивного master DAG без создания
   фиктивного следующего NNN. Появившийся физический unanswered goal всегда
   прерывает autorun и получает приоритет.
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
if active is absent and mode = MANUAL_BUS: NO_OPEN_BUS_GOAL / STOP
if active is absent and mode = OWNER_AUTHORIZED_AUTORUN:
    execute the first eligible master-DAG leaf
next free NNN is a number only, not a selected theorem gate
```

## OWNER_AUTHORIZED_AUTORUN

Canonical master files:

```text
../../routeB_lamport_rh_closure/MASTER_GOAL.md
../../routeB_lamport_rh_closure/STATE.json
../../routeB_lamport_rh_closure/START_GOAL.md
```

Autorun invariants:

1. Exactly one canonical proof leaf is active for mutation at a time.
2. Multiple independent workers may investigate that same leaf.
3. A leaf closes only by exact proof/falsification/route-kill/decomposition
   under the master contract and required validation.
4. After leaf closure Codex performs the legal assembly/zoom-out checks and
   selects the next eligible leaf without waiting for a new NNN.
5. Autorun stops only for a real mathematical fatal code, missing external
   authority/data that cannot be reconstructed safely, user pause, or an
   unanswered physical bus goal.
6. Codex does not manufacture `010_*` or later bus files merely to represent
   internal master leaves.
7. `PO-0`/ZEO provenance defects remain open facts unless independently
   repaired; autorun does not relabel them as proved.

Текущий snapshot после Bus 009: пары `001..009` закрыты, active physical goal
отсутствует, следующий свободный номер `010` остаётся несозданным. `PO-0`
остаётся открыт из-за `ZEO_EXPORT_AMBIGUOUS` и `R13_SOURCE_MISSING`; 010 не
становится задачей, пока Mythos не создаст физический immutable goal. В режиме
`OWNER_AUTHORIZED_AUTORUN` принял конечное определение `bDet` из immutable
owner input, но остановлен на внутреннем master leaf
`D0.7e.5 ExactWPrimeZeoCrosswalk` с кодом `D0_7E_XWALK_OPEN`: theorem shape
не закрывает лист, а exact alpha/DeltaE/delta_dict/limit/uniform-A_K ещё не
запинены. Это не создаёт Bus 010 и не закрывает PO-0/ZEO.

Машинная проверка:

```bash
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```

Current address и proof-compiler DAG:

- `../ROUTE_B_EXECUTION_STATE.json`;
- `../ROUTE_B_EXECUTION_CONTROL.md`.
