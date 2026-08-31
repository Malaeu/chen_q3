# DRAFT [→CODEX] — CONTROL_PLANE_REFRESH: одна ограниченная контрольная транзакция (M3 а/в/г + K1-дыра чекера)

```yaml
STATUS: DRAFT   # исполнять только после per-action OK владельца
CLASS: CONTROL_PLANE_ONLY / ZERO_COMPUTE / NO_MATH
BRANCH: rh_clean
TIP_AT_DRAFT: d78a18e   # Codex переприннивает fresh HEAD при старте
SOURCE_AUDIT: claude.ai project → claude/MYTHOS_REPO_AUDIT_chen_q3_rh_clean_2026-08-27.md
BOUNDS: ROUTE, BUS_010, GOAL_055, PX_RH_CLAIM — не трогаются; номера шины не потребляются;
  доказательные файлы (*.lean) не изменяются
W9: CLOSES [M3a_STALE_NOW_HEADER, M3v_STALE_CANONICAL_REPO_PATH, M3g_STALE_DECK_ACCEPTANCE_PIN,
  K1_CHECKER_BLIND_SPOT_EXECUTION_CONTROL]; OPENS []
```

## Мотив (из аудита, проверяемо)

`ROUTE_B_EXECUTION_CONTROL.md` в секции «Короткий ответ прямо сейчас» утверждает
`RB-IDLE … next free number 010`, тогда как живое состояние — гол 058 открыт,
следующий номер 059 (вывод `routeb_status.py --check` 2026-08-27). Файл не менялся
с 056a30fc (08-13), шапка — эры 08-03. `routeb_status.py --check` при этом даёт
`CHECK: OK`, потому что ЭТОТ файл он не проверяет — детектор не видит данное
нарушение (K1-дыра). Плюс: `canonical_repo_path` в живом
`ROUTE_B_EXECUTION_STATE.json` указывает `/Users/emalam/GitHub/rh_lean_01_2026`
(Mac-путь, старое имя репо), а стоячая приёмка колоды
(`PROSHKA_VERDICT_ARSENAL_ACCEPTANCE_2026-08-17.md`) пиннит `018dbf6b…` при живом
`46065599…` (минт C13 ратифицирован — вердикт `ebd1d70f`, owner-ratified,
коммит ece40b7a — но единый актуальный пин отсутствует).

## Шаги (ровно эти, в этом порядке)

### Шаг 1. EXECUTION_CONTROL: снять ложное «прямо сейчас»

Файл: `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_CONTROL.md`.

1a. Заголовок секции «## Короткий ответ прямо сейчас» заменить на
«## Снимок состояния (датированный; НЕ текущее состояние)».

1b. Первой строкой секции добавить:
```text
СНИМОК ОТ: <дата исполнения>. Текущее состояние даёт ТОЛЬКО
`python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check`.
Прозаические снимки протухают; при расхождении верить чекеру и физической шине.
```

1c. Содержимое снимка перегенерировать из фактического вывода
`routeb_status.py --check` на момент исполнения (GOAL/STEP/BUS/ACTOR/ACTION),
строку `CONTRACT:` дополнить указателем на
`docs/ROUTE_B_CONTRACT_V2_STATUS_ADDENDUM_v1.md`, если/когда тот ратифицирован
(иначе оставить «v2 historical candidate» как есть).

1d. Секцию «Исправленная финальная цепь» НЕ удалять; над ней добавить одну
датирующую строку: «Историческая W′-ветка (v2); исполняемый DAG с 2026-08-11 —
мастер-маршрут 058» (или ссылку на addendum после ратификации).

### Шаг 2. canonical_repo_path

Файл: `.../ROUTE_B_EXECUTION_STATE.json`.

2a. `"canonical_repo_path": "/Users/emalam/GitHub/rh_lean_01_2026"` →
`"/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean"` (живой Linux-канон chen_q3@rh_clean).
Mac-двойник остаётся описанным в `ROUTE_B_STATE.md` (строка про stale twin) — её
не трогать.

2b. Проверить зеркала: `grep -n "canonical_repo\|rh_lean_01_2026" loop_state.json`
и request-local файлы; зеркальные поля обновить в ТОЙ ЖЕ транзакции
(иначе — самодельный `CONTROL_PLANE_DRIFT`).

2c. Убедиться, что ни один валидатор не сверяет путь с диском Mac
(`grep -rn "canonical_repo_path" q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/*.py`).

### Шаг 3. Закрыть K1-дыру чекера (симптом лечится шагом 1, генератор — здесь)

Файл: `routeb_status.py`. Добавить в `--check` read-only проверку:

3a. Распарсить из EXECUTION_CONTROL.md строку `СНИМОК ОТ: <дата>` (или её
отсутствие) и greppable-поля снимка (goal NNN, next-number).

3b. FAIL с кодом `CONTROL_PLANE_DRIFT_EXECUTION_CONTROL`, если: снимок без даты;
или NNN/next-number снимка расходятся с bus-сканом; или дата снимка старше
`ROUTE_B_EXECUTION_STATE.json:updated_at` более чем на 14 дней.

3c. Чекер остаётся read-only; никаких автоправок.

### Шаг 4. Пере-пин приёмки колоды — элемент очереди к Прошке (НЕ немедленная отправка)

В `docs/routeB_bus/PROSHKA_QUEUE.md` добавить OPEN-элемент (REQ-id присваивает
Linux-тело по дисциплине очереди; батчевать по правилу 2–4):

```text
REQ-<id> STATUS: OPEN — Пере-пин приёмки арсенала: подтвердить действующую
колоду 13 карт ARSENAL_CARDS_v1.md sha256
46065599a77c36df14cdda1dcb7e838fe1a23789c7f31736d5890255a08b0918
(заменяет пин 018dbf6b… из PROSHKA_VERDICT_ARSENAL_ACCEPTANCE_2026-08-17;
минт C13 уже ратифицирован вердиктом ebd1d70f, owner-ratified, ece40b7a).
Ожидаемый ответ: одна строка-приёмка с новым EXPECTED_SHA256.
```

### Шаг 5. Верификация и закрытие

5a. `python3 routeb_status.py --check` → EXIT 0 (и умышленный негативный тест
шага 3: временно испортить дату снимка → FAIL → вернуть).
5b. `bash specs_docs/session_start.sh` → зелёный.
5c. `git diff` — ревью, что затронуты ТОЛЬКО перечисленные файлы.
5d. Коммит-манифест владельцу (per-action OK), push только после OK.

## Явные запреты

Не редактировать v2-контракт, вердикты, goal/answer-пары, ARSENAL_CARDS_v1.md.
Не создавать новые голы. Не менять ROUTE/BUS_010/GOAL_055/PX_RH_CLAIM.
