# BUS GOAL 008 — ContractV2CrosscheckAndStateSync_v1

STATUS: READY.
SCOPE: NOT_RH; ZERO compute (никаких численных моделей); state/provenance only; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.

## Purpose

Уровень 0 контракта v2 (PO-0): заверить контракт, синхронизировать контрольную плоскость и закрыть провенанс источников — ДО любых kill-гейтов уровня 1 и тем более тяжёлой аналитики уровня 2.

## Immutable inputs (read, do not modify)

- `docs/ROUTE_B_THEOREM_CONTRACT_v2.md`
- `docs/ROUTE_B_THEOREM_CONTRACT_v1.md` (SUPERSEDED — только для сверки Δ-списка)
- `docs/ALPHA_DEMAND_AUDIT.md` (TAG: NOT_A_DEFINITION_SOURCE)
- `docs/ALPHA_DETECTOR_OBJECT_LOCK.md`
- `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md`
- `docs/CODEX_REORIENT_BRIEF_2026-07-10.md`
- `ROUTE_B_STATE.md`, `loop_state.json`
- `docs/trackB/WEIL_SQUARE_CLASS_SPEC.md`

## G1 — Contract v2 crosscheck

1. Проверить существование v2 и пометку SUPERSEDED в v1.
2. Символьно перепроверить центральную лемму §3: из W′² = |b|²·λ·α/Δe и трёх границ вывести показатель q_b + (1+r_α−r_Δ)/2 и строгое условие r_Δ − r_α > 2q_b + 1. Подтвердить или опровергнуть «поправку +1» (никаких чисел — только алгебра степеней).
3. Проверить, что все восемь пунктов Δ-списка (v2 §1) действительно отражены в тексте v2.
4. Проверить, что каждый путь/sha, процитированный в v2, существует и совпадает.

PASS: `CONTRACT_V2_LOCKED`.
FAIL: `CONTRACT_DEPENDENCY_GAP` (указать точную строку), `POWER_ARITHMETIC_MISMATCH`.

## G2 — State/loop синхронизация

1. Зафиксировать текущую рассинхронизацию: `ROUTE_B_STATE.md` содержит историю до `PoissonResidualChannelAudit_v1`, `loop_state.json` — `last_completed_gate = RegisterReadOnlyDocs_v1`.
2. Обновить `loop_state.json`: перенести линию гейтов 001–007 (имена + вердикт-коды + даты из STATE), `current_gate = AWAIT_BUS`, `next_gate = STOP_NO_NEXT_GATE_SELECTED`.
3. Ничего в `ROUTE_B_STATE.md`, кроме финальной одной history-строки этого гейта, не менять.

PASS: `STATE_LOOP_SYNCED`.
FAIL: `STATE_SYNC_CONFLICT` (перечислить расхождения, ничего не удалять).

## G3 — Source provenance

1. Подтвердить физическое наличие и корректные шапки:
   - `docs/ALPHA_DEMAND_AUDIT.md` — первая содержательная строка TAG: NOT_A_DEFINITION_SOURCE;
   - `docs/ALPHA_DETECTOR_OBJECT_LOCK.md`.
   Записать их sha256.
2. rGap13 source audit: найти в репо ВСЕ источники чисел вида «μ₁/(μ₃−μ₁)» (в частности значение ≈ 2.66e−8) и локального r1 = θ₁/λ₁(G_even) ≈ 9.51e−32. Для каждого: файл, строка, какой α-вариант (raw/projected/opt), какое N, чётностный статус прогона. НЕ вычислять новые значения.
3. Присвоить ровно один статус:
   - `R13_SOURCE_RESOLVED` — источники найдены, объекты разведены, коллизия имён снята переименованием rGap13;
   - `R13_SOURCE_COLLISION` — объекты смешаны в существующих файлах (перечислить где);
   - `R13_SOURCE_MISSING` — значение 2.66e−8 не найдено ни в одном артефакте.
4. Инвентаризация трёх реализаций α (raw/projected/opt): файл, строка определения каждой; БЕЗ выбора канонической (это PO-1).

PASS: `SOURCE_PROVENANCE_COMPLETE`.
FAIL: `SOURCE_POINTER_MISSING` (список), `ZEO_EXPORT_AMBIGUOUS` (если в репо найдены конфликтующие формулировки экспорта).

## Planted check (обязателен даже для ZERO-compute гейта)

В отчёте G1.4 обязан быть проверен и помечен ABSENT заведомо несуществующий путь-приманка:
`docs/ROUTE_B_THEOREM_CONTRACT_v3.md`.
Если чекер не сообщает его отсутствие — `PROVENANCE_CHECKER_INERT`, гейт недействителен.

## Required artifacts

- `bus/008_contract_v2_crosscheck_and_state_sync.answer.md`
- обновлённый `loop_state.json`
- ровно одна history-строка в `ROUTE_B_STATE.md`

## Required answer format

Начало файла — дословно:

```text
# MYTHOS_PROSHKA_HANDOFF: ContractV2CrosscheckAndStateSync_v1

STATUS: STOP.
SCOPE: NOT_RH; ZERO compute; state/provenance only; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.
```

Затем: Verdict (ровно один из PASS/FAIL-кодов на каждый G1/G2/G3 + planted), R1 — crosscheck-таблица Δ-списка, R2 — sync-протокол, R3 — provenance-таблица (файл:строка для каждого источника), ACTIONS LOG (команды; sha256 goal/answer/state/loop; scoped git add; unrelated files preserved), финал:

```text
No next gate selected.
No bus 009 file created or executed.
STOP.
```

## FINAL STEP

Одна history-строка в `ROUTE_B_STATE.md` с: `ContractV2CrosscheckAndStateSync_v1`; тремя кодами G1/G2/G3; статусом planted-проверки. Затем scoped `git add`, `git diff --check`. STOP.
