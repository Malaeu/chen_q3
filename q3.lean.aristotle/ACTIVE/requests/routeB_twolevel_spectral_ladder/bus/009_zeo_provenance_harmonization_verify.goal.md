# BUS GOAL 009 — ZeoProvenanceHarmonizationVerify_v1

STATUS: READY.
SCOPE: NOT_RH; ZERO compute; provenance/status-language only; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched. Repair-гейт для провала G3 гола 008 (`ZEO_EXPORT_AMBIGUOUS`).

## Purpose

Гол 008 зафиксировал: контракт v2 честно держит экспортную стрелку `W′ → RH` в статусе OPEN_CRITICAL, но по репо разбросаны формулировки с несовместимым уровнем уверенности. Mythos внёс два ремонта (см. Immutable inputs). Задача 009 — проверить, что после ремонтов в репо НЕ осталось ни одного overclaim, и выдать замену вердикта G3.

## Immutable inputs (read, do not modify)

- `docs/ROUTE_B_THEOREM_CONTRACT_v2.md` (sha256 контролировать против R1.4 гола 008)
- `docs/CODEX_REORIENT_BRIEF_2026-07-10.md` — ПОСЛЕ ремонта Mythos (узел 2 переименован в «Детекторная цепь… PEN_CLAIMED_VERIFY», добавлена строка «[2.1/2.2 — формулы-эскизы; стрелка W′ → RH НЕ заверена: OPEN_CRITICAL]»)
- `docs/ALPHA_DETECTOR_OBJECT_LOCK.md` — ПОСЛЕ ремонта Mythos (к строке (S2) добавлена пометка «[Формула-эскиз; … OPEN_CRITICAL … — не теорема.]»)
- `docs/ALPHA_DEMAND_AUDIT.md` (TAG: NOT_A_DEFINITION_SOURCE)
- `bus/008_contract_v2_crosscheck_and_state_sync.answer.md` (раздел R3.5 — список конфликтов)
- `loop_state.json`, `ROUTE_B_STATE.md`

## G1 — Repo-wide overclaim scan

1. Область: `q3.lean.aristotle/**` + `docs/trackB/**` (markdown, python, json; из скана исключаются только каталоги `out/` как данные).
2. Токены: `ZEO`, `AlphaDetector`, `W'`, `W_prime`, `W′`, `⟹ RH`, `=> RH`, `-> RH`.
3. Каждое совпадение классифицировать ровно одним из:
   - `HISTORICAL_ROW` — неизменяемые исторические строки (bus-ответы, History-раздел STATE, старые actions-логи);
   - `CONTRACT_ALIGNED` — рядом (та же строка или соседняя) присутствует один из маркеров: `OPEN_CRITICAL`, `PEN_CLAIMED_VERIFY`, `NOT_A_DEFINITION_SOURCE`, `диагност`, `эскиз`, `FIT_NOT_LAW`, `не теорема`, `is_proof: false`;
   - `OVERCLAIM` — строка статусного характера, подающая экспортную стрелку как доказанную/зарегистрированную-как-доказательство, без маркера.
4. Отдельно проверить четыре адреса из R3.5 гола 008 (brief:20-28; object-lock:15-16; legacy loop-регистрации; symbol_diagonal_crosscheck_v1) — для каждого указать новый класс.

PASS: ноль `OVERCLAIM` вне `HISTORICAL_ROW` → `ZEO_PROVENANCE_HARMONIZED`.
FAIL: `OVERCLAIM_LIST` — полная таблица файл:строка (ничего не править самостоятельно).

## G2 — Verification of Mythos repairs

Контент-проверкой (дословные подстроки) подтвердить оба ремонта в двух файлах из Immutable inputs. Зафиксировать их новые sha256.

PASS: `MYTHOS_REPAIRS_PRESENT`. FAIL: `MYTHOS_REPAIR_MISSING` (какая строка).

## G3 — Legacy-нейтрализация

Подтвердить и записать указатели: (а) `loop_state.json` содержит `legacy_AlphaDetector_ZEO_registration_is_proof: false`; (б) реклассификация `TAUTOLOGICAL_CHANNEL` для symbol_diagonal-канала видна в его файлах; (в) `zeo_export_current_status = OPEN_CRITICAL_ZEO_EXPORT_AMBIGUOUS` обновить на `OPEN_CRITICAL_HARMONIZED` только при PASS G1+G2.

## Planted check (обязателен)

Токен-приманка `ZEO_EXPORT_PROVEN_FULL` обязан быть просканирован по всей области G1 и доложен как ABSENT. Если чекер не сообщает его отсутствие — `PLANT_INERT`, гейт недействителен.

## Explicitly OUT OF SCOPE

- Никаких вычислений rGap13 (заблокировано до PASS PO-2: чётностные гейты 010/011).
- Никакого выбора канонической α (это PO-1).
- Никаких правок в docs/ (правки — только Mythos; Codex докладывает).

## Required artifacts

- `bus/009_zeo_provenance_harmonization_verify.answer.md`
- обновлённый `loop_state.json` (поля last_*, zeo_export_current_status по правилу G3.в)
- ровно одна history-строка в `ROUTE_B_STATE.md`

## Required answer format

Начало файла — дословно:

```text
# MYTHOS_PROSHKA_HANDOFF: ZeoProvenanceHarmonizationVerify_v1

STATUS: STOP.
SCOPE: NOT_RH; ZERO compute; provenance/status-language only; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.
```

Затем: Verdict (ровно один код на G1/G2/G3 + planted), R1 — таблица классификации совпадений (счётчики по классам + полный список OVERCLAIM, если есть), R2 — sha-таблица ремонтов, R3 — legacy-указатели, ACTIONS LOG (команды; sha goal/answer/state/loop; scoped git add; unrelated preserved), финал:

```text
No next gate selected.
No bus 010 file created or executed.
STOP.
```

## FINAL STEP

Одна history-строка в `ROUTE_B_STATE.md`: `ZeoProvenanceHarmonizationVerify_v1` + коды G1/G2/G3 + planted. Scoped `git add`, `git diff --check`. STOP.
