# SOURCE DRAFT — ROUTE B CONTRACT v2 STATUS ADDENDUM v1 (закрытие находки M3-б)

```yaml
STATUS: RATIFIED_SOURCE_PRESERVED
RATIFIED_AT: 2d2a6441328f70ae28de5058c336518b6733ff04
CANONICAL_TARGET: docs/ROUTE_B_CONTRACT_V2_STATUS_ADDENDUM_v1.md
AUTHOR: Mythos (аудит 2026-08-27)
ROUTING: показан владельцу; коммитит Linux-канал/Codex ТОЛЬКО по per-action OK (R0.1/R0.2)
OPTIONAL_COUNTERSIGN: Прошка (кандидат в PROSHKA_QUEUE, батчевать по правилу 2–4)
BRANCH: rh_clean
TIP_AT_DRAFT: d78a18ea5bd13c47db643a98d0673c21e086ff1b
KERNEL_SHA256_8: a13dfbe1
DECK_SHA256_8: 46065599
TARGET_PATH_PROPOSED: docs/ROUTE_B_CONTRACT_V2_STATUS_ADDENDUM_v1.md
IMMUTABILITY: ROUTE_B_THEOREM_CONTRACT_v2.md НЕ редактируется (CLOSED_GOAL_IMMUTABLE-аналог);
  это отдельный версионированный артефакт
ROUTE: CHALLENGER_NOT_RH; BUS_010: VOID; GOAL_055: HOLD; PX_RH_CLAIM: NOT_MADE
GLOSSARY: новых терминов НЕТ; статусная лексика взята дословно из существующих файлов
W9: CLOSES [M3b_TWO_DAGS_WITHOUT_WRITTEN_BRIDGE]; OPENS []
```

## 1. Проверяемые факты (все — из живого дерева @ d78a18e)

1. `q3.lean.aristotle/docs/ROUTE_B_THEOREM_CONTRACT_v2.md` (2026-07-10) задаёт
   W′-детекторную цепь (QuantitativeSafeWitness → ZEO → RH) и реестр PO-0…PO-13.
2. `ROUTE_B_EXECUTION_CONTROL.md` подаёт эту цепь как «Исправленная финальная
   цепь», а стадии RB-0…RB-10 стоят `BLOCKED_BY_RB-0`; собственная шапка файла
   уже называет v2 «historical candidate» (строка «CONTRACT: v2 historical
   candidate; no mathematical front selected»).
3. С 2026-08-11 исполняемый DAG Route B — мастер-маршрут
   `docs/routeB_bus/proshka/PROSHKA_MASTER_ROUTE_REALZERO_GROUND_DIAGONAL_TO_XI_2026-08-11.md`
   (гол 058, SOURCE_PIN `b124fba1fcf33cd105a078254caa9d62240d59e6`), ворота
   G0–G5; физическая шина и вердикты августа исполняют именно его.
4. `SESSION_ENTRY.md` (Updated 2026-08-09, т.е. ДО мастер-маршрута) в scoped
   precedence Route B, пункт 4, всё ещё называет v2 источником DAG.
5. Письменного моста «v2 ↔ маршрут 058» в дереве нет (проверено поиском по
   `THEOREM_CONTRACT|Contract v2|CONTRACT_V2` в docs/routeB_bus/ на 2026-08-27).

## 2. Предлагаемая статусная запись (одной строкой)

`ROUTE_B_THEOREM_CONTRACT_v2.md` = **historical candidate** (лексика его же
шапки в EXECUTION_CONTROL): не исполняется, не убит, не редактируется; его
дисциплинарные статьи (K7, анти-циркулярность, kill-код
`SAFE_IS_RH_REPACKAGING`, запрет tau0-подмены) остаются общепроектными.
Исполняемый DAG Route B = мастер-маршрут 058 (G0–G5) — что уже следует из
прецедентности физической шины; данный addendum лишь материализует это письменно.

## 3. Карта обязательств v2 → маршрут 058 (предложение; ратифицировать построчно)

| v2 | Содержание | Статус под 058 | Где живёт теперь |
|---|---|---|---|
| PO-0 | crosscheck/провенанс/синхронизация | STANDING_PRACTICE | слоёная прецедентность SESSION_ENTRY + `routeb_status.py --check`; код `CONTROL_PLANE_DRIFT` |
| PO-1 | словарь H0 (α, crosswalk, N-режим) | ABSORBED_RESHAPED | ворота G0 гола 058 («точный объект, координата, нормировка») |
| PO-2 | чётность (ParityLock) | ABSORBED_RESHAPED | внутри G1 («simple-EVEN ground-пакет»); parity-работа 08-26 (G6N1…GroundParityRealification) |
| PO-11 | ZEOExportSoundness (OPEN_CRITICAL) | ABSORBED_RESHAPED | G4/G5 + именованные слоты `MontelAnchorGate`, `SlotS2`, `Theorem510RealZeroBridge` в `CanonicalRHRouteSkeleton.lean` (sha256 `2e849d67…`); содержание «Руше/идентификация предела/no escaping zeros» перераспределено по слотам |
| PO-12a/12 | SAFE feasibility + четыре листа | DORMANT_W_PRIME_SPECIFIC | без консьюмера при спящей W′-цепи; kill-коды остаются общей дисциплиной |
| PO-3…PO-10 | supply-цепь W′ (defect equation → DetectorBridge) | DORMANT_W_PRIME_SPECIFIC | реактивируются только с реактивацией W′-цепи отдельным решением |
| PO-13 | Lean-приёмка (zero sorry/axioms, скан, #print axioms) | STANDING_PRACTICE | пер-узловая практика Route B (production-дерево: 348 файлов, 0 sorry/admit/axiom, токен-проверка 2026-08-27) |

## 4. Сопутствующие однострочные правки (исполняет Codex; те же per-action правила)

1. `SESSION_ENTRY.md`, scoped precedence п.4: «`ROUTE_B_THEOREM_CONTRACT_v2.md`
   и `ROUTE_B_EXECUTION_CONTROL.md` задают DAG» → «Исполняемый DAG задаёт
   мастер-маршрут 058 (см. ADDENDUM v1); v2 — historical candidate, его
   дисциплинарные статьи действуют».
2. `ROUTE_B_EXECUTION_CONTROL.md`: строка-указатель на этот addendum рядом с
   «CONTRACT: v2 historical candidate» (сама секция «Исправленная финальная
   цепь» остаётся как история W′-ветки с датирующей пометкой).

## 5. Чем этот addendum НЕ является

Не route-kill v2, не промоушен 058, не изменение ранга CHALLENGER/NOT_RH, не
новая математика, не goal. Никакой номер шины не потребляется.
