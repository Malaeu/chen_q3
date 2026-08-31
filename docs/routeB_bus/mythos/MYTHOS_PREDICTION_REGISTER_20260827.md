# MYTHOS PREDICTION REGISTER — 2026-08-27 (K6: публичный счёт на себя)

```yaml
AUTHOR: Mythos
KIND: PREDICTION_REGISTER   # не goal, не verdict; номера шины не потребляет
BRANCH: rh_clean
TIP_AT_REGISTRATION: d78a18e
KERNEL: a13dfbe1 · DECK: 46065599
TARGET_PATH_PROPOSED: docs/routeB_bus/mythos/MYTHOS_PREDICTION_REGISTER_2026-08-27.md
SCORING: любой канал с загруженным кернелом, по датам resolve-by; формулировки
  заморожены (registered wording may not drift, K6)
ROUTE: CHALLENGER_NOT_RH; PX_RH_CLAIM: NOT_MADE
```

## A. Закрытый счёт аудита 2026-08-27 (зарегистрировано ДО скана, отскорено ПОСЛЕ)

| # | p | Формулировка (сжатая) | Исход |
|---|---|---|---|
| P1 | 0.65 | вне production есть sorry; production-цепь чистая | HIT (270 sorry вне; RouteB 348 файлов — 0 sorry/admit/axiom, токен-скан) |
| P2 | 0.60 | ≥1 расхождение статусов между живыми доками | HIT (EXECUTION_CONTROL «прямо сейчас» ≠ живое состояние) |
| P3 | 0.60 | CLOSED_GOAL_IMMUTABLE держится на спот-чеке | HIT (goal 053/056m нетронуты после выпуска) |
| P4 | 0.75 | твёрдость в 1–2 RH-эквивалентных утверждениях, доки признают | HIT («alpha-Gate remains RH-equivalent core»; SAFE_IS_RH_REPACKAGING) |
| P5 | 0.50/0.80 | реальное K7-нарушение / хотя бы флирт | MISS/HIT (нарушения нет; флирт карантинирован NOT_THEOREM-метками) |
| P6 | 0.70 | процессного текста ≥3× больше математического | MISS (математический корпус доминирует: ~8.8 МБ шина+вердикты против ~0.1–1 МБ контрольной плоскости) |
| P7 | 0.55 | после C13 нет обновлённой приёмки колоды | SPLIT (стоячая приёмка пиннит старый хэш — да; но минт ратифицирован ebd1d70f) |

Мета-урок: оба промаха — в сторону ПРОТИВ проекта. Направление моего остаточного
перекоса измерено; негативные суждения дисконтируются, позитивные — нет.

## B. Открытые предсказания (скорить по датам)

### R1 [p=0.85] · resolve-by 2027-02-27
К дате НЕ существует kernel-green БЕЗУСЛОВНОЙ теоремы G3-трекинга в смысле
мастер-маршрута 058 (та же F_j отслеживает projected trial), принятой Прошкой
без классификации CONDITIONAL.
HIT = такой теоремы нет. MISS = есть (и это главный позитивный сюрприз года).

### R2 [p=0.60] · resolve-by 2026-09-24
За окно 2026-08-27…09-24 случится ≥1 вердикт-килл предложенного узла класса
«нормировка/шкала/знак» (образцы класса: 82ac9628 V0-preflight, c5524509 H2a-
predicate, 6a47f79c/809b776b от 27.08).
HIT = ≥1 такой килл. MISS = ноль киллов этого класса за окно.
Примечание регистрации: это ставка на СОХРАНЕНИЕ здоровой частоты киллов
(базовая частота августа ~2/нед), не против проекта.

### R3 [p=0.70] · resolve-by 2026-10-27
К дате несущий объект главного открытого гейта фронта G6/H2a сменится
(K4-джамп): не «selected Ferrers ground family / H2a-крыша текущей
параметризации», а другой объект, зафиксированный route-doc'ом или
мастер-вердиктом.
HIT = смена несущего объекта. MISS = фронт закрыт/продолжается на текущем
объекте. Пограничное: смена под-узловой репрезентации (как «compact Gamma →
Rayleigh-excess» 27.08) НЕ считается — только смена объекта самого гейта.

## C. Приложение: замороженный pre-scan файл (дословно)

# PRE-SCAN PREDICTIONS — Mythos repo audit, 2026-08-27 (K6)
Registered AFTER: clone, tree listing, PIN computation, kernel v3 full read, ARSENAL_CARDS diff (C13 mint).
Registered BEFORE: reading any contract, goal, verdict, ledger, session protocol, or Lean file content.
Wording frozen; scored at end of audit; no mid-analysis drift.

P1 [0.65]: Lean tree (outside archive/) contains ≥1 `sorry`/`admit`, but the
production chain gated by Прошка verdicts is sorry-free per its own ledgers.

P2 [0.60]: ≥1 factual status inconsistency between two live (non-archive)
documents — a goal CLOSED in one ledger but OPEN in another, or a stale hash
pin still cited as current after a legitimate change.

P3 [0.60]: Spot-check of 3 closed goal files via git history shows NO
post-closure semantic edit (CLOSED_GOAL_IMMUTABLE held; typo-level allowed).

P4 [0.75]: The mathematical hard core of Route B is concentrated in 1–2
statements that are RH-equivalent or stronger (hardness conserved, not
reduced), AND the docs somewhere admit this explicitly.

P5 [0.50 real violation / 0.80 at-least-flirting]: ≥1 place where a numeric
result is used in a way that flirts with K7 (computation near a quantifier),
even if formally quarantined.

P6 [0.70]: Live docs contain ≥3× more process/protocol text than mathematics
by byte count (process-heavy operation).

P7 [0.55]: After the C13 mint (2026-08-23), no updated Прошка deck-acceptance
pinning the NEW deck sha256 46065599 exists; standing acceptance still pins
018dbf6b only.
