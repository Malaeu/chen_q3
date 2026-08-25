# PROPOSAL — PROSHKA_SYSTEM_PROMPT v2.1 SHADOW (decision-theoretic + certificate-first delta)

```yaml
ARTIFACT_CLASS: PROPOSAL_RELAY
ORIGIN: внешний корреспондент владельца (GitHub-доступ на чтение), 2026-08-26
RELAY_STATUS: текст ниже — пересказ-артефакт; НЕ директива
TARGET: PROSHKA_SYSTEM_PROMPT_v2.md (HARD, sha-зеркало) — живой файл НЕ тронут
ROUTE: судья адъюдицирует по своему мандату -> shadow-бэктест -> owner ratification
VERIFIED_BY_LINUX_FROM_DISK:
  - blob SHA v2 = 00bfecaf84de3a8b48c79e9fb0e25f45daf168f5 (точно)
  - drift подтверждён: v2 строка 13 говорит "C01..C12"; C13 ратифицирована
    2026-08-23 и используется живыми вердиктами
  - v2 строка 297 = "next_decisive_test: <cheapest belief-changing test>"
  - PROJECT_INSTRUCTIONS_v3_arsenal.md несёт K9 (ARSENAL OF MOVES)
NOT_VERIFIED (нужен судья/бэктест): совместимость новых полей заголовка с
  парсерами; утверждения о полноте покрытия K1-K8 в v3; оценка процессного веса
OVERLAP_WITH_ALREADY_DONE:
  - VOI-гейт уже вписан на слое Linux-тела и очереди (38e4c1b7):
    ветки "что меняется в действиях" в шаблоне PROSHKA_QUEUE — сделаны
  - certificate-first рамка уже лежит: docs/FINITE_CERTIFICATE_PRINCIPLE.md
    (+ кандидат FINITE_CERTIFICATE_RECEIVER)
  - W9->HARDNESS_DELTA требует синхронной правки SUPPLIER_CONTRACT (HARD,
    per-action OK владельца) — очередь за ратификацией судьи
KNOWN_RISK_NOTE: дрейф словаря операторов уже ЕСТЬ (вердикты судьи используют
  CONSUMER_STRENGTH_REDUCTION, ENERGY_REPRESENTATION, TYPE_BOUNDARY,
  FUNCTIONAL_AUDIT вне реестра 2026-08-06; strict-валидация красная) — новые
  поля заголовка без обновления реестров усилят этот класс проблем; дельта
  сама это учитывает (не менять first-line grammar), но реестры надо вести
```

Полный текст дельты корреспондента (дословный пересказ):

---

## 1. Главный вердикт корреспондента

Новая философия уже сидит в v2 процентов на семьдесят (K1 judge-before-player,
K2 cheapest-decisive-test, K4 rename-until-it-computes, K8 compress-the-unknown,
M0–M4, W5, W9). Но формализована не до конца: строка
`next_decisive_test: <cheapest belief-changing test>` несёт архитектурную
ошибку — belief-changing не равно decision-changing. Тест может дать десять
бит и убить второстепенную гипотезу, не изменив следующий ход — тогда его
решенческая ценность (VOI) нулевая.

## 2. Пять предлагаемых изменений (сжатая форма; полный текст — у владельца)

1. K2: kill-power/cost -> NET_VOI. Для каждого зонда объявлять
   DECISION_AT_STAKE / CURRENT_BEST_ACTION / ACTION_AFTER_EACH_OBSERVATION /
   полную цену и риск. Если все ветки дают одно действие — VOI_CLASS: ZERO,
   зонд не запускается. Числовой EVOI только при декларированных приорах;
   иначе ordinal-класс POSITIVE | ZERO | UNKNOWN. Lookahead по умолчанию 1;
   глубина 2 только с COMPLEMENTARITY_WITNESS.

2. P2 -> Certificate-First Gate: обязательный каскад
   exact identity/counterexample -> global certificate (factorisation /
   dual witness / calibration / coercive tail + finite core / monotone
   potential) -> finite-core reduction -> localized inequality -> bounded
   diagnostics -> Lean. Каждый маршрут объявляет CERTIFICATE_SHAPE,
   DISCOVERY_COST_CLASS и VERIFICATION_COST_CLASS раздельно (короткий
   сертификат может проверяться за секунду и находиться год).

3. W9 -> frontier-hardness gate: CLOSES/OPENS остаются, добавляются
   FRONTIER_BEFORE/AFTER, HARDNESS_DELTA (SHRUNK | REPARAMETERIZED |
   UNCHANGED | GREW), COMPRESSION_WITNESS. Старый запрет — дефолт;
   единственное исключение — REPRESENTATION_PROGRESS со свидетелем сжатия
   (бесформенная бесконечная стена -> конечные типизированные обязательства,
   кванторы не усилены, предположения не спрятаны, потребитель явен).
   ТРЕБУЕТ синхронной правки SUPPLIER_CONTRACT — иначе старый W9 перебивает.

4. ROLE_MODE: JUDGE | AUTHOR — firewall. В JUDGE не писать судимый объект;
   в AUTHOR не допускать семантически собственный source; чистый Lean-гейт
   даёт только KERNEL_GATE: GREEN, а PROVED — лишь после независимого
   семантического аудита вторым телом или владельцем
   (KERNEL_GREEN != SEMANTICALLY_ADMITTED — уже записано в карте Agent OS).

5. Prompt drift: убрать из промпта динамические факты (C01..C12 при живой
   C13 — пойманный пример), не дублировать K1-K8 при живом KERNEL v3 (K1-K9);
   слоистая сборка SLOW CORE / JUDGE POLICY / FAST LOOP / RUNTIME STATE /
   INCIDENT MEMORY, текущие факты — из репозитория, не из текста промпта.
   Session-lock шапка: KERNEL_SHA / OPERATIONAL_PROMPT_SHA /
   SUPPLIER_CONTRACT_SHA / ARSENAL_MANIFEST_SHA / CAPABILITY_LOCK;
   недостижимый источник -> DEEP_VERDICT_AUTHORIZED: false (fail-closed).

Плюс: расширение машиночитаемого заголовка вердикта (ROLE_MODE,
DECISION_AT_STAKE, HARDNESS_DELTA, KERNEL_GATE, SEMANTIC_ADMISSION,
PROBE_BLOCK, CERTIFICATE_BLOCK) БЕЗ изменения first-line грамматики;
новый M4-скоринг (5..0 с VOI-семантикой; два подряд <=2 -> STOP_PROBING).

## 3. Протокол внедрения (корреспондент, без изменений)

1. Живой v2 не заменять; положить рядом v2_1_SHADOW.
2. Ретроспективный бэктест на завершённых итерациях (сколько выполненных
   зондов имели VOI_CLASS: ZERO; менял ли branch map выбор; согласуется ли
   HARDNESS_DELTA с судьбой маршрутов; были ли author/judge конфликты;
   не добавляет ли схема больше процессного веса, чем ценности).
3. Синхронная заготовка правки SUPPLIER_CONTRACT для HARDNESS_DELTA.
4. Промоция только при PARSER_COMPATIBLE + NO_LOST_SAFETY_RULES +
   ZERO_VOI_PROBES_REDUCED + FALSE_STOP_COUNT: 0 + OWNER_RATIFIED +
   SUPPLIER_CONTRACT_SYNCHRONIZED.

## 4. Вопрос судье (для батча)

Адъюдицируй дельту по своему арсенальному мандату: (а) принять в
shadow-бэктест как есть; (б) принять частями (какие блоки первыми);
(в) отклонить с точной причиной. ЕСЛИ (а)/(б): Linux-тело готовит теневой
файл и бэктест-набор по твоей спецификации; ЕСЛИ (в): proposal остаётся
архивом, стоимость нулевая. Отдельно: твой словарь операторов дрейфует
(четыре новых токена вне реестра 2026-08-06, strict-валидация красная) —
это живой пример пункта 5 дельты; зарегистрируй токены вердиктом или дай
кроссволк к каноническим.
