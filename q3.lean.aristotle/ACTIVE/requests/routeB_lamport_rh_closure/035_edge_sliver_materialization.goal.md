# ГОЛ 035 — MATERIALIZE EDGE-SLIVER TRANSACTION 034 + BUS REPAIR

От: Mythos (диспетчер). Авторизация: «го» владельца, доставлено кондуктором
2026-07-30. Статус: `CHALLENGER / NOT_RH`. `BUS_010_VOID`.
Scope: материализация облачной транзакции 034 (edge sliver), ремонт нумерации
и канала; никакой новой математики в этом голе.

Целевой путь этого файла:
`/Users/emalam/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/035_edge_sliver_materialization.goal.md`

## Почему этот гол

Контракт Прошки «034 edge sliver» исполнен облачной ячейкой 2026-07-29
(без чекаута репо). Шесть артефактов лежат в
`_INBOX_cowork_034edge_2026-07-29/` (коммит `288c190`), помечены DRAFT и в
шину как гол не введены. Одновременно на шине висит самодельный
`034_tooth_sign.goal.md` (коммит `ce2654a`, судьёй не утверждён) — коллизия
номера 034. Этот гол: (i) вводит транзакцию 034 в канон с полной
хэш-цепочкой, (ii) снимает коллизию перенумерацией зубного гола в 036,
(iii) прогоняет эмитированные планты по реальному бэкенду 033,
(iv) чинит канал по ветке. Redигирование судьёй (Прошкой) идёт следующим
шагом после зелёного 035 — бриф подготовит Mythos.

## Дистанционная предпроверка (уже выполнена Mythos, повторить на диске)

Сверка SHA-256 INBOX-копий против леджера ответа 034 — все совпали побайтово:

```text
00ad87dac777367e5954ac105c1434aa72f70f59d68185c8b8c5d85cef4e596b  034_REGISTRATION.md
8fba7657164fd16411e6356f018cf661e2cc843b7f01777353a3ddacd5f3f79b  check_034_edge_sliver_reduction.py
49a965798b1be4a802ddc144ae51bd2e9c287c9c323b68dea7ec2221ba277969  CHECK_034_RUN.log
5b9a7fba98626aca3ab6d0bf1443bcd15b829bab2426c1f08a04ffac6ff1ac7d  ARISTOTLE_TASK_EdgeSliverMomentReduction.md
90af30037ec0340bca1ea7d530a37aca3f48342d856d02bd5717cc6d3c627c95  ARISTOTLE_TASK_EStarMuntzContinuation_v3_PoleSubtracted.md
e4079081c02d977ec1f0ea4aca4f50cf583ead0e8035e7c628516e2c70305145  034_cofinal_scaled_edge_sliver_moment.answer.md   # фиксируется впервые
4d02e6c773cbe924c976d69f36b9673e3ae0654f14fbbda2a558176b1302c25d  _STATUS.md (обложка INBOX)
```

Расхождение любого хэша на диске → стоп-код `HASH_MISMATCH_034_ARTIFACT`,
гол останавливается на этом пункте, остальные задачи не выполняются.

## Задача A — перенумерация зубного гола (выполнить ПЕРВОЙ)

1. `git mv docs/routeB_bus/034_tooth_sign.goal.md docs/routeB_bus/036_tooth_sign.goal.md`.
2. Создать канонную копию
   `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/036_tooth_sign.goal.md`
   (гол родился в зеркале — это нарушение направления потока, канон живёт в
   шине; выровнять).
3. В начало обеих копий вставить дословно следующий блок, исходный текст ниже
   не менять:

```text
> ПЕРЕНУМЕРОВАН 034 → 036 (гол 035): номер 034 занят транзакцией Прошки
> «edge sliver» (COFINAL_EDGE_SLIVER_REDUCTION_PROVED). Рефрейм: этот гол —
> фоновая РЕПЕТИЦИЯ двигателя Поставщика A на конечном скелете: та же машина
> 031 (divided difference + конечный Green ledger + dual-множитель Y), но в
> точках-зубьях вместо a.e. Приоритет ниже 035 и ниже контракта Supplier A.
> Судьёй по-прежнему не утверждён; при расхождении приоритет за судьёй.
> Зубья не входят в лебеговский бюджет (034: TOOTH_LEDGER_IRRELEVANT_TO_
> LEBESGUE_CONSUMER, plant P6).
```

Пока `036` не утверждён Прошкой — не исполнять, только перенумеровать.

## Задача B — ввод шести артефактов 034 в канон

После задачи A (стем 034 свободен):

1. `git mv` каждого из шести файлов из
   `_INBOX_cowork_034edge_2026-07-29/` в корень шины
   `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/`,
   имена без изменений, кроме:
   `034_REGISTRATION.md` → `034_edge_sliver_REGISTRATION.md`.
   Байты не менять; никаких правок внутри проверенных артефактов.
2. `_STATUS.md` переименовать в
   `034_edge_sliver_INBOX_COVER.md` и оставить рядом (история приёмки).
3. Каталог `_INBOX_cowork_034edge_2026-07-29/` после переноса удалить.
4. Пересчитать SHA-256 всех перенесённых файлов, сверить с таблицей выше,
   таблицу с результатом сверки включить в ответ.

## Задача C — материализация входных вердиктов Прошки (EXTERNAL_VERDICT_MATERIALIZATION)

Ячейка 034 потребляла два документа, которых в репо нет:

```text
aad7e9de123c42d989a53ed6b10d4bd2f66fc6915e46e0e1d4c46a72087dfcf2  PROSHKA_033_AND_MUNTZ_POLE_SUBTRACTED_v2.md
f18c9a6d3b712fa7cea07bd19b31858fc99d82ae61143cdecd34fc8c51d0362?  proshka_answer.md (контракт 034 edge sliver)
```

ВНИМАНИЕ: второй хэш взять дословно из YAML-шапки
`034_cofinal_scaled_edge_sliver_moment.answer.md` (строка INPUT_HASHES) —
он там канонический; строка выше набрана диспетчером по памяти и НЕ является
эталоном.

1. Файлы поставляет кондуктор (у него вкладки/загрузки ячейки). Положить в
   `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/proshka/` под
   именами `PROSHKA_033_AND_MUNTZ_POLE_SUBTRACTED_v2.md` и
   `PROSHKA_034_EDGE_SLIVER_CONTRACT.md`.
2. Сверить SHA-256 с записанными в YAML-шапке ответа 034. Совпало →
   `INPUT_VERDICTS_MATERIALIZED`. Файл не доставлен или хэш разошёлся →
   стоп-код `MISSING_INPUT_VERDICT` (с именем файла); задачи D–H при этом
   ПРОДОЛЖАЮТСЯ (fail-closed по пункту, не по голу), а стоп-код обязан
   попасть в primary-строку ответа и в STATE.

## Задача D — реплей чекера

`python3 check_034_edge_sliver_reduction.py` из корня шины. Ожидание:
26/26 PASS, планты стреляют. Лог → `CHECK_035_REPLAY.log`. Любой FAIL →
стоп-код `CHECKER_REPLAY_FAILED`, гол останавливается.

## Задача E — эмитированные планты по реальному бэкенду 033 (в песочнице)

Все мутации — на КОПИЯХ; оригиналы сертификатов и скриптов не трогать.

- **P1 radius mutation** (решающий): в копии бэкенда 033 изменить outward
  cutoff radius ×1/2 и ×2, пересчитать сертификатную отсечку `r_cert`.
  Прогноз P035-2 (зарегистрирован): отсечка сдвинется ⇒
  `P1_RADIUS_DRIVEN_CONFIRMED` (флаг `CERTIFICATE_CUTOFF_RADIUS_DRIVEN`
  разрешён; скорит Прошкин P034-1 как CONFIRMED). Не сдвинется ⇒
  `P1_RADIUS_INTRINSIC_SUSPECT` — это находка для Поставщика A, не провал.
  Таблица (radius, r_cert, max ε_r) → `P1_RADIUS_MUTATION.csv`.
- **P5 crossing-band deletion**: из копии сертификата удалить полосу `r=192`
  (кроссинговая полоса по 034 §4) → coverage-чекер обязан выстрелить.
- **P7 backend δ₀-lock**: подтвердить точное `δ₀ = 0` в бэкенде; в
  песочнице флип `Ψ → −Ψ` → положительная часть обязана мигрировать из
  сливера, судья стреляет.

Незажигание любого планта → стоп-код `PLANT_INERT_<P#>`.

## Задача F — scope-чек 027

Прочитать `027_hlambda_outer_lobe_gate.answer.md` (+ сертификат) и
классифицировать квантор outer-lobe gate `E⋆ ≤ 0 на u ∈ [1, λ]`:

- только `m = 257` → `OUTER_LOBE_SCOPE_FINITE_CELL` (прогноз P035-3);
- параметрически по семейству → `OUTER_LOBE_SCOPE_COFINAL` + дословная
  цитата квантора в ответ.

Это условие потребления леммы 034-D (сжатие домена Поставщика A до
`[4/3, √m]`); без него 034-D остаётся условной.

## Задача G — канал: ветка

1. Дефолтная ветка репо уже переключена на `rh_clean` (проверено дистанционно:
   `git ls-remote --symref origin HEAD` → `refs/heads/rh_clean`). Подтвердить
   локально, строку вывода — в ответ.
2. В `docs/routeB_bus/CHANNEL_RULE.md` дописать правило: «каждый бриф
   внешнему агенту называет ветку явно: branch `rh_clean`; ссылки полные:
   https://github.com/Malaeu/chen_q3/tree/rh_clean/docs/routeB_bus».
3. Отдельным крошечным коммитом на `main` (checkout `main` → добавить один
   файл → push → вернуться на `rh_clean`; НИКАКИХ merge/rebase/force между
   ветками) положить в корень `ACTIVE_BRANCH.md`:

```text
# Эта ветка заморожена (архив 2026-01)
Активная работа: ветка `rh_clean`.
https://github.com/Malaeu/chen_q3/tree/rh_clean
Шина Route B: docs/routeB_bus/ (MANIFEST.md там же).
```

Личные архивы владельца в `docs/` не трогать.

## Задача H — STATE, MANIFEST, зеркало, ответ

1. Одна строка истории в
   `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_STATE.md`
   по образцу существующих, шаблон (заполнить плейсхолдеры):

```text
- 2026-07-30 HH:MM CEST: Bus 035 EdgeSliverMaterialization -> EDGE_SLIVER_034_MATERIALIZED; six 034 cell artifacts adopted from _INBOX (answer sha e4079081..., five ledger hashes byte-match on disk), checker replay 26/26, plants P1/P5/P7-backend -> <P1_RADIUS_DRIVEN_CONFIRMED|P1_RADIUS_INTRINSIC_SUSPECT>, P5 fired, P7 fired; tooth goal renumbered 034->036 (Supplier A rehearsal, background, judge pending); 027 outer-lobe scope = <FINITE_CELL|COFINAL>; Proshka inputs <INPUT_VERDICTS_MATERIALIZED|MISSING_INPUT_VERDICT:...>; default branch rh_clean + explicit-branch brief rule + ACTIVE_BRANCH pointer on main; smallest gaps remain ScaledOuterSignBarrierFourThirds then RelativeBoundaryCellProductBound; NOT_RH; no Bus 010.
```

2. Обновить `docs/routeB_bus/MANIFEST.md`: перенумерация 036, новые файлы 034
   и 035, `proshka/`-входы — каждому SHA-256.
3. Зеркало по правилу 014: закрыл гол → обновил зеркало → commit → push в
   `rh_clean`.
4. Ответ: `035_edge_sliver_materialization.answer.md` с handoff и полным
   ACTIONS LOG (иначе REJECTED), primary-вердикт первой строкой.

## Замки

```text
- статус Route B не повышать; RH из результата не выводить
- Aristotle R4 / Müntz-колею не трогать (отдельный контракт)
- байты проверенных артефактов не менять; переносы только git mv
- никаких force-push; никаких merge между main и rh_clean
- глоссарий STATE заморожен: новые термины не вводить (коды вердиктов —
  шинные коды гола, не термины глоссария)
- новые проверки — stdlib-only, как в 033
```

## Ожидаемый выход

Единственный первичный вердикт: `EDGE_SLIVER_034_MATERIALIZED`
(+ вторичные: `P1_RADIUS_DRIVEN_CONFIRMED` или `P1_RADIUS_INTRINSIC_SUSPECT`;
`OUTER_LOBE_SCOPE_FINITE_CELL` или `OUTER_LOBE_SCOPE_COFINAL`;
`INPUT_VERDICTS_MATERIALIZED` или `MISSING_INPUT_VERDICT`).
Стоп-коды: `HASH_MISMATCH_034_ARTIFACT`, `CHECKER_REPLAY_FAILED`,
`PLANT_INERT_<P#>`.

Зарегистрированные прогнозы диспетчера (скорить в ответе): P035-1 — хэши
сойдутся на диске; P035-2 — отсечка радиус-зависима; P035-3 — scope 027
finite-cell.
