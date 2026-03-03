# Project Insights

Этот файл теперь используется как hub-навигация. Полный исторический лог сохранён отдельно, без потерь.

## Quick Links

- Полный legacy-лог: `docs/insights/INSIGHTS_legacy_2026_02_26.md`
- Полный список insight-файлов (автоиндекс): `docs/insights/INDEX.md`
- Карта секций (legacy line -> domain): `docs/insights/HUB_SECTION_MAP_2026_02_26.md`
- Карта alias-дублей (`* 2.md` -> canonical): `docs/insights/ALIAS_MAP_2026_02_26.md`
- Статус/навигация: `docs/insights/HUB_STATUS_2026_02_26.md`
- PrimeCert/Path B/margin: `docs/insights/HUB_PRIMECERT_PATHB_2026_02_26.md`
- Weil/tau0/compact bridges: `docs/insights/HUB_WEIL_TAU0_2026_02_26.md`
- A3/FLOOR/Rayleigh/density: `docs/insights/HUB_A3_FLOOR_DENSITY_2026_02_26.md`
- Ops/checkers/perf: `docs/insights/HUB_OPS_CHECKERS_2026_02_26.md`
- Decisions/risks/roadmap: `docs/insights/HUB_DECISIONS_ROADMAP_2026_02_26.md`

## Refactor Policy (2026-02-26)

- Новые записи добавлять в соответствующий spoke-файл.
- Если запись пересекает несколько доменов: класть в домен primary-owner и ставить cross-link.
- Для обратной трассировки использовать `HUB_SECTION_MAP_2026_02_26.md` и `legacy_line` маркеры.
- Legacy-файл считать read-only архивом, не использовать как рабочий лог.

## Current Note

- Текущий тяжёлый checker-процесс можно ждать в фоне; docs-рефактор не блокирует сборку.

## Synthesis (2026-02-27, in progress) — Path B tau0 gate switched to provider-route

- Переключён `Q3.prime_term_pathB_tcritical_tau0_brange_thm` на quarter-route
  в `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` (без `Brange_2046` в каноническом доказательстве).
- `#print axioms Q3.Main.RH_of_Weil_and_Q3` теперь не тянет grid/bucket data-узлы и не тянет
  `Lean.trustCompiler` из PrimeCert data-цепочки.
- Текущий остаток project-аксиом в mainline:
  `Q3.prime_term_tcritical_le_cstar_quarter_mathan`,
  `Q3.cstar_quarter_le_arch_term_tcritical_mathan`
  (+ `Q3.Weil_criterion_tau0` как доменный top-level).
- По локальному семантическому поиску (`research_oracle`) лучшие попадания идут в заметку
  `qmd://q3_docs/insights/prime-cert-tcritical-2026-01-26.md`; это подтверждает, что следующий
  инженерный фокус — доказательный replacement B_min/arch и quarter bound, не возврат в checker-ветку.
- Next plan (5 шагов):
  1. Закрыть theorem-route для `prime_term_tcritical_le_cstar_quarter_mathan` в
     `Q3/Proofs/PrimeTerm_PathB_legacy_provider.lean` через отдельный модуль `PrimeTerm_PathB_quarter_theorem.lean`.
  2. Закрыть theorem-route для `cstar_quarter_le_arch_term_tcritical_mathan`
     в том же модуле, с отдельной леммой под arch-quarter.
  3. Держать `PrimeTerm_PathB_tau0_brange_analytic.lean` как thin-specialization
     через `prime_term_pathB_tcritical_from_legacy`, без возврата к Brange cert route.
  4. После каждого шага: `lake build <touched module>` и `lake env lean Q3/CheckTau0BrangeGate.lean`.
  5. Финально: `lake env lean Q3/CheckAxioms.lean` и фиксация сокращённого axioms-list.

## Synthesis (2026-02-27, in progress) — Path B tau0 quarter refactor (no cert fallback in canonical route)

- Baseline подтверждён `check_axioms`: в mainline остаются ровно два bridge-узла
  `Q3.prime_term_tcritical_le_cstar_quarter_mathan` и
  `Q3.cstar_quarter_le_arch_term_tcritical_mathan` (плюс `Q3.Weil_criterion_tau0`).
- В `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` добавлен явный split:
  `PrimeTermTau0BrangePrimeQuarter` + `PrimeTermTau0BrangeArchQuarter` и
  композиция `prime_term_pathB_tcritical_tau0_brange_of_quarter_slack`.
- Канонический `prime_term_pathB_tcritical_tau0_brange_thm` переведён на quarter-composition,
  без обращения к global provider (`prime_term_pathB_tcritical_from_legacy`) в самом финальном шаге.
- Критически: route `...of_prime_quarter` через
  `prime_term_tau0_brange_arch_floor_from_heat` оставлен как off-mainline helper.
  Он тянет `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data`, поэтому не подходит
  как canonical путь, если цель — не возвращать cert/data axioms в mainline.
- Проверка после рефактора:
  - `lake build Q3.Proofs.PrimeTerm_PathB_tau0_brange_analytic` — OK
  - `lake env lean Q3/CheckTau0BrangeGate.lean` — OK
  - `lake env lean Q3/CheckAxioms.lean` — mainline axioms unchanged (ровно 2 bridge-узла Path B).

Next step (targeted):
1. Закрыть theorem-route для `prime_term_tcritical_le_cstar_quarter_mathan`.
2. Закрыть theorem-route для `cstar_quarter_le_arch_term_tcritical_mathan`.
3. Держать canonical tau0 route только на quarter-composition, не включая heat/data fallback.

## Synthesis (2026-02-27, implemented) — checker-free grid data route + guarded mainline

- Вынесен bucket API из checker-модуля в отдельный checker-free слой:
  `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_BucketScaffold.lean`.
- `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean` переключён с
  `..._Checker` на `..._BucketScaffold` и теперь использует
  `prime_b_grid_weight_tail_bound_by_majorant` (через `GaussianTailKernel`) для tail-части.
- `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Checker.lean` оставлен как
  compatibility hub (опциональный checker-entrypoint), без load-bearing API.
- В `scripts/check_axioms.sh` добавлен guard (Step 0.9), который валит проверку, если
  активные mainline data-модули снова начнут импортировать `*Checker`.
- Проверка после правок:
  - `lake build Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_BucketScaffold` — OK
  - `lake build Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_Data` — OK
  - `lake build Q3.Main` — OK
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` — OK
- Зафиксированный axiom-snapshot mainline (`Q3.Main.RH_of_Weil_and_Q3`):
  `propext`, `Classical.choice`, `Q3.Weil_criterion_tau0`,
  `Q3.cstar_quarter_le_arch_term_tcritical_mathan`,
  `Q3.prime_term_tcritical_le_cstar_quarter_mathan`, `Quot.sound`.

## Synthesis (2026-02-27, implemented) — margin-route RH entrypoint (bridge-free profile)

- В `Q3/Main.lean` добавлена параллельная theorem-цепочка на явном margin-контракте:
  - `Q_nonneg_on_W_K_tau0_of_margin`
  - `Q_nonneg_on_Weil_cone_tau0_of_margin`
  - `RH_of_Weil_and_Q3_of_margin`
- Ключевая цель: иметь production-ready entrypoint без зависимости от legacy quarter-узлов
  `Q3.cstar_quarter_le_arch_term_tcritical_mathan` и
  `Q3.prime_term_tcritical_le_cstar_quarter_mathan`.
- Старый `RH_of_Weil_and_Q3` сохранён без изменений (обратная совместимость).
- В `scripts/check_axioms.sh` добавлен Step 2.1:
  автоматическая проверка, что `RH_of_Weil_and_Q3_of_margin` действительно
  bridge-free по quarter-аксиомам.
- Проверка:
  - `lake build Q3.Main` — OK
  - `#print axioms Q3.Main.RH_of_Weil_and_Q3_of_margin`:
    `propext`, `Classical.choice`, `Q3.Weil_criterion_tau0`, `Quot.sound`.

## Synthesis (2026-02-27, implemented) — dual RH profiles in Main (quarter-route + data-route)

- В `Q3/Main.lean` добавлены:
  - `prime_cert_margin_on_Brange_from_PrimeCert : PrimeCertMarginOnBrange`
  - `RH_of_Weil_and_Q3_via_margin_cert : RH`
- Это даёт явный data-route профиль без quarter bridge-узлов:
  `RH_of_Weil_and_Q3_via_margin_cert` не зависит от
  `Q3.cstar_quarter_le_arch_term_tcritical_mathan` и
  `Q3.prime_term_tcritical_le_cstar_quarter_mathan`.
- Axiom-snapshot для `RH_of_Weil_and_Q3_via_margin_cert`:
  - Standard: `propext`, `Classical.choice`, `Quot.sound`
  - Tier-1: `Q3.Weil_criterion_tau0`
  - Data-route: `prime_b_grid_arch_bounds_data`,
    `prime_b_grid_bucket_bounds`,
    `prime_heat_bounds_arch_data`,
    `prime_heat_bucket_bounds_data`,
    плюс `Lean.ofReduceBool`, `Lean.trustCompiler`.
- В `scripts/check_axioms.sh` добавлен Step 2.2:
  smoke-check, что `RH_of_Weil_and_Q3_via_margin_cert` quarter-bridge free.

## Synthesis (2026-02-27, in progress) — узел `prime_b_grid_arch_bounds_data` (BrangeCert_2046)

- Target blocker: закрыть `Q3.Proofs.PrimeCert.prime_b_grid_arch_bounds_data` (сейчас аксиома) в
  `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`, не ломая margin-route.
- Фактический axiom-след (`#print axioms`): узел тянется в
  `prime_b_grid_bounds_cert -> prime_b_grid_val_le_margin -> prime_cert_margin_on_Brange_axiom`
  и в `prime_cert_margin_on_Brange_kernel_shadow`.
- Semantic search (4 запроса через `./scripts/research_oracle.py query ... -c q3_docs`):
  релевантно только `qmd://q3_docs/insights/prime-cert-brange-tcritical-2026-01-26.md`;
  остальное низкой точности (индекс устарел, часть запросов падала по VRAM у qmd-rerank).
- External web-check (built-in web): общие источники по heat/Lipschitz/interval ideas;
  прямого Lean-ready per-grid arch-certificate маршрута не найдено.
- Ключевой вывод: в текущем коде нет существующей theorem-леммы, которая даёт
  per-grid неравенства уровня `prime_b_grid_arch_term i ≤ arch_term(...)` для всех 20 точек.
  Лемма `arch_term_Lipschitz_heat` даёт только глобальный transport от `B_min` и численно слишком слаба
  для таблицы `prime_b_grid_arch_term_q_get`.
- Рабочий theorem-fallback (без этого узла): доказывать `prime_b_grid_val_le_margin` напрямую из
  (i) `arch_term_cert_on_Bmin_tau0` + `arch_term_Lipschitz_heat` (heat transport),
  (ii) `prime_term_tau0_brange_prime_quarter_from_legacy` (prime quarter bound),
  (iii) табличного `prime_b_grid_val` max-bound (`fin_cases`).
- Next implementation plan:
  1) добавить в `BrangeCert_2046` глобальный lower-bound для `arch_term (prime_b_grid i)`;
  2) добавить global upper-bound для `prime_term (prime_b_grid i)` через quarter-route;
  3) заменить `prime_b_grid_val_le_margin` на прямое доказательство от этих двух bound-лемм;
  4) удалить `prime_b_grid_arch_bounds_data`, `PrimeBGridBounds`, `prime_b_grid_bounds_cert`;
  5) прогнать `lake env lean Q3/Proofs/PrimeCert/BrangeCert_2046.lean` и `#print axioms` для двух route-теорем.

## Synthesis (2026-02-27, implemented) — isolate data-profile from canonical Main

- `Q3/Main.lean` очищен от data-profile glue:
  удалён импорт `Q3.Proofs.PrimeCert.Brange_2046` и локальные theorem-обвязки
  `prime_cert_margin_on_Brange_from_PrimeCert` / `RH_of_Weil_and_Q3_via_margin_cert`.
- Добавлен отдельный модуль `Q3/Main_DataProfile.lean`, который держит data-driven профиль
  отдельно от канонической mainline-цепочки.
- `scripts/check_axioms.sh` переключён:
  Step 2.2 теперь импортирует `Q3.Main_DataProfile`,
  Step 1.5 пересобирает `.olean` для `Q3/Main_DataProfile.lean`.
- Проверка:
  - `lake build Q3.Main` — OK
  - `lake env lean Q3/Main_DataProfile.lean` — OK
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` — PASS.
- Текущий status:
  - canonical `Q3.Main.RH_of_Weil_and_Q3` и `..._of_margin` не тянут data-route;
  - data-profile по-прежнему зависит от 4 load-bearing data-аксиом
    (`prime_b_grid_arch_bounds_data`, `prime_b_grid_bucket_bounds`,
    `prime_heat_bounds_arch_data`, `prime_heat_bucket_bounds_data`)
    и от `Lean.ofReduceBool`/`Lean.trustCompiler` в bucket-sum equalities.

## Synthesis (2026-02-27, research) — local semantic search reliability note

- Для блокеров heat/grid были запущены embedding-запросы:
  `./scripts/research_oracle.py query "..."`
  (контейнер `q3_docs`).
- Один запрос вернул релевантный контекст по `insights/prime-cert-brange-tcritical-2026-01-26.md`.
- Два запроса аварийно упали внутри `qmd`/`bun` (NAPI finalizer assertion),
  поэтому полагались на локальный code-scan + explorer-агенты как primary source.

### Update (2026-02-27, in progress) — load-bearing PrimeCert data axioms (4-node frontier)

- Зафиксирован активный фронтир data-route: `prime_heat_bucket_bounds_data`, `prime_heat_bounds_arch_data`, `prime_b_grid_bucket_bounds`, `prime_b_grid_arch_bounds_data`.
- Semantic search (`scripts/research_oracle.py`, 3 запроса по `q3_docs`) дал низкий релевантный сигнал для точных bridge-лемм этого узла; полезных готовых theorem-route не найдено.
- Внешний Lean reference-check подтвердил trust-модель: `native_decide` транзитивно добавляет `Lean.ofReduceBool`/`Lean.trustCompiler` в `#print axioms`.
- Практический вывод: для kernel-safe профиля нужно убирать именно `native_decide`-узлы в bucket sum equalities (`..._ub_sum_q_eq`) и checker-dependent bridges.
- Проверка на case-bridge (`Full.prime_heat_bucket_pp_sum_ub_q ⟨0⟩` -> `Full.prime_heat_pp_term_ub_q_sum_bucket_0`) показала heartbeat timeout на `simpa/isDefEq`; прямой definal reduction не проходит.
- Следующий шаг: строить отдельный bridge-модуль с явными промежуточными леммами (без массивного `simpa`), затем подключить в `BrangeHeat..._SumData`/`BrangeGrid..._Data`.
- Политика цикла остаётся прежней: canonical `Q3.Main` не трогаем; закрываем data-profile изолированно через `Q3.Main_DataProfile`.

### Update (2026-02-27, Aristotle attempt for heat bucket bridge)

- Подготовлен узкий target для леммы `prime_heat_bucket_pp_sum_ub_q_le_kernel`:
  - `ACTIVE/aristotle/queue/manual_prime_heat_bucket_pp_sum_ub_q_le_kernel/TARGET.lean`
  - `ACTIVE/aristotle/queue/manual_prime_heat_bucket_pp_sum_ub_q_le_kernel/PROMPT.txt`
- CLI submit с `--no-validate-lean-project` упал на ограничении Aristotle API (`validate_lean_project must be True when auto_add_imports=True`).
- Повторная отправка через Python API с `auto_add_imports=False` прошла успешно.
- Aristotle Project ID: `4cdbddf1-ba97-40a8-add1-61c61e07c57e`.
- Следующий шаг: скачать output этого project id, прогнать hole-scan (`rg -n "sorry|exact\\?|admit"`), интегрировать только hole-free фрагменты.

## Synthesis (2026-03-02, implemented) — heat checker bottleneck inventory + checker-free wiring

- Инвентаризация фактов (без догадок):
  - `prime_heat_bounds_arch_data` остаётся аксиомой в
    `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.
  - `BrangeHeatCert_2026_01_28_Checker.lean` тянет тяжёлую цепочку
    `PrimePowFull + PrimePowBucket0Auto + PrimePowAutoGT10000`.
  - В `/tmp` подтверждены прошлые артефакты/логи по checker и axiom-check
    (`check_axioms_*`, `primepow_agg_build_20260217.log`, `lake_build_sumdata.log`, `q3_checks_20260227.log`).
  - Аналитический heat-tail уже закрыт в
    `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Tail.lean`
    и экспортируется через `GaussianTailKernel`.
- Реализован первый шаг decouple:
  - `BrangeHeatCert_2026_01_28_SumData.lean` больше не импортирует `..._Checker`.
  - В `SumData` введён data-level узел `axiom prime_heat_bucket_bounds`
    (по аналогии с `prime_b_grid_bucket_bounds` в grid data-route), и
    `prime_heat_bucket_bounds_data` теперь строится от него.
  - `BrangeHeatCert_2026_01_28_Partial.lean` больше не импортирует `..._Checker` и
    получает `h_sum` через `prime_heat_sum_data_sum_ub` + `prime_cert_heat_prime_sum_up_to_ub_le_partial`.
  - В `scripts/check_axioms.sh` усилен Step 0.9:
    checker-import guard теперь проверяет и `BrangeHeatCert_2026_01_28_Partial.lean`.
- Итог текущего шага:
  - active heat `Partial/SumData` переведены на checker-free wiring;
  - frontier аксиом теперь явно отделён:
    `prime_heat_bucket_bounds` (data-level) и `prime_heat_bounds_arch_data` (arch integral).
- Next:
  1) закрыть `prime_heat_bounds_arch_data` theorem-route (analytic core/tail),
  2) заменить `prime_heat_bucket_bounds` на theorem-route (global cap вместо pointwise checker graph).

## Synthesis (2026-03-02, in progress) — prime-heat compute bottleneck quantified (fact-only)

- Цель шага: зафиксировать, что именно тормозит в heat-ветке, на измерениях, без предположений.

### Факты по объёму кода (PrimeCert heat)

- `BrangeHeatCert_2026_01_28_PrimePowAutoGT10000*.lean`:
  - файлов: `1095`
  - суммарно строк: `4,571,502`
- `BrangeHeatCert_2026_01_28_PrimePowFullBucket*.lean`:
  - файлов: `500`
  - суммарно строк: `86,934`

### Факты по времени проверки (`lake env lean`, с активной `.venv`)

- `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`:
  - `ELAPSED=0:07.19`, `MAXRSS=5424236KB`
- `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Partial.lean`:
  - `ELAPSED=0:06.88`, `MAXRSS=5411620KB`
- `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`:
  - после `34+` минут не завершился (прерван вручную для сохранения сессии);
  - `ps` во время прогона подтверждал активный `lean`-процесс (`~10% CPU`, `~21.8% MEM`).

### Текущий вывод (рабочий)

- Узкое место времени — не `SumData/Partial`, а именно checker-цепочка,
  завязанная на большой граф `PrimePowAutoGT10000*`.
- Это согласуется с целью вынести checker из load-bearing пути и заменять
  его sum-level theorem/data узлами.

### План фиксов (следующий шаг)

1. Оставить `Checker.lean` только как off-mainline audit-ветку.
2. В active heat-route держать только checker-free модули (`SumData`, `Partial`, `Tail`, `Gaussian*`).
3. Закрыть `prime_heat_bounds_arch_data` theorem-route (analytic core/tail), чтобы убрать второй критический узел.
4. После этого заменить remaining heat sum-data axiom на theorem/data bridge без импорта checker.

## Synthesis (2026-03-02, implemented) — arch-data source resolved + theorem-wrapper normalization

- Проверен точный источник одноимённого узла через `#print`:
  - в текущем дереве есть один load-bearing источник
    `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` в
    `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.
  - Дубликатов с тем же именем в `PrimeCert` не найдено (`rg` по `*.lean`).
- Добавлен checker-free модуль аналитических заготовок:
  - `Q3/Proofs/PrimeCert/ArchHeatMajorant.lean`
  - экспортирует generic леммы типа `pointwise majorant -> integral bound` для heat-arch ядра на `[-Bmax,Bmax]`.
  - `lake env lean Q3/Proofs/PrimeCert/ArchHeatMajorant.lean` — OK (без warning).
- Нормализован источник в `BrangeHeatCert_2026_01_28.lean`:
  - прямая data-аксиома переименована в
    `prime_heat_bounds_arch_data_from_data`;
  - публичный узел теперь theorem-обёртка
    `prime_heat_bounds_arch_data := prime_heat_bounds_arch_data_from_data`.
- Совместимость проверена:
  - `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean` — OK;
  - `lake env lean Q3/Proofs/PrimeCert/PrimeHeatMarginWitness_2026_01_28.lean` — OK.

### План fix-итерации (конкретно)

1. В `ArchHeatMajorant.lean` добавить специализированную лемму
   `prime_heat_bounds_arch_data_of_linear_growth` (инстанс от `a_star_linear_growth`
   + явная оценка интеграла majorant на `[-Bmax,Bmax]`).
2. Вынести численный/символьный bound для majorant-integral в отдельный локальный theorem
   (временный data-level, но уже не на исходный arch-integral).
3. Подменить
   `prime_heat_bounds_arch_data_from_data` на этот theorem-route,
   сохранив внешний API `prime_heat_bounds_arch_data` без изменений.
4. После закрытия arch-route перейти к замене `prime_heat_bucket_bounds`
   (sum-level route без checker-import).

### Update (2026-03-02, implemented) — `#print` cache pitfall resolved

- Обнаружена и подтверждена причина «старой аксиомы» в `#print`:
  - `lake env lean <file>` проверяет файл, но не гарантирует обновление импортируемых `.olean`.
  - Для корректного `#print` по импортам нужен `lake build <Module>`.
- После `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28`:
  - `#print prime_heat_bounds_arch_data` показывает theorem-обёртку,
  - `#print axioms prime_heat_bounds_arch_data` теперь зависит от
    `prime_heat_bounds_arch_data_from_data` (как и задумывалось), а не от одноимённой аксиомы.
- `ArchHeatMajorant.lean` расширен специализированными bridge-леммами:
  - `prime_heat_bounds_arch_of_uniform_abs_bound`
  - `prime_heat_bounds_arch_of_linear_abs_bound`
  (оба checker-free; это прямые точки встраивания для последующей замены data-аксиомы theorem-route).

### Update (2026-03-02, validated) — `a_star` scaling check blocks naive global linear-majorant route

- Проверен источник нормировки в коде:
  - `Q3/Basic/Defs.lean`: `a_star ξ = 2 * π * a ξ`.
- Проверен численный sanity-check для текущего heat узла (`t_critical = 3/20`, `B_max = 4.9`) на той же формуле, что в helper-скрипте:
  - `a(0) ≈ 5.3721834192`
  - `a_star(0) ≈ 33.7544239272`
  - `∫_{-Bmax}^{Bmax} |a_star(ξ)| exp(-4π² t_critical ξ²) |ξ| dξ ≈ 1.36037830996`
  - это согласуется с `prime_cert_L_arch_heat_raw = 1.360378581976`.
- Критический вывод:
  - route `|a_star ξ| ≤ C0 + C1|ξ|` с `C0 = a_star(0)` и глобальной erf-free заменой на `ℝ`
    даёт нижнюю планку `C0/α` (где `α=4π² t_critical ≈ 5.92`), то есть уже `≈ 5.70 > 1.36`;
  - значит такой «глобальный линейный majorant + whole-line integral» несовместим с текущим целевым bound.
- Практически:
  - для theorem-route нужен более острый план (piecewise majorant / core-offcore upper bound,
    с локально малыми интервалами у нуля и отдельным хвостовым контролем),
    либо пересмотр нормировки целевого интеграла (если в манускрипте шаг был в нормировке `a`, не `a_star`).

### Update (2026-03-02, implemented) — heat partial cert precision policy

- По запросу снижена избыточная рабочая точность в helper-скрипте
  `scripts/prime_brange_heat_partial_interval_cert.py`:
  - `DIGITS: 12 -> 15` (целевой вывод до 15 знаков после запятой)
  - `DPS_PRIMARY: 80 -> 40`
  - `DPS_VERIFY: 120 -> 60`
- Мотивация: убрать чрезмерный `mpmath`-overkill, сохранив умеренный guard
  для устойчивости interval arithmetic при целевом формате `15 d.p.`.
- Проверка: `python3 -m py_compile scripts/prime_brange_heat_partial_interval_cert.py` — OK.

## Synthesis (2026-03-02, in progress) — `prime_heat_bounds_arch_data`: что уже проверено и почему узел всё ещё открыт

- Целевой узел: `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`,
  `prime_heat_bounds_arch_data` (сейчас theorem-обёртка над `prime_heat_bounds_arch_data_from_data`).
- Что уже есть в коде (checker-free):
  - `Q3/Proofs/PrimeCert/ArchHeatMajorant.lean`:
    generic bridge-леммы `pointwise majorant -> integral bound`.
  - `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatIntegrable.lean`:
    интегрируемость arch-интегранда.
- Локальный semantic search (research_oracle, `q3_docs`) дал релевантные указатели
  на core/tail маршрут (Lemma 8.15 / extracted-structure), но не готовую Lean-лемму,
  которую можно сразу импортировать и закрыть узел без новой математики.
- Внешний web-search по первоисточникам дал низкий сигнал (шум), поэтому
  практический источник истины остаётся локальный код + manuscript extraction.
- Проверенный блокер (факт):
  - наивный глобальный route (`|a_star ξ| ≤ C0 + C1|ξ|` + whole-line/erf-free bound)
    не совместим с `prime_cert_L_arch_heat_raw = 1.360378581976` при текущей нормировке
    `a_star = 2π a` и `exp(-4π² t_critical ξ²)`.
  - даже усиленный Stieltjes-based upper без piecewise sharpening остаётся выше целевого bound.
- Практический вывод: нужен именно **piecewise core/offcore majorant route** (не глобальный linear-over-R).

### Multi-agent fix plan (конкретные deliverables)

1. `Q3/Proofs/PrimeCert/PrimeHeatArchPiecewiseKernel.lean` (новый):
   theorem-шаблон `core/offcore bounds -> prime_heat_bounds_arch_data`.
2. Agent A (матан, специальные функции):
   дать sharp upper bound для `|a_star|` на core-интервале (в явной форме для интегрирования).
3. Agent B (интегральные оценки):
   закрыть offcore Gaussian-tail часть и свести к конечной численной константе.
4. Agent C (интеграция):
   заменить `prime_heat_bounds_arch_data_from_data` на theorem-route,
   прогнать `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28`,
   затем `#print axioms Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data`.

### Вопросы к Прошке (чтобы не терять цикл на догадки)

- Нужный минимальный sharp core-majorant для `a_star` (формула + диапазон `|ξ| ≤ r`),
  который уже гарантированно проталкивает integral bound ниже `1.360378581976`.
- Предпочтительный offcore bound для Lean (без `erf` или с `erf`, что проще замкнуть kernel-safe).
- Подтверждение нормировки в целевом узле (`a_star` vs `a`) и коэффициента в экспоненте
  именно для `BrangeHeatCert_2026_01_28`.

## Update (2026-03-02, in progress) — blocker `prime_heat_bucket_pp_sum_ub_q_le_kernel`

- Целевой checker-free узел:
  - `Full.prime_heat_bucket_pp_sum_ub_q k ≤ prime_heat_bucket_ub_q_get k`
  - старый вариант в `BrangeHeatCert_2026_01_28_Checker.lean` закрыт через
    `fin_cases k <;> native_decide`.
- Где данные уже есть:
  - `prime_heat_bucket_ub_q_get` таблица (100 бакетов):
    `BrangeHeatCert_2026_01_28_Intervals.lean`.
  - `Full.prime_heat_pp_term_ub_q_sum_bucket_0 .. _99`:
    `BrangeHeatCert_2026_01_28_PrimePowFull.lean`.
  - готовые сравнения каждого precomputed bucket sum с bucket UB:
    `prime_heat_pp_term_ub_q_sum_bucket_le_0 .. _99` в
    `BrangeHeatCert_2026_01_28_PpSumBounds.lean`.
- Подтверждённый computational bottleneck:
  - наивная попытка развернуть
    `Full.prime_heat_bucket_pp_sum_ub_q` через `simp` даже для `k=0`
    падает в `isDefEq` timeout (heartbeats), то есть узкое место —
    giant definitional unfolding, а не финальная арифметика.
- Добавлены артефакты для Прошки/Aristotle:
  - `aristotle_input/prime_heat_bucket_pp_sum_ub_q_le_kernel_target.lean`
  - `aristotle_input/proshka_prime_heat_bucket_pp_sum_kernel_2026_03_02.md`
  - `aristotle_input/proshka_prime_heat_bucket_pp_sum_kernel_2026_03_03.md`
    (цель, репро таймаута, ограничения, suggested strategy).

## Update (2026-03-02, integrated) — Aristotle project `e20aa050-3f28-4851-8924-4e3d4d872fb8`

- Статус проекта: `COMPLETE`; output скачан в
  `aristotle_output/e20aa050-3f28-4851-8924-4e3d4d872fb8-output.lean`.
- Hole-scan output: пусто (`sorry|exact?|admit` не найдено в коде доказательства).
- Интеграция выполнена в:
  - `ACTIVE/aristotle/queue/manual_prime_heat_bucket_pp_sum_ub_q_le_kernel/TARGET.lean`
  - `aristotle_input/prime_heat_bucket_pp_sum_ub_q_le_kernel_target.lean`
- Текущий proof-route в интегрированном артефакте использует
  `native_decide +revert`; это рабочая интеграция, но **не kernel-safe final**.
  Следующий шаг: добить checker-free theorem-route через `PpSumBounds` bridge
  без `native_decide`.

## Update (2026-03-03, in progress) — Digamma shift route for `prime_heat_bounds_arch_data`

- Усилен файл:
  - `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeHeatDigammaShift.lean`
- Добавлены и компилируются (hole-free):
  - `re_digamma_quarter_shift`
  - `a_eq_a0_sub_shift_series`
  - `a_star_eq_a_star0_sub_shift_series`
  - `a_star_le_a_star_zero`
- Проверка компиляции:
  - `lake env lean Q3/Proofs/PrimeCert/PrimeHeatDigammaShift.lean` — OK.
  - `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean` — OK.
- Это ещё не закрывает `prime_heat_bounds_arch_data`, но снимает ключевой подблок:
  точная shift-серия для `a_star` теперь готова для core/offcore majorant route.
- Артефакт для координации с Прошкой (уже на месте):
  - `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/proshka_prime_heat_bucket_pp_sum_kernel_2026_03_02.md`
  - `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/proshka_prime_heat_arch_kernel_2026_03_03.md`
- `2026-03-03`: arch-запрос к Прошке усилен данными для глубокого анализа:
  - актуальное имя legacy-аксиомы (`prime_heat_bounds_arch_data_from_data_legacy_axiom`);
  - зафиксированные sanity-check числа для целевого интеграла;
  - явные acceptance-критерии (`lake env lean`, `lake build`, `#print axioms`);
  - явные non-goals (не трогать bucket-ветку и константы cert-слоя).
- `2026-03-03`: добавлен единый context-pack для Прошки:
  - `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/proshka_context_pack_2026_03_03.md`
  - оба запроса (`arch` и `bucket`) теперь явно требуют сначала загрузить этот контекст.
- `2026-03-03`: bucket-запрос (`...bucket_pp_sum_kernel_2026_03_02.md` и `..._2026_03_03.md`)
  усилен текущим статусом draft-proof (`native_decide + revert`) и жёсткими acceptance-критериями.
- `2026-03-03`: собран переносимый единый контекст-пакет для Прошки (без зависимости от локального доступа):
  - каталог: `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/proshka_bundle_2026_03_03`
  - архив: `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/proshka_bundle_2026_03_03.tar.gz`
- `2026-03-03`: формат переведён на 2 отдельные self-contained директории (без zip/tar):
  - ARCH:
    `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/proshka_arch_request_2026_03_03`
  - BUCKET:
    `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/aristotle_input/proshka_bucket_request_2026_03_03`
  - каждая директория содержит:
    `REQUEST.md`, `WEEKLY_CONTEXT.md`, `MANIFEST.txt`, `context_files/...` (локальные копии нужных Lean/MD файлов).
  - старый bundle/архив удалён, чтобы не путать канонический workflow.
- Технический hygiene-шаг в cert-файле:
  - в `/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
    переименована аксиома в явный legacy-name:
    `prime_heat_bounds_arch_data_from_data_legacy_axiom`.
  - `#print axioms Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` теперь явно показывает
    именно legacy-узел (без путаницы имён), что упрощает контроль closure.
