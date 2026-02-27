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
