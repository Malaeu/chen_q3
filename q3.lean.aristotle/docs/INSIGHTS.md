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
