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

## Synthesis (2026-02-27, in progress) — Path B tau0 gate switched to quarter-route

- Переключён `Q3.prime_term_pathB_tcritical_tau0_brange_thm` на quarter-route
  в `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` (без `Brange_2046` в каноническом доказательстве).
- `#print axioms Q3.Main.RH_of_Weil_and_Q3` теперь не тянет grid/bucket data-узлы и не тянет
  `Lean.trustCompiler` из PrimeCert data-цепочки.
- Текущий остаток project-аксиом в mainline:
  `Q3.prime_term_tcritical_le_cstar_quarter_mathan`,
  `Q3.Proofs.PrimeCert.arch_term_cert_on_Bmin_tau0`,
  `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` (+ `Q3.Weil_criterion_tau0` как доменный top-level).
- По локальному семантическому поиску (`research_oracle`) лучшие попадания идут в заметку
  `qmd://q3_docs/insights/prime-cert-tcritical-2026-01-26.md`; это подтверждает, что следующий
  инженерный фокус — доказательный replacement B_min/arch и quarter bound, не возврат в checker-ветку.
- Next plan (5 шагов):
  1. Закрыть theorem-route для `prime_term_tcritical_le_cstar_quarter_mathan` в
     `Q3/Proofs/PrimeTerm_PathB_legacy_provider.lean` через отдельный модуль `PrimeTerm_PathB_quarter_theorem.lean`.
  2. Закрыть `arch_term_cert_on_Bmin_tau0` theorem-route в
     `Q3/Proofs/PrimeCert/Bmin_1826.lean` (через существующий A3/floor стек и `BrangeHeatCert_2026_01_28_ArchHelpers.lean`).
  3. Закрыть `prime_heat_bounds_arch_data` theorem-route в
     `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean` через выделенный arch-bound модуль.
  4. После каждого шага: `lake build <touched module>` и `lake env lean Q3/CheckTau0BrangeGate.lean`.
  5. Финально: `lake env lean Q3/CheckAxioms.lean` и фиксация сокращённого axioms-list.
