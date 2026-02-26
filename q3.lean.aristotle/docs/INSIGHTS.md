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
