# Q3 Proof Geometry Engine — V0 backtest layer

```yaml
target: Q3_PROOF_GEOMETRY_V0_BACKTEST
mode: read-only over project state (writes only inside proof_geometry/)
authority: ADVISORY_ONLY — не proof-source, не route-selection
route_touch: none (no Lean edits, no route promotion, no RH claim)
directive_source: owner message 2026-08-09 (Proshka-format adjudication,
  PROGRESS_CLASS: REPRESENTATION_PROGRESS, ROUTE_SCORE: 5)
```

## Что это

V0 «heat navigator»: weighted Dirichlet potential на **directed AND-factor
graph** исторического коридора, с бэктестом против записанной хронологии.
Simple graph запрещён как production model (C04-риск: забытый AND — уже
другой объект); каждый логический шаг — factor-вершина, соединяющая ВСЕ свои
входы и один выход.

## Коридор

`GOAL056_S2_WALL__GOAL057_B3_0_LADDER`:

- 25 узлов-детей B3.0A…B3.0Q — механически из closeout-файлов
  (`docs/routeB_bus/GOAL057_B3_0*_CLOSEOUT_*.md`), продакшн-Lean-файлы из их
  секций `## Production object`;
- AND-входы — из `import`-строк этих Lean-файлов (импорты не врут);
- хронология — из git-коммитов `Prove/Close Goal 057 B3.0X`;
- ≥3 убитых веток — 10 kill-строк `VERDICT_GOAL056_*` из knowledge.db
  (среди них source-object/class mismatch);
- plant — синтетический короткий путь `CORPUS → PLANT → TARGET` через
  wrong-object conditional edge, помечен `synthetic_plant`.

## Протокол честности

1. Веса и все правила ранжирования заморожены в `flow.PRECOMMIT` **до**
   первого запуска `backtest.py`; коммит кода+данных предшествует коммиту
   результатов — порядок проверяется по git-истории.
2. Один прогон. Тюнинг весов после просмотра held-out чекпоинтов запрещён
   директивой; результат публикуется как вышел, включая failure-коды.
3. Held-out истина (какой узел исторически был следующим) лежит в
   `corridor_057.json:checkpoints` и читается только evaluator'ом.
4. Известное ограничение теста, заявленное заранее: граф реконструирован
   ретроспективно (импорты будущих файлов на момент чекпоинта людям известны
   не были). Тест сравнивает **механизмы ранжирования** на фиксированном
   графе — flow против baseline'ов в равных условиях; он не проверяет
   генерацию узлов. Диффузия узлов не порождает — это зафиксировано в
   адъюдикации `docs/insights/proof_space_diffusion_potential_2026_08_09.md`.

## Файлы

- `extract_corridor.py` → `corridor_057.json` (граф + чекпоинты + provenance)
- `flow.py` — потенциал (star expansion, Гаусс–Зейдель), conductances
  `c_e = maturity(verifier)·exp(−α(cost−1)−β·|risk|−γ·unverified)`,
  score = `c_e·(u(out)−mean u(inputs))/cost`; baselines: shortest path,
  PageRank, topo depth, random (seed 57)
- `backtest.py` → `results_057.json` + отчёт; критерии успеха и failure-коды
  из директивы

## Критерий успеха (из директивы, дословно)

- исторически правильный следующий узел в top-3 на ≥70% чекпоинтов;
- flow строго бьёт все четыре baseline'а по top-3 rate;
- plant отвергнут (никогда не в top-3 и всегда ниже правильного узла).

Иначе — `Q3_PROOF_GEOMETRY_NO_PREDICTIVE_GAIN` /
`Q3_PROOF_GEOMETRY_AND_STRUCTURE_LOST` /
`Q3_PROOF_GEOMETRY_FAKE_SHORTCUT_ACCEPTED`.
