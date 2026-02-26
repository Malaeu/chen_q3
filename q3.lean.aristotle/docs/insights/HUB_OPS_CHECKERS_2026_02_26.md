# Hub: Ops Checkers Performance

Источник: `docs/insights/INSIGHTS_legacy_2026_02_26.md`.
Инженерные заметки: tooling, checker-процессы, build/perf и эксплуатация.

## Included Sections

- line 30: Tooling / Checks
- line 178: Progress (2026-02-19) — PrimePow Auto GT10000 aggregate build
- line 432: Synthesis (2026-01-31, in progress) — Formal interval checker for pilot sums
- line 527: Research note (2026-01-29) — digamma/trigamma asymptotics sanity check
- line 536: Synthesis (2026-01-29, in progress) — BMO Bellman check-mode + regularity gate
- line 1257: Ops note (2026-02-08, done) — isolated heavy runs for Lean/Codex
- line 1282: Synthesis (2026-02-10, in progress) — Step 2 GT10000 blocker: deep disjunction elaboration

<!-- wave2_related_start -->
## Related Legacy Files (Wave 2)

Связанные standalone-файлы по домену `ops`:

- `docs/insights/aristotle_error_recovery.md`
- `docs/insights/aristotle_strategy_pure_informal.md`
- `docs/insights/breakthrough_proshka_full_proof_2026_01_14.md`
- `docs/insights/decision_tree_template.md`
- `docs/insights/documentation_discipline.md`
- `docs/insights/drift_report_m1_m4.md`
- `docs/insights/file_organization_aristotle.md`
- `docs/insights/lean_simpa_performance_fix_2026_01_19.md`
- `docs/insights/mgrep_websearch_discovery_2026_01_18.md`
- `docs/insights/proshka_key_resource.md`
- `docs/insights/research_swarm_symlink_caching_2026_01_17.md`
<!-- wave2_related_end -->

## Content

<!-- legacy_line:30 -->

## Tooling / Checks


- **Lean build hangs на MeasureTheory/HasSum**: `simpa using` убивает перфоманс → `docs/insights/lean_simpa_performance_fix_2026_01_19.md`.
- check_axioms падает на A3_FLOOR: нужен предварительный build → `docs/insights/check_axioms_prebuild_a3_floor_2026_01_16.md`.
- FloorCert grid min: `floor_grid_val_ge_min_lb` closed via `native_decide`;
  required `set_option maxRecDepth` / `maxHeartbeats` in `Q3/Proofs/FloorCert/Grid_2219.lean`.
- Semantic search workflow (Embeddings + web tool):
  1) сначала embedding‑поиск по нашей базе (3-5 запросов, до ~75% уверенности),
     команда: `./scripts/research_oracle.py query "keyword" -c q3_docs`
  2) потом внешний web‑поиск через встроенный web tool,
  3) синтез в 5-10 строк, 4) обновить `docs/INSIGHTS.md` + коммит "in progress",
  5) по завершении добавить итоговый инсайт. НЕ использовать mgrep/websearch.


<!-- legacy_line:178 -->

## Progress (2026-02-19) — PrimePow Auto GT10000 aggregate build

- `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000` отработал весь пул `*_970001_980000` … `*_990001_1000000` и завершился успешно (`Build completed successfully (7962 jobs)`).
- Появились артефакты:
  - `.lake/build/lib/lean/.../BrangeHeatCert_2026_01_28_PrimePowAutoGT10000.olean`
  - `.lake/build/lib/lean/.../BrangeHeatCert_2026_01_28_PrimePowAutoGT10000.ilean`
- После этого автоматически стартовал `Checker` с тем же модулем в tmux (`lake env lean ...Checker.lean`) и он ещё находится в прогоне (последний статус: `Sl+`, ~8h в процессе по моментальному snapshot).
- Вывод сборки в `/tmp/primepow_agg_build_20260217.log` — чистый по ошибкам, только warnings `linter.unnecessarySimpa`.


<!-- legacy_line:432 -->

## Synthesis (2026-01-31, in progress) — Formal interval checker for pilot sums

Target lemmas (PrimeCert):
- `prime_b_grid_pilot_sum_le_0_ub`, `prime_b_grid_pilot_sum_le_19_ub`
  (`Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30_Data.lean`)

Embedding search: `scripts/research_oracle.py` blocked (qmd not on PATH).
Web search: no obvious built‑in interval‑arithmetic tactic surfaced; results mostly point to
`norm_num` for numeric goals and `interval_cases` for interval reasoning, so expect a custom
interval checker if we want axiom‑free bounds.

Plan (5–10 lines, concrete pointers):
1) Add a generic “sum ≤ upper bound” lemma for finite/tsum bounds in a new file
   `Q3/Proofs/PrimeCert/IntervalChecker.lean` (use `Finset.sum_le_sum` + `tsum_le_tsum`).
2) Introduce a pilot‑specific certificate file (generated) with bucketed upper bounds for
   `prime_b_grid_weight_term` over ranges of `n`, e.g. `BrangeGrid_Pilot_2026_01_30_Intervals.lean`.
3) Provide monotonicity lemmas to justify bucket bounds (log/exp monotone, Fejér ≤ 1),
   so each bucket proof is `linarith` + `norm_num` on rationals.
4) Generate the bucket table + Lean proof skeleton via a new script
   `scripts/prime_brange_interval_checker_pilot.py` (keeps numeric bounds reproducible).
5) Replace `prime_b_grid_pilot_sum_le_*_ub` with theorems using the checker; then
   `lake env lean` on pilot files + `./scripts/check_axioms.sh`.

Status (2026-01-31):
- Added generator `scripts/prime_brange_interval_checker_pilot.py` and produced
  `Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30_Intervals.lean` (bucketed
  interval sums + numeric sum ≤ pilot UB lemmas).


<!-- legacy_line:527 -->

## Research note (2026-01-29) — digamma/trigamma asymptotics sanity check

- Asymptotics (DLMF 5.11 / trigamma) imply `ψ(1/4 + iπξ) = log|πξ| + O(1/ξ)` on tails,
  so `|a_star ξ| = O(log|ξ|)` and is strictly better than the current linear-growth axiom.
- Formalization gap: asymptotics are tail-only; to get a global bound we must
  combine tail bound with `a_star_bdd_on_compact` on `Icc (-R) R` and fix constants.
- Connes/Toeplitz remarks are good context but **not needed** for heat integrability;
  keep as background only.


<!-- legacy_line:536 -->

## Synthesis (2026-01-29, in progress) — BMO Bellman check-mode + regularity gate

- Added a lightweight `--check` mode to `bellman_bmo.py` to verify the closed‑form
  answer numerically (balance residual + value check). Heavy concavity/optimizer
  checks stay as future work.
- Methodology takeaway for Q3: **regularity‑gate**. The Fejér×heat window has kinks
  (|ξ| and cutoffs), so every step that assumes C² must be rejected unless
  explicitly justified; stick to Lip/modulus control.
- Future work capture: keep deeper BMO/Bellman formalization in `docs/INSIGHTS.md`
  and only link it from `ACTIVE/insights.md` (short).


<!-- legacy_line:1257 -->

## Ops note (2026-02-08, done) — isolated heavy runs for Lean/Codex

- Added executable helper: `scripts/run_heavy.sh`.
- What it does:
  1. Checks user-systemd availability.
  2. Creates `codex-heavy.slice` (if missing) with defaults:
     `MemoryHigh=20G`, `MemoryMax=28G`, `CPUWeight=80`,
     `ManagedOOMPreference=avoid`.
  3. Runs the command inside that slice via
     `systemd-run --user --scope`.
- Usage:
  - Interactive shell in isolated slice:
    `./scripts/run_heavy.sh`
  - Run a command in isolated slice:
    `./scripts/run_heavy.sh lake build Q3.Main`
- Verified smoke checks:
  - `./scripts/run_heavy.sh --help`
  - `./scripts/run_heavy.sh bash -lc 'echo RUN_HEAVY_OK'`
- Operational caveat:
  - Very large PrimeCert builds can exceed default `MemoryMax=28G` and be
    killed by `systemd-oomd` in that scope.
  - For those runs only, start a one-off scope with higher limits
    (e.g. `MemoryHigh=36G`, `MemoryMax=48G`) and keep the default slice
    limits unchanged for regular work.


<!-- legacy_line:1282 -->

## Synthesis (2026-02-10, in progress) — Step 2 GT10000 blocker: deep disjunction elaboration

- Target: unblock `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
  by replacing the last fallback axiom path for `n > 10000`.
- Root cause (code-level): GT10000 shard mem-lemmas generated a giant
  `have hcases : n = ... ∨ ...` and `rcases hcases with ...` tree
  (about 1k branches per shard), which is a recursion/elaboration hotspot.
- Evidence pointers:
  - `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowAutoGT10000_10001_20000.lean`
    (around `prime_heat_weight_term_le_pp_ub_of_10001_20000_primepow_mem`).
  - Generator path in `scripts/prime_brange_heat_pp_auto.py` (mem-lemma emission block).
- External cross-check: `lean-stat-learning-theory` (`7b82b13`) uses
  small-lemma decomposition and local heartbeat tuning, and does not rely on
  giant OR-dispatch chains for this kind of branching.
- Applied workaround:
  1. Generator now emits `classical; fin_cases hmem` for mem dispatch.
  2. Existing GT10000 shard files were migrated from `hcases/rcases` to `fin_cases`.
- Smoke verification:
  - `timeout 240 lake build +Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000_10001_20000:olean`
    reaches long compile phase without immediate recursion-depth crash (`EXIT=124`, timeout).
  - `timeout 240 lake build +Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000:olean`
    also proceeds without early compile errors (`EXIT=124`, timeout).
- Next checkpoint:
  - run isolated long build (`scripts/run_heavy.sh`) to completion and confirm
    `.olean` for GT10000 shards + aggregator, then re-run
    `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`.
- Update (2026-02-17):
  - Isolated long build was completed in `tmux` session `primepow`.
  - Final GT10000 shards reported as built:
    `970001_980000`, `980001_990000`, `990001_1000000`
    (`[done] all GT10000 shards built`).
  - This closes the long-run completion checkpoint for GT10000 shard compilation.

### Strategy memo (фиксируем, чтобы не забыть)

- Не лечить это как «системный баг»: первопричина в форме proof-term
  (`hcases/rcases` на огромном дизъюнкте), а не в Ubuntu.
- Базовый паттерн для GT10000: `classical; fin_cases hmem` вместо giant OR.
- Держать проверку двухступенчато:
  1. короткий smoke-timeout (ловит ранние ошибки/регрессии генерации),
  2. длинный изолированный прогон в `codex-heavy.slice` до `.olean`.
- После длинного прогона обязательный контрольный шаг:
  `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`.
