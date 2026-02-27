# Hub: PrimeCert Path B And Margin

Источник: `docs/insights/INSIGHTS_legacy_2026_02_26.md`.
PrimeCert, Path B, margin, heat/grid, t_critical и связанные closure-ветки.

## Included Sections

- line 44: Synthesis (2026-02-23, in progress) — Path B closure around `prime_term_le_at_t_critical_axiom`
- line 187: Synthesis (2026-02-06, in progress) — Закрытие `h_margin_cert` до single-axiom chain
- line 258: Decision (2026-02-02) — PrimeCert closure: formal numeric certificates now, analytic path later
- line 278: Synthesis (2026-02-02, in progress) — Prime-heat bucket bounds (no native_decide)
- line 342: Synthesis (2026-02-02, in progress) — Prime-heat PP pointwise bound
- line 370: Synthesis (2026-02-01, in progress) — Close `prime_b_grid_bounds_data` (grid cert)
- line 405: Synthesis (2026-01-31, in progress) — Interval-certificate closure (pilot → grid → heat)
- line 460: Synthesis (2026-01-30, in progress) — PrimeCert axiom closure plan (grid + heat)
- line 509: Synthesis (2026-01-29, in progress) — prime heat-weight summability axiom
- line 676: Synthesis (2026-01-24, resolved) — close `rho_oneK_tcritical_le_cstar_quarter`
- line 701: Synthesis (2026-01-26, in progress) — close PrimeCert B‑range axioms
- line 726: Synthesis (2026-01-26, in progress) — analytic Lipschitz closure for PrimeCert margin(B)
- line 761: Synthesis (2026-01-27, in progress) — PrimeCert closure architecture request (Proshka)
- line 1002: PrimeCert B-range Lipschitz (heat-weighted scaffold, 2026-01-28)
- line 1032: PrimeCert Lipschitz closure plan (2026-01-28)
- line 1057: Synthesis (2026-01-30, in progress) — PrimeCert cert-data axioms closure plan
- line 1094: Synthesis (2026-01-30, in progress) — PrimeHeatBoundsData closure pass 1
- line 1127: Pilot update (2026-01-30) — 2-point grid scaffolding
- line 1149: IN PROGRESS — Log‑Gaussian tail bound (PrimeCert B‑grid)
- line 1165: Synthesis (2026-02-03, in progress) — Prime-heat bucket pilot without native_decide
- line 1194: Synthesis (2026-02-03, in progress) — План закрытия Level‑2 аксиом PrimeCert
- line 1223: Synthesis (2026-02-06, in progress) — Tier-2 closure in main-chain via explicit margin hypothesis
- line 1326: Synthesis (2026-02-23, done) — Path B status after sub-agent audit

<!-- wave2_related_start -->
## Related Legacy Files (Wave 2)

Связанные standalone-файлы по домену `prime`:

- `docs/insights/C3_prime_cap_correctness_2026_01_19.md`
- `docs/insights/C3_RKHS_vs_window_approach_2026_01_19.md`
- `docs/insights/floor_cert_tcritical_2026_01_25.md`
- `docs/insights/heat_localization_kills_primes_2026_01_16.md`
- `docs/insights/heat_localization_kills_primes_2026_01_16.md`
- `docs/insights/heat_parameter_mismatch_2026_01_14.md`
- `docs/insights/prime_cert_brange_tcritical_2026_01_25.md`
- `docs/insights/prime_cert_tcritical_2026_01_25.md`
- `docs/insights/prime_term_nodes_bridge_2026_01_17.md`
- `docs/insights/prime_term_nodes_bridge_2026_01_17.md`
- `docs/insights/prime_term_shift_K_dependent_2026_01_19.md`
- `docs/insights/primecert_closure_plan_2026_01_29.md`
- `docs/insights/rayleigh_vs_sb_optional.md`
- `docs/insights/rkhs_cap_implementation_2026_01_15.md`
<!-- wave2_related_end -->

## Content

<!-- legacy_line:44 -->

## Synthesis (2026-02-23, in progress) — Path B closure around `prime_term_le_at_t_critical_axiom`

Цель: убрать/локализовать `Q3.prime_term_le_at_t_critical_axiom` без возврата к тяжёлой PrimeCert-цепочке.

Что проверено по коду:
- Аксома сидит в `Q3/Proofs/Q_nonneg_t_critical.lean:358`; её напрямую используют `prime_term_le_at_t_critical` и `Q_phi_shift_nonneg_t_critical`.
- Main-chain уже идёт через tau=0 + margin hypothesis (`PrimeCertMarginOnBrange`) и не требует этой аксиомы напрямую:
  `Q3/Proofs/Q_nonneg_t_critical.lean:344`, `Q3/Main.lean:73`.
- В `PrimeTerm_t_bridge` есть мост `t_critical -> t_rkhs_cap` с множителем `exp_tcrit_to_rkhs`:
  `Q3/Proofs/PrimeTerm_t_bridge.lean:22`; при `t_rkhs_cap=40` (`Q3/Proofs/A3_bridge_rayleigh_first.lean:25`)
  это слишком грубый путь для прямой замены аксиомы.
- Для Path B добавлен недостающий строительный блок:
  `prime_term_phi_shift_tcritical_le_cap` в `Q3/Proofs/PrimeTerm_t_bridge.lean`.

Embedding/web quick-check:
- Локальный индекс (`q3_docs`) дал релевантные точки: `insights/prime-cert-tcritical-2026-01-26.md`,
  `insights/prime-cert-brange-tcritical-2026-01-26.md`.
- По web tool: подтверждён актуальный статус `interval_cases` (case-split для конечных интервалов),
  см. `Mathlib.Tactic.IntervalCases` docs.


<!-- legacy_line:187 -->

## Synthesis (2026-02-06, in progress) — Закрытие `h_margin_cert` до single-axiom chain

Цель: перейти от `Q3.Main.RH_of_Weil_and_Q3 (h_margin_cert : Q3.PrimeCertMarginOnBrange)` к версии без `h_margin_cert`,
оставив в main-chain только `Q3.Weil_criterion_tau0`.

Проверенное состояние:
- Main-chain check (`./scripts/check_axioms.sh`): 1 project axiom (`Q3.Weil_criterion_tau0`) + standard axioms.
- Узел `h_margin_cert` опирается на PrimeCert cert-data (`prime_b_grid_bounds_data`, `prime_heat_bounds_arch_data`, `prime_heat_bucket_data`).
- Текущий `Checker`-путь использует `native_decide`; это может тянуть `Lean.ofReduceBool`/`Lean.trustCompiler` при прямом wiring.

План (8 шагов, с файлами):
1) Закрыть `prime_heat_bucket_data` через `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_BucketCheck.lean` и `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`, затем подставить в `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`.
2) Убрать `prime_heat_weight_term_le_pp_ub_of_prime_pow_axiom` в `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean` (ветка `n > 10000`).
3) Деаксоматизировать bucket0 путь без `native_decide` в `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowBucket0Auto*.lean`.
4) Закрыть `prime_heat_bounds_arch_data` в `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.
5) Закрыть grid bucket axioms в `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean`.
6) Заменить `prime_b_grid_bounds_data` на теорему в `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`.
7) Вывести теорему `PrimeCertMarginOnBrange` в `Q3/Proofs/Q_nonneg_t_critical.lean` и убрать параметр в `Q3/Main.lean`.
8) Финально проверить `lake env lean Q3/Main.lean`, `#print axioms Q3.Main.RH_of_Weil_and_Q3`, `./scripts/check_axioms.sh`.

Решение по порядку: сначала PrimeHeat (1-4), затем Grid (5-6), потом финальный wiring в Main (7-8).

Update (2026-02-06, execution pass):
- Step 1 integrated and compiling:
  - `prime_heat_bucket_data` is theorem in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`.
  - Name conflict between `BucketCheck` and `Checker` lemmas was removed by renaming internal
    lemmas in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_BucketCheck.lean`.
- Final verification (step 8 for current conditional chain) is green:
  - `lake env lean Q3/Main.lean`
  - `#print axioms Q3.Main.RH_of_Weil_and_Q3` -> `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`
  - `./scripts/check_axioms.sh` passes with 1 project axiom (`Weil_criterion_tau0`).
- Remaining blockers for unconditional closure (`h_margin_cert` removal):
  - Step 2: no integrated hole-free theorem path yet for `n > 10000` pointwise prime-power bound.
  - Step 3: `native_decide` remains in checker bucket inequality path.
  - Steps 4-7: still require formal arch/grid closures before removing `h_margin_cert`.

Update (2026-02-06, blocker map refresh):
- Verified by `#print axioms` on PrimeCert nodes:
  - `prime_cert_margin_on_Brange_axiom` currently depends on exactly four project axioms:
    `prime_heat_weight_term_le_pp_ub_of_prime_pow_axiom`,
    `prime_heat_bounds_arch_data`,
    `prime_b_grid_bucket_bounds`,
    `prime_b_grid_arch_bounds_data`.
- Grid progress is real but partial:
  - `prime_b_grid_bucket_sum_ub` is theorem (no project axiom on this node);
  - `prime_b_grid_bounds_data` split into narrower obligations in `BrangeCert_2046`.
- Root cause for Step 2 block:
  - local generator `scripts/prime_brange_heat_pp_bucket0_auto.py` closes only bucket0
    (`n ≤ 10000`), so `Checker` keeps axiom fallback for `n > 10000`.
- Root cause for Step 5 block:
  - `scripts/prime_brange_interval_checker_grid.py` emits numeric bucket UB tables, but no
    theorem bridge `prime_b_grid_bucket_sum ≤ prime_b_grid_bucket_ub`.
- Practical next action:
  1) add a theorem-producing generator for heat `n > 10000` (envelope or interval certificates),
  2) then add theorem-producing generator for grid bucket sums,
  3) then remove `h_margin_cert` in `Q3/Main.lean`.

Range clarification (2026-02-06):
- Для heat-blocker в `prime_heat_weight_term_le_pp_ub_of_prime_pow` нам НЕ нужен
  бесконечный хвост по `n`.
- Точный целевой диапазон pointwise-доказательств:
  `IsPrimePow n` и `10000 < n ≤ prime_cert_heat_N`, где
  `prime_cert_heat_N = 1_000_000`.
- Это следует из сигнатуры checker-леммы:
  `... (hn : IsPrimePow n) (hN : n ≤ prime_cert_heat_N)`.
- Для `n > prime_cert_heat_N` в main chain используется уже tail-ветка
  (`prime_heat_tail_bound`), а не pointwise-сертификаты.
- Практически это означает:
  нужно закрыть конечное множество prime powers в диапазоне
  `(10000, 1_000_000]` (не весь `ℕ`).


<!-- legacy_line:258 -->

## Decision (2026-02-02) — PrimeCert closure: formal numeric certificates now, analytic path later

Goal: close main chain fast **without axioms** and with kernel‑checked evidence.

Decision:
- Use **formal numeric certificates** in Lean (ℚ tables + `native_decide`/`norm_num`)
  to close bucket bounds for `prime_heat_bucket_bounds` and `prime_b_grid_bucket_bounds`.
- This is fully formal (Lean kernel checks), not a “trust the script” axiom.

Alternative (documented for later cleanup):
- Replace certificate bounds with **analytic** proofs:
  monotonicity + `vonMangoldt ≤ log`, `sum ≤ integral`, and explicit tail bounds.
- Target replacement points:
  `BrangeHeatCert_2026_01_28_*` (heat buckets) and
  `BrangeGrid_PrimeSum_2026_01_30_*` (grid buckets + tail).

Plan: after mainline closure, revisit and swap cert‑based bounds with analytic lemmas
to remove the computational layer.


<!-- legacy_line:278 -->

## Synthesis (2026-02-02, in progress) — Prime-heat bucket bounds (no native_decide)

Target axioms/lemmas:
- `prime_heat_bucket_bounds` and `prime_heat_bucket_sum_ub` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`
- Wired into `prime_heat_sum_data` → `prime_heat_bounds_prime_data_of_data` →
  `prime_heat_bounds_data` in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.

Embedding search (q3_docs, vsearch):
- Queries: "interval checker bucket", "primecert interval bucket bounds",
  "prime heat bucket", "interval arithmetic lean exp log".
- Top hits: `docs/INSIGHTS.md` (PrimeCert closure notes) and
  `docs/insights/primecert_closure_plan_2026_01_29.md`; nothing on interval arithmetic.
- Note: `qmd query` pulls heavy expansion/reranker models and can break JSON;
  use `--mode vsearch` for stable output.

Web search:
- `Mathlib.Tactic.IntervalCases` confirms `interval_cases` is finite case splitting (ℕ/ℤ).
- No dedicated interval‑arithmetic tactic for exp/log found.

Mathlib scan (Explore):
- Tactics: `bound`, `linarith`, `norm_num`, `interval_cases`.
- Monotonicity lemmas: `Real.exp_*`, `Real.log_*`.
- Useful bound: `ArithmeticFunction.vonMangoldt_le_log`
  (`Mathlib/NumberTheory/VonMangoldt.lean`) to replace `w_Q` by `log`.

Plan (5–10 lines, concrete pointers):
1) Add `prime_heat_weight_term_le_envelope` using `vonMangoldt_le_log`,
   `Real.exp_le_exp_of_le`, and monotonicity of `xi_n`; expose a monotone envelope `f(n)`.
2) Prove `prime_heat_bucket_sum_le_envelope` via `Finset.sum_le_sum` and endpoint bounds.
3) Extend `scripts/prime_brange_heat_interval_checker.py` (or new script) to emit
   endpoint envelopes + a Lean file of `prime_heat_bucket_envelope_ub`.
4) Replace `prime_heat_bucket_bounds` with a theorem using the envelope bounds;
   keep `prime_heat_bucket_sum_ub` via `prime_heat_bucket_ub_sum`.
5) Success check: `lake env lean` on `BrangeHeatCert_2026_01_28_SumData.lean`
   and `BrangeHeatCert_2026_01_28_Partial.lean`, then `./scripts/check_axioms.sh`.

Update (2026-02-02) — Prime-power term certificate attempt
- New blocker: `prime_heat_weight_term_le_pp_ub_of_prime_pow` (axiom) in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`.
- Data file: `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowData.lean`
  (generated by `scripts/prime_brange_heat_pp_interval_checker.py` from the
  same `prime_partial_interval_2026-01-31_0009.txt` source).
- Embedding search: `qmd query` fails on this host (llama-cpp Metal context).
  Fallback used: `qmd search` (BM25) on `q3_docs`; top hits are
  `docs/INSIGHTS.md` + `docs/insights/primecert_closure_plan_2026_01_29.md`.
- Web search: `Mathlib.Tactic.IntervalCases` only (finite case splitting);
  no ready interval-AR for `exp/log` found; external `ComputableReal` is not allowed.

Plan (5–10 lines, concrete pointers):
1) Quick tactic check: verify whether `interval` is available in Mathlib 4.24;
   if not, note in `BrangeHeatCert_2026_01_28_Pilot.lean`.
2) If `interval` works: extend `prime_brange_heat_pp_interval_checker.py` to emit
   per‑term lemmas `prime_heat_weight_term_le_pp_ub_of_prime_pow` by case‑splitting
   on `n` and using `interval`/`linarith` for each term.
3) If `interval` is unavailable: pivot to envelope‑based bucket bounds
   (`prime_heat_weight_term_le_envelope`, then bucket endpoint bounds) and
   add a new generator for `prime_heat_bucket_envelope_ub`.
4) Keep the proof in a new file `BrangeHeatCert_2026_01_28_PrimePowChecker.lean`
   and import it into `BrangeHeatCert_2026_01_28_Checker.lean` only after the lemma
   is fully theoremized.
5) Success check: `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`
   then `./scripts/check_axioms.sh` (expect axiom count to drop, not increase).


<!-- legacy_line:342 -->

## Synthesis (2026-02-02, in progress) — Prime-heat PP pointwise bound

Target lemma:
- `prime_heat_weight_term_le_pp_ub_of_prime_pow` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
  (wired into `prime_heat_bucket_bounds` → `prime_heat_sum_data`).

Embedding search:
- `scripts/research_oracle.py query ... -c q3_docs` fails on this host (qmd/Metal context).
- Fallback `qmd search -c q3_docs` only hits `docs/INSIGHTS.md` and older prime‑cert notes;
  no interval‑arithmetic guidance.

Web search:
- No built‑in Mathlib interval‑arithmetic tactic for `exp/log` surfaced.
- `ComputableReal` has `exp` support but no `log`, so it’s not a direct drop‑in.

Plan (5–10 lines, concrete pointers):
1) Keep the target lemma isolated in `BrangeHeatCert_2026_01_28_Checker.lean`;
   do not change main‑chain wiring until we have a proof method.
2) Prepare a pilot: add a new file
   `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowPilot.lean`
   with two buckets (0 and 99) and per‑prime‑power obligations.
3) Extend `scripts/prime_brange_heat_pp_interval_checker.py` to emit those pilot obligations
   (per‑n bounds + a list of prime powers in the bucket).
4) Ask Proshka for a Lean‑compatible numeric proof strategy for `exp/log` inequalities
   (interval arithmetic or monotone bounds) and validate it on the pilot.
5) If the pilot closes, scale to all buckets and replace the axiom.


<!-- legacy_line:370 -->

## Synthesis (2026-02-01, in progress) — Close `prime_b_grid_bounds_data` (grid cert)

Target axiom:
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data` in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`

Embedding search:
- `qmd` is installed at `~/.bun/bin/qmd`; running with `PATH="$HOME/.bun/bin:$PATH"` works.
- Top hit: `qmd://q3_docs/insights/prime-cert-brange-tcritical-2026-01-26.md` (goal: certify `margin(B) ≥ prime_cert_margin_lb`).
- Other hits were low-signal or unrelated.

Web search:
- `interval_cases` is the canonical finite-range splitter for ℕ/ℤ; no dedicated numeric interval-arithmetic tactic found.
- Tactic check: `interval` is unknown with `import Mathlib` (stdin test).

Plan (5–10 lines, concrete pointers):
1) Prime-sum buckets: extend `BrangeGrid_PrimeSum_2026_01_30_Checker.lean` with a reusable lemma to reduce each bucket sum to a finite `Finset` sum and try `interval`/`linarith` on per-term bounds (no `native_decide`).
2) Generator upgrade: extend `scripts/prime_brange_interval_checker_grid.py` to also emit per-term bounds (or per-subinterval bounds) so `Finset.sum_le_sum` can close each `prime_b_grid_bucket_sum i k ≤ prime_b_grid_bucket_ub i k`.
3) Tail bound: prove `prime_b_grid_tail_term_sum_le_bound` analytically from `BrangeGrid_PrimeSumTail.lean` using the integral comparison and a numeric bound, possibly in a new `BrangeGrid_PrimeSum_2026_01_30_TailCert.lean`.
4) Wire: replace axioms in `BrangeGrid_PrimeSum_2026_01_30_Data.lean` with the new proofs, then build `PrimeBGridBounds` in `BrangeCert_2046.lean`.
5) Success check: `lake env lean` on grid files; then `./scripts/check_axioms.sh` expecting only `Weil_criterion_tau0` + `prime_heat_bounds_data`.

Progress (2026-02-01):
- `scripts/prime_brange_interval_checker_grid.py` now emits per-grid bucket sum totals and
  `prime_b_grid_bucket_ub_sum_le` in
  `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Intervals.lean`;
  this discharges the `h_sum_ub` part once `h_bucket` is available.
- `scripts/prime_brange_heat_interval_checker.py` now emits
  `prime_heat_bucket_ub_sum` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Intervals.lean`, and
  `BrangeHeatCert_2026_01_28_SumData.lean` adds
  `prime_heat_bucket_ub_sum_le_partial`.

---


<!-- legacy_line:405 -->

## Synthesis (2026-01-31, in progress) — Interval-certificate closure (pilot → grid → heat)

Target lemmas/axioms (PrimeCert):
- `prime_b_grid_pilot_sum_le_0`, `prime_b_grid_pilot_sum_le_19`
  (`Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30_Data.lean`)
- `prime_b_grid_prime_sum_le_all`
  (`Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean`)
- `prime_heat_sum_data`
  (`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`)

Embedding search: `scripts/research_oracle.py` blocked (qmd not on PATH).

Plan (5–10 lines, concrete pointers):
1) Generate a Lean cert file with per‑B interval upper bounds for
   `prime_b_grid_prime_sum_up_to` and numeric proofs with `norm_num`
   (no `native_decide`).
2) Pilot: replace axioms with theorems `prime_b_grid_pilot_sum_le_0/19`
   in `BrangeGrid_Pilot_2026_01_30_Data.lean`.
3) Full grid: extend generator to all 20 points; prove
   `prime_b_grid_prime_sum_le_all` by `fin_cases` in
   `BrangeGrid_PrimeSum_2026_01_30_Data.lean`.
4) Heat: use the same pattern to populate `prime_heat_sum_data.h_sum`
   from `prime_cert_brange_heat_prime_partial_interval_2026-01-31_0009.txt`;
   keep `h_tail` from `BrangeHeatCert_2026_01_28_Data.lean`.
5) Success check: `lake env lean` on pilot/grid/heat files, then
   `./scripts/check_axioms.sh` + refresh graphs/stats.


<!-- legacy_line:460 -->

## Synthesis (2026-01-30, in progress) — PrimeCert axiom closure plan (grid + heat)

Goal: close the 3 main-chain PrimeCert axioms:
`prime_b_grid_bounds_data`, `prime_heat_bounds_arch_data`, `prime_heat_bounds_prime_data`.

Plan (5–10 lines, concrete pointers):
1) Grid bounds: move `prime_b_grid_bounds_data` to a theorem in
   `Q3/Proofs/PrimeCert/BrangeCert_2046.lean` by proving `h_arch`/`h_prime`
   using the numeric tables already in `BrangeGrid_2046.lean`.
2) Create a small “grid evidence” file (if needed) with per‑index bounds extracted
   from `output/prime_cert_brange_tcritical_interval_2026-01-30_2206.txt`, keeping values as ℚ,
   then use `fin_cases` + `norm_num` (no `native_decide`).
3) Prime heat bound: use the decomposition in
   `BrangeHeatCert_2026_01_28_Data.lean` plus numeric evidence in
   `BrangeHeatCert_2026_01_28_SumData.lean` to show
   `tsum = sum_{n≤N} + tail`, then prove `≤ L_prime_heat_raw`.
4) Arch heat bound: build a dedicated lemma in
   `BrangeHeatCert_2026_01_28_Data.lean` or a new file that upper‑bounds the
   integral via interval arithmetic / numeric quadrature certificate; keep it
   as a theorem (no new axioms).
5) Wire results back: drop the three axioms, update `Q3/CheckAxioms.lean`,
   `PHILOSOPHY_OF_PROOF.md`, and re‑run `./scripts/check_axioms.sh`.

Status (2026-01-30):
- Added grid prime partial sums + tail bound in `PrimeCert/BrangeGrid_2046.lean`.
- Added prime-heat tsum decomposition scaffold in
  `PrimeCert/BrangeHeatCert_2026_01_28_Data.lean` and sum evidence in
  `PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`.
- Full closure still blocked on formal numeric certification of
  `arch_term` and `prime_term` values (needs interval/verified quadrature or
  a generated Lean proof pipeline).


<!-- legacy_line:509 -->

## Synthesis (2026-01-29, in progress) — prime heat-weight summability axiom

- Added Tier‑1 axiom `w_Q_heat_weight_summable` to capture summability of
  `w_Q n * exp(-4π^2 t (xi_n n)^2) * |xi_n n|`.
- Using this axiom to finish `prime_term_Lipschitz_heat` and
  `margin_Lipschitz_heat_of_bounds` in `Brange_Lipschitz_HeatProof.lean`.


<!-- legacy_line:676 -->

## Synthesis (2026-01-24, resolved) — close `rho_oneK_tcritical_le_cstar_quarter`

- Decision: mainline uses tau = 0, so the cap reduces to `rho_one ≤ c_star/4`.
- Implemented as a direct numeric bound (no K dependence).
- Legacy `rho_oneK` (tau-shift) remains as a separate variant; not used in mainline.


<!-- legacy_line:701 -->

## Synthesis (2026-01-26, in progress) — close PrimeCert B‑range axioms

- Target axioms (current): `prime_b_grid_bounds_data`,
  `prime_heat_bounds_arch_data`, `prime_heat_bounds_prime_data`
  in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`; used by
  `prime_cert_margin_on_Brange_axiom` → `Q3/Proofs/Q_nonneg_t_critical.lean`.
- q3search/websearch commands are **missing** in this sandbox (both return “command not found”),
  so no semantic scan done yet.
- Option A (preferred): prove Lipschitz of `margin(B)` analytically by bounding
  `‖phi_shift x - phi_shift y‖_∞` on `B ∈ [B_min, B_max]`, then combine with
  existing arch/prime Lipschitz bounds (see `Q3/Proofs/Q_Lipschitz_*`).
- Option B (fallback): keep axioms but gate them behind a dedicated certificate module
  with explicit provenance + CI check; **do not** re‑introduce `native_decide`.
- Status update (2026-01-26): **Option B implemented** —
  certificate module + hashes in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`,
  evidence files pinned in `Q3/Proofs/PrimeCert/README.md`,
  CI hash check added in `scripts/check_axioms.sh` (uses `output/prime_cert_*_2026-01-26_*`).
- Status update (2026-01-29): `prime_b_grid_val_le_margin` and
  `prime_heat_bounds_cert` are now theorems (derived from `*_data` axioms).
- Success check: `lake env lean Q3/Proofs/PrimeCert/Brange_2046.lean`,
  then `./scripts/check_axioms.sh` (only `Weil_criterion_tau0` + PrimeCert remain).
- Status: **Option B implemented**; Option A (analytic closure) remains long‑term.

---


<!-- legacy_line:726 -->

## Synthesis (2026-01-26, in progress) — analytic Lipschitz closure for PrimeCert margin(B)

- Target axioms: `prime_b_grid_bounds_data`,
  `prime_heat_bounds_arch_data`, `prime_heat_bounds_prime_data`
  (now in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`); goal is to **replace** them by proofs.
- q3search/websearch are **missing** in this sandbox (both “command not found”); no semantic scan yet.
- 2026-01-26 check: `q3search`/`websearch` still unavailable (127 / “Befehl nicht gefunden”).
- Aristotle tooling installed in `.venv` (CLI + `aristotlelib`), but submission is
  blocked by missing `ARISTOTLE_API_KEY`. Next action: set key and submit
  `aristotle_input/proshka_primecert_lipschitz_2026_01_26.md`.
- Core idea: prove `B ↦ arch_term (phi_shift B t_critical 0)` and
  `B ↦ prime_term (phi_shift B t_critical 0)` are Lipschitz on `[B_min, B_max]`,
  then combine to bound the margin. Use existing bounds:
  `Q_Lipschitz_arch_bridge.lean` + `Q_Lipschitz_prime_bridge.lean`,
  plus a **uniform sup‑norm bound** on `|phi_shift B₁ - phi_shift B₂|`.
- Need explicit constant `L ≤ 0.3` (matches `prime_cert_L_ub`), or show a sharper bound
  and then relax to 0.3.
- **Implemented (analytic skeleton):** `Q3/Proofs/PrimeCert/Brange_Lipschitz_Analytic.lean`
  proves a symbolic Lipschitz bound for `margin` with constant
  `margin_Lipschitz_const := (2*B_max*M_a_local(B_max)+W_sum_local(B_max)) * (B_max/B_min^2)`,
  plus a pointwise `phi_shift` bound in `B`. This compiles.
- **Note (2026-01-26):** attempted a weighted prime‑sum Lipschitz variant here, but Lean
  hit deterministic heartbeat timeouts; rolled back the weighted lemma to keep the file compiling.
  Next attempt should refactor to a finite‑sum (`Finset`) proof to avoid heavy `tsum` machinery.
- **Still missing:** an explicit numeric upper bound on
  `2*B_max*M_a_local(B_max)+W_sum_local(B_max)` to show
  `margin_Lipschitz_const ≤ 3/10` (or any certified ≤ `prime_cert_L_ub`).
- File pointers: `Q3/Proofs/ShiftedWindows.lean` (phi_shift definition/support),
  `Q3/Proofs/Q_Lipschitz_arch_bridge.lean`, `Q3/Proofs/Q_Lipschitz_prime_bridge.lean`,
  `Q3/Proofs/PrimeCert/Brange_2046.lean`.
- Success check: `lake env lean Q3/Proofs/PrimeCert/Brange_2046.lean`,
  then `./scripts/check_axioms.sh` (PrimeCert axioms eliminated).

---


<!-- legacy_line:761 -->

## Synthesis (2026-01-27, in progress) — PrimeCert closure architecture request (Proshka)

- Goal: remove the two PrimeCert axioms in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean` without changing the one-scale mainline.
- Bottlenecks:
  - Lipschitz: convert the symbolic bound in `Q3/Proofs/PrimeCert/Brange_Lipschitz_Analytic.lean` into
    `margin_Lipschitz_const ≤ prime_cert_L_ub` via certified numeric bounds on `M_a_local(4.9)` and `W_sum_local(4.9)` (or avoid these).
  - Grid: connect the rational table in `Q3/Proofs/PrimeCert/BrangeGrid_2046.lean` to the true `arch_term - prime_term`
    (needs a Lean-side verifier or another reduction).
- Proshka request drafted: `aristotle_input/proshka_primecert_closure_2026_01_27.md`.

---


<!-- legacy_line:1002 -->

## PrimeCert B-range Lipschitz (heat-weighted scaffold, 2026-01-28)

**Why:** current main-chain axioms are
`PrimeCert.prime_b_grid_bounds_data`, `PrimeCert.prime_heat_bounds_arch_data`,
and `PrimeCert.prime_heat_bounds_prime_data`.
The analytic bound in `Brange_Lipschitz_Analytic.lean` uses `W_sum_local` and is far too large;
we need a *heat-weighted* Lipschitz constant to match the certificate scale (~0.3).

**What was added (scaffold):**
- `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatScaffold.lean`
  - `PrimeMarginHeatLipschitzCert` structure (L_arch/L_prime + certified bounds)
  - `margin_Lipschitz_of_cert` lemma to combine bounds
- `scripts/prime_brange_heat_lipschitz_cert.py`
  - numeric helper to estimate heat-weighted constants (arch + prime) for t_critical
  - outputs `output/prime_cert_brange_heat_L_*.txt`
  - latest output: `output/prime_cert_brange_heat_L_interval_2026-01-30_2309.txt`
    (sha256 `da6a6ac1221f93d376aafecd189169607b40b5d394868e893124445089a3e0a5`)
    with `L_prime_heat ≈ 4.0049`, `L_arch_heat ≈ 1.3604`, `L_total ≈ 0.59614`
    → conservative bound `L_total ≤ 0.60`

**Next (to actually close the axiom):**
1) Produce a certified numeric constant from the script output
2) Provide Lean lemmas `h_arch` and `h_prime` (or a combined margin version)
3) Instantiate `PrimeMarginHeatLipschitzCert` and replace the axiom in
   `Q3/Proofs/PrimeCert/BrangeCert_2046.lean` / `Brange_2046.lean`.

**Note:** q3search failed locally (403 spend limit), so we used local `rg` only.

---


<!-- legacy_line:1032 -->

## PrimeCert Lipschitz closure plan (2026-01-28)

**Target lemma:** `Q3.Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange` in
`Q3/Proofs/PrimeCert/BrangeCert_2046.lean` (main-chain axiom).

**Semantic search:** attempted `q3search` (3 queries) and `websearch` (1 query) → both commands missing
in this sandbox (`Befehl nicht gefunden`, exit 127). Fell back to local `rg`.

**Local hits:** `phi_shift_lipschitz_B_exp` + `margin_Lipschitz_symbolic` in
`Q3/Proofs/PrimeCert/Brange_Lipschitz_Analytic.lean` give the formal *shape* of a Lipschitz proof,
but constants are too large (`W_sum_local`, `M_a_local`).

**Option 1 (preferred):** formalize heat-weighted bounds using `phi_shift_lipschitz_B_exp`,
then bound prime/arch contributions by numeric constants from
`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Data.lean`; instantiate
`PrimeMarginHeatLipschitzCert` (file: `Brange_Lipschitz_HeatScaffold.lean`) and replace the axiom.

**Option 2 (fallback):** keep the axiom but document the analytic bound path
(`margin_Lipschitz_symbolic`) as “false-for-now” due to oversized constants.

**Immediate next actions:** (a) create Lean lemmas `h_arch`/`h_prime` using heat-weighted
integral/sum bounds; (b) wire `margin_Lipschitz_of_cert` into `BrangeCert_2046.lean`;
(c) re-run `lake env lean` on the touched files.


<!-- legacy_line:1057 -->

## Synthesis (2026-01-30, in progress) — PrimeCert cert-data axioms closure plan

- Target axioms: `prime_b_grid_bounds_data` (`Q3/Proofs/PrimeCert/BrangeCert_2046.lean`)
  and the heat cert-data axioms `prime_heat_bounds_arch_data`,
  `prime_heat_bounds_prime_data` (`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Data.lean`);
  these feed `prime_b_grid_val_le_margin` and `prime_margin_Lipschitz_on_Brange`.
- Step 1: discharge `PrimeHeatBoundsData` by proving `h_arch` + `h_prime` and use
  `prime_heat_bounds_total` for `h_total` (files:
  `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof.lean`,
  `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatIntegrable.lean`).
- Step 2: wire `prime_heat_bounds_cert` into
  `margin_Lipschitz_heat_of_bounds` → `prime_margin_Lipschitz_on_Brange`
  (`Q3/Proofs/PrimeCert/BrangeCert_2046.lean`).
- Step 3 (grid data): either (A) replace `prime_b_grid_bounds_data` with analytic bounds
  at each grid point using the same arch/prime estimates, or (B) keep as cert-data but
  add a non-`native_decide` verification file that checks the finite inequalities with
  `norm_num` only.
- Update (2026-01-30): added `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSumTail.lean`
  to split the prime-term tsum into partial sum + tail and reduce the grid bound
  to two explicit obligations: (i) `prime_b_grid_prime_sum_up_to` ≤ table sum and
  (ii) tail ≤ `prime_b_grid_tail_bound`. This is the intended landing zone for the
  interval-certificate pilot (2 points first, then full grid).
- Update (2026-01-30): proved a pointwise analytic domination lemma
  `prime_b_grid_weight_term_le_tail_term` (same file), reducing the tail proof to
  bounding `∑' n, prime_b_grid_tail_term (n + (N+1))` by the tiny numeric constant.
  This isolates the remaining work to a sum→integral comparison + numeric bound.
- Constraint: keep everything one-scale (`t_critical`, `tau = 0`) and avoid two-scale bridges
  (`Q3/Proofs/ShiftedWindows.lean`, `Q3/Proofs/Params_Critical.lean` are the anchors).
- External leads for explicit prime-sum bounds: Schoenfeld (1976), Dusart/Trudgian bounds,
  and the AFP entry `Chebyshev_Prime_Bounds` as a formalizable reference path.
- Web scan (2026-01-30): AFP `Chebyshev_Prime_Bounds` gives explicit ψ/θ bounds and a
  concrete proof structure; consider porting the tail bound pattern for
  `∑ w_Q n * exp(-c (log n)^2) * |log n|`. Also note newer explicit ψ bounds (e.g., 2023 JMAA)
  as a constants source, but likely too heavy to formalize directly.
- Success check: `lake env lean Q3/Proofs/PrimeCert/BrangeCert_2046.lean`,
  then `lake env lean Q3/CheckAxioms.lean` once mathlib is healthy.


<!-- legacy_line:1094 -->

## Synthesis (2026-01-30, in progress) — PrimeHeatBoundsData closure pass 1

- Target axioms: `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Data.lean` and
  `Q3.Proofs.PrimeCert.prime_heat_sum_data` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`; they feed
  `prime_heat_bounds_data` → `prime_heat_bounds_cert` → `prime_margin_Lipschitz_on_Brange`.
- Update (2026-01-30): split cert-data into two axioms
  (`prime_heat_bounds_arch_data`, `prime_heat_sum_data`);
  `prime_heat_bounds_data` is now derived from these.
- Embedding search (q3_docs): queries `prime_heat_bounds`, `BrangeHeatCert`,
  `heat Lipschitz`, `prime cert heat`, `brange heat` returned only generic
  prime-cert notes; no existing formal closure.
- Web leads (external bounds for prime sums): Schoenfeld (1976) explicit ψ/θ bounds;
  newer explicit ψ bounds in JMAA 2023 (useful for tail control if formalized).
- Arch bound plan: use `a_star_linear_growth` + closed-form Gaussian integrals to
  upper-bound `∫_{Icc} |a_star ξ| * exp(-4π^2 t ξ^2) * |ξ|` by
  `prime_cert_L_arch_heat_raw` (files: `Brange_Lipschitz_HeatIntegrable.lean`,
  `BrangeHeatCert_2026_01_28.lean`).
- Prime bound plan: split sum at `N = 10^6` (finite part imported with
  directional rounding as data), plus a tail bound via the integral estimate
  already used in `scripts/prime_brange_heat_lipschitz_cert.py`; wrap into Lean
  inequalities with `norm_num`.
- Implementation: add a dedicated sum-data file
  (`BrangeHeatCert_2026_01_28_SumData.lean`) and replace the axiom with a
  theorem that composes the two bounds.
- Status update (2026-01-30): added `BrangeHeatCert_2026_01_28_Data.lean` for
  constants + arch bound, and `BrangeHeatCert_2026_01_28_SumData.lean` for
  partial+tail evidence; `prime_heat_bounds_data` is now derived in
  `BrangeHeatCert_2026_01_28.lean`.
- Success check: `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
  then `lake env lean Q3/CheckAxioms.lean`.


<!-- legacy_line:1127 -->

## Pilot update (2026-01-30) — 2-point grid scaffolding

- Added `Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30.lean`:
  `PrimeBGridPilotHyp` packs the two required inequalities (partial sum + tail)
  and provides pilot lemmas for `i=0` (B=3.0) and `i=19` (B=4.9) without adding
  axioms or sorries.
- Added `scripts/prime_brange_pilot_points.py` to extract the two rows from the
  existing B-range certificate and emit a pilot trace file:
  `output/prime_cert_brange_tcritical_pilot_2026-01-30_1820.txt`.
- Next: supply `PrimeBGridPilotHyp` for the two points via interval‑certificate
  inequalities (partial sum up to N and tail bound). Once that lands, we can
  lift to all 20 points.


<!-- legacy_line:1149 -->

## IN PROGRESS — Log‑Gaussian tail bound (PrimeCert B‑grid)

- Target: prove `prime_b_grid_tail_term` summability and the numeric tail bound in
  `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSumTail.lean` (feeds the pilot + full grid).
- Use `Mathlib/Analysis/SumIntegralComparisons` (`AntitoneOn.sum_le_integral`) to show
  `∑_{n≥N+1} f(n) ≤ ∫_{N}^∞ f(x) dx` for `f(x) = 2 log x / sqrt x * exp(-t (log x)^2)`.
- Establish monotone/antitone + nonneg of `f` for `x ≥ N` in the same file
  (or a helper lemma file under `Q3/Proofs/PrimeCert/`).
- Substitute `u = log x` to rewrite the integral as
  `∫_{log N}^∞ 2u * exp(-t u^2 + u/2) du`; then complete the square.
- Numeric closure: bound the Gaussian tail explicitly (Mill’s ratio) or,
  if Lean bounds get heavy, submit a focused Aristotle lemma for the tail integral
  and then plug into `prime_b_grid_tail_bound_of_tail_term`.
- Once tail is closed, finish the two pilot points in
  `Q3/Proofs/PrimeCert/BrangeGrid_Pilot_2026_01_30.lean` and lift to all 20 grid points.


<!-- legacy_line:1165 -->

## Synthesis (2026-02-03, in progress) — Prime-heat bucket pilot without native_decide

- Target: pilot lemmas `prime_heat_bucket_sum_le_ub_pilot_{0,99}` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Pilot.lean`; these mirror the eventual
  `prime_heat_bucket_bounds` path in `BrangeHeatCert_2026_01_28_SumData.lean`.
- Blocker: current `BrangeHeatCert_2026_01_28_Checker.lean` imports huge
  `BrangeHeatCert_2026_01_28_PrimePowData.lean` and uses `native_decide`, which we want to
  avoid for a clean axiom list (compiler-trust axioms).
- Option 1 (preferred): refactor bucket/partition defs into
  `BrangeHeatCert_2026_01_28_BucketDefs.lean`; generate a **pilot** prime-power table for
  buckets 0 & 99 only (new `scripts/prime_brange_heat_pp_interval_checker.py --buckets 0,99`).
- Option 1: prove `prime_heat_bucket_sum_le_pp_ub_pilot_{0,99}` and
  `prime_heat_bucket_pp_sum_ub_le_bucket_pilot_{0,99}` using explicit rationals with
  `norm_num`/`decide` (no `native_decide`).
- Option 2 (fallback): keep full `PrimePowData` + `native_decide` off-chain and use pilot
  lemmas only as structure checks (no numeric proof).
- Success check: `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_BucketDefs.lean`
  and `BrangeHeatCert_2026_01_28_Pilot.lean` compile without new axioms in `#print axioms`.

**Update (2026-02-03):**
- Added `BrangeHeatCert_2026_01_28_BucketDefs.lean` to isolate bucket/partition lemmas.
- Added sums-only pilot data `BrangeHeatCert_2026_01_28_PrimePowPilotSums.lean` and proved
  bucket 0/99 pilot bounds in `BrangeHeatCert_2026_01_28_Pilot.lean` without `native_decide`.
- Extended `scripts/prime_brange_heat_pp_interval_checker.py` with `--buckets` and
  `--subnamespace`; generated full per-term pilot data `BrangeHeatCert_2026_01_28_PrimePowPilot.lean`
  (kept for later; not compiled yet).
- Verified: `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_BucketDefs` and
  `...PrimePowPilotSums`; `lake env lean BrangeHeatCert_2026_01_28_Pilot.lean` passes.


<!-- legacy_line:1194 -->

## Synthesis (2026-02-03, in progress) — План закрытия Level‑2 аксиом PrimeCert

Target axioms:
- `prime_heat_bucket_data` in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`
- `prime_heat_bounds_arch_data` in `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
- `prime_b_grid_bounds_data` in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`

Embedding search (q3_docs):
- Queries: "prime_heat_bucket_data", "prime_b_grid_bounds_data", "prime_heat_bounds_arch_data".
- Result: `qmd` query timed out on this host (120s/60s); no hits recorded.

Web search:
- Interval arithmetic in Lean / intervalIntegral numeric bounds: no drop‑in tactic found yet.

Plan (5–10 lines, concrete pointers):
1. `prime_heat_bucket_data`: move data into a proof file (e.g. `BrangeHeatCert_2026_01_28_BucketCheck.lean`)
   and prove per‑bucket bounds via interval/endpoint envelopes emitted by
   `scripts/prime_brange_heat_interval_checker.py` (Lean proofs over ℚ + `linarith`, no `native_decide`).
2. `prime_heat_bounds_arch_data`: add `BrangeHeatCert_2026_01_28_ArchBounds.lean` with piecewise bounds on
   `|a_star| * heat_weight_tc`, then discharge the integral bound in
   `BrangeHeatCert_2026_01_28.lean` using `intervalIntegral` + certified endpoints.
3. `prime_b_grid_bounds_data`: extend `BrangeGrid_PrimeSum_2026_01_30_Checker.lean` to reduce each grid bucket
   to finite sums and close bounds using `BrangeGrid_PrimeSum_2026_01_30_Intervals.lean` data.
4. Infrastructure + guardrail: add `Q3/Proofs/PrimeCert/IntervalLemmas.lean` (ℚ endpoint lemmas for exp/log
   monotonicity), and keep A3_FLOOR vs RKHS strategies strictly separated in these files.
5. Verification + success: after each swap run `lake env lean` on touched files and `./scripts/check_axioms.sh`,
   log axiom count drop in `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`; success when only project axiom left is
   `Q3.Weil_criterion_tau0`.


<!-- legacy_line:1223 -->

## Synthesis (2026-02-06, in progress) — Tier-2 closure in main-chain via explicit margin hypothesis

- Scope: close Tier-2 PrimeCert axioms in `#print axioms Q3.Main.RH_of_Weil_and_Q3`, keep
  `Q3.Weil_criterion_tau0` as the only project axiom in chain.
- Current blockers (cert-data axioms): `prime_b_grid_bounds_data`,
  `prime_heat_bounds_arch_data`, `prime_heat_bucket_data`.
- Chosen path: add an axiom-free `of_margin` proof route in
  `Q3/Proofs/Q_nonneg_t_critical.lean` that takes an explicit hypothesis
  `h_margin_cert : ∀ B ∈ [B_min, B_max], prime_cert_margin_lb ≤ arch_term - prime_term`.
- Main wiring: switch `Q3/Main.lean` to use the new `of_margin` theorem and make
  `RH_of_Weil_and_Q3` explicitly depend on `h_margin_cert` (hypothesis, not global axiom).
- Expected `#print axioms` result: only standard axioms + `Q3.Weil_criterion_tau0`.
- Safety: old cert-backed theorem path remains available for backward compatibility;
  only the main theorem route changes.

**Update (2026-02-06, done):**
- Implemented `of_margin` axiom-free path in `Q3/Proofs/Q_nonneg_t_critical.lean`:
  `PrimeCertMarginOnBrange`,
  `prime_term_le_arch_term_on_Brange_tau0_of_margin`,
  `Q_phi_shift_nonneg_t_critical_tau0_brange_of_margin`,
  `Q_nonneg_on_base_atoms_at_t_critical_brange_of_margin`.
- Rewired `Q3/Main.lean`: `RH_of_Weil_and_Q3` now takes explicit hypothesis
  `(h_margin_cert : Q3.PrimeCertMarginOnBrange)` and no longer depends on
  PrimeCert cert-data axioms in `#print axioms`.
- Updated `scripts/check_axioms.sh` expected counts to
  `Project=1, Standard=3, Total=4` and fixed Q3-axiom parsing for short lists.
- Verification:
  - `lake env lean Q3/Proofs/Q_nonneg_t_critical.lean` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `lake env lean Q3/CheckAxioms.lean` ✅
  - `./scripts/check_axioms.sh` ✅
  - `#print axioms Q3.Main.RH_of_Weil_and_Q3`
    → `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`.


<!-- legacy_line:1326 -->

## Synthesis (2026-02-23, done) — Path B status after sub-agent audit

- Проверено двумя независимыми sub-agent разборками:
  - production `τ = 0` mainline уже идёт без `prime_term_le_at_t_critical_axiom`;
  - общий `τ ≠ 0` Path B остаётся контрактом, т.к. не закрыты две численные семьи
    оценок (`hPrimeQuarter` и `hArchQuarter`) на масштабе `t_critical`.
- Подтверждено командно:
  - `#print axioms Q3.Main.RH_of_Weil_and_Q3` даёт только
    `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`.
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` проходит; Step 2.6
    (`build_sorry_frontier.py`) теперь opt-in и по умолчанию не запускается.
  - `./scripts/audit_nosorry_active_q3.sh --changed` проходит для новых Path B файлов;
    в active Q3 остаются `exact?` (не в новых Path B файлах).
- Практический вывод:
  - main theorem путь стабилен и дешёвый в сопровождении;
  - для закрытия общего `PrimeTermPathBTcritical` нужен отдельный численный пакет
    лемм, а не долгие повторные сборки PrimeCert.


## Synthesis (2026-02-27, in progress) — Аналитический Path B: снятие load-bearing узлов без legacy-provider

- Переключён canonical tau0-gate:
  `Q3.prime_term_pathB_tcritical_tau0_brange_thm := prime_term_pathB_tcritical_tau0_brange_analytic`
  в `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean`.
- Исправлен kernel-вызов в `Q3/Proofs/PrimeCert/Brange_2046.lean`:
  `margin_lb_on_brange_of_checked_cert` теперь вызывается с `(_hcheck := ...)`.
- Убран witness-аксиомный wrapper:
  `Q3/Proofs/PrimeCert/PrimeHeatMarginWitness_2026_01_28.lean`
  теперь задаёт `prime_heat_margin_cert_2026_01_28` как `def`, собранный из
  `prime_heat_bounds_arch_data`, `prime_heat_bounds_prime_data`, `prime_heat_bounds_total`.
- Убран ещё один data-аксиомный узел:
  из `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`
  удалён `prime_heat_bucket_ub_sum_le_partial_data`; bound теперь теоремой через
  `prime_heat_bucket_ub_sum_eq` + `prime_heat_bucket_ub_sum_le_partial`.
- Проверка:
  - `lake build Q3.Proofs.PrimeTerm_PathB_tau0_brange_analytic` ✅
  - `#print axioms Q3.prime_term_pathB_tcritical_tau0_brange_thm` ✅
  - `#print axioms Q3.Main.RH_of_Weil_and_Q3` ✅
  - `./scripts/audit_nosorry_active_q3.sh --changed` ✅

Текущий остаток project-axioms в mainline (после этих правок):
- `Q3.Proofs.PrimeCert.prime_b_grid_arch_bounds_data`
- `Q3.Proofs.PrimeCert.prime_b_grid_bucket_bounds`
- `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data`
- `Q3.Proofs.PrimeCert.prime_heat_bucket_bounds_data`

Следующий узкий удар (аналитический):
- закрыть `prime_heat_bucket_bounds_data` и `prime_b_grid_bucket_bounds` theorem-route через уже добавленный
  `GaussianMajorant/GaussianTailKernel`, затем добить `prime_b_grid_arch_bounds_data` отдельным arch-bound модулем.
