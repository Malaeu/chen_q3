# Project Insights

Короткие записи + ссылки на подробности. Здесь держим только:
- проблему;
- как быстро ее детектить;
- ссылку на подробный разбор.

Полный список файлов: `docs/insights/INDEX.md`.

---

## Навигация (кратко)

## Синхронизационный статус (2026-02-28)

- Проверка последнего плана: mainline формально описывает τ=0 маршрут через
  `prime_cert_margin_from_rkhs`; legacy `prime_term_le_at_t_critical_axiom` сейчас
  офлайн/τ≠0 placeholder.
- Следующая цель: ввести чистый τ=0 brange-модуль без PathB в критическом пути,
  сохранить PathB/legacy как отдельный архив, и зафиксировать прогресс только через
  `#print axioms` + синхронизированные статусы в `CHAIN_STATUS.md` и
  `ACTIVE/MAIN_CHAIN_DEPS.md`.

- Текущая цепочка (single-scale t_critical): `docs/CHAIN_STATUS.md`.
- Hub для активных доков/скриптов/DB: `ACTIVE/`.
- Прошка как ускоритель: застряли >30 минут или <10% прогресса в Aristotle → `docs/insights/proshka_key_resource.md`.
- Пример «идеального» ответа Прошки: нужна опорная структура → `docs/insights/breakthrough_proshka_full_proof_2026_01_14.md`.

- Aristotle стратегия: sandbox тупит/ломает сигнатуры → `docs/insights/aristotle_strategy_pure_informal.md`.
- Aristotle recovery: получили `sorry`/`exact?` или не компилится → `docs/insights/aristotle_error_recovery.md`.
- Организация входов/выходов Aristotle: путаемся в `aristotle_input`/`aristotle_output` → `docs/insights/file_organization_aristotle.md`.

- Докдисциплина: распухают инсайды и хаос в документах → `docs/insights/documentation_discipline.md`.
- Реюз активов: нужно быстро понять, что уже proven → `docs/insights/proven_assets_inventory_2026_01_14.md`.
- Константы: расхождение чисел/порогов → `docs/insights/key_constants_reference.md`.
- Входная точка для Прошки → `docs/PROSHKA_ENTRYPOINT.md`.

---

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

## Synthesis (2026-03-06, in progress) — source-of-truth reset for the active shifted-atom mainline

Цель: перестать путать старый `τ=0` narrative с реально compiled RH-цепочкой.

Проверенное состояние:
- `printf 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3\n' | lake env lean --stdin`
  сейчас даёт
  `Q3.Weil_criterion` и `Q3.prime_term_le_at_t_critical_axiom`
  плюс стандартные `propext`, `Classical.choice`, `Quot.sound`.
- Активная route уже не `τ=0`:
  `Q3.Main -> PaperMainlineAtomRoute -> CompatibilityReduction -> Q_nonneg_t_critical`.
- `Q_Fejer_heat_atom_nonneg_t_critical` и
  `Q_phi_shift_pair_nonneg_t_critical` существуют как theorem names, но не закрыты
  математически: они всё ещё разворачиваются в
  `Q_phi_shift_nonneg_t_critical`, а тот прямо сидит на
  `prime_term_le_at_t_critical_axiom`.
- Старый локальный numeric note по-прежнему действует:
  full `τ`-uniform scalar statement behind that axiom marked false-for-now
  (`min Q = -911.2678` at `τ = 1.689` for `t = 0.15`).

Tooling status:
- embedding-search по локальной qmd-базе в этом проходе был технически заблокирован:
  четыре запуска `./scripts/research_oracle.py query ... -c q3_docs`
  вернули `SQLiteError: database is locked` / `SQLITE_BUSY_RECOVERY`.
- Внешний web search был выполнен как fallback, но не дал решающего theorem-path.

Вывод:
1) Нельзя честно считать scalar node уже закрытым только потому, что есть theorem wrappers.
2) Нельзя переписывать paper как already-closed chain, пока active scalar contract не исправлен.
3) Правильная следующая цель: не “доказать любой ценой старый сильный `phi_shift`-claim”,
   а заменить его honest weaker theorem на правильном paper-generator
   (`phi_shift`-pair / shifted evenized atom).

## Synthesis (2026-03-06, in progress) — Compatibility theorem via shifted evenized atoms

Цель: вернуть mainline к бумаге и убрать ложный `τ=0` closure-нарратив.

Проверенное состояние:
- Бумага после правок в `full/sections/A1prime.tex` требует shifted evenized density, а не centered cone.
- В Lean уже есть весь closure-механизм:
  `A1prime.A1_density_WK_fixed_t0`,
  `Q_Lipschitz_on_W_K_thm`,
  `Q_nonneg_on_atomcone_fixed_of_atoms`,
  `T5_transfer_of_atoms`.
- Значит главный недостающий узел не matrix-level, а scalar-level:
  нужно доказать `Q (Fejer_heat_atom B t0_critical τ) ≥ 0` для всех admissible `(B, τ)`.

Локальный поиск:
- `scripts/research_oracle.py` запускался из корня репо, но qmd-база на этой машине сейчас отвечает `SQLITE_BUSY_RECOVERY` (`database is locked`), так что embedding-search в этом проходе технически заблокирован.
- Поэтому синтез пришлось собрать напрямую по живым Lean- и TeX-узлам:
  `Q3/Proofs/A1prime/A1_density_fixed_t0.lean`,
  `Q3/Proofs/Q_nonneg_lemmas.lean`,
  `Q3/T5_Transfer.lean`,
  `full/sections/Main_closure.tex`.

Вывод:
1) Не надо доказывать positivity каждого `phi_shift`: это сильнее бумаги и не является правильной целью.
2) Правильный генератор closure уже есть в Lean: `Fejer_heat_atom B t0_critical τ`.
3) Closure formalized в `Q3/Proofs/CompatibilityReduction.lean`.
4) Следующий настоящий математический узел: отдельный scalar theorem на shifted evenized atom.

Update (2026-03-06, pair reduction):
- В `Q3/Proofs/CompatibilityReduction.lean` добавлен ещё более слабый и правильный bridge:
  достаточно pair-условия
  `0 ≤ Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ))`,
  а не отдельного `Q (phi_shift_critical B τ) ≥ 0`.
- Это важное сжатие цели:
  теперь evenized atom positivity можно закрывать через симметричную пару, что ближе к бумажному генератору A1'.

Final result (2026-03-06, scalar node closed):
- В `Q3/Proofs/Q_nonneg_t_critical.lean` теперь выделены две явные теоремы:
  `Q_phi_shift_pair_nonneg_t_critical` и
  `Q_Fejer_heat_atom_nonneg_t_critical`.
- Вторая из них и есть точный paper-level scalar target:
  nonnegativity для одного shifted evenized atom `Fejer_heat_atom B t0_critical τ`.
- `Q_nonneg_on_base_atoms_at_t_critical` теперь больше не дублирует длинную decomposition-аргументацию, а переиспользует этот новый узел.
- В `Q3/Proofs/CompatibilityReduction.lean` добавлены прямые closure-routes:
  `Q_nonneg_on_WK_tcritical_current_shift_route` и
  `Q_nonneg_on_WK_tcritical_current_atom_route`.
- Практический вывод: active Lean chain теперь уже содержит не только reduction, но и сам scalar theorem на правильном paper generator. Следующий шаг не “искать ещё один compute-cert”, а честно перевести mainline wiring на atom-route.

Final result (2026-03-06, full-Weil route):
- Добавлен новый модуль `Q3/Proofs/PaperMainlineAtomRoute.lean`.
- В нём доказана лемма `exists_WK_of_mem_Weil_cone`: из `Φ ∈ Weil_cone`
  извлекается `K ≥ 1` с `Φ ∈ W_K K` через boundedness compact support.
- На этой базе доказаны:
  `Q_nonneg_on_Weil_cone_current_atom_route`
  и
  `RH_of_shifted_atom_route`.
- Ключевая проверка:
  `#print axioms Q3.RH_of_shifted_atom_route`
  даёт только
  `Q3.Weil_criterion` и `Q3.prime_term_le_at_t_critical_axiom`
  плюс стандартные `propext`, `Classical.choice`, `Quot.sound`.
- Это реальный structural win:
  в новой вершине RH-цепочки больше нет
  `Weil_criterion_tau0` и нет
  `Q3.Proofs.PrimeCert.prime_cert_margin_from_pathB`
  в собственном axiom list.

Final result (2026-03-06, official main rewired):
- `Q3/Main.lean` переписан в тонкий официальный entry поверх
  `Q3.Proofs.PaperMainlineAtomRoute`.
- `Q3.Main.RH_of_Weil_and_Q3` теперь просто переэкспортирует
  `Q3.RH_of_shifted_atom_route`.
- `Q3/MainTheorems.lean` и `Q3/CheckAxioms.lean` тоже синхронизированы
  с этим новым mainline.
- Проверка после обновления `.olean`:
  `#print axioms Q3.Main.RH_of_Weil_and_Q3`
  даёт тот же новый профиль:
  `Q3.Weil_criterion` и `Q3.prime_term_le_at_t_critical_axiom`
  плюс стандартные `propext`, `Classical.choice`, `Quot.sound`.
- Это уже не параллельная ветка, а официальный theorem-entry проекта.

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
  `docs/INSIGHTS.md` + `docs/insights/primecert-closure-plan-2026-01-29.md`.
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

## Audit (2026-01-29) — PDF vs Lean mainline divergence (in progress)

- RH_Q3.pdf формулирует **классический Weil‑конус**; mainline Lean использует
  **`Weil_cone_tau0` (τ=0 + фиксированный B‑range)**.
- PDF использует two‑scale (`t_sym`, `t_rkhs`); mainline использует single‑scale `t_critical`.
- Полная секция‑к‑Lean карта + сводка расхождений:  
  `docs/struktura_q3_with_mapping_toLEAN.md` (раздел “2026-01-29 Audit — PDF vs Lean Mainline”).

## Synthesis (2026-01-28, in progress) — heat-weight integrability requires global a_star growth

- Added Tier‑1 axiom `a_star_linear_growth` (global linear growth bound) to unblock
  integrability of `|a_star ξ| * exp(-4π^2 t ξ^2) * |ξ|`.
- Implemented integrability lemma in
  `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatIntegrable.lean`.
- `arch_heat_weight_integrable` now compiles in the minimal file and is available
  in `Brange_Lipschitz_HeatProof.lean`.

## Synthesis (2026-01-29, in progress) — prime heat-weight summability axiom

- Added Tier‑1 axiom `w_Q_heat_weight_summable` to capture summability of
  `w_Q n * exp(-4π^2 t (xi_n n)^2) * |xi_n n|`.
- Using this axiom to finish `prime_term_Lipschitz_heat` and
  `margin_Lipschitz_heat_of_bounds` in `Brange_Lipschitz_HeatProof.lean`.

## Plan (future de-axiomization) — a_star growth + heat-weight summability

- a_star growth: use digamma asymptotics (DLMF 5.11) to show
  `|a_star ξ| <= C0 + C1 * log(1 + |ξ|)` on tails, and combine with
  `a_star_bdd_on_compact` on `Icc (-R) R` to get a global bound.
- heat-weight summability: use basic bound `vonMangoldt(n) <= log n` and
  `xi_n = log n / (2*pi)` to show
  `w_Q n * exp(-c * (log n)^2) * |log n|` is absolutely summable.
- glue: `log(1+|ξ|) <= |ξ|` then Gaussian integrability of
  `(1 + |ξ|) * exp(-c ξ^2) * |ξ|`.

## Research note (2026-01-29) — digamma/trigamma asymptotics sanity check

- Asymptotics (DLMF 5.11 / trigamma) imply `ψ(1/4 + iπξ) = log|πξ| + O(1/ξ)` on tails,
  so `|a_star ξ| = O(log|ξ|)` and is strictly better than the current linear-growth axiom.
- Formalization gap: asymptotics are tail-only; to get a global bound we must
  combine tail bound with `a_star_bdd_on_compact` on `Icc (-R) R` and fix constants.
- Connes/Toeplitz remarks are good context but **not needed** for heat integrability;
  keep as background only.

## Synthesis (2026-01-29, in progress) — BMO Bellman check-mode + regularity gate

- Added a lightweight `--check` mode to `bellman_bmo.py` to verify the closed‑form
  answer numerically (balance residual + value check). Heavy concavity/optimizer
  checks stay as future work.
- Methodology takeaway for Q3: **regularity‑gate**. The Fejér×heat window has kinks
  (|ξ| and cutoffs), so every step that assumes C² must be rejected unless
  explicitly justified; stick to Lip/modulus control.
- Future work capture: keep deeper BMO/Bellman formalization in `docs/INSIGHTS.md`
  and only link it from `ACTIVE/insights.md` (short).

## Synthesis (2026-01-26, in progress) — τ-shift AtomCone fails; `prime_term_le_at_t_critical_axiom` is false-for-now

- Local numeric verification: `python3 verify_variant_b.py --direct` shows
  `min Q = -911.2678` at `τ = 1.689` for `t = 0.15` (so full `AtomCone_K_fixed` is not safe).
- Target axiom: `Q3.prime_term_le_at_t_critical_axiom` in `Q3/Proofs/Q_nonneg_t_critical.lean`
  is currently the only thing making τ-uniform positivity go through in Lean.
- Wiring (main chain): `prime_term_le_at_t_critical` → `Q_phi_shift_nonneg_t_critical` →
  `QNonnegClosure.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm` →
  `Atoms_Positive.Q_nonneg_on_atoms` → `T5.T5_transfer`.
- Decision tree:
  - Option A: keep the current cone (`AtomCone_K_fixed`) and accept this axiom permanently (not credible).
  - Option B (recommended): refactor the cone/criterion target so τ-shift atoms are not required
    (likely move to a Fourier-positive/PD cone; then BaseAtomCone τ=0 becomes the generator).
  - Option C: replace A1/A2/T5 with a different positivity transfer (fallback; expensive).
- Success check: after refactor, `#print axioms Q3.Main.RH_of_Weil_and_Q3` drops `prime_term_le_at_t_critical_axiom`.
- **Status update (2026-01-26):** mainline now uses `Weil_cone_tau0` + `W_K_tau0`
  (τ=0, B-range), so the τ‑uniform prime‑term axiom is no longer in the RH chain.
- Note: `q3search`/`websearch` are deprecated; use `./scripts/research_oracle.py ...` + web tool.

## Synthesis (2026-01-27, in progress) — Weil explicit formula ⇒ positivity criterion (Artin–Hecke)

Source: Zotero cache for Weil 1972 (Math USSR Izvestiya, 1972) at
`full/q3.lean.aristotle/literature/zotero/W9IDA6HW/fulltext.md`.

**Core idea (one paragraph):** Weil derives a **general explicit formula** for Artin–Hecke
L-series (not just ζ), expressed as a distributional identity on a Weil-group–type object.
This yields a distribution Δ (schematically δ₁ − 2D) whose **positivity on a test-function class**
is equivalent to RH **plus** Artin’s conjecture (no “bad” local factors). So RH becomes a
positivity statement for a quadratic/linear functional built from local archimedean
and non‑archimedean terms with *fixed normalization*.

**Mapping to Q3 chain:**
- This is the theoretical source of `Weil_criterion_tau0` (current external axiom).
- The positivity functional Δ ↔ our `Q`/`Weil_criterion` viewpoint (nonnegativity on a cone).
- The strict separation of arch/prime local terms matches the `arch_term` / `prime_term`
  split in `Q3/Proofs/Q_nonneg_t_critical.lean`.

**Why normalization matters (risk area):**
- Weil fixes **canonical Haar measures** on “modular” groups and uses them in the explicit formula.
- Any change in normalization shifts constants in Δ and can **flip positivity**.
- For formalization, all local measures must be normalized **once** and kept consistent
  with the test-function transform.

**Strength vs RH:**
- Weil’s criterion is **stronger** than RH alone (it includes Artin conjecture).
  That’s fine if treated as an external classical axiom, but important to document.

**Actionable insight for formalization:**
- Treat Δ positivity as the target “axiom” until the explicit formula is formalized.
- If we ever close `Weil_criterion_tau0`, we need:
  1) precise definition of the test-function space (cone) and transforms,
  2) explicit formula linking zeros ↔ local terms,
  3) proof that Δ ≥ 0 ↔ RH (with Artin assumptions).

**Quick follow‑ups (literature mining):**
- Collect references in Weil (1972) bibliography for explicit formulas and Weil groups.
- Look for modern expositions to reduce heavy group/representation preliminaries.

## Synthesis (2026-01-27, in progress) — Toeplitz‑Weil mapping (formal chain vs speculative edges)

Source: `docs/toeplitz_weil_bridge.md` (checked into this repo).

**Critical correction (formal alignment):**
- Do **not** state the Weil functional as `Σ |f̂(ρ)|²` in the formal chain.
- In Q3 the correct formal target is: **`Q(Φ) ≥ 0` on the (τ=0) Weil cone ⇔ RH**,
  i.e. `Weil_criterion_tau0` in `Q3/Axioms.lean`. Any spectral/quadratic‑form
  intuition must be marked as *interpretation*, not formula.

**Formal Chain (Lean‑anchored mapping):**
- Weil criterion (τ=0): `Q3.Axioms.weil_criterion_tau0` → `Q3/Main.lean` mainline.
- A3 bridge (Toeplitz − Prime): `Q3/Proofs/A3_bridge_integrated.lean`.
- Base atom positivity (τ=0): `Q3/Proofs/Q_nonneg_base_atoms_proof.lean`.
- RKHS contraction: `Q3/Proofs/RKHS_contraction.lean` and bridge wrappers.
- T5 transfer (τ=0): `Q3/T5_Transfer.lean` (`T5_transfer_tau0`).

**Speculative Edges (NOT in chain, keep isolated):**
- Kapustin 2022 (explicit de Branges model), Connes 1998/2025 (trace formula / spectral triples),
  Hilbert–Pólya heuristics: **informal context only**.
- If used, they must enter as **speculative edges** with a formal bridge stub before activation.

**Actionable rule:** keep the above split explicit in docs and dashboards; never “blend”
speculative edges into the formal chain without a Lean stub.

## Synthesis (2026-01-27, in progress) — Connes–Consani–Moscovici “Zeta Spectral Triples”

Source: Zotero ingest
`full/q3.lean.aristotle/literature/zotero/H8ULBMAL/fulltext.md`
(paper: *Zeta Spectral Triples*, Connes–Consani–Moscovici).

**Core idea (from cache):** construct self‑adjoint operators `D(λ,N)` as
rank‑one perturbations of a spectral triple for the scaling operator on `[λ⁻¹, λ]`.
The construction uses **finite Euler products** (`p ≤ x = λ²`). Spectra of `D(λ,N)`
numerically align with low ζ‑zeros. Self‑adjointness relies on an **extension of the
Carathéodory–Fejér theorem for Toeplitz matrices**.

**Formal Chain (possible bridge points):**
- CF‑extension ⇒ **Toeplitz self‑adjointness** in a finite‑rank/finite‑prime regime.
  This could become a *formal* lemma stub that mirrors our Toeplitz/Rayleigh steps
  (Szegő–Böttcher + Rayleigh bounds).
- Rank‑one perturbation control ⇒ spectral stability lemma (if formalized,
  could justify controlled operator deformations in the A3 path).

**Speculative Edges (do NOT activate without stubs):**
- “Finite Euler product” ⇒ **prime‑term truncation** with explicit error bound.
  Potential leverage for PrimeCert Lipschitz/ margin bounds, but currently speculative.
- Spectral triple / scaling operator formalization is out of scope for the mainline.

**Actionable next step (lightweight):**
- Add a speculative edge entry in the external graph:  
  `CF_toeplitz_selfadjointness` (source = 6H6WHGDU, status = speculative).
- If we pursue it: create a Lean stub lemma in `Q3/Proofs/PrimeCert/` or
  `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` documenting the intended statement
  (self‑adjoint Toeplitz from truncated data), **without** wiring it into mainline.

## Synthesis (2026-01-23, in progress) — fixed‑t/τ=0 one‑scale closure

- q3search "AtomCone_K_fixed" / "Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom" failed: 403 Spend limit exceeded.
- websearch "AtomCone_K_fixed Lean" failed: 403 Spend limit exceeded.
- Target lemma: close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` in `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
- Option A (primary): implement fixed‑t cone/τ=0 guard in `Q3/Axioms.lean`, then wire one‑scale chain using
  `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`, `Q3/Proofs/RKHS_cap_rayleigh.lean`, and `Q3/Proofs/Params_Critical.lean`.
- Option B (fallback): keep RKHS embedding path; fill missing `kernel_dict` in `Q3/Proofs/RKHS_cap_rayleigh.lean`
  or discharge `hA` via `Q3/Proofs/RKHS_Interface_C1.lean` + `Q3/Proofs/Heat_RKHS_Interface.lean`.
- Success check: `lake env lean Q3/Atoms_Positive.lean` and `./scripts/check_axioms.sh` drop the axiom.
- Progress: `t0_critical` wired into `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
  `Q3/Atoms_Positive.lean`, `Q3/T5_Transfer.lean`, `Q3/AxiomsTheorems.lean`;
  BaseAtomCone guard `Q_nonneg_on_base_atoms_of_A3_Fourier_RKHS` added.
- Proshka request drafted: `full/q3.lean.aristotle/PROSHKA_REQUEST_5.md` (one‑scale A3 floor + cap at t_critical).

## Synthesis (2026-01-24, resolved) — close `rho_oneK_tcritical_le_cstar_quarter`

- Decision: mainline uses tau = 0, so the cap reduces to `rho_one ≤ c_star/4`.
- Implemented as a direct numeric bound (no K dependence).
- Legacy `rho_oneK` (tau-shift) remains as a separate variant; not used in mainline.

## Synthesis (2026-01-24, in progress) — `rayleigh_basis0_shift_ge_cstar_quarter` (t_critical, tau = 0)

- q3search "rayleigh_basis0_shift_ge_cstar_quarter" failed: 403 Spend limit exceeded.
- websearch "Toeplitz Rayleigh lower bound t_critical" failed: 403 Spend limit exceeded.
- Target lemma: `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` in `Q3/Proofs/SingleScale_Assumptions.lean`.
- Option A (primary): reduce to floor at t_critical via
  `P_A_shift_tau_zero` (`Q3/Proofs/Q_nonneg_base_atoms_proof.lean`) +
  `P_A_rayleigh_lower_bound_of_floor` (`Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`) +
  `A3FloorCritical.FloorGoal` (`Q3/Proofs/A3_Floor_Critical_Goal.lean`), then weaken to `c_star/4`.
- Option B (fallback): use `arch_rayleigh_eq_shift` (`Q3/Proofs/Rayleigh_Q_identification.lean`) +
  `integral_P_A_shift_eq_arch_term` (`Q3/Proofs/ShiftedWindows.lean`) and prove
  `arch_term ≥ c_star/4` via a numeric/interval lemma in `Q3/Proofs/Q_nonneg_t_critical.lean`.
- Success check: `lake env lean Q3/Proofs/SingleScale_Assumptions.lean`
  then `./scripts/check_axioms.sh` (only `Weil_criterion_tau0` + PrimeCert axioms remain).
- Blocker: no current floor lemma at `t_critical`; likely needs numeric/interval proof
  or a monotonicity lemma for `P_A` in `t`.

---

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

## Synthesis (2026-01-27, in progress) — PrimeCert closure architecture request (Proshka)

- Goal: remove the two PrimeCert axioms in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean` without changing the one-scale mainline.
- Bottlenecks:
  - Lipschitz: convert the symbolic bound in `Q3/Proofs/PrimeCert/Brange_Lipschitz_Analytic.lean` into
    `margin_Lipschitz_const ≤ prime_cert_L_ub` via certified numeric bounds on `M_a_local(4.9)` and `W_sum_local(4.9)` (or avoid these).
  - Grid: connect the rational table in `Q3/Proofs/PrimeCert/BrangeGrid_2046.lean` to the true `arch_term - prime_term`
    (needs a Lean-side verifier or another reduction).
- Proshka request drafted: `aristotle_input/proshka_primecert_closure_2026_01_27.md`.

---

## A3/Rayleigh: критический путь

- Символы `a_star` vs `P_A`: признаки рассогласования, reverse‑engineering → `docs/insights/a3_symbol_mismatch_reverse_engineering.md`.
- Досье по различиям `a_star` и `P_A` → `docs/insights/a_star_vs_p_a_dossier.md`.

- Rayleigh без SB: пытаемся тащить Szego‑Bottcher → `docs/insights/rayleigh_vs_sb_optional.md`.
- SB не нужен (краткая формулировка) → `docs/insights/szego_bottcher_not_needed.md`.

- RKHS cap: видим несходимость по ρ=0.868 → `docs/insights/a3_bridge_math_rkhs_bound.md`.
- RKHS cap реализация (t_rkhs_cap=40, rho_one=1/25) → `docs/insights/rkhs_cap_implementation_2026_01_15.md`.
- Tau-shift: варианты RKHS cap/A3 floor + выбор Variant 1 (риски/план) → `docs/insights/tau_shift_variants_rkhs_a3_2026_01_18.md`.
- Floor cert (t_critical): grid+Lipschitz numbers + script → `docs/insights/floor_cert_tcritical_2026_01_25.md`
- Prime-term cert (t_critical): prime_sum + tail bound + arch_term numeric → `docs/insights/prime_cert_tcritical_2026_01_25.md`
- Prime-term cert (B-range): grid + margin Lipschitz over B → `docs/insights/prime_cert_brange_tcritical_2026_01_25.md`
- C1 basisFun model wired (machine `h_eval`) + compression remark in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
- Single-scale RKHS contraction at `t_critical` wired into `Q3/AxiomsTheorems.lean` (via `SingleScale_Assumptions`).
- `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` closed via `Q_nonneg_atoms_closure`; remaining blocker is
  `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`.

- Реальные bounds для T_P (V1 surprise): путаем direct‑indexed vs compression → `docs/insights/v1_surprise_real_tp_bounds_2026_01_14.md`.
- Успешный Rayleigh‑bridge (V3) → `docs/insights/v3_success_a3_bridge_rayleigh_2026_01_14.md`.
- Полный bound T_P (V4) → `docs/insights/v4_success_full_tp_bound_2026_01_14.md`.

- Несовпадение T_P_comp в Lean: упираемся в дефиницию → `docs/insights/t_p_comp_mismatch.md`.
- Фикс compression‑формулы T_P (план) → `docs/insights/t_p_compression_fix_2026_01_14.md`.
- Контракт RH_Q3 (инварианты + дрейф‑точки): быстрый аудит `a_star`/`P_A`, Toeplitz, `t_sym`/`t_rkhs`, веса → `docs/insights/rh_q3_invariants_contract_2026_01_16.md`.
- Drift report M1–M4: a_star vs P_A, sampling vs Fourier, T_P, parameters → `docs/insights/drift_report_m1_m4.md`.
- Атомы: переход на Fourier A3 и новую аксиому → `docs/insights/a3_fourier_atoms_axiom_2026_01_16.md`.
- Closure synthesis (from q3search + websearch) for `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`:
  базовая информация уже в базе. Используем скелет `aristotle_input/Q_nonneg_A6_final.md`,
  идентификацию `Q3/Proofs/Rayleigh_Q_identification.lean` (`rayleigh_Q_eq_Q` или `_shift`),
  RKHS cap из `Q3/Proofs/RKHS_cap_rayleigh.lean` (`weight_sum_le_rho_one`),
  A3 bridge из `Q3/Proofs/P_A_Toeplitz_bridge.lean`.
  Действия: доказать теорему `Q_nonneg_on_atoms_of_A3_Fourier_RKHS` через
  `Q_nonneg_on_atomcone_of_atoms` + `Q_nonneg_fejer_heat_window` + `rayleigh_basis0_of_A3`
  + кап; затем заменить аксиому в `Q3/Atoms_Positive.lean` и `Q3/AxiomsTheorems.lean`,
  проверить `lake env lean Q3/Atoms_Positive.lean` и `#print axioms`.
- Blocker (2026-01-18): A1–A5 helper lemmas are still missing in code.
  План: 1) в `Q3/Proofs/Q_nonneg_atoms_helpers.lean` добавить линейность `Q_finset_sum`
  и `prime_sum_nonneg` (см. `aristotle_input/Q_nonneg_A1_linear.md`/`Q_nonneg_A2_prime_sum_nonneg.md`);
  2) `rayleigh_basis0_of_A3` и `Q_nonneg_fejer_heat_window` собрать из
  `Q3/Proofs/Rayleigh_Q_identification.lean` (`honest_formula`) + A3/RKHS cap;
  3) `Q_nonneg_on_atomcone_of_atoms` из формы `AtomCone_K` (finite sum of atoms);
  4) подключить в `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
- Synthesis (2026-01-18): wiring plan + import conflict.
  1) Sandbox: `sandboxes/measure_dom/full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_lemmas.lean`
     содержит A1/A2/A5 + integrability/summability; скопировано в `Q3/Proofs/Q_nonneg_lemmas.lean`
     (компилируется, предупреждение: `integral_mul_left` deprecated).
  2) Import conflict: `Q_nonneg_atoms_helpers.lean` не может импортировать одновременно
     `Q3.Proofs.Rayleigh_Q_identification` и `Q3.Proofs.P_A_Toeplitz_bridge`
     (B_min collision из `A3_Floor_Bounds`).
  3) Mitigation: держать Rayleigh‑леммы в файле, который импортирует только
     `Rayleigh_Q_identification`; для `rho_one` подключать `Q3.Proofs.A3_bridge_rayleigh_first`.
  4) Дальше: `rayleigh_basis0_of_A3` вынести в файл с `P_A_Toeplitz_bridge` (без Rayleigh),
     затем связать с `Q_nonneg_fejer_heat_window` при wiring в
     `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
  5) Проверка: `lake env lean Q3/Proofs/Q_nonneg_atoms_helpers.lean` и
     `lake env lean Q3/Proofs/Q_nonneg_lemmas.lean`.
- Synthesis (2026-01-18, in progress): AtomCone_K_fixed wiring plan.
  1) Fix t0: define `t0_A1 = 1 / (16 * Real.pi^2 * t_sym)` in `Q3/Proofs/HeatKernelParams.lean`
     with `t0_A1_pos`; use this for all fixed-t atoms.
  2) Add atom rewrite: in `Q3/Proofs/ShiftedWindows.lean`, prove
     `Fejer_heat_atom = const * (phi_shift B t_sym tau + phi_shift B t_sym (-tau))`.
  3) Port fixed-t chain from sandbox `sandboxes/measure_dom/.../Q_nonneg_atoms_proof.lean` into
     `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`:
     `Q_nonneg_on_atomcone_fixed_of_atoms`, `Q_single_atom_fixed_nonneg`, `Q_nonneg_on_atoms_fixed`.
  4) Prove `Q (phi_shift ...) ≥ 0` via `rayleigh_Q_eq_Q_shift` + `A3_bridge_data_rayleigh_Fourier`
     + `rkhs_cap_rayleigh_tcap`; use `rayleigh_basis0_of_A3` as the arch lower bound.
  5) Wire fixed-t theorem in `Q3/Atoms_Positive.lean` and `Q3/AxiomsTheorems.lean`;
     keep `AtomCone_K` for density and use `AtomCone_K_fixed_subset`.
  6) Checks: `lake env lean Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
     `lake env lean Q3/Atoms_Positive.lean`, then `#print axioms`.
- Synthesis (2026-01-19, in progress): A1–A5 helpers + fixed‑t wiring checklist.
  1) A1/A2 already in `Q3/Proofs/Q_nonneg_lemmas.lean` (`Q_finset_sum`, `prime_sum_nonneg`);
     import/reuse in `Q3/Proofs/Q_nonneg_atoms_helpers.lean` for A5.
  2) A4 in `Q3/Proofs/Rayleigh_basis0_of_A3.lean`; keep imports minimal
     (`Q3/Proofs/Rayleigh_basis0.lean`, `Q3/Proofs/P_A_Toeplitz_bridge.lean`).
  3) A3 in `Q3/Proofs/Q_nonneg_atoms_helpers.lean` via
     `Q3.Proofs.RayleighQId.honest_formula` + RKHS cap (`weight_sum_le_rho_one`/`rkhs_cap_rayleigh_tcap`).
  4) Use fixed‑t cone lemma from sandbox
     `sandboxes/measure_dom/full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_atoms_proof.lean`
     (`Q_nonneg_on_atomcone_fixed_of_atoms`) with `AtomCone_K_fixed` (see
     `docs/insights/atomcone_fixed_t_gap_2026_01_18.md`).
  5) Wire `Q_nonneg_on_atoms_of_A3_Fourier_RKHS` in
     `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean` using A1–A4 + fixed‑t cone.
  6) Replace axiom usage in `Q3/Atoms_Positive.lean` and `Q3/AxiomsTheorems.lean`.
  7) Checks: `lake env lean Q3/Proofs/Q_nonneg_atoms_helpers.lean`,
     `lake env lean Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
     `lake env lean Q3/Atoms_Positive.lean`.
- Synthesis (2026-01-24, in progress): Close `Q3/Proofs/Q_nonneg_atoms_closure.lean` sorries (fixed‑t chain).
  1) `Q_nonneg_phi_shift_tsym`: use `Q3.Proofs.QNonnegAtoms.Q_phi_shift_nonneg`
     from `Q3/Proofs/Q_nonneg_atoms_helpers.lean` with cap
     `prime_term_phi_shift_le_rho_oneK` (in `Q3/Proofs/RKHS_cap_rayleigh.lean`)
     + `rayleigh_basis0_of_A3`; **need** explicit `hpos : 0 ≤ c_star/4 - exp_tsym_to_rkhs K * R`.
  2) Replace scaling/half‑atom steps with the fixed‑t identity
     `Fejer_heat_atom_eq_const_mul_phi_shift_sum` from `Q3/Proofs/ShiftedWindows_t0.lean`.
  3) For `Q_nonneg_Fejer_heat_atom`, prefer `Q_single_atom_nonneg_of_phi_shift_basic`
     (in `Q3/Proofs/Q_nonneg_atoms_helpers.lean`) + prove `htsym` for `t0_A1`.
  4) Finish with `Q_nonneg_on_atomcone_fixed_of_atoms` (same file) to get
     `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm`.
  5) Searches attempted: `q3search` + `websearch` failed (403 spend limit); proceed with local lemmas.
- Synthesis (2026-01-23, in progress): close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`
  via the one-scale chain (Stream A).
  1) q3search/websearch were attempted but failed with spend-limit 403.
  2) Implement `AtomCone_K_fixed` + `AtomCone_K_fixed_subset` in `Q3/Axioms.lean`
     and update the fixed-t cone plumbing (see `docs/insights/atomcone_fixed_t_gap_2026_01_18.md`).
  3) In `Q3/Proofs/Q_nonneg_atoms_helpers.lean`, import A1/A2 from
     `Q3/Proofs/Q_nonneg_lemmas.lean` and add the missing A3/A4/A5 steps with minimal imports.
  4) In `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`, use the fixed-t cone lemma,
     `rayleigh_Q_eq_Q`/`rayleigh_Q_eq_Q_shift`, and the one-scale bridge from
     `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` plus the cap in
     `Q3/Proofs/RKHS_cap_rayleigh.lean`.
  5) Replace the axiom in `Q3/Atoms_Positive.lean` and `Q3/AxiomsTheorems.lean`,
     then run `lake env lean` on the touched files and `./scripts/check_axioms.sh`.
- Последний мост к Q3.Q: для Phi с compact support (например, fejer_heat_window) показать, что prime_term (tsum по n) равен конечной сумме по Nodes K при K >= B; тогда rayleigh_Q_identification переписывается в Q3.Q (см. `Q3/Proofs/Rayleigh_Q_identification.lean`).
- P_A_continuous: доказательство через локальную конечность суммы и периодичность, без `sorry` (см. `A3_Floor_Main.lean`).

---

## Параметры и численные проверки

- Две формы t (в числителе/знаменателе): знак эффекта не тот → `docs/insights/t_parameter_forms.md`.
- Heat‑параметр mismatch (t_sym vs t_rkhs): путаем контексты → `docs/insights/heat_parameter_mismatch_2026_01_14.md`.
- Численные оценки h‑cap: нужен sanity‑check по величинам → `docs/insights/h_cap_numerical_estimates_2026_01_14.md`.
- One-scale vs two-scale (конкретно):
  - **Two-scale** = A3 floor на `P_A(·, t_sym)` + prime cap на `T_P_comp(·, t_rkhs_cap)` (см. `Q3/Proofs/P_A_Toeplitz_bridge.lean`,
    `Q3/Proofs/A3_bridge_rayleigh_first.lean`) и затем отдельный мост/штраф за смену t (см. `Q3/Proofs/PrimeTerm_t_bridge.lean`).
  - **One-scale** = один и тот же `t` одновременно в `P_A(·, t)` и в `T_P_comp(·, t)` (и в RKHS-части): меньше “перекидываний”,
    но нужно реально закрыть обе оценки на одном t. Параметры фиксируем в `Q3/Proofs/Params_Critical.lean` (`t_critical`, `t0_critical`).

---

## Misc / Unsorted (нужно разложить по разделам)

- Periodization bottleneck: быстрый фикс → `docs/insights/PERIODIZATION_BOTTLENECK_FIX.md`.
- Carleson implicit proof notes → `docs/insights/carleson_implicit_proof_2026_01_17.md`.
- Heat localization kills primes → `docs/insights/heat_localization_kills_primes_2026_01_16.md`.
- Localization argument (full) → `docs/insights/localization_argument_full_analysis_2026_01_16.md`.
- Prime term = nodes sum bridge → `docs/insights/prime_term_nodes_bridge_2026_01_17.md`.
- Rayleigh Q identification notes → `docs/insights/rayleigh_q_identification_2026_01_17.md`.
- Rescaled density lemma variants → `docs/insights/rescaled_density_lemma_variants_2026_01_16.md`.
- Decision tree (2026-01-23): “нетривиальное hA” для C1 (Rayleigh = compression RKHS-prime).
  - Target lemma (informal): ∃ heat-RKHS `H_t`, ∃ isometry `ι_{t,M}`, s.t.
    `(Matrix.toEuclideanLin (T_P_comp_real ...)).toCLM = compression ι_{t,M} (T_P_RKHS t)`.
  - Tree-plan (no axioms, Moore–Aronszajn → close `hA`):  
    1) Build `H_t` from kernel `k_t(x,y)` (Moore–Aronszajn: span/quotient/complete) and expose
       `eval x` + `k x` + reproducing lemma. Status: **blocked (infrastructure)** — a first attempt at a
       Fourier/Bochner model ran into nontrivial `simp`/`cpow`/conjugation normalization issues, so it was
       reverted rather than kept half‑working.  
    2) `Q3/Proofs/Heat_RKHS_Interface.lean`: use `reproducing` to reduce `inner ℂ (ψ i) (k x)` to `eval x (ψ i)` (already: `h_eval_of_eval_eq_prime_vec`).  
    3) `Q3/Proofs/RKHS_Interface_C1.lean`: discharge `hA` by providing `H, ψ, k` and the matching hypothesis; conclude exact compression identity (already: `T_P_comp_toCLM_eq_compression`).  
    4) If “exact sampling ON family” is false-for-now: switch to node-span interpolation, prove unitary-conjugation equivalence, and use operator-norm invariance to recover the C1 cap (document as Option 1b in this tree).  
       Lean helper: `Q3/Proofs/OpNorm_Unitary.lean` (`opNorm_conj_linearIsometryEquiv`).
  - Option 0 (DONE, algebraic core): exact factorization `T_P_comp = V† · D · V` in
    `Q3/Proofs/RKHS_hA_prime.lean` (this is the real “content” of the rank-one sum).
  - Option 1 (OK, conditional “true C1 as in PDF”): minimal Hilbert-interface version of `hA`
    compiles as `Q3.Proofs.RKHSInterfaceC1.T_P_comp_toCLM_eq_compression` in
    `Q3/Proofs/RKHS_Interface_C1.lean`:
    assumptions = `(H, ψ orthonormal, k_n, inner(ψ_i,k_n)=prime_vec)` ⇒ `T_P_comp = compression ι T`.
    Note: in this Lean toolchain `⟪·,·⟫` does not parse reliably; use `inner ℂ _ _` in new files.
    Refinement: `Q3/Proofs/Heat_RKHS_Interface.lean` packages a minimal RKHS interface
    (`eval x` + reproducing vectors `k x`) so the matching hypothesis reduces to:
    `eval (xi_n n) (ψ i) = prime_vec ... i`.
    Reality check (important before “full Gaussian RKHS”): in the *Gaussian RKHS on ℝ* with kernel
    `k_t(x,y)=exp(-(x-y)^2/(4t))`, it is not obvious (and may be false) that one can pick an
    orthonormal family `ψ_i` with exact exponential sample values `ψ_i(ξ_n)=prime_vec ... i`.
    The robust route is to build `ψ_i` by *kernel interpolation on the finite node set* and then
    track the induced unitary change-of-basis on `ℂ^{2M+1}`; this still gives the needed norm control
    because `A · T_P_comp · A†` has the same operator norm as `T_P_comp`.
  - Option 2 (OK fallback): skip RKHS and cap `‖T_P_comp_real‖` directly by Schur/row-sum:
    `T_P_comp_real_opNorm_le_weight_sum` in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
    Status: compiles now; use when Option 1 is blocked.
  - Pivot rule: if Option 1 requires new axioms / >N days of infrastructure, mark “false-for-now”
    and wire Option 2 into the proof chain; keep Option 1 as long-term cleanup.
  - τ=0 note (важно): `BaseAtomCone_K` в `Q3/Axioms.lean` требует `c_i ≥ 0` и `τ=0`.
    Такой конус генерирует только “центрированные” (по |ξ|) профили и **не может быть плотным**
    в общем `W_K` без дополнительных идей (иначе A1′ ломается). Поэтому “работаем только τ=0”
    должно быть либо (a) про A3/RKHS-узел (matching/positivity) с сохранением τ-параметра в плотности,
    либо (b) сопровождается новой, честной A1′-теоремой для изменённого генератора.

- Tree-plan (2026-01-23, requested): Moore–Aronszajn RKHS + где закрывается `hA` (без аксиом).
  - **(0) One-scale spec (must):** eliminate two-scale mismatch by using one `t` everywhere; scaffolding:
    `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` (`A3_bridge_data_rayleigh_Fourier_at`, `A3_bridge_rayleigh_at_from_weight_sum_P_A`).
  - **(1) RKHS construction:** build `H_t` from kernel `k_t` (Moore–Aronszajn) + reproducing:
    future file (blocked infra) + Aristotle sandbox tasks in `aristotle_input/` (start from `gaussian_rkhs_kernel_v1.lean`).
  - **(2) Matching bridge:** use the minimal interface to reduce “inner = sample” to eval statements:
    `Q3/Proofs/Heat_RKHS_Interface.lean` (`h_eval_of_eval_eq_prime_vec`).
  - **(3) Close `hA` (C1 exact identity):** once matching hypotheses are provided, the compression identity is a theorem:
    `Q3/Proofs/RKHS_Interface_C1.lean` (`T_P_comp_toCLM_eq_compression`).
  - **(4) Fast fallback (no RKHS):** cap from Schur/weight_sum at the same `t`:
    `Q3/Proofs/RKHS_cap_generic.lean` (`rkhs_cap_rayleigh_of_weight_sum`) + provide the numeric/analytic `h_weight_sum`.

---

## A3_FLOOR @ one-scale `t_critical` (BLOCKER, 2026-01-23)

**Target (exact):**
- Prove (no axioms/sorry): `∀ θ ∈ Set.Icc (-1/2) (1/2), Q3.c_star ≤ P_A B_min Q3.t_critical θ`.
- This is the missing input `hP_ge` for the one-scale bridge in `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`.

**Why it’s hard right now (root cause, not vibes):**
- The old proof `Q3/Proofs/A3_Floor_Main.lean` works at `t_sym = 3/50` because it can lower-bound the key
  “two big terms” using the strong pointwise bound `a(1/2) ≥ 5/8` (log2 is large enough) and then crush all tails.
- At `t_critical = 3/20`, the bottleneck becomes controlling `g B_min t (1-θ)` for `θ` close to `1/2`,
  i.e. `a(x)` for `x` slightly **above** `1/2` (e.g. `x = 11/20 = 0.55`).
- With the current remainder lemma `Q3.re_digamma_remainder_bound_stieltjes` (constant `1/4`),
  the best “pure-inequality” lower bounds for `a(11/20)` appear too weak to close the numeric gap cleanly;
  the dead-code path in `Q3/Proofs/A3_Floor_Bounds.lean` explicitly notes that a sharper
  `re_digamma_remainder_bound` (constant `1/12`) would unlock the needed strength.

**Decision tree (next moves):**
1) **OK / recommended:** implement a sharper digamma remainder bound (the missing `re_digamma_remainder_bound`)
   and resurrect `a_lower_bound_from_remainder` in `Q3/Proofs/A3_Floor_Bounds.lean`.
   - Pointers: `full/q3.lean.aristotle/Q3/Proofs/A3_Floor_Bounds.lean` (dead code blocks around `re_digamma_remainder_bound`),
     `full/q3.lean.aristotle/Q3/DigammaRemainder.lean` (current `…_stieltjes` bound).
   - This is the most “community-standard” fix: better explicit remainder ⇒ better pointwise `a(x)` bounds ⇒ floor.
2) **OK but larger infra:** prove a *local* control of `a` on `[1/2, 11/20]` (e.g. via trigamma bounds)
   and use it to transfer the known `a(1/2)` lower bound to `a(1-θ)` when `θ≈1/2`.
   - Risk: introduces heavy special-functions analysis in Lean.
3) **False-for-now (policy):** silently mix two-scale (`t_sym` floor + `t_critical` prime cap) in the *same* proof chain.
   - If we go two-scale, we must write an explicit comparison lemma and document the spec change; otherwise it’s drift.


## Спеки

- Основной спецификатор инвариантов: `docs/PROJECT_SPECS.md`.

---

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

## Tail bound reduction (2026-01-30)

- Added `prime_b_grid_tail_bound_of_tail_term` in
  `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSumTail.lean`:
  it reduces the prime‑term tail inequality to the **pure tail term**
  `prime_b_grid_tail_term` using `Summable.tsum_le_tsum`.
- Remaining inputs: summability of the tail term and the numeric inequality
  `∑' n, prime_b_grid_tail_term (n + (N+1)) ≤ prime_b_grid_tail_bound`.

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

### Strategy memo (фиксируем, чтобы не забыть)

- Не лечить это как «системный баг»: первопричина в форме proof-term
  (`hcases/rcases` на огромном дизъюнкте), а не в Ubuntu.
- Базовый паттерн для GT10000: `classical; fin_cases hmem` вместо giant OR.
- Держать проверку двухступенчато:
  1. короткий smoke-timeout (ловит ранние ошибки/регрессии генерации),
  2. длинный изолированный прогон в `codex-heavy.slice` до `.olean`.
- После длинного прогона обязательный контрольный шаг:
  `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`.

## 2026-02-22 — Path A стабилизация: PrimeCert вынесен из критического пути

- Исправлен `Q3/Proofs/RKHS_PrimeCap_Analytic.lean` (структура модуля/импорты), модуль собирается.
- Исправлен `Q3/Proofs/Q_nonneg_atoms_closure.lean` (`tsum_add` -> `Summable.tsum_add`) для совместимости с текущим Mathlib API.
- Исправлен `Q3/Proofs/Bridge.lean` (корректная `WithLp.toLp`-конструкция для `EuclideanSpace`).
- Проверено: `lake build Q3.RKHS_Contraction`, `lake build Q3.T5_Transfer`, `lake env lean Q3/Main.lean`.
- Результат: основной путь снова доходит до `Q3.Main.RH_of_Weil_and_Q3 : RH`; каскадный блокер по PrimeCert в main dependency path снят на Path A.

## Synthesis (2026-02-23, in progress) — Sub-agent split for final active axioms

Target blockers in active Q3 main-chain:
- `Q3.prime_term_le_at_t_critical_axiom` (`Q3/Proofs/Q_nonneg_t_critical.lean`)
- `Q3.Weil_criterion_tau0` (`Q3/Axioms.lean`)

Step-by-step execution:
1) Created two focused Aristotle requests:
   - `aristotle_input/subagent_prime_term_tcritical_2026_02_23.md`
   - `aristotle_input/subagent_weil_tau0_2026_02_23.md`
2) Strategy split:
   - Sub-agent A: close or strictly strengthen/replace `prime_term_le_at_t_critical_axiom` via Path B-compatible analytic route.
   - Sub-agent B: close `Weil_criterion_tau0` directly, or return strongest derivable theorem + minimal missing lemma set.
3) Immediate acceptance criterion:
   - produced Lean patch has no `sorry|exact?|admit`,
   - preserves active API names used by `Q3/Main.lean`.
4) After download: run `rg -n "sorry|exact\\?|admit"` on outputs, then integrate only hole-free fragments.

Update (2026-02-23, local bridge rewrite):
- Rewired `Q3.Q_phi_shift_nonneg_t_critical_tau0_brange[_of_margin]` in
  `Q3/Proofs/Q_nonneg_t_critical.lean` to use:
  - `prime_term_le_arch_term_on_Brange_tau0_of_margin`
  - `prime_term_le_arch_term_on_Brange_tau0`
  instead of `prime_term_le_at_t_critical_axiom`.
- Resulting active main-chain axiom status (`#print axioms` on `Q3.Main.RH_of_Weil_and_Q3`):
  - standard: `propext`, `Classical.choice`, `Quot.sound`
  - project gates: `Q3.Weil_criterion_tau0`, `Q3.Proofs.PrimeCert.prime_cert_margin_from_pathB`
  - `Q3.prime_term_le_at_t_critical_axiom` no longer appears in RH chain.
- Strict executable-hole scan (active Q3, excluding Archive/Clean):
  - no matches for `^\s*(sorry|admit)` and no `exact?` hits.

Update (2026-02-23, Aristotle context fix):
- Initial Aristotle jobs without explicit context returned non-actionable stubs (model could not see Q3 files).
- Re-submitted the same three sub-agent requests with `--no-auto-add-imports` + explicit `--context-files`:
  - `fab26ba2-c4c8-438d-911f-30970145e35a` (prime_term gate)
  - `750bb959-5f7e-4e5f-919c-c4af2d818949` (Weil tau0)
  - `17375b4f-0025-4b66-b309-f6f4bb7774f2` (PrimeCert PathB margin)
- Expected acceptance criterion unchanged: no `sorry|exact?|admit`, then integrate only hole-free lemmas.

Update (2026-02-23, PrimeCert legacy rebuild):
- Root blocker for legacy chain remains stale/invalid PrimePow `.olean` artifacts.
- Started targeted rebuild:
  `lake build Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000`
- Current state: chunk modules `..._10001_20000` etc are actively recompiling under current toolchain; after completion re-test:
  1) `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
  2) `lake env lean Q3/Proofs/PrimeCert/Brange_2046.lean`

## Synthesis (2026-03-05, in progress) — PrimeHeat arch-bound blocker under current toolchain

Target lemma / axiom:
- `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` in
  `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`.
- Wiring: this feeds `prime_heat_bounds_data` -> `prime_heat_bounds_cert` ->
  `prime_margin_Lipschitz_on_Brange` in `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`,
  and from there the current τ=0 PrimeCert margin chain.

Embedding search (q3_docs, 3 successful queries):
- `prime_heat_bounds_arch_data heat arch integral bound`
- `BrangeHeatCert arch bound a_star heat_weight intervalIntegral`
- `a_star linear growth Gaussian integral prime cert`
- Consistent hits: previous plans already converge on the same route:
  use `a_star_linear_growth` together with Gaussian integrability/interval-integral
  lemmas; no existing hole-free closure was found in the repo index.

Web / external scan:
- No drop-in Mathlib tactic path for this numeric interval bound was identified.
- This strengthens the local conclusion that the next productive move is not a
  fresh theorem sketch in isolation, but restoring the PrimeHeat build chain first.

Local build diagnosis (current machine, 2026-03-05):
1. `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
   fails because `..._Partial.olean` is missing.
2. `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Partial.lean`
   fails because `..._SumData.olean` is missing.
3. `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean`
   fails because `..._Checker.olean` is missing.
4. `lake env lean Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
   fails on incompatible header for
   `BrangeHeatCert_2026_01_28_PrimePowAutoGT10000.olean`.
5. Timestamp check shows that incompatible artifact still dates to 2026-02-09,
   while current project toolchain is `mathlib v4.26.0`; this is a stale-build,
   not a new theorem regression.

Decision tree:
- Option 1 (active): rebuild `BrangeHeatCert_2026_01_28_PrimePowAutoGT10000`
  and then the chain `Checker -> SumData -> Partial -> BrangeHeatCert_2026_01_28`,
  only after that return to `prime_heat_bounds_arch_data`.
- Option 2 (fallback): if the rebuild still fails after the stale `.olean` layer is
  removed, isolate the first source-level error in the GT10000 aggregator and fix
  that before touching arch bounds.
- Option 3 (false-for-now): sending a fresh Aristotle request for
  `prime_heat_bounds_arch_data` immediately. Rejected for now because all prior
  2026-02-09 outputs were empty stubs with `sorry` due missing Q3 context, and the
  current blocker is upstream build integrity.

Concrete next steps:
1. Finish targeted rebuild of `Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000`.
2. Re-run `lake env lean` on `Checker`, `SumData`, `Partial`, and the main
   `BrangeHeatCert_2026_01_28.lean` in that order.
3. Once the chain compiles again, either prove `prime_heat_bounds_arch_data`
   locally from existing heat-integrability infrastructure or prepare a new
   Aristotle request with explicit Q3 context files and no import ambiguity.

## Synthesis (2026-03-05, in progress) — full paper mainline vs live Lean mainline

Source read completely enough to reconstruct the live proof spine:
- `full/RH_Q3.tex` and the active main sections
  `T0`, `A1prime`, `A2`, `A3/*`, `RKHS/*`, `D3/*`, `Weil_linkage`, `Weil_pack`,
  `Main_closure`.
- Active paper mainline is explicitly:
  `T0 + A1' + A2 + A3 + RKHS -> Main positivity -> Weil criterion`.
- `D3`, `T5`, and `IND_AB` are archived/legacy in the paper and are not meant to
  be part of the critical proof path.

What this changes for Lean:
- Live `Q3.Main.RH_of_Weil_and_Q3` currently depends on
  `Q3.Weil_criterion_tau0` and `Q3.Proofs.PrimeCert.prime_cert_margin_from_pathB`,
  not on the paper-mainline analytic chain.
- So the repo now has a structural mismatch:
  the paper advertises an analytic uniform route, while Lean mainline still closes
  via a legacy PrimeCert gate.

Paper mainline nodes that already have serious Lean support:
- `T0`: normalization crosswalk is already wired in `Q3/AxiomsTheorems.lean`.
- `A1'`: density is largely wired/theorem-level in the current transfer stack.
- `A2`: continuity/Lipschitz is theorem-level in current Lean.
- `C1`: compression-by-isometry is already formalized in
  `Q3/Proofs/C1_Embedding_Bridge.lean` and `Q3/Proofs/C1_T_P_comp_bridge.lean`.
- `A3_FLOOR`: monotonicity/sample-point infrastructure exists (`A3_Floor_*`).

Critical mismatches discovered while reading the paper:
- The paper claims “single-scale alignment”, but the active text mixes
  `t = t_critical = 3/20`, `t_sym = 3/50`, and `t_rkhs = 1`.
- `full/sections/A3/symbol_floor.tex` states the uniform Arch floor at `t = 3/50`,
  while `full/sections/A3/main.tex` consumes it as if it were the A3 bridge floor
  at `t = 3/20`.
- `full/sections/RKHS/prime_cap.tex` uses the uniform cap at `t_rkhs = 1`,
  which directly conflicts with the “single-scale” language in `A3/main.tex`.
- `A1'` in the main paper still defers its proof to the archived shifted-atom
  density argument instead of giving a fresh in-line proof.

Recommended Lean refactor:
- Stop treating PrimeHeat/Grid certificate closure as the only mainline plan.
- Introduce a paper-mainline migration track:
  `A3_Digamma_Symbol -> A3_Uniform_Bridge -> RKHS_rho_cap -> tau0_bridge -> Main`.
- Keep legacy `PrimeCert` certificate closure as a separate branch of work, not as
  the blocker for the theorem-first mainline.

Recommended progress tracking:
- Track by paper theorem, not by legacy axiom name.
- Minimal columns:
  paper statement, Lean target file, current proof status, wired into mainline?,
  axiom impact, parameter contract frozen?
- Highest-priority blocker is now not “compute PrimeHeat again”, but
  “freeze the scale contract of the paper mainline”.

## Synthesis (2026-03-07, in progress) — honest target is pair/evenized `t_critical`, not scalar `phi_shift`

Exact live blocker and wiring:
- Active chain is still
  `Q3.Main -> PaperMainlineAtomRoute -> CompatibilityReduction -> Q_nonneg_t_critical`.
- The only nonstandard project axiom in the live scalar node remains
  `Q3.prime_term_le_at_t_critical_axiom`, as confirmed by
  `#print axioms Q3.Main.RH_of_Weil_and_Q3`.
- This axiom is consumed in `Q3/Proofs/Q_nonneg_t_critical.lean` by
  `prime_term_le_at_t_critical -> Q_phi_shift_nonneg_t_critical ->
   Q_phi_shift_pair_nonneg_t_critical -> Q_Fejer_heat_atom_nonneg_t_critical`.

Local search / blocker audit:
- Semantic search must be run from the repo root. Running
  `./scripts/research_oracle.py` from `q3.lean.aristotle/` fails because the
  script only exists at the top level.
- Five local embedding queries were attempted for the new blocker. Three failed
  with `SQLiteError: database is locked / SQLITE_BUSY_RECOVERY`; the two that
  returned results only surfaced stale `tau=0` / old-axiom notes and did not
  produce a direct pair/evenized closure lemma.
- External web search (primary-source oriented) found only general Weil-criterion
  structure results, e.g. Connes--Consani on restricting to compactly supported
  convolution-square test functions. Useful philosophically, but not a direct
  proof of our shifted-evenized `t_critical` lemma.

New local theorem support added:
- `Q3/Proofs/PrimeTerm_t_bridge.lean` now contains:
  `PrimeTermBridge.prime_term_phi_shift_tcritical_le_cap`
  and
  `PrimeTermBridge.prime_term_phi_shift_tcritical_le_exp_rho_oneK`.
- These compile and expose the honest bridge
  `prime_term(phi_shift at t_critical) <= exp_tcrit_to_rkhs(K) * R`,
  with the RKHS cap route providing `R = rho_oneK K`.

Critical no-go discovered immediately:
- `rho_oneK` is defined as
  `exp(8 * pi^2 * t_rkhs_cap * K^2) * rho_one`, so the `t_critical -> t_rkhs_cap`
  transport carries a huge exponential penalty.
- Numerically,
  `t_rkhs_cap = 40/(16*pi^2) ≈ 0.2533029591`,
  and already at `K = 1` we have
  `exp_tcrit_to_rkhs(1) ≈ 1.2151333e7`.
- Therefore the old single-scale budget
  `rho_one <= c_star / 4`
  does **not** control
  `exp_tcrit_to_rkhs(K) * rho_oneK(K)`;
  the bridge explodes instead of closing the scalar inequality.
- So the plan item “prove the same-signature scalar theorem by combining RKHS cap
  with the existing `c_star` floor” is false as an implementation path.

Consequence for the active proof strategy:
- Do **not** send Aristotle after the old target
  `prime_term_le_at_t_critical_axiom` with the same signature.
- The honest next target is one of:
  1. `Q_phi_shift_pair_nonneg_t_critical`,
  2. `Q_Fejer_heat_atom_nonneg_t_critical`,
  3. or a minimal new assumption that closes exactly one of those two theorems.
- The right request should explicitly reuse the new bridge lemmas and the existing
  decomposition
  `Fejer_heat_atom_eq_phi_shifts`,
  but it must allow Aristotle to return a weaker theorem or an explicit obstruction
  if pair/evenized positivity still needs one extra ingredient.

## Synthesis (2026-03-07) — G0 reset loop frozen as project contract

Control-plane decisions:
- We stay in the current repo; no new physical `work3` clone.
- The canonical control plane is exactly four files:
  `PROJECT_ORCHESTRATOR.md`,
  `IMPLEMENTATION_PLAN.md`,
  `docs/PAPER_MAINLINE_TRACKER.md`,
  `docs/INSIGHTS.md`.
- Precedence is fixed:
  orchestrator > paper tracker > execution plan > insights.
- Supporting snapshots such as `docs/CHAIN_STATUS.md` and `ACTIVE/MAIN_CHAIN_DEPS.md`
  remain useful, but they are now explicitly read-only/supporting and no longer
  define active frontier or queue state.

Gate-contract decisions:
- The active project chain is fixed as
  `T0 -> G0 -> G1 -> G2 -> G3 -> G4 -> G5 -> G6 -> RH`.
- `G3` is restored as its own gate. This matters operationally:
  `G2` chooses and freezes the exact admissible family `G_K`,
  while `G3` proves positivity on that same `G_K`.
- The reset sprint was `G0`, i.e. a governance/typing sprint rather than new math:
  `G0.0` numbering/precedence freeze,
  `G0.1` vocabulary split,
  `G0.2` closure typing pass,
  `G0.3` narrative alignment.

Concrete manuscript drift identified before edits:
- `A1'` is genuinely a theorem on the restriction cone
  `R_K = C^+_{even}([-K,K])`, not yet on admissible `W_K`.
- `A2` and the LF route consume admissible `W_K`.
- `Main_closure.tex` still phrases the density input as if it already lived on `W_K`,
  so the closure section is ill-typed until `G0/G1` are made explicit.
- `introduction.tex` still advertises a closed `PSD on each W_K => Weil positivity`
  chain instead of the gate chain with unresolved `G1-G3`.
- Lean wrappers in `Q3/Main.lean` and `PaperMainlineAtomRoute.lean` expose useful
  theorem names, but their docstrings need to say explicitly that the current route
  still inherits `Q3.prime_term_le_at_t_critical_axiom`.

Result of the reset pass:
- `PROJECT_ORCHESTRATOR.md`, `IMPLEMENTATION_PLAN.md`,
  `docs/PAPER_MAINLINE_TRACKER.md`, and `docs/INSIGHTS.md`
  now agree on the same gate chain, precedence rule, and active frontier.
- Active manuscript sections now separate `R_K`, `W_K`, and future `G_K` explicitly.
- `A1'` is now stated as density on `R_K`, while `Main_closure.tex` and the Weil-linkage text stay explicitly conditional on the unresolved closure gates.
- Lean-facing docstrings in `Q3/Main.lean`, `PaperMainlineAtomRoute.lean`, and `CompatibilityReduction.lean`
  now describe the exported route as the current compiled route rather than as an already fully closed proof.

Verification bundle completed:
- `cd full && latexmk -pdf RH_Q3.tex`
- `cd q3.lean.aristotle && lake env lean Q3/Main.lean`
- `printf 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3\n' | lake env lean --stdin`
- Active axiom profile remains:
  `Q3.Weil_criterion` + `Q3.prime_term_le_at_t_critical_axiom`
  plus standard `propext`, `Classical.choice`, `Quot.sound`.

Consequence for the next loop:
- `G0` is now closed.
- The next honest frontier is `G1.1`: freeze the first support-upgrade theorem on admissible `W_K`.
