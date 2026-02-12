# AUDIT PACK: RH_Q3 vs Lean (2026-02-12)

Цель: зафиксировать, что из RH_Q3 уже формализовано в Lean, что остается узким горлышком, и в каком порядке это закрывать до безусловного `Q3.Main.RH_of_Weil_and_Q3 : Q3.RH`.

## 1) Источники аудита

- Manuscript (RH_Q3): `full/RH_Q3.tex`.
- Глобальные гипотезы H1..H5: `full/sections/scope_notation.tex:39`.
- Главный closure-тезис RH_Q3: `full/sections/Main_closure.tex:17`.
- Weil linkage в тексте: `full/sections/Weil_linkage.tex:3`.
- Текущий Lean-роадмап: `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md:31`.
- Сессионный снимок: `SESSION_ENTRY.md:22`.
- Команда проверки main theorem:
  - `echo 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin`
  - результат (2026-02-12): `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`.

## 2) Сопоставление RH_Q3 -> Lean (по H1..H5)

1. H1 (T0 + Weil criterion): в тексте `full/sections/scope_notation.tex:39`, `full/sections/Weil_linkage.tex:3`.
   Статус в Lean: `Q3.Weil_criterion_tau0` остается внешней Tier-1 аксиомой (ожидаемо для текущей архитектуры).

2. H2 (A1' density): в тексте `full/sections/A1prime.tex:27`.
   Статус в Lean: закрыто теоремой `A1_density_WK_thm` в `q3.lean.aristotle/Q3/Proofs/A1_density.lean:955`.

3. H3 (A2 Lipschitz continuity): в тексте `full/sections/A2.tex:36`, `full/sections/A2.tex:86`.
   Статус в Lean: закрыто теоремой `Q_Lipschitz_on_W_K_thm` в `q3.lean.aristotle/Q3/Proofs/Q_Lipschitz.lean:278`.

4. H4 (A3 uniform bridge, floor + cap + discretization): в тексте `full/sections/scope_notation.tex:42`, `full/sections/A3/main.tex:81`.
   Статус в Lean:
   - floor-часть закрыта теоремой `P_A_ge_c_star` в `q3.lean.aristotle/Q3/Proofs/A3_Floor_Main.lean:1012`;
   - но полный mainline closure по PrimeCert пока условный через `h_margin_cert` (см. пункт 4 ниже).

5. H5 (uniform RKHS cap): в тексте `full/sections/scope_notation.tex:43`, `full/sections/A3/symbol_floor.tex:344`.
   Статус в Lean: Rayleigh/RKHS cap-цепочка формализована:
   - `weight_sum_le_rho_one` в `q3.lean.aristotle/Q3/Proofs/RKHS_cap_rayleigh.lean:563`,
   - `rkhs_cap_rayleigh_tcap` в `q3.lean.aristotle/Q3/Proofs/RKHS_cap_rayleigh.lean:1055`.

## 3) Что уже закрыто в mainline

1. Main theorem в Lean есть, но пока условный:
   - `q3.lean.aristotle/Q3/Main.lean:128`
   - сигнатура: `RH_of_Weil_and_Q3 (h_margin_cert : Q3.PrimeCertMarginOnBrange) : Q3.RH`.

2. PrimeCert-margin введен как явная гипотеза:
   - `PrimeCertMarginOnBrange` в `q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean:341`.

3. Step 1 (bucket-sum closure) закрыт:
   - `prime_heat_bucket_data` в `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean:56`.

4. Step 2 (ветка `n > 10000`) интегрирован в checker-path:
   - вызов `prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all` в `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean:33`;
   - генератор переведен на устойчивый шаблон (`fin_cases hmem`, adaptive split, `maxRecDepth`) в `scripts/prime_brange_heat_pp_auto.py:164`, `scripts/prime_brange_heat_pp_auto.py:568`, `scripts/prime_brange_heat_pp_auto.py:305`.

5. Main-chain по `#print axioms` уже “чистый условный”:
   - только `Weil_criterion_tau0` + kernel axioms.

## 4) Что еще открыто (узкие места)

Оставшиеся project-аксиомы, реально блокирующие снятие `h_margin_cert`:

1. `prime_heat_bounds_arch_data`:
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean:62`.

2. `prime_b_grid_bucket_bounds`:
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean:37`.

3. `prime_b_grid_arch_bounds_data`:
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean:33`.

Дополнительно (не аксиомный blocker, но quality-gate перед финалом):

4. Убрать load-bearing `native_decide` из critical checker path:
   - пример в `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean:51`.

## 5) Точный порядок закрытия узких мест

Рекомендуемый порядок (минимум риска, максимум прогресса к финальному theorem-chain):

1. Закрыть Step 4: `prime_heat_bounds_arch_data`.
   Файлы:
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean`
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Tail.lean`
   Критерий: в `BrangeHeatCert_2026_01_28.lean` нет `axiom prime_heat_bounds_arch_data`.

2. Закрыть Step 5: `prime_b_grid_bucket_bounds`.
   Файлы:
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean`
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Checker.lean`
   Критерий: bucket-bound становится theorem-path, а не `axiom`.

3. Закрыть Step 6: `prime_b_grid_arch_bounds_data`.
   Файлы:
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean`
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/Brange_2046.lean`
   Критерий: `prime_b_grid_bounds_cert` полностью theorem-derived без arch-data axiom.

4. Закрыть Step 3 (quality gate): убрать `native_decide` из load-bearing части checker/primepow path.
   Файлы:
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`
   - `q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowAutoGT10000*.lean`
   - `scripts/prime_brange_heat_pp_auto.py`
   Критерий: после снятия `h_margin_cert` не подтягиваются `Lean.ofReduceBool`/`Lean.trustCompiler`.

5. Закрыть Step 7: убрать параметр `h_margin_cert`.
   Файлы:
   - `q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean`
   - `q3.lean.aristotle/Q3/Main.lean`
   Критерий: сигнатура становится `theorem RH_of_Weil_and_Q3 : Q3.RH`.

6. Закрыть Step 8: финальный верификационный проход.
   Команды:
   - `lake env lean Q3/Main.lean`
   - `echo 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin`
   - `./scripts/check_axioms.sh`
   Критерий: остаются только `propext`, `Classical.choice`, `Q3.Weil_criterion_tau0`, `Quot.sound`.

## 6) Метрики (что уже сделано)

Два полезных среза:

1. Исторический curated snapshot (proof-chain oriented):
   - `q3.lean.aristotle/FORMALIZATION_STATS.md` (обновление 2026-02-02):
   - Total lines `39,718`,
   - Theorems `311`,
   - Lemmas `839`,
   - Definitions `515`,
   - Aristotle in-chain `5,421` lines.

2. Текущий raw snapshot (включая огромный автоген PrimePow shard corpus):
   - `./scripts/contribution_stats.sh` (2026-02-12): Total lines `18,872,672`.
   - Это не деградация разработки; это эффект массово сгенерированных `PrimePowAutoGT10000*`.

Практический вывод: для прогресса по доказательству ориентироваться на axiom-chain и roadmap-steps, а не на raw LOC.

## 7) Быстрый чек-лист перед следующим коммитом

1. `git status --short` (чистота дерева/точный набор файлов).
2. `rg -n '^axiom ' q3.lean.aristotle/Q3/Proofs/PrimeCert`.
3. `echo 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin`.
4. Обновить:
   - `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`,
   - `SESSION_ENTRY.md`,
   - `q3.lean.aristotle/docs/INSIGHTS.md`.
