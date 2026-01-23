# Project Insights

Короткие записи + ссылки на подробности. Здесь держим только:
- проблему;
- как быстро ее детектить;
- ссылку на подробный разбор.

Полный список файлов: `docs/insights/INDEX.md`.

---

## Навигация (кратко)

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
- Semantic search workflow (q3search/websearch):
  1) сначала q3search (3-5 запросов, до ~75% уверенности), 2) потом websearch,
  3) синтез в 5-10 строк, 4) обновить `docs/INSIGHTS.md` + коммит "in progress",
  5) по завершении добавить итоговый инсайт. НЕ запускать `mgrep watch`/`mgrep --sync`.

---

## A3/Rayleigh: критический путь

- Символы `a_star` vs `P_A`: признаки рассогласования, reverse‑engineering → `docs/insights/a3_symbol_mismatch_reverse_engineering.md`.
- Досье по различиям `a_star` и `P_A` → `docs/insights/a_star_vs_p_a_dossier.md`.

- Rayleigh без SB: пытаемся тащить Szego‑Bottcher → `docs/insights/rayleigh_vs_sb_optional.md`.
- SB не нужен (краткая формулировка) → `docs/insights/szego_bottcher_not_needed.md`.

- RKHS cap: видим несходимость по ρ=0.868 → `docs/insights/a3_bridge_math_rkhs_bound.md`.
- RKHS cap реализация (t_rkhs_cap=40, rho_one=1/25) → `docs/insights/rkhs_cap_implementation_2026_01_15.md`.
- Tau-shift: варианты RKHS cap/A3 floor + выбор Variant 1 (риски/план) → `docs/insights/tau_shift_variants_rkhs_a3_2026_01_18.md`.

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

---

## Спеки

- Основной спецификатор инвариантов: `docs/PROJECT_SPECS.md`.
