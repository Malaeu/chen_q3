# Hub: Status And Navigation

Источник: `docs/insights/INSIGHTS_legacy_2026_02_26.md`.
Навигация, быстрые входы и контекстные блоки.

## Included Sections

- line 1: (preamble)
- line 12: Навигация (кратко)
- line 892: Параметры и численные проверки
- line 905: Misc / Unsorted (нужно разложить по разделам)

<!-- wave2_related_start -->
## Related Legacy Files (Wave 2)

Связанные standalone-файлы по домену `status`:

- `docs/insights/key_constants_reference.md`
- `docs/insights/proven_assets_inventory_2026_01_14.md`
- `docs/insights/rh_q3_invariants_contract_2026_01_16.md`
<!-- wave2_related_end -->

## Content

<!-- legacy_line:1 -->

# Project Insights

Короткие записи + ссылки на подробности. Здесь держим только:
- проблему;
- как быстро ее детектить;
- ссылку на подробный разбор.

Полный список файлов: `docs/insights/INDEX.md`.

---


<!-- legacy_line:12 -->

## Навигация (кратко)

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


<!-- legacy_line:892 -->

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


<!-- legacy_line:905 -->

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
