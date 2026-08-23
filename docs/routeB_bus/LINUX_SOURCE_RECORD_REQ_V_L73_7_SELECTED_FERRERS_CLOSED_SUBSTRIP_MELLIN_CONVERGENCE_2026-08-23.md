# SOURCE RECORD — L73.7 selected Ferrers closed-substrip Mellin convergence (Linux-тело за Codex)

```yaml
PRIMARY: L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 4c8b995a — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 4c8b995ab2fe44a2c6486a4dfdbbf84fdb3451ba
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен после q3_check перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"preAnchorGwinTransformCoordinate windowed Mellin closed
  substrip convergence Gwin\" exited 0 — найдены только известные поставщики
  (preAnchorGwinTransformCoordinate, mellin_eq_lower_add_window_add_upper,
  windowedMellin, crosswalk); целевых дубликатов нет, имя свободно."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersClosedSubstripMellinConvergence.lean
LEAN_GIT_BLOB: 43c2d6a1902b84b4bea5861d2be473fa52d7eb32
LEAN_SHA256: 8ee76ce62560e19a3f4c3ada79d8d1f16c1f7603c72a7b052de933c0bea89cbd
LEAN_LINES: 1052

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail
  - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinOuterTail

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates
    # TendstoUniformlyOn (fun k z => sourceScale·Gwin) centeredXi atTop {|z.im| ≤ σ},
    # 0 ≤ σ < 1/2; точная выбранная пара, прекоммитнутый индекс m=N=k+2,
    # точный factor-four масштаб, точная Gwin-координата, продакшн centeredXi

PRIVATE_DECLARATIONS:
  - closedSubstrip_margin_is_loadBearing_plant  # REQUIRED plant: (1/λ)(λ−1)=1−1/λ ∧ >0
    # (в вердикте биндер назван λ — в Lean 4 λ зарезервирована, локально lam)
  - exp_linear_bound' / s4_exp_bound / s3_exp_bound
    / explicitCCMLimitH_inverse_four_decay / summable_pnat_inv_four
    / E_star_norm_bound / sqrt_mul_inv_pow_eq_rpow  # копии (upstream приватны)
  - E_star_isBigO_atTop / E_star_isBigO_zero / continuous_explicitCCMLimitH
    / continuousOn_E_star / locallyIntegrableOn_E_star  # копии из L73.5-слоя
  - E_star_four_mul_eq / lambda_ge_one / lambda_pos / neg_I_mul_re  # копии
  - lambda_gt_one / lambda_m_idx_eq / muntz_Estar_eq
  - gwin_eq_window_integral            # Gwin = ∫_{Ioo λ⁻¹ λ} u^{s−1}·E⋆q
  - continuousOn_E_star_four / locallyIntegrableOn_E_star_four
    / E_star_four_isBigO_atTop / E_star_four_isBigO_zero
  - mellinConvergent_E_star_four       # ДОКАЗАН локально, не предположен
  - centeredXi_eq_lower_add_window_add_upper  # Ξ = lower+window+upper (crosswalk)
  - windowedMellin_eq_Ioo_integral     # Icc-индикатор → Ioo-интеграл, концы нулевой меры
  - comb_zero_beyond_window / E_star_comb_eq_finite_on_window
    # равномерное конечное усечение: ≤ k+2 активных дилатов на всём окне
  - integrable_comb / weight_continuousOn / integrableOn_window_source
    # интегрируемость source-стороны из полей h0_integrable/h4_integrable
    # через integrable_comp_mul_left_iff + Integrable.bdd_mul
  - integrableOn_window_target / integrableOn_window_error
  - source_minus_target_split          # РЕШАЮЩЕЕ ТОЖДЕСТВО (см. ниже)
  - window_error_norm_le               # двухчленный rate вердикта

DECISIVE_IDENTITY:
  statement: "sourceScale·Gwin − centeredXi = ∫_{Ioo λ⁻¹ λ} u^{−Iz−1}·FullError − OuterTail"
  scope: "для КАЖДОГО k и каждого z открытой полосы — точно, без eventual-условий"
  new_hypothesis_required: no
  source_object_changed: no
  target_Mellin_convergence_assumed: no (доказана локально)
  stop_condition_of_directive: NOT_TRIGGERED

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrers_closedSubstripMellinConvergence_of_modeAndChiRates:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - CCM_LEMMA_7_3_SELECTED_FERRERS_CLOSED_SUBSTRIP_CONVERGENCE
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "L73.3 + L73.4 дали eventual C_full = C₁+C₂ с ‖FullError‖ ≤ C_full/(λ√u)
     на всём окне (пункт 2: eq_main_sub_targetTail + norm_sub_le)"
  - "точное source-тождество Gwin ↔ окно-Mellin: lambda_m(idx k) = paperLambda,
     Muntz Estar = E_star, Ioo↔Icc только через концы нулевой меры
     (integral_Icc_eq_integral_Ioo) (пункт 3)"
  - "MellinConvergent(E⋆(4h))(−Iz) передоказан локально: двусторонний Big-O
     ×4 + mellinConvergent_of_isBigO_rpow; НЕ гипотеза, upstream не правился
     (пункт 4)"
  - "точное поточечное тождество source − target = windowMellin(FullError)
     − OuterTail; интегрируемость source-стороны из конечной поддержки
     (≤ k+2 дилатов) и Bochner-полей пары (пункт 5)"
  - "фиксированные σ, z, |z.im| ≤ σ; окно разрезано в u = 1
     (Ioo_union_Ico + setIntegral_union) (пункт 6)"
  - "[λ⁻¹,1]: мажоранта u^{−σ−3/2}, точный интеграл integral_rpow ⇒
     ≤ Cf·λ^{σ−1/2}/(σ+1/2) (пункт 7)"
  - "[1,λ]: мажоранта u^{σ−3/2}, ∫ ≤ ∫_{Ioi 1} = 1/(1/2−σ)
     (integral_Ioi_rpow_of_lt) ⇒ ≤ Cf·λ⁻¹/(1/2−σ) (пункт 8)"
  - "двухчленный rate вердикта получен дословно:
     Cf·(λ^{−1/2+σ}/(σ+1/2) + λ⁻¹/(1/2−σ)) (пункт 9)"
  - "финал: единая мажоранта Crate·λ^{σ−1/2} → 0 (λ² = k+2,
     tendsto_rpow_neg_atTop) + публичный L73.6 TendstoUniformlyOn для
     хвоста; ε/2 + ε/2 (пункт 10)"
  - "#print axioms публичной теоремы (пункт 11)"

FORBIDDEN_CHECK:
  whole_open_strip_source_convergence: not_claimed (плант держит граничную
    модель 1 − 1/λ ↛ 0; закрытая подполоса |z.im| ≤ σ < 1/2)
  pointwise_relabeled_as_uniform: no (честный Metric.tendstoUniformlyOn_iff)
  free_window_Mellin_error_hypothesis: not_added (доказан)
  free_Mellin_convergence_hypothesis: not_added (доказана локально)
  unscaled_target: no (E⋆(4h) в тождестве и хвосте)
  factor_four_omitted_or_duplicated: no (ровно один, в sourceScale и в
    target-функции соответственно — как в L73.4-определении FullError)
  selected_pair_or_schedule_changed: no (m = N = k+2 прекоммитнут)
  sigma_chosen_after_k: no (σ фиксирована до atTop-квантора)
  F72_6_sup_error_integrated_over_physical_window: no (Mellin-веса, не sup·2λ)
  L73_3_to_L73_6_edited: no (только импорт/вызовы)
  L73_8_or_port_inhabitant_bundled: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 6 (indicator-под-smul — ручная поточечная коммутация;
    Integrable-как-And ломает дот-нотацию congr_fun — квалификация
    IntegrableOn.congr_fun; Pi.sub_apply; continuousAt_cpow_const без
    Complex-префикса; positivity не видит λ>0 из set-переменной — ручные
    div_nonneg/mul_nonneg; rpow_add съел σ+1/2 не там — явный hsplit;
    поверх — слово «admitted» в докстринге валило q3_check-скан
    (переписано «ratified»; известная ловушка сканера).
    Предсказанный GWIN_IOO_ICC_ENDPOINT_OR_MELLIN_INTEGRABLE_NORMAL_FORM
    сбой выстрелил ЧАСТИЧНО: Ioo/Icc-стык прошёл сразу через
    integral_Icc_eq_integral_Ioo, тёрлись — интегрируемость-нормальные
    формы (P_L73_7_3 подтверждён: friction, не математика)"
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersClosedSubstripMellinConvergence.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersClosedSubstripMellinConvergence — Build completed successfully (7853 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersClosedSubstripMellinConvergence.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE_LEAN
NEXT_LOAD_BEARING_GAP: L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_INHABITANT
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
