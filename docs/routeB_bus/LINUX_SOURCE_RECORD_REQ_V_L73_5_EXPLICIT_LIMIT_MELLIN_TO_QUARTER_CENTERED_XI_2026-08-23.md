# SOURCE RECORD — L73.5 explicit limit Mellin to quarter centered Xi (Linux-тело за Codex)

```yaml
PRIMARY: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 1dc92546 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 1dc9254650d8a53639b8be42bc37170cbb5f2c6a
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен после q3_check перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"mellin E_star quarter centeredXi Gaussian Mellin
  normalization riemannXi functional equation\" exited 0 — найдены только
  известные поставщики (mellin_E_star_eq_riemannZeta_mul,
  rh_iff_centeredXi_zeros_real, integral_mul_cpow_eq_mellin); целевых
  дубликатов нет, имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinNormalization.lean
LEAN_GIT_BLOB: bc9b5eddf38bb8377d118cfec749e4f37b4cd516
LEAN_SHA256: 0d79d4aba4d54374e17a9ccfdc0018020f5f152ce3b0a4fe9d71e8a563451fc9
LEAN_LINES: 794

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.D0PstarExplicitCCMLimitFourier
  - Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk
  - Q3.Proofs.RouteB.CenteredXiZeroNonzero

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi
  - Q3.RouteB.D0Pstar.mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi

PRIVATE_DECLARATIONS:
  - quarter_centeredXi_ne_centeredXi_at_zero   # REQUIRED plant, дословно из вердикта
  - exp_linear_bound' / s4_exp_bound / s3_exp_bound
  - explicitCCMLimitH_inverse_four_decay  # ‖h x‖ ≤ 33/x⁴, локальная передоказка
    (upstream-факт приватен в L73.4-файле и неимпортируем)
  - gaussH / gaussH_eq_rpow_form / monoGaussH / mellin_congr_Ioi
  - mellin_exp_neg (Γ-интеграл) / mellin_exp_neg_pi_mul / re_div_two
  - mellin_gaussH  # ℳ(e^{−πx²})(s) = (1/2)·Γℝ(s)
  - mellinConvergent_exp_neg / mellinConvergent_gaussH
  - monomial_integrand_eqOn / mellinConvergent_monomial_gaussH / mellin_monomial_gaussH
  - explicitCCMLimitH_decomp  # h = π²·x⁴G − (3π/2)·x²G
  - mellinConvergent_explicitCCMLimitH
  - mellin_explicitCCMLimitH  # ℳh(s) = s(s−1)/8 · Γℝ(s) — 1/8 ДО ζ-умножения
  - dilate_aestronglyMeasurable / dilate_lintegral_eq
    / ennreal_pnat_rpow_mul_tsum_ne_top  # скейлинг-аргумент MuntzV3, воспроизведён
  - eStarMellinAbsolute_explicitCCMLimitH  # payload ДОКАЗАН, не предположен
  - summable_pnat_inv_four / E_star_norm_bound / sqrt_mul_inv_pow_eq_rpow
  - E_star_isBigO_atTop   # E⋆h = O(u^{−7/2}) на ∞
  - E_star_isBigO_zero    # E⋆h = O(u^{7/2}) в 0 — через публичную инверсию
  - continuous_explicitCCMLimitH / continuousOn_E_star / locallyIntegrableOn_E_star
  - xiStrip / isOpen_xiStrip / preconnected_xiStrip  # связная полоса −3<re<3
  - differentiableOn_mellin_E_star  # mellin_differentiableAt_of_isBigO_rpow
  - half_re_eq / seed_identity  # half-plane тождество на 1/2 < s.re
  - strip_identity  # AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
  - riemannXi_one_sub  # функц. уравнение из completedRiemannZeta₀_one_sub

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.mellin_E_star_explicitCCMLimitH_eq_quarter_centeredXi:
    - propext
    - Classical.choice
    - Quot.sound
  Q3.RouteB.D0Pstar.mellin_E_star_four_mul_explicitCCMLimitH_eq_centeredXi:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - EXPLICIT_CCM_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI
    - FACTOR_FOUR_EXPLICIT_CCM_LIMIT_MELLIN_TO_CENTERED_XI
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "гауссова формула ℳh(p) = p(p−1)/8·Γℝ(p) доказана приватно в абсолютной
     полуплоскости через mellin_comp_rpow / mellin_comp_mul_left /
     mellin_cpow_smul / Complex.Gamma_eq_integral / Gammaℝ_def /
     Gammaℝ_add_two; коэффициент 1/8 появляется ДО ζ-умножения (пункт 2)"
  - "EStarMellinAbsolute payload построен скейлинг-аргументом MuntzV3
     (дилатационное lintegral-масштабирование n^{−re p} + Σ n^{−re p} < ∞);
     interchange НЕ предположен (пункт 3)"
  - "mellin_E_star_eq_riemannZeta_mul применён на полуплоскости 1/2 < s.re;
     с riemannXi_eq_completedRiemannZeta и
     completedRiemannZeta_eq_Gamma_mul_riemannZeta даёт
     ℳ(E⋆h)(s) = (1/4)·riemannXi(s+1/2) (пункт 4)"
  - "связная полоса −3 < s.re < 3: на ∞ O(u^{−7/2}) из локального
     inverse-four-распада и Σn⁻⁴; в 0 O(u^{7/2}) через точную публичную
     инверсию E_star_explicitCCMLimitH_inv;
     mellin_differentiableAt_of_isBigO_rpow (пункт 5)"
  - "продолжение через AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
     в точке z₀ = 1; аналитичность НЕ предположена (пункт 6)"
  - "функциональное уравнение riemannXi(1−s) = riemannXi(s) приватно из
     completedRiemannZeta₀_one_sub; подстановка s = −I·z даёт
     centeredXi z (пункт 7)"
  - "фактор-четыре следствие чистой линейностью E⋆/tsum/mellin
     (tsum_mul_left + mellin_const_smul) (пункт 8)"
  - "#print axioms обеих публичных теорем (пункт 9)"

FORBIDDEN_CHECK:
  unscaled_coefficient_one_equality: not_proved (плант держит: (1/4)·Xi(0) ≠ Xi(0))
  centeredXi_changed: no
  explicitCCMLimitH_changed: no
  factor_four_fitted_numerically: no (чистая линейность после quarter-тождества)
  EStarMellinAbsolute_assumed: no (доказан)
  Mellin_analyticity_or_continuation_assumed: no (двусторонний Big-O + identity theorem)
  only_half_plane_identity_proved: no (полоса −3<re<3 покрывает centered strip)
  F72_6_imported_as_substitute: no (импорты ровно три, по директиве)
  L73_6_L73_7_or_port_inhabitant_bundled: no
  upstream_files_edited: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 5 (коэрция s/↑2 в mellin_comp_rpow; cpow-vs-npow элаборация
    мономов — решено real-cast мономами monoGaussH + mellin_congr_Ioi;
    отсутствие open Topology для 𝓝[>]; setOf-membership в выпуклости;
    MulRightStrictMono-instance → mul_lt_mul_of_pos_left;
    convex_halfSpace_re_* вне замыкания импортов → ручная выпуклость.
    Предсказанный BIGO_NEAR_ZERO_OR_ANALYTIC_IDENTITY_NORMAL_FORM сбой
    НЕ выстрелил: Big-O-слой и identity-слой прошли без правок по существу)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinNormalization.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinNormalization — Build completed successfully (7758 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinNormalization.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: обе публичные теоремы
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: L73_5_EXPLICIT_LIMIT_MELLIN_TO_QUARTER_CENTERED_XI_LEAN
NEXT_LOAD_BEARING_GAP: L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
