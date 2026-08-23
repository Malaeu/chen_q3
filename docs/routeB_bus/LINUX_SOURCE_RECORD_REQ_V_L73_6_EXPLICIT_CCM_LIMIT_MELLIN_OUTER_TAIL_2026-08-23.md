# SOURCE RECORD — L73.6 explicit CCM limit Mellin outer tail (Linux-тело за Codex)

```yaml
PRIMARY: L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 04b95c7e — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 04b95c7e3534d7bc176598d6ea1067a27757b0c7
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен после q3_check перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"explicit limit Mellin outer tail lowerMellinTail
  upperMellinTail inverse four\" exited 0 — только известные поставщики
  (lowerMellinTail/upperMellinTail в EStarWindowedMellinCrosswalk);
  целевых дубликатов нет, имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinOuterTail.lean
LEAN_GIT_BLOB: d2d729e5b5360d7e86167ee07f09b7344ba2d27a
LEAN_SHA256: db836a402448fcd8f9dd632b672d1ee98e68502361f67a26d75dbdaaca445d72
LEAN_LINES: 520

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinNormalization
  - Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrersFactorFourExplicitLimitMellinOuterTail  # def, factor-four target, координата −I·z
  - Q3.RouteB.D0Pstar.selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn

PRIVATE_DECLARATIONS:
  - neg_I_mul_re                               # (−I·z).re = z.im — знаковый гейт ДО оценок
  - centeredStrip_tail_exponent_guard_plant    # REQUIRED plant, дословно из вердикта
  - exp_linear_bound' / s4_exp_bound / s3_exp_bound
  - explicitCCMLimitH_inverse_four_decay       # локальная передоказка (upstream приватен)
  - summable_pnat_inv_four / E_star_norm_bound / sqrt_mul_inv_pow_eq_rpow
  - E_star_four_mul_eq                         # E⋆(4h) = 4·E⋆h (tsum_mul_left)
  - factorFour_norm_le_rpow_top                # ‖E⋆(4h)(u)‖ ≤ 132·Z₄·u^{−7/2}, ∀u>0
  - factorFour_norm_le_rpow_bot                # ‖E⋆(4h)(u)‖ ≤ 132·Z₄·u^{7/2}, ∀u>0, через инверсию
  - lambda_ge_one / lambda_pos
  - upper_tail_bound                           # ≤ 44·Z₄/λ³ (integral_Ioi_rpow_of_lt)
  - lower_tail_bound                           # ≤ 44·Z₄/λ³ (integral_pow на 0..λ⁻¹)
  - factorFour_outerTail_norm_le_inv_cube      # REQUIRED rate: ≤ 88·Z₄/λ³ на всей полосе

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrersFactorFourExplicitLimitMellinOuterTail_tendstoUniformlyOn:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "factor-four хвост определён дословно по вердикту (пункт 2)"
  - "inverse-four ‖h(x)‖ ≤ 33/x⁴ передоказан приватно (пункт 3)"
  - "factor-four E⋆-границы на обеих сторонах: 132·Z₄·u^{∓7/2}, нулевая
     сторона через точную публичную инверсию E_star_explicitCCMLimitH_inv
     (пункт 4)"
  - "(−I·z).re = z.im доказан отдельной леммой; плант экспонент
     y−9/2 < −4 ∧ 2 < y+5/2 исполнен ДО обеих оценок (пункт 5)"
  - "верхний индикаторный интеграл ≤ 44·Z₄/λ³: norm_integral_le_of_norm_le
     + setIntegral_indicator + integral_Ioi_rpow_of_lt при a = −4 (пункт 6)"
  - "нижний индикаторный интеграл ≤ 44·Z₄/λ³: мажоранта 132·Z₄·u² на
     Ioo 0 λ⁻¹, integral_pow на 0..λ⁻¹ (пункт 7)"
  - "общий приватный rate 88·Z₄/λ³ доказан ДО топологии (пункт 8)"
  - "TendstoUniformlyOn через Metric.tendstoUniformlyOn_iff;
     selectedFerrersPaperLambda_sq и λ ≥ 1 дают λ³ ≥ λ² = k+2;
     tendsto_const_div_atTop_nhds_zero_nat (пункт 9)"
  - "#print axioms публичной теоремы (пункт 10)"

PINNED_MATHLIB_USED:
  - "Mathlib.Analysis.SpecialFunctions.ImproperIntegrals: integral_Ioi_rpow_of_lt (строка 173), integrableOn_Ioi_rpow_of_lt (строка 131)"
  - "нижний конечный интервал: integral_pow (Mathlib.Analysis.SpecialFunctions.Integrals.Basic, строка 172) через intervalIntegral.integral_of_le + integral_Ioc_eq_integral_Ioo"

FORBIDDEN_CHECK:
  unscaled_target_in_public_definition: no (E⋆(4·h) в определении дословно)
  factor_four_omitted_or_duplicated: no (ровно один, внутри целевой функции)
  outer_tail_decay_as_hypothesis: not_added (доказан)
  pointwise_only_convergence: no (TendstoUniformlyOn на всей открытой полосе —
    сильнее закрытых подполос, по вердикту)
  Mellin_convergence_or_inversion_assumed: no (инверсия — публичная теорема
    L73-цепи; сходимость мажорант доказана)
  L73_3_or_L73_4_imported: no (импорты ровно два, по директиве)
  L73_5_or_prior_admitted_files_edited: no
  L73_7_L73_8_port_inhabitant_bundled: no
  numerical_constants_fitted: no (33 локально выведено; 132 = 4·33;
    44 = 132/3; 88 = 2·44; Z₄ символически)
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 4 (rpow_add-паттерн при несоседних множителях — развёрнут в
    прямую сторону + ring; deprecated div_le_div_iff — переписано на
    field_simp-равенство; Nat-cast (↑2+1) в integral_pow; rw закрыл цель
    рефлексивностью раньше хвостовых тактик. Предсказанный
    MELLIN_INDICATOR_SET_INTEGRAL_AND_RPOW_NORMAL_FORM сбой выстрелил
    ЧАСТИЧНО: только rpow/cast-нормальные формы, индикаторная механика
    прошла с первого раза)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinOuterTail.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1ExplicitCCMLimitMellinOuterTail — Build completed successfully (7838 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1ExplicitCCMLimitMellinOuterTail.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: L73_6_EXPLICIT_CCM_LIMIT_MELLIN_OUTER_TAIL_UNIFORM_ON_CLOSED_SUBSTRIPS_LEAN
NEXT_LOAD_BEARING_GAP: L73_7_SELECTED_FERRERS_CLOSED_SUBSTRIP_MELLIN_CONVERGENCE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
