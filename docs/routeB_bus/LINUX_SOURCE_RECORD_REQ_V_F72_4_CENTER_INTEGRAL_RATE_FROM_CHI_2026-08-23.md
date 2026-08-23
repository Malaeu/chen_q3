# SOURCE RECORD — F72.4 center-anchored integral rate from chi (Linux-тело за Codex)

```yaml
PRIMARY: F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict b0cbbc9e — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: b0cbbc9ef0e49b8a52e818f417d85540dfcb2161
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"centerAnchorScalarZero I0 h0_fourier_center center
  integral rate chi defect\" exited 0 — только TEXT_CANDIDATE, дубликата нет;
  ProlatePair.h0_fourier_center/h4_fourier_center и центральные замки
  подтверждены точными поставщиками."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCenterIntegralRate.lean
LEAN_GIT_BLOB: 5fbff847fe85311e0face9b8afc532ca1af19f6c
LEAN_SHA256: c08d502b278fecf715241e80dbe02f246b4ea2064fbcd1cfc903d0ac8473c7e4
LEAN_LINES: 135

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_4_CENTER_INTEGRAL_RATE_FROM_CHI_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate

PRIVATE_DECLARATIONS:
  - centerAnchoredIntegral_without_chiRate_plant  # REQUIRED: |−1−1|=2 ∧ |3(−1)−3|=6

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrers_centerAnchoredIntegralRate_of_chiDefectRate:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "eventual chi-границы из hχ (filter_upwards)"
  - "точные тождества: a0·I0 = χ0 из h0_fourier_center + centerAnchorScalarZero_
     mul_center (через selectedFerrersCenterZero); a4·I4 = 3·χ2 аналогично"
  - "комплексные нормы вещественных кастов: Complex.norm_real +
     Real.norm_eq_abs + abs_sub_comm (пункт 4 дословно)"
  - "mode0-дефект напрямую; mode4-дефект умножен на 3 точно"
  - "CI = 3·Cχ; hCχ использован только для расширения mode0-строки"
  - "F72.1C, Satz 9, cylinder-границы, новые guard'ы — НЕ использованы"

FORBIDDEN_CHECK:
  pointwise_F72_1C_error_integrated_over_window: not_done (в докстринге явно
    записано, почему это потеряло бы степень λ)
  G6N1SelectedFerrersDirectCylinderRate_imported: not_imported (ровно один
    предписанный импорт)
  integral_rate_hypothesis_added: not_added
  target_integral_values_as_hypotheses: not_added (из полей ProlatePair)
  I0_I4_replaced_by_neighboring_integral: not_present (литеральные поля)
  target_centers_changed: no (1 и 3)
  chi2_identified_with_paper_degree_2: not_present
  CI_fitted_after_inspection: no (3·Cχ a priori)
  F72_5_L73_2_bundled: not_bundled
  F72_3B_center_anchor_edited: none_edited
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 2 (единственный сбой — div_le_div_of_nonneg_right ждёт 0 ≤, дан
    был 0 <; .le)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersCenterIntegralRate.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersCenterIntegralRate — Build completed successfully (7841 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersCenterIntegralRate.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: F72_4_CENTER_INTEGRAL_RATE_FROM_CHI_LEAN
NEXT_LOAD_BEARING_GAP: F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
