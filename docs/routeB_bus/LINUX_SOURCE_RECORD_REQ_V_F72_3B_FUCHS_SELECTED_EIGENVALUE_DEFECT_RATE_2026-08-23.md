# SOURCE RECORD — F72.3B Fuchs selected eigenvalue defect-rate port (Linux-тело за Codex)

```yaml
PRIMARY: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict b2099885 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: b20998850bdcc89205440022f6ed2f143b596c6f
BASE_HEAD_PROVENANCE: git rev-parse HEAD, снят живым перед созданием файла и
  перепроверен перед коммитом; точный родитель (промежуточных коммитов нет)

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"Fuchs paper eigenrelation paperFiniteFourierAction
  paperRescale selected chi defect rate\" exited 0 — только TEXT_CANDIDATE
  в comparator-хранилище, дубликата порта нет; F72.3A-поставщик
  paperFiniteFourierAction_paperRescale_eq_smul_paperRescale_finiteFourierAction
  подтверждён единственным intertwining-поставщиком."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1FuchsSelectedEigenvalueDefectRate.lean
LEAN_GIT_BLOB: 11cc5ffa7d3154f7641e155b2a85b5f2e39a9463
LEAN_SHA256: 9e94718d95a63ac9d8575a345856a3defcb44cbf01de5dd784885d6dbfe5a31f
LEAN_LINES: 249

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates

PRIVATE_DECLARATIONS:
  - fuchs_positive_branch_guard_plant   # REQUIRED_PRIVATE_PLANT: |1−(−1)²|=0 ∧ |1−(−1)|=2
  - selectedLambda_pos_defectPort
  - mu_crosswalk                        # mu = √(2π)·chi через F72.3A при t=0
  - chi_defect_of_mu                    # positive branch + |1−χ| ≤ |1−χ²| + окно-переход

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrers_finiteFourierEigenvalueDefectRate_of_explicitFuchsRates:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - F72_3_SELECTED_PROJECT_FUCHS_EIGENVALUE_CROSSWALK
    - F72_3B_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "t=0 в F72.3A: F_a(Uh)(0) = √(2π)·U(T_λ h)(0)"
  - "проектные эйгенotношения из selectedFerrersPreAnchorPair_spec (компоненты
     8 и 9) при x=0; внешние Fuchs-отношения при t=0 (hwin0: 0 ∈ Icc)"
  - "paperRescale h 0 ≠ 0: центр ≠ 0 (selectedFerrersCenterZero/Four_ne,
     развёрнутые через def) × коэффициент (2π)^{-1/4} ≠ 0; сокращение
     mul_right_cancel₀ ⇒ μ = √(2π)·χ (mu_crosswalk; μ НЕ определён как
     произведение — выведен сокращением)"
  - "положительная ветвь: μ>0 ∧ √2π>0 ⇒ χ>0 (от противного через
     mul_nonpos_of_nonneg_of_nonpos)"
  - "μ²/(2π) = χ² из точного √-тождества (sq_sqrt), не из нормировочной
     конвенции"
  - "|1−χ| ≤ |1−χ²| для χ>0: факторизация (1−χ)(1+χ), |1+χ| ≥ 1"
  - "paperWindowRadius(λ)² = 2πλ² и 2π ≥ 1 (через pi_gt_three):
     C/a² ≤ C/λ², без подгоночных факторов"
  - "пересечение событий, общая константа Cχ = C0 + C4"

FORBIDDEN_CHECK:
  mu_defined_as_sqrt2pi_chi: not_present (выведено сокращением центра)
  full_eigenrelation_replaced_by_center_only_equation: not_present (гипотезы —
    полные отношения на окне; в доказательстве потреблены при t=0, что
    корректно для ∀-гипотезы)
  Lambda_eq_chi_assumed: not_present
  a_eq_lambda_assumed: not_present (точное a = √(2π)·λ)
  chi2_identified_with_Fuchs_degree_2: not_present
  hmu0pos_hmu4pos_dropped: not_dropped (несущие для positive branch)
  defect_hypothesis_stated_directly_on_chi: not_present (входы — о μ в
    paper-окне)
  fitted_constant: none (Cχ = C0 + C4)
  F72_1C_imported: not_imported (ровно два предписанных импорта)
  F72_4_F72_5_L73_2_bundled: not_bundled
  F72_3A_F72_1C_center_anchor_edited: none_edited
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 2 (пропущенная локальная позитивность λ — добавлена приватно;
    nlinarith для 2πλ² ≥ λ² потребовал pi_gt_three вместо pi_pos)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1FuchsSelectedEigenvalueDefectRate.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1FuchsSelectedEigenvalueDefectRate — Build completed successfully (7840 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1FuchsSelectedEigenvalueDefectRate.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT_LEAN
NEXT_LOAD_BEARING_GAP: F72_4_CENTER_INTEGRAL_RATE_FROM_CHI
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
