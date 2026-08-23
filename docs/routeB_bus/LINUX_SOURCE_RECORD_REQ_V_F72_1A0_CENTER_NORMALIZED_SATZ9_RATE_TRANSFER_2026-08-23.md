# SOURCE RECORD — F72.1A0 center-normalized Satz-9 rate transfer (Linux-тело за Codex)

```yaml
PRIMARY: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict a0b787db — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: a0b787dbfa2d75b526973f05263d501036c7eced
BASE_HEAD_PROVENANCE: git rev-parse HEAD, выполнен непосредственно перед
  созданием файла И перепроверен непосредственно перед коммитом; не скопирован
  из директивы

COMMIT: SAME_COMMIT_AS_THIS_RECORD

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CenterNormalizedSatz9RateTransfer.lean
LEAN_GIT_BLOB: 02cb54e4040552445a44134ceaea548adcbaa92c
LEAN_SHA256: 8614db5e2ee487ce41b70e3899ca83533b88f7668e399418e797e2f25005a184
LEAN_LINES: 141

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_1A0_CENTER_NORMALIZED_SATZ9_RATE_TRANSFER_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.centerNormalizedSatz9Rate_of_scaledFixedModeRate

PRIVATE_PLANT:
  name: centerNormalization_denominator_guard_plant
  statement: "|1/100 − 1| ≤ 1 ∧ |1 − 1| ≤ 1 ∧ |1/(1/100) − 1| > 10"
  demonstrates: центр-нормализация усиливает равномерную ошибку на два
    порядка при малом центре; денominator-guard hdenom несущий, не декоративный

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.centerNormalizedSatz9Rate_of_scaledFixedModeRate:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - F72_1A_CENTER_NORMALIZATION_DENOMINATOR_LEDGER
    - F72_1A_GAMMA_TO_LAMBDA_SQUARED_RATE_TRANSFER
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "filter_upwards [hraw, hdenom] — пересечение eventual-событий"
  - "0 < gamma k из hgamma + positivity"
  - "hraw при x=0 + hcenter ⇒ ‖q 0‖ ≥ targetCenter − eps ≥ targetCenter/2 > 0
     (norm_sub_norm_le + денominator-guard)"
  - "centerNormalized через scale: (scale·p x)/(scale·p 0) = p x/p 0,
     mul_div_mul_left c hscale k"
  - "точное числительное тождество: c·(qx/q0) − tx =
     [c·(qx−tx) + tx·(c−q0)]/q0, field_simp+ring при q0 ≠ 0"
  - "треугольник + htarget + деление на гарантированный знаменатель
     (div_le_div₀ против targetCenter/2)"
  - "hgamma-переписывание: (c+B)·eps/(c/2) = rawC(c+B)/(π·c)/λ² —
     закрыто field_simp ТОЧНО (le_of_eq), константа не подгонялась"

FORBIDDEN_CHECK:
  raw_Satz9_asymptotic_asserted_or_axiomatized: not_present (hraw — явная
    гипотеза теоремы, paper-вход остаётся открытым и типизированным)
  Satz8_L2_rate_used_for_sup_norm: not_used
  O_gamma_minus_one_on_unscaled_raw_mode: not_present (rate стоит на
    scale k * p, масштаб — явный вход)
  rate_inferred_from_payload_type: not_present
  scale_defined_after_inspecting_error: not_present (scale — параметр)
  hdenom_removed_or_weakened: not_weakened (плант доказывает необходимость)
  project_Ferrers_mode_as_source_function: not_used
  selected_transport_or_project_carrier_imported: not_imported
    (единственный импорт — G6N1Satz9SourcePackageInterface)
  F72_1C_bundled: not_bundled
  sorry_admit_typed_hole: none
  target_weakened: none (TARGET_SHAPE дословно, включая точную константу)

GATE:
  ROUNDS: 3 (Cyrillic-идентификатор переименован до первого прогона;
    Complex.norm_real даёт ‖·‖-форму — нужен Real.norm_eq_abs перед
    abs_of_pos; финальный field_simp закрыл равенство сам — ring после
    него был No goals)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1CenterNormalizedSatz9RateTransfer.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1CenterNormalizedSatz9RateTransfer — Build completed successfully (7842 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1CenterNormalizedSatz9RateTransfer.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER_LEAN
NEXT_LOAD_BEARING_GAP: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
