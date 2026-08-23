# SOURCE RECORD — F72.1C selected Ferrers direct cylinder rate (Linux-тело за Codex)

```yaml
PRIMARY: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_WITH_EXPLICIT_PAPER_RATE_INPUT
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict a3675740 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: a3675740207f3e65f6bc67132865125199225825
BASE_HEAD_PROVENANCE: git rev-parse HEAD, снят живым непосредственно перед
  коммитом; совпадает с фактическим родителем (промежуточных коммитов нет)

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selectedFerrers_directCylinderRate ProjectModeData
  constructor satz9_source_bind_closed\" exited 0 — только TEXT_CANDIDATE
  в внешней zeta23-базе (слово constructor как тактика), точного поставщика
  цели нет; конструктор ProjectModeData для выбранной пары ранее не строился."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean
LEAN_GIT_BLOB: eee58ca3139abb8b132945ed9e721be6ae61bf29
LEAN_SHA256: 14f78726cd53c4559eca50d1adcb2d01df021e3e581802a2d0b807a3774f7ee1
LEAN_LINES: 407

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrers_directCylinderRate_of_explicitSatz9RawRates

PRIVATE_DECLARATIONS:
  - exp_linear_bound            # s·e^{−s/c} ≤ c из add_one_le_exp
  - targetD0_bound              # |D0(projArg x)| ≤ 1
  - targetD4_bound              # |D4(projArg x)| ≤ 91 (16·4 + 24·1 + 3·1)
  - selectedProjectModeData0    # ProjectModeData из solution0-полей
  - selectedProjectModeData4    # ProjectModeData из solution4-полей
  - selectedLambda_pos
  - selected_denominator_guard  # eventual guard из расписания, не гипотеза

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrers_directCylinderRate_of_explicitSatz9RawRates:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - F72_0B2_SELECTED_CENTER_NORMALIZED_SOURCE_BIND
    - F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_COMPOSITION
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1 директивы)"
  - "ProjectModeData ×2 из готовых полей: normalizedPhysicalMode_hasDerivAt,
     physicalComplex_flux_hasDerivAt (div_const + indicator_of_mem + ring),
     normalizedPhysicalMode_even, normalizedPhysicalMode_zero_ne,
     physicalComplex_continuousOn_closed (congr через indicator)"
  - "приватные границы D0 ≤ 1 и D4 ≤ 91: s = π·x², |16s²−24s+3| ≤ 16s²+24s+3,
     s·e^{−s} ≤ 1, s²·e^{−s} = (s·e^{−s/2})² ≤ 4, e^{−s} ≤ 1 —
     ровно предписанная схема 64+24+3"
  - "оба eventual-guard'а выведены из selectedFerrersPaperGamma_eq
     (N = ⌈2·rawC/(centre·π)⌉₊), НЕ добавлены гипотезами"
  - "centerNormalizedSatz9Rate_of_scaledFixedModeRate применён к S0 (centre 1,
     bound 1) и S4 (centre 3, bound 91)"
  - "satz9_source_bind_closed на ТЕХ ЖЕ S0/S4, что несут hraw0/hraw4"
  - "анкеры: centerAnchorScalarZero/Four + дикционарные равенства
     pair.h0/h4 = solution.normalizedPhysicalMode; (1/c)·f = 1·(f/c) и
     (3/c)·f = 3·(f/c) чистыми rewrite (one_div_mul_eq_div,
     div_mul_eq_mul_div + mul_div_assoc — без side-условий)"
  - "константы: rawC0(1+1)/(π·1) = 2·rawC0/π и rawC4(3+91)/(π·3) =
     94·rawC4/(3π) — le_of_eq + ring, точно"

FORBIDDEN_CHECK:
  raw_rate_inferred_from_Satz9SourceData: not_present (hraw0/hraw4 — явные
    гипотезы о тех же семействах)
  source_payload_defined_from_selected_project_mode: not_present (S0/S4 —
    универсально квантифицированные аргументы)
  replacement_source_witness_inside_theorem: not_present
  different_witnesses_for_hraw_and_bind: not_present (тот же S0 k / S4 k)
  hdenom_added_as_input: not_added (выведен из расписания)
  D0_D4_bounds_added_as_inputs: not_added (доказаны приватно)
  target_centers_changed: no (1 и 3)
  ordinal_2_identified_with_full_degree_2: not_present
  transport_V3_2_F72_1A0_anchor_files_imported_or_edited: строго два
    предписанных импорта; ничего не редактировано
  F72_3_F72_4_L73_2_bundled: not_bundled
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 2 (единственный содержательный сбой — beta-редукция hcenter-цели
    `(fun x => ...) 0 = ↑1`: rw не входил под нередуцированную лямбду,
    почин через show с явной формой; плюс переименование неиспользуемой
    гипотезы. Flux и ContinuousOn — предсказанный судьёй класс сбоя —
    прошли С ПЕРВОГО прогона)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersDirectCylinderRate — Build completed successfully (7843 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE_CONDITIONAL_LEAN
NEXT_LOAD_BEARING_GAP: F72_3B_FUCHS_SELECTED_EIGENVALUE_DEFECT_RATE_PORT
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
