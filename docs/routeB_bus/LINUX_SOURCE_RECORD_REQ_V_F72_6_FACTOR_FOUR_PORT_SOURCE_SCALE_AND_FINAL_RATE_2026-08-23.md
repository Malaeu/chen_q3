# SOURCE RECORD — F72.6 factor-four port source scale and final rate (Linux-тело за Codex)

```yaml
PRIMARY: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict f9623d8b — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: f9623d8b193d32a6c4311d279411f0bb06452401
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selectedFerrersLemma73SourceScale factor four port
  rate\" exited 0 — только TEXT_CANDIDATE, имени нигде нет, дубликата нет."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean
LEAN_GIT_BLOB: ccc86efd6bb52fb2dace277262e08dbc953600e3
LEAN_SHA256: 53ce931302f59c8f3ae0ba338f1b7696df29748d1ea2d96a2833d81c08fab18c
LEAN_LINES: 125

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrersLemma73SourceScale        # def, = 4 * Lemma72Scale
  - Q3.RouteB.D0Pstar.selectedFerrersLemma73SourceScale_ne
  - Q3.RouteB.D0Pstar.selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates

PRIVATE_DECLARATIONS:
  - factorFour_occurs_exactly_once_plant  # REQUIRED: 1/4≠1 ∧ 4·(1/4)=1 ∧ 16·(1/4)≠1

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrersLemma73SourceScale_ne:
    - propext
    - Classical.choice
    - Quot.sound
  Q3.RouteB.D0Pstar.selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE
    - F72_6_FACTOR_FOUR_PORT_PACKET_RATE
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "def = 4 * selectedFerrersLemma72Scale (пункт 2, boxed-формула дословно)"
  - "ne из 4 ≠ 0 + selectedFerrersLemma72Scale_ne (пункт 3)"
  - "F72.5 вызван на hmode/hχ, получены C и внутренний rate (пункт 4)"
  - "Cport = 4·C выбран до инспекции значений (пункт 5)"
  - "точечное тождество 4sq − 4h = 4(sq − h) через ring (пункт 6)"
  - "norm_mul + ‖4‖ = 4 + точная алгебра 4·(C/λ²) = 4C/λ² (пункт 7)"
  - "#print axioms обе публичные теоремы (пункт 8)"

FORBIDDEN_CHECK:
  explicitCCMLimitH_changed: untouched
  centeredXi_changed: untouched
  factor_four_inserted_into_F72_5: no (F72.5 не редактировался)
  factor_sixteen_inserted: no (плант различает)
  factor_four_hypothesis_added: not_added
  scalar_chosen_from_observed_convergence: no (фиксирован из
    REQ-E quarter-centered-Xi нормировочного аудита, задокументировано)
  quarter_Mellin_theorem_imported_as_substitute: not_imported
  L73_3_L73_5_port_inhabitant_bundled: not_bundled
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 1 — с первого прогона (предсказанный сбой
    POINTWISE_SCALAR_MULTIPLICATION_OR_COMPLEX_NORM_FOUR не выстрелил)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate — Build completed successfully (7848 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: обе публичные декларации
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: F72_6_FACTOR_FOUR_PORT_SOURCE_SCALE_AND_FINAL_RATE_LEAN
NEXT_LOAD_BEARING_GAP: L73_3_SELECTED_FERRERS_ESTAR_WINDOW_MAIN_ERROR
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
