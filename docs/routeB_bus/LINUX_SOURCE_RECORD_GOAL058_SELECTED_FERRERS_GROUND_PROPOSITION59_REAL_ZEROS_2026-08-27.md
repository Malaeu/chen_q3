# LINUX SOURCE RECORD — GOAL058 SELECTED FERRERS GROUND PROPOSITION-59 REAL ZEROS

```yaml
STATUS_MAX: SOURCE_WRITTEN
TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_PROPOSITION59_REAL_ZEROS
AUTHORIZATION: PROSHKA_VERDICT_REQ_2026_08_26_N_KERNEL_ADMISSION (commit d79e39bc)
MODE: LEAN_SOURCE_TRANSACTION
BODY: Linux-Claude
GRANT: LINUX_STANDING_GRANT_2026-08-25
COMMIT: FILLED_AT_COMMIT_TIME_SAME_COMMIT_AS_THIS_RECORD
LEAN_FILES:
  - LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersGroundProposition59RealZeros.lean
    CHANGE: new_file
    LEAN_GIT_BLOB: 88d5b2ba19f325113845ce65106b2c00740955eb
    SHA256: 939d3db2c58e819bbb492865e359fb09c8e8d4b583b27b5ac831bb782c53d597
    LINES: 90
SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_GROUND_PROPOSITION59_REAL_ZEROS_2026-08-27.md
PUBLIC_SURFACE:
  - selectedFerrersGround_exists_proposition59_zerosRealOn_of_sectorFloors
EXPECTED_AXIOM_PROFILES:
  selectedFerrersGround_exists_proposition59_zerosRealOn_of_sectorFloors:
    - propext
    - Classical.choice
    - Quot.sound
CLOSES:
  - SELECTED_FERRERS_GROUND_PROPOSITION59_REAL_ZERO_SUPPLIER
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_GROUND_CANONICAL_FAMILY_TRACKING_ASSEMBLY
VERIFICATION_HANDOFF:
  - "WORKDIR q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersGroundProposition59RealZeros.lean"
  - "WORKDIR q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersGroundProposition59RealZeros"
  - "WORKDIR repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersGroundProposition59RealZeros.lean"
NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_GROUND_CANONICAL_FAMILY_TRACKING_ASSEMBLY
UNVERIFIED_EXTERNAL_NAME: none
NEW_ANALYTIC_INPUT: none
```

## Публичная теорема

`selectedFerrersGround_exists_proposition59_zerosRealOn_of_sectorFloors` —
из ровно тех же входов, что и ратифицированный узел чётности (P, k, β₀, β,
положительности, `2 ≤ m`, `1 ≤ N`, пол нечётного сектора при точном
рэлеевском сдвиге, литеральный пол дополнения), возвращает тот же пакет
свидетелей (ε, ξ_ℂ, ξ_ℝ, c) со всеми конечными грунтовыми полями И
дополнительно:

    ZerosRealOn Set.univ (proposition59CCMTransform (ccmL m) N ξ_ℝ)

## Конструкция (маршрут вердикта, четыре шага)

1. Ратифицированный узел
   `selectedFerrersGround_exists_realEtaNormalizedEvenRepresentative_of_sectorFloor`
   вызывается **ровно один раз**.
2. Его свидетели сохраняются без изменений — второй грунтовой ряд не
   выбирается.
3. Квоциентный базис строится **внутри** через
   `Module.Basis.ofVectorSpace` на факторе
   `(CCMModeFinite N → ℝ) ⧸ ker (toBilin' (ccmShiftedWeilMatFinite m N ε))`.
   Он не является входом теоремы.
4. `Proposition59GroundLagrangeZeroSetBridge` применяется к `ξ_ℝ` с уже
   имеющимися полями (собственность, η-нормировка, нижняя рэлеевская
   граница, простота) и даёт вещественность нулей.

## Что НЕ используется

Ни гипотез residual/floor-ratio, ни компактного трекинга, ни асимптотической
близости для переноса конечной вещественнокорневости, ни отождествления
пробного ряда с грунтовым, ни смены расписания. Никаких заявок на cofinal
H2a, SlotS2, продвижение маршрута или RH.

## Гейт

Прямой Lean: EXIT 0 (зелёный с первой попытки). `lake build`: OK, 7925 jobs.
Hole-scan `sorry|exact?|admit`: 0 совпадений. `scripts/q3_check.sh`:
`q3_check ok`. `#print axioms`: только `propext, Classical.choice, Quot.sound`.

SUCCESS_CODE: SELECTED_FERRERS_GROUND_PROPOSITION59_REAL_ZEROS_LEAN
