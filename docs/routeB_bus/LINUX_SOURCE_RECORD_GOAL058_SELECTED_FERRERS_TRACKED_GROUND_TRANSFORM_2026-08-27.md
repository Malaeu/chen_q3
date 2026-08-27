# LINUX SOURCE RECORD — GOAL058 SELECTED FERRERS TRACKED GROUND TRANSFORM

```yaml
STATUS_MAX: SOURCE_WRITTEN
TASK_ID: GOAL058_SELECTED_FERRERS_TRACKED_GROUND_TRANSFORM_SAME_WITNESS_LOCK
AUTHORIZATION: PROSHKA_VERDICT_REQ_2026_08_26_N_GROUND_P59_REAL_ZEROS_ADMISSION (commit 2d691796)
MODE: LEAN_SOURCE_TRANSACTION
BODY: Linux-Claude
GRANT: LINUX_STANDING_GRANT_2026-08-25
COMMIT: FILLED_AT_COMMIT_TIME_SAME_COMMIT_AS_THIS_RECORD
LEAN_FILES:
  - LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean
    CHANGE: new_file
    LEAN_GIT_BLOB: 0296bb09885805e78b22183cbf14c70023265d8a
    SHA256: d65c282a2760f63f72008fa974129b18f689dc33279f7791653f692f730469df
    LINES: 668
SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_TRACKED_GROUND_TRANSFORM_2026-08-27.md
PUBLIC_SURFACE:
  - selectedFerrersTrackedGroundEigenvalue
  - selectedFerrersTrackedGroundVector
  - selectedFerrersTrackedGroundVector_spec
  - selectedFerrersTrackedGroundOverlap
  - selectedFerrersTrackedGroundResidualFloorRatio
  - selectedFerrersTrackedGroundScale
  - selectedFerrersTrackedGroundTransform
  - selectedFerrersTrackedGroundTransform_realZeros_and_pointwiseTracking_of_sectorFloors
EXPECTED_AXIOM_PROFILES:
  selectedFerrersTrackedGroundTransform_realZeros_and_pointwiseTracking_of_sectorFloors:
    - propext
    - Classical.choice
    - Quot.sound
CLOSES:
  - SELECTED_FERRERS_GROUND_CANONICAL_FAMILY_SAME_WITNESS_LOCK
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_GROUND_COFINAL_RATE_ASSEMBLY
VERIFICATION_HANDOFF:
  - "WORKDIR q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean"
  - "WORKDIR q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersTrackedGroundTransform"
  - "WORKDIR repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean"
NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_GROUND_COFINAL_RATE_ASSEMBLY
UNVERIFIED_EXTERNAL_NAME: none
NEW_ANALYTIC_INPUT: none
SECOND_GROUND_ROW_CHOSEN: false
```

## Публичная теорема

`selectedFerrersTrackedGroundTransform_realZeros_and_pointwiseTracking_of_sectorFloors`
— для ОДНОЙ названной функции `selectedFerrersTrackedGroundTransform`
доказаны оба конечных свойства:

1. `ZerosRealOn Set.univ` — весь набор нулей вещественный;
2. точная поточечная оценка против `centeredPstar` отобранного шелла:
   `‖tracked z − centeredPstar z‖ ≤ ‖Ξ(0)/rawFplus(0)‖ · kernelL2 z · √ratio`.

Входы: те же, что у ратифицированного узла чётности, плюс `hratio < 1`.

## Замок свидетеля — почему он настоящий

Отслеживаемый комплексный грунтовой вектор и вещественный η-нормированный
представитель приходят из ДВУХ независимых `Classical.choose`. Фраза «то же
простое основное состояние» замком не является, поэтому доказано:

1. **Равенство собственных значений** (`gtt_eigenvalue_unique` в общем виде,
   в теореме — двумя односторонними оценками БЕЗ нормировки):
   комплексное нижнее свойство отслеживаемого пакета, применённое к
   комплексификации вещественного представителя, даёт `ε_t ≤ ε₂`;
   вещественное нижнее свойство узла P59, применённое к ненулевой
   вещественной или мнимой части отслеживаемого вектора (она сама
   собственная — `gtt_re_im_eigen`), даёт `ε₂ ≤ ε_t`.
2. **Общая линия** (`gtt_ground_line`): положительный зазор загоняет любой
   собственный вектор уровня `ε` на грунтовую линию, откуда
   `ξ_ℝ = α · ξ_tracked` с `α ≠ 0` (иначе `ξ_ℝ = 0` против η-нормировки).

## Обращённые полюсные метки сняты чётностью

`sourceOrderedCCMCoefficient` берёт прямую метку, `proposition59CCMCoefficient`
— обращённую `−k`. Для отражательно-ЧЁТНОГО вещественного представителя оба
семейства совпадают на всём носителе (`gtt_coefficient_crosswalk`), откуда

    sourceOrderedCCMRawTransform L N ξ_ℝ z = proposition59CCMTransform L N ξ_ℝ (−z)

(`gtt_transform_crosswalk`). Производственное отражение `−z` остаётся явным;
вещественность нулей переносится через него (`gtt_zerosRealOn_neg`) и через
ненулевой скаляр (`zerosRealOn_of_eq_smul`). Ненулевость скаляра оплачена:
`Ξ(0) ≠ 0`, `rawFplus k 0 ≠ 0` полем шелла, перекрышка `≠ 0` из `hratio < 1`.

## Поточечная оценка

`sourceOrderedCCMRawTransform_sub_projection_le` с единичными
отслеживаемым вектором и строкой, домноженное на `‖Ξ(0)/rawFplus(0)‖`;
слева получается разность с `centeredPstar` через крoссволк строки; справа
`√(1 − |overlap|²) ≤ √ratio` из проективного дефекта.

## Гейт

Прямой Lean: EXIT 0. `lake build`: OK, 7927 jobs. Hole-scan: 0 совпадений.
`scripts/q3_check.sh`: `q3_check ok`. `#print axioms` публичной теоремы:
только `propext, Classical.choice, Quot.sound`.

SUCCESS_CODE: SELECTED_FERRERS_TRACKED_GROUND_TRANSFORM_REAL_ZEROS_AND_TRACKING_LEAN
