# LINUX SOURCE RECORD — GOAL058 TRACKED GROUND POINTWISE FLOOR AND EVENTUAL TAIL REINDEX

```yaml
STATUS_MAX: SOURCE_WRITTEN
TASK_ID: GOAL058_SELECTED_FERRERS_TRACKED_GROUND_EVENTUAL_TAIL_REINDEX
AUTHORIZATION: PROSHKA_VERDICT_2026_08_27_TRACKED_GROUND_SAME_WITNESS_ADMISSION_AND_TAIL_REINDEX (commit f4243db5)
MODE: LEAN_SOURCE_TRANSACTION
BODY: Linux-Claude
GRANT: LINUX_STANDING_GRANT_2026-08-25
COMMIT: FILLED_AT_COMMIT_TIME_SAME_COMMIT_AS_THIS_RECORD
LEAN_FILES:
  - LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean
    CHANGE: append_only_pointwise_floor_layer
    DIFF_NUMSTAT: "361 insertions, 0 deletions"
    LEAN_GIT_BLOB: 0a1d46404872a96c7e0ecdab295103c7ff9b500a
    SHA256: 2d219a5cc23cb290a41d3aaf22fc83c7f69c84d5e6f4b68556d41f67e354db6f
    LINES: 1029
  - LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTailReindex.lean
    CHANGE: new_file
    LEAN_GIT_BLOB: 2ba30bb0673ced5eb9b9ba2f6a49ff3f8005f7e5
    SHA256: 58264c73ab71b5d0c04da8c7d46d9bb39869a06475b481ff54e420d8e38aa4b9
    LINES: 114
SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_TRACKED_GROUND_TAIL_REINDEX_2026-08-27.md
PUBLIC_SURFACE:
  - selectedFerrersTrackedGroundEigenvalueAt
  - selectedFerrersTrackedGroundVectorAt
  - selectedFerrersTrackedGroundVectorAt_spec
  - selectedFerrersTrackedGroundOverlapAt
  - selectedFerrersTrackedGroundScaleAt
  - selectedFerrersTrackedGroundTransformAt
  - selectedFerrersTrackedGroundTransformAt_realZeros_and_pointwiseTracking_of_sectorFloors
  - selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors
EXPECTED_AXIOM_PROFILES:
  ALL_PUBLIC_THEOREMS:
    - propext
    - Classical.choice
    - Quot.sound
CLOSES:
  - SELECTED_FERRERS_TRACKED_GROUND_EVENTUAL_FLOOR_API_SEAM
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_GROUND_COFINAL_RATE_ASSEMBLY
VERIFICATION_HANDOFF:
  - "WORKDIR q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean"
  - "WORKDIR q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersTrackedGroundTransform"
  - "WORKDIR q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTailReindex.lean"
  - "WORKDIR q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersTrackedGroundTailReindex"
  - "WORKDIR repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean"
  - "WORKDIR repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTailReindex.lean"
NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_GROUND_COFINAL_RATE_ASSEMBLY
UNVERIFIED_EXTERNAL_NAME: none
NEW_ANALYTIC_INPUT: none
EXISTING_PUBLIC_STATEMENTS_CHANGED: false
HONEST_LIMITATION: INDEX_PAIR_SCALE_RECEIPTS_ARE_DEFINITIONAL_SEE_PROSE
```

## Что закрывает узел

Судья указал шов, которого не было в моей записи: названные ранее объекты
принимают ГЛОБАЛЬНОЕ семейство полов `∀ j`, тогда как источник поставляет
пол лишь ЭВЕНТУАЛЬНО. Выдумать доказательства на конечном префиксе нельзя,
отбросить его молча — тоже.

Узел закрывает шов двумя слоями:

1. **Поточечный слой** (append-only в существующий файл): объекты
   `...At`, чья конструкция потребляет пол ТОЛЬКО в текущей ячейке, и
   теорема
   `selectedFerrersTrackedGroundTransformAt_realZeros_and_pointwiseTracking_of_sectorFloors`
   с тем же математическим содержанием, что у глобальной версии.
   Ни одна существующая формулировка не изменена (361 вставка, 0 удалений).

2. **Хвостовой слой** (новый файл): из эвентуальных полов, эвентуального
   пола нечётного сектора и эвентуального `ratio < 1` берутся пороги,
   `k₀ := max`, и возвращается ОДИН прекоммитированный аддитивный сдвиг
   `φ n = n + k₀` со строгой монотонностью, кофинальностью и — в каждом
   `φ n` — обоими конечными выводами для поточечной трансформы.

Один и тот же хвост несёт и вещественность нулей, и оценку: разные хвосты
для двух выводов запрещены вердиктом и не использованы.

## Честное ограничение

Три равенства-квитанции (`index`, `pair`, `sourceScale` в сдвинутых точках)
доказаны **определительно** (`fun _ => rfl`), поскольку шелл один и тот же и
сдвиг применяется к нему же — второго шелла, второй диагонали или
альтернативного источника в узле нет.

Это верно, но содержательной связи с исходным pre-anchor семейством такие
равенства не несут. Если требуется именно она, её даёт отдельное уточнение
через уже доказанную квитанцию шелла
`selectedProlateCofinalSourceDataOfPreAnchorPort_exists_cofinal_reindex`.
Тавтологию за содержание я не выдаю и предлагаю уточнение отдельным узлом,
если судья сочтёт его нужным.

## Гейт

Прямой Lean обоих файлов: EXIT 0. `lake build`: OK, 7928 jobs. Hole-scan:
0 совпадений в обоих. `scripts/q3_check.sh`: `q3_check ok` на оба.
`#print axioms`: только `propext, Classical.choice, Quot.sound`.
Diff-аудит существующего файла: 361 вставка, 0 удалений.

## Ловушка инструмента (для всех пишущих тел)

После append-only правки файла его `.olean` устаревает; зависимый модуль
перестаёт видеть новые объявления до повторного `lake build` этого модуля.
Симптом — «Function expected at …» на свежедобавленном имени.

SUCCESS_CODE: SELECTED_FERRERS_TRACKED_GROUND_EVENTUAL_TAIL_REINDEX_LEAN
