# LINUX SOURCE RECORD — GOAL058 SELECTED FERRERS GROUND PARITY REALIFICATION

```yaml
STATUS_MAX: SOURCE_WRITTEN
TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_PARITY_REALIFICATION_ASSEMBLY
AUTHORIZATION: PROSHKA_VERDICT_REQ_2026_08_26_N (commit 431e3fc3)
MODE: LEAN_SOURCE_TRANSACTION
BODY: Linux-Claude
GRANT: LINUX_STANDING_GRANT_2026-08-25
COMMIT: FILLED_AT_COMMIT_TIME_SAME_COMMIT_AS_THIS_RECORD
LEAN_FILES:
  - LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersGroundParityRealification.lean
    CHANGE: new_file
    LEAN_GIT_BLOB: e6c087de917767e5d48bb34bc53ef78befdbdea5
    SHA256: 3bc7fd829c055ae4e26da50c9bd1f3d62437afd3c0c4bac96a2c2d45f10f6a34
    LINES: 644
SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_GROUND_PARITY_REALIFICATION_2026-08-26.md
PUBLIC_SURFACE:
  - selectedFerrersGround_exists_realEtaNormalizedEvenRepresentative_of_sectorFloor
EXPECTED_AXIOM_PROFILES:
  selectedFerrersGround_exists_realEtaNormalizedEvenRepresentative_of_sectorFloor:
    - propext
    - Classical.choice
    - Quot.sound
CLOSES:
  - SELECTED_FERRERS_GROUND_PARITY_SELECTION
  - SELECTED_FERRERS_GROUND_LINE_REALIFICATION
  - SELECTED_FERRERS_GROUND_ETA_NORMALIZATION
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_GROUND_CANONICAL_FAMILY_THEOREM510_AND_TRACKING_ASSEMBLY
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
VERIFICATION_HANDOFF:
  - "WORKDIR q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersGroundParityRealification.lean"
  - "WORKDIR q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersGroundParityRealification"
  - "WORKDIR repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersGroundParityRealification.lean"
NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_GROUND_CANONICAL_FAMILY_THEOREM510_AND_TRACKING_ASSEMBLY
UNVERIFIED_EXTERNAL_NAME: none
NEW_ANALYTIC_INPUT: none
```

## Публичная теорема

`selectedFerrersGround_exists_realEtaNormalizedEvenRepresentative_of_sectorFloor`
— из удержанного пола нечётного сектора при точном рэлеевском сдвиге и
литерального пола дополнения строит для выбранной конечной CCM-ячейки
вещественный, отражательно-чётный, η-нормированный простой нижний
собственный вектор и один ненулевой комплексный скаляр, связывающий его
с комплексным грунтовым вектором.

Входы — ровно два пола плюс `0 < beta0`, `0 < beta`, `2 ≤ m`, `1 ≤ N`.
Гипотезы `heta` нет; отождествления пробной строки с грунтовой нет;
квоциентный базис не вводится; численных данных нет.

## Конструкция (семь шагов вердикта N)

1. **Извлечение грунта** (`gpr_ground_extraction`): общий приёмник
   `hermitian_unit_trialLine_complementFloor_gives_ground_gap_tracking`
   на литеральных объектах ячейки — матрица, единичная пробная строка,
   точный рэлеевский сдвиг, точный остаток. Реконструирована приватная
   лемма вещественности эрмитовой квадратичной формы.
2. **Дихотомия чётности** (`gpr_parity_dichotomy`): коммутирование
   `sourceCCMFiniteMatrix_commutes_ccmComplexReflectionMatrix` плюс
   положительный зазор дают `J·ξ = ±ξ`. Только дихотомия — чётность здесь
   НЕ выводится (контрпример `commute_simple_ground_does_not_force_even`
   охраняет этот шаг).
3. **Смерть нечётной ветви** (`gpr_ground_is_even`): пол нечётного сектора,
   применённый к самому грунтовому вектору, даёт `β₀ ≤ ε − a`; но
   `ε ≤ a` из нижней рэлеевской границы на единичной пробной строке;
   противоречие с `0 < β₀`. **Строгость нечётного сектора выведена, а не
   постулирована** — ровно как указал вердикт.
4. **Реализация** (`gpr_re_im_eigen`, `gpr_re_or_im_ne_zero`,
   `gpr_parts_even`): `sourceCCMFiniteMatrix` — поэлементная
   комплексификация вещественной `ccmWeilMatFinite`, поэтому вещественная
   и мнимая части грунта сами вещественные собственные векторы при том же
   ε; из `‖ξ‖ = 1` одна из них ненулевая; чётность переносится покоординатно.
5. **Грунтовая линия** (`gpr_complex_line`, `gpr_real_proportional`):
   зазор загоняет любой собственный вектор уровня ε на грунтовую линию;
   два вещественных собственных вектора пропорциональны над ℝ.
6. **Простота** (`gpr_mem_eigenspace_iff`,
   `gpr_real_eigenspace_finrank_one`): `finrank ℝ (eigenspace ε) = 1`
   через `finrank_eq_one_iff_of_nonzero'`. Простота ВЫВЕДЕНА из зазора.
7. **Сборка**: чётность установлена ДО η-нормировки, затем
   `exists_ccmEta_normalized_even_eigenvector_of_simple_even_eigenvector`
   закрывает нормировку; вещественная нижняя рэлеевская граница получена
   кастом; скаляр `c = t · ⟨ξ, часть⟩ ≠ 0` экспортирован.

## Разорванный круг

`ccmEigenvector_even_of_simple_eigenspace_and_normalized` требует
η-нормировку ради чётности; `ccmEtaFinite_dotProduct_ne_zero_of_even_simple_eigenvector`
требует чётность ради η-невырождения. Круг разорван шагом 3: чётность
получена из пола нечётного сектора независимо от нормировки.

## Гейт

Прямой Lean: EXIT 0. `lake build`: OK, 7924 jobs. Hole-scan: 0 совпадений.
`scripts/q3_check.sh`: `q3_check ok`. `#print axioms` публичной теоремы:
только `propext, Classical.choice, Quot.sound`.

SUCCESS_CODE: SELECTED_FERRERS_GROUND_PARITY_REALIFICATION_NORMALIZATION_LEAN
