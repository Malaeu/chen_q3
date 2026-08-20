# SOURCE RECORD — обитатель SelectedProlatePreAnchorData (Linux-тело за Codex)

```yaml
PRIMARY: SELECTED_PROLATE_PREANCHOR_DATA_INHABITANT
DATE: 2026-08-20
BODY: Linux (Claude), по прямому поручению владельца — Codex на лимите до 05:39
TASK: docs/Codex/TASK_2026-08-20_return_briefing_and_preanchor_inhabitant.md (раздел 2)

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: a60f01da4d813c8cb4ade2510fd07c5914c9fe9a
  FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPreAnchorDataInhabitant.lean
  GIT_BLOB: 8d420f8a6e2926f9c10d65480dca41e13ffe97ce
  SHA256: 2a672c771cb806388331ac0b8129949e981720932f5593357593fc339a947527
  LINES: 411

LEDGER:
  CLOSES:
    - SELECTED_PROLATE_PREANCHOR_DATA_INHABITANT
  OPENS: []

PRECOMMITTED_SCHEDULE:
  index: "k ↦ PairIndex ⟨k+2, k+2⟩"
  truncation: "K = 5*(k+2)"
  chosen: до первой попытки доказательства (C09); не подгонялось
  separation: pi ≤ 4 даёт (31/24)(2πm)² ≤ 4K²−20 при K=5m, m≥2 — чистая арифметика

EXPORTED_NAMES:
  D_INHABITANT: Q3.RouteB.D0Pstar.selectedFerrersPreAnchorData
  INDEX_FORMULA: selectedFerrersPreAnchorIndex (k) = ⟨k+2, k+2⟩   # @[simp] rfl-export
  PAIR_FORMULA: selectedFerrersPreAnchorPair (k)                   # @[simp] rfl-export
  PAIR_SPEC: selectedFerrersPreAnchorPair_spec                     # полная 10-конъюнкция свидетеля
  DATA_PAIR_SPEC: selectedFerrersPreAnchorData_pair_spec           # h0/h4 = normalizedPhysicalMode S0/S4
  PROVENANCE: пара при каждом k — Classical.choose ПОВЕРХ доказанного
    exists_modeZero_modeFour_selectedFerrersProductionProlatePair (k+2) (5(k+2));
    никакой другой ProlatePair в файле не строится

NEW_GENERAL_LEMMA:
  prolateCombination_E_star_memLp_of_windowBound:
    зачем: старый поставщик MemLp требовал IsActualProlateModePair,
      которого Ferrers-теорема существования не даёт
    гипотезы: глобальная граница нормы + AESM вместо IsActual;
      обе выведены из непрерывности Ferrers-серии на замкнутом окне
    НЕ открывает вход: обе гипотезы закрыты в этом же файле
      (normalizedPhysicalMode_aestronglyMeasurable, normalizedPhysicalMode_norm_bound)

GATE:
  ROUNDS: 3 (7 ошибок → 1 warning → 0)
  LEAN: lake env lean — EXIT 0
  LAKE_BUILD: Build completed successfully (7831 jobs) — EXIT 0
  Q3_CHECK: scripts/q3_check.sh <file> — "q3_check ok", EXIT 0
  AXIOM_PROFILES: все 9 печатаемых деклараций
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ
  ПЕЧАТАЕМЫЕ: selectedFerrersPreAnchorSeparation, selectedFerrersPreAnchorPair_spec,
    selectedFerrersPreAnchorPair_lambda_eq, normalizedPhysicalMode_aestronglyMeasurable,
    normalizedPhysicalMode_norm_bound, prolateCombination_E_star_memLp_of_windowBound,
    selectedFerrersPreAnchorPair_eStar_memLp, selectedFerrersPreAnchorData,
    selectedFerrersPreAnchorData_pair_spec

FORBIDDEN_RESPECTED:
  G6N1_FILE_UNTOUCHED: true          # зелёный файл не менялся
  NO_CHOOSE_WITHOUT_EXISTENCE: true  # choose только поверх доказанного ∃
  NO_ARBITRARY_PROLATE_PAIR: true    # прецедент-запрет N0-kill соблюдён
  NO_LEMMA73_PORT_STARTED: true      # CCMLemma73PreAnchorPort не тронут
  NO_LEMMA72_RATE_ASSUMED: true
  NO_SOURCE_SCALE_DEFINED: true
  NO_N2_STARTED: true

JUDGE_PREDICTION_P_L73_1:
  statement: "обитателю понадобится дополнительная pair_spec/provenance теорема"
  status: выполнено ЗАРАНЕЕ — pair_spec и data_pair_spec экспортированы сразу

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```

## Что дальше (порядок судьи, без изменений)

1. Судья читает пакет: reducible-экспорты `@[simp] rfl` + `pair_spec` — требование
   «непрозрачная запись недостаточна» выполнено конструкцией.
2. L73.0 (provenance-замок) теперь стоит на поданном пакете.
3. L73.1 (sourceScale из нормировки) — следующий; в этом файле сознательно НЕ начат.
4. Codex после резета: задание в TASK-файле выполнено этим телом; Codex сверяет
   и идёт дальше по разделу 3 (стоп и доклад — актуально и для нас).
