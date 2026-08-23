# SOURCE RECORD — H2A_0 selected Ferrers finite CCM source row lock (Linux-тело за Codex)

```yaml
PRIMARY: H2A_0_SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_LOCK
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 4df7b14a — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 4df7b14a26abee5bcd589d7a5ad04e5e5f2f5523
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен после q3_check перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selectedProlateCofinalSourceDataOfPreAnchorPort finite
  CCM row c_n sourceOrderedCCMRawTransform\" exited 0 — конструктор шелла
  найден (G6N1PreAnchorLimitZeroModeAndSelectedShell:572); машинерия строки
  существует ТОЛЬКО на интерфейсе ProlateCanonicalSourceData
  (D0PstarCCMFiniteSourceResidual, приватные леммы) — специализация на
  selected shell отсутствовала; имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMSourceRow.lean
LEAN_GIT_BLOB: 21c23251f3db4494f9fb8ba06a74ed4c24b8a97a
LEAN_SHA256: 5938530f617e53106abb6912e117d09cabda3fc12ab5e66bbfb384c5564f45d3
LEAN_LINES: 296

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_0_SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.G6N1SelectedFerrersCCMLemma73PreAnchorPort
  - Q3.Proofs.RouteB.LiteralCCMCofinalResidualFloorEnvelopeAndTransformTail

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrersCofinalSourceData
    # def: generic-конструктор на selected data + условный L73.8-порт;
    #   экспонирован ТОЛЬКО потому, что немедленно потребляется строкой ниже
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMRow
    # def: q_{k,j} = c_n(i_k, prolateCombination(P_k), ccmModeFinite N j)
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMRow_apply       # rfl-формула
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMRow_unit        # q* ⬝ᵥ q = 1
  - Q3.RouteB.D0Pstar.sourceOrderedCCMRawTransform_selectedFerrersFiniteCCMRow_eq_rawFplus
    # source-ordered Proposition-59 transform строки = rawFplus шелла, ∀z

PRIVATE_DECLARATIONS:
  - unit_rows_do_not_identify_source_row_plant  # REQUIRED: два разных unit
    #   ряда на Fin 2 — unit-норма не идентифицирует source row
  - selectedModeEquiv / selected_finite_sum_reindex
    / selected_finite_synthesis_inner_identity   # копии (upstream приватны)
  - ccmFiniteSynthesis_selectedFerrersFiniteCCMRow
    # синтез строки = (kTrial_m_N ... : H_m) через проекционную
    #   реконструкцию coe_P_m_N_apply_eq_sum_inner_V_n_m_smul

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMRow_apply:
    - propext
    - Classical.choice
    - Quot.sound
  Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMRow_unit:
    - propext
    - Classical.choice
    - Quot.sound
  Q3.RouteB.D0Pstar.sourceOrderedCCMRawTransform_selectedFerrersFiniteCCMRow_eq_rawFplus:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - SELECTED_FERRERS_COFINAL_SOURCE_SHELL_EXPOSED
    - SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_OBJECT_LOCK
    - SELECTED_FERRERS_FINITE_ROW_TO_RAW_TRANSFORM_CROSSWALK
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "шелл-специализация задана определением из вердикта дословно и
     немедленно потреблена строкой (shell-only alias НЕ создан)"
  - "строка = точная c_n-строка шелла; формула применения — rfl"
  - "unit: синтез строки реконструирует (kTrial_m_N : H_m) через
     P_m_N-проекцию и carrier-reindex; ⟨x,x⟩ = ‖x‖² = 1 через точный
     norm_kTrial_m_N — как предсказано (P_H2A0_2)"
  - "crosswalk: оба transform-а — proposition59RawTransform на общем
     множестве Icc(−N,N) = modeSet; коэффициенты совпадают на множестве
     через ccmModeFiniteEquivIcc.apply_symm_apply; вне множества
     сравнение не требуется (сумма по множеству)"
  - "#print axioms всех трёх публичных теорем"

FORBIDDEN_CHECK:
  shell_only_alias_as_separate_transaction: no (шелл потреблён в том же файле)
  ProlateCanonicalSourceData_substituted: no (всё на selected shell; старая
    машинерия НЕ вызвана через другой интерфейс — приватные леммы
    специализированы локально)
  arbitrary_unit_row_in_place_of_selected: no (плант держит; строка — точная
    c_n-строка)
  tail_shift_moved_or_refitted: no (шелл-конструктор применён как есть)
  new_selected_pair_or_schedule: no
  hmode_hchi_hidden_in_axiom_or_structure: no (порт остаётся параметром P)
  complement_floor_penalty_certificate_Theorem510_bundled: no
  L73_3_to_L73_8_edited: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 3 (LinearMap-коэрция синтеза — simp only с coe_mk по образцу
    upstream; congr на transform-ах уводил в ложную функциональную
    экстенсиональность коэффициентов — заменён на unfold + Finset.sum_congr
    с поэлементным сравнением на множестве; set-абстракция i применилась
    неравномерно после simp — закрыто rfl по defeq.  Предсказанный
    DEPENDENT_SELECTED_TAIL_INDEX_OR_CCM_MODE_CARRIER_NORMAL_FORM сбой
    выстрелил ЧАСТИЧНО: трение — элаборация зависимого индекса/коэрций,
    ноль новой математики — P_H2A0_3 подтверждён)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMSourceRow.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMSourceRow — Build completed successfully (7919 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMSourceRow.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: все три публичные теоремы
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: H2A_0_SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_LOCK_LEAN
NEXT_LOAD_BEARING_GAP: COFINAL_SIMPLE_EVEN_GROUND_SUPPLIER
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
