# SOURCE RECORD — L73.8 conditional selected Ferrers CCM Lemma 7.3 pre-anchor port (Linux-тело за Codex)

```yaml
PRIMARY: L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 6e10d992 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 6e10d9925866fd1d415c790cc277e6ad60062a91
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен после q3_check перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"CCMLemma73PreAnchorPort selectedFerrersPreAnchorData
  compact closed substrip helper\" exited 0 — структура порта
  (G6N1PreAnchorLimitZeroModeAndSelectedShell:275), data-record с
  simp-экспортами, компакт-хелпер найдены; каталожный GAP шаг 12
  GOAL057_CONTINUUM_NUMERATOR_BRIDGE — целевой; дубликатов конструктора нет."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCCMLemma73PreAnchorPort.lean
LEAN_GIT_BLOB: 8ca9276b39a16dcf9c6e38c46eb89ba810d9c334
LEAN_SHA256: 07654e40a15fdfa06bf208dfe10024f08bfdc601080a78f55a7183820829748c
LEAN_LINES: 141

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.G6N1SelectedFerrersClosedSubstripMellinConvergence
  - Q3.Proofs.RouteB.D0CriticalStripCompactBound

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
    # УСЛОВНЫЙ конструктор (hmode, hχ) → CCMLemma73PreAnchorPort
    #   selectedFerrersPreAnchorData; безусловный порт НЕ объявлен —
    #   Satz-9/Fuchs-входы не спрятаны ни в структуру, ни в аксиому

PRIVATE_DECLARATIONS:
  - openStrip_not_contained_in_fixed_closedSubstrip_plant  # REQUIRED, дословно из вердикта

FIELDS:
  sourceScale: selectedFerrersLemma73SourceScale        # существующий, не менялся
  sourceScale_ne: selectedFerrersLemma73SourceScale_ne  # существующий поставщик
  convergence: "tendstoLocallyUniformlyOn_iff_forall_isCompact
    (CanonicalRHRoute.isOpen_centeredCriticalStrip) → на каждом компакте K:
    compact_subset_centeredCriticalStrip_contained_in_closed_substrip даёт
    строгую закрытую подполосу σ < 1/2; L73.7-теорема на ней; сужение на K;
    simp-экспорты selectedFerrersPreAnchorData_index/_pair"

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - CCM_LEMMA_7_3_PREANCHOR_PORT_FROM_MODE_AND_CHI_RATES
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "плант исполнен ДО конструктора (пункт 2)"
  - "sourceScale = существующий factor-four масштаб (пункт 3)"
  - "sourceScale_ne = существующая теорема неисчезания (пункт 4)"
  - "TendstoLocallyUniformlyOn развёрнут через compact-subset эквивалентность
     (пункт 5)"
  - "для каждого компакта K — одна строгая закрытая подполоса из
     существующей компактности (пункт 6)"
  - "L73.7-теорема сужена с подполосы на K (пункт 7)"
  - "переписаны только точные reducibility-экспорты
     selectedFerrersPreAnchorData_index/_pair (пункт 8)"
  - "#print axioms публичного конструктора (пункт 9)"

FORBIDDEN_CHECK:
  unconditional_port_without_hmode_hchi: not_declared
  hmode_hchi_as_port_fields: no (порт-структура не менялась)
  satz9_or_fuchs_as_axiom: no
  one_sigma_for_whole_open_strip: no (per-compact; плант держит)
  selectedFerrersPreAnchorData_changed: no
  selectedFerrersLemma73SourceScale_changed: no
  schedule_changed: no
  SelectedProlateCofinalSourceData_constructed_here: no
  theorem510_H2a_H2b_roof_bundled: no
  L73_3_to_L73_7_edited: no
  route_promotion_or_RH_claimed: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 1 (KERNEL GREEN с первого прогона; предсказанный
    TENDSTO_LOCALLY_UNIFORMLY_ON_COMPACT_RESTRICTION_OR_STRUCTURE_REWRITE
    сбой НЕ выстрелил — вердиктный скелет скомпилировался дословно,
    единственная адаптация: квалификация
    CanonicalRHRoute.isOpen_centeredCriticalStrip)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersCCMLemma73PreAnchorPort.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersCCMLemma73PreAnchorPort — Build completed successfully (7858 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersCCMLemma73PreAnchorPort.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILE_OBSERVED: [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: L73_8_SELECTED_FERRERS_CCM_LEMMA73_PREANCHOR_PORT_CONDITIONAL_LEAN
NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_COFINAL_SOURCE_SHELL_BIND_OR_RETURN_TO_H2A_FRONT
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
