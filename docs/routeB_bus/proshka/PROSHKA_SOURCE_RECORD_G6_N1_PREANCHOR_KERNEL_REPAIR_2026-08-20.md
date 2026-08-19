# STATUS: SOURCE_WRITTEN — G6/N1 KERNEL REPAIR WRITTEN; RE-GATE PENDING

```yaml
PRIMARY: G6_N1_PREANCHOR_KERNEL_REPAIR_SOURCE_WRITTEN
PRIMARY_COUNT: 1

REQUEST:
  ID: REQ-2026-08-20-C
  KIND: KERNEL_REPAIR
  LINUX_GATE_REPORT: docs/routeB_bus/LINUX_GATE_G6N1_PREANCHOR_RED_2026-08-20.md

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  BASE_HEAD: 7877040a100ff565214b30d69e012d7a26bdfdd9
  FAILED_SOURCE_COMMIT: ccb664b6dc1225e1080a6e09eba8246c4e271a25
  FAILED_SOURCE_BLOB: 04893ae10b51fcec3acc76cce25247b755c2fb6a

DELIVERY:
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  LEAN_GIT_BLOB: e34c43decf1df6a9604755e50e14fb24eaf8f300
  LEAN_SHA256: 9dffa6b961215b2fd3631c5c6c4ac5b830768c1284fb916c0b047ad227b4bdc1
  LEAN_LINES: 493
  SOURCE_RECORD_PATH: docs/routeB_bus/proshka/PROSHKA_SOURCE_RECORD_G6_N1_PREANCHOR_KERNEL_REPAIR_2026-08-20.md
  SOURCE_AND_RECORD_ONE_COMMIT: true

STATUS_FLAGS:
  SOURCE_WRITTEN: true
  KERNEL_VALIDATION: PENDING
  LEAN_PROVED: false
  OLD_RED_GATE_ACKNOWLEDGED: true

RED_GATE:
  ERROR_COUNT: 36
  SORRYAX_THEOREMS: 6
  CLEAN_THEOREM:
    - preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate
  CLASSIFICATION:
    - FIRST_LOCAL_SCALAR_IDENTITY_FAILED
    - IMPLICIT_ARGUMENT_REWRITE_FAILED
    - SOURCE_TYPE_IMPORT_MISSING
    - PROP_TO_DATA_LARGE_ELIMINATION
    - FILTER_PRECOMPOSITION_OVERLOAD_TIMEOUT
    - ZERO_TARGET_PLANT_TACTIC_FAILED

CLOSES:
  - CCM_LEMMA_7_3_SELECTED_MUNTZ_LIMIT
  - SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING
OPENS: []

BOUNDARY:
  STATEMENTS_CHANGED: false
  HYPOTHESES_CHANGED: false
  SOURCE_OBJECT_GRAPH_CHANGED: false
  IMPORTS_CHANGED: true
  IMPORT_CHANGE_ONLY:
    - Q3.Proofs.RouteB.ProlateLayer
  AUTO_IMPLICIT_DISABLED: true
  EXISTING_ALL_INDEX_LAYER_CHANGED: false
  PAPER_ANALYTICS_REPROVED_IN_LEAN: false

REPAIRS:
  R1_SOURCE_TYPE_LOCK:
    action: DIRECT_IMPORT_PLUS_AUTOIMPLICIT_FIREWALL
    effect: ProlatePair_and_prolateCombination_are_source_resolved_before_structure_elaboration
  R2_ZERO_MODE_SCALAR:
    action: EXPLICIT_NONZERO_SQRT_SCALAR_CANCELLATION
    line: 173
    effect: no_post_simp_goal_is_left_unproved
  R3_REWRITE_ARGUMENTS:
    action: ALL_DEPENDENT_THEOREM_ARGUMENTS_SUPPLIED_EXPLICITLY
    effect: no_fresh_MemLp_metavariable_is_generated
  R4_FINITE_PREFIX:
    action: CLASSICAL_CHOOSE_FROM_EVENTUAL_ATTOP
    lines: [363, 367]
    effect: no_large_elimination_from_Prop_into_structure_data
  R5_LOCALLY_UNIFORM_TAIL_SHIFT:
    action: DIRECT_EVENTUAL_TRANSPORT_THROUGH_TENDSTO_SHIFT
    line: 404
    effect: no_overloaded_comp_resolution_or_isDefEq_timeout
  R6_ZERO_TARGET_PLANT:
    action: DIRECT_THRESHOLD_WITNESS_CONTRADICTION
    line: 481
    effect: no_simp_dependency_on_atTop_nonemptiness_normal_form

EXTERNAL_NAME_AUDIT:
  NEW_MATHLIB_NAMES_INTRODUCED: []
  REMOVED_MEMORY_GUESSES:
    - Nat.le_add_left
    - RCLike.inner_apply'
  PROJECT_DECLARATIONS_SOURCE_LOCKED:
    - Q3.Proofs.RouteB.ProlateLayer::ProlatePair
    - Q3.Proofs.RouteB.ProlateLayer::prolateCombination
    - Q3.Proofs.RouteB.D0AnchorFloor::inner_V0_gTrial_m_N_eq

PUBLIC_SURFACE:
  DEFINITIONS_AND_STRUCTURES:
    - preAnchorGwinTransformCoordinate
    - preAnchorFullMellinCoordinate
    - preAnchorRawTransformCoordinate
    - SelectedProlatePreAnchorData
    - CCMLemma73PreAnchorPort
    - SelectedProlateCofinalSourceData
    - selectedProlateCofinalSourceDataOfPreAnchorPort
    - SelectedProlateCofinalSourceData.rawFplus
    - SelectedProlateCofinalSourceData.muntzApproximation
    - SelectedProlateCofinalSourceData.centeredPstar
    - SelectedProlateCofinalSourceData.canonicalApproximation
  THEOREMS:
    - preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate
    - preAnchorFullMellinCoordinate_zero_eq_sqrtL_mul_innerV0
    - preAnchorGwin_zero_eq_sqrtL_mul_innerV0
    - trialNonzero_of_preAnchorGwin_zero_ne
    - preAnchorRawTransformCoordinate_zero_eq_sqrt_mul_c0
    - preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero
    - preAnchorRawTransformCoordinate_zero_ne
    - eventually_preAnchorGwin_zero_ne
    - SelectedProlateCofinalSourceData.centeredPstar_zero
    - SelectedProlateCofinalSourceData.muntzApproximation_tendsto_centeredXi
    - SelectedProlateCofinalSourceData.canonicalApproximation_slotAnchor
    - goalG6N1ZeroTarget_nonvanishing_not_free

PRINTED_AXIOM_TARGETS:
  preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate: [propext, Classical.choice, Quot.sound]
  preAnchorGwin_zero_eq_sqrtL_mul_innerV0: [propext, Classical.choice, Quot.sound]
  trialNonzero_of_preAnchorGwin_zero_ne: [propext, Classical.choice, Quot.sound]
  preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero: [propext, Classical.choice, Quot.sound]
  eventually_preAnchorGwin_zero_ne: [propext, Classical.choice, Quot.sound]
  selectedProlateCofinalSourceDataOfPreAnchorPort: [propext, Classical.choice, Quot.sound]
  SelectedProlateCofinalSourceData.muntzApproximation_tendsto_centeredXi: [propext, Classical.choice, Quot.sound]
  SelectedProlateCofinalSourceData.canonicalApproximation_slotAnchor: [propext, Classical.choice, Quot.sound]
  goalG6N1ZeroTarget_nonvanishing_not_free: [propext, Classical.choice, Quot.sound]

UNCHECKED_TACTIC_SHAPE:
  - line_173_single_goal_field_simp
  - line_443_single_goal_field_simp
  - locally_uniform_eventual_transport_normal_form

REGISTERED_PREDICTIONS:
  P_G6N1_C0:
    statement: direct ProlateLayer import plus autoImplicit false removes the structure/type cascade
    probability: 0.97
    fate: PENDING
  P_G6N1_C1:
    statement: explicit sqrt scalar cancellation closes the zero-mode pointwise identity
    probability: 0.74
    fate: PENDING
  P_G6N1_C2:
    statement: explicit dependent arguments remove both fresh MemLp obligations
    probability: 0.96
    fate: PENDING
  P_G6N1_C3:
    statement: Classical.choose tail extraction and direct eventual transport compile without timeout
    probability: 0.71
    fate: PENDING
  P_G6N1_C4:
    statement: every printed declaration has exactly the standard axiom triple
    probability: 0.61
    fate: PENDING

PRIOR_PREDICTION_FATES:
  P_G6N1_1_COMPILES_UNCHANGED: REFUTED
  P_G6N1_2_STANDARD_TRIPLE_FOR_ALL_PRINTS: REFUTED_BY_RED_GATE
  P_G6N1_3_NO_UNUSED_PUBLIC_HYPOTHESIS: NOT_TESTED_BY_RED_GATE

LIKELIEST_FAILURE:
  code: LEAN_NORMAL_FORM_AT_ZERO_MODE_OR_FILTER_EVENTUAL_TRANSPORT
  response: repair_only_the_exact_returned_normal_form_without_statement_change

GATE:
  WORKDIR_Q3_LEAN:
    - lake env lean Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
    - lake build Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell
  WORKDIR_REPO_ROOT:
    - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  SUCCESS: G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL_LEAN
  FAILURE: G6_N1_PREANCHOR_KERNEL_REPAIR_MISMATCH

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

NEXT_LOAD_BEARING_GAP:
  SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
```

## Repair note

The red result is accepted as evidence against the committed proof script.  It is not reclassified as a mathematical failure: the only theorem that reached the kernel cleanly was the full-Mellin/Gwin crosswalk, while the later type cascade began after the source used `ProlatePair` and `prolateCombination` without a direct import and with automatic implicit synthesis enabled.

The repaired source keeps every theorem statement, every source object, the selected schedule, and both intended catalog closures unchanged.  It changes only the import firewall, explicit dependent arguments, proof terms, and the finite-prefix construction mechanism.

## Verification handoff

### WORKDIR: `q3.lean.aristotle`

```bash
lake env lean \
  Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean

lake build \
  Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell
```

### WORKDIR: repository root

```bash
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
```

A green compile closes only the two named N1 catalog inputs.  It does not prove the remaining N2 compact-decay supplier, does not promote Route B, and does not claim RH.
