# STATUS: SOURCE_WRITTEN — G6/N1 ROUND-4 TAIL-LIMIT KERNEL FLOOR SPLIT WRITTEN; RE-GATE PENDING

```yaml
PRIMARY: G6_N1_PREANCHOR_KERNEL_REPAIR_ROUND4_SOURCE_WRITTEN
PRIMARY_COUNT: 1

REQUEST:
  ID: REQ-2026-08-20-C
  ROUND: 4
  KIND: STRUCTURAL_KERNEL_REPAIR
  ROUND3_REPORT:
    PATH: docs/routeB_bus/LINUX_GATE_G6N1_PREANCHOR_RED_ROUND3_2026-08-20.md
    GIT_BLOB: 90037a55ff6337d24fb6060d1ac3984cd34ea299

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  BASE_HEAD: 176066eee1781f2bcc8703f118b2b8fe7737b02b
  PREVIOUS_REPAIR_COMMIT: cfee730a43d5066d448feca32d0ee04c8b9514fe
  PREVIOUS_LEAN_BLOB: 5649e3b91545b41898734069e41e87c25630f150

DELIVERY:
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  LEAN_GIT_BLOB: c552654e2666eafa6bdbe5eac453ac7bdc7a4c67
  LEAN_SHA256: 88cfc9dea2fa24a1f3a93531d402d3d6a95e7c348cffb9d944b1840bc1f94636
  LEAN_LINES: 663
  SOURCE_RECORD_PATH: docs/routeB_bus/proshka/PROSHKA_SOURCE_RECORD_G6_N1_PREANCHOR_KERNEL_REPAIR_ROUND4_2026-08-20.md
  SOURCE_AND_RECORD_ONE_COMMIT: true

STATUS_FLAGS:
  SOURCE_WRITTEN: true
  KERNEL_VALIDATION: PENDING
  LEAN_PROVED: false
  ROUND3_RED_ACKNOWLEDGED: true
  VERDICT_DEFERRED_UNTIL_GATE: true

ROUND3_GATE:
  ERROR_TRAJECTORY: [36, 5, 2]
  CURRENT_ERRORS: 2
  ROOT_FAILURE:
    theorem: preAnchorTail_muntzLimit
    kind: KERNEL_DETERMINISTIC_TIMEOUT
  DOWNSTREAM_FAILURE:
    declaration: selectedProlateCofinalSourceDataOfPreAnchorPort
    kind: UNKNOWN_PRIVATE_CONSTANT
  NO_SORRYAX_IN_PRINTS: true
  STANDARD_TRIPLE_PRINTS: 8
  CONSTRUCTOR_SELF_AXIOM_FROM_FAILED_PRIVATE_FLOOR: true

CLOSES:
  - CCM_LEMMA_7_3_SELECTED_MUNTZ_LIMIT
  - SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING
OPENS: []

BOUNDARY:
  STATEMENTS_CHANGED: false
  HYPOTHESES_CHANGED: false
  IMPORTS_CHANGED: false
  PUBLIC_SURFACE_CHANGED: false
  SOURCE_OBJECT_GRAPH_CHANGED: false
  NORMALIZATION_CHANGED: false
  COFINAL_SCHEDULE_CHANGED: false
  EXISTING_ALL_INDEX_LAYER_CHANGED: false
  PAPER_ANALYTICS_REPROVED_IN_LEAN: false
  MAX_HEARTBEATS_INCREASED: false

STRUCTURAL_REPAIR:
  REMOVED_FROM_HEAVY_FLOOR:
    - tendstoLocallyUniformlyOn_iff_forall_isCompact expansion
    - compact-set quantifier reconstruction
    - local hbase term
    - local htail term
  ADDED_PRIVATE_KERNEL_FLOORS:
    - tendstoLocallyUniformlyOn_atTop_precomp
    - preAnchorTail_muntzLimit_shifted
    - preAnchorTail_muntzLimit_indexed
  FINAL_PRIVATE_FLOOR:
    name: preAnchorTail_muntzLimit
    form: ONE_SIMPA_REFERENCE_TO_INDEXED_FLOOR
  GENERIC_PRECOMPOSITION:
    level: DEFINING_FILTER_LEVEL
    operation: COFINAL_PULLBACK
    new_analytic_input: false

EXTERNAL_NAME_AUDIT:
  NEW_MATHLIB_NAMES_INTRODUCED: []
  UNVERIFIED_EXTERNAL_NAME: []
  PROJECT_DECLARATIONS_REUSED:
    - Q3.RouteB.D0Pstar.CCMLemma73PreAnchorPort.convergence
    - Q3.RouteB.D0Pstar.preAnchorTailShift_tendsto

PUBLIC_SURFACE:
  DEFINITIONS_AND_STRUCTURES:
    - Q3.RouteB.D0Pstar.preAnchorGwinTransformCoordinate
    - Q3.RouteB.D0Pstar.preAnchorFullMellinCoordinate
    - Q3.RouteB.D0Pstar.preAnchorRawTransformCoordinate
    - Q3.RouteB.D0Pstar.SelectedProlatePreAnchorData
    - Q3.RouteB.D0Pstar.CCMLemma73PreAnchorPort
    - Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData
    - Q3.RouteB.D0Pstar.selectedProlateCofinalSourceDataOfPreAnchorPort
    - Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.rawFplus
    - Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.muntzApproximation
    - Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.centeredPstar
    - Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.canonicalApproximation
  PRINTED_THEOREMS:
    - Q3.RouteB.D0Pstar.preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate
    - Q3.RouteB.D0Pstar.preAnchorGwin_zero_eq_sqrtL_mul_innerV0
    - Q3.RouteB.D0Pstar.trialNonzero_of_preAnchorGwin_zero_ne
    - Q3.RouteB.D0Pstar.preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero
    - Q3.RouteB.D0Pstar.eventually_preAnchorGwin_zero_ne
    - Q3.RouteB.D0Pstar.selectedProlateCofinalSourceDataOfPreAnchorPort
    - Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.muntzApproximation_tendsto_centeredXi
    - Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.canonicalApproximation_slotAnchor
    - Q3.RouteB.D0Pstar.goalG6N1ZeroTarget_nonvanishing_not_free

EXPECTED_AXIOM_PROFILES:
  Q3.RouteB.D0Pstar.preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate: [propext, Classical.choice, Quot.sound]
  Q3.RouteB.D0Pstar.preAnchorGwin_zero_eq_sqrtL_mul_innerV0: [propext, Classical.choice, Quot.sound]
  Q3.RouteB.D0Pstar.trialNonzero_of_preAnchorGwin_zero_ne: [propext, Classical.choice, Quot.sound]
  Q3.RouteB.D0Pstar.preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero: [propext, Classical.choice, Quot.sound]
  Q3.RouteB.D0Pstar.eventually_preAnchorGwin_zero_ne: [propext, Classical.choice, Quot.sound]
  Q3.RouteB.D0Pstar.selectedProlateCofinalSourceDataOfPreAnchorPort: [propext, Classical.choice, Quot.sound]
  Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.muntzApproximation_tendsto_centeredXi: [propext, Classical.choice, Quot.sound]
  Q3.RouteB.D0Pstar.SelectedProlateCofinalSourceData.canonicalApproximation_slotAnchor: [propext, Classical.choice, Quot.sound]
  Q3.RouteB.D0Pstar.goalG6N1ZeroTarget_nonvanishing_not_free: [propext, Classical.choice, Quot.sound]

UNCHECKED_TACTIC_SHAPE:
  - theorem: tendstoLocallyUniformlyOn_atTop_precomp
    location: direct_definition_elimination_and_hshift_eventual_pullback
  - theorem: preAnchorTail_muntzLimit_indexed
    location: simpa_only_two_named_tail_definitions
  - theorem: preAnchorTail_muntzLimit
    location: simpa_only_tail_scale_definition
  MANUAL_BULLET_COUNT_GUESSES: 0
  CONVERT_GOAL_COUNT_GUESSES: 0
  SAFETY_TACTICS_AFTER_POSSIBLE_CLOSURE: 0

REGISTERED_PREDICTIONS:
  P_G6N1_R4_1:
    statement: direct defining-filter precomposition theorem compiles unchanged
    probability: 0.94
    fate: PENDING
  P_G6N1_R4_2:
    statement: shifted and indexed opaque floors remove the deterministic kernel timeout
    probability: 0.84
    fate: PENDING
  P_G6N1_R4_3:
    statement: every printed declaration has exactly the standard axiom triple
    probability: 0.86
    fate: PENDING

PRIOR_PREDICTION_FATES:
  P_G6N1_R3_1_NAMED_FLOORS_REMOVE_TIMEOUT: REFUTED_BY_FINAL_MUNTZ_FLOOR_TIMEOUT
  P_G6N1_R3_2_ISOLATED_ARITHMETIC_FLOORS_COMPILE: CONFIRMED
  P_G6N1_R3_3_DIV_MUL_CANCEL_CLOSES_ANCHOR: CONFIRMED
  P_G6N1_R3_4_ALL_STANDARD_TRIPLE: REFUTED_BY_CONSTRUCTOR_SELF_AXIOM

LIKELIEST_FAILURE:
  code: TENDSTO_PRECOMP_EVENTUAL_TYPE_OR_DEFINITIONAL_SIMPA
  response: repair_only_the_exact_private_floor_reported_by_the_kernel

VERIFICATION_HANDOFF:
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake env lean Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake build Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell
  - WORKDIR: REPO_ROOT
    COMMAND: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean

SUCCESS_CODE: G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL_LEAN
FAILURE_CODE: G6_N1_PREANCHOR_KERNEL_REPAIR_ROUND4_MISMATCH

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED: []

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

Round 3 reduced the transaction to one private convergence floor.  Round 4 preserves the literal source family, normalization and cofinal shift.  It replaces the compact-local proof expansion by a generic filter-level pullback theorem and two opaque definitional floors.  No new supplier, theorem hypothesis, external name or heartbeat budget is introduced.

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

A green gate closes only the two named N1 inputs.  It leaves N2 compact decay open, does not promote Route B and does not claim RH.
