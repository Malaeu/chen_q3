# STATUS: SOURCE_WRITTEN — G6/N1 ROUND-3 STRUCTURAL KERNEL REPAIR WRITTEN; RE-GATE PENDING

```yaml
PRIMARY: G6_N1_PREANCHOR_KERNEL_REPAIR_ROUND3_SOURCE_WRITTEN
PRIMARY_COUNT: 1

REQUEST:
  ID: REQ-2026-08-20-C
  ROUND: 3
  KIND: STRUCTURAL_KERNEL_REPAIR
  ROUND2_REPORT:
    PATH: docs/routeB_bus/LINUX_GATE_G6N1_PREANCHOR_RED_ROUND2_2026-08-20.md
    GIT_BLOB: 95a27c9f611909b0a41722d13e4a19736c0373a7

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  BASE_HEAD: 2f013e59017e4ad35dd9167884b7de3a7600cedd
  PREVIOUS_REPAIR_COMMIT: 02d21ef9f7979e90f9bb1761dc460e631aa1f621
  PREVIOUS_LEAN_BLOB: e34c43decf1df6a9604755e50e14fb24eaf8f300

DELIVERY:
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  LEAN_GIT_BLOB: 5649e3b91545b41898734069e41e87c25630f150
  LEAN_SHA256: 1a7a3b4528ccd10ed3baa9ee8c8bd06b88de9dbd80dfc9f7935052ff15145325
  LEAN_LINES: 623
  SOURCE_RECORD_PATH: docs/routeB_bus/proshka/PROSHKA_SOURCE_RECORD_G6_N1_PREANCHOR_KERNEL_REPAIR_ROUND3_2026-08-20.md
  SOURCE_AND_RECORD_ONE_COMMIT: true

STATUS_FLAGS:
  SOURCE_WRITTEN: true
  KERNEL_VALIDATION: PENDING
  LEAN_PROVED: false
  ROUND2_RED_ACKNOWLEDGED: true
  VERDICT_DEFERRED_UNTIL_GATE: true

ROUND2_GATE:
  ERRORS: 5
  CLEAN_PRINTED_DECLARATIONS: 6
  STRUCTURAL_TIMEOUT:
    theorem: selectedProlateCofinalSourceDataOfPreAnchorPort
    location: 354
  ARITHMETIC_FAILURES:
    - location: 379
      kind: omega_could_not_unfold_opaque_shift
    - location: 389
      kind: omega_could_not_unfold_opaque_shift
  SLOT_ANCHOR_FAILURE:
    location: 441
    goal: centeredXi_0_mul_raw_div_raw_eq_centeredXi_0

CLOSES:
  - CCM_LEMMA_7_3_SELECTED_MUNTZ_LIMIT
  - SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING
OPENS: []

BOUNDARY:
  STATEMENTS_CHANGED: false
  HYPOTHESES_CHANGED: false
  SOURCE_OBJECT_GRAPH_CHANGED: false
  IMPORTS_CHANGED: false
  PUBLIC_SURFACE_CHANGED: false
  EXISTING_ALL_INDEX_LAYER_CHANGED: false
  PAPER_ANALYTICS_REPROVED_IN_LEAN: false
  MAX_HEARTBEATS_INCREASED: false

STRUCTURAL_REPAIR:
  MONOLITHIC_DEPENDENT_RECORD_TERM_REMOVED: true
  PRIVATE_KERNEL_FLOORS:
    - preAnchorTailStart
    - preAnchorTailStart_spec
    - preAnchorTailShift
    - preAnchorTailStart_le_shift
    - preAnchorTailIndex_le_shift
    - preAnchorTailShift_tendsto
    - preAnchorTailIndex
    - preAnchorTailPair
    - preAnchorTail_mCofinal
    - preAnchorTail_nCofinal
    - preAnchorTail_lambda_eq
    - preAnchorTail_eStar_memLp
    - preAnchorTail_gwin_zero_ne
    - preAnchorTail_trialNonzero
    - preAnchorTail_rawZeroNonzero
    - preAnchorTailSourceScale
    - preAnchorTailSourceScale_ne
    - preAnchorTail_muntzLimit
  PUBLIC_CONSTRUCTOR:
    name: selectedProlateCofinalSourceDataOfPreAnchorPort
    form: SMALL_NAMED_FIELD_ASSEMBLY
  OMEGA_ISOLATION:
    count: 2
    locations:
      - preAnchorTailStart_le_shift
      - preAnchorTailIndex_le_shift
    each_goal_unfolds_to:
      - start_le_start_add_k
      - k_le_start_add_k
  SLOT_ANCHOR_REPAIR:
    theorem: SelectedProlateCofinalSourceData.centeredPstar_zero
    engine: div_mul_cancel₀
    denominator_witness: D.rawZeroNonzero_k

EXTERNAL_NAME_AUDIT:
  NEW_MATHLIB_NAMES_INTRODUCED:
    - div_mul_cancel₀
  VERIFIED_EXTERNAL_NAMES:
    div_mul_cancel₀:
      SOURCE_FILE: q3.lean.aristotle/Q3/Proofs/S_K_small.lean
      SOURCE_LINE: 55
      STATUS: SOURCE_VERIFIED
  UNVERIFIED_EXTERNAL_NAME: []

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
  - theorem: preAnchorFullMellinCoordinate_zero_eq_sqrtL_mul_innerV0
    location: scalar_field_simp
    inherited_from_round2: true
  - theorem: preAnchorTailStart_le_shift
    location: unfold_preAnchorTailShift_then_omega
  - theorem: preAnchorTailIndex_le_shift
    location: unfold_preAnchorTailShift_then_omega
  - theorem: preAnchorTail_muntzLimit
    location: eventual_transport_then_simpa_only
  - theorem: SelectedProlateCofinalSourceData.centeredPstar_zero
    location: exact_div_mul_cancel₀

REGISTERED_PREDICTIONS:
  P_G6N1_R3_1:
    statement: named private theorem floors remove the deterministic kernel timeout
    probability: 0.81
    fate: PENDING
  P_G6N1_R3_2:
    statement: both isolated arithmetic floors compile after explicit shift unfolding
    probability: 0.96
    fate: PENDING
  P_G6N1_R3_3:
    statement: div_mul_cancel₀ closes the exact slotAnchor scalar identity
    probability: 0.98
    fate: PENDING
  P_G6N1_R3_4:
    statement: every printed declaration has exactly the standard axiom triple
    probability: 0.76
    fate: PENDING

PRIOR_PREDICTION_FATES:
  P_G6N1_C0_IMPORT_AND_AUTOIMPLICIT_FIREWALL: CONFIRMED
  P_G6N1_C1_EXPLICIT_SQRT_CANCELLATION: CONFIRMED
  P_G6N1_C2_EXPLICIT_DEPENDENT_ARGUMENTS: CONFIRMED
  P_G6N1_C3_CHOOSE_AND_DIRECT_TRANSPORT_COMPILE: REFUTED_BY_TIMEOUT_AND_OMEGA
  P_G6N1_C4_ALL_STANDARD_TRIPLE: REFUTED_BY_MAIN_SELF_AXIOM_AND_SLOTANCHOR_SORRYAX

LIKELIEST_FAILURE:
  code: DEPENDENT_RECORD_FIELD_DEFINITIONAL_EQUALITY_OR_EVENTUAL_TRANSPORT
  response: repair_only_the_exact_named_floor_reported_by_the_kernel

VERIFICATION_HANDOFF:
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake env lean Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake build Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell
  - WORKDIR: REPO_ROOT
    COMMAND: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean

SUCCESS_CODE: G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL_LEAN
FAILURE_CODE: G6_N1_PREANCHOR_KERNEL_REPAIR_ROUND3_MISMATCH

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

Round 2 is accepted as a structural failure of one proof term, not as a mathematical failure.  Six printed declarations, including both nonvanishing keys, already reached the standard axiom profile.  Round 3 does not change any theorem statement or source object.  It replaces one dependent monolith with kernel-sized named floors, isolates the two arithmetic goals, and proves the anchor by the exact field cancellation theorem.

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

A green gate closes only the two named N1 catalog inputs.  It does not prove the remaining N2 compact-decay supplier, does not promote Route B, and does not claim RH.
