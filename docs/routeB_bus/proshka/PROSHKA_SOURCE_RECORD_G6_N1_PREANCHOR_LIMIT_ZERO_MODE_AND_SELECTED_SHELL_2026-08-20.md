# STATUS: SOURCE_WRITTEN — G6/N1 PRE-ANCHOR LIMIT, EXACT ZERO MODE, AND ADDITIVE SELECTED SHELL AWAIT KERNEL GATE

```yaml
PRIMARY: G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL_SOURCE_WRITTEN
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  OWNER_INPUT_PIN: d4f4f4d103f2d7ca662a50d65ffcd2cbed789cc1
  BASE_HEAD: fa7d248e7b66eabe0eb21efee22e9d5fbcd40910
  REBASED_OVER_CONCURRENT_DOCS_ONLY_COMMITS: true

DELIVERY:
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  LEAN_GIT_BLOB: 04893ae10b51fcec3acc76cce25247b755c2fb6a
  LEAN_SHA256: 920ae5d1090f53e822d967b04d366be95a43d9024b516b8f52da08faf27ae7f7
  LEAN_LINES: 467
  SOURCE_RECORD_PATH: docs/routeB_bus/proshka/PROSHKA_SOURCE_RECORD_G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL_2026-08-20.md
  SOURCE_AND_RECORD_ONE_COMMIT: true

STATUS_FLAGS:
  SOURCE_WRITTEN: true
  KERNEL_VALIDATION: PENDING
  LEAN_PROVED: false
  PAPER_ANALYTICS_REPROVED_IN_LEAN: false

CLOSES:
  - CCM_LEMMA_7_3_SELECTED_MUNTZ_LIMIT
  - SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING
OPENS: []

VERIFIER_SPLIT:
  CCM_LEMMA_7_3_ANALYTIC_LIMIT:
    SCOPE: COFINAL_FAMILY
    VERIFIER: PAPER
    PROJECT_ROLE: EXACT_PREANCHOR_TYPED_PORT
  ZERO_MODE_AND_FINITE_NONVANISHING:
    SCOPE: COFINAL_FAMILY
    VERIFIER: CONDITIONAL_UNTIL_GATE
  SELECTED_SHELL_AND_ANCHOR:
    SCOPE: COFINAL_FAMILY
    VERIFIER: CONDITIONAL_UNTIL_GATE

OBJECT_FIREWALL:
  LIMIT_INPUT_USES_PROLATE_CANONICAL_SOURCE_DATA: false
  LIMIT_INPUT_USES_TRIAL_NONZERO: false
  LIMIT_INPUT_USES_CENTRAL_INDEX: false
  LIMIT_INPUT_USES_RAWFPLUS_DENOMINATOR: false
  EXISTING_ALL_INDEX_D0PSTAR_FILES_CHANGED: false
  NEW_SELECTED_TERMINAL_VIEW_ONLY: true

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
    location: L2.inner_def plus integral_const_mul plus one terminal simp
  - theorem: preAnchorRawTransformCoordinate_zero_eq_sqrt_mul_c0
    location: simpa through a local constant CoefficientFamily
  - theorem: selectedProlateCofinalSourceDataOfPreAnchorPort
    location: TendstoUniformlyOn.comp under the locally-uniform compact normal form
  - theorem: SelectedProlateCofinalSourceData.centeredPstar_zero
    location: field_simp may close the only goal

UNVERIFIED_EXTERNAL_NAME:
  - Nat.le_add_left

REGISTERED_PREDICTIONS:
  P_G6N1_1:
    statement: committed source compiles unchanged
    probability: 0.41
    fate: PENDING
  P_G6N1_2:
    statement: every printed declaration has exactly the standard axiom triple
    probability: 0.94
    fate: PENDING
  P_G6N1_3:
    statement: no public hypothesis is reported unused
    probability: 0.81
    fate: PENDING
  LIKELIEST_FAILURE_CLASS:
    TACTIC_SHAPE_OR_FILTER_PRECOMPOSITION_NORMAL_FORM

PLANT:
  NAME: goalG6N1ZeroTarget_nonvanishing_not_free
  DETECTS: NONZERO_TARGET_IS_LOAD_BEARING
  EXPECTED: CLEAN_STANDARD_TRIPLE

VERIFICATION_HANDOFF:
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake env lean Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  - WORKDIR: q3.lean.aristotle
    COMMAND: lake build Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell
  - WORKDIR: REPO_ROOT
    COMMAND: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean

SUCCESS_CODE: G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL_LEAN
FAILURE_CODE: G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL_KERNEL_MISMATCH

NEXT_LOAD_BEARING_GAP:
  SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
```

The source makes the ratified paper limit explicit as `CCMLemma73PreAnchorPort`, then proves the exact zero-mode identity, theorem-generated `TrialNonzero`, theorem-generated finite raw central nonvanishing, finite-prefix extraction, and a terminal selected `CanonicalApproximation ℕ`.  It does not claim that the paper analysis itself was reproved by Lean, and it does not touch the existing all-index D0Pstar layer.
