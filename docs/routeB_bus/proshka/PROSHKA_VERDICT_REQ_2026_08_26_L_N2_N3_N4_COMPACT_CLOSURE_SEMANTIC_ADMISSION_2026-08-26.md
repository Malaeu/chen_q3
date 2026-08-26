# STATUS: PROVED — SELECTED-SHELL N2/N3/N4 COMPACT CLOSURE SEMANTICALLY ADMITTED; H2a IS NOW THE ANALYTIC ROOF WALL
```yaml
PRIMARY: ADMIT_GOAL058_SELECTED_FERRERS_N2_N3_N4_COMPACT_CLOSURE
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-L
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_EXECUTION_FOLLOWUP_OF_REQ_2026_08_26_K
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false
  STALE_OPEN_ENTRY_OBSERVED: REQ-2026-08-21-P_HAS_PRIOR_VERDICT_AND_IS_NOT_REANSWERED

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: 28df2481869eab257cc55420450ab192bec8f7e1
  HEAD_IS_ORIGIN_RH_CLEAN_AT_AUDIT: true
  PARENT_VERDICT_COMMIT: 1473ea0a4b902703112e966b51b4d74f97699dc0
  EXECUTION_COMMIT: 28df2481869eab257cc55420450ab192bec8f7e1
  COMMIT_DELTA:
    commits: 1
    added_files: 2
    modified_files: 1
    deleted_files: 0
  APPEND_ONLY_REINDEX_AUDIT:
    additions: 33
    deletions: 0
    existing_declaration_changed: false

ARTIFACTS:
  source_record:
    path: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_N2_COMPACT_DECAY_ASSEMBLY_2026-08-26.md
    git_blob: 327e4d43ed6c9552b5b0b754bab27adac8d64c74
    reported_sha256: absent_for_source_record
  lean_1:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
    git_blob: 69d9004c034ad6f1cc29ca909780bb6db0a9de33
    reported_sha256: 99199fcc04007e9f61bcac5f776f5da2e8dbb506635fa003b471bcf00f80cdef
    change: APPEND_ONLY_PUBLIC_COFINAL_REINDEX_RECEIPT
  lean_2:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersN2CompactDecayAssembly.lean
    git_blob: e200b829f5e0e7589a0e885e8999781f3fd989a9
    reported_sha256: 190fed60932a6e748bab7e75b9309ac382924a62d5bbbf8d094e6792b81a6356
    change: NEW_FILE

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN_REINDEX: PASS_EXIT_0
  LINUX_REPORTED_LAKE_BUILD_REINDEX: PASS
  LINUX_REPORTED_Q3_CHECK_REINDEX: PASS
  LINUX_REPORTED_LAKE_ENV_LEAN_ASSEMBLY: PASS_EXIT_0
  LINUX_REPORTED_LAKE_BUILD_ASSEMBLY: PASS
  LINUX_REPORTED_Q3_CHECK_ASSEMBLY: PASS
  LINUX_REPORTED_HOLE_SCAN: PASS
  LINUX_REPORTED_AXIOMS:
    selectedProlateCofinalSourceDataOfPreAnchorPort_exists_cofinal_reindex:
      - propext
      - Classical.choice
      - Quot.sound
    centeredXi_neg:
      - propext
      - Classical.choice
      - Quot.sound
    preAnchorProjectedMellinCoordinate_neg_eq_rawTransformCoordinate:
      - propext
      - Classical.choice
      - Quot.sound
    preAnchorRawTransformCoordinate_eq_normalizer_mul_projected:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrersCofinalSlotS2_of_modeChiThetaRates:
      - propext
      - Classical.choice
      - Quot.sound
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_LAKE_BUILD: false
  JUDGE_RERAN_Q3_CHECK: false

RECEIPT_AUDIT:
  SOURCE_RECORD_STARTS_WITH_REQUIRED_YAML: false
  SOURCE_RECORD_COMMIT_FIELD_IS_ACTUAL_SHA: false
  SOURCE_RECORD_CONTAINS_OWN_BLOB_FIELD: false
  LEAN_GIT_BLOBS_PRESENT: true
  LEAN_SHA256_VALUES_REPORTED: true
  CLASSIFICATION: NONFATAL_PROCESS_NONCONFORMITY
  REPAIR_POLICY: VERDICT_SUPPLIES_ACTUAL_COMMIT_AND_GIT_BLOBS_APPEND_ONLY

PUBLIC_SURFACE:
  theorem_1:
    name: selectedProlateCofinalSourceDataOfPreAnchorPort_exists_cofinal_reindex
    role: EXACT_COFINAL_REINDEX_RECEIPT
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  theorem_2:
    name: preAnchorProjectedMellinCoordinate_neg_eq_rawTransformCoordinate
    role: EXACT_FPLUS_ORIENTATION_CROSSWALK
    scope: ABSTRACT
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  theorem_3:
    name: preAnchorRawTransformCoordinate_eq_normalizer_mul_projected
    role: EXACT_FINITE_NORMALIZER_FACTOR
    scope: ABSTRACT
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  theorem_4:
    name: centeredXi_neg
    role: EXACT_CENTERED_XI_REFLECTION
    scope: ABSTRACT
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  theorem_5:
    name: selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates
    role: N2_SELECTED_SHELL_COMPACT_RESIDUAL_DECAY
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  theorem_6:
    name: selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates
    role: N3_SAME_FAMILY_LOCALLY_UNIFORM_LIMIT
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  theorem_7:
    name: selectedFerrersCofinalSlotS2_of_modeChiThetaRates
    role: N4_SLOT_S2_ON_THE_SAME_CANONICAL_APPROXIMATION
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN

SEMANTIC_ADMISSION:
  status: SEMANTICALLY_ADMITTED_AS_EXACT_CONDITIONAL_COFINAL_SUPPLIER
  selected_shell: THEOREM_GENERATED_FINITE_PREFIX_DELETION_OF_LITERAL_FERRERS_PREANCHOR_FAMILY
  one_reindex_function_exposed: true
  reindex_tends_to_atTop: true
  exact_index_equality: true
  exact_pair_equality: true
  exact_sourceScale_equality: true
  exact_center_normalizer_cancellation_before_inequality: true
  raw_transform_orientation: FPLUS_Z_EQUALS_PROJECTED_MELLIN_AT_NEG_Z
  reflected_anchored_main_used_in_N2: true
  reflection_removed_only_by_PROVED_centeredXi_evenness: true
  old_all_index_S_used: false
  hFamily_used: false
  selectedTrialNormalizer_used_as_N2_input: false
  sourceScale_upper_bound_used: false
  inverse_sourceScale_bound_used: false
  new_subsequence_added: false
  free_compact_rate_premise_added: false
  sigma_endpoint_claimed: false
  new_analytic_input: none

N2_CLAIM:
  statement: centered_finite_minus_reflected_Muntz_anchored_main_tends_to_zero_locally_uniformly
  exact_domain: centeredCriticalStrip
  scope: COFINAL_FAMILY
  verifier: LEAN_REPORTED_NOT_JUDGE_RERUN

N3_CLAIM:
  statement: selected_shell_centeredPstar_tends_locally_uniformly_to_centeredXi
  exact_family: same_selectedFerrersCofinalShell_used_by_N2
  scope: COFINAL_FAMILY
  verifier: LEAN_REPORTED_NOT_JUDGE_RERUN

N4_CLAIM:
  statement: SlotS2_holds_for_the_same_selected_shell_canonicalApproximation
  witness_c: one
  witness_gamma: constant_one
  proof_mechanism: uniqueness_of_pointwise_limits_from_cluster_convergence_and_N3
  scope: COFINAL_FAMILY
  verifier: LEAN_REPORTED_NOT_JUDGE_RERUN

SEMANTIC_GUARDS:
  C04_SAME_COORDINATES_TWO_LAWS: PASS_EXACT_INDEX_PAIR_SCALE_RECEIPT
  C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT: PASS_ONLY_FINITE_PREFIX_DELETION_NO_RATE_SELECTED_SUBSEQUENCE
  C10_FUNCTIONAL_NOT_SURROGATE: PASS_LITERAL_CENTERED_PSTAR_AND_LITERAL_MUNTZ_COORDINATE
  FPLUS_ORIENTATION: PASS_EXACT_NEGATION_THEOREM
  SAME_FAMILY_SLOT_S2: PASS_SELECTED_FAMILY_EQUALS_CENTERED_PSTAR_BY_RFL
  CENTER_NORMALIZER_CANCELLATION: PASS_BEFORE_NORMS
  COMPACT_COVER: PASS_EVERY_COMPACT_IS_PUT_IN_ONE_STRICT_CLOSED_SUBSTRIP
  ENDPOINT_SIGMA_HALF: NOT_CLAIMED

FRONT_STATUS:
  SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE: CLOSED_CONDITIONALLY
  N2_SELECTED_SHELL_COMPACT_DECAY: CLOSED_CONDITIONALLY
  N3_SAME_FAMILY_LOCALLY_UNIFORM_LIMIT: CLOSED_CONDITIONALLY
  N4_SLOT_S2: CLOSED_CONDITIONALLY
  F72_LITERAL_CENTER_ANCHORED_MODE_RATE_FAMILY: CARRIED_OPEN
  F72_CHI_DEFECT_RATE_FAMILY: CARRIED_OPEN
  SELECTED_DIFFERENTIAL_EIGENVALUE_DEFECT_RATE_FAMILY: CARRIED_OPEN
  SLOT_H2A_SIMPLE_EVEN_GROUND: OPEN_ANALYTIC_ROOF_WALL
  THEOREM510_REAL_ZERO_BRIDGE: OPEN_SOURCE_ASSEMBLY_WALL
  ROUTE_PROMOTION: false
  RH_CLAIM: false

CLOSES:
  - PREANCHOR_TO_SELECTED_SHELL_COFINAL_REINDEX_SEAM
  - SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY
  - N2_6_COMPACT_DECAY_ASSEMBLY
  - N3_SAME_FAMILY_LIMIT_ASSEMBLY
  - N4_SLOT_S2_ASSEMBLY
OPENS: []
CARRIES_OPEN:
  - F72_LITERAL_CENTER_ANCHORED_MODE_RATE_FAMILY
  - F72_CHI_DEFECT_RATE_FAMILY
  - SELECTED_DIFFERENTIAL_EIGENVALUE_DEFECT_RATE_FAMILY
  - SLOT_H2A_SIMPLE_EVEN_GROUND
  - THEOREM510_REAL_ZERO_BRIDGE

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_H2A_FINAL_CONSUMER_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT: false
  NUMERICAL_PROBE: false
  OBJECTIVE: >-
    Lock the exact selected-shell H2a predicate and determine whether the
    existing finite CCM bottom/Lagrange/P59 machinery can close the
    Theorem510 real-zero bridge conditionally before the remaining analytic
    simple-even ground supplier is attacked. Return exactly one theorem-sized
    next transaction; do not reopen N2, W5, the edge band or the Mellin rate.
  PRIMARY_DISCRIMINATOR:
    name: THEOREM510_ASSEMBLY_READY_VS_H2A_OBJECT_OR_COMPLEMENT_FLOOR_GAP
    branch_A: >-
      Existing source-row, P59 and quotient-basis machinery already provide a
      same-family conditional Theorem510RealZeroBridge. Authorize that one
      assembly theorem first, leaving H2a as the sole roof wall.
    branch_B: >-
      A source-object, real-row, normalization, quotient-basis or complement-
      floor premise is still missing. Name exactly one minimal missing theorem
      and its current suppliers.
  REQUIRED_RETURN:
    - exact_H2aAt_predicate_for_the_selected_shell
    - exact_selected_matrix_row_parity_and_normalization_objects_after_reindex
    - exact_existing_G2_and_Proposition59_consumers
    - whether_Theorem510_bridge_is_assembly_only
    - one_public_Lean_theorem_statement_or_one_minimal_missing_identity
    - exact_import_list
    - CLOSES_and_OPENS_catalog_names
  SUCCESS_CODE: SELECTED_FERRERS_H2A_OR_THEOREM510_SINGLE_NEXT_NODE_LOCKED
  FAILURE_CODE: GOAL058_H2A_SELECTED_OBJECT_OR_REALZERO_BRIDGE_UNMAPPED
  FORBIDDEN:
    - reopen_N2_N3_N4
    - reopen_W5_edge_band_or_top
    - add_a_free_simple_even_ground_premise_under_a_new_name
    - use_a_trial_row_as_a_ground_row_without_the_exact_H2a_predicate
    - use_real_zero_results_from_a_different_family
    - select_a_new_subsequence
    - claim_RH_or_promote_Route_B

NEXT_LOAD_BEARING_GAP: SLOT_H2A_SIMPLE_EVEN_GROUND

PREDICTION_FATES:
  P_N2_ASSEMBLY_1:
    prior_probability: 0.89
    fate: CONFIRMED
  P_N2_COMPACT_ASSEMBLY_LEAN_1:
    prior_probability: 0.84
    fate: CONFIRMED
  P_N2_SLOT_S2_COROLLARY_1:
    prior_probability: 0.96
    fate: CONFIRMED

NEW_PREDICTIONS:
  P_H2A_PREFLIGHT_1:
    probability: 0.88
    prediction: >-
      The exact selected-shell H2a object is already source-locked; the next
      uncertainty is one finite bottom/complement-floor supplier rather than
      any transform, normalization or compact-limit issue.
  P_THEOREM510_ASSEMBLY_1:
    probability: 0.82
    prediction: >-
      The conditional same-family real-zero bridge can be assembled from the
      existing CCM bottom/Lagrange/P59 machinery without a new analytic input.

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: LEAN_REPORTED_NOT_JUDGE_RERUN
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

Commit `28df2481869eab257cc55420450ab192bec8f7e1` closes the selected-shell compact layer on the exact source objects. The old private-tail seam is now exposed by one cofinal reindex receipt whose index, pair and source scale equalities are definitional. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

The N2 theorem proves compact-local decay of the literal centered finite family minus the correctly reflected Müntz-anchored main term. The reflection is not dismissed by convention: the raw `Fplus` coordinate is proved to equal the projected Mellin coordinate at `-z`, and `centeredXi(-z)=centeredXi(z)` is separately proved from the functional equation. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

The N3 theorem combines that exact error decay with the selected shell's Lemma-7.3 limit and obtains locally uniform convergence of the same `centeredPstar` family to `centeredXi`. No old all-index source record, family crosswalk, selected trial normalizer, scale majorant or newly selected subsequence enters. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

The N4 theorem is not a neighboring-family corollary. In the proof, the roof's `selectedFamily` is definitionally the shell's `centeredPstar`, and uniqueness of limits identifies every `ClusterData.limit` with `centeredXi`. Hence `SlotS2` is witnessed by `c=1` and the constant zero-free gauge `1`. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

The closure remains conditional exactly on the frozen `hmode`, `hchi` and two-eigenvalue `htheta` rate families. Those hypotheses were not discharged by this transaction and are not relabeled as theorems. The finite simple-even ground and the Theorem-5.10 real-zero application remain separate roof fronts. `[COFINAL_FAMILY][CONDITIONAL]`

## STRONGEST ATTACK

The strongest attack is a wrong-family `SlotS2`: a cluster theorem could have been proved for the abstract canonical family while N3 concerned a neighboring raw or pre-anchor family.

That attack fails here. The N4 proof records

```lean
have hfam : CanonicalRHRoute.selectedFamily
    shell.canonicalApproximation = shell.centeredPstar := rfl
```

and compares `DC.convergence` with the N3 convergence theorem at the same point. No transport theorem, forgotten normalization or implicit diagonal is used. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]` **[C04]**

The second attack is the `Fplus` sign. The finite transform uses `proposition59RawTransform ... (-z)`, while `Gwin` uses the Mellin coordinate at `z`. The code proves the exact reflected-coordinate identity and only removes the reflection at the target through the proved evenness of centered Xi. Therefore the sign is cargo, not prose. `[ABSTRACT][LEAN_REPORTED_NOT_JUDGE_RERUN]` **[C10]**

The remaining fatal-to-promotion objection is conditionality: `hmode`, `hchi` and `htheta` are public hypotheses. The theorem does not turn them into unconditional production facts. Consequently no RH claim or route promotion follows. `[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

Freeze N2, N3 and N4. Do not reopen the Mellin kernel, normalizer, shell reindex, non-top/top split or W5 rate.

Run one read-only consumer preflight on the two remaining roof fronts. It must decide whether the already-proved finite bottom/Lagrange/P59 machinery makes the Theorem-5.10 bridge a pure same-family assembly, or whether one exact H2a object/certificate premise is still unmapped. The output is one theorem-sized next node, not another route map.

Registered prediction: the transform and compact-limit side is finished; the substantive remaining analytic obstruction is the selected finite simple-even ground/complement-floor supply.

## CODEX DIRECTIVE

```text
TASK_ID:
  GOAL058_SELECTED_FERRERS_H2A_FINAL_CONSUMER_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

READ_FIRST:
  q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMSourceRow.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilBottomSpectral.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilParity.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/H2aPenaltyCoercivity.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersN2CompactDecayAssembly.lean

OBJECTIVE:
  Lock the exact selected-shell H2a predicate and return exactly one next
  public theorem. Prefer a conditional same-family Theorem510RealZeroBridge
  assembly if every required object is already present. Otherwise name the
  single smallest missing H2a supplier and show the exact consumer field it
  fails to fill.

DO_NOT_EDIT:
  any Lean source
  any route state
  any existing verdict
  N2/N3/N4 files

RETURN_EXACTLY:
  1. exact selected-shell H2aAt type;
  2. exact selected finite matrix, row, parity and normalization objects;
  3. exact existing G2/P59 real-zero theorem chain;
  4. one theorem statement or one minimal missing identity;
  5. exact imports;
  6. CLOSES and OPENS;
  7. SUCCESS_CODE or FAILURE_CODE.

SUCCESS_CODE:
  SELECTED_FERRERS_H2A_OR_THEOREM510_SINGLE_NEXT_NODE_LOCKED

FAILURE_CODE:
  GOAL058_H2A_SELECTED_OBJECT_OR_REALZERO_BRIDGE_UNMAPPED
```

## META CLOSEOUT

**What became smaller?** The entire selected-shell transform/compact-limit side collapsed from N2/N3/N4 into three kernel-green conditional theorems. The only roof fronts left are the frozen rate inputs, H2a and the Theorem-5.10 same-family application.

**What was killed?** The old objections based on a private tail shift, a hidden trial normalizer, a separate all-index family, an untracked `z ↦ -z` reflection, and a distinct cluster family.

**What must not be tried again?** No new subsequence, no old `S + hFamily` transport, no scale-bound multiplication, no bare L2-to-compact inference, and no re-opening of the edge-band derivative analysis.

**Current smallest named gap?** `SLOT_H2A_SIMPLE_EVEN_GROUND`, with `THEOREM510_REAL_ZERO_BRIDGE` as the remaining source-assembly seam.

**Next cheapest decisive test?** Read the exact consumer types and determine whether the real-zero bridge is assembly-only before spending new mathematics on H2a.

**Prediction fate?** All three registered N2 assembly predictions are confirmed without retroactive repair.

**Memory entry?**

```yaml
iteration:
  target: selected_shell_N2_N3_N4_compact_closure
  status: PROGRESS
  failed_strategy: none
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SLOT_H2A_SIMPLE_EVEN_GROUND
  invariant_learned: reflection_and_finite_prefix_reindex_must_be_exact_theorems
  forbidden_future_move: reopen_compact_Mellin_rate_or_use_neighboring_family
  next_decisive_test: H2a_and_Theorem510_exact_consumer_preflight
```
