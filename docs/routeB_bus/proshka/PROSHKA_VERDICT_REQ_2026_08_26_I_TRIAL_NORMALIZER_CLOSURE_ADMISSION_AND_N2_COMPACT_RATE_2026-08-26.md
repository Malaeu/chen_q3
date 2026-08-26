# STATUS: PROVED — LOCAL-CELL TRIAL NORMALIZER AND LITERAL NORMALIZED GALERKIN RESIDUAL ADMITTED; N2 COMPACT MELLIN RATE IS THE NEXT WALL

```yaml
PRIMARY: ADMIT_GOAL058_SELECTED_FERRERS_LOCAL_CELL_NORMALIZER_CLOSURE
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-I
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_DIRECT_FOLLOWUP_OF_REQ_2026_08_26_H
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  HEAD: b057fda3d6d759c47a6cdc4427298224c2215d51
  HEAD_IS_ORIGIN_RH_CLEAN_AT_AUDIT: true
  PARENT_VERDICT_COMMIT: 82ac9628f0c99a8b1755f66430e075c5c6d8e458
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrialNormalizerClosure.lean
  LEAN_GIT_BLOB: 9731d9e7dcd616f46cd9d1a23708077d7a71b721
  LEAN_SHA256_REPORTED: absent
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_TRIAL_NORMALIZER_CLOSURE_2026-08-26.md
  SOURCE_RECORD_GIT_BLOB: 13fcfee8254cd8d22d8d67dd86035eca61de7efd
  SOURCE_RECORD_SHA256_REPORTED: absent
  COMMIT_DELTA:
    added_files: 2
    existing_files_modified: 0

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS_EXIT_0
  LINUX_REPORTED_MODULE_BUILD: PASS
  LINUX_REPORTED_Q3_CHECK: PASS
  LINUX_REPORTED_HOLE_SCAN: PASS
  LINUX_REPORTED_AXIOMS:
    selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger:
      - propext
      - Classical.choice
      - Quot.sound
    selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_selectedFerrersW5RateLedger:
      - propext
      - Classical.choice
      - Quot.sound
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_MODULE_BUILD: false
  JUDGE_RERAN_Q3_CHECK: false
  FULL_PROJECT_BUILD_CLAIMED: false

RECEIPT_AUDIT:
  SOURCE_RECORD_STARTS_WITH_REQUIRED_YAML: false
  SOURCE_RECORD_CONTAINS_GIT_BLOB_AND_SHA256_FIELDS: false
  CLASSIFICATION: NONFATAL_PROCESS_NONCONFORMITY
  REPAIR_POLICY: APPEND_ONLY_NO_RETROACTIVE_EDIT
  FUTURE_SOURCE_RECORDS_MUST_FOLLOW_SUPPLIER_CONTRACT_V7_HEADER: true

PUBLIC_SURFACE:
  theorem_1:
    name: selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
    conclusion: SelectedTrialNormalizerBounded S
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  theorem_2:
    name: selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_selectedFerrersW5RateLedger
    conclusion: Tendsto_norm_selectedNormalizedGalerkinResidual_to_zero
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  public_inputs:
    - S_ProlateCanonicalSourceData
    - hFamily_SelectedFerrersPreAnchorProductionFamilyCrosswalk_S
    - hmode_literal_center_anchored_mode_rate_family
    - hchi_literal_chi_defect_rate_family
    - htheta_two_selected_differential_eigenvalue_defect_rate_families
  new_analytic_input: none

SEMANTIC_ADMISSION:
  status: SEMANTICALLY_ADMITTED_AS_EXACT_CONDITIONAL_COFINAL_SUPPLIER
  selected_full_trial_object: literal_gTrial_m_on_selectedPairIndex
  selected_projected_trial_object: literal_gTrial_m_N_on_same_moving_carrier
  normalizer_object: literal_inverse_norm_of_selected_projected_trial
  residual_object: literal_selected_normalized_projection_minus_full_residual
  subsequence_added: false
  surrogate_functional_used: false
  uniform_D_used: false
  global_V0_overlap_used: false
  riemann_zeta_half_used: false
  mellin_gamma_constant_used: false

LOCAL_CELL_MECHANISM:
  fixed_cell: "[1, 9/8]"
  target_profile: four_mul_explicitCCMLimitH
  active_term_sign:
    statement: every_active_n_has_nu_ge_one_and_H_nu_positive
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  fixed_witness_term:
    index: 1
    statement: n_equals_one_is_eventually_active_and_supplies_a_fixed_positive_floor
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  inactive_terms:
    statement: exactly_zero_by_literal_compact_support
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  accumulated_packet_error:
    per_term: Cp_div_lambda_squared
    active_cardinality: at_most_lambda
    total: Cp_div_lambda
    fate: tends_to_zero
  source_scale_direction:
    proved_input: eventual_upper_bound_on_norm_sourceScale73
    valid_division: scaled_comb_floor_implies_unscaled_comb_floor
    old_inverse_scale_floor_error_reused: false
  cell_measure:
    measure: dStar_equals_du_over_u
    lower_bound: one_ninth
    role: fixed_positive_L2_mass

SEMANTIC_GUARDS:
  C01_SIGN_MASS_LOCALIZATION: PASS_USED
  C04_SAME_COORDINATES_TWO_LAWS: PASS_SAME_MOVING_CARRIER_AND_TRIAL
  C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT: PASS_CELL_FIXED_IN_PARENT_VERDICT
  C10_FUNCTIONAL_NOT_SURROGATE: PASS_LITERAL_NORM_AND_LITERAL_RESIDUAL
  SCALE_INEQUALITY_DIRECTION: PASS
  ACTIVE_INACTIVE_PARTITION_COMPLETE: PASS
  N_EQUALS_ONE_ACTIVITY: PASS_EVENTUALLY
  SOURCE_FAMILY_TRANSPORT: PASS_VIA_HFAMILY
  REVERSE_TRIANGLE_PROJECTED_FLOOR: PASS
  POINTWISE_TRIAL_NONZERO_USED_AS_UNIFORM_FLOOR: false
  INDIVIDUAL_ANCHOR_BOUNDS_ASSUMED: false
  NUMERICS_USED_AS_PROOF: false

FRONT_STATUS:
  W5_ANALYTIC_DECOMPOSITION: COMPLETE_AT_CONSUMER_STRENGTH
  SELECTED_PROJECTION_TAIL_DECAY:
    status: CLOSED_CONDITIONALLY
    theorem: selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
  SELECTED_TRIAL_NORMALIZER_BOUNDED:
    status: CLOSED_CONDITIONALLY
    theorem: selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
  LITERAL_NORMALIZED_GALERKIN_RESIDUAL_L2_DECAY:
    status: CLOSED_CONDITIONALLY
    theorem: selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_selectedFerrersW5RateLedger
  SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY:
    status: OPEN
    reason: moving_Mellin_evaluation_norm_requires_a_quantitative_rate_not_bare_L2_decay
  SLOT_S2: OPEN
  ROUTE_PROMOTION: false
  RH_CLAIM: false

N2_RATE_OBSERVATION:
  status: PAPER_RATE_LEDGER_SURVIVES_FIRST_ATTACK
  w5_residual_squared_upper_shape: constant_times_Ck_squared_div_physical_bandwidth
  selected_Ck_shape: k_plus_2_to_one_quarter_times_sqrt_log_plus_two
  selected_bandwidth_exact_shape: two_pi_times_k_plus_3_div_log_k_plus_2
  residual_norm_shape: log_k_div_k_to_one_quarter
  closed_substrip_kernel_envelope_shape: sqrt_log_k_times_k_to_sigma_over_two
  sourceScale73: eventually_bounded
  combined_shape: log_k_to_three_halves_times_k_to_sigma_over_two_minus_one_quarter
  vanishing_range: every_fixed_sigma_strictly_less_than_one_half
  theorem_status: NOT_YET_LEAN_EXPORTED

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_N2_COMPACT_RATE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT: false
  NUMERICAL_PROBE: false
  CREATE_REPORT: docs/routeB_bus/LINUX_SELECTED_FERRERS_N2_COMPACT_RATE_PREFLIGHT_GOAL058_2026-08-26.md
  OBJECTIVE: >-
    Lock the exact source-facing N2 compact-Mellin error object and derive the
    complete moving-carrier exponent ledger from the admitted W5 rate. Return
    exactly one Lean theorem signature and one implementation transaction.
  PRIMARY_DISCRIMINATOR:
    name: CENTER_NORMALIZER_CANCELLATION_VS_LITERAL_NORMALIZED_RESIDUAL
    preferred_route: >-
      Prove compact decay for the sourceScale-weighted UNNORMALIZED projection
      residual after the exact center-normalizer cancellation. Do not retain
      selectedTrialNormalizer as an N2 premise merely because it is now bounded.
    fallback_route: >-
      Use the literal normalized residual only if the exact centered-family
      algebra proves that it is the consumer object without introducing an
      additional growing factor.
  EXACT_OBJECTS_TO_LOCK:
    - selectedFamily_of_the_literal_projected_trial
    - selectedMuntzApproximation_of_the_same_precommitted_Ferrers_family
    - literal_unnormalized_projection_minus_full_residual
    - literal_selected_normalized_residual
    - selectedFerrersLemma73SourceScale
    - exact_parent_extract_schedule_and_moving_window
  RATE_LEDGER_TO_DERIVE:
    - residual_squared_upper_bound_from_the_W5_first_order_rate_receiver
    - exact_Ck_growth_used_by_the_W5_assembly
    - exact_physical_bandwidth_formula_on_selectedFerrersPreAnchorIndex
    - compact_Mellin_kernel_L2_envelope_on_abs_Im_z_le_sigma
    - eventual_upper_bound_on_sourceScale73
    - strict_log_vs_power_limit_for_every_sigma_less_than_one_half
  REQUIRED_RETURN:
    - one_exact_public_Lean_theorem_statement
    - exact_import_list
    - whether_private_W5_reconstruction_is_required
    - CLOSES_and_OPENS_catalog_names
  SUCCESS_CODE: SELECTED_FERRERS_N2_COMPACT_RATE_LEAN_READY
  FAILURE_CODE: GOAL058_W5_RATE_TO_N2_MOVING_MELLIN_ENVELOPE_GAP
  FORBIDDEN:
    - add_a_free_compact_rate_premise
    - infer_compact_open_decay_from_bare_L2_convergence
    - keep_selectedTrialNormalizer_as_N2_input_after_exact_cancellation
    - choose_a_faster_subsequence_after_inspecting_the_rate
    - confuse_ground_transform_tracking_with_projection_tail_decay
    - reopen_W5_edge_analysis

CLOSES:
  - SELECTED_TRIAL_NORMALIZER_BOUNDED_OR_DIRECT_WEIGHTED_PRODUCT
  - SELECTED_TRIAL_NORMALIZER_BOUNDED
  - LITERAL_SELECTED_NORMALIZED_GALERKIN_RESIDUAL_L2_DECAY
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_LITERAL_CENTER_ANCHORED_MODE_RATE_FAMILY
  - F72_CHI_DEFECT_RATE_FAMILY
  - SELECTED_DIFFERENTIAL_EIGENVALUE_DEFECT_RATE_FAMILY
  - SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY
  - COFINAL_SIMPLE_EVEN_FINITE_GROUND
  - TRUE_COMPLEMENT_GAP_LOWER_BOUND
  - SLOT_S2_SAME_FAMILY_LIMIT

NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY

PREDICTION_FATES:
  P_LOCAL_CELL_FLOOR_1:
    prior_probability: 0.84
    fate: CONFIRMED
  P_LOCAL_CELL_NORMALIZER_LEAN_1:
    prior_probability: 0.80
    fate: CONFIRMED
  P_NORMALIZER_ROUTE_1:
    prior_probability: 0.58
    fate: PARTIALLY_CONFIRMED_BY_REPAIRED_R1
    note: >-
      The full-object-floor strategy survived, but the proposed central-V0
      mechanism was refuted and was not retroactively repaired. The confirmed
      mechanism is the separately registered fixed local cell.
  P_N2_RATE_1:
    probability: 0.87
    prediction: >-
      The already-proved W5 coefficient rate, selected bandwidth and bounded
      sourceScale pay the moving Mellin envelope on every closed substrip
      abs(Im z) <= sigma with sigma < 1/2, without a new analytic hypothesis.
  P_N2_OBJECT_1:
    probability: 0.90
    prediction: >-
      Exact center-normalizer cancellation makes the sourceScale-weighted
      unnormalized projection residual the minimal N2 object; the newly proved
      bounded selected normalizer is true but not load-bearing for N2.

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
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
RH_CLAIM: false
```

## ROUTE MAP

Commit `b057fda3d6d759c47a6cdc4427298224c2215d51` contains exactly the authorized new Lean module and its source record. No existing Lean source or route state was modified. `[COFINAL_FAMILY][PAPER]`

The first public theorem proves eventual boundedness of the literal selected trial normalizer. The proof does not promote pointwise `TrialNonzero` into a uniform statement. It first constructs a positive lower norm floor for the full trial, transports that exact object through `hFamily`, and only then uses the already-admitted projection-tail decay and the reverse triangle inequality to obtain a lower floor for the projected norm. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

The second public theorem applies the existing exact factorization

\[
\|s_k(P_kg_k-g_k)\|
=
|s_k|\,\|P_kg_k-g_k\|
\]

with the two now-supplied inputs. Therefore the literal normalized Galerkin residual tends to zero in its moving Hilbert carrier. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

The decisive representation shift is local sign retention. On the fixed cell

\[
1\le u\le 9/8,
\]

every active source argument satisfies `n*u >= 1`, where the explicit limiting profile is positive. The term `n=1` supplies a fixed lower envelope, inactive terms vanish exactly by support, and the aggregate F72 packet error is only `Cp/lambda`. This is the exact signature of C01: keep WHERE the sign lives instead of asking a global zero-mass functional for a lower bound. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

The source-scale inequality also has the correct direction. The file proves an eventual upper bound on `norm(sourceScale73)`. Hence a lower bound for `norm(sourceScale73 * E_star)` produces a lower bound for `norm(E_star)` by division by a fixed positive upper ceiling. It does not reuse the previously killed attempt to derive a floor from an upper bound on the inverse scale. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

The status is conditional only in its public inputs. The assembly itself is proved at the reported kernel gate:

```text
hFamily + hmode + hchi + htheta
  -> SelectedProjectionTailDecay
  -> SelectedTrialNormalizerBounded
  -> norm(selectedNormalizedGalerkinResidual) -> 0.
```

No route promotion follows. The frozen input families still have to be supplied on the production route. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

## STRONGEST ATTACK

The strongest attack is that positivity of the single `n=1` target term might be destroyed by the remaining comb.

It is not. The proof partitions the exact finite comb into active and inactive terms. Inactive terms are exactly zero by the literal compact support. Every active target term is nonnegative because `n*u >= 1`; every active source term differs from its positive target by at most the same `Cp/lambda^2` budget. The number of active terms is at most `lambda`, so all possible negative deviations total at most `Cp/lambda`. Eventually this is below half the fixed `n=1` floor. This gives a genuine lower envelope, not a numerical or asymptotic sign guess. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

A second attack is that the source scale might tend to zero or infinity. A lower bound on the scale is unnecessary for this direction. The proof needs only an upper bound, because it starts with a floor for the scaled comb and divides by the upper ceiling. The upper ceiling is derived from the same `hmode` and `hchi` families, unit-L2 normalization and exact anchor locks; it is not added as a new premise. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

A third attack is wrong-family transport. The public theorem does not substitute an abstract pre-anchor object by notation. `hFamily` eventually identifies both the selected moving `PairIndex` and the selected trial function with the precommitted Ferrers family. The norm transport is then proof-irrelevant after exact substitution. `[COFINAL_FAMILY][LEAN_REPORTED_NOT_JUDGE_RERUN]`

The surviving boundary is compact Mellin topology. Hilbert-norm decay is not itself compact-open decay on a moving window. The new W5 rate appears strong enough to pay the exact evaluation envelope, but that exponent ledger and the exact center-normalizer cancellation must be source-locked before Lean. `[COFINAL_FAMILY][PAPER]`

## FINAL PROPOSAL

Ratify and freeze `G6N1SelectedFerrersTrialNormalizerClosure.lean`. Do not revisit the central `V0` route, the edge-band estimates, or uniform-D. The literal normalized residual L2 decay is now a reusable conditional supplier.

Do not immediately feed this normalized residual into N2. The sharper centered-family algebra cancels the finite projection normalizer. The next task must first identify the exact sourceScale-weighted unnormalized residual and prove that the explicit W5 rate beats the moving Mellin evaluation norm on every closed substrip.

## CODEX / LINUX DIRECTIVE

```text
TASK_ID: GOAL058_SELECTED_FERRERS_N2_COMPACT_RATE_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

OBJECTIVE:
  Derive the exact source-facing compact-Mellin projection-tail rate from the
  admitted W5 rate, without a free compact-rate hypothesis and without a new
  subsequence.

READ_FIRST:
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrialNormalizerClosure.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFirstOrderProjectionTailReceiver.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualCrosswalk.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean
  docs/routeB_bus/proshka/PROSHKA_VERDICT_G6_N2_SELECTED_MELLIN_COMPACT_DECAY_2026-08-20.md

DO:
  1. Write the exact centered finite-minus-anchored-main identity and decide
     whether its residual is unnormalized or selected-normalized.
  2. Extract the exact W5 quantitative residual-square upper bound, not merely
     the qualitative SelectedProjectionTailDecay conclusion.
  3. Extract the exact selected C_k and physical-bandwidth formulas.
  4. Prove on paper the L2 norm of u^(-i*z) on the moving dStar window for
     abs(Im z) <= sigma.
  5. Combine with the eventual sourceScale73 upper bound and derive the exact
     log-versus-power exponent for every fixed sigma < 1/2.
  6. Return one exact public Lean theorem signature, exact imports, and whether
     private W5 reconstruction is required.

DO_NOT:
  edit Lean;
  assume compact-open decay from bare L2 convergence;
  retain SelectedTrialNormalizerBounded as an N2 premise after exact
  center-normalizer cancellation;
  add a compact-rate field;
  select a faster subsequence;
  reopen W5 edge analysis;
  confuse projection-tail decay with finite-ground spectral tracking.

SUCCESS:
  SELECTED_FERRERS_N2_COMPACT_RATE_LEAN_READY

FAILURE:
  GOAL058_W5_RATE_TO_N2_MOVING_MELLIN_ENVELOPE_GAP
```

## META CLOSEOUT

**What became smaller?** The normalizer problem and the literal normalized residual L2 problem are gone; the remaining projection-side issue is now only the moving compact-Mellin rate.

**What was killed?** The global central-overlap route remains killed. No retroactive repair was applied.

**What must not be tried again?** Global zero-mass lower bounds, inverse-scale direction errors, uniform-D edge repair, or bare `L2 -> compact-open` claims.

**Current smallest named gap:**

```text
SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY
```

**Next cheapest decisive test:** derive the complete exponent ledger on every fixed closed substrip before writing Lean.

**Prediction fates:** both registered local-cell predictions are confirmed; the older general R1 prediction is only partially confirmed because its proposed V0 mechanism was refuted.

**Memory entry:**

```yaml
iteration:
  target: SELECTED_TRIAL_NORMALIZER_BOUNDED_OR_DIRECT_WEIGHTED_PRODUCT
  status: PROGRESS
  failed_strategy: CENTRAL_V0_OVERLAP_FLOOR
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_SOURCE_SCALED_MELLIN_COMPACT_DECAY
  invariant_learned: preserve sign location on a fixed cell and keep the exact moving family
  forbidden_future_move: infer a global lower floor from zero mass or from an inverse-scale upper bound
  next_decisive_test: exact W5-rate versus moving Mellin-envelope exponent ledger
```
