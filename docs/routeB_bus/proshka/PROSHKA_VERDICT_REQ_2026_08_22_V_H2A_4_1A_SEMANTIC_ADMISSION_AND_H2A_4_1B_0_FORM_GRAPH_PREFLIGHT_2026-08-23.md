# STATUS: PROVED — H2A.4.1A SEMANTICALLY ADMITTED; L73-L2-TO-RIESZ-ACTION SHORTCUT REJECTED; FORM-GRAPH PREFLIGHT AUTHORIZED
```yaml
PRIMARY: ADMIT_H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: H2A_4_1A_SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_SPLIT_LEAN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 569b7b05fdcfe24e5ed6c200df5fb68b92e8f6eb
  SOURCE_COMMIT: 569b7b05fdcfe24e5ed6c200df5fb68b92e8f6eb
  ACTUAL_PARENT: e0c47c3bfc06a7251d4f34c5126377ec36f8ecfd
  CLAIMED_PARENT: e0c47c3bfc06a7251d4f34c5126377ec36f8ecfd
  CLAIMED_PARENT_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean
  LEAN_GIT_BLOB: 9db9c3bee39dd8f958c3df25762c9733054d0276
  LEAN_SHA256_REPORTED: 2f85ea8890f83aa397dd193d9b0c8e6e527c9c25af3f2df7a666540715b0983e
  LEAN_LINES_REPORTED: 811
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1A_SELECTED_FERRERS_FINITE_CCM_RESIDUAL_SOURCE_ACTION_SPLIT_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 99f2b24b72db694f834006548ae48dbd3d27e7d3
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7927_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS_FOR_ALL_3_PUBLIC_THEOREMS_AND_2_PLANTS:
    - propext
    - Classical.choice
    - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_SELECTED_FINITE_RIESZ_SOURCE_ACTION_SPLIT
  SELECTED_INDEX: same_for_every_object
  WINDOW_HILBERT_CARRIER: H_m_at_selected_index
  FINITE_CARRIER: E_m_N_at_same_selected_index
  PROJECTION: exact_same_P_m_N
  TARGET_VECTOR: E_star_of_factor_four_explicitCCMLimitH
  PHYSICAL_ERROR: sourceScale_smul_gTrial_sub_target
  SELECTED_TRIAL: exact_selected_kTrial
  NORMALIZER: exact_sTrial_m_N
  RAYLEIGH_SHIFT: exact_selectedFerrersFiniteCCMRayleigh
  RIESZ_OPERATOR: exact_sourceCCMFiniteRieszOperator
  VECTOR_IDENTITY: "s_k*x_k = t_k*(eE_k+gE_k)"
  ACTION_IDENTITY: "s_k*(R_k*x_k-a_k*x_k) = t_k*((R_k*eE_k-a_k*eE_k)+(R_k*gE_k-a_k*gE_k))"
  NORM_BUDGET: "norm(s_k)*norm(R_k*x_k-a_k*x_k) <= t_k*(A_k+T_k)"
  RATE_CONTENT: none
  AMBIENT_OPERATOR_CLAIMED: false
  COMPRESSION_CLAIMED: false
  C04_OBJECT_AUDIT: PASS
  C10_FUNCTIONAL_AUDIT: PASS

PLANT_AUDIT:
  VANISHING_HILBERT_ERROR_WITHOUT_UNIFORM_ACTION:
    STATUS: PASS
    SCOPE: ABSTRACT
    VERIFIER: LEAN
    CONCLUSION: L2_tracking_does_not_control_a_growing_operator_family
  EXACT_TARGET_MATCH_WITH_NONZERO_TARGET_DEFECT:
    STATUS: PASS
    SCOPE: ABSTRACT
    VERIFIER: LEAN
    CONCLUSION: zero_physical_error_does_not_control_the_targets_own_shifted_defect

H2A_BOUNDARY_AFTER_ADMISSION:
  SELECTED_ODD_MASS_DECAY: CLOSED
  SELECTED_RESIDUAL_VARIANCE_AND_RIESZ_LOCK: CLOSED
  SELECTED_FACTOR_FOUR_TARGET_HILBERT_OBJECT: CLOSED
  SELECTED_SCALED_PHYSICAL_ERROR_PROJECTION: CLOSED
  SELECTED_FINITE_RIESZ_SOURCE_ACTION_SPLIT: CLOSED
  SELECTED_RESIDUAL_SOURCE_ACTION_BUDGET: CLOSED
  ERROR_ACTION_DECAY: OPEN
  TARGET_ACTION_DEFECT_DECAY: OPEN
  SELECTED_RESIDUAL_DECAY: OPEN
  SECTOR_FLOORS: OPEN
  POSITIVE_COFINAL_EFFECTIVE_FLOOR: OPEN
  SIMPLE_BOTTOM_GROUND: OPEN
  THEOREM_510_APPLICATION: OPEN
  REAL_ZEROS: OPEN

H2A_4_1B_RULING:
  NAIVE_TARGET: existing_L73_Hilbert_error_implies_both_action_terms_decay
  STATUS: REJECTED_AS_UNSUPPORTED_INFERENCE
  MATHEMATICAL_NEGATION_OF_SELECTED_RESIDUAL_DECAY_PROVED: false
  KILL_SCOPE: current_L73_L2_inputs_to_finite_Riesz_action_rate
  REASONS:
    - finite_Riesz_action_is_the_restricted_source_Weil_form_action_not_the_H_m_norm
    - W02_and_prime_parts_are_bounded_but_the_shifted_archimedean_part_lives_on_a_form_domain
    - current_L73_controls_norm_e_k_but_not_the_shifted_archimedean_graph_norm_of_eE_k
    - inversion_evenness_and_transform_convergence_do_not_make_the_projected_target_a_Riesz_eigenvector
    - no_current_theorem_identifies_the_factor_four_target_as_a_finite_or_ambient_Weil_radical_vector
    - the_primary_source_calls_rigorous_trial_to_ground_approximation_the_main_remaining_obstacle
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE

SOURCE_AUDIT_FINDINGS:
  FINITE_RIESZ_OBJECT:
    status: EXACT
    note: conjugated_literal_CCM_coefficient_operator_on_E_m_N_only
  FINITE_SOURCE_WEIL_LEDGER:
    status: EXACT
    note: W02_plus_arch_minus_prime_equals_ccmWeilMatFinite_form_on_the_exact_finite_span
  W02_FORM:
    status: BOUNDED_AMBIENT_FORM
  PRIME_FORM:
    status: BOUNDED_AMBIENT_FORM
  SHIFTED_ARCHIMEDEAN_FORM:
    status: POSITIVE_FORM_ON_EXACT_SHIFTED_FORM_DOMAIN
    H_m_upper_continuity: not_supplied
    graph_norm_is_load_bearing: true
  AMBIENT_ASSOCIATED_OPERATOR_OR_COMPRESSION:
    status: NOT_AVAILABLE_AND_NOT_REQUIRED_FOR_THE_PREFLIGHT

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED_READ_ONLY
  CODE: H2A_4_1B_0_SELECTED_FERRERS_FINITE_FORM_GRAPH_ENVELOPE_PREFLIGHT
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  LEAN_WRITE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  OUTPUT_PATH: docs/routeB_bus/H2A_4_1B_0_SELECTED_FERRERS_FINITE_FORM_GRAPH_ENVELOPE_PREFLIGHT_2026-08-23.md
  PRIMARY_ROLE: >-
    Determine, before any further Lean source, whether the exact source Weil
    representation supplies source-derived graph-form envelopes for the two
    action terms exposed by H2A.4.1A. Separate the bounded W02/prime pieces
    from the unbounded shifted archimedean piece, derive the exact weighted
    rate ledger, and decide whether the projected factor-four target has an
    independent source identity or is the true ground-to-trial wall.
  CLOSES_IF_SUCCESSFUL:
    - H2A_4_1B_SOURCE_REPRESENTATION_SELECTION
    - H2A_4_1B_EXACT_MISSING_GRAPH_NORM_CONTRACT
  OPENS: []

PREFLIGHT_REQUIRED_OBJECTS:
  i_k: selected_index
  e_k: selectedFerrersScaledPhysicalErrorVector
  eE_k: selectedFerrersScaledPhysicalErrorProjection
  G_k: selectedFerrersFactorFourTargetVector
  gE_k: selectedFerrersFactorFourTargetProjection
  R_k: sourceCCMFiniteRieszOperator_i_k
  a_k: selectedFerrersFiniteCCMRayleigh
  t_k: exact_sTrial_normalizer
  s_k: exact_sourceScale
  A_k: "norm(R_k*eE_k-a_k*eE_k)"
  T_k: "norm(R_k*gE_k-a_k*gE_k)"

PREFLIGHT_REQUIRED_TESTS:
  - name: EXACT_DUAL_DEFECT_IDENTITY
    task: >-
      Verify the basis-invariant finite-dimensional identity expressing
      norm((R_k-a_k)e) as the supremum over unit v in E_m_N of the exact
      source-Weil pairing minus a_k times the Hilbert pairing. Give the exact
      conjugation orientation and the existing theorem names that identify
      the source form with ccmWeilMatFinite.
  - name: BOUNDED_COMPONENT_LEDGER
    task: >-
      Extract explicit source-derived bounds for W02 and prime components.
      Do not replace them by absolute row sums. Record their growth in m_k.
  - name: SHIFTED_ARCH_GRAPH_LEDGER
    task: >-
      Identify the exact shifted-weighted Fourier norm needed to control the
      archimedean component on eE_k and gE_k. Decide whether current hmode/hchi
      and L73 estimates imply this graph-norm control. A bare H_m norm is not
      accepted.
  - name: TARGET_IDENTITY_DISCRIMINATOR
    task: >-
      Search the primary source and production tree for an exact radical,
      window-defect, commutator, or finite-form identity for the projected
      factor-four target. Inversion-evenness alone is forbidden.
  - name: WEIGHTED_RATE_LEDGER
    task: >-
      For every legal envelope C_A(k), C_T(k), test the actual consumer
      (t_k/norm(s_k))*(C_A(k)+C_T(k)). A small unweighted term is not a pass.

PREFLIGHT_OUTCOME_CODES_EXACTLY_ONE:
  - SOURCE_GRAPH_ENVELOPES_FOUND_FOR_BOTH_TERMS
  - ERROR_GRAPH_ENVELOPE_FOUND_TARGET_DEFECT_OPEN
  - L73_L2_INPUT_INSUFFICIENT_FOR_ERROR_GRAPH_NORM
  - SOURCE_GRAPH_ENVELOPE_RATE_FATAL_FOR_CURRENT_SCHEDULE
  - SOURCE_TARGET_IDENTITY_PROVENANCE_AMBIGUOUS

CANDIDATE_REPRESENTATIONS:
  R1:
    CODE: FINITE_SOURCE_WEIL_DUAL_GRAPH_DEFECT
    ROLE: PRIMARY
    KILL_POWER: 10
    COST: 4
    ADVANTAGE: basis_invariant_exact_consumer_functional_and_existing_source_ledger
    DISCRIMINATOR: explicit_graph_norm_envelopes_with_weighted_sum_tending_to_zero
  R2:
    CODE: STRUCTURED_CCM_COMMUTATOR_DIVIDED_DIFFERENCE
    ROLE: RUNNER_UP
    KILL_POWER: 8
    COST: 6
    ADVANTAGE: exploits_exact_rank_two_commutator_and_target_coefficient_structure
    DISCRIMINATOR: source_identity_that_cancels_or_bounds_the_target_defect_without_row_sums
  R3:
    CODE: GLOBAL_RADICAL_WINDOW_DEFECT
    ROLE: HIGH_COST_RUNNER_UP
    KILL_POWER: 10
    COST: 9
    ADVANTAGE: could_turn_the_target_term_into_a_window_or_projection_tail
    DISCRIMINATOR: exact_source_theorem_with_domain_and_boundary_terms_not_a_narrative_radical_claim

ZERO_CONSISTENT_RESULT:
  status: INCONCLUSIVE
  required_discriminator: graph_norm_or_exact_target_defect_identity

FORBIDDEN:
  - infer_finite_Riesz_action_from_H_m_or_L2_norm_alone
  - infer_shifted_archimedean_graph_norm_from_L73_without_a_theorem
  - infer_target_defect_zero_from_inversion_evenness
  - infer_target_defect_zero_from_trial_transform_convergence
  - substitute_the_ambient_associated_operator_A_m
  - claim_finite_Riesz_is_an_ambient_compression
  - use_absolute_row_sums_as_the_source_rate
  - use_an_unproved_or_fitted_operator_norm
  - add_action_decay_as_a_new_hypothesis_and_call_it_H2A_4_1B
  - change_the_selected_shell_row_schedule_scale_or_exact_Rayleigh_shift
  - launch_Lean_before_the_preflight_selects_an_exact_source_contract
  - bundle_sector_floors_ground_Theorem510_or_real_zeros
  - paper_axiom
  - sorry
  - admit
  - typed_hole
  - theorem_weakening

SUCCESS: H2A_4_1B_0_SELECTED_FERRERS_FINITE_FORM_GRAPH_ENVELOPE_PREFLIGHT_CLASSIFIED
FAILURE: H2A_4_1B_0_SOURCE_FORM_GRAPH_OR_TARGET_IDENTITY_UNMAPPED

NEXT_LOAD_BEARING_GAP: H2A_4_1B_SELECTED_FERRERS_ERROR_AND_TARGET_FINITE_FORM_ACTION_DECAY
NEXT_CHEAPEST_DECISIVE_TEST: >-
  Audit the exact source form in dual/graph coordinates. First separate the
  bounded W02/prime pieces from the shifted archimedean graph norm. Then test
  whether the factor-four target has an independent exact source identity.
  Do not write another algebraic receiver and do not run large numerics.

REGISTERED_PREDICTIONS:
  P_H2A41B0_1:
    claim: current_L73_L2_control_does_not_by_itself_bound_the_shifted_archimedean_graph_norm
    probability: 0.97
  P_H2A41B0_2:
    claim: bounded_W02_and_prime_component_envelopes_are_extractable_from_existing_continuous_forms
    probability: 0.88
  P_H2A41B0_3:
    claim: projected_factor_four_target_defect_remains_load_bearing_without_a_new_radical_or_source_action_identity
    probability: 0.95
  LIKELIEST_FAILURE: SHIFTED_ARCH_FORM_GRAPH_NORM_OR_TARGET_RADICAL_IDENTITY_MISSING

PRIOR_PREDICTION_FATES:
  P_H2A41A_1:
    probability: 0.93
    fate: CONFIRMED
    result: exact_vector_and_Riesz_action_splits_closed_by_linearity
  P_H2A41A_2:
    probability: 0.84
    fate: CONFIRMED_EXACTLY
    result: factor_four_MemLp_public_object_required_a_local_copy_of_the_private_H2A3_block
  P_H2A41B_1:
    probability: 0.98
    fate: CONFIRMED_AS_OBJECT_AND_SOURCE_BOUNDARY
    result: L73_error_control_alone_does_not_supply_the_error_action_envelope
  P_H2A41B_2:
    probability: 0.95
    fate: CONFIRMED_AT_CURRENT_SOURCE_LEVEL
    result: target_defect_is_not_definitionally_zero_and_no_current_source_theorem_closes_it
  RETROACTIVE_REPAIR: false

CLOSES:
  - SELECTED_FERRERS_FACTOR_FOUR_TARGET_HILBERT_OBJECT_LOCK
  - SELECTED_FERRERS_SCALED_PHYSICAL_ERROR_PROJECTION_LOCK
  - SELECTED_FERRERS_FINITE_RIESZ_SOURCE_ACTION_EXACT_SPLIT
  - SELECTED_FERRERS_RESIDUAL_SOURCE_ACTION_BUDGET
OPENS: []

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ARISTOTLE_AUTHORIZED: false
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### H2A.4.1A admission

The new file keeps every object on the exact selected shell and exact selected
index. The factor-four target and the physical L73 error live in the same
window Hilbert space, and both are projected through the same orthogonal
projection into the same finite source subspace. The selected trial is the
existing normalized projected `kTrial`; the shift is its exact selected
Rayleigh value. `[COFINAL_FAMILY][LEAN]`

The vector identity is pure projection algebra. Applying the literal finite
Riesz operator and the exact shift gives the action split. The norm theorem
uses only `norm_smul`, the triangle inequality, and nonnegativity of the exact
normalizer. No asymptotic statement, operator continuity, ambient operator, or
compression theorem enters. `[COFINAL_FAMILY][LEAN]`

The finite Riesz object is exactly the literal CCM coefficient operator
transported isometrically to `E_m_N`. Its source file explicitly denies an
ambient associated-operator or compression claim. The H2A.4.1A theorem honors
that boundary. `[FINITE_CELL][LEAN]`

Both plants are load-bearing. The first gives unit vectors converging in the
Hilbert norm to an exact eigenvector while their residuals stay bounded away
from zero under a growing Hermitian operator family. The second has exact
physical error zero but target residual energy two. Thus neither L2 tracking
nor exact target matching supplies an action theorem. `[ABSTRACT][LEAN]`

### Why H2A.4.1B is not authorized as Lean yet

The exact finite source-Weil ledger is already available: W02 plus the
archimedean contribution minus the prime contribution equals the literal
`ccmWeilMatFinite` form on the exact finite Fourier span. This is the correct
source representation for the next audit. `[FINITE_CELL][LEAN]`

The bounded pieces are not the whole story. The prime contribution is an
ambient continuous sesquilinear form, and W02 is also bounded. In contrast,
the shifted archimedean contribution is represented by a weighted Fourier
`L2` map on an exact shifted form domain. The repository proves positivity of
that shifted form, not continuity with respect to the bare `H_m` norm.
Consequently the L73 estimate `norm(e_k) -> 0` does not yet control the graph
quantity required by the finite Riesz action. `[ABSTRACT][LEAN]` **[C10]**

The target term is independent. The factor-four target is inversion-even and
its transform is the desired limit packet, but neither property identifies its
finite projection as an eigenvector or radical vector of the source Weil
form. The zero-error plant rejects exactly that inference. `[ABSTRACT][LEAN]`
**[C04]**

This boundary agrees with the primary source: the prolate packet `k_lambda`
is presented as an educated guess for a scalar multiple of the actual lowest
Weil eigenfunction, and rigorously justifying that approximation is called the
main remaining obstacle. `[COFINAL_FAMILY][PAPER]`

## FINAL PROPOSAL

Ratify H2A.4.1A exactly at its declared scope. Do not immediately formalize a
rate receiver. Run one source-locked, read-only graph-form preflight. Its first
job is to isolate the shifted archimedean graph norm from the bounded W02 and
prime pieces. Its second job is to decide whether the projected factor-four
target has a genuine source identity or is the actual ground-to-trial wall.

Registered outcome:

```text
The bounded W02/prime estimates will be cheap. The first substantive missing
quantity will be a shifted-archimedean graph norm for the physical error, and
the target defect will remain open unless an exact radical/window identity is
located.
```

## STRONGEST ATTACK

The strongest reviewer objection is:

```text
You decomposed the residual into two terms, but both terms are just the
original missing operator-action theorem with new names.
```

The objection is valid against any immediate H2A.4.1B receiver. H2A.4.1A is
still useful because it separates two logically independent obstructions and
ships two falsifiers. The repair is not another triangle inequality. It is an
exact source-form representation with a graph-norm budget for the physical
error and an independent identity or estimate for the target defect.

Failure of that sufficient program will not prove residual decay false. It
will kill only the current L73-to-action representation.

## CODEX DIRECTIVE

Execute exactly the authorized read-only preflight from the YAML header.

```text
NO LEAN EDIT.
NO ARISTOTLE.
NO NUMERICAL FIT.
ONE REPORT FILE.
```

Start from the exact production objects and inspect, at minimum:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersFiniteCCMResidualSourceActionSplit.lean
  G6N1SelectedFerrersFiniteCCMResidualVariance.lean
  D0PstarCCMFiniteRieszOperator.lean
  D0PstarSourceWeilFiniteFourierLedger.lean
  D0PstarSourceWeilSesquilinearForm.lean
  D0PstarShiftedArchSesquilinearForm.lean
  D0PstarPrimeAmbientSesquilinearForm.lean
  D0PstarW02AmbientContinuousForm.lean
  CCMFiniteWeilSourceCommutator.lean
```

Also inspect the pinned primary-source discussion of `k_lambda` versus the
actual lowest Weil eigenfunction. Return exactly one preflight outcome code,
the exact missing theorem statement, a complete rate ledger, and the next
single executable theorem only if the source contract survives.

## META CLOSEOUT

**What became smaller?**

The residual front is no longer one overloaded scalar. It is exactly two
source-action terms on one finite carrier. The generic L2-to-action shortcut is
killed, and the unbounded part is localized to one shifted graph norm.

**What was killed?**

- L73 Hilbert error as an automatic finite Riesz action rate;
- target inversion-evenness as an eigenvector theorem;
- exact physical matching as target residual control;
- another thin rate receiver with the action rate hidden as a premise.

**What must not be tried again?**

Do not use row sums, a fitted matrix norm, ambient compression language, or an
unweighted small error. Do not conflate the bounded prime/W02 pieces with the
shifted archimedean form-domain problem.

**Current smallest named gap:**

```text
H2A_4_1B_0_SELECTED_FERRERS_FINITE_FORM_GRAPH_ENVELOPE_PREFLIGHT
```

**Next cheapest decisive test:**

Determine whether current source data control the shifted-weighted Fourier
norm of `eE_k`, and whether an exact radical/window identity controls `gE_k`.

```yaml
iteration:
  target: H2A.4.1A semantic admission and H2A.4.1B selection
  status: PROGRESS
  failed_strategy: infer_finite_Riesz_action_decay_from_L73_Hilbert_error
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: H2A_4_1B_0_SELECTED_FERRERS_FINITE_FORM_GRAPH_ENVELOPE_PREFLIGHT
  invariant_learned: finite_Weil_action_requires_form_graph_control_not_bare_Hilbert_control
  forbidden_future_move: smuggle_action_decay_through_operator_norm_or_target_evenness
  next_decisive_test: exact_source_dual_graph_and_target_identity_audit
  progress_class: PROOF_PROGRESS
  route_score: 5
```
