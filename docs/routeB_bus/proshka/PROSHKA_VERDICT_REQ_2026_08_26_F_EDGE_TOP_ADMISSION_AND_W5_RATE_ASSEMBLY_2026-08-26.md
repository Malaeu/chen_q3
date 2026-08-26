# STATUS: PROVED — EDGE-TOP STRICT-LATTICE CONSUMER SEMANTICALLY ADMITTED; W5 ANALYTIC COMPONENTS COMPLETE; FINAL RATE-AWARE ASSEMBLY AUTHORIZED

```yaml
PRIMARY: RUN_GOAL058_SELECTED_FERRERS_W5_RATE_ASSEMBLY
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-F
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_DIRECT_FOLLOWUP_OF_REQ_2026_08_26_E
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  HEAD: c5c88de8caeea0a3cb56b1e51cd98b6f9abe17a0
  HEAD_IS_ORIGIN_RH_CLEAN: true
  PARENT_VERDICT_COMMIT: ed7c8f7dd4197af57e9dc2a037cbc793611809e7
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEdgeTopFluxConsumer.lean
  LEAN_GIT_BLOB: 3ec01188fd09763f1fd169291242af85b299ecdf
  LEAN_SHA256_REPORTED: 4c459466ad3f8041ca99c47e1336a99e8d8a3e51f9bb7d9d03552ea9317b50df
  LEAN_LINES: 1583
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_EDGE_TOP_FLUX_CONSUMER_2026-08-26.md
  SOURCE_RECORD_GIT_BLOB: 41fd1b7a405bb275f7b393a7267e48e038a73b01

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS
  LINUX_REPORTED_FULL_BUILD: PASS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_SORRY_COUNT: 0
  PUBLIC_SURFACE_COUNT:
    theorems_with_axiom_prints: 8
    public_definitions_without_axiom_print: 1
  LINUX_REPORTED_AXIOMS_FOR_ALL_EIGHT_THEOREMS:
    - propext
    - Classical.choice
    - Quot.sound
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  selectedFerrersLemma73SourcePacket_eq_anchored_combination:
    status: SEMANTICALLY_ADMITTED
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
    object: literal_selectedFerrersLemma73SourcePacket
    exact_identity: sourcePacket_eq_one_quarter_chi0_a4h4_minus_three_chi2_a0h0
  four_mul_explicitCCMLimitH_eq_cylinder:
    status: SEMANTICALLY_ADMITTED
    scope: ABSTRACT
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  edgeTop_boundary_trichotomy:
    status: SEMANTICALLY_ADMITTED
    scope: ABSTRACT
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  edgeTop_strictTop_unique:
    status: SEMANTICALLY_ADMITTED
    scope: ABSTRACT
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  edgeTop_strictTop_outer:
    status: SEMANTICALLY_ADMITTED
    scope: ABSTRACT
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  sturm_outer_flux_derivative_bound:
    status: SEMANTICALLY_ADMITTED
    scope: ABSTRACT
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
    exact_rate: abs_phi_prime_le_41_A_div_lambda_cubed
  selectedFerrersDefectEdgeTopBudget:
    status: EXACT_LITERAL_STRICT_TOP_FUNCTIONAL
    scope: COFINAL_FAMILY
    verifier: DEFINITIONAL
  selectedFerrersDefectEdgeTopBudget_bound_of_modeChiThetaRates:
    status: SEMANTICALLY_ADMITTED_AS_CONDITIONAL_COFINAL_RATE
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
    rate: O_lambda_pow_neg_three_over_two
  selectedFerrersDefectEdgeTopBudget_bandwidthNegligible_of_modeChiThetaRates:
    status: SEMANTICALLY_ADMITTED_AS_CONDITIONAL_COFINAL_SUPPLIER
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
    exported_upper_rate: O_lambda_pow_neg_four
    sharp_asymptotic_claimed: false

SEMANTIC_GUARDS:
  EXACT_SOURCE_OBJECT: PASS
  DISTINCT_MODE_EIGENVALUES_PRESERVED: PASS
  COMMON_THETA_ON_PROLATE_COMBINATION_USED: false
  STRICT_TOP_FILTER_LITERAL: PASS
  PHYSICAL_SEAM_EXCLUDED: PASS
  SEAM_ROUTED_TO_W4_LEDGER: PASS_AT_EXISTING_CONTRACT
  NON_TOP_ROUTED_TO_NODE_3B: PASS_AT_EXISTING_CONTRACT
  DISTANCE_FACTOR_CANCELLED_BEFORE_WEIGHT_DIVISION: PASS
  ENDPOINT_WEIGHTED_FTC_USED: false
  DERIVATIVE_SUP_NORM_USED: false
  DELTA_SECOND_DERIVATIVE_USED: false
  INDIVIDUAL_ANCHOR_BOUND_USED: false
  NUMERICS_USED_AS_PROOF: false
  NEW_ANALYTIC_HYPOTHESIS: none

FRONT_STATUS_CORRECTION:
  W5_ANALYTIC_COMPONENTS:
    H_EXPLICIT_COMB: CLOSED
    NON_TOP_DEFECT: CLOSED_AT_SQRT_LOG_RATE
    PHYSICAL_SEAM: CLOSED_BY_EXISTING_W4_JUMP_LEDGER
    STRICT_TOP_DEFECT: CLOSED_AT_BANDWIDTH_NEGLIGIBLE_RATE
    status: COMPONENT_COMPLETE
  W5_ROUTE_LEVEL_OUTPUT:
    target: SelectedProjectionTailDecay
    status: OPEN_ASSEMBLY_ONLY
    reason: >-
      No current public theorem imports the new strict-top supplier, instantiates
      the node-1 energy ledger for both selected modes, combines H/non-top/top,
      builds the growing first-order coefficient constant C_k, proves
      C_k^2 / physicalBandwidth_k -> 0, and invokes the rate-aware receiver.
  FORBIDDEN_LABEL: W5_FULLY_CLOSED_IN_LEAN_BEFORE_FINAL_ASSEMBLY

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_W5_RATE_ASSEMBLY
  MODE: ONE_GOAL_ONE_COMMIT
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_W5_RATE_ASSEMBLY_2026-08-26.md
  REQUIRED_PUBLIC_THEOREM: selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
  OPTIONAL_PUBLIC_INTERMEDIATE: selectedFerrersFirstOrderCoefficientRate_of_modeChiThetaRates
  REQUIRED_CONCLUSION: SelectedProjectionTailDecay S
  REQUIRED_PUBLIC_INPUTS:
    - S_ProlateCanonicalSourceData
    - hFamily_SelectedFerrersPreAnchorProductionFamilyCrosswalk_S
    - existing_F72_mode_rate_family
    - existing_chi_defect_rate_family
    - exact_selected_differential_eigenvalue_rate_inputs_needed_by_node_1
  NEW_ANALYTIC_INPUT: none
  PRIVATE_DERIVATIONS_REQUIRED:
    - instantiate_sturm_defect_energy_rate_ledger_for_mode_zero
    - instantiate_sturm_defect_energy_rate_ledger_for_mode_four
    - apply_sturm_weighted_consumer_nonTop_rate_per_mode
    - recombine_nonTop_two_mode_defect_exactly
    - add_explicit_H_derivative_comb_budget
    - add_selectedFerrersDefectEdgeTopBudget_bound
    - use_existing_W4_jump_and_endpoint_ledgers
    - produce_selectedFerrersAbelFourierDecayBudget_growing_rate
    - transport_coefficient_envelope_through_source_scale_and_hFamily
    - prove_C_k_squared_over_physical_bandwidth_tends_to_zero
    - invoke_selectedProjectionTailDecay_of_firstOrderCoefficientRate
  RATE_COMBINATION_GUARD: >-
    Prove the squared-ratio limit by an explicit finite sum-of-squares majorant,
    for example (a+b+c)^2 <= 3(a^2+b^2+c^2). Do not infer it from informal
    O-notation or from separate unsquared limits.
  PRIVATE_RECONSTRUCTION_ALLOWED: >-
    The existing derivative reduction is private. Reconstruct the minimal exact
    reduction in the new file or expose a deliberately named public adapter;
    do not weaken the derivative functional.

FORBIDDEN_IN_NEXT_TRANSACTION:
  - claim_uniform_D_for_the_non_top_band
  - change_existing_uniform_D_theorems
  - apply_one_common_eigenvalue_to_prolateCombination
  - evaluate_deriv_at_the_physical_seam
  - fold_W4_jump_mass_into_the_strict_top_derivative_integral
  - replace_literal_top_budget_by_an_existential_majorant
  - derivative_sup_norm
  - delta_second_derivative
  - source_scale_inverse_as_individual_anchor_bound
  - numerical_gaussian_fit
  - raw_O_notation_as_a_limit_proof
  - new_analytic_supplier
  - route_promotion_or_RH_claim

EXPECTED_AXIOM_PROFILES:
  ALL_PUBLIC:
    - propext
    - Classical.choice
    - Quot.sound

VERIFICATION_HANDOFF:
  WORKDIR_q3_lean_aristotle:
    - lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
    - lake build Q3.Proofs.RouteB.G6N1SelectedFerrersW5RateAssembly
  WORKDIR_repo_root:
    - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean

SUCCESS_CODE: SELECTED_FERRERS_W5_RATE_ASSEMBLY_TO_PROJECTION_TAIL_LEAN
FAILURE_CODE: GOAL058_W5_SELECTED_ENERGY_INSTANTIATION_OR_RATE_COMPOSITION_GAP

CLOSES:
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  - W5_STRICT_TOP_OBJECT_AND_BOUNDARY_PARTITION
  - W5_OUTER_FLUX_DERIVATIVE_RATE
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_W5_RATE_ASSEMBLY_TO_PROJECTION_TAIL
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_MODE_AND_CHI_RATE_INPUTS

NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_W5_RATE_ASSEMBLY_TO_PROJECTION_TAIL
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: GOAL058_SELECTED_FERRERS_W5_RATE_ASSEMBLY

PREDICTION_FATES:
  P_EDGE_TOP_ASSEMBLY_1:
    prior_probability: 0.90
    fate: CONFIRMED
  P_EDGE_TOP_ASSEMBLY_2:
    prior_probability: 0.96
    fate: CONFIRMED
  P_OUTER_TOP_2:
    prior_probability: 0.78
    fate: CONFIRMED_FULLY_THROUGH_TOP_CONSUMER
  P_WC_TOP_1:
    prior_probability: 0.72
    fate: REFUTED_AS_STATED_NO_RETROACTIVE_REPAIR
  P_W5_FINAL_ASSEMBLY_1:
    probability: 0.86
    prediction: >-
      The existing node-1 rate ledger, non-top sqrt-log receiver, exact H node,
      W4 seam ledger and strict-top rate assemble into SelectedProjectionTailDecay
      without a new analytic hypothesis.
  LIKELIEST_FAILURE:
    class: SELECTED_MODE_ENERGY_CONSTANT_OR_PRIVATE_DERIVATIVE_REDUCTION_API
    response: preserve_the_public_target_and_reduce_to_one_exact_adapter

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

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

The committed theorem proves the exact missing strict-top component. The source
packet is not treated as one eigenmode: its two literal anchored modes retain
separate differential eigenvalues, and the proof recombines only after applying
the one-mode flux estimate. The strict inequalities remove the physical seam
from every derivative evaluation. `[COFINAL_FAMILY][LEAN]`

The per-mode flux estimate is mathematically sound. Outer value decay
`A/lambda^6` makes the flux source at most `41 A/lambda^2`; integration from
`y` to the zero-flux endpoint contributes `(lambda-y)`, and
`lambda^2-y^2 >= lambda(lambda-y)` cancels that distance before division. Thus
`|phi'(y)| <= 41 A/lambda^3`. `[ABSTRACT][LEAN]`

The selected strict-top budget is the literal log-window functional with filter
`n u < lambda < (n+1)u`. At most one index survives for each spacing, its point
lies in the outer half, and the integrated rate is
`O(lambda^(-3/2))`. Squaring and dividing by the literal selected physical
bandwidth gives a proved upper rate `O(lambda^(-4))`; this is a sufficient upper
rate, not a claimed sharp asymptotic. `[COFINAL_FAMILY][LEAN]`

## STRONGEST ATTACK

The strongest remaining objection is not to the strict-top theorem. It is to the
sentence "the W5 derivative wall is fully closed." The repository currently has
all four analytic pieces, but it does not yet have one public theorem that
assembles those pieces into the growing first-order coefficient envelope and
then calls `selectedProjectionTailDecay_of_firstOrderCoefficientRate`.

Compilation of separate components does not create their conjunction. In
particular, the non-top theorem is abstract and must still be instantiated for
the two selected modes using the node-1 energy ledger; the square of the combined
coefficient constant must then be shown negligible against the same physical
bandwidth. This is an assembly gap, not a new analytic wall.

The repaired statement is therefore:

```text
W5 analytic decomposition: complete.
W5 strict-top supplier: proved.
W5 route-level SelectedProjectionTailDecay: one assembly theorem remains.
```

## FINAL PROPOSAL

Run exactly one final W5 transaction. Its public endpoint is

```lean
selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
```

with conclusion `SelectedProjectionTailDecay S`. It must consume only the
existing production-family crosswalk and the already frozen rate families. All
Sturm-energy instantiation, two-mode recombination, rate algebra, scale control
and bandwidth calculation stay internal.

## CODEX / LINUX DIRECTIVE

```text
TASK_ID: GOAL058_SELECTED_FERRERS_W5_RATE_ASSEMBLY

MODE:
  ONE_GOAL_ONE_COMMIT

OBJECTIVE:
  Prove SelectedProjectionTailDecay for the production family by assembling
  the already kernel-green H, non-top, seam and strict-top W5 components and
  invoking selectedProjectionTailDecay_of_firstOrderCoefficientRate.

READ_FIRST:
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmDefectTruncatedEnergy.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmWeightedConsumerNonTopRate.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitHDerivativeCombBudget.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEdgeTopFluxConsumer.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5DerivativeBudgetRate.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFirstOrderBudgetApplication.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersScaleBandwidthClosure.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFirstOrderProjectionTailReceiver.lean

PREFLIGHT:
  Run ./ask.sh for the exact selected-energy instantiation and W5 assembly
  names before minting helpers. Reuse any exact supplier found.

CREATE:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
  docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_W5_RATE_ASSEMBLY_2026-08-26.md

DO_NOT_EDIT:
  existing Lean files
  prior verdicts or source records
  route state
  Q3.Main

PUBLIC_SURFACE:
  required:
    selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
  optional:
    selectedFerrersFirstOrderCoefficientRate_of_modeChiThetaRates

SUCCESS:
  SELECTED_FERRERS_W5_RATE_ASSEMBLY_TO_PROJECTION_TAIL_LEAN

FAILURE:
  GOAL058_W5_SELECTED_ENERGY_INSTANTIATION_OR_RATE_COMPOSITION_GAP
```

## META CLOSEOUT

**What became smaller?** The open strict-top functional disappeared. The W5
front is reduced to one source-specific rate assembly theorem.

**What was killed?** A common-eigenvalue proof for `prolateCombination`, seam
derivative evaluation, endpoint weighted FTC, derivative sup norms and a
uniform-D claim for the non-top edge band.

**What must not be tried again?** Do not relabel component completeness as the
public route consumer. Do not replace the squared ratio limit by informal
asymptotic notation.

**Current smallest named gap:**
`SELECTED_FERRERS_W5_RATE_ASSEMBLY_TO_PROJECTION_TAIL`.

**Next cheapest decisive test:** catalogue preflight for an existing selected
energy-instantiation/assembly theorem; if absent, write the one file above.

**Prediction fate:** `P_EDGE_TOP_ASSEMBLY_1` and `_2` confirmed;
`P_WC_TOP_1` remains refuted as stated.

**Memory entry:**

```yaml
iteration:
  target: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  status: PROGRESS
  failed_strategy: uniform_edge_band_from_weighted_energy_alone
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_W5_RATE_ASSEMBLY_TO_PROJECTION_TAIL
  invariant_learned: preserve_two_mode_eigenvalues_and_three_way_boundary_partition
  forbidden_future_move: claim_route_closure_before_public_rate_assembly
  next_decisive_test: ask_catalog_then_build_one_selected_rate_assembly
```
