# STATUS: PROVED — SEMANTICALLY ADMIT THE LITERAL ANCHORED OUTER DECAY; AUTHORIZE THE EXACT EDGE-TOP FLUX CONSUMER WITH A THREE-WAY BOUNDARY PARTITION
```yaml
PRIMARY: RUN_GOAL058_EDGE_TOP_FLUX_CONSUMER_ASSEMBLY
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-E
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_DIRECT_FOLLOWUP_OF_REQ_2026_08_26_D
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  HEAD: 128a27f0210a2aeffbdef9323aa8d1842fa21991
  HEAD_IS_ORIGIN_RH_CLEAN: true
  PARENT_VERDICT_COMMIT: fce7669ca73bb69ace22ed054710820900256b89
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean
  LEAN_GIT_BLOB: 5c942fb1ae59a49e95540ddb6df40f7c9662c155
  LEAN_SHA256_REPORTED: 0644e33487e20cbba0b95aa06015feb172c3101031d7295506b571a3eb4e0078
  LEAN_LINES: 1026
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_OUTER_POLYNOMIAL_DECAY_2026-08-26.md
  SOURCE_RECORD_GIT_BLOB: 9ea8c5f241994c48e5bdd4ad0c70dc3b88c0bd6d

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS
  LINUX_REPORTED_FULL_BUILD: PASS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_SORRY_COUNT: 0
  LINUX_REPORTED_AXIOMS:
    sturm_outer_polynomial_decay:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrersAnchoredOuterPolynomialDecay_of_modeAndThetaRates:
      - propext
      - Classical.choice
      - Quot.sound
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  sturm_outer_polynomial_decay:
    status: SEMANTICALLY_ADMITTED
    object: LITERAL_RAW_COMMITTED_PHYSICAL_FERRERS_SERIES
    input: eigenvalue_window_plus_half_window_L2_mass
    output: abs_phi_le_65536_sqrt_B_div_lambda_pow_6_on_outer_half
    scope: ABSTRACT
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  selectedFerrersAnchoredOuterPolynomialDecay_of_modeAndThetaRates:
    status: SEMANTICALLY_ADMITTED_AS_EXACT_CONDITIONAL_COFINAL_SUPPLIER
    object:
      - centerAnchorScalarZero_k_times_literal_selected_h0_k
      - centerAnchorScalarFour_k_times_literal_selected_h4_k
    inputs:
      - F72_mode_rate_hmode
      - differential_eigenvalue_theta_rate
    output: both_literal_anchored_modes_are_O_lambda_pow_neg_6_on_outer_half
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  CLAIMS_EXPONENTIAL_DECAY: false
  CLAIMS_OUTER_DEFECT_DERIVATIVE_RATE: false
  CLAIMS_EDGE_TOP_CONSUMER: false

SEMANTIC_AUDIT:
  EXACT_SOURCE_OBJECT: PASS
  OUTER_POTENTIAL_SIGN: PASS
  ZERO_FLUX_ENDPOINT: PASS
  MONOTONICITY_DIRECTION: PASS
  THREE_BLOCK_RECURSION: PASS
  POINTWISE_RATE:
    proved_internal: O_lambda_pow_neg_13_over_2
    exported_weaker_rate: O_lambda_pow_neg_6
    weakening_valid_for_lambda_ge_one: true
  ANCHORED_L2:
    source: existing_hmode_plus_explicit_D0_D4_gaussian_envelope
    individual_anchor_upper_bound_used: false
    scale_cancellation_exact: true
    uniform_mass_constant: 2032129
  FORBIDDEN_ENDPOINT_WEIGHTED_FTC_USED: false
  DERIVATIVE_SUP_NORM_USED: false
  DELTA_SECOND_DERIVATIVE_USED: false
  NUMERICS_USED_AS_PROOF: false
  NEW_ANALYTIC_SOURCE_USED: false
  API_NOTE:
    dummy_existential_C_in_selected_theorem: NONFATAL_REDUNDANCY
    repair_old_file: forbidden_append_only
    next_consumer_must_use_literal_fixed_bound_not_the_dummy_witness

SOURCE_DISCRIMINATOR:
  SATZ9_FIXED_MODE_HIGHER_ORDER_OUTER_RATE:
    fate: REFUTED_AT_CURRENT_AUDITED_SOURCE_SCOPE
  DIRECT_SELECTED_ODE_OUTER_DECAY:
    fate: PROVED_AT_REPORTED_KERNEL_GATE

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_EDGE_TOP_FLUX_CONSUMER_ASSEMBLY
  MODE: ONE_GOAL_ONE_COMMIT
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEdgeTopFluxConsumer.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_EDGE_TOP_FLUX_CONSUMER_2026-08-26.md
  PUBLIC_DEFINITION: selectedFerrersDefectEdgeTopBudget
  REQUIRED_PUBLIC_THEOREM: selectedFerrersDefectEdgeTopBudget_bandwidthNegligible_of_modeChiThetaRates
  OPTIONAL_PUBLIC_RATE_THEOREM: selectedFerrersDefectEdgeTopBudget_bound_of_modeChiThetaRates
  REQUIRED_OUTPUTS:
    - exists_Ctop_eventually_top_budget_le_Ctop_div_lambda_pow_3_over_2
    - Tendsto_top_budget_squared_times_inverse_physical_bandwidth_to_zero
  REQUIRED_INPUTS:
    - hmode_F72_mode_rate
    - hchi_F72_3B_chi_defect_rate
    - htheta_differential_eigenvalue_rate
  NEW_ANALYTIC_INPUT: none
  hchi_is_new_supplier: false
  hchi_role: bound_the_exact_source_packet_coefficients_on_the_existing_frozen_input_ledger

EXACT_OBJECT_LOCK_FOR_NEXT_TRANSACTION:
  SOURCE_PACKET: selectedFerrersLemma73SourcePacket
  SOURCE_PACKET_EXPANSION: >-
    selectedFerrersLemma73SourceScale * prolateCombination equals exactly
    one quarter of chi0 times the literal mode-four anchored mode minus
    three chi2 times the literal mode-zero anchored mode.
  TARGET_PACKET: four_mul_explicitCCMLimitH
  TARGET_EXPANSION: one_quarter_times_D4_minus_three_D0
  DEFECT: SOURCE_PACKET_MINUS_TARGET_PACKET
  TOP_BUDGET: >-
    The literal log-window integral of sqrt(u) times the norm of the finite
    derivative-defect comb restricted to the unique seam-free uppermost
    lattice cell.
  PROHIBITED_SURROGATES:
    - raw_unanchored_mode
    - one_mode_replacement_of_the_two_mode_packet
    - an_existential_majorant_not_equal_to_the_literal_top_functional
    - numerical_gaussian_fit

MANDATORY_MODE_SPLIT:
  decision: APPLY_FLUX_PER_MODE_THEN_RECOMBINE_EXACTLY
  reason: >-
    prolateCombination is a linear combination of two modes with distinct
    differential eigenvalues.  It is not one eigenmode and must not be fed
    to a one-mode Sturm flux theorem with a fabricated common theta.
  mode_four_defect: chi0_times_anchored_h4_minus_D4
  mode_zero_defect: chi2_times_anchored_h0_minus_D0
  packet_defect_derivative: one_quarter_times_mode_four_defect_derivative_minus_three_times_mode_zero_defect_derivative
  C04_GUARD: true
  C10_GUARD: true

BOUNDARY_PARTITION:
  NON_TOP_DERIVATIVE:
    condition: (n_plus_one)_times_u_le_lambda
    status: already_closed_by_nodes_3A_3B_at_sqrt_log_rate
  TOP_DERIVATIVE:
    condition: n_times_u_lt_lambda_and_lambda_lt_(n_plus_one)_times_u
    status: target_of_this_transaction
  PHYSICAL_SEAM:
    condition: n_times_u_eq_lambda
    status: handled_by_existing_W4_jump_seam_ledger_not_by_deriv_at_edge
  coverage_requirement: >-
    Prove that every active lattice term is in exactly the non-top, strict-top,
    or seam class, including all equality boundaries.  Do not erase seams as
    measure-zero before proving the exact partition.

RATE_LEDGER:
  outer_mode_value_rate: O_lambda_pow_neg_6
  one_mode_flux_source_rate: O_lambda_pow_neg_2
  exact_distance_factor_cancellation: >-
    abs_F_y <= (lambda-y)*sup_abs_r and
    lambda_squared-y_squared >= lambda*(lambda-y)
  one_mode_derivative_defect_rate: O_lambda_pow_neg_3
  exact_packet_derivative_defect_rate: O_lambda_pow_neg_3
  top_budget_rate: O_lambda_pow_neg_3_over_2
  physical_bandwidth_lower_rate: Omega_lambda
  squared_ratio_rate: O_lambda_pow_neg_4
  downstream_condition: bandwidth_negligible

PROOF_ORDER:
  - run_capability_catalog_preflight_before_minting_helpers
  - prove_or_reconstruct_the_exact_public_source_packet_anchored_mode_identity
  - prove_the_exact_D4_D0_identity_for_four_mul_explicitCCMLimitH
  - derive_eventual_abs_chi0_and_abs_chi2_bounds_from_hchi
  - apply_the_outer_decay_supplier_to_both_literal_anchored_modes
  - prove_one_mode_outer_flux_derivative_bound_for_each_exact_theta_and_cylinder
  - recombine_the_two_mode_derivative_defects_with_the_exact_packet_coefficients
  - define_the_literal_strict_top_filtered_finite_comb
  - prove_non_top_top_seam_partition_and_unique_strict_top_index
  - prove_y_top_greater_than_lambda_over_two
  - integrate_the_pointwise_top_bound_over_the_log_window
  - prove_the_lambda_pow_neg_3_over_2_budget_rate
  - close_the_squared_budget_over_physical_bandwidth_limit

FORBIDDEN_IN_NEXT_TRANSACTION:
  - applying_one_common_eigenvalue_to_prolateCombination
  - using_deriv_at_the_physical_seam
  - folding_the_W4_jump_term_into_the_top_derivative_term
  - endpoint_FTC_through_inverse_lambda_squared_minus_y_squared
  - derivative_sup_norm
  - delta_second_derivative
  - individual_anchor_upper_bound
  - source_scale_inverse_as_an_anchor_bound
  - changing_existing_uniform_D_theorems
  - claiming_the_numeric_exp_minus_pi_lambda_squared_over_four_law
  - adding_Meixner_or_Sips_as_an_axiom
  - weakening_the_literal_top_functional_to_an_unrelated_majorant

EXPECTED_AXIOM_PROFILES:
  ALL_PUBLIC:
    - propext
    - Classical.choice
    - Quot.sound

VERIFICATION_HANDOFF:
  WORKDIR_q3_lean_aristotle:
    - lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersEdgeTopFluxConsumer.lean
    - lake build Q3.Proofs.RouteB.G6N1SelectedFerrersEdgeTopFluxConsumer
  WORKDIR_repo_root:
    - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersEdgeTopFluxConsumer.lean

SUCCESS_CODE: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE_LEAN
FAILURE_CODE: GOAL058_EDGE_TOP_FLUX_OBJECT_OR_BOUNDARY_PARTITION_GAP

CLOSES:
  - SELECTED_ANCHORED_OUTER_POLYNOMIAL_DECAY_KERNEL_ADMISSION
  - DIRECT_SELECTED_ODE_OUTER_DECAY_REPRESENTATION
  - SATZ9_HIGHER_ORDER_SOURCE_ACQUISITION_AS_CRITICAL_PATH
OPENS: []
CARRIES_OPEN:
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_6_MODE_AND_CHI_RATE_INPUTS

NEXT_LOAD_BEARING_GAP: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: GOAL058_EDGE_TOP_FLUX_CONSUMER_ASSEMBLY

PREDICTION_FATES:
  P_SATZ9_HIGH_ORDER_1:
    prior_probability: 0.38
    fate: REFUTED_AT_AUDITED_SOURCE_SCOPE
  P_OUTER_TOP_2:
    prior_probability: 0.78
    prior_claim: source_faithful_forbidden_region_estimate_closes_the_direct_top_contract_without_derivative_sup_norm
    fate: CONFIRMED_ON_THE_ANALYTIC_SUPPLIER_SIDE_TOP_CONSUMER_PENDING
  P_LEAN_OUTER_1:
    prior_probability: 0.76
    fate: CONFIRMED_WITH_ROUTE_DELTA_FROM_CACCIOPPOLI_TO_ENERGY_MONOTONICITY
  P_WC_TOP_1:
    prior_probability: 0.72
    prior_claim: exact_flux_ODE_plus_the_already_committed_uniform_C0_rate_is_sufficient
    fate: REFUTED_AS_STATED_AND_NOT_RETROACTIVELY_REPAIRED
  P_EDGE_TOP_ASSEMBLY_1:
    probability: 0.90
    prediction: >-
      Per-mode flux, exact two-mode packet algebra, and the strict-top/seam
      partition close the O(lambda^-3/2) top budget without a new analytic input.
  P_EDGE_TOP_ASSEMBLY_2:
    probability: 0.96
    prediction: >-
      Once the top budget rate is proved, the selected schedule closes its
      squared ratio to physical bandwidth at O(lambda^-4).
  LIKELIEST_FAILURE:
    class: COMPLEX_TO_REAL_ANCHOR_COERCION_OR_STRICT_TOP_SEAM_NORMAL_FORM
    response: keep_the_literal_objects_and_reduce_to_one_exact_crosswalk_helper

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
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

The source is semantically admitted at its exact boundary.  The core theorem is
about the literal raw physical Ferrers series and proves a stronger
`lambda^(-13/2)` estimate before exporting the requested `lambda^(-6)` bound.
The selected theorem then derives a uniform half-window `L2` budget for the two
literal center-anchored modes from the existing cylinder approximation; no
individual bound on either anchor is imported.  The reported kernel gate and
axiom profiles match the intended theorem surface.

The implementation delta is acceptable.  The verdict prescribed a Caccioppoli
route because it avoided the false endpoint-FTC step.  The committed proof found
a shorter identity on the same object: the energy product

\[
 E(y)=((\lambda^2-y^2)\phi'(y))\phi(y)
\]

has nonnegative derivative in the outer positive-potential region and tends to
zero at the singular endpoint.  Therefore `E <= 0`, `phi^2` is nonincreasing,
and three precommitted `lambda/32` block recursions yield the same outer mass
rate without a cutoff.  No hypothesis was added and no conclusion was weakened.

The next node must preserve the exact two-mode structure.  The port packet is
not one eigenmode: its mode-zero and mode-four summands have different
differential eigenvalues.  A proof that applies a single Sturm flux equation
directly to `prolateCombination` would be a wrong-object theorem even if it
compiled.  The legal route applies flux separately to the two literal anchored
modes and then uses the exact source-scale algebra to recombine them.

The lattice boundary also has three classes, not two.  A derivative term with
`n*u = lambda` sits at the physical seam and belongs to the already committed
W4 jump ledger.  The new top derivative functional must use the strict class

\[
 n u<\lambda<(n+1)u,
\]

while node 3B retains `(n+1)u <= lambda`.  This partition prevents an undefined
edge derivative from being silently inserted into the top budget.

## FINAL PROPOSAL

Run one Lean transaction for the literal defect top functional.  First expose
or reconstruct the exact packet identity

\[
 \text{sourcePacket}_k
 =\frac14\left(\chi_{0,k}\,\phi_{4,k}
              -3\chi_{2,k}\,\phi_{0,k}\right),
\]

where `phi_0` and `phi_4` are the literal anchored selected modes.  Pair it with

\[
 4H=\frac14(D_4-3D_0).
\]

Use the new outer mode theorem and the existing `hchi` rate to bound both exact
one-mode defects on the outer half.  Apply the endpoint flux cancellation to
each mode separately.  The exact distance factor cancels before division by
the degenerate weight, giving derivative-defect rate `O(lambda^(-3))` at every
strict top point.  Integration over the log window gives

\[
 T_k=O(\lambda_k^{-3/2}),
 \qquad
 \frac{T_k^2}{\operatorname{physicalFourierBandwidth}_k}
 =O(\lambda_k^{-4})\to0.
\]

The numerical Gaussian law is not needed and is not promoted.

## STRONGEST ATTACK

The strongest attack is a source-object mismatch hidden by linearity.  The
selected packet combines two different eigenmodes.  Linearity of the function
does not create one common eigenvalue.  The packet derivative estimate is valid
only after two separate one-mode flux estimates and exact recombination.  This
is the C04/C10 guard for the next node.

The second attack is the seam.  `deriv` at the zero-extension edge is not the
interior derivative consumed by the comb.  Equality `n*u=lambda` must remain in
the W4 jump ledger.  Declaring it measure-zero before proving the exact
non-top/top/seam decomposition would leave the theorem about a different
functional.

The third attack is a prefactor overclaim.  The abstract one-mode rate map has a
clean `8*pi^2*A` leading budget, but the literal two-mode packet also carries
fixed cylinder and coefficient constants.  The consumer theorem should export
an exact existential constant with the `lambda^(-3/2)` exponent, not assert the
literal prefactor `8*pi^2` unless the complete algebra produces it.

## CODEX / LINUX DIRECTIVE

```text
TASK_ID: GOAL058_EDGE_TOP_FLUX_CONSUMER_ASSEMBLY
MODE: ONE_GOAL_ONE_COMMIT

OBJECTIVE:
  Prove the literal selected Ferrers defect edge-top budget is bandwidth-negligible.

READ_FIRST:
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersZeroMassCylinderPacket.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmDefectTruncatedEnergy.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmWeightedConsumerNonTopRate.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersScaleBandwidthClosure.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitHDerivativeCombBudget.lean

CATALOG_PREFLIGHT:
  ./ask.sh "selected Ferrers edge top flux defect derivative budget bandwidth negligible"
  ./ask.sh "source packet chi anchored combination four explicit H"

CREATE:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEdgeTopFluxConsumer.lean
  docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_EDGE_TOP_FLUX_CONSUMER_2026-08-26.md

DO_NOT_EDIT:
  existing Lean files
  prior source records and verdicts
  Q3.Main
  route state

PUBLIC_OBJECT:
  selectedFerrersDefectEdgeTopBudget

PUBLIC_TARGET:
  selectedFerrersDefectEdgeTopBudget_bandwidthNegligible_of_modeChiThetaRates

EXACT_PARTITION:
  non-top: (n+1)*u <= lambda
  strict top: n*u < lambda AND lambda < (n+1)*u
  physical seam: n*u = lambda

SUCCESS:
  exact literal strict-top budget;
  eventual O(lambda^(-3/2)) upper bound;
  top_budget^2 / physicalBandwidth -> 0;
  no new analytic supplier;
  standard axiom triple on every public declaration.

FAILURE:
  GOAL058_EDGE_TOP_FLUX_OBJECT_OR_BOUNDARY_PARTITION_GAP
```

## META CLOSEOUT

**What became smaller?**  The analytic supplier for the outer region is now a
kernel-green conditional theorem.  The remaining top gap is a finite-comb,
per-mode-flux, and asymptotic bookkeeping assembly.

**What was killed?**  Higher-order Satz-9 acquisition as critical path; the need
for an individual anchor bound; endpoint weighted FTC; and a one-eigenvalue
interpretation of the two-mode packet.

**What must not be tried again?**  Numerical exponential fitting, direct flux on
`prolateCombination`, or evaluating the derivative at `n*u=lambda`.

**Current smallest named gap?**
`W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE`.

**Next cheapest decisive test?**  Compile the exact source-packet anchored-mode
identity and the non-top/strict-top/seam partition before writing the long
integral estimate.

**Prediction fate?**  `P_LEAN_OUTER_1` is confirmed.  `P_OUTER_TOP_2` is
confirmed only on the supplier side.  `P_WC_TOP_1` remains refuted as stated;
there is no retroactive repair.

**Memory entry?**

```yaml
iteration: GOAL058_OUTER_DECAY_ADMISSION
target: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
status: PROGRESS
failed_strategy: HIGHER_ORDER_SATZ9_SOURCE_AND_ENDPOINT_WEIGHTED_FTC
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: EDGE_TOP_PER_MODE_FLUX_AND_STRICT_SEAM_PARTITION
invariant_learned: two_mode_packet_requires_two_eigenvalue_fluxes_and_exact_recombination
forbidden_future_move: direct_single_theta_flux_on_prolateCombination
next_decisive_test: exact_packet_identity_plus_three_way_lattice_partition_compiles
```
