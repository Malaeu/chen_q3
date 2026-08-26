# STATUS: CONDITIONAL — RATIFY NODES 3A/3B AND THE RATE-AWARE RECEIVER; KEEP THE DIRECT TOP CONTRACT; DO NOT PROMOTE E1/E2 OR SOURCE THEM FROM THE CURRENT SATZ-9/CCM STATEMENTS
```yaml
PRIMARY: RUN_EDGE_TOP_DIRECT_OUTER_ASYMPTOTIC_SOURCE_PREFLIGHT
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-C
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_DIRECT_FOLLOWUP_OF_REQ_2026_08_26_B
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  HEAD: 92ee11cba601c8d7ffc8fe7b1a9012409469145b
  NODE_3A_3B_COMMIT: 1a229b3aa3d46d3e386980295c790431fa1ed7ff
  NODE_3A_3B_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmWeightedConsumerNonTopRate.lean
  NODE_3A_3B_BLOB: bddf326b5dad68cda67c14204c35749beb1ca742
  RATE_RECEIVER_COMMIT: a39c28e58b72f0b51d00e45e4f912747e571fe75
  RATE_RECEIVER_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFirstOrderProjectionTailReceiver.lean
  RATE_RECEIVER_BLOB: 67e775e2d528b2d445ff987845b60cfcd69eb3d1
  EDGE_PREFLIGHT_PATH: docs/routeB_bus/LINUX_EDGE_TOP_PREFLIGHT_GOAL058_GAUSSIAN_DEATH_2026-08-26.md
  EDGE_PREFLIGHT_BLOB: b941c6d0e91c9c596e796b54421e91fda55f5076
  SATZ9_USAGE_CARD: docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md
  F72_1_SCOPE_VERDICT: docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_I_MEIXNER_SCHAEFKE_F72_1_PARAMETER_CHAIN_2026-08-20.md

KERNEL_ADMISSION:
  STURM_WEIGHTED_CONSUMER_INTERIOR:
    status: RATIFIED_AT_REPORTED_KERNEL_GATE
    theorem: sturm_weighted_consumer_interior_bound
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  STURM_WEIGHTED_CONSUMER_NON_TOP_SQRT_LOG_RATE:
    status: RATIFIED_AT_REPORTED_KERNEL_GATE
    theorem: sturm_weighted_consumer_nonTop_sqrtLog_bound
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  RATE_AWARE_FIRST_ORDER_RECEIVER:
    status: RATIFIED_AT_REPORTED_KERNEL_GATE
    theorem: selectedProjectionTailDecay_of_firstOrderCoefficientRate
    exact_consumer: C_k_squared_times_inverse_physical_bandwidth_tends_to_zero
    scope: COFINAL_FAMILY
    verifier: LEAN_REPORTED_NOT_JUDGE_RERUN
  JUDGE_RERAN_LAKE_BUILD: false

EDGE_TOP_DIAGNOSTIC:
  TOP_POINT_OUTER_HALF_ARITHMETIC:
    statement: y_top_is_strictly_greater_than_lambda_over_two
    status: PAPER_PASS_LEAN_NOT_YET_WRITTEN
    scope: ABSTRACT
    verifier: PAPER
  PROBE:
    status: DIAGNOSTIC_NEVER_A_PROOF
    supports: outer_forbidden_region_decay_is_the_right_mechanism
    does_not_prove:
      - asymptotic_law_T_sim_exp_minus_pi_lambda_squared_over_four
      - any_cofinal_upper_envelope
      - any_Satz9_or_CCM_weighted_remainder
    scope: FINITE_CELL
    verifier: CONDITIONAL
  TWO_PRE_FLOOR_POINTS:
    verdict: CONSISTENT_WITH_EXPONENTIAL_DECAY_NOT_AN_ASYMPTOTIC_CERTIFICATE
  F72_6_NUMERIC_CHECK:
    verdict: SUPPORTS_THE_EXISTING_INPUT_FAMILY_ONLY
    theorem_status_changed: false

PREDICTION_FATES:
  P_LINUX_WC_1:
    fate: CONFIRMED_AT_ENERGY_ONLY_SCOPE
  P_WC_RATE_RECEIVER_1:
    fate: CONFIRMED
  P_WC_TOP_1:
    prior_claim: exact_flux_ODE_and_uniform_C0_control_yield_bandwidth_negligible_top_budget
    fate: REFUTED_AS_STATED
    reason: the_exact_flux_ledger_with_only_the_committed_lambda_minus_two_C0_rate_gives_only_a_polynomially_growing_top_bound
    no_retroactive_repair: true
  NEW_P_OUTER_TOP_2:
    probability: 0.78
    prediction: a_source_faithful_outer_forbidden_region_estimate_closes_the_direct_top_contract_with_no_derivative_sup_norm
    fate: UNTESTED
  NEW_P_SATZ9_HIGH_ORDER_1:
    probability: 0.38
    prediction: the_full_Meixner_Schaefke_construction_contains_an_explicit_uniform_fixed_mode_expansion_of_sufficient_order_to_close_the_top_contract_without_a_weighted_Gaussian_remainder
    fate: UNTESTED

PUBLIC_ROUTE_CONTRACT:
  name: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  statement: top_budget_k_squared_times_inverse_physicalFourierBandwidth_k_tends_to_zero
  status: CARRIED_OPEN
  new_public_outer_envelope_supplier: false
  reason: E1_and_E2_are_proof_representations_not_the_exact_downstream_consumer

E1_ADJUDICATION:
  token: OUTER_GAUSSIAN_C0_DEFECT
  decision: DO_NOT_PROMOTE_AS_PRIMITIVE_SUPPLIER
  reason:
    - cancellation_shaped_statement_between_source_mode_and_cylinder_target
    - current_Satz9_and_CCM_statements_do_not_supply_a_weighted_outer_remainder
    - direct_top_contract_needs_less
  may_be_used_privately_if_proved: true

E2_ADJUDICATION:
  token: OUTER_GAUSSIAN_MODE_BOUND
  raw_statement_decision: REJECT_TYPE_AMBIGUOUS
  defect: raw_S_phys_omits_the_exact_center_anchor_or_source_scale
  repaired_private_shape:
    name: SELECTED_FERRERS_ANCHORED_OUTER_GAUSSIAN_MODE_ENVELOPE
    statement: >-
      There is C >= 0 such that eventually, for y in [lambda_k/2, lambda_k],
      both exact anchored source modes satisfy
      norm(centerAnchorScalarZero(k) * h0_k(y)) <= C*exp(-y^2/4) and
      norm(centerAnchorScalarFour(k) * h4_k(y)) <= C*exp(-y^2/4).
    role: OPTIONAL_PRIVATE_LEMMA_ONLY
  reason_for_preferring_repaired_E2_over_E1_if_a_weighted_source_exists: >-
    It is source-local on the two literal selected eigenmodes; the explicit
    cylinder targets then give the defect/source-residual envelope without
    importing cancellation as a hypothesis.

CURRENT_SOURCE_ADJUDICATION:
  MEIXNER_SCHAEFKE_SATZ9_AS_VERIFIED:
    statement_strength: normalized_additive_uniform_error_O_gamma_inverse
    physical_strength: additive_uniform_error_O_lambda_inverse_squared
    supplies_E1: false
    supplies_E2: false
    reason: >-
      On y >= lambda/2, a fixed multiple of lambda^-2 cannot be bounded by
      C*exp(-y^2/4) with C independent of lambda.  The desired weighted or
      higher-order conclusion is strictly stronger than the verified theorem.
  CCM_LEMMA_7_2_AS_VERIFIED:
    statement_strength: same_additive_uniform_lambda_inverse_squared_rate
    supplies_E1: false
    supplies_E2: false
  SOURCE_PROMOTION_BY_THIS_VERDICT: false
  C10_GUARD: additive_global_error_is_not_a_weighted_outer_envelope
  C04_GUARD: raw_mode_is_not_the_anchored_mode_consumed_by_the_project

SELECTED_PROOF_REPRESENTATION:
  code: R1_FINITE_HIGHER_ORDER_OUTER_ASYMPTOTIC
  public_output: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  plan:
    - derive_the_exact_rate_map_from_an_outer_half_C0_defect_rate_to_the_top_budget_ratio
    - determine_the_minimal_required_polynomial_order_before_reading_the_source
    - inspect_the_full_Satz9_construction_and_section_2_333_for_a_uniform_normalized_fixed_mode_expansion_beyond_first_order
    - accept_only_an_exact_stated_or_proved_remainder_with_source_page_and_normalization
    - use_polynomial_times_Gaussian_correction_terms_privately
    - prove_the_direct_top_contract_without_exporting_E1_or_E2
  safe_candidate_rate_for_preflight: outer_half_defect_O_lambda_inverse_six
  safe_candidate_rate_is_a_theorem_now: false
  kill_power: 9/10
  cost: 3/10

SOURCE_DISCRIMINATOR:
  name: SATZ9_FIXED_MODE_HIGHER_ORDER_OUTER_RATE
  pass: >-
    A source-locked fixed-mode expansion for n=0 and n=4, in the exact project
    normalization, has a uniform remainder of sufficient order to make the
    direct top-budget ratio tend to zero; every correction term is explicitly
    controlled on y in [lambda/2,lambda].
  fail: >-
    The available source gives only the first additive O(lambda^-2) remainder,
    or higher-order coefficients without a proved uniform remainder.
  zero_consistent: INCONCLUSIVE

CANDIDATE_REREPRESENTATIONS:
  R2_OUTER_FORBIDDEN_REGION_AGMON:
    description: >-
      Use the exact selected physical ODE, the F72.3 eigenvalue scale, L2
      normalization, and a turning-point/Agmon weight to prove outer-half decay
      directly; then feed the exact zero-flux equation into the top functional.
    kill_power: 10/10
    cost: 6/10
  R3_COEFFICIENT_ALTERNATING_EDGE_ROW:
    description: >-
      Control the exact alternating endpoint derivative rows from the committed
      three-term recurrence and tail contraction, retaining cancellation.
    kill_power: 8/10
    cost: 8/10

CLOSES:
  - STURM_WEIGHTED_CONSUMER_3A_3B_GATE_ADMISSION
  - RATE_AWARE_FIRST_ORDER_RECEIVER_GATE_ADMISSION
  - EDGE_TOP_SUPPLIER_SHAPE_FORK
  - CURRENT_SATZ9_CCM_AS_OUTER_GAUSSIAN_SUPPLIER
OPENS: []
CARRIES_OPEN:
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_6_MODE_AND_CHI_RATE_INPUTS

NEXT_LOAD_BEARING_GAP: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
NEXT_DECISIVE_TEST: SATZ9_FIXED_MODE_HIGHER_ORDER_OUTER_RATE

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```

## ROUTE MAP

### 1. Kernel-green work is admitted at its exact boundary

The eight public theorems in `G6N1SturmWeightedConsumerNonTopRate.lean` are
admitted at the reported kernel boundary.  Node 3A closes the literal interior
region with the absolute companion constant

\[
\frac12\log\frac43,
\]

and node 3B closes every non-top contribution at the honest
\(O(\sqrt{\log(m+1)})\) rate.  The top lattice point remains excluded by the
exact filter `(n+1)u <= lambda`; no derivative sup-norm, second derivative, or
uniform edge-band claim entered.

The rate-aware receiver is also admitted at the reported boundary.  Its exact
hypothesis is not bare bandwidth cofinality but

\[
C_k^2\,\operatorname{physicalFourierBandwidth}_k^{-1}\longrightarrow0.
\]

Thus a growing coefficient budget is legal only when its growth is paid by the
same selected schedule.

### 2. The numerical probe changes the representation, not the theorem status

The probe is strong evidence that the top point lives in a forbidden region and
that a Gaussian-type mechanism is present.  It does not establish the law

\[
T_k\sim e^{-\pi\lambda_k^2/4}.
\]

Only two points occur before the floating-point floor.  ODE residuals and the
F72.6 control checks validate the instrument as a diagnostic; they do not
occupy the cofinal quantifier.

The prior prediction `P_WC_TOP_1` is therefore not confirmed.  It claimed that
the exact flux equation plus the already committed uniform `C0` rate would be
sufficient.  The preflight itself shows that this input combination gives only
a polynomially growing bound.  The observed exponential top decay is a new
fact candidate requiring a new source mechanism; changing the mechanism after
seeing the probe would be retroactive repair.

### 3. Why neither E1 nor E2 is promoted

The current Satz-9/CCM input has the form

\[
\sup_{|y|\le\lambda_k}
\left|\text{anchored mode}_k(y)-W(y)\right|
\le C\lambda_k^{-2}.
\]

This additive estimate is compatible with Gaussian outer decay, but it does not
prove it.  On `y >= lambda/2`, the proposed envelope is exponentially small,
while `lambda^-2` is only polynomially small.  Treating the former as a
corollary of the latter would instantiate C10: a bound for one functional and
weight would be relabeled as a bound for another.

Raw E2 also drops a load-bearing normalization.  The project consumes the
center-anchored/scaled modes.  A theorem about an unscaled `S_phys` cannot be
inserted unless the exact scale is included or independently bounded.  This is
C04.

If a source supplies a weighted theorem, the repaired anchored E2 is the clean
private interface.  It is source-local; explicit Gaussian bounds for the two
cylinder targets then give E1 and the outer flux-source envelope.  But neither
private interface should become a new public route input: the downstream route
already has the exact minimal top-budget contract.

### 4. Selected move: finite higher-order outer asymptotic

The consumer does not require exponential decay.  It requires only

\[
T_k^2\,\operatorname{physicalFourierBandwidth}_k^{-1}\to0.
\]

Therefore the cheapest source test is not to demand a new weighted-Gaussian
theorem.  First derive the exact polynomial rate needed by the existing flux
ledger.  Then inspect the full fixed-mode asymptotic construction behind Satz 9
for a sufficiently high finite expansion with a proved uniform remainder.

On the outer half-window, every explicit parabolic-cylinder correction is a
fixed polynomial times a Gaussian and is therefore harmless.  A sufficiently
high uniform remainder can pay the consumer even if it is only polynomially
small.  A sixth-order physical candidate is deliberately conservative; it is
not declared proved until the source and the exact flux rate map are checked.

If the source has only the already verified first-order statement, stop.  Do
not infer a hidden higher-order theorem from the existence of a long eigenvalue
expansion.  The next representation is the exact ODE/Agmon barrier, not another
numerical ladder.

## STRONGEST ATTACK

The strongest attack on the preflight is simple: two non-floor numerical values
cannot identify a Gaussian asymptotic law.  The recurrence probe may be
accurate, and the actual top contribution may indeed be exponentially small,
but the route still lacks a cofinal upper envelope on the literal anchored
modes.  The theorem must come from an exact weighted/higher-order source or from
the selected ODE itself.

The strongest attack on E1/E2 is the scale mismatch.  Satz 9 and CCM Lemma 7.2
as currently source-locked prove an additive `O(lambda^-2)` approximation.
That estimate cannot be exponentiated by prose.  Failure of that sufficient
source does not show that the Gaussian envelope is false; it shows only that it
is not presently sourced.

## CODEX / LINUX DIRECTIVE

```text
TASK_ID: GOAL058_EDGE_TOP_DIRECT_OUTER_ASYMPTOTIC_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY_BEFORE_LEAN

OBJECTIVE:
  Close or kill the finite-higher-order-asymptotic proof representation for
  W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE.

READ_FIRST:
  docs/routeB_bus/LINUX_EDGE_TOP_PREFLIGHT_GOAL058_GAUSSIAN_DEATH_2026-08-26.md
  docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md
  docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_I_MEIXNER_SCHAEFKE_F72_1_PARAMETER_CHAIN_2026-08-20.md
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmDefectTruncatedEnergy.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmWeightedConsumerNonTopRate.lean

PHASE_0_RATE_MAP:
  Derive on paper the exact implication

    outer-half C0 defect rate O(lambda^-p)
      -> top_budget^2 / physicalFourierBandwidth -> 0.

  Return the minimal sufficient p and one conservative integer p_safe.
  Do not assume p_safe = 6 merely because this verdict names it as a candidate.

PHASE_1_SOURCE_AUDIT:
  Inspect the exact fixed-mode construction behind Meixner-Schaefke Satz 9,
  including section 2.333 if needed.

  Accept a source only if it provides:
    - fixed modes n=0 and n=4;
    - the exact normalized representative used by Q3;
    - explicit correction functions;
    - a proved uniform remainder of order at least p_safe after unit transport;
    - an exact page/theorem/proof pointer.

  The long eigenvalue expansion alone is not evidence for a mode remainder.
  CCM Lemma 7.2's first-order O(lambda^-2) statement is insufficient.

OUTPUT_EXACTLY_ONE_REPORT:
  docs/routeB_bus/LINUX_EDGE_TOP_SOURCE_PREFLIGHT_GOAL058_2026-08-26.md

REPORT_STATUS:
  SOURCE_HIGH_ORDER_PASS
  | SOURCE_ONLY_FIRST_ORDER_FAIL
  | SOURCE_PROVENANCE_AMBIGUOUS

IF_PASS:
  Return the exact theorem statement and rate ledger for one subsequent Lean
  transaction that proves the direct top-budget contract.  Keep E1/E2 private.

IF_FAIL:
  Select R2_OUTER_FORBIDDEN_REGION_AGMON and return its exact paper theorem
  target.  Do not write Lean and do not run another numerical probe.

FORBIDDEN:
  - fit an exponential law from m=16 and m=32
  - promote diagnostic float values to a cofinal theorem
  - infer a weighted Gaussian envelope from an additive O(lambda^-2) bound
  - state E2 on an unanchored source mode
  - create a conditional Lean bridge before the analytic supplier is sourced
  - reopen nodes 3A/3B or the rate-aware receiver
```

## META CLOSEOUT

**What became smaller?**  The top fork is no longer E1 versus E2 versus an
expensive coefficient cancellation.  The public gap remains one exact top
functional.  The first proof representation is a bounded source question:
does a sufficiently high fixed-mode uniform expansion exist with a proved
remainder?

**What was killed?**  The claim that the current Satz-9/CCM first-order theorem
already supplies an outer Gaussian envelope; raw unanchored E2; confirmation of
`P_WC_TOP_1` by changing its mechanism after the probe.

**What must not be tried again?**  More float points after the floor, a
pointwise derivative sup-norm, or a public outer-envelope assumption stronger
than the exact consumer.

**Current smallest named gap:**
`W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE`.

**Next cheapest decisive test:**
`SATZ9_FIXED_MODE_HIGHER_ORDER_OUTER_RATE`.

**Memory entry:**
```yaml
iteration:
  target: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  status: OPEN
  failed_strategy: uniform_C0_plus_flux_as_sufficient_top_control
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SATZ9_FIXED_MODE_HIGHER_ORDER_OUTER_RATE
  invariant_learned: preserve_exact_anchor_and_keep_the_direct_top_functional_as_public_consumer
  forbidden_future_move: infer_weighted_outer_decay_from_unweighted_lambda_inverse_squared_error
  next_decisive_test: source_locked_higher_order_fixed_mode_remainder_audit
```
