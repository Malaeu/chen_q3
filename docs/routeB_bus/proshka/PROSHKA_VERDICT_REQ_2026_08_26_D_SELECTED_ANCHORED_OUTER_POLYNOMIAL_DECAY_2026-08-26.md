# STATUS: CONDITIONAL — RATIFY THE ANCHORED OUTER POLYNOMIAL DECAY TARGET WITH A REPAIRED CACCIoppoli/MONOTONICITY PROOF; AUTHORIZE ONE LEAN TRANSACTION

```yaml
PRIMARY: RUN_SELECTED_FERRERS_ANCHORED_OUTER_POLYNOMIAL_DECAY
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-D
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_DIRECT_FOLLOWUP_OF_REQ_2026_08_26_C
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  HEAD: 9cfb5e3cf9cedf89fd15157c7565e412b9c33378
  SOURCE_PREFLIGHT_PATH: docs/routeB_bus/LINUX_EDGE_TOP_SOURCE_PREFLIGHT_GOAL058_2026-08-26.md
  SOURCE_PREFLIGHT_BLOB: ba72976b3f265adf3cca57d30a2134cf0f23165e
  PRIOR_VERDICT: 95e9584fad6fcad412f82be693a9c0782346a2eb
  NODE_3A_3B_COMMIT: 1a229b3aa3d46d3e386980295c790431fa1ed7ff
  RATE_RECEIVER_COMMIT: a39c28e58b72f0b51d00e45e4f912747e571fe75

KERNEL_ADMISSION_CARRIED:
  STURM_WEIGHTED_CONSUMER_3A_3B: RATIFIED_AT_REPORTED_GATE
  RATE_AWARE_FIRST_ORDER_RECEIVER: RATIFIED_AT_REPORTED_GATE
  JUDGE_RERAN_LAKE_BUILD: false

SOURCE_DISCRIMINATOR:
  SATZ9_FIXED_MODE_HIGHER_ORDER_OUTER_RATE:
    outcome: FAIL_AT_CURRENT_SOURCE_SCOPE
    reason: >-
      Rendered pages 243–247 state only the first uniform mode approximation;
      the higher-order construction is a method description with recursions
      delegated to external Meixner/Sips references and no stated uniform
      remainder of sufficient order.
    MEIXNER_SIPS_ACQUISITION: NOT_SELECTED_FOR_CRITICAL_PATH

RATE_MAP:
  assumption: sup_outer_half_norm_defect_le_A_times_lambda_pow_neg_p
  top_budget: T_k_le_8_pi_sq_A_lambda_pow_4_5_minus_p
  bandwidth_lower_bound: physical_bandwidth_ge_pi_lambda
  ratio: T_k_sq_div_bandwidth_is_O_lambda_pow_8_minus_2p
  exact_threshold: p_greater_than_4
  minimal_integer_p: 5
  selected_p: 6
  selected_ratio_margin: O_lambda_pow_neg_4
  status: PAPER_PASS

TARGET:
  name: SELECTED_ANCHORED_OUTER_POLYNOMIAL_DECAY
  statement: >-
    There is C >= 0 such that eventually, for every y in
    [lambda_k/2,lambda_k], both literal anchored selected modes satisfy
    norm(centerAnchorScalarZero(k) * h0_k(y)) <= C/lambda_k^6 and
    norm(centerAnchorScalarFour(k) * h4_k(y)) <= C/lambda_k^6.
  object: LITERAL_SELECTED_CENTER_ANCHORED_MODES
  scope: COFINAL_FAMILY
  verifier: PAPER_CONDITIONAL
  paper_status: PROVED_BY_REPAIRED_ROUTE_BELOW
  lean_status: AUTHORIZED_NOT_WRITTEN

INPUT_CONTRACT:
  - exact_physical_prolate_ODE_and_zero_flux_for_each_selected_mode
  - eventual_differential_eigenvalue_upper_bound_theta_j_le_Ctheta_lambda_sq
  - existing_center_anchored_direct_cylinder_rate_hmode
  - real_valuedness_and_nonzero_center_of_the_literal_selected_modes
  - exact_selected_schedule_lambda_k_sq_eq_k_plus_2
  anchor_scalar_upper_bound_as_new_input: NOT_REQUIRED
  reason: >-
    The existing anchored hmode estimate plus the explicit cylinder L2 bounds
    gives a uniform L2 bound for the anchored modes directly.

ORIGINAL_PREFLIGHT_REPAIRS:
  ENDPOINT_UNIT_CELL_FTC:
    decision: REJECT_AS_STATED
    reason: >-
      The weighted energy has coefficient lambda^2-y^2; direct Cauchy–Schwarz
      to the endpoint sees integral 1/(lambda^2-y^2), which diverges.
    replacement: OUTER_ZERO_FREE_SIGN_AND_MONOTONICITY
  THREE_PASSES_REACH_LAMBDA_NEG_14:
    decision: SUPERSEDED
    replacement: >-
      Three scaled-shell Caccioppoli steps give outer mass O(lambda^-12);
      monotonicity and a left interval of length lambda/16 give pointwise
      O(lambda^-13/2), then weaken to lambda^-6.
  SOURCE_SCALE_INVERSE_IMPLIES_ANCHOR_UPPER:
    decision: REJECT
    reason: >-
      selectedFerrersSourceScale_inverse_bounded controls one composite source
      scale; it does not separately upper-bound both center-anchor scalars.

REPAIRED_PAPER_PROOF:
  potential_region: y_in_lambda_over_4_to_lambda
  potential_floor: q_j_y_ge_cq_lambda_pow_4_eventually
  caccioppoli_shells:
    - [1/4, 5/16]
    - [5/16, 3/8]
    - [3/8, 7/16]
  cutoff_slope: O_lambda_inverse
  mass_gain_per_shell: O_lambda_pow_neg_4
  after_three_shells: outer_mass_on_7lambda_over_16_to_lambda_is_O_lambda_pow_neg_12
  zero_free_argument: >-
    A zero in the positive-potential outer region, tested against the mode up
    to the zero-flux endpoint, forces both derivative and potential energies
    to vanish; source nontriviality excludes this.
  monotonicity_argument: >-
    On the zero-free outer component the mode has fixed sign, and the exact
    flux identity makes its absolute value nonincreasing toward lambda.
  pointwise_recovery: >-
    The interval [7lambda/16,lambda/2] has length lambda/16 and every value
    there dominates the value at lambda/2. Hence sup on [lambda/2,lambda]^2
    is at most 16/lambda times the O(lambda^-12) mass.
  derived_rate: O_lambda_pow_neg_13_over_2
  exported_rate: O_lambda_pow_neg_6

LEAN_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_ANCHORED_OUTER_POLYNOMIAL_DECAY
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_OUTER_POLYNOMIAL_DECAY_2026-08-26.md
  PUBLIC_THEOREM: selectedFerrersAnchoredOuterPolynomialDecay_of_modeAndThetaRates
  REQUIRED_CONCLUSION: >-
    A single eventual constant C for both selected anchored modes, uniformly
    on Set.Icc (lambda_k/2) lambda_k, with bound C/lambda_k^6.
  IMPLEMENTATION_ORDER:
    - derive_uniform_anchored_L2_bound_from_existing_hmode
    - prove_outer_potential_floor
    - prove_one_scaled_shell_Caccioppoli_step
    - iterate_the_three_precommitted_rational_shells
    - prove_outer_zero_free_and_abs_antitone_from_ODE_and_zero_flux
    - derive_lambda_pow_neg_13_over_2_then_weaken_to_lambda_pow_neg_6
  PRIVATE_HELPERS_PREFERRED: true
  DO_NOT_EXPORT_NEW_ANALYTIC_SUPPLIERS: true
  FORBIDDEN:
    - derivative_sup_norm
    - delta_second_derivative
    - numerical_probe_as_proof
    - raw_unanchored_mode_substitution
    - source_scale_inverse_as_individual_anchor_bound
    - endpoint_FTC_through_the_degenerate_weight
    - new_Meixner_or_Sips_axiom
  EXPECTED_AXIOM_PROFILE:
    - propext
    - Classical.choice
    - Quot.sound
  VERIFICATION_HANDOFF:
    WORKDIR_q3_lean_aristotle:
      - lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean
      - lake build Q3.Proofs.RouteB.G6N1SelectedFerrersOuterPolynomialDecay
    WORKDIR_repo_root:
      - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean
  SUCCESS_CODE: SELECTED_FERRERS_ANCHORED_OUTER_POLYNOMIAL_DECAY_LEAN
  FAILURE_CODE: SELECTED_FERRERS_OUTER_CACCIOPPOLI_OR_MONOTONICITY_KERNEL_GAP

CLOSES:
  - SATZ9_FIXED_MODE_HIGHER_ORDER_OUTER_RATE_SOURCE_FORK
  - SELECTED_ANCHORED_OUTER_POLYNOMIAL_DECAY_PAPER_TARGET
OPENS: []
CARRIES_OPEN:
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_6_MODE_AND_CHI_RATE_INPUTS

NEXT_LOAD_BEARING_GAP: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: EDGE_TOP_FLUX_CONSUMER_ASSEMBLY

PREDICTION_FATES:
  P_SATZ9_HIGH_ORDER_1:
    prior_probability: 0.38
    fate: REFUTED_AT_AUDITED_SOURCE_SCOPE
  P_OUTER_TOP_2:
    prior_probability: 0.78
    fate: CONFIRMED_AT_PAPER_THEOREM_SHAPE_NOT_YET_AT_KERNEL
  P_LEAN_OUTER_1:
    probability: 0.76
    prediction: >-
      The repaired three-shell Caccioppoli plus monotonicity theorem compiles
      without a new analytic hypothesis.
  LIKELIEST_FAILURE:
    class: DEGENERATE_ENDPOINT_INTEGRATION_OR_REAL_MODE_COERCION_API
    response: keep_the_statement_and_reduce_to_one_exact_helper_not_weaken_the_rate

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```

## ROUTE MAP

The source preflight is accepted at its exact boundary.  The audited pages do
not state a higher-order uniform fixed-mode remainder.  Therefore the
finite-higher-order source representation is closed at the current source
scope.  The optional Meixner/Sips acquisition is not required before trying the
source-free ODE route.

The direct target is correct, but the proof route in the preflight needed three
repairs.

First, the bound on the inverse composite Lemma-7.3 source scale is not a bound
on each center-anchor scalar.  The target should not acquire that new input.
The already available anchored cylinder approximation gives instead

\[
 \|\phi_{j,k}\|_{L^2[-\lambda_k,\lambda_k]}
 \le \|W_j\|_{L^2(\mathbb R)}
      +\sqrt{2\lambda_k}\,C_j\lambda_k^{-2},
\]

so both anchored modes are uniformly bounded in \(L^2\).  This uses the exact
anchored objects consumed downstream.

Second, pointwise recovery by weighted FTC all the way to \(y=\lambda\) is not
legal: the companion integral of \((\lambda^2-y^2)^{-1}\) diverges at the
degenerate endpoint.  The repair is stronger and cheaper.  In the outer
positive-potential region a zero would make the integrated mode energy on the
interval from that zero to the zero-flux endpoint vanish.  Hence the mode has a
fixed sign there.  The flux equation then makes its absolute value
nonincreasing toward the endpoint.

Third, use three fixed rational shells.  Put

\[
 p(y)=\lambda^2-y^2,
 \qquad
 q(y)=4\pi^2\lambda^2y^2-\theta.
\]

The differential-eigenvalue rate gives, eventually,

\[
 q(y)\ge c_q\lambda^4
 \qquad(y\ge\lambda/4).
\]

For a cutoff \(\eta\) changing across a shell of width \(\lambda/16\), testing

\[
 -(p\phi')'+q\phi=0
\]

against \(\eta^2\phi\) gives

\[
 \frac12\int \eta^2p|\phi'|^2
 +\int \eta^2q|\phi|^2
 \le 2\int p|\eta'|^2|\phi|^2.
\]

Since \(p\le\lambda^2\) and \(|\eta'|\le16/\lambda\), every shell gains
\(O(\lambda^{-4})\) in outer \(L^2\)-mass.  The precommitted shells

\[
 \frac14\to\frac5{16}\to\frac38\to\frac7{16}
\]

give

\[
 \int_{7\lambda/16}^{\lambda}|\phi|^2
 \le C\lambda^{-12}.
\]

Absolute-value monotonicity now gives

\[
 \frac{\lambda}{16}|\phi(\lambda/2)|^2
 \le
 \int_{7\lambda/16}^{\lambda/2}|\phi|^2,
\]

and therefore

\[
 \sup_{\lambda/2\le y\le\lambda}|\phi(y)|
 \le C\lambda^{-13/2}
 \le C\lambda^{-6}.
\]

Thus the requested \(p=6\) theorem is a valid consumer-strength weakening of a
stronger polynomial estimate.  It uses no derivative sup-norm and no second
derivative supplier.

## FINAL PROPOSAL

Run one Lean transaction for the literal two anchored selected modes.  Do not
formalize a general Agmon library and do not acquire the delegated Meixner/Sips
sources first.  The public theorem should expose only the selected cofinal
supplier; Caccioppoli, zero-free outer-region, and monotonicity lemmas should
remain private unless the repository catalog already has exact public slots.

After semantic admission of this theorem, assemble the already paper-checked
flux consumer to close
`W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE`.

## STRONGEST ATTACK

The strongest objection to the returned preflight was the endpoint step.  The
weight \(\lambda^2-y^2\) vanishes at \(y=\lambda\), so weighted derivative
energy does not by itself control the endpoint trace.  Any proof that silently
uses

\[
 \int^{\lambda}\frac{dy}{\lambda^2-y^2}<\infty
\]

is false.  The repaired proof never takes this step.  It obtains a fixed-sign
outer solution from the positive potential and zero-flux boundary, then uses
monotonicity to transfer an interior mass estimate to the entire outer half.

The second objection is normalization.  `selectedFerrersSourceScale_inverse_bounded`
controls a composite source scale, not the two individual anchor multipliers.
The repaired target instead derives the exact anchored \(L^2\) bound from the
already committed anchored cylinder approximation.

## CODEX / LINUX DIRECTIVE

```text
TASK_ID: GOAL058_SELECTED_FERRERS_ANCHORED_OUTER_POLYNOMIAL_DECAY

MODE:
  ONE_GOAL_ONE_COMMIT

OBJECTIVE:
  Prove the single cofinal selected-family theorem
  selectedFerrersAnchoredOuterPolynomialDecay_of_modeAndThetaRates.

READ_FIRST:
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  docs/routeB_bus/LINUX_EDGE_TOP_SOURCE_PREFLIGHT_GOAL058_2026-08-26.md
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CenterAnchorScalarLock.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersDirectCylinderRate.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmDefectTruncatedEnergy.lean

CREATE:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean
  docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_OUTER_POLYNOMIAL_DECAY_2026-08-26.md

DO_NOT_EDIT:
  existing Lean files
  Q3.Main
  route state
  prior verdicts or source records

THEOREM SHAPE:
  Consume the existing anchored mode rate and the existing differential
  eigenvalue-rate input.  Produce one common eventual C for both literal
  anchored modes on [lambda/2,lambda], bounded by C/lambda^6.

MANDATORY PROOF ROUTE:
  1. Derive a uniform anchored L2 bound from hmode and explicit cylinder L2.
  2. Establish q(y) >= c*lambda^4 on y >= lambda/4.
  3. Prove one scaled-shell Caccioppoli lemma.
  4. Iterate exactly the three precommitted shells 1/4,5/16,3/8,7/16.
  5. Prove outer zero-freeness and absolute-value monotonicity from the exact
     ODE, real-valuedness, nonzero center, and zero flux.
  6. Obtain lambda^-13/2 and weaken to lambda^-6.

FORBIDDEN:
  endpoint weighted-FTC
  derivative sup hypothesis
  delta'' hypothesis
  individual anchor bound inferred from composite source scale
  numerical evidence
  paper theorem inserted as axiom
  theorem weakening

GATE:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersOuterPolynomialDecay

  WORKDIR repo root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean

EXPECTED AXIOMS FOR EVERY PUBLIC THEOREM:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  SELECTED_FERRERS_ANCHORED_OUTER_POLYNOMIAL_DECAY_LEAN

FAILURE:
  SELECTED_FERRERS_OUTER_CACCIOPPOLI_OR_MONOTONICITY_KERNEL_GAP

If blocked, return the exact smallest missing helper and do not add a new
analytic hypothesis.
```

## META CLOSEOUT

**What became smaller?**  The edge-top wall is reduced to one literal
selected-family outer-decay theorem with a complete paper proof and no new
analytic supplier.

**What was killed?**  The currently sourced higher-order Satz-9 route; the
endpoint weighted-FTC step; the inference from composite source-scale control
to individual anchor bounds.

**What must not be tried again?**  Do not treat a method paragraph as a uniform
remainder theorem.  Do not cross the degenerate endpoint with the reciprocal
energy weight.

**Current smallest named gap?**
`SELECTED_ANCHORED_OUTER_POLYNOMIAL_DECAY_LEAN`.

**Next cheapest decisive test?**  Compile the one selected-family file against
the exact existing ODE/flux APIs.

**Prediction fate?**  The higher-order-source prediction is refuted at the
audited source scope.  The forbidden-region prediction is confirmed at paper
theorem shape and remains untested at the kernel.

**Memory entry:**

```yaml
iteration: GOAL058_EDGE_TOP_D
target: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
status: PROGRESS
failed_strategy: FINITE_HIGHER_ORDER_SATZ9_OUTER_ASYMPTOTIC
cognitive_operator_used: MINIMAL_LEMMA
new_gap_name: SELECTED_ANCHORED_OUTER_POLYNOMIAL_DECAY_LEAN
invariant_learned: degenerate_endpoint_requires_monotonicity_or_trace_theorem_not_weighted_FTC
forbidden_future_move: infer_individual_anchor_bounds_from_composite_source_scale
next_decisive_test: compile_selected_outer_polynomial_decay
```
