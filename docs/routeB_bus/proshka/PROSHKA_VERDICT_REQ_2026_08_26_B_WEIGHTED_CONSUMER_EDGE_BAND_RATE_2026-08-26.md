# STATUS: CONDITIONAL — AUTHORIZE THE INTERIOR/NON-TOP LEAN NODE; SELECT RATE-AWARE B1; KILL THE ENERGY-ONLY UNIFORM BAND CLAIM; KEEP THE TOP FUNCTIONAL WITH A WEAKER BANDWIDTH-NEGLIGIBLE CONTRACT
```yaml
PRIMARY: RUN_STURM_WEIGHTED_CONSUMER_NON_TOP_RATE
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-B
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_DIRECT_FOLLOWUP_OF_REQ_2026_08_26_A
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  HEAD: 1dec336acce7d0853c38b371dacf2f93cdfc5128
  PREFLIGHT_PATH: docs/routeB_bus/LINUX_WEIGHTED_CONSUMER_PREFLIGHT_GOAL058_COMPANION_LEDGER_2026-08-26.md
  PREFLIGHT_BLOB: 35b54b48324b0516d0a4674a66a4b289d0a594d8
  STURM_PREFLIGHT_COMMIT: 4c62caa5abd416cd30d1de87aece0eaf95e2e339
  STURM_NODE1_COMMIT: a3c84e453192507b7e96f6c5f670b761e1dea1d5
  STURM_NODE1_BLOB: 0ce87ceab417e5eea9b376917168187057f1fd6e
  CURRENT_BOUNDED_D_THEOREM: selectedFerrersAbelFourierDecayBudget_bounded_of_modeAndChiRates
  CURRENT_FIRST_ORDER_RECEIVER: selectedProjectionTailDecay_of_firstOrderCoefficientBudgetAndBandwidth
  CURRENT_SELECTED_SCHEDULE: selectedFerrersPreAnchorIndex_k_eq_m_N_k_plus_2

PREFLIGHT_ADMISSION:
  EXACT_PER_N_CHANGE_OF_VARIABLES: PAPER_VERIFIED
  EXACT_COMPANION_FORMULA: PAPER_VERIFIED
  INTERIOR_CONSTANT_HALF_LOG_FOUR_THIRDS: PAPER_VERIFIED
  NON_TOP_PURE_ENERGY_RATE: O_CE_SQRT_LOG_LAMBDA
  OLD_SECTION6_RATE_O_SQRT_LOG_OVER_LAMBDA: SUPERSEDED_AT_ENERGY_ONLY_SCOPE
  DISCRIMINATOR: PARTIAL_PASS

QUESTION_A_INTERIOR:
  DECISION: AUTHORIZE_WITH_NODE_SPLIT
  NODE3A:
    name: STURM_WEIGHTED_CONSUMER_INTERIOR
    conclusion: interior_budget_le_2_lambda_sqrt_half_log_four_thirds_sqrt_E0
    corollary_under_E0_rate: interior_budget_le_0_76_CE
    status: LEAN_AUTHORIZED
  NODE3B:
    name: STURM_WEIGHTED_CONSUMER_NON_TOP_SQRT_LOG_RATE
    conclusion: non_top_budget_le_2_lambda_sqrt_half_log_m_plus_one_sqrt_E0
    corollary_under_E0_rate: non_top_budget_le_sqrt_2_CE_sqrt_log_m_plus_one
    status: LEAN_AUTHORIZED_SAME_TRANSACTION
  NODE3_FULL_CLOSED: false
  reason: top_lattice_functional_remains_separate

QUESTION_B_EDGE_BAND:
  CHOICE: B1_RATE_AWARE
  DECISION: ACCEPT_RELAXED_RATE_AS_NEW_PARALLEL_CONSUMER_BRANCH
  OLD_UNIFORM_D_THEOREMS_MUTATED: false
  OLD_UNIFORM_D_BRANCH_RETAINED: true
  NEW_DERIVATIVE_RATE_SHAPE: derivative_budget_non_top_le_D_sqrt_L
  NEW_GENERIC_RECEIVER_REQUIRED:
    name: selectedProjectionTailDecay_of_firstOrderCoefficientRate
    coefficient_shape: coeff_sq_le_Ck_sq_times_L_over_n_sq
    exact_rate_consumer: Ck_sq_div_physicalBandwidth_tends_to_zero
  GENERIC_SelectedPhysicalBandwidthCofinal_ALONE_SUFFICIENT: false
  SELECTED_FERRERS_SCHEDULE_SUFFICIENT: true
  selected_schedule_payment:
    L: log_k_plus_2
    physical_bandwidth_lower: pi_sqrt_k_plus_2
    conclusion: L_div_physical_bandwidth_tends_to_zero
  B2_NEW_UNIFORM_BAND_SUPPLIER:
    decision: NOT_SELECTED
    reason: unnecessary_new_analytic_supplier_after_rate_aware_consumer
    status: HOLD_AS_OPTIONAL_STRENGTHENING_ONLY
  B3_STRONGER_ENERGY_ONLY_PAIRING:
    decision: REJECT_AT_CURRENT_ABSTRACT_SCOPE
    reason: explicit_edge_band_counterprofile_has_fixed_weighted_energy_and_sqrt_log_budget
    rescue_policy: any future uniform theorem must consume additional_C0_ODE_or_cell_regularization_data

QUESTION_C_TOP:
  FUNCTIONAL_OBJECT: UNCHANGED_AND_ISOLATED
  OLD_REQUIRED_STRENGTH_BOUNDED: NO_LONGER_MINIMAL
  NEW_MINIMAL_CONTRACT:
    name: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
    statement: top_budget_k_sq_div_physicalFourierBandwidth_k_tends_to_zero
  OLD_BOUNDED_CONTRACT_IMPLIES_NEW: true
  CARRIED_OPEN: true

ENERGY_ONLY_COUNTERPROFILE:
  profile: smooth_cutoff_of_a_lambda_sqrt_y_div_lambda_sq_minus_y_sq_on_y_in_lambda_over_2_to_lambda_minus_4
  normalization: a_lambda_asymp_CE_div_lambda_sqrt_log_lambda
  weighted_energy: O_CE_sq_div_lambda_sq
  non_top_band_budget_lower: Omega_CE_sqrt_log_lambda
  scope_guard: does_not_claim_the_profile_satisfies_the_committed_C0_defect_rate_or_exact_defect_ODE
  kill: energy_only_uniform_band_bound

RATE_LEDGER:
  non_top_budget: O_sqrt_L
  mass_and_jump_budget: O_1
  top_budget: T_k
  Fourier_decay_constant: O_1_plus_sqrt_L_plus_T_k
  projection_tail_squared: O_of_Fourier_decay_constant_sq_div_bandwidth
  sufficient_selected_schedule_conditions:
    - L_div_bandwidth_tends_to_zero
    - T_k_sq_div_bandwidth_tends_to_zero

CLOSES:
  - WEIGHTED_CONSUMER_REPRESENTATION_FORK
  - SECTION6_SLIVER_FREE_RATE_AS_ENERGY_ONLY_CLAIM
  - EDGE_BAND_NEW_UNIFORM_SUPPLIER_AS_REQUIRED_ROUTE_INPUT
OPENS: []
CARRIES_OPEN:
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_6_MODE_AND_CHI_RATE_INPUTS

NEXT_LOAD_BEARING_GAP: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
DISCRIMINATOR: TOP_BUDGET_SQUARED_OVER_PHYSICAL_BANDWIDTH

PREDICTIONS:
  P_LINUX_WC_1:
    prior_probability: 0.80
    fate: CONFIRMED_AT_ENERGY_ONLY_BLACK_BOX_SCOPE
  P_EDGE_CONSUMER_1:
    fate: PARTIALLY_CONFIRMED_EDGE_OBJECT_EXPANDED_FROM_POINT_TO_BAND_TOP_REMAINS_UNTESTED
  P_EDGE_SUP_1:
    fate: CONFIRMED_NO_SUP_RATE_IS_REQUIRED_OR_DERIVED
  P_WC_RATE_RECEIVER_1:
    probability: 0.93
    prediction: rate_aware_first_order_receiver_closes_by_reusing_the_existing_tsum_tail_and_the_selected_schedule_bandwidth_lower_bound
  P_WC_TOP_1:
    probability: 0.72
    prediction: exact_flux_ODE_and_C0_control_yield_bandwidth_negligible_top_budget_without_a_derivative_sup_norm

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C07_PROBABILITY_WEIGHTED_ESTIMATE
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

The exact companion computation is accepted.  For

\[
R_n=(n/\lambda,\lambda n/(n+1)]
\]

one has

\[
\int_{R_n}\frac{y}{\lambda^2-y^2}\,dy
=\frac12\log\!\left(
\frac{(\lambda^2-n^2/\lambda^2)(n+1)^2}
{\lambda^2(2n+1)}
\right).
\]

The interior cutoff \(y\le\lambda/2\) replaces this by the absolute constant
\(\frac12\log(4/3)\).  Thus the interior theorem is a valid standalone
consumer-strength result.  It closes a literal region of the comb and opens no
new supplier.  It is authorized as node 3A, but it must not be reported as the
whole node 3.

The same transaction should carry the honest non-top rate theorem.  The coarse
finite estimates

\[
\operatorname{companion}_n\le\frac12\log(m+1),\qquad
\sum_{n=1}^{m}n^{-1/2}\le2\sqrt m
\]

give

\[
B_{\mathrm{nonTop}}
\le2\lambda\sqrt{\tfrac12\log(m+1)}\sqrt{E_0}.
\]

Under \(E_0\le C_E^2/\lambda^2\), this is

\[
B_{\mathrm{nonTop}}
\le\sqrt2\,C_E\sqrt{\log(m+1)}.
\]

This is the correct output of the node-1 energy black box.  The old Section 6
claim \(O(\sqrt{\log\lambda/\lambda})\) is superseded at that scope.

### The energy-only uniform claim is false

For \(\lambda\) large, take a nonnegative smooth cutoff of

\[
g_\lambda(y)=a_\lambda\frac{\sqrt y}{\lambda^2-y^2}
\]

on \([\lambda/2,\lambda-4]\).  On this interval the set of non-top indices
contributing at a given \(y\) has an inverse-square-root sum bounded below by
\(c\lambda\).  Also

\[
I_\lambda:=\int_{\lambda/2}^{\lambda-4}
\frac{y}{\lambda^2-y^2}\,dy\asymp\log\lambda.
\]

Choosing \(a_\lambda=C_E/(\lambda\sqrt{I_\lambda})\) gives weighted energy
\(C_E^2/\lambda^2\), while the non-top budget is bounded below by
\(cC_E\sqrt{\log\lambda}\).  Smoothing the two cutoff endpoints only changes
absolute constants.  Therefore no pairing that consumes only the weighted
energy can prove a uniform band bound.  This kill is deliberately scoped: the
profile is not claimed to satisfy the committed \(C^0\) defect rate or the
exact defect ODE.  A future stronger theorem using those additional data would
be a different theorem, not a repair of the old energy-only calculation.

This is an instance of **C01**: the lost factor is carried by the physical edge
band, not by the total energy alone.

## FINAL PROPOSAL

Select **b1**, but do not weaken or edit the already kernel-green uniform-\(D\)
theorems.  Add a parallel rate-aware branch.

The existing first-order receiver assumes a fixed coefficient constant \(C\)
and uses only `SelectedPhysicalBandwidthCofinal`.  That generic cofinality is
not enough when the coefficient constant grows like \(\sqrt L\).  The correct
generic receiver is:

```text
selectedProjectionTailDecay_of_firstOrderCoefficientRate

INPUT:
  ||c_k(n)||^2 <= C_k^2 * L_k / n^2   on omitted modes
  C_k^2 / physicalFourierBandwidth_k -> 0

OUTPUT:
  SelectedProjectionTailDecay
```

The selected Ferrers schedule pays the extra logarithm.  It has
\(L_k=\log(k+2)\) and the committed arithmetic proof gives

\[
\operatorname{physicalFourierBandwidth}_k
\ge\pi\sqrt{k+2}.
\]

Hence

\[
\frac{L_k}{\operatorname{physicalFourierBandwidth}_k}\to0.
\]

So a non-top derivative budget of order \(\sqrt{L_k}\) still produces
projection-tail decay.  No new analytic edge-band supplier is required.

The signed Euler--Maclaurin identity remains useful, but only as an exact split:
its cell-mean part is paid by the \(C^0\) rate, while its cell-deviation term is
not silently declared small.  This is the **C13** discipline.

### Top-point repair

The top functional stays isolated.  Its old name ending in `BOUNDED` is now a
strong sufficient supplier, not the minimal consumer.  The rate-aware receiver
needs only

\[
\frac{T_k^2}
{\operatorname{physicalFourierBandwidth}_k}\to0,
\]

where \(T_k\) is the exact top-lattice contribution.  Rename the minimal open
contract to

```text
W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE.
```

Uniform boundedness implies this contract, but must not be demanded unless the
source naturally supplies it.

## STRONGEST ATTACK

The strongest attack on b1 is not the \(\sqrt{\log}\) loss.  It is a quantifier
mistake: `SelectedPhysicalBandwidthCofinal` by itself says only bandwidth tends
to infinity.  It does not imply

\[
L_k/\operatorname{bandwidth}_k\to0.
\]

Therefore the rate-aware theorem must either consume the exact ratio limit or
be specialized to the precommitted Ferrers schedule.  Reusing the old generic
receiver unchanged would be a semantic bug.

A second guard is that the energy-only counterprofile does not kill a theorem
which additionally consumes the \(C^0\) rate, the exact defect ODE, or a cell
regularity estimate.  Those are legitimate future strengthenings, but they are
not needed for the current projection-tail consumer.

## CODEX / LINUX DIRECTIVE

```text
TASK_ID: GOAL058_STURM_WEIGHTED_CONSUMER_NON_TOP_RATE

CREATE:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmWeightedConsumerNonTopRate.lean
  docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_STURM_WEIGHTED_CONSUMER_NON_TOP_RATE_2026-08-26.md

PUBLIC THEOREMS:
  sturm_weighted_consumer_interior_bound
  sturm_weighted_consumer_nonTop_sqrtLog_bound

MATHEMATICAL TARGETS:
  1. Interior:
       B_interior <=
         2 * lambda * sqrt((1/2) * log(4/3)) * sqrt(E0).

  2. All non-top contributions:
       B_nonTop <=
         2 * lambda * sqrt((1/2) * log(m+1)) * sqrt(E0),
     with lambda = sqrt(m).

  3. Rate corollaries under E0 <= CE^2/lambda^2.

PROOF ROUTE:
  - finite triangle inequality over n;
  - exact change of variables y = n*exp(x)/lambda;
  - Cauchy--Schwarz against (lambda^2-y^2)*||gd||^2;
  - exact antiderivative of y/(lambda^2-y^2);
  - interior cap by (1/2)*log(4/3);
  - non-top cap by (1/2)*log(m+1);
  - sum n^(-1/2) <= 2*sqrt(m).

EXCLUSIONS:
  - do not include the top point;
  - do not claim a uniform edge-band bound;
  - do not use an unweighted L2 derivative norm;
  - do not assume a derivative sup norm;
  - do not consume delta'';
  - do not edit the existing uniform-D theorems;
  - no sorry, admit, native_decide, fake axiom, or theorem weakening.

CLOSES:
  - WEIGHTED_CONSUMER_INTERIOR
  - WEIGHTED_CONSUMER_NON_TOP_SQRT_LOG_RATE
OPENS: []
CARRIES_OPEN:
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE

VERIFICATION_HANDOFF:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SturmWeightedConsumerNonTopRate.lean
    lake build Q3.Proofs.RouteB.G6N1SturmWeightedConsumerNonTopRate
  WORKDIR repo-root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SturmWeightedConsumerNonTopRate.lean

EXPECTED_AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  both public theorems compile unchanged;
  exact top exclusion is visible in the statement;
  source record and Lean source land in one commit.

FAILURE_CODE:
  GOAL058_WEIGHTED_CONSUMER_NON_TOP_RATE_LEAN_GAP
```

After this gate, the next theorem is the generic rate-aware first-order
projection-tail receiver.  Do not start it in the same transaction.

## META CLOSEOUT

**What became smaller?**  The edge-band wall is no longer an analytic supplier;
it is a proved \(\sqrt L\)-rate target.  The only remaining edge functional is
the exact top contribution.

**What was killed?**  The old energy-only sliver-free uniform rate and option b3
at the current abstraction.

**What must not be tried again?**  Re-running Cauchy--Schwarz with a different
order while consuming only the same weighted energy, or forcing the old
uniform-\(D\) receiver onto a growing coefficient constant.

**Current smallest named gap:**
`W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE`.

**Next cheapest decisive test:** formalize the non-top exact rate, then derive
the rate-aware receiver with the explicit ratio `C_k^2 / bandwidth_k`.

**Prediction memory:**

```yaml
iteration:
  target: WEIGHTED_CONSUMER_EDGE_BAND
  status: PROGRESS
  failed_strategy: ENERGY_ONLY_UNIFORM_WEIGHTED_CAUCHY_SCHWARZ
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE
  invariant_learned: carry consumer growth together with physical bandwidth
  forbidden_future_move: hide sqrt_log_growth_inside_a_fixed_constant
  next_decisive_test: kernel_gate_non_top_sqrt_log_rate
```
