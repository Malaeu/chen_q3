# STATUS: CONDITIONAL — CENTRAL V0 FLOOR KILLED BY ZERO-MASS CANCELLATION; LOCAL-CELL FULL-NORM FLOOR SELECTED; ONE LEAN TRANSACTION AUTHORIZED

```yaml
PRIMARY: RUN_GOAL058_SELECTED_FERRERS_LOCAL_CELL_NORMALIZER_CLOSURE
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-H
  QUEUE_REQ_ID_PROVENANCE: JUDGE_ASSIGNED_TO_DIRECT_FOLLOWUP_OF_REQ_2026_08_26_G
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  HEAD: 97322718791fe9fd0542defc1753f3f0c5a4f0bf
  HEAD_IS_ORIGIN_RH_CLEAN_AT_AUDIT: true
  PARENT_VERDICT_COMMIT: f9b9c169e9a7fcaadf2ad9cc7f2b9b195acfd750
  PREFLIGHT_PATH: docs/routeB_bus/LINUX_SELECTED_TRIAL_NORMALIZER_ROUTE_PREFLIGHT_GOAL058_2026-08-26.md
  PREFLIGHT_GIT_BLOB: a716ad023dca3b6894ca5ecbdb9a18ee93b59de5
  PREFLIGHT_COMMIT: 97322718791fe9fd0542defc1753f3f0c5a4f0bf
  PREFLIGHT_MODE: PAPER_AND_SOURCE_READ_ONLY

EXACT_IDENTITY_AUDIT:
  selectedTrialNormalizer_eq_inverse_projected_norm:
    status: PASS
    scope: ABSTRACT
    verifier: LEAN
  normalized_residual_norm_factorization:
    status: PASS
    scope: COFINAL_FAMILY
    verifier: LEAN
  inner_V0_projection_preservation:
    status: PASS
    scope: ABSTRACT
    verifier: LEAN
  V0_unit_norm:
    status: PASS
    scope: ABSTRACT
    verifier: LEAN

PREFLIGHT_DISCRIMINATOR:
  claimed_outcome: SELECTED_TRIAL_NORMALIZER_FULL_NORM_FLOOR_ROUTE_READY
  adjudicated_outcome: FAIL_AS_SPECIFIED_REPAIR_READY
  failure_code: SELECTED_TRIAL_NORMALIZER_V0_ZERO_MASS_CANCELLATION_AND_SCALE_DIRECTION
  kills:
    - CENTRAL_V0_OVERLAP_GROWS_LIKE_SQRT_LAMBDA_OVER_SQRT_LOG
    - CENTRAL_V0_OVERLAP_ALONE_SUPPLIES_EVENTUAL_PROJECTED_NORM_FLOOR
  does_not_kill:
    - SelectedTrialNormalizerBounded
    - full_object_norm_floor_route
    - direct_weighted_product_route

CENTRAL_V0_FATALS:
  SUPPORT_WINDOW_ERROR:
    finding: >-
      After y=n*u, compact source support truncates the physical integral at
      lambda, not at n*lambda. The exact source-window central comb is
      sum_{n<=lambda^2} n^(-1/2) integral_{n/lambda}^{lambda}
      y^(-1/2) H(y) dy.
    scope: COFINAL_FAMILY
    verifier: PAPER
  ONE_SIGN_MIDDLE_STRIP_ERROR:
    finding: >-
      The inner integrals do not have one sign on n in [sqrt(lambda),lambda].
      The full Mellin-half mass is negative, while for n/lambda near one the
      integral is over the positive outer region of H and is positive.
      Therefore a selected partial strip is not a lower bound for the modulus
      of the complete central overlap.
    scope: COFINAL_FAMILY
    verifier: PAPER
  ZERO_MASS_LEADING_CANCELLATION:
    finding: >-
      The Dirichlet-window leading term is proportional to
      2*sqrt(lambda)*integral_0^infty H(y)dy, and this flat mass is exactly zero.
      Nonzero Mellin-half mass does not restore the discarded leading term.
    scope: COFINAL_FAMILY
    verifier: PAPER
  SCALE_INEQUALITY_DIRECTION:
    finding: >-
      norm(sourceScale^{-1}) <= 8 is an upper bound on the unscaled object in
      terms of the scaled object. It cannot produce a lower floor. A lower
      floor requires an eventual upper bound on norm(sourceScale), equivalently
      a positive lower bound on norm(sourceScale^{-1}).
    scope: ABSTRACT
    verifier: PAPER

LOGICAL_BOUNDARY:
  failure_of_sufficient_route_certifies_negation: false
  exact_statement: >-
    The report did not establish the requested lower envelope for the literal
    V0 overlap. This rejects its ROUTE_READY code only. It does not prove that
    the selected normalizers are unbounded.

REPAIRED_PRIMARY:
  name: SELECTED_FERRERS_LOCAL_CELL_FULL_TRIAL_NORM_FLOOR
  representation: FIXED_MULTIPLICATIVE_CELL
  fixed_cell: Set.Icc 1 (9/8)
  principle: >-
    Keep sign location instead of averaging it into V0. On this fixed cell,
    every active explicit-H summand is positive and the n=1 term gives a fixed
    positive floor. The F72 packet error is O(lambda^{-1}) after active-card
    counting, so it cannot cancel the floor.
  scope: COFINAL_FAMILY
  verifier: PAPER_CONDITIONAL

REPAIRED_PAPER_ROUTE:
  STEP_1_SCALE_UPPER:
    output: >-
      exists M>0, eventually norm(selectedFerrersLemma73SourceScale k) <= M.
    inputs:
      - literal_center_anchored_mode_rates
      - chi_defect_rates
      - unit_L2_normalization_of_h0_and_h4
      - exact_center_anchor_locks
      - explicit_polynomial_gaussian_L2_majorants
    exact_algebra: >-
      From a0*h0(0)=1, a4*h4(0)=3 and Ij=chij*hj(0), derive
      norm(scale73)^2 = (norm(a4)^2*chi0^2 + 9*norm(a0)^2*chi2^2)/16.
      The anchored L2 rates give eventual upper bounds for norm(a0), norm(a4),
      and hchi gives eventual abs(chi0),abs(chi2)<=2.
    new_analytic_input: none
  STEP_2_LOCAL_ESTAR_FLOOR:
    target: >-
      exists b>0, eventually for all u in [1,9/8],
      b <= norm(selectedFerrersLemma73SourceScale k *
                E_star(prolateCombination pair_k) u).
    source: selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
    mechanism: >-
      The literal source comb is finite on the window. The n=1 term is active.
      For y>=1, explicitCCMLimitH(y)>0. Hence the exact 4H comb has a fixed
      positive lower floor on [1,9/8]. The total packet error is at most
      sqrt(u)*card(active)*(C/lambda^2) <= constant*C/lambda and tends to zero.
  STEP_3_FULL_OBJECT_NORM_FLOOR:
    target: >-
      exists c>0, eventually c <= norm(gTrial_m i'_k h_k hLp_k).
    mechanism: >-
      Divide the local scaled floor by the scale upper bound from Step 1, then
      integrate the resulting pointwise norm floor over [1,9/8] with dStar=du/u.
      This cell has fixed positive dStar mass log(9/8).
  STEP_4_PROJECTED_NORM_FLOOR:
    input: selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
    mechanism: >-
      hFamily transports the literal full and projected trials. Reverse triangle
      gives norm(P_k g_k) >= norm(g_k)-norm(P_k g_k-g_k); tail decay makes the
      second term <=c/2 eventually, so norm(P_k g_k)>=c/2.
  STEP_5_NORMALIZER_AND_RESIDUAL:
    outputs:
      - SelectedTrialNormalizerBounded S
      - Tendsto (fun k => norm(selectedNormalizedGalerkinResidual S k)) atTop (nhds 0)
    mechanism: >-
      selectedTrialNormalizer is the inverse projected norm, hence eventually
      <=2/c. Invoke the existing exact two-premise residual receiver with the
      already admitted SelectedProjectionTailDecay supplier.

WHY_THIS_REPAIR_IS_STRONGER:
  uses_V0_global_average: false
  uses_zeta_half_nonvanishing: false
  uses_gamma_mellin_constant: false
  uses_subsequence: false
  uses_new_owner_hypothesis: false
  keeps_literal_moving_carriers: true
  keeps_literal_normalized_residual: true

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_LOCAL_CELL_NORMALIZER_CLOSURE
  MODE: ONE_GOAL_ONE_COMMIT
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrialNormalizerClosure.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_TRIAL_NORMALIZER_CLOSURE_2026-08-26.md
  REQUIRED_PUBLIC_THEOREMS:
    - selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
    - selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_selectedFerrersW5RateLedger
  REQUIRED_PUBLIC_INPUTS:
    - S_ProlateCanonicalSourceData
    - hFamily_SelectedFerrersPreAnchorProductionFamilyCrosswalk_S
    - hmode_literal_center_anchored_mode_rates
    - hchi_literal_chi_defect_rates
    - htheta_two_distinct_selected_differential_eigenvalue_defect_rates
  NEW_ANALYTIC_INPUT: none
  PRIVATE_HELPERS_PREFERRED:
    - selectedFerrersLemma73SourceScale_eventually_bounded_above
    - selectedFerrersScaledEStar_localCell_floor
    - selectedFerrersFullTrialNorm_eventually_bounded_below
    - selectedFerrersProjectedTrialNorm_eventually_bounded_below
  PROOF_ORDER:
    - run_capability_catalog_preflight
    - derive_anchored_L2_and_scale_upper_bound
    - prove_explicit_H_positive_floor_on_Icc_1_9_over_8
    - prove_active_finite_comb_error_O_lambda_inverse
    - derive_scaled_and_unscaled_local_cell_floors
    - integrate_to_full_Hm_norm_floor
    - transport_through_hFamily
    - combine_with_selectedProjectionTailDecay_by_reverse_triangle
    - prove_SelectedTrialNormalizerBounded
    - invoke_existing_normalized_residual_receiver
  FORBIDDEN:
    - reuse_the_rejected_V0_sqrt_lambda_growth
    - infer_uniform_bound_from_TrialNonzero
    - use_norm_sourceScale_inverse_upper_as_a_lower_floor
    - discard_complement_terms_under_a_norm
    - treat_zero_positive_mass_as_nonzero
    - select_a_second_subsequence
    - replace_object_residual_by_scalar_Mellin_coordinate
    - fixed_carrier_projection_theorem_for_the_moving_family
    - numerical_fit_or_probe_as_proof
    - add_new_owner_hypothesis
    - route_promotion_or_RH_claim
  EXPECTED_AXIOM_PROFILES:
    ALL_PUBLIC:
      - propext
      - Classical.choice
      - Quot.sound
  VERIFICATION_HANDOFF:
    WORKDIR_q3_lean_aristotle:
      - lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersTrialNormalizerClosure.lean
      - lake build Q3.Proofs.RouteB.G6N1SelectedFerrersTrialNormalizerClosure
    WORKDIR_repo_root:
      - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersTrialNormalizerClosure.lean
  SUCCESS_CODE: SELECTED_FERRERS_TRIAL_NORMALIZER_AND_NORMALIZED_RESIDUAL_LEAN
  FAILURE_CODE: GOAL058_LOCAL_CELL_ESTAR_FLOOR_OR_SCALE_UPPER_BOUND_GAP

ALTERNATIVE_R2:
  name: DIRECT_WEIGHTED_NORMALIZER_TIMES_TAIL
  status: RUNNER_UP_NOT_SELECTED
  kill_power: 8/10
  proof_cost: 7/10
  activation_condition: repaired_local_cell_floor_fails_at_exact_scale_or_Lp_port
  discriminator: >-
    If no fixed local cell can produce a cofinal lower norm floor while preserving
    the literal source scale, prove directly that normalizer_k*tail_k tends to zero
    from coupled coefficient and projection rates.

CLOSES:
  - SELECTED_TRIAL_NORMALIZER_ROUTE_DISCRIMINATOR
  - CENTRAL_V0_OVERLAP_GROWTH_FALSE_ROUTE
OPENS: []
CARRIES_OPEN:
  - SELECTED_TRIAL_NORMALIZER_BOUNDED_UNTIL_KERNEL_GATE
  - SELECTED_NORMALIZED_GALERKIN_RESIDUAL_DECAY_UNTIL_KERNEL_GATE
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_LITERAL_CENTER_ANCHORED_MODE_RATE_FAMILY
  - F72_CHI_DEFECT_RATE_FAMILY
  - SELECTED_DIFFERENTIAL_EIGENVALUE_DEFECT_RATE_FAMILY
  - G6_S2_DOWNSTREAM_SAME_FAMILY_COMPACT_DECAY

NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_LOCAL_CELL_FULL_TRIAL_NORM_FLOOR
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: G6_S2_DOWNSTREAM_SAME_FAMILY_COMPACT_DECAY

PREDICTION_FATES:
  P_NORMALIZER_ROUTE_1:
    prior_probability: 0.58
    prior_claim: >-
      A source-faithful eventual lower norm floor for the full selected trial,
      combined with tail decay, yields bounded selected trial normalizers.
    fate: SUPPORTED_AT_REPAIRED_PAPER_SHAPE_NOT_YET_AT_KERNEL
  P_NORMALIZER_ROUTE_2:
    prior_probability: 0.34
    fate: UNTESTED_RUNNER_UP
  PREFLIGHT_CENTRAL_V0_GROWTH_CLAIM:
    fate: REFUTED_AS_STATED
  P_LOCAL_CELL_FLOOR_1:
    probability: 0.84
    prediction: >-
      The fixed cell [1,9/8], F72 packet rate and a derived source-scale upper
      bound prove a uniform full-trial norm floor without a new analytic input.
  P_LOCAL_CELL_NORMALIZER_LEAN_1:
    probability: 0.80
    prediction: >-
      One Lean transaction closes both SelectedTrialNormalizerBounded and the
      literal normalized Galerkin residual decay on the frozen selected family.
  LIKELIEST_FAILURE:
    class: SOURCE_SCALE_UPPER_BOUND_OR_LP_LOCAL_CELL_NORM_API
    response: preserve_the_public_targets_and_isolate_one_exact_private_helper

ARSENAL_MANDATE: ACCEPTED_CURRENT_DECK
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C01_SIGN_MASS_LOCALIZATION
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_CONDITIONAL
PROGRESS_CLASS: FALSIFICATION_PROGRESS_AND_REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```

## ROUTE MAP

The preflight correctly locked the exact normalizer and residual identities.  The
normalizer is the inverse norm of the literal finite Galerkin projection, and the
normalized residual norm is exactly the product of that normalizer with the
unnormalized projection tail.  The committed `V₀` overlap-preservation theorem is
also correct.  `[ABSTRACT][LEAN]`

The failure occurs in the proposed lower envelope, not in those identities.
For the finite source packet, compact support changes the post-substitution
integral to

\[
 A_\lambda
 =\sum_{n\le\lambda^2} n^{-1/2}
   \int_{n/\lambda}^{\lambda} y^{-1/2}H(y)\,dy.
\]

The report instead used an upper endpoint `n*lambda`.  More importantly, the
inner integrals do not have one sign on the proposed middle strip.  The full
Mellin-half mass is negative, but the integrals whose lower endpoint approaches
one lie in the region where the explicit packet `H` is positive.  Dropping the
remaining terms therefore cannot give a lower bound on the modulus of the whole
sum.  `[COFINAL_FAMILY][PAPER]`

The same obstruction appears in Dirichlet-window coordinates.  The leading
square-root term is

\[
 2\sqrt\lambda\int_0^\infty H(y)\,dy,
\]

and the positive-half mass of the explicit packet is exactly zero.  Thus the
claimed `sqrt(lambda)` main term is precisely the term that cancels.  The
calculation that the Mellin-half mass is nonzero may be correct, but it does not
undo this leading zero-mass cancellation.  `[COFINAL_FAMILY][PAPER]`

There is a second independent direction error.  A theorem
`norm(sourceScale⁻¹) <= 8` supplies only an upper estimate for the unscaled
central overlap in terms of the scaled overlap.  A lower floor needs an upper
bound on `norm(sourceScale)` instead.  The report did not supply that bound.
`[ABSTRACT][PAPER]`

Therefore its success code is rejected.  This is not a proof that the selected
normalizers are unbounded.  It kills one sufficient representation only, in
accordance with the rule that failure of a sufficient condition never certifies
the negation.

## REPAIRED PRIMARY

Use **sign localization**, not the global zero Fourier mode.  Fix the
multiplicative cell

\[
 J=[1,9/8].
\]

For sufficiently large `k`, this cell lies inside the exact source window.  The
`n=1` term is active throughout `J`.  Moreover, for every `y>=1`,

\[
 H(y)=\frac\pi2y^2(2\pi y^2-3)e^{-\pi y^2}>0.
\]

Hence every active target summand has the same sign, and the first summand alone
provides a fixed positive lower floor.  This is exactly what the global `V₀`
average forgot.  `[COFINAL_FAMILY][PAPER]`

The factor-four packet theorem gives a pointwise error `C/lambda²` for each
active physical summand.  There are at most `lambda/u` active terms, so on the
fixed cell the total starred-comb error is at most a fixed multiple of
`C/lambda`.  It tends to zero and cannot cancel the target floor.
`[COFINAL_FAMILY][PAPER]`

One missing algebraic helper must be derived internally: an eventual upper bound
on the literal source scale.  It follows from the existing anchored mode rates,
unit `L²` normalization and explicit Gaussian `L²` envelopes.  The exact center
locks give

\[
 a_0I_0=\chi_0,
 \qquad
 a_4I_4=3\chi_2,
\]

and therefore

\[
 \|s_{73}\|^2
 =\frac{\|a_4\|^2\chi_0^2+9\|a_0\|^2\chi_2^2}{16}.
\]

The frozen rates bound all four factors eventually.  This is a theorem
consequence of existing inputs, not a new owner hypothesis.  `[COFINAL_FAMILY][PAPER_CONDITIONAL]`

Dividing the scaled local floor by this scale ceiling gives a pointwise floor
for the literal `E_star` packet on `J`.  Integrating over `J` with `du/u` gives a
fixed positive lower bound for the full `H_m` norm.  The already admitted
projection-tail theorem then makes the projected norm at least half of this
floor by the reverse triangle inequality.  Its inverse is eventually bounded,
and the existing two-premise receiver closes the literal normalized residual.
`[COFINAL_FAMILY][PAPER_CONDITIONAL]`

## STRONGEST ATTACK

The local-cell route must not smuggle a sign assertion through a norm.  The Lean
transaction must explicitly filter active indices, prove that `n=1` belongs to
the filter, prove positivity of every target summand on the fixed cell, and only
then derive the lower floor.  It must also prove the source-scale **upper** bound
before dividing.  Reusing the existing inverse-scale upper theorem is the wrong
inequality direction and is forbidden.

## FINAL PROPOSAL

Run one Lean transaction for the local-cell full-norm floor, normalizer bound and
final normalized-residual corollary.  Do not formalize the rejected central
Mellin asymptotic, do not import zeta-half nonvanishing, and do not reopen W5.
If the local-cell `Lp` port or scale ceiling fails, stop with the exact private
helper that failed and activate the coupled weighted-product runner-up.

## CODEX / LINUX DIRECTIVE

```text
TASK_ID: GOAL058_SELECTED_FERRERS_LOCAL_CELL_NORMALIZER_CLOSURE
MODE: ONE_GOAL_ONE_COMMIT

OBJECTIVE:
  Prove SelectedTrialNormalizerBounded and decay of the literal normalized
  selected Galerkin residual from the frozen selected-family inputs, using a
  fixed positive multiplicative cell rather than the rejected V0 average.

READ_FIRST:
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage1.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage2.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0KTrialStage3.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5RateAssembly.lean
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean

CREATE:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrialNormalizerClosure.lean
  docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_TRIAL_NORMALIZER_CLOSURE_2026-08-26.md

PUBLIC_SURFACE:
  selectedTrialNormalizerBounded_of_selectedFerrersW5RateLedger
  selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_selectedFerrersW5RateLedger

SUCCESS:
  SELECTED_FERRERS_TRIAL_NORMALIZER_AND_NORMALIZED_RESIDUAL_LEAN

FAIL:
  GOAL058_LOCAL_CELL_ESTAR_FLOOR_OR_SCALE_UPPER_BOUND_GAP
```
