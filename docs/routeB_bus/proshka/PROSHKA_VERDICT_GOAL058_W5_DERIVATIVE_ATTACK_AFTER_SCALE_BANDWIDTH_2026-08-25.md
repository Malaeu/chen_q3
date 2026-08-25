# STATUS: CONDITIONAL — SELECT LEGENDRE Q-COMB REPRESENTATION BEFORE ADDING A C1 SUPPLIER
```yaml
PRIMARY: W5_LEGENDRE_QCOMB_EXACT_REPRESENTATION_PREFLIGHT
OPERATIVE_CLASS: TRY_DERIVATIVE_ROW_REPRESENTATION_SHIFT

SOURCE_LOCK:
  SCALE_BANDWIDTH_GREEN_COMMIT: 7d27b5ad6cc65691752b85d4f3f5456aadc62b03
  D2_COMMIT: 584b45d2091befc449451cc3e8964d84da50fa3b
  D3_WALL_COMMIT: 2ce801a35f063be04676bc160f553502f2e35b25
  DERIVATIVE_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5DerivativeBudgetRate.lean
  FERRERS_SOLUTION_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersRegularEvenProlateSolution.lean
  NORMALIZED_MODE_LOCAL_FIELDS: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersNormalizedActualModeLocalFields.lean

CURRENT_FRONT:
  exact_gap: W5_LOG_DERIVATIVE_BUDGET_BOUNDED
  statement: >-
    exists D >= 0 such that eventually
    selectedFerrersAbelLogDerivativeBudget k <= D
  D3a_reduction: >-
    DerivativeBudget_k <= (1/2)*L1_k +
      integral_0^L sqrt(u(x))*norm(sum_active Q_k(n*u(x))) dx,
    Q_k(y)=y*deriv(pkt_k)(y)

ADJUDICATION:
  A_HIDDEN_SIGNED_IBP_MECHANISM: NOT_SELECTED
  reason_A: >-
    The norm is inside the integral. Signed integration by parts and zero-mass
    identities do not control total variation. A no-C1 sign route would need a
    new quantitative geometric fact about the real Q-comb itself (monotonicity,
    bounded sign changes, or equivalent variation control), and no such committed
    supplier was found.

  B_MINIMAL_C1_AS_NEW_PUBLIC_INPUT: HOLD_RUNNER_UP
  reason_B: >-
    The sufficient candidate norm(pkt'_k-4H') <= C'/sqrt(lambda_k) is not
    source-locked by Meixner-Schaefke Satz 9 or CCM Lemma 7.2. Do not promote it
    to a route input until the internal coefficient/ODE representation is tested.

  C_LEGENDRE_COEFFICIENT_QCOMB: SELECTED_PRIMARY
  reason_C: >-
    The Ferrers source already carries an exact three-term recurrence, tail splice,
    C2 interior regularity, and derivative-series realization. During construction
    the existing theorem mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
    proves summability of (q+1)^2*|a_q|. This is strong enough to justify moving
    the Legendre derivative series through the finite active E-star sum. It offers
    a genuinely different representation of the object under the norm: compute
    the Q-comb first, then estimate it.

PRIMARY_PREFLIGHT:
  name: W5_LEGENDRE_QCOMB_EXACT_REPRESENTATION_PREFLIGHT
  scope: PAPER_OR_SOURCE_ALGEBRA_FIRST
  no_lean_source_until_discriminator: true
  objective: >-
    For each selected mode and then for the exact scaled packet, expand
    y*h'(y) in the ordinary-even Legendre coefficient row and interchange the
    absolutely convergent q-series with the finite active n-sum. On each seam
    cell, write sum_n Q(n*u) as a q-series whose kernel is the explicit finite
    polynomial/power-sum functional
      K_q(M,r) = sum_{1<=n<=M} (n*r) * P'_{2q}(n*r),
    with r=u/lambda and M=floor(lambda/u) fixed on the cell.

  required_exact_output:
    - exact coefficient orientation and physical lambda factors
    - exact active-index endpoint convention
    - exact center/edge shadow terms; no endpoint value set to zero
    - an identity or one-sided bound for K_q that keeps the leading Euler/power-sum cancellation explicit
    - a final coefficient functional B_k such that
        integral sqrt(u)*norm(Qcomb_k(u)) <= B_k
      and whose cofinal boundedness can be decided from committed recurrence/tail data

DISCRIMINATOR:
  name: LEGENDRE_QCOMB_BOUND_FROM_COMMITTED_WEIGHTED_ROW
  PASS: >-
    The exact K_q representation reduces B_k to coefficient quantities already
    bounded by normalization/recurrence/tail-splice/F72.6, with no new analytic
    premise, and yields eventually B_k <= constant.
  FAIL: >-
    After exact cancellation, B_k still requires a new cofinal quantitative
    coefficient norm not supplied by the recurrence/tail data, or produces a
    positive power of lambda under every available committed bound.
  ZERO_CONSISTENT: INCONCLUSIVE_REQUIRES_NAMED_WEIGHTED_COEFFICIENT_SUPPLIER

CHEAP_KILL_GUARD:
  forbidden_triangle_route: >-
    Do not take absolute values term-by-term in the active n-sum before exposing
    its cancellation. That route gives scale approximately
    sqrt(lambda)*integral_0^lambda y*|pkt'_k(y)|dy and therefore grows even for
    the fixed cylinder target; it cannot prove the desired bounded budget.

RUNNER_UP_C1_IF_PRIMARY_FAILS:
  name: MINIMAL_C1_F72_6_DERIVATIVE_ERROR
  exact_candidate: >-
    exists C1 >= 0 such that eventually, for every y in the open source window,
      norm(deriv(selectedFerrersLemma73SourcePacket k) y -
           4*deriv(explicitCCMLimitH) y)
        <= C1 / Real.sqrt(selectedFerrersPaperLambda k)
  status: UNPROVED_CANDIDATE
  activation_rule: >-
    Activate only if the Legendre-Q-comb preflight returns FAIL and identifies
    this derivative-error norm, or a weaker explicit derivative norm, as the
    smallest sufficient missing quantity.

SECOND_RUNNER_UP:
  name: ODE_RESIDUAL_TO_DERIVATIVE_ENERGY
  description: >-
    Subtract the physical prolate ODE from the limiting cylinder ODE and use a
    weighted Sturm energy estimate for the remainder. This may derive a C1/L2
    derivative rate from the existing C0 and eigenvalue-defect data rather than
    importing a paper C1 theorem.
  kill_power: 8/10
  cost: 7/10

REGISTERED_PREDICTIONS:
  P_DERIV_LEGENDRE_1:
    probability: 0.66
    prediction: >-
      The exact Legendre/power-sum Q-comb representation exposes cancellation
      invisible to the D3a pointwise triangle bound and reduces the derivative
      wall to a quantitative weighted coefficient functional smaller than full C1.
    fate: UNTESTED
  P_DERIV_LEGENDRE_2:
    probability: 0.72
    prediction: >-
      Qualitative polynomially weighted summability alone is insufficient;
      if the route fails, the first failure will be lack of a cofinal uniform
      bound on the resulting weighted coefficient functional, not inability to
      justify differentiation or series interchange.
    fate: UNTESTED
  P_DERIV_C1_1:
    probability: 0.58
    prediction: >-
      A full uniform C1 analogue of F72.6 is stronger than necessary for the
      consumer and should remain a runner-up until the coefficient preflight is scored.
    fate: UNTESTED

CLOSES:
  - W5_DERIVATIVE_NEXT_REPRESENTATION_SELECTION
  - PREMATURE_C1_IMPORT_AS_PRIMARY
OPENS: []
CARRIES_OPEN:
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED

NEXT_LOAD_BEARING_GAP: LEGENDRE_QCOMB_BOUND_FROM_COMMITTED_WEIGHTED_ROW

ARSENAL_MANDATE: ACCEPTED_NO_LIVE_SIDECAR_MUTATION
CARDS_APPLIED:
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```

## ROUTE MAP

The scale and bandwidth transaction is accepted at the reported kernel boundary. The projection-tail chain now leaves `W5_LOG_DERIVATIVE_BUDGET_BOUNDED` as the unique non-owner analytic gap. The old D3 wall remains valid: the norm is inside the derivative budget, so signed integration by parts does not close it.

The next move should not be to add a C1 theorem by assumption. The Ferrers construction already contains more structure than the C0 statement exposes: an exact Jacobi recurrence, a tail splice, interior C2 regularity, endpoint zero-flux, and a derivative series whose construction uses polynomially weighted absolute summability. The correct representation shift is therefore to expand the exact Q-comb itself in that coefficient row before taking its norm.

For a physical mode written as a normalized even Legendre series, `y*h'(y)` has no extra physical power of lambda after the change `s=y/lambda`: it is a coefficient sum of `s*P'_{2q}(s)`. On one E-star seam cell the active n-set is finite and fixed, so the signed comb is a coefficient series against an explicit finite polynomial power-sum kernel. This is the place where exact cancellation can survive the norm. Taking absolute values before this rewrite destroys that possibility and gives a provably wrong scale for the target profile.

## FINAL PROPOSAL

Run a paper/source preflight first; do not write a new Lean theorem yet. Derive the exact Legendre coefficient formula for the finite Q-comb, including all endpoint terms, and reduce its log-window L1 norm to one explicit weighted coefficient functional. Then ask only whether the committed recurrence/tail-splice/normalization bounds that functional uniformly in k.

If that discriminator passes, formalize the exact representation and the resulting bound as the derivative supplier. If it fails, name the smallest missing weighted coefficient estimate. Only if that missing estimate is equivalent to pointwise derivative control should the route activate the minimal C1 candidate.

## STRONGEST ATTACK

Polynomially weighted summability is currently qualitative for each fixed selected solution. It guarantees legality of differentiation and interchange, not a cofinal uniform constant. A proof that simply cites this summability and hides its k-dependence would not move the route. The preflight must expose the exact weighted coefficient functional and its lambda scaling before any formalization.

## META CLOSEOUT

- `P_SCALE_1`: CONFIRMED by commit 7d27b5ad.
- `P_BANDWIDTH_1`: CONFIRMED by commit 7d27b5ad.
- The remaining analytic wall is genuinely the W5 derivative budget.
- Direct signed IBP remains killed.
- Full C1 remains a runner-up, not an imported theorem.
- Next discriminator: `LEGENDRE_QCOMB_BOUND_FROM_COMMITTED_WEIGHTED_ROW`.
