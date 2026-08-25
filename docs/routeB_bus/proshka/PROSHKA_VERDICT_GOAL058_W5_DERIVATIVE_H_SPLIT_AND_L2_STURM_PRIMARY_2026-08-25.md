# STATUS: CONDITIONAL — COMMIT THE EXPLICIT H-BUDGET NODE; SELECT C1-L2 / STURM-ODE RESIDUAL FOR THE DEFECT
```yaml
PRIMARY: W5_DERIVATIVE_DEFECT_L2_STURM
OPERATIVE_CLASS: TRY_EXPLICIT_H_SPLIT_THEN_L2_DEFECT_ENERGY
SOURCE_LOCK:
  QCOMB_PREFLIGHT_COMMIT: 0a6d94d6585e6fa983b6aa7b85e9612af284ad9b
  SCALE_BANDWIDTH_COMMIT: 7d27b5ad6cc65691752b85d4f3f5456aadc62b03
  D2_D3A_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5DerivativeBudgetRate.lean
  FERRERS_ODE_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersNormalizedActualModeLocalFields.lean
ADJUDICATION:
  LEGENDRE_QCOMB_FROM_COMMITTED_WEIGHTED_ROW: FAIL
  LEADING_EULER_MACLAURIN_TERM: CLOSED_BY_COMMITTED_DATA
  OLD_C1_SUP_RUNNER_UP_LAMBDA_MINUS_HALF: KILLED_INSUFFICIENT
  EXPLICIT_H_BUDGET_NODE: RATIFIED_NOW
  C1_L1_DEFECT_PACKAGE: RUNNER_UP
  C1_L2_STURM_DEFECT_PACKAGE: SELECTED_PRIMARY
EXPLICIT_H_NODE:
  name: W5_EXPLICIT_H_QCOMB_BOUNDED
  target: >-
    Define the explicit target comb from g_H(y)=4*y*deriv(explicitCCMLimitH)(y)
    on the same multiplicative window and prove an absolute constant D_H with
    integral u^(-1/2)*norm(sum_active g_H(n*u)) du <= D_H for every k.
  inputs: []
  verifier: LEAN
  scope: COFINAL_FAMILY
DEFECT_OBJECT:
  delta_k: selectedFerrersLemma73SourcePacket k - 4*explicitCCMLimitH
  window: [0, selectedFerrersPaperLambda k]
PRIMARY_MISSING_SUPPLIER:
  name: W5_PACKET_DEFECT_DERIVATIVE_L2_RATE
  statement: >-
    exists C >= 0 such that eventually in k,
    integral_0^lambda norm(deriv(delta_k)(y))^2 dy <= C^2/lambda^4.
  equivalent_norm_shape: >-
    norm(delta_k')_{L2(0,lambda)} <= C/lambda^2.
  scope: COFINAL_FAMILY
  verifier: CONDITIONAL
WHY_L2:
  - one scalar energy supplier instead of the L1 package's bulk second-derivative mass plus separate edge-slope input
  - the Q-comb preflight already supplies the Cauchy-Schwarz consumer map from this L2 rate to a bounded defect derivative budget
  - the selected normalized modes carry an exact physical Sturm/prolate ODE and exact eigenvalue-defect inputs, so an energy estimate is source-faithful
  - endpoint jump values do not have to be declared zero; the L2 defect derivative is an interior/window energy object
STURM_PREFLIGHT_TARGET:
  name: W5_PACKET_DEFECT_STURM_ENERGY_IDENTITY
  instruction: >-
    Before Lean, subtract the exact physical prolate ODE for the anchored selected modes from the exact limiting cylinder ODE for the corresponding D0/D4 targets. Multiply the defect equation by conjugate(delta), integrate on the physical window, and keep every endpoint flux, potential mismatch, eigenvalue defect, and normalization factor explicit. Determine whether the resulting coercive/energy identity yields lambda^4 * integral|delta'|^2 <= O(1) from the already committed C0 and eigenvalue-defect rates.
  discriminator:
    PASS: existing F72.6 inputs imply W5_PACKET_DEFECT_DERIVATIVE_L2_RATE with no new analytic source
    FAIL: return the exact positive/indefinite term whose coefficient has the wrong lambda scaling; do not replace it by a generic C1 request
RUNNER_UP_C1_L1:
  statement: >-
    integral_0^lambda (norm(delta') + y*norm(delta'')) dy <= C/sqrt(lambda)
    and sup_{y in (lambda-1,lambda]} norm(delta'(y)) <= C/lambda^(3/2).
  status: HOLD
KILLS:
  - OLD_MINIMAL_C1_SUP_NORM_RATE_lambda_minus_half
  - TRIANGLE_BEFORE_QCOMB_CANCELLATION
  - QUALITATIVE_WEIGHTED_LEGENDRE_SUMMABILITY_AS_COFINAL_BOUND
FORBIDDEN:
  - import a C1 theorem from Meixner-Schaefke Satz 9 or CCM Lemma 7.2; current source lock is C0 only
  - infer integral of a norm from signed IBP
  - drop endpoint flux terms in the Sturm subtraction
  - use numerical derivative stability as a cofinal proof
  - change the packet, downstream consumer, or family
CLOSES:
  - W5_DERIVATIVE_REPRESENTATION_FORK
  - OLD_C1_LAMBDA_MINUS_HALF_CANDIDATE
OPENS: []
CARRIES_OPEN:
  - W5_PACKET_DEFECT_DERIVATIVE_L2_RATE
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED
REGISTERED_PREDICTIONS:
  P_DERIV_H_1:
    probability: 0.94
    prediction: the explicit H Q-comb admits a uniform absolute budget with no source hypotheses
  P_DERIV_STURM_1:
    probability: 0.61
    prediction: the exact Sturm subtraction improves the naive C0-to-H1 scaling by at least the missing sqrt(lambda), enough to reach the L2 defect target or isolate one exact term that prevents it
  P_DERIV_C1L1_1:
    probability: 0.43
    prediction: the L1 package is formally sufficient but materially harder to source because it needs both bulk second-derivative mass and a separate edge-slope rate
ARSENAL_MANDATE: ACCEPTED_NO_LIVE_SIDECAR_MUTATION
CARDS_APPLIED:
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW
SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: ENERGY_REPRESENTATION
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```

## ROUTE MAP

The Q-comb preflight kills the hope that qualitative polynomially weighted Legendre summability closes the derivative budget. It also kills the previously suggested uniform derivative-error bound of order lambda^(-1/2): that rate is quantitatively insufficient once the norm-inside-integral geometry is respected.

The preflight nevertheless closes the leading Euler-Maclaurin contribution and exposes an exact source/target split. The explicit limiting target H contributes a standalone Q-comb with no selected-source uncertainty. That piece should be formalized immediately and removed from the live gap.

For the remaining defect delta=pkt-4H, the preferred missing quantity is the L2 derivative rate. It is strictly cleaner than the C1-L1 package because it asks for one energy quantity and is aligned with the exact self-adjoint prolate/Sturm operator already carried by the selected normalized Ferrers modes. The next decisive action is therefore not to assume the L2 rate but to derive the exact defect energy identity before Lean and test its lambda scaling.

## STRONGEST ATTACK

The L2 target may itself be too strong: naive C0 differentiation predicts only lambda^(-3/2) in L2, while the requested rate is lambda^(-2). Therefore the Sturm preflight must identify where the extra sqrt(lambda) is gained. If no coercive/eigenvalue-defect term supplies that gain, return the exact failed inequality and fall back to the C1-L1 package or a weaker consumer-weighted energy. Do not silently promote the L2 target to a new source assumption.

## CODEX / LINUX DIRECTIVE

First commit the unconditional explicit-H budget node. Separately, run the W5_PACKET_DEFECT_STURM_ENERGY_IDENTITY preflight on paper/source algebra before writing any defect Lean. No second-order bulk computation is authorized until every endpoint flux and lambda factor is visible.

## META CLOSEOUT

The derivative wall is now split into a solved explicit target component and one defect-energy question. This is a smaller gap than generic C1 regularity. If the Sturm discriminator fails, the returned obstruction must be one named weighted term with exact lambda scaling.
