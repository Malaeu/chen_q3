# STATUS: CONDITIONAL — RATIFY STURM ENERGY / EXPLICIT TRANSPORT / WEIGHTED CONSUMER; DO NOT PROMOTE THE SLIVER SUP-NORM
```yaml
PRIMARY: W5_DEFECT_WEIGHTED_STURM_TO_EXACT_EDGE_CONSUMER
OPERATIVE_CLASS: TRY_WEIGHTED_STURM_CHAIN_THEN_EDGE_CONSUMER_COMPRESSION
QUEUE_ENTRY: LINUX_2026_08_25_STURM_PREFLIGHT
QUEUE_REQ_ID: UNASSIGNED_IN_SOURCE

SOURCE_LOCK:
  STURM_PREFLIGHT_COMMIT: 4c62caa5abd416cd30d1de87aece0eaf95e2e339
  H_BUDGET_COMMIT: 17d7a5a817c77d20db88646712cea072bafa1a2e
  PHYSICAL_ODE_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersPhysicalProlateScaling.lean
  ENDPOINT_FLUX_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersEndpointFlux.lean

ADMISSION:
  P_DERIV_STURM_1: CONFIRMED
  EXPLICIT_H_QCOMB: KERNEL_GREEN_REPORTED
  STURM_PREFLIGHT: PARTIAL_PASS_WEIGHTED
  LITERAL_UNWEIGHTED_L2_TARGET_AS_REQUIRED_CONSUMER: REJECTED_TOO_STRONG

RATIFIED_NODE_ORDER:
  1_STURM_ENERGY_NODE:
    status: AUTHORIZED
    output: >-
      eventual weighted defect energy
      integral_{-lambda}^{lambda} (lambda^2-x^2)*norm(delta'(x))^2 dx
      <= C_E^2/lambda^2
    inputs:
      - committed F72.6 C0 mode rates
      - committed F72.3B eigenvalue-defect rates
    new_analytic_suppliers: []
  2_W_TRANSPORT_L1_NODE:
    status: AUTHORIZED
    output: >-
      absolute L1 bound for the explicit cylinder transport derivative
      d/dx(x^2 W'(x)), uniform in the selected mode class needed by the Sturm ledger
    inputs: []
    new_analytic_suppliers: []
  3_WEIGHTED_CONSUMER_NODE:
    status: AUTHORIZED
    output: >-
      convert the weighted Sturm energy to the defect Q-comb budget on every
      lattice contribution except the exact uppermost-edge contribution
    requirement: >-
      keep the companion factor and the top lattice point explicit; do not
      replace the residual by a stronger pointwise derivative hypothesis
    new_analytic_suppliers: []

SLIVER_ADJUDICATION:
  proposed_sup_supplier:
    name: W5_DEFECT_EDGE_SLIVER_SLOPE
    statement: >-
      eventually sup_{y in (lambda-1/lambda,lambda]} norm(delta'(y))
      <= C/sqrt(lambda)
    verdict: DO_NOT_PROMOTE_YET
    reason: >-
      It is only one sufficient bound for the residual top-lattice contribution.
      The committed endpoint theorem gives zero FLUX, not this quantitative
      derivative sup-rate. The physical ODE has mode4JacobiG(m)=(2*pi*m)^2,
      so at m=lambda^2 the shifted endpoint relation can amplify an O(lambda^-2)
      edge value. Current C0 data therefore do not imply the stated sup-rate.

  minimal_missing_consumer:
    name: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BOUNDED
    statement: >-
      The exact contribution of the uppermost active lattice point after the
      weighted-Cauchy-Schwarz decomposition is eventually bounded on the
      selected family. State this contribution in the same u-variable and
      normalization used by W5; do not replace it by a sup norm.
    role: ONLY_OPEN_DERIVATIVE_INPUT_AFTER_NODES_1_TO_3

FIRST_DISCRIMINATOR:
  name: EDGE_TOP_BUDGET_FROM_ZERO_FLUX_ODE_AND_C0
  pass: >-
    exact physical ODE + endpoint zero-flux + committed C0/eigenvalue data
    bound the top-lattice integral at consumer strength, with no new source input
  fail: >-
    return the exact edge trace/amplitude functional whose rate is still missing
  zero_consistent: INCONCLUSIVE

CANDIDATE_REREPRESENTATIONS:
  R_EDGE_FLUX_AVERAGE:
    description: >-
      Write F(y)=(lambda^2-y^2)delta'(y) and use the exact defect ODE plus
      F(lambda-)=0. Estimate the top-lattice contribution after the u-to-y
      cell change of variables. This preserves averaging and may avoid any
      derivative sup norm.
    kill_power: 10/10
    cost: 4/10
  R_EDGE_VALUE_TRACE:
    description: >-
      If the derivative really must be pointwise, derive the exact endpoint
      derivative/value relation from the Ferrers ODE and endpoint-convergent
      Legendre derivative row. Translate the proposed O(lambda^-1/2) slope
      into the corresponding stronger edge-value rate and test that rate
      against the committed source/asymptotic data before sourcing it.
    kill_power: 9/10
    cost: 3/10

FORBIDDEN:
  - infer a quantitative derivative sup-rate from zero-flux alone
  - infer edge slope O(lambda^-1/2) from the uniform C0 O(lambda^-2) rate
  - reintroduce whole-window unweighted L2 as a required consumer
  - hide the uppermost lattice point inside a divergent companion-factor estimate
  - source a Fuchs/Ferrers turning-point derivative estimate without an exact source lock
  - treat a sufficient edge condition as necessary

PREDICTIONS:
  P_DERIV_STURM_1:
    fate: CONFIRMED
  P_EDGE_CONSUMER_1:
    probability: 0.76
    prediction: >-
      The exact top-lattice contribution admits a strictly weaker averaged
      flux/trace formulation than the proposed sliver sup-norm.
    fate: UNTESTED
  P_EDGE_SUP_1:
    probability: 0.63
    prediction: >-
      The proposed O(lambda^-1/2) sliver sup-rate is not derivable from the
      currently committed C0 + zero-flux data without an additional edge
      asymptotic or an exact endpoint-amplitude improvement.
    fate: UNTESTED

ARSENAL_MANDATE: ACCEPTED_NO_LIVE_SIDECAR_MUTATION
CARDS_APPLIED:
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

CLOSES:
  - STURM_NODE_ORDER_FORK
  - UNWEIGHTED_L2_AS_REQUIRED_DERIVATIVE_CONSUMER
  - EDGE_SLIVER_SUP_NORM_AS_PREMATURE_NAMED_SUPPLIER
OPENS: []
CARRIES_OPEN:
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BOUNDED

NEXT_LOAD_BEARING_GAP: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BOUNDED
DISCRIMINATOR: EDGE_TOP_BUDGET_FROM_ZERO_FLUX_ODE_AND_C0

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: CONSUMER_STRENGTH_REDUCTION
ROUTE_SCORE: 5
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
RH_CLAIM: false
```

## ROUTE MAP

The Sturm preflight is productive. The exact defect equation inherits the degenerate prolate weight, and this makes the boundary flux disappear at the form level. The cylinder-potential sign localizes the adverse potential to a fixed core, while the F72.3B eigenvalue defect and the explicit cylinder transport both enter at the required scale. The correct analytic output is therefore the weighted derivative energy, not the stronger unweighted H1 norm.

The proposed three Lean nodes preserve this gain. First formalize the weighted energy identity and its rate. Second isolate the explicit W-transport L1 constant. Third prove the weighted Cauchy-Schwarz consumer with the singular companion factor and the uppermost lattice point kept separate. These nodes close existing quantified statements and introduce no new analytic supplier.

The remaining sliver should not yet be named by a derivative sup norm. The repository source-locks endpoint zero-flux, but zero-flux is a statement about `(1-s^2) f'(s)`, not a quantitative bound on `f'`. In physical coordinates the exact ODE retains the large shifted Jacobi parameter. Thus the existing C0 approximation cannot by itself certify `sup |delta'| <= C/sqrt(lambda)` on the final sliver.

The consumer needs less: only the actual top-lattice contribution to the W5 derivative comb must be bounded. Keep that integral as the single open quantity. The first attack should preserve its averaging by writing the weighted flux through the exact ODE and changing variables cell-by-cell. Only if this fails should the route ask for an endpoint trace or turning-point asymptotic.

## STRONGEST ATTACK

The strongest attack on the weighted repair is the top lattice point itself. Weighted energy degenerates exactly where that point approaches the physical edge, so a naive companion-factor estimate diverges. The repair is not to assume a global or sliver sup bound prematurely; it is to isolate the exact top-point functional and test whether zero-flux plus the defect ODE controls its averaged contribution. If that test fails, the returned edge trace becomes the true supplier.

## META CLOSEOUT

The derivative wall has shrunk from a whole-window C1 problem to one edge consumer. The H part is unconditional, the bulk defect energy is structurally controlled, and the remaining uncertainty is localized at the uppermost lattice point. No route promotion or RH claim follows.