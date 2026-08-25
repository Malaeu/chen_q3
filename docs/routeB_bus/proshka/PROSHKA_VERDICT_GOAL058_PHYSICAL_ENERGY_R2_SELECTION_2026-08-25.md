# STATUS: CONDITIONAL — SELECT R2 COEFFICIENT-SIDE PROLATE ODE; DO NOT REPAIR THE LITERAL JUMPED REPRESENTATIVE
```yaml
PRIMARY: SELECT_R2_COEFFICIENT_SIDE_PROLATE_ODE
OPERATIVE_CLASS: PHYSICAL_ENERGY_SOURCE_SUPPLIER_REPRESENTATION_SHIFT

SOURCE_LOCK:
  JUMP_DISCRIMINATOR_COMMIT: 3e22c1001bbbe7fc8faf946937123a707106ba2d
  PRIOR_W4_EDGE_VERDICT_COMMIT: 461f259e1526dfb30ce423c39d26d0cae21e49c5
  JUMP_STATUS: NOT_PROVED_ZERO
  ENDPOINT_ZERO_SUPPLIER: NOT_AVAILABLE
  NONVANISHING_PROVED: false

DECISION:
  R1_PERIODIC_H1_PARSEVAL: HOLD_DEPENDS_ON_EXACT_ZERO_TRACES
  R2_COEFFICIENT_SIDE_PROLATE_ODE: SELECTED_PRIMARY
  R3_SEAM_FREE_REPRESENTATIVE_REPAIR: REJECT_AS_PRIMARY_C10_RISK
  R4_REVISE_PHYSICAL_ENERGY_WEIGHTS: REJECT_WITHOUT_CONSUMER_REDESIGN
  SOURCE_EDGE_VALUE_QUERY: PARALLEL_NONBLOCKING_CHECK_ONLY

REASON: >-
  The literal physical-energy contract requires per-k summability with an n^2
  weight. The production representative carries internal and periodic trace
  defects unless exact endpoint cancellation is supplied. Smallness does not
  imply zero. R2 attacks the exact coefficient row directly through the
  prolate differential equation/recurrence and therefore survives whether the
  endpoint value is zero, nonzero, or merely unresolved.

EXACT_CONSUMER:
  contract: SelectedPhysicalFourierEnergyControl
  first_conjunct: per_k_summability_of_physical_n_squared_weighted_coefficients
  second_conjunct: eventual_boundedness_of_selectedPhysicalFourierEnergy

NEXT_TARGET:
  name: G6_S2_D0_SELECTED_PROLATE_PHYSICAL_FOURIER_ENERGY_SOURCE_SUPPLIER_R2
  theorem_shape: >-
    Prove directly for the literal full gTrial_m family that the physical
    Fourier coefficient row is summable for every selected k and that the
    resulting physicalFourierEnergy family is eventually bounded, using the
    exact prolate ODE / coefficient recurrence rather than periodic-H1 of the
    jumped log representative.

FIRST_R2_SUBTARGET:
  name: PHYSICAL_FOURIER_COEFFICIENT_WEIGHTED_RECURRENCE
  required_output: >-
    An exact coefficient-side identity or inequality strong enough to control
    sum_n abs(2*pi*n/L_m)^2 * norm(inner(V_n_m,n,gTrial_m))^2, with all boundary
    terms explicit and no assumption that the production seams vanish.
  forbidden:
    - infer endpoint cancellation from asymptotic smallness
    - replace the literal coefficient row by a seam-free surrogate without an exact consumer-preserving map
    - infer n^2-energy from the logarithmic shifted-archimedean form
    - weaken SelectedPhysicalFourierEnergyControl by changing its weight

SOURCE_QUERY:
  question: do the selected even Ferrers/prolate modes vanish at the physical window edge
  role: PARALLEL_DISCRIMINATOR_ONLY
  blocking: false
  consequence_if_yes: reopens R1 as cheaper cross-check
  consequence_if_no_or_absent: R2 unchanged

CANDIDATE_REREPRESENTATIONS:
  R2A_ODE_TO_FOURIER_COEFFICIENT_RECURRENCE:
    kill_power: 10/10
    cost: 5/10
  R2B_WEAK_DERIVATIVE_FORM_ON_MULTIPLICATIVE_WINDOW:
    kill_power: 8/10
    cost: 6/10
    note: use only if it controls the exact V_n_m coefficient functional without periodic trace assumptions

DISCRIMINATOR:
  name: R2_EXACT_N2_WEIGHTED_COEFFICIENT_IDENTITY
  pass: exact identity/one-sided bound on the literal coefficient row closes per-k summability without zero-seam hypotheses
  fail: ODE route produces only an unweighted/L2 or logarithmically weighted coefficient control
  zero_consistent: INCONCLUSIVE

REGISTERED_PREDICTIONS:
  P_PHYS_R2_1:
    probability: 0.81
    prediction: the exact prolate ODE yields a coefficient-side weighted identity before any source endpoint-zero theorem is needed
    fate: UNTESTED
  P_PHYS_R2_2:
    probability: 0.74
    prediction: any successful route will expose an explicit boundary term rather than silently imposing periodic traces
    fate: UNTESTED

ARSENAL_MANDATE: ACCEPTED_NO_LIVE_SIDECAR_MUTATION
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

CLOSES:
  - PHYSICAL_ENERGY_ROUTE_FORK
OPENS: []
NEXT_LOAD_BEARING_GAP: R2_EXACT_N2_WEIGHTED_COEFFICIENT_IDENTITY

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

`3e22c100` answers the first discriminator only as `NOT_PROVED_ZERO`. The older W4 verdict `461f259e` already forbids promoting asymptotically small endpoint values to exact cancellation. Therefore R1, the periodic-H1/Parseval route, is not currently executable on the literal production representative.

Changing the representative to remove seams is not a neutral repair. `SelectedPhysicalFourierEnergyControl` is a contract on the literal full `gTrial_m` coefficient row, so a seam-free replacement must first come with an exact consumer-preserving map. Without that map it is a C10 surrogate and is rejected as the primary move.

Revising the `n^2` weights would change the consumer contract rather than prove it. That is a route redesign, not a supplier theorem, and is not authorized by the present evidence.

R2 is selected because it is invariant under all three unresolved endpoint possibilities. The next theorem must act directly on the coefficients `inner(V_n_m i n, gTrial_m ...)` and derive the exact `n^2`-weighted summability/boundedness consumed by `SelectedPhysicalFourierEnergyControl` from the prolate ODE or its coefficient recurrence.

## FINAL PROPOSAL

Take one theorem-sized R2 preflight before writing Lean: derive the exact Fourier-coefficient recurrence obtained by pairing the prolate differential equation with `V_n_m`. Keep every integration-by-parts boundary term explicit. The first acceptable output is an identity or one-sided estimate that controls

\[
\sum_{n\in\mathbb Z}\left|\frac{2\pi n}{L_m}\right|^2 |\langle V_n,gTrial_m\rangle|^2.
\]

If the ODE pairing yields only unweighted `L2` control or a logarithmic weight, report `R2_N2_WEIGHTED_COEFFICIENT_IDENTITY_GAP`; do not compensate by changing the consumer.

The first-source endpoint question may be asked in parallel because it is cheap and could reopen R1, but it is not allowed to block R2.

## STRONGEST ATTACK

R2 can fail if the exact ODE-to-Fourier integration by parts inherits the same boundary traces that killed periodic H1. That is why the first subtarget is the exact coefficient identity, not an assumed recurrence. Boundary terms must be carried explicitly. If they cannot be controlled at the required `n^2` scale, R2 is genuinely blocked and the contract itself must be revisited.

## META CLOSEOUT

The fork is closed without assuming either endpoint zero or endpoint nonzero. The route moves to the one representation that survives both cases. No RH or route-promotion claim follows.