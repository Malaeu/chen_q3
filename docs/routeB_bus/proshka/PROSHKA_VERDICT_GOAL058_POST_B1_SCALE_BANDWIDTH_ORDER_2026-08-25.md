# STATUS: CONDITIONAL — CLOSE SOURCE SCALE AND BANDWIDTH TOGETHER BEFORE RETURNING TO THE W5 DERIVATIVE
```yaml
PRIMARY: G6_S2_D0_SELECTED_FERRERS_FIRST_ORDER_BUDGET_WITH_DERIVED_SCALE_AND_BANDWIDTH
OPERATIVE_CLASS: TRY_REMOVE_HSCALE_AND_HBANDWIDTH_AS_SEPARATE_INPUTS

SOURCE_LOCK:
  MIDPOINT_DELTA_COMMIT: 26d0449f
  B1_APPLICATION_COMMIT: 23c6b4bd60bc55a6513974c79aed54f4881de931
  GENERIC_RECEIVER_COMMIT: 1d9caa755fe47585566627e992e4c4b4f4268f96
  COEFFICIENT_CROSSWALK_COMMIT: c082e0702475485f28118e61f6f3f65871218af1
  PREANCHOR_SCHEDULE_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPreAnchorDataInhabitant.lean
  PREANCHOR_SCHEDULE: m_eq_N_eq_k_plus_2
  SCALE_DEF_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersZeroMassCylinderPacket.lean
  PORT_SCALE_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFactorFourPortRate.lean

GREEN_ADMISSION:
  midpoint_delta: REPORTED_KERNEL_GREEN
  b1_application: REPORTED_KERNEL_GREEN
  P_MIDPOINT_1: CONFIRMED
  P_FAMILY_B1_1: CONFIRMED

CURRENT_APPLICATION_INPUTS:
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_6_MODE_AND_CHI_RATE_INPUTS
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED
  - SOURCE_SCALE_INVERSE_BOUNDED
  - SELECTED_PHYSICAL_BANDWIDTH_COFINAL

ADJUDICATION:
  SOURCE_SCALE_INVERSE_BOUNDED_AS_OWNER_INPUT: REJECTED_PREMATURE
  SELECTED_PHYSICAL_BANDWIDTH_COFINAL_AS_INDEPENDENT_INPUT_AFTER_HFAMILY: REJECTED_PREMATURE
  W5_LOG_DERIVATIVE_BUDGET_BOUNDED_AS_NEXT_STEP: HOLD_ONE_NODE
  SELECTED_NEXT_NODE: DERIVE_HSCALE_AND_HBANDWIDTH_AND_REAPPLY_EXISTING_CHAIN

WHY:
  hScale: >-
    The source scale is not free OWNER_DATA. It is an explicit function of the
    center anchors and the ProlatePair normalizing denominator. The committed
    F72.6 mode/chi hypotheses plus the exact unit-L2 normalization of the selected
    Ferrers modes are sufficient to seek an eventual lower bound on the scale.
    Therefore bounded inverse scale must be tested as a theorem consequence before
    it is promoted to an owner contract.
  hBandwidth: >-
    Bare PairCofinal is insufficient because independent m->infinity and N->infinity
    do not imply (N+1)/log(m)->infinity. But the already-selected b1 family contract
    eventually identifies the production PairIndex with selectedFerrersPreAnchorIndex,
    whose exact precommitted schedule is m=N=k+2. On that schedule physical bandwidth
    is 2*pi*(k+3)/log(k+2), hence cofinality is pure arithmetic and should be derived
    inside the application chain rather than carried as a separate supplier.

PREFERRED_HSCALE_PROOF_ROUTE:
  step_1: >-
    Use the mode-zero F72.6 approximation on one fixed compact interval J around 0,
    where D0(projectCylinderArgument x)=exp(-pi*x^2) has a fixed positive lower bound.
  step_2: >-
    The selected mode-zero physical Ferrers mode has exact whole-line unit L2 mass.
    Therefore if |centerAnchorScalarZero*k*h0 - D0| <= C0/lambda^2 uniformly on J,
    then eventually the L2 mass of centerAnchorScalarZero*h0 on J is bounded below,
    hence |centerAnchorScalarZero k| has an eventual positive lower bound.
  step_3: >-
    Since centerAnchorScalarZero=1/h0(0), the selected center value h0(0) is eventually
    bounded above. The chi2 defect gives an eventual positive lower bound on chi2.
  step_4: >-
    Rewrite selectedFerrersLemma73SourceScale = 4*selectedFerrersLemma72Scale and
    selectedFerrersLemma72Scale = -((a0*a4)/16)*normalizingDenominator. Using
    I4=chi2*h4(0) and normalizingDenominator>=|I4|, cancel the mode-four center factor
    and bound |scale^{-1}| by a constant multiple of |h0(0)|/|chi2|.
  target: SOURCE_SCALE_INVERSE_BOUNDED
  new_analytic_supplier: none

ALTERNATE_HSCALE_ROUTE:
  description: >-
    Prove exact unit-L2 mass of the selected prolateCombination and use the F72.6
    packet rate to lower-bound |selectedFerrersLemma73SourceScale| by comparison with
    the fixed nonzero L2 mass of 4*explicitCCMLimitH on a fixed compact interval.
  status: RUNNER_UP
  kill_power: 9/10
  cost: 4/10

HBANDWIDTH_ROUTE:
  from_hFamily: >-
    eventually selectedPairIndex S k = selectedFerrersPreAnchorIndex k
  exact_schedule: selectedFerrersPreAnchorIndex k = PairIndex(m=k+2,N=k+2)
  bandwidth_formula: 2*pi*(k+3)/log(k+2)
  target: SelectedPhysicalBandwidthCofinal S
  verifier_class: PURE_ANALYTIC_ARITHMETIC_NO_NEW_ROUTE_INPUT

PUBLIC_TARGET:
  preferred_name: selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget_closedScaleBandwidth
  inputs:
    - S : ProlateCanonicalSourceData
    - hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S
    - existing F72.6 mode/chi hypotheses
    - hD : W5_LOG_DERIVATIVE_BUDGET_BOUNDED
  conclusion: SelectedProjectionTailDecay S
  proof_route:
    - derive SOURCE_SCALE_INVERSE_BOUNDED from committed F72.6 plus exact L2 normalization
    - derive SelectedPhysicalBandwidthCofinal S from hFamily plus m=N=k+2
    - invoke selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget
  forbidden:
    - add hScale to OWNER_DATA without first falsifying the derivation above
    - infer bandwidth cofinality from PairCofinal alone
    - construct a second production S
    - weaken the downstream consumer

CLOSES:
  - SOURCE_SCALE_INVERSE_BOUNDED_AS_SEPARATE_INPUT
  - SELECTED_PHYSICAL_BANDWIDTH_COFINAL_AS_SEPARATE_INPUT_ON_B1_PATH
OPENS: []

CARRIES_OPEN_AFTER_SUCCESS:
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_6_MODE_AND_CHI_RATE_INPUTS
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED

NEXT_LOAD_BEARING_GAP_AFTER_SUCCESS: W5_LOG_DERIVATIVE_BUDGET_BOUNDED

REGISTERED_PREDICTIONS:
  P_SCALE_1:
    probability: 0.84
    prediction: >-
      SOURCE_SCALE_INVERSE_BOUNDED follows from the existing mode-zero F72.6
      uniform rate, exact unit-L2 normalization of the selected physical mode,
      and the chi2 defect rate, with no new owner or paper input.
    fate: UNTESTED
  P_BANDWIDTH_1:
    probability: 0.97
    prediction: >-
      Under the already-ratified hFamily equality, SelectedPhysicalBandwidthCofinal
      is an arithmetic consequence of selectedFerrersPreAnchorIndex having m=N=k+2.
    fate: UNTESTED
  P_ORDER_1:
    probability: 0.90
    prediction: >-
      Closing scale and bandwidth first removes two bookkeeping inputs at lower cost
      than attacking the derivative wall and leaves W5_LOG_DERIVATIVE_BUDGET_BOUNDED
      as the unique non-owner analytic gap in this projection-tail chain.
    fate: UNTESTED

ARSENAL_MANDATE: ACCEPTED_NO_LIVE_SIDECAR_MUTATION
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT

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

The two new kernel-green nodes materially change the frontier. The midpoint correction is no longer open, and the b1 application theorem already reaches the exact production consumer. Its two new non-owner inputs, `SOURCE_SCALE_INVERSE_BOUNDED` and `SelectedPhysicalBandwidthCofinal`, should not be frozen as independent assumptions yet.

The bandwidth input is the clearer case. `CanonicalData.parentCofinal` alone is too weak: independent divergence of `m` and `N` does not control their ratio. But b1 already assumes eventual equality with the Ferrers pre-anchor index, and that index is source-locked to `m=N=k+2`. Therefore the production bandwidth on the b1 path is eventually the explicit sequence `2*pi*(k+3)/log(k+2)`, which tends to infinity.

The scale input is also source-derived. The port scale is `4*selectedFerrersLemma72Scale`; the inner scale is the explicit product of the two center anchors and the positive normalizing denominator. The selected Ferrers modes are exactly unit-L2 normalized. The F72.6 mode-zero approximation is uniform with error `O(lambda^-2)` on the expanding source window. Restricting it to any fixed interval on which the D0 cylinder target has positive L2 mass forces the mode-zero anchor to stay away from zero. The chi defect then prevents the relevant finite-Fourier scalar from approaching zero. These facts are enough to attempt an eventual inverse-scale bound without any new source assumption.

## FINAL PROPOSAL

Take one theorem-sized node whose public conclusion is again `SelectedProjectionTailDecay S`, but whose public inputs omit both `hScale` and `hBandwidth`. Prove those two facts privately from the already-ratified b1 family equality, F72.6 inputs, the fixed pre-anchor schedule, and the exact physical-mode normalization, then call the existing green application theorem from commit `23c6b4bd`.

Do not attack `W5_LOG_DERIVATIVE_BUDGET_BOUNDED` until this node is tried. If the scale derivation fails at an exact named inequality, return that inequality as the new discriminator; only then decide whether scale belongs in OWNER_DATA or whether a weaker coupled scale/bandwidth rate should replace bounded inverse scale.

## STRONGEST ATTACK

The dangerous shortcut is to infer `SelectedPhysicalBandwidthCofinal` from generic `PairCofinal`; that implication is false without a relation between `m` and `N`. The b1 equality to the pre-anchor schedule is what repairs it. For the scale, mere nonvanishing is not enough: the proof must produce an eventual quantitative lower bound on the scale, not just reuse `selectedFerrersLemma73SourceScale_ne`.

## META CLOSEOUT

The b1 chain now has one owner/source identity and three analytic families. Two of the latter appear reducible to existing structure. The correct next action is therefore to eliminate those structural inputs before returning to the derivative wall.