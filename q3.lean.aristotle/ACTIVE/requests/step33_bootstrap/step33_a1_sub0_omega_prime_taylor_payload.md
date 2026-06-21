# Step33A.1-A Sub0 OmegaPrime Taylor Payload

Fail-closed payload surface. This is not Lean proof data and does
not close Step33A.1-A.

## Status

- schema: `q3_psdpd_step33_a1_sub0_omega_prime_taylor_payload.v7`
- route: `STEP33_A1_SUB0_OMEGA_PRIME_TAYLOR_PAYLOAD`
- status: `fail_closed_missing_center_jet_payload`
- first failure: `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP`
- receiver schema current: `True`
- function: `step22OmegaArchWeightDerivClosedForm`
- center: `1/20`
- radius: `1/20`
- degree: `15`
- proof-safe closed fields: `0`
- Lean emitted: `False`

## Target Lean Surface

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean`
- structure: `Step33Sub0OmegaPrimeTaylorRemainderCert`
- valid predicate: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid`
- bound theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound`
- centered bridge theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_of_order16_bound`
- left bridge theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_left_of_order16_bound`
- right bridge theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_right_of_order16_bound`
- valid constructor: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound`
- OmegaPrime smoothness theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_contDiff16`
- checked-smooth valid constructor: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound_checked_smooth`
- active payload receiver: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_integer_budget_checked_deriv`
- receiver checked: `True`
- old receiver rejected for new payloads: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound_checked_smooth`
- reflected derivative theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_reflected_iteratedDeriv`
- Taylor exact-poly theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.taylorWithinEval_eq_exactTaylorPoly`
- reflected Taylor exact-poly theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.reflectedTaylorWithinEval_eq_exactTaylorPoly`
- status: `receiver_checked_deriv_present_missing_concrete_payload`

```text
theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound {data : Step33Sub0OmegaPrimeTaylorRemainderCert} (h : data.Valid) : forall eta in Set.Icc 0 (1/10), norm (step22OmegaArchWeightDerivClosedForm eta - data.poly eta) <= data.remainderAbs
```

Next constructor surface:

```text
theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_integer_budget_checked_deriv (data : Step33Sub0OmegaPrimeTaylorRemainderCert) (hCoeffErrorNonneg : forall j, 0 <= data.coeffErrorAbs j) (hCenterJet : center coefficient enclosures) (hIntegerBudget : omegaPrimeOrder16CondensedFactorBudgetBound <= data.order16Abs) (hRemainderBudget : coefficient plus Lagrange budget <= data.remainderAbs) : data.Valid
```

Normalization note:

`rawOmegaATaylorPolynomial expects a Rat center and a Fin (degree + 1) -> Rat coefficient function.`

## Required Fields

- `coeff[0..15]`
- `coeffErrorAbs[0..15]`
- `centerJet[0..15].{coeff,coeffErrorAbs,lower,upper,sourceLeanTheorem,sourceLeanChecked,lowerCheckPassed,upperCheckPassed,enclosurePassed}`
- `order16Abs`
- `order16.{condensedFactorBudgetBoundExact,order16Abs,marginExact,integerBudgetPassed,sourceLeanTheorems,sourceLeanChecked}`
- `remainder.{coeffErrorContributionExact,lagrangeContributionExact,requiredTotalExact,remainderAbs,marginExact,budgetPassed}`
- `remainderAbs`
- `centerJetSource[0..15]`
- `integerBudgetSource`
- `exactRationalChecksPassed`
- `sourceDefinitionHashes`
- `allCenterJetsProved`
- `allPayloadObligationsPassed`
- `leanOutputPath`
- `leanValidationStatus`
- `proofSafeClosedFields`
- `outLeanWritten`
- `failureCodes[]`

## Required Proofs

- already proved locally: the full centered Taylor bridge centerTaylorBridge_of_order16_bound from a uniform order-16 bound on [0, 1/10]
- already proved locally: the left reflected Lagrange bridge centerTaylorBridge_left_of_order16_bound and the reflected Taylor polynomial normalization
- already proved locally: the right-half Lagrange bridge centerTaylorBridge_right_of_order16_bound with the sharp 16! denominator on eta in [1/20, 1/10]
- already proved locally: taylorWithinEval agrees with exactTaylorPoly under UniqueDiffOn and global ContDiff 16
- already proved locally: reflected iterated derivative identity iteratedDeriv n (fun x => f (1/10 - x)) x = (-1)^n * iteratedDeriv n f (1/10 - x)
- already proved locally: trigamma is analytic in the right half-plane and step22OmegaArchWeightDerivClosedForm is ContDiff Real 16
- already proved locally: Valid.of_order16_integer_budget_checked_deriv uses omegaPrimeClosedForm_iteratedDeriv16_eq, so generated payloads no longer need to supply hSmooth or hDerivEq
- for each j < 16, prove 0 <= coeffErrorAbs[j]
- for each j < 16, prove |iteratedDeriv j omegaPrimeClosedForm (1/20) / j! - coeff[j]| <= coeffErrorAbs[j]
- prove omegaPrimeOrder16CondensedFactorBudgetBound <= order16Abs
- prove sum_j coeffErrorAbs[j] * radius^j + order16Abs * radius^16 / 16! <= remainderAbs

## Local Source Scan


### Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean

| symbol | line | status |
| --- | --- | --- |
| `rawOmegaATaylorPolynomial` | `30` | `found` |
| `digamma_analyticAt_of_re_pos` | `6446` | `found` |
| `trigamma_differentiableAt_of_re_pos` | `6470` | `found` |
| `trigamma_analyticAt_of_re_pos` | `6484` | `found` |
| `step22OmegaArchWeightDerivClosedForm` | `6440` | `found` |
| `step22OmegaArchWeightDerivClosedForm_differentiableAt` | `6499` | `found` |
| `step22OmegaArchWeightDerivClosedForm_contDiff16` | `6532` | `found` |
| `step22OmegaArchWeight_deriv_eq_closedForm` | `8493` | `found` |
| `Step22OmegaClosedFormEndpointBoundsCert` | `8623` | `found` |
| `ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound` | `12252` | `found` |

### Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean

| symbol | line | status |
| --- | --- | --- |
| `step33_shift16_digamma_m6_integral_remainder_bound` | `842` | `found` |
| `Q3.digammaM6IntegralRemainderBound` | `843` | `found` |

## Target Symbol Scan

| symbol | line | status |
| --- | --- | --- |
| `Step33Sub0OmegaPrimeTaylorRemainderCert` | `9634` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid` | `10069` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound` | `11463` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_of_order16_bound` | `10051` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_left_of_order16_bound` | `9911` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_right_of_order16_bound` | `9810` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound` | `10098` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_contDiff16` | `9647` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound_checked_smooth` | `10132` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_integer_budget_checked_deriv` | `11370` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_reflected_iteratedDeriv` | `9654` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.taylorWithinEval_eq_exactTaylorPoly` | `9683` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.reflectedTaylorWithinEval_eq_exactTaylorPoly` | `9759` | `found` |
| `STEP33_A1_SUB0_OMEGAPRIME_STALE_RECEIVER_SCHEMA_FAIL` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_INTEGER_BUDGET_PAYLOAD_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_PAYLOAD_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_CENTERED_TAYLOR_LAGRANGE_SPLIT_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_LEFT_REFLECTED_LAGRANGE_BRIDGE_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_TAYLOR_WITHINEVAL_EXACT_POLY_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_RIGHT_LAGRANGE_BRIDGE_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP` | `None` | `gap` |

## Proof Status

- componentTaylorBoundsProved: `False`
- centeredTaylorBridgeProved: `True`
- centeredTaylorRightBridgeProved: `True`
- centeredTaylorLeftReflectedBridgeProved: `True`
- validOfOrder16ConstructorProved: `True`
- taylorWithinEvalExactPolyBridgeProved: `True`
- reflectedTaylorWithinEvalExactPolyBridgeProved: `True`
- reflectedIteratedDerivBridgeProved: `True`
- omegaPrimeAnalyticSmoothnessProved: `True`
- validCheckedSmoothConstructorProved: `True`
- omegaPrimeHDerivEqProved: `True`
- validIntegerBudgetCheckedDerivConstructorProved: `True`
- omegaPrimeOrder16AnalyticBoundReducedToIntegerBudget: `True`
- omegaPrimeCenterJetBoundsProved: `False`
- omegaPrimeOrder16BoundProved: `False`
- omegaPrimeOrder16IntegerBudgetProved: `False`
- omegaPrimeRemainderBudgetPassed: `False`
- exactRationalChecksPassed: `False`
- allCenterJetsProved: `False`
- allPayloadObligationsPassed: `False`
- leanValidationStatus: `not_run`
- proofSafeClosedFields: `0`
- outLeanWritten: `False`

## Failure Codes

- `STEP33_A1_SUB0_OMEGAPRIME_STALE_RECEIVER_SCHEMA_FAIL`
- `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_INTEGER_BUDGET_PAYLOAD_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_PAYLOAD_GAP`

## Closed Historical Failures

- `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP`
- `STEP33_A1_SUB0_CENTERED_TAYLOR_LAGRANGE_SPLIT_GAP`
- `STEP33_A1_SUB0_LEFT_REFLECTED_LAGRANGE_BRIDGE_GAP`
- `STEP33_A1_SUB0_TAYLOR_WITHINEVAL_EXACT_POLY_GAP`
- `STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP`
- `STEP33_A1_SUB0_RIGHT_LAGRANGE_BRIDGE_GAP`

## Decision

The checked-deriv receiver is now the active Lean surface:
`Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_integer_budget_checked_deriv`.
The old order-16 polygamma failure is historical, not the active
payload blocker. The next proof-producing step is a concrete
`Step33Sub0OmegaPrimeTaylorRemainderCert` payload with center-jet
coefficient enclosures, the integer order-16 budget, and the exact
rational Taylor remainder budget.

Until those payload fields exist locally, the correct fail code is:

```text
STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP
```
