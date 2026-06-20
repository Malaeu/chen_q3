# Step33A.1-A Sub0 OmegaPrime Taylor Payload

Fail-closed payload surface. This is not Lean proof data and does
not close Step33A.1-A.

## Status

- schema: `q3_psdpd_step33_a1_sub0_omega_prime_taylor_payload.v6`
- route: `STEP33_A1_SUB0_OMEGA_PRIME_TAYLOR_PAYLOAD`
- status: `fail_closed_missing_order16_polygamma_bound`
- first failure: `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP`
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
- reflected derivative theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_reflected_iteratedDeriv`
- Taylor exact-poly theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.taylorWithinEval_eq_exactTaylorPoly`
- reflected Taylor exact-poly theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.reflectedTaylorWithinEval_eq_exactTaylorPoly`
- status: `receiver_and_centered_taylor_bridge_present_missing_payload`

```text
theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound {data : Step33Sub0OmegaPrimeTaylorRemainderCert} (h : data.Valid) : forall eta in Set.Icc 0 (1/10), norm (step22OmegaArchWeightDerivClosedForm eta - data.poly eta) <= data.remainderAbs
```

Next constructor surface:

```text
theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound (data : Step33Sub0OmegaPrimeTaylorRemainderCert) (hSmooth : ContDiff Real 16 step22OmegaArchWeightDerivClosedForm) (hCenterJet : center coefficient enclosures) (hOrder16 : forall eta in [0,1/10], norm (iteratedDeriv 16 step22OmegaArchWeightDerivClosedForm eta) <= data.order16Abs) (hBudget : coefficient plus Lagrange budget <= data.remainderAbs) : data.Valid
```

Normalization note:

`rawOmegaATaylorPolynomial expects a Rat center and a Fin (degree + 1) -> Rat coefficient function.`

## Required Fields

- `coeff[0..15]`
- `coeffErrorAbs[0..15]`
- `order16Abs`
- `coefficientErrorBudget`
- `lagrangeRemainderBudget`
- `remainderAbs`
- `centerJetSource[0..15]`
- `order16BoundSource`
- `exactRationalChecksPassed`
- `sourceDefinitionHashes`
- `proofSafeClosedFields`
- `outLeanWritten`
- `failureCodes[]`

## Required Proofs

- already proved locally: the full centered Taylor bridge centerTaylorBridge_of_order16_bound from a uniform order-16 bound on [0, 1/10]
- already proved locally: the left reflected Lagrange bridge centerTaylorBridge_left_of_order16_bound and the reflected Taylor polynomial normalization
- already proved locally: the right-half Lagrange bridge centerTaylorBridge_right_of_order16_bound with the sharp 16! denominator on eta in [1/20, 1/10]
- already proved locally: taylorWithinEval agrees with exactTaylorPoly under UniqueDiffOn and global ContDiff 16
- already proved locally: reflected iterated derivative identity iteratedDeriv n (fun x => f (1/10 - x)) x = (-1)^n * iteratedDeriv n f (1/10 - x)
- for each j < 16, prove |iteratedDeriv j step22OmegaArchWeightDerivClosedForm (1/20) / j! - coeff[j]| <= coeffErrorAbs[j]
- prove forall eta in [0, 1/10], |iteratedDeriv 16 step22OmegaArchWeightDerivClosedForm eta| <= order16Abs
- prove sum_j coeffErrorAbs[j] * radius^j + order16Abs * radius^16 / 16! <= remainderAbs

## Local Source Scan


### Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean

| symbol | line | status |
| --- | --- | --- |
| `rawOmegaATaylorPolynomial` | `30` | `found` |
| `digamma_analyticAt_of_re_pos` | `6446` | `found` |
| `trigamma_differentiableAt_of_re_pos` | `6470` | `found` |
| `step22OmegaArchWeightDerivClosedForm` | `6440` | `found` |
| `step22OmegaArchWeightDerivClosedForm_differentiableAt` | `6485` | `found` |
| `step22OmegaArchWeight_deriv_eq_closedForm` | `8438` | `found` |
| `Step22OmegaClosedFormEndpointBoundsCert` | `8568` | `found` |
| `ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound` | `12197` | `found` |

### Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean

| symbol | line | status |
| --- | --- | --- |
| `step33_shift16_digamma_m6_integral_remainder_bound` | `841` | `found` |
| `Q3.digammaM6IntegralRemainderBound` | `842` | `found` |

## Target Symbol Scan

| symbol | line | status |
| --- | --- | --- |
| `Step33Sub0OmegaPrimeTaylorRemainderCert` | `9633` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid` | `10061` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound` | `10190` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_of_order16_bound` | `10043` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_left_of_order16_bound` | `9903` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_right_of_order16_bound` | `9802` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound` | `10090` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeClosedForm_reflected_iteratedDeriv` | `9646` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.taylorWithinEval_eq_exactTaylorPoly` | `9675` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.reflectedTaylorWithinEval_eq_exactTaylorPoly` | `9751` | `found` |
| `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_CENTERED_TAYLOR_LAGRANGE_SPLIT_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_LEFT_REFLECTED_LAGRANGE_BRIDGE_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_TAYLOR_WITHINEVAL_EXACT_POLY_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_RIGHT_LAGRANGE_BRIDGE_GAP` | `None` | `gap` |

## Proof Status

- componentTaylorBoundsProved: `False`
- centeredTaylorBridgeProved: `True`
- centeredTaylorRightBridgeProved: `True`
- centeredTaylorLeftReflectedBridgeProved: `True`
- validOfOrder16ConstructorProved: `True`
- taylorWithinEvalExactPolyBridgeProved: `True`
- reflectedTaylorWithinEvalExactPolyBridgeProved: `True`
- reflectedIteratedDerivBridgeProved: `True`
- omegaPrimeCenterJetBoundsProved: `False`
- omegaPrimeOrder16BoundProved: `False`
- omegaPrimeRemainderBudgetPassed: `False`
- exactRationalChecksPassed: `False`
- proofSafeClosedFields: `0`
- outLeanWritten: `False`

## Failure Codes

- `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP`
- `STEP33_A1_SUB0_CENTERED_TAYLOR_LAGRANGE_SPLIT_GAP`
- `STEP33_A1_SUB0_LEFT_REFLECTED_LAGRANGE_BRIDGE_GAP`
- `STEP33_A1_SUB0_TAYLOR_WITHINEVAL_EXACT_POLY_GAP`
- `STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP`
- `STEP33_A1_SUB0_RIGHT_LAGRANGE_BRIDGE_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SOURCE_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_TAYLOR_LEAN_PAYLOAD_MISSING`

## Decision

The centered Taylor bridge from a uniform order-16 bound is now
proved locally, including right-half and reflected left-half
Lagrange bridges plus the `Valid.of_order16_bound` constructor.
The next proof-producing step is the proof-grade order-16
polygamma bound together with center-jet coefficient enclosures
and the exact rational remainder budget.

Until those payload fields exist locally, the correct fail code is:

```text
STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP
```
