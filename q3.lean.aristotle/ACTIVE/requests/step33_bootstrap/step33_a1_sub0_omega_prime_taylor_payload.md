# Step33A.1-A Sub0 OmegaPrime Taylor Payload

Fail-closed payload surface. This is not Lean proof data and does
not close Step33A.1-A.

## Status

- schema: `q3_psdpd_step33_a1_sub0_omega_prime_taylor_payload.v2`
- route: `STEP33_A1_SUB0_OMEGA_PRIME_TAYLOR_PAYLOAD`
- status: `fail_closed_missing_centered_taylor_reflection_bridge`
- first failure: `STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP`
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
- valid constructor: `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound`
- status: `receiver_present_missing_centered_taylor_bridge`

```text
theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound {data : Step33Sub0OmegaPrimeTaylorRemainderCert} (h : data.Valid) : forall eta in Set.Icc 0 (1/10), norm (step22OmegaArchWeightDerivClosedForm eta - data.poly eta) <= data.remainderAbs
```

Next bridge surface:

```text
theorem Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_of_order16_bound (data : Step33Sub0OmegaPrimeTaylorRemainderCert) (hSmooth : ContDiff Real 16 step22OmegaArchWeightDerivClosedForm) (hCenterJet : center coefficient enclosures) (hOrder16 : forall eta in [0,1/10], norm (iteratedDeriv 16 step22OmegaArchWeightDerivClosedForm eta) <= data.order16Abs) (hBudget : coefficient plus Lagrange budget <= data.remainderAbs) : forall eta in [0,1/10], norm (step22OmegaArchWeightDerivClosedForm eta - exactTaylorPoly eta) <= data.order16Abs * radius^16 / 16!
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

- prove the centered Taylor bridge from a uniform order-16 bound: right half by taylor_mean_remainder_bound, left half by reflecting x |-> 1/10 - x
- prove the reflected iterated derivative identity iteratedDeriv n (fun x => f (1/10 - x)) x = (-1)^n * iteratedDeriv n f (1/10 - x)
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
| `step33_shift16_digamma_m6_integral_remainder_bound` | `840` | `found` |
| `Q3.digammaM6IntegralRemainderBound` | `841` | `found` |

## Target Symbol Scan

| symbol | line | status |
| --- | --- | --- |
| `Step33Sub0OmegaPrimeTaylorRemainderCert` | `9632` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid` | `9655` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound` | `9750` | `found` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.centerTaylorBridge_of_order16_bound` | `None` | `gap` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.of_order16_bound` | `None` | `gap` |
| `STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP` | `None` | `gap` |

## Proof Status

- componentTaylorBoundsProved: `False`
- centeredTaylorBridgeProved: `False`
- reflectedIteratedDerivBridgeProved: `False`
- omegaPrimeCenterJetBoundsProved: `False`
- omegaPrimeOrder16BoundProved: `False`
- omegaPrimeRemainderBudgetPassed: `False`
- exactRationalChecksPassed: `False`
- proofSafeClosedFields: `0`
- outLeanWritten: `False`

## Failure Codes

- `STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SOURCE_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_TAYLOR_LEAN_PAYLOAD_MISSING`

## Decision

The next proof-producing step is not endpoint subdivision and not
a full residual interval payload.  It is the centered Taylor
bridge from the uniform order-16 bound.  The right half can use
`taylor_mean_remainder_bound`; the left half needs a reflected
iterated-derivative bridge for `x |-> 1/10 - x` before the
order-16/polygamma payload can be spent.

Until that exists locally, the correct fail code is:

```text
STEP33_A1_SUB0_CENTERED_TAYLOR_REFLECTED_ITERATED_DERIV_GAP
```
