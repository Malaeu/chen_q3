# Step33A.1-A Sub0 OmegaPrime Taylor Payload

Fail-closed payload surface. This is not Lean proof data and does
not close Step33A.1-A.

## Status

- schema: `q3_psdpd_step33_a1_sub0_omega_prime_taylor_payload.v1`
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
- status: `planned_not_in_lean`

```text
theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound {data : Step33Sub0OmegaPrimeTaylorRemainderCert} (h : data.Valid) : forall eta in Set.Icc 0 (1/10), norm (step22OmegaArchWeightDerivClosedForm eta - data.poly eta) <= data.remainderAbs
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
| `step33_shift16_digamma_m6_integral_remainder_bound` | `837` | `found` |
| `Q3.digammaM6IntegralRemainderBound` | `838` | `found` |

## Target Symbol Scan

| symbol | line | status |
| --- | --- | --- |
| `Step33Sub0OmegaPrimeTaylorRemainderCert` | `None` | `gap` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid` | `None` | `gap` |
| `Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound` | `None` | `gap` |
| `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP` | `None` | `gap` |

## Proof Status

- componentTaylorBoundsProved: `False`
- omegaPrimeCenterJetBoundsProved: `False`
- omegaPrimeOrder16BoundProved: `False`
- omegaPrimeRemainderBudgetPassed: `False`
- exactRationalChecksPassed: `False`
- proofSafeClosedFields: `0`
- outLeanWritten: `False`

## Failure Codes

- `STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_SOURCE_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_GAP`
- `STEP33_A1_SUB0_OMEGAPRIME_TAYLOR_LEAN_PAYLOAD_MISSING`

## Decision

The next proof-producing step is not endpoint subdivision and not
a full residual interval payload.  It is a proof-grade order-16
bound plus center-jet coefficient enclosures for
`step22OmegaArchWeightDerivClosedForm` on `[0, 1/10]`.

Until that exists locally, the correct fail code is:

```text
STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP
```
