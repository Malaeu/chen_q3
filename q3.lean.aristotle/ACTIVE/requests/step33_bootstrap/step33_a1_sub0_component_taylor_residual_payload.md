# Step33A.1-A Sub0 Component Taylor Residual Payload

Fail-closed route-B payload. This is not Lean proof data and does
not close Step33A.1-A.

## Status

- schema: `q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v2`
- route: `STEP33_A1_SUB0_COMPONENT_TAYLOR_RESIDUAL`
- chosen route: `B`
- status: `fail_closed_missing_omega_shape_shapederiv_taylor_remainders`
- first failure: `STEP33_A1_SUB0_OMEGA_SHAPE_SHAPEDERIV_TAYLOR_REMAINDER_GAP`
- closed historical failures: `STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP, STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP, STEP33_A1_SUB0_OMEGAPRIME_ORDER16_INTEGER_BUDGET_PAYLOAD_GAP, STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_PAYLOAD_GAP`
- advisory source: `browser_proshka_route_advice_not_proof_evidence`
- proof-safe closed fields: `1`
- Lean emitted: `False`

## Target

- theorem: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean`
- component degree: `15`
- assembled degree: `45`
- center: `1/20`
- radius: `1/20`
- target interval: `[-94119513411/500000000000000000000000000000, 1866608532757/500000000000000000000000000000]`

```text
theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure {eta : Real} (heta : eta in Set.Icc 0 (1/10)) : norm ((RawIntegrandDerivClosedForm eta - rawOmegaATaylorPolynomial 15 (1/20) ResidualDerivmodelCoeff eta) - rawOmegaATaylorPolynomial 45 (1/20) ResidualTaylorCoeff eta) <= ResidualTaylorRemainderAbs
```

## Model Derivative Coefficients

Extracted from local Lean definition `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff`.

| i | coeff | source line |
| --- | --- | --- |
| 0 | `2814585322345983/31250000000000000` | 49 |
| 1 | `432682670395380743/250000000000000000` | 50 |
| 2 | `-2076189217694411487/1000000000000000000` | 51 |
| 3 | `-155822302127901237/12500000000000000` | 52 |
| 4 | `248352666423100477/12500000000000000` | 53 |
| 5 | `32291651785944130749/500000000000000000` | 54 |
| 6 | `-69999411432932463909/500000000000000000` | 55 |
| 7 | `-34707798540256129409/125000000000000000` | 56 |
| 8 | `836575734719049511113/1000000000000000000` | 57 |
| 9 | `100643501888413806697/100000000000000000` | 58 |
| 10 | `-897573400754971084771/200000000000000000` | 59 |
| 11 | `-142205390337268351947/50000000000000000` | 60 |
| 12 | `5554290524724778241613/250000000000000000` | 61 |
| 13 | `916884525703826724093/250000000000000000` | 62 |
| 14 | `-19999872807938988432933/200000000000000000` | 63 |
| 15 | `62148786708414316877/2500000000000000` | 64 |

## Required Component Fields

- `omegaCoeff[0..15]`
- `omegaDerivCoeff[0..15]`
- `shapeCoeff[0..15]`
- `shapeDerivCoeff[0..15]`
- `omegaRemainderAbs`
- `omegaDerivRemainderAbs`
- `shapeRemainderAbs`
- `shapeDerivRemainderAbs`
- `assembledRawDerivCoeff[0..45]`
- `residualTaylorCoeff[0..45]`
- `residualTaylorRemainderAbs`
- `residualPolynomialLower` / `residualPolynomialUpper`
- `finalResidualLower` / `finalResidualUpper`

## Component Closure Ledger

- omega: `missing_proof_grade_component_taylor_remainder`
- omegaDeriv: `formal_available_not_assembled`
- shape: `missing_proof_grade_component_taylor_remainder`
- shapeDeriv: `missing_proof_grade_component_taylor_remainder`

## OmegaDeriv Taylor Source

- proof-grade: `True`
- valid theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert_valid`
- theorem found: `True`
- payload generated valid cert proved: `True`
- coeff source: `omegaPrimePayload.generatorFields.coeff`
- remainder source: `omegaPrimePayload.generatorFields.remainder.remainderAbs`

## Component Taylor Status

- omegaDerivTaylor: `FORMAL`
- omegaDerivTaylor Lean theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert_valid`
- omegaTaylor: `MISSING_PROOF_GRADE_REMAINDER`
- shapeTaylor: `MISSING_PROOF_GRADE_REMAINDER`
- shapeDerivTaylor: `MISSING_PROOF_GRADE_REMAINDER`
- assembly Lean written: `False`
- overall proof safe: `False`

## Proof Status

- exactCoefficientAssemblyPassed: `False`
- componentTaylorProofsPresent: `False`
- omegaDerivTaylorProofPresent: `True`
- omegaDerivTaylorProofAssembledIntoRawDerivative: `False`
- residualPolynomialRangePassed: `False`
- finalBudgetPassed: `False`
- proofSafeClosedFields: `1`
- outLeanWritten: `False`

## Existing Lean Inputs

- modelDerivCoeffSource: `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff`
- modelDerivCoeffCount: `16`
- fullTaylorPolynomialDerivativeCrosswalk: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel`
- fullTaylorResidualDerivativeCrosswalk: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm`
- fullTaylorDirectValidityBridge: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_direct_segment_cert_valid_of_residual_bounds`
- omegaDerivTaylorValidCert: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert_valid`

## Proshka Decision

- chosen: `B`
- why not A: Endpoint finite-cover machinery still lacks proof-grade Omega/OmegaPrime/E/EPrime remainder sources; it would create another empty checker first.
- why not C: A monolithic direct Lean proof would mix component expansions, product assembly, model subtraction, and range proof in one hard-to-audit theorem.

## Failure Codes

- `STEP33_A1_SUB0_OMEGA_SHAPE_SHAPEDERIV_TAYLOR_REMAINDER_GAP`
- `STEP33_A1_SUB0_SHAPE_SHAPEDERIV_TAYLOR_REMAINDER_GAP`
- `STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_GAP`
- `STEP33_A1_SUB0_RESIDUAL_POLYNOMIAL_RANGE_GAP`
- `STEP33_A1_SUB0_COMPONENT_TAYLOR_RESIDUAL_LEAN_PAYLOAD_MISSING`

## Decision

The next proof-producing gate is component Taylor/remainder data for
`omega`, `shape`, and `shapeDeriv`, plus a raw-derivative assembly
bridge that consumes the already checked `omegaDeriv` Taylor source.
Only after those component proofs exist may the generator assemble the
raw derivative, subtract the model derivative coefficients, bound the
residual polynomial, and emit Lean for the interval theorem.
