# Step33A.1-A Sub0 Omega/OmegaPrime Taylor Remainder Gap

Status: GAP.

This file is a source map and proof contract for the current first live
blocker.  It is not a proof object, does not emit Lean, and does not close
Step33A.1-A.

## Current blocker

```text
STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP
```

The active route is the component Taylor residual route selected after the
previous endpoint-vs-Taylor route fork.  In the current payload this route is
called `B`.

Local payload:

```text
ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_taylor_residual_payload.md
ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_taylor_residual_payload.json
```

Payload status:

```text
schema = q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v1
status = fail_closed_missing_omega_omegaprime_taylor_remainder
firstFailure = STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP
componentDegree = 15
assembledDegree = 45
proofSafeClosedFields = 0
outLeanWritten = false
```

## Exact consumer

The proof-grade consumer already exists locally in:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean
```

Relevant local objects:

- line 1820: `primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm`
- line 1848: `primaryFiniteRow0Parent0Split100Sub0_raw_integrand_deriv_eq_closedForm`
- line 1912: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm`
- line 2815: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_direct_segment_cert_valid_of_residual_bounds`
- line 2868: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_residual_bounds`

The exact interval required by the consumer is:

```lean
forall eta in Set.Icc (0 : Real) ((1 : Real) / 10),
  ((-94119513411 : Real) / 500000000000000000000000000000) <=
    primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
      rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta
  and
    primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
      rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta <=
      ((1866608532757 : Real) / 500000000000000000000000000000)
```

If this exact same-expression interval is proved, Lean can feed it through:

```lean
primaryFiniteRow0Parent0Split100Sub0_fullTaylor_direct_segment_cert_valid_of_residual_bounds
primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_residual_bounds
```

## Current raw derivative expression

The checked raw derivative closed form is:

```lean
def primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm
    (eta : Real) : Real :=
  (((3 : Real) / 10) / Real.pi) *
    (step22OmegaArchWeightDerivClosedForm eta *
        (centeredBSplineImagTransformRealClosedForm 11 ((3 : Real) / 10) eta) ^ 2 +
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta *
        (2 *
          centeredBSplineImagTransformRealClosedForm 11 ((3 : Real) / 10) eta *
            centeredBSplineImagTransformRealClosedFormDerivClosedForm
              11 ((3 : Real) / 10) eta))
```

Thus the component split is:

- `omega = step22OmegaArchWeight`
- `omegaPrime = step22OmegaArchWeightDerivClosedForm`
- `shape = centeredBSplineImagTransformRealClosedForm 11 (3/10)`
- `shapePrime = centeredBSplineImagTransformRealClosedFormDerivClosedForm 11 (3/10)`

The route-B payload must build exact component Taylor data around center
`1/20` on radius `1/20`, assemble the raw derivative polynomial, subtract the
checked model derivative polynomial, and then prove the residual polynomial
range plus combined remainder against the exact interval above.

## Local source inventory

### Analytic Omega source

File:

```text
Q3/Proofs/PSD_CenteredCoeffAnalyticABoundsBackend.lean
```

Local definitions/facts:

- line 60: `step22OmegaArchWeight`
- line 3280: `step22OmegaArchWeight_eq_neg_inv_twoPi_aStar`
- line 3328: `step22OmegaArchWeight_differentiableAt`
- line 3392: `step22PositiveAxisOmegaAIntegrand_differentiableAt`

Status: FORMAL support for the Omega function and differentiability, but not a
Taylor remainder certificate for `omega` on `[0, 1/10]` around center `1/20`.

### Chunk Taylor checker and endpoint support

File:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean
```

Local definitions/facts:

- line 30: `rawOmegaATaylorPolynomial`
- line 56: `RawOmegaATaylorModelCertificate`
- line 2633: `LocalRawOmegaComponentIntervalCert`
- line 3007: `LocalRawOmegaComponentIntervalCert.of_anchor_deriv_bounds_auto_differentiability`
- line 3090: `centeredBSplineImagTransformRealClosedFormDerivClosedForm`
- line 6440: `step22OmegaArchWeightDerivClosedForm`
- line 6446: `digamma_analyticAt_of_re_pos`
- line 6470: `trigamma_differentiableAt_of_re_pos`
- line 6485: `step22OmegaArchWeightDerivClosedForm_differentiableAt`
- line 8438: `step22OmegaArchWeight_deriv_eq_closedForm`
- line 8486: `step22OmegaArchWeight_deriv_eq_closedForm_on_Icc`
- line 8501: `Step22OmegaEndpointIntervalCert`
- line 8568: `Step22OmegaClosedFormEndpointBoundsCert`
- line 9224: `Step22OmegaClosedFormEndpointBoundsCert.toStep22OmegaEndpointIntervalCert`
- line 12137: `ResidualDerivativeDirectNormCert`
- line 12170: `ResidualDerivativeDirectNormCert.Valid.of_interval_bounds`
- line 12197: `ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound`

Status: FORMAL support for endpoint/component interval receivers and direct
residual derivative norm receivers.  GAP for Taylor coefficients/remainders of
`omega` and `omegaPrime` in the current first-subchunk coordinate system.

### Generated route-B payload

File:

```text
scripts/generate_step33_a1_sub0_component_taylor_residual_payload.py
```

Local facts:

- line 47: schema `q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v1`
- line 50: first failure `STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP`
- line 54: planned theorem surface suffix `fullTaylor_residual_deriv_taylor_enclosure`

Status: PROBE/DOC.  It extracts existing model derivative coefficients and
records the next proof obligations.  It does not prove component Taylor data,
does not assemble proof-grade residual bounds, and does not emit Lean.

### Candidate theorem surface

The candidate theorem name

```lean
primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure
```

currently appears in the generator and generated payload, not as a local Lean
theorem.  Its intended statement is advisory/planned until a Lean file provides
it and `lake env lean` checks it.

Status: GAP.

## Search record

Local semantic searches were run before naming this blocker:

```bash
cd q3.lean.aristotle
./scripts/research_oracle.py query "STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP omega omegaPrime Taylor remainder" -c q3_docs
./scripts/research_oracle.py query "step22OmegaArchWeightDerivClosedForm Taylor remainder first subchunk residual derivative" -c q3_docs
./scripts/research_oracle.py query "primaryFiniteRow0Parent0Split100Sub0 fullTaylor residual deriv closedForm bounds" -c q3_docs
./scripts/research_oracle.py query "RawOmegaATaylorModelCertificate omega derivative endpoint interval cert Taylor remainder" -c q3_docs
```

Result: no ready local proof-producing omega/omegaPrime Taylor remainder bridge
was found.

External Mathlib Taylor documentation was used only as route context, not as
proof evidence.  Any Taylor route must import/use local Lean theorems and pass
`lake env lean` before it becomes proof evidence.

## Advisory browser record

Browser/Proshka was used for route selection.  This is advisory only and is
not proof evidence.

The first Proshka answer chose the component Taylor residual route and named:

```lean
primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure
```

with fields:

```text
center = 1/20
radius = 1/20
componentDegree = 15
assembledDegree = 45
omegaCoeff[0..15]
omegaDerivCoeff[0..15]
shapeCoeff[0..15]
shapeDerivCoeff[0..15]
omegaRemainderAbs
omegaDerivRemainderAbs
shapeRemainderAbs
shapeDerivRemainderAbs
assembledRawDerivCoeff[0..45]
modelDerivCoeff[0..15]
residualTaylorCoeff[0..45]
productTruncationRemainderAbs
componentPropagationRemainderAbs
residualTaylorRemainderAbs
residualPolynomialLower
residualPolynomialUpper
finalResidualLower
finalResidualUpper
targetLower = -94119513411/5e29
targetUpper = 1866608532757/5e29
exactCoefficientAssemblyPassed
componentTaylorProofsPresent
residualPolynomialRangePassed
finalBudgetPassed
proofSafeClosedFields
outLeanWritten
failureCodes[]
```

Follow-up review request sent for the narrower fork:

```md
## PRO_REVIEW_REQUEST

Route:
Q3 PSD-pd Step33A.1-A, current component Taylor residual route for first
subchunk.

Current step:
Close `STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP`.

Current theorem:
`primaryFiniteRow0Parent0Split100Sub0_fullTaylor_direct_segment_cert_valid_of_residual_bounds`

File:
`Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean`

Lean error / blocker:
No local theorem currently proves Taylor coefficients/remainders for
`step22OmegaArchWeight` and `step22OmegaArchWeightDerivClosedForm` around
center `1/20` over `[0, 1/10]`, nor the assembled same-expression residual
interval needed by the consumer.

Options:
A. Build `OmegaTaylorRemainderCert` / `OmegaPrimeTaylorRemainderCert` receiver
   using a local Taylor theorem or local high-derivative/polygamma bounds, then
   assemble coefficients/remainder.
B. Use existing endpoint finite-cover interval certs to prove the
   same-expression residual derivative interval directly, without Taylor
   coefficients.

Codex recommendation:
A, if it can be made proof-grade with a compact receiver.  Use B as fallback if
high-derivative Taylor bounds become too expensive.

Question for Louise:
Choose the smallest next proof-producing patch.  Give exact theorem/generator
surface and first failure code if it cannot close.
```

Follow-up Proshka answer, advisory-only:

```text
CHOSEN: A
GENERATOR TARGET: scripts/generate_step33_a1_sub0_omega_prime_taylor_payload.py
FIRST FAILURE CODE: STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP
```

Suggested proof surface, normalized before any Lean edit:

```lean
structure Step33Sub0OmegaPrimeTaylorRemainderCert where
  coeff : Fin 16 -> Rat
  coeffErrorAbs : Fin 16 -> Rat
  order16Abs : Rat
  remainderAbs : Rat

theorem Step33Sub0OmegaPrimeTaylorRemainderCert.Valid.bound
    {data : Step33Sub0OmegaPrimeTaylorRemainderCert}
    (h : data.Valid) :
    forall eta in Set.Icc (0 : Real) ((1 : Real) / 10),
      norm (step22OmegaArchWeightDerivClosedForm eta - data.poly eta) <=
        (data.remainderAbs : Real)
```

The answer also warns that the endpoint finite-cover route only subdivides the
domain; it does not by itself provide the missing same-expression interval
arithmetic.  The recommended first proof-producing subproblem is therefore the
order-16 bound for `step22OmegaArchWeightDerivClosedForm`.

Local normalization note: Proshka wrote the shape using a Lean sketch.  Before
editing Lean, align it with the local convention that
`rawOmegaATaylorPolynomial` takes a `Rat` center and a `Fin (degree + 1) -> Rat`
coefficient function.

## Missing proof

The missing proof is not a new scalar budget and not an independent sampled
diagnostic.  It is a same-expression interval proof for the exact consumer.

Required component proof objects:

1. `omegaCoeff[0..15]` and `omegaRemainderAbs` for
   `step22OmegaArchWeight` around center `1/20`, radius `1/20`.
2. `omegaDerivCoeff[0..15]` and `omegaDerivRemainderAbs` for
   `step22OmegaArchWeightDerivClosedForm` around center `1/20`, radius `1/20`.
3. Shape and shape derivative Taylor data in the same center/radius convention.
4. Exact coefficient assembly for the raw derivative expression, degree 45.
5. Exact subtraction of
   `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff`, padded from
   degree 15 to degree 45.
6. Exact range proof for the residual Taylor polynomial on `[0, 1/10]`.
7. Exact combined remainder proof that yields the consumer interval.

Until these are present, the correct status remains:

```text
GAP
```

## Next proof-producing patch

Smallest useful next patch:

```text
Build an OmegaPrime Taylor remainder receiver or generator surface.
```

Minimum acceptable output:

- a fail-closed generator or Lean receiver named around
  `step33_a1_sub0_omega_prime_taylor_payload`
- exact center/radius: `center = 1/20`, `radius = 1/20`
- exact interval: `[0, 1/10]`
- proof status fields for `coeff[0..15]`, `coeffErrorAbs[0..15]`,
  `order16Abs`, `coefficientErrorBudget`, `lagrangeRemainderBudget`,
  `remainderAbs`, `centerJetSource[0..15]`, `order16BoundSource`
- first failure code if it cannot close:

```text
STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP
```

No Lean payload should be emitted from this route until the component
remainder proof objects are proof-grade.

## Generated OmegaPrime payload

The first narrow payload surface now exists:

```text
scripts/generate_step33_a1_sub0_omega_prime_taylor_payload.py
ACTIVE/requests/step33_bootstrap/step33_a1_sub0_omega_prime_taylor_payload.json
ACTIVE/requests/step33_bootstrap/step33_a1_sub0_omega_prime_taylor_payload.md
```

Current status:

```text
status = fail_closed_missing_order16_polygamma_bound
firstFailure = STEP33_A1_SUB0_OMEGAPRIME_ORDER16_POLYGAMMA_BOUND_GAP
proofSafeClosedFields = 0
outLeanWritten = false
```

The payload confirms that the existing Lean source gives differentiability and
endpoint/remainder support, but not the order-16 bound required for a
proof-grade Taylor remainder certificate.
