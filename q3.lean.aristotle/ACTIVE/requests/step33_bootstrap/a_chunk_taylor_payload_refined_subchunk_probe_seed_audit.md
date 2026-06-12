# Step33A.1-A Refined Subchunk Probe Seed Audit

Fail-closed pilot audit.  This is not Lean proof data.

## Verdict

- status: `diagnostic_probe_not_proof_data`
- blocker: `probe lacks universal raw/poly value and diff-bound proofs`
- family: `primary_finite`
- row: `0`
- parent chunk: `0`
- degree: `16`
- split: `100`

## Counts

| item | count |
| --- | ---: |
| `expectedSubchunks` | `100` |
| `probePreviewSubchunks` | `100` |
| `missingPreviewSubchunks` | `0` |
| `endpointMatchesInPreview` | `100` |
| `endpointMismatches` | `0` |
| `candidateMappedFields` | `400` |
| `proofSafeClosedFields` | `0` |
| `proofFieldsRequiredForParent` | `1100` |
| `zeroRemainderWithPositiveSampledResidual` | `0` |

## Candidate Field Map

| probe field | skeleton field |
| --- | --- |
| `coeff_rational_candidate` | `coeff` |
| `remainder_rational_candidate` | `remainder` |
| `lower_model_integral` | `integralLower` |
| `upper_model_integral` | `integralUpper` |

## Guard

- do not mutate the refined skeleton from this audit
- do not emit Lean from sampled probe data
- coefficients and model integrals are diagnostic candidates only
- future proof-data must use outward rationalization for remainders
- future proof-data must provide universal raw/poly value bounds or a checked replacement theorem
- future proof-data must still provide row hLowerSum/hUpperSum comparisons

## Next Generator Contract

- emit all refined subchunks, not preview rows
- emit outward-rational coeff/remainder/integralLower/integralUpper candidates
- emit polynomial value bounds accepted by the checked polynomial-radius helper
- emit raw-integrand value bounds or a checked analytic enclosure helper
- emit diffLower/diffUpper and integral comparisons as Lean-checkable rational inequalities
- then rerun the existing refined emitter guard
