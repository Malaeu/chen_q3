# Step33A.1-A Refined Subchunk Candidate Overlay

Fail-closed candidate overlay.  This is not Lean proof data.

## Verdict

- status: `candidate_overlay_not_proof_data`
- family: `primary_finite`
- row: `0`
- parent chunk: `1`
- degree: `16`
- split: `10`

## Counts

| item | count |
| --- | ---: |
| `expectedSubchunks` | `10` |
| `probeSubchunks` | `10` |
| `candidateSubchunks` | `10` |
| `endpointMismatchSubchunks` | `0` |
| `seededCandidateFields` | `90` |
| `stillMissingFields` | `20` |
| `proofSafeClosedFields` | `0` |

## Seeded Candidate Fields

- `coeff`
- `remainder`
- `remainderNonneg`
- `polyLower`
- `polyUpper`
- `polynomialLowerBound`
- `polynomialUpperBound`
- `integralLower`
- `integralUpper`

## Still Missing Fields

- `diffLower`
- `diffUpper`

## Guard

- do not mutate the refined skeleton or worklist from this overlay
- do not emit Lean from this overlay
- sampled residuals must be replaced by universal checked bounds
- rational coefficients must be residual-rechecked after rounding
- raw-integrand value bounds or direct diff bounds remain required
- row hLowerSum/hUpperSum comparisons remain required

## Next Generator Contract

- recompute residual bounds against the rational polynomial candidates
- generate universal raw-integrand value bounds or direct diff bounds
- turn polynomial-radius arithmetic into Lean-checkable proof terms
- then lift this overlay shape from one parent chunk to shardable refined worklists
