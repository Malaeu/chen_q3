# Step33A.1-A Refined Subchunk Rational Residual Audit

Sampled diagnostic audit.  This is not Lean proof data.

## Verdict

- status: `sampled_rational_residual_audit_passed_not_proof`
- family: `primary_finite`
- row: `0`
- parent chunk: `0`
- degree: `16`
- split: `100`

## Counts

| item | count |
| --- | ---: |
| `candidateSubchunks` | `100` |
| `sampledRemainderPasses` | `100` |
| `sampledRemainderFails` | `0` |
| `proofSafeClosedFields` | `0` |
| `sampledDiffCandidateFields` | `200` |

## Worst Sample

- subchunk: `37`
- worst eta: `3.700000000000000000E+0`
- sampled max residual: `5.167745095026847270E-19`
- current remainder: `1/1000000000000000000`
- required remainder: `1/1000000000000000000`

## Guard

- do not emit Lean from sampled residual audit
- sampled diff candidates must be replaced by universal checked bounds
- if sampled audit fails, increase or recompute candidate remainder before any proof-data attempt
- if sampled audit passes, the next target is a checked analytic enclosure for the same rational polynomial candidates
