# Step33A.1-A Refined Subchunk Rational Residual Audit

Sampled diagnostic audit.  This is not Lean proof data.

## Verdict

- status: `sampled_rational_residual_audit_failed`
- family: `primary_finite`
- row: `0`
- parent chunk: `1`
- degree: `16`
- split: `10`

## Counts

| item | count |
| --- | ---: |
| `candidateSubchunks` | `10` |
| `sampledRemainderPasses` | `7` |
| `sampledRemainderFails` | `3` |
| `proofSafeClosedFields` | `0` |
| `sampledDiffCandidateFields` | `20` |

## Worst Sample

- subchunk: `0`
- worst eta: `1.001666666666666667E+1`
- sampled max residual: `1.294726270209177252E-28`
- current remainder: `69/500000000000000000000000000000`
- required remainder: `143/1000000000000000000000000000000`

## First Failures

| subchunk | current | required | worst eta |
| ---: | ---: | ---: | ---: |
| 0 | `69/500000000000000000000000000000` | `143/1000000000000000000000000000000` | `1.001666666666666667E+1` |
| 1 | `7/250000000000000000000000000000` | `29/1000000000000000000000000000000` | `1.101666666666666667E+1` |
| 2 | `7/1000000000000000000000000000000` | `1/125000000000000000000000000000` | `1.201666666666666667E+1` |

## Guard

- do not emit Lean from sampled residual audit
- sampled diff candidates must be replaced by universal checked bounds
- if sampled audit fails, increase or recompute candidate remainder before any proof-data attempt
- if sampled audit passes, the next target is a checked analytic enclosure for the same rational polynomial candidates
