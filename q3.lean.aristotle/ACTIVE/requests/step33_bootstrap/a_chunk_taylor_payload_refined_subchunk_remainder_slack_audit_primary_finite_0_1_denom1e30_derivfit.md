# Step33A.1-A Refined Subchunk Remainder Slack Audit

Fail-closed accounting report.  This is not Lean proof data.

## Verdict

- status: `derivative_slack_exceeds_current_parent_or_row_bounds`
- family: `primary_finite`
- row: `0`
- parent chunk: `1`
- split: `10`

## Counts

| item | count |
| --- | ---: |
| `subchunks` | `10` |
| `derivativeFailuresNeedingSlack` | `0` |
| `proofSafeClosedFields` | `0` |

## Parent Accounting

| item | value |
| --- | ---: |
| `parentLower` | `2.615058139399545823E-1` |
| `parentUpper` | `2.615058139399545823E-1` |
| `candidateLowerSum` | `2.615058139399545823E-1` |
| `candidateUpperSum` | `2.615058139399545823E-1` |
| `adjustedLowerSum` | `2.615058139399545823E-1` |
| `adjustedUpperSum` | `2.615058139399545823E-1` |
| `currentParentLowerSlack` | `-2.000000000000000000E-20` |
| `currentParentUpperSlack` | `2.000000000000000000E-20` |
| `adjustedParentLowerSlack` | `-2.000000000000000000E-20` |
| `adjustedParentUpperSlack` | `2.000000000000000000E-20` |
| `parentLowerDeltaIfReplaced` | `-2.000000000000000000E-20` |
| `parentUpperDeltaIfReplaced` | `-2.000000000000000000E-20` |
| `totalExtraRemainderNeeded` | `0.000000000000000000E+18` |

## Row Accounting

| item | value |
| --- | ---: |
| `rowTargetLower` | `1.233644453639219465E-1` |
| `rowTargetUpper` | `1.233644453639219559E-1` |
| `rowParentLowerSumBefore` | `1.233644453639219558E-1` |
| `rowParentUpperSumBefore` | `1.233644453639219558E-1` |
| `rowLowerSlackBefore` | `9.339065424863067479E-18` |
| `rowUpperSlackBefore` | `6.093457513693252068E-20` |
| `rowLowerSlackAfterReplacingParent` | `9.319065424863067479E-18` |
| `rowUpperSlackAfterReplacingParent` | `8.093457513693252068E-20` |

## Guard

- accounting audit only
- do not emit Lean from this report
- do not mutate parent or row bounds from this report
- if current row slack is insufficient, choose an explicit row-target refresh or global slack policy before payload emission
- proofSafeClosedFields remains zero
