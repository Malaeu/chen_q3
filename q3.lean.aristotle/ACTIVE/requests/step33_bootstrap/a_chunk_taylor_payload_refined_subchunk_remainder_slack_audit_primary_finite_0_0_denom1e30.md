# Step33A.1-A Refined Subchunk Remainder Slack Audit

Fail-closed accounting report.  This is not Lean proof data.

## Verdict

- status: `derivative_slack_exceeds_current_parent_or_row_bounds`
- family: `primary_finite`
- row: `0`
- parent chunk: `0`
- split: `100`

## Counts

| item | count |
| --- | ---: |
| `subchunks` | `100` |
| `derivativeFailuresNeedingSlack` | `0` |
| `proofSafeClosedFields` | `0` |

## Parent Accounting

| item | value |
| --- | ---: |
| `parentLower` | `-3.535346901998863369E-1` |
| `parentUpper` | `-3.535346901998863369E-1` |
| `candidateLowerSum` | `-3.535346901998863369E-1` |
| `candidateUpperSum` | `-3.535346901998863369E-1` |
| `adjustedLowerSum` | `-3.535346901998863369E-1` |
| `adjustedUpperSum` | `-3.535346901998863369E-1` |
| `currentParentLowerSlack` | `8.910000000000000000E-21` |
| `currentParentUpperSlack` | `-1.891000000000000000E-20` |
| `adjustedParentLowerSlack` | `8.910000000000000000E-21` |
| `adjustedParentUpperSlack` | `-1.891000000000000000E-20` |
| `parentLowerDeltaIfReplaced` | `8.910000000000000000E-21` |
| `parentUpperDeltaIfReplaced` | `1.891000000000000000E-20` |
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
| `rowLowerSlackAfterReplacingParent` | `9.347975424863067479E-18` |
| `rowUpperSlackAfterReplacingParent` | `4.202457513693252068E-20` |

## Guard

- accounting audit only
- do not emit Lean from this report
- do not mutate parent or row bounds from this report
- if current row slack is insufficient, choose an explicit row-target refresh or global slack policy before payload emission
- proofSafeClosedFields remains zero
