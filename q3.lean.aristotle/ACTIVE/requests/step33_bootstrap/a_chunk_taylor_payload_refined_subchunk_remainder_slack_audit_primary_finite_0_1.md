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
| `derivativeFailuresNeedingSlack` | `1` |
| `proofSafeClosedFields` | `0` |

## Parent Accounting

| item | value |
| --- | ---: |
| `parentLower` | `2.615058139399545823E-1` |
| `parentUpper` | `2.615058139399545823E-1` |
| `candidateLowerSum` | `2.615058139399545770E-1` |
| `candidateUpperSum` | `2.615058139399545870E-1` |
| `adjustedLowerSum` | `2.615058139399545769E-1` |
| `adjustedUpperSum` | `2.615058139399545871E-1` |
| `currentParentLowerSlack` | `-5.300000000000000000E-18` |
| `currentParentUpperSlack` | `-4.700000000000000000E-18` |
| `adjustedParentLowerSlack` | `-5.356029973344000000E-18` |
| `adjustedParentUpperSlack` | `-4.756029973344000000E-18` |
| `parentLowerDeltaIfReplaced` | `-5.356029973344000000E-18` |
| `parentUpperDeltaIfReplaced` | `4.756029973344000000E-18` |
| `totalExtraRemainderNeeded` | `5.602997334400000000E-20` |

## Row Accounting

| item | value |
| --- | ---: |
| `rowTargetLower` | `1.233644453639219465E-1` |
| `rowTargetUpper` | `1.233644453639219559E-1` |
| `rowParentLowerSumBefore` | `1.233644453639219558E-1` |
| `rowParentUpperSumBefore` | `1.233644453639219558E-1` |
| `rowLowerSlackBefore` | `9.339065424863067479E-18` |
| `rowUpperSlackBefore` | `6.093457513693252068E-20` |
| `rowLowerSlackAfterReplacingParent` | `3.983035451519067479E-18` |
| `rowUpperSlackAfterReplacingParent` | `-4.695095398207067479E-18` |

## Slack-Needing Subchunks

| subchunk | interval | sampled excess | extra remainder |
| ---: | --- | ---: | ---: |
| 0 | `(1.000000000000000000E+1, 1.100000000000000000E+1]` | `5.602997334400000000E-20` | `5.602997334400000000E-20` |

## Guard

- accounting audit only
- do not emit Lean from this report
- do not mutate parent or row bounds from this report
- if current row slack is insufficient, choose an explicit row-target refresh or global slack policy before payload emission
- proofSafeClosedFields remains zero
