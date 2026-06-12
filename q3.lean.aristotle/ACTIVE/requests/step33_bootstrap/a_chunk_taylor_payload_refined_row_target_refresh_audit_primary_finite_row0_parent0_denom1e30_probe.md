# Step33A.1-A Refined Row Target Refresh Audit

Fail-closed aggregate row accounting report.  This is not Lean proof data.

## Verdict

- status: `row_target_refresh_required_for_covered_candidate_parents`
- family: `primary_finite`
- row: `0`

## Counts

| item | count |
| --- | ---: |
| `rowParentChunks` | `26` |
| `coveredCandidateParents` | `2` |
| `slackFitParents` | `0` |
| `derivativeFailuresNeedingSlack` | `1` |
| `proofSafeClosedFields` | `0` |

## Row Accounting

| item | value |
| --- | ---: |
| `targetLowerBefore` | `1.233644453639219465E-1` |
| `targetUpperBefore` | `1.233644453639219559E-1` |
| `rowParentLowerSumBefore` | `1.233644453639219558E-1` |
| `rowParentUpperSumBefore` | `1.233644453639219558E-1` |
| `rowLowerSlackBefore` | `9.339065424863067479E-18` |
| `rowUpperSlackBefore` | `6.093457513693252068E-20` |
| `rowParentLowerSumAfterReplacingCoveredParents` | `1.233644453639219504E-1` |
| `rowParentUpperSumAfterReplacingCoveredParents` | `1.233644453639219606E-1` |
| `rowLowerSlackAfterReplacingCoveredParents` | `3.939065424863067479E-18` |
| `rowUpperSlackAfterReplacingCoveredParents` | `-4.739065424863067479E-18` |
| `requiredLowerTargetDecrease` | `0.000000000000000000E+18` |
| `requiredUpperTargetIncrease` | `4.739065424863067479E-18` |
| `minimalRefreshedTargetLower` | `1.233644453639219465E-1` |
| `minimalRefreshedTargetUpper` | `1.233644453639219606E-1` |

## Covered Parent Replacements

| parent | interval | current upper | adjusted upper | upper delta | adjusted upper slack | derivative failures |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 0 | `(0.000000000000000000E+0, 1.000000000000000000E+1]` | `-3.535346901998863369E-1` | `-3.535346901998863369E-1` | `0.000000000000000000E-1` | `-1.891000000000000000E-20` | `0` |
| 1 | `(1.000000000000000000E+1, 2.000000000000000000E+1]` | `2.615058139399545823E-1` | `2.615058139399545871E-1` | `4.800000000000000000E-18` | `-4.756029973344000000E-18` | `1` |

## Guard

- aggregate accounting audit only
- do not emit Lean from this report
- do not mutate parent or row bounds from this report
- covered parents only; uncovered parents keep current worklist bounds
- if refresh is chosen, prove a local row-target/recenter containment theorem before payload emission
- proofSafeClosedFields remains zero
