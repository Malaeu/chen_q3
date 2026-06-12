# Step33A.1-A Refined Row-Sum Worklist

Address-only worklist for the exact-sum parent refined route.
This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a_refined_row_sum_worklist.v1`
- status: `refined_row_sum_worklist_address_only`
- parent bounds mode: `exact_subchunk_sums`
- families: `4`
- rows: `92`
- lower obligations: `92`
- upper obligations: `92`
- total obligations: `184`

## Families

| family | kind | rows | lower | upper |
| --- | --- | ---: | ---: | ---: |
| `primary_finite` | `finite` | `23` | `23` | `23` |
| `primary_tail` | `tail` | `23` | `23` | `23` |
| `control_finite` | `finite` | `23` | `23` | `23` |
| `control_tail` | `tail` | `23` | `23` | `23` |

## Obligation Shape

- lower: target lower <= nested sum of refined subchunk lower bounds
- upper: nested sum of refined subchunk upper bounds <= target upper

## Guard

- address-only worklist
- not Lean proof data
- do not use old parent-chunk row_sum_seed as proof for refined exact sums
- row proofs depend on generated refined subchunk integralLower/integralUpper data
- do not emit RefinedPayloadFin while row or subchunk analytic fields are missing
