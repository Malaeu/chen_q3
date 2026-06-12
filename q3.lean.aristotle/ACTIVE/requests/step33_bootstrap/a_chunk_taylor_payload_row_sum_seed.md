# Step33A.1-A Taylor Payload Row-Sum Seed

This seed adds row-level arithmetic proof-term candidates for
`lowerSum` / `upperSum` on top of the geometry seed.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- status: `row_sum_seed_chunk_bounds_geometry_and_row_sums`
- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- lowerSum seeded rows: `92`
- upperSum seeded rows: `92`
- row-sum failures: `0`

## Families

| family | rows | lowerSum rows | upperSum rows |
| --- | ---: | ---: | ---: |
| primary_finite | 23 | 23 | 23 |
| primary_tail | 23 | 23 | 23 |
| control_finite | 23 | 23 | 23 |
| control_tail | 23 | 23 | 23 |

## Route Guard

- row-sum proof terms are arithmetic candidates pending generated Lean check
- this seed does not contain Taylor/model analytic proof data
- do not emit Lean until all proof-data fields are complete
