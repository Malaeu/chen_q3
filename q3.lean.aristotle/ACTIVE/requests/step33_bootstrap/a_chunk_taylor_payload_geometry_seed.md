# Step33A.1-A Taylor Payload Geometry Seed

This seed adds deterministic chunk midpoint/radius data and arithmetic
proof terms on top of the diagnostic chunk-bound seed.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- status: `geometry_seed_chunk_bounds_and_radius_only`
- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- geometry seeded cells: `2392`
- populated proof cells: `2392`

## Populated Fields

- `center`
- `radius`
- `radiusNonneg`
- `radiusLeft`
- `radiusRight`

## Families

| family | rows | chunks | geometry seeded cells |
| --- | ---: | ---: | ---: |
| primary_finite | 23 | 26 | 598 |
| primary_tail | 23 | 26 | 598 |
| control_finite | 23 | 26 | 598 |
| control_tail | 23 | 26 | 598 |

## Route Guard

- geometry proof terms are arithmetic only and still need generated Lean check
- this seed does not contain Taylor/model analytic proof data
- do not emit Lean until all proof-data fields are complete
