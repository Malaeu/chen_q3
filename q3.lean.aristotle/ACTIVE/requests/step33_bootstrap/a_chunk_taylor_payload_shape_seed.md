# Step33A.1-A Taylor Payload Shape-Square Seed

This seed adds structural centered B-spline transform-square bounds on
top of the current cosine seed.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- status: `shape_square_seed_chunk_bounds_geometry_row_sums_scale_cos_and_shape`
- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- shape-square seeded cells: `2392`
- lower proof: `RawOmegaAChunkIntegral.centeredBSplineImagTransformRealClosedForm_sq_nonneg`
- upper proof: `RawOmegaAChunkIntegral.centeredBSplineImagTransformRealClosedForm_sq_le_globalMajorant`

## Populated Fields

- `shapeSqLower`: `2392`
- `shapeSqUpper`: `2392`
- `shapeSqLowerBound`: `2392`
- `shapeSqUpperBound`: `2392`

## Families

| family | rows | chunks | shape seeded cells | already present |
| --- | ---: | ---: | ---: | ---: |
| primary_finite | 23 | 26 | 598 | 0 |
| primary_tail | 23 | 26 | 598 | 0 |
| control_finite | 23 | 26 | 598 | 0 |
| control_tail | 23 | 26 | 598 | 0 |

## Route Guard

- shapeSqLower/Upper use checked structural sinc envelope lemmas
- this seed does not contain Omega enclosure data
- this seed does not contain Taylor polynomial or remainder proof data
- do not emit Lean until all proof-data fields are complete
