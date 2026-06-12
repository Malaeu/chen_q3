# Step33A.1-A Taylor Payload Scale Seed

This seed adds shared family scale nonnegativity proof terms on top of
the current row-sum seed.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- status: `scale_interval_seed_chunk_bounds_geometry_row_sums_and_scale`
- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- scale interval seeded cells: `2392`
- scaleNonneg seeded cells: `2392`
- scale interval: `9/100 <= ell / Real.pi <= 1/10`
- primary lower proof: `RawOmegaAChunkIntegral.primaryK11Ell_div_pi_scaleLower`
- primary upper proof: `RawOmegaAChunkIntegral.primaryK11Ell_div_pi_scaleUpper`
- control lower proof: `RawOmegaAChunkIntegral.controlK9Ell_div_pi_scaleLower`
- control upper proof: `RawOmegaAChunkIntegral.controlK9Ell_div_pi_scaleUpper`
- primary proof: `RawOmegaAChunkIntegral.primaryK11Ell_div_pi_nonneg`
- control proof: `RawOmegaAChunkIntegral.controlK9Ell_div_pi_nonneg`

## Populated Fields

- `scaleLower`
- `scaleUpper`
- `scaleLowerBound`
- `scaleUpperBound`
- `scaleNonneg`

## Families

| family | rows | chunks | scale interval seeded cells | scaleNonneg seeded cells | already present |
| --- | ---: | ---: | ---: | ---: | ---: |
| primary_finite | 23 | 26 | 598 | 598 | 0 |
| primary_tail | 23 | 26 | 598 | 598 | 0 |
| control_finite | 23 | 26 | 598 | 598 | 0 |
| control_tail | 23 | 26 | 598 | 598 | 0 |

## Route Guard

- scaleLower/scaleUpper are shared family values, not cell enclosure data
- scaleLowerBound/scaleUpperBound are shared Lean theorem references
- scaleNonneg is retained only as compatibility diagnostic data
- this seed does not contain Taylor/model analytic proof data
- do not emit Lean until all proof-data fields are complete
