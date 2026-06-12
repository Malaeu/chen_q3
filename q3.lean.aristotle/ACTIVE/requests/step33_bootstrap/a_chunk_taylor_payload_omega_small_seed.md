# Step33A.1-A Taylor Payload Omega Small-Window Seed

This seed fills the first finite `(0,10]` raw-Omega chunk using a
checked compact Stieltjes bound.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- status: `omega_small_seed_chunk_bounds_geometry_row_sums_scale_cos_shape_and_all_omega`
- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- Omega small-window seeded cells: `46`
- already present target cells: `0`
- lower proof: `RawOmegaAChunkIntegral.step22OmegaArchWeight_neg_twoHundred_le_on_Ioc_zero_ten`
- upper proof: `RawOmegaAChunkIntegral.step22OmegaArchWeight_le_twoHundred_on_Ioc_zero_ten`

## Populated Fields

- `omegaLower`: `46`
- `omegaUpper`: `46`
- `omegaLowerBound`: `46`
- `omegaUpperBound`: `46`

## Families

| family | rows | chunks | seeded | already present | not target |
| --- | ---: | ---: | ---: | ---: | ---: |
| primary_finite | 23 | 26 | 23 | 0 | 575 |
| primary_tail | 23 | 26 | 0 | 0 | 598 |
| control_finite | 23 | 26 | 23 | 0 | 575 |
| control_tail | 23 | 26 | 0 | 0 | 598 |

## Route Guard

- small Omega seed applies only to primary/control finite first chunk (0,10]
- do not use this as Step33A.1-A closure
- this seed does not contain Taylor polynomial or remainder proof data
- do not emit Lean until all proof-data fields are complete
