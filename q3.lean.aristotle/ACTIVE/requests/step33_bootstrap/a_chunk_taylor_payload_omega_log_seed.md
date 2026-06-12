# Step33A.1-A Taylor Payload Omega Log Seed

This seed adds checked log-Omega component bounds for every chunk with
left endpoint at least `10`.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- status: `omega_log_seed_chunk_bounds_geometry_row_sums_scale_cos_shape_and_omega_after_ten`
- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- Omega seeded cells: `2346`
- skipped first-chunk cells: `46`
- lower proof: `RawOmegaAChunkIntegral.step22OmegaArchWeight_neg_ten_logOmega_right_le_on_Ioc`
- upper proof: `RawOmegaAChunkIntegral.step22OmegaArchWeight_le_ten_logOmega_right_on_Ioc`

## Populated Fields

- `omegaLower`: `2346`
- `omegaUpper`: `2346`
- `omegaLowerBound`: `2346`
- `omegaUpperBound`: `2346`

## Families

| family | rows | chunks | Omega seeded cells | skipped | already present |
| --- | ---: | ---: | ---: | ---: | ---: |
| primary_finite | 23 | 26 | 575 | 23 | 0 |
| primary_tail | 23 | 26 | 598 | 0 | 0 |
| control_finite | 23 | 26 | 575 | 23 | 0 |
| control_tail | 23 | 26 | 598 | 0 | 0 |

## Route Guard

- Omega log seed applies only when chunk left endpoint is at least 10
- first finite chunk (0,10] remains open for compact small-window Omega
- this seed does not contain Taylor polynomial or remainder proof data
- do not emit Lean until all proof-data fields are complete
