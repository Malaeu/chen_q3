# Step33A.1-A Taylor Payload Probe Seed

This file seeds candidate `chunkLower` / `chunkUpper` values from the
diagnostic Arb/acb probe.  It is not a Lean proof object.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- status: `probe_seed_chunk_bounds_only_missing_proofs`
- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- seeded chunk bounds: `2392`
- missing probe cells: `0`
- populated proof cells: `0`

## Families

| family | rows | chunks | seeded chunk bounds |
| --- | ---: | ---: | ---: |
| primary_finite | 23 | 26 | 598 |
| primary_tail | 23 | 26 | 598 |
| control_finite | 23 | 26 | 598 |
| control_tail | 23 | 26 | 598 |

## Route Guard

- chunk bounds seeded from Arb/acb diagnostics are candidates only
- do not treat this seed as trusted proof data
- do not emit Lean until Taylor/model proof fields are complete
