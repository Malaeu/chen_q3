# Step33A.1-A Taylor Payload Proof-Data Skeleton

This is an addressed schema template, not a Lean proof object.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- status: `skeleton_address_only_missing_values`
- include null fields: `False`
- payload type: `RawOmegaAChunkTaylorPayload.PayloadFin`
- Step33A wrapper: `RawOmegaAChunkTaylorPayload.PayloadFin.toDirectTailWindowInputs`
- Step33B/33C wrapper: `psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs`

## Counts

- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- populated proof cells: `0`

## Required Cell Fields

- `chunkLower`
- `chunkUpper`
- `center`
- `radius`
- `degree`
- `coeff`
- `remainder`
- `omegaLower`
- `omegaUpper`
- `omegaLowerBound`
- `omegaUpperBound`
- `shapeSqLower`
- `shapeSqUpper`
- `shapeSqLowerBound`
- `shapeSqUpperBound`
- `cosLower`
- `cosUpper`
- `cosLowerBound`
- `cosUpperBound`
- `rawLower`
- `rawUpper`
- `termLower`
- `termUpper`
- `polyLower`
- `polyUpper`
- `radiusNonneg`
- `remainderNonneg`
- `radiusLeft`
- `radiusRight`
- `polynomialTermBounds`
- `polyLowerSum`
- `polyUpperSum`
- `diffLower`
- `diffUpper`
- `integralLower`
- `integralUpper`

## Required Row Fields

- `lowerSum`
- `upperSum`

## Families

| family | rows | chunks | cells | constructor |
| --- | ---: | ---: | ---: | --- |
| primary_finite | 23 | 26 | 598 | `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds` |
| primary_tail | 23 | 26 | 598 | `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.primaryK11_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds` |
| control_finite | 23 | 26 | 598 | `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_finiteChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds` |
| control_tail | 23 | 26 | 598 | `RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.Valid.controlK9_tailChunk_of_raw_component_abs_cos_and_polynomial_term_bounds_model_integral_bounds` |

## Route Guard

- skeleton addresses are not proof data
- do not emit Lean payload from omitted or null fields
- do not use Arb/acb numeric probes as trusted proofs
- do not call Step33A.1-A closed until PayloadFin compiles
