# Step33A.1-A Refined Subchunk Worklist

Address-only worklist.  This file does not close any Lean theorem and
must not be imported as trusted proof data.

## Summary

- degree candidate: `16`
- first finite chunk split: `100`
- remaining finite chunk split: `10`
- tail chunk split: `20`
- families: `4`
- distance rows: `92`
- parent chunks: `2392`
- refined subchunks: `40020`
- Lean landing surface: `RawOmegaAChunkTaylorPayload.RefinedPayloadFin`

| family | domain | rows | parent chunks | subchunks |
| --- | --- | ---: | ---: | ---: |
| `primary_finite` | `(0,260]` | `23` | `598` | `8050` |
| `primary_tail` | `(260,520]` | `23` | `598` | `11960` |
| `control_finite` | `(0,260]` | `23` | `598` | `8050` |
| `control_tail` | `(260,520]` | `23` | `598` | `11960` |

## Missing Proof Fields

Each refined subchunk still needs:

- `degree`
- `coeff`
- `remainder`
- `remainderNonneg`
- `polyLower`
- `polyUpper`
- `polynomialLowerBound`
- `polynomialUpperBound`
- `diffLower`
- `diffUpper`
- `integralLower`
- `integralUpper`

Each parent fold still needs:

- `RawOmegaAChunkTaylorPayload.RefinedPayloadFin`
- `RawOmegaAChunkTaylorPayload.RefinedPayloadFin.toDirectTailWindowInputs`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.n`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.pts`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.subLower`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.subUpper`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.first_eq`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.last_eq`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.mono`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.hProfileInt`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.subCert`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.lower_le_sum`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.sum_le_upper`
- `RawOmegaAChunkIntegral.RefinedWindowPartBoundsCert.of_refinedSubchunkSums (exact-sum parent cert)`
- `RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunks`
- `RawOmegaAChunkIntegral.WindowPartBoundsCert.of_refinedSubchunkSums (optional exact-sum parent route)`

## Guard

- address-only worklist
- not Lean proof data
- do not import this file as a trusted payload
- outer parent chunk shape remains unchanged
- parent closure must go through RefinedWindowPartBoundsCert
- exact-sum parent bounds build RefinedWindowPartBoundsCert.of_refinedSubchunkSums
- do not replace the top-level 26 parent chunks by a fully refined payload
