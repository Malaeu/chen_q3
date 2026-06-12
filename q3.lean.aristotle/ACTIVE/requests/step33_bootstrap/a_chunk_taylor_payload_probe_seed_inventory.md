# Step33A.1-A Taylor Payload Proof-Data Inventory

This report is a guardrail, not a Lean proof object.

## Verdict

- status: `missing_proof_data`
- payload type: `RawOmegaAChunkTaylorPayload.PayloadFin`
- Step33A wrapper: `RawOmegaAChunkTaylorPayload.PayloadFin.toDirectTailWindowInputs`
- Step33B/33C wrapper: `psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs`
- expected proof-data schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- proof-data source: `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_probe_seed.json`

## Proof Data Source

- available: `True`
- status: `probe_seed_chunk_bounds_only_missing_proofs`
- families: `4`
- rows: `92`
- chunk cells: `2392`
- cells with any populated required field: `2392`
- cells with any populated proof field: `0`

## Counts

- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- complete rows: `0`
- complete cells: `0`
- missing cells: `2392`

## Diagnostic Probe

- available: `True`
- families: `4`
- rows: `92`
- chunk cells: `2392`
- numeric chunk intervals complete: `True`
- Taylor proof data present: `False`

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

## Product Proof Alternative

Each cell must provide one of three product proof packets: direct universal proof fields, all exact-scale eight-corner fields, or a family-scale interval with all sixteen scale/omega/shape/cos corner fields.  This stays sign-generic because the raw Step22 omega weight is negative on early finite chunks.

Direct fields:
- `componentProductLower`
- `componentProductUpper`

Corner receiver: `RawOmegaATaylorModelCertificate.product_bounds_of_eight_corners`

Corner fields:
- `componentProductCornerLowerLLL`
- `componentProductCornerLowerLLU`
- `componentProductCornerLowerLUL`
- `componentProductCornerLowerLUU`
- `componentProductCornerLowerULL`
- `componentProductCornerLowerULU`
- `componentProductCornerLowerUUL`
- `componentProductCornerLowerUUU`
- `componentProductCornerUpperLLL`
- `componentProductCornerUpperLLU`
- `componentProductCornerUpperLUL`
- `componentProductCornerUpperLUU`
- `componentProductCornerUpperULL`
- `componentProductCornerUpperULU`
- `componentProductCornerUpperUUL`
- `componentProductCornerUpperUUU`

Scale-interval receiver: `RawOmegaATaylorModelCertificate.product_bounds_of_scale_interval_and_sixteen_corners`

Scale-interval fields:
- `scaleLower`
- `scaleUpper`
- `scaleLowerBound`
- `scaleUpperBound`
- `componentProductScaleCornerLowerLLLL`
- `componentProductScaleCornerLowerLLLU`
- `componentProductScaleCornerLowerLLUL`
- `componentProductScaleCornerLowerLLUU`
- `componentProductScaleCornerLowerLULL`
- `componentProductScaleCornerLowerLULU`
- `componentProductScaleCornerLowerLUUL`
- `componentProductScaleCornerLowerLUUU`
- `componentProductScaleCornerLowerULLL`
- `componentProductScaleCornerLowerULLU`
- `componentProductScaleCornerLowerULUL`
- `componentProductScaleCornerLowerULUU`
- `componentProductScaleCornerLowerUULL`
- `componentProductScaleCornerLowerUULU`
- `componentProductScaleCornerLowerUUUL`
- `componentProductScaleCornerLowerUUUU`
- `componentProductScaleCornerUpperLLLL`
- `componentProductScaleCornerUpperLLLU`
- `componentProductScaleCornerUpperLLUL`
- `componentProductScaleCornerUpperLLUU`
- `componentProductScaleCornerUpperLULL`
- `componentProductScaleCornerUpperLULU`
- `componentProductScaleCornerUpperLUUL`
- `componentProductScaleCornerUpperLUUU`
- `componentProductScaleCornerUpperULLL`
- `componentProductScaleCornerUpperULLU`
- `componentProductScaleCornerUpperULUL`
- `componentProductScaleCornerUpperULUU`
- `componentProductScaleCornerUpperUULL`
- `componentProductScaleCornerUpperUULU`
- `componentProductScaleCornerUpperUUUL`
- `componentProductScaleCornerUpperUUUU`

## Required Row Fields

- `lowerSum`
- `upperSum`

## Families

| family | rows | chunks | cells | complete rows | complete cells | first examples |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| primary_finite | 23 | 26 | 598 | 0 | 0 | d0, d1, d2 |
| primary_tail | 23 | 26 | 598 | 0 | 0 | d0, d1, d2 |
| control_finite | 23 | 26 | 598 | 0 | 0 | d0, d1, d2 |
| control_tail | 23 | 26 | 598 | 0 | 0 | d0, d1, d2 |

## Missing Field Counts

- `cell.center`: `2392`
- `cell.coeff`: `2392`
- `cell.componentProductLower`: `2392`
- `cell.componentProductUpper`: `2392`
- `cell.cosLower`: `2392`
- `cell.cosLowerBound`: `2392`
- `cell.cosUpper`: `2392`
- `cell.cosUpperBound`: `2392`
- `cell.degree`: `2392`
- `cell.diffLower`: `2392`
- `cell.diffUpper`: `2392`
- `cell.integralLower`: `2392`
- `cell.integralUpper`: `2392`
- `cell.omegaLower`: `2392`
- `cell.omegaLowerBound`: `2392`
- `cell.omegaUpper`: `2392`
- `cell.omegaUpperBound`: `2392`
- `cell.polyLower`: `2392`
- `cell.polyLowerSum`: `2392`
- `cell.polyUpper`: `2392`
- `cell.polyUpperSum`: `2392`
- `cell.polynomialTermBounds`: `2392`
- `cell.radius`: `2392`
- `cell.radiusLeft`: `2392`
- `cell.radiusNonneg`: `2392`
- `cell.radiusRight`: `2392`
- `cell.rawLower`: `2392`
- `cell.rawUpper`: `2392`
- `cell.remainder`: `2392`
- `cell.remainderNonneg`: `2392`
- `cell.shapeSqLower`: `2392`
- `cell.shapeSqLowerBound`: `2392`
- `cell.shapeSqUpper`: `2392`
- `cell.shapeSqUpperBound`: `2392`
- `cell.termLower`: `2392`
- `cell.termUpper`: `2392`
- `row.lowerSum`: `92`
- `row.upperSum`: `92`

## Missing Field Groups

- `chunk_geometry`: `11960` missing field instances
  Fields: `cell.center`, `cell.radius`, `cell.radiusNonneg`, `cell.radiusLeft`, `cell.radiusRight`
- `cosine_envelope`: `9568` missing field instances
  Fields: `cell.cosLower`, `cell.cosUpper`, `cell.cosLowerBound`, `cell.cosUpperBound`
- `diff_integral_comparisons`: `9568` missing field instances
  Fields: `cell.diffLower`, `cell.diffUpper`, `cell.integralLower`, `cell.integralUpper`
- `omega_shape_enclosures`: `19136` missing field instances
  Fields: `cell.omegaLower`, `cell.omegaUpper`, `cell.omegaLowerBound`, `cell.omegaUpperBound`, `cell.shapeSqLower`, `cell.shapeSqUpper`, `cell.shapeSqLowerBound`, `cell.shapeSqUpperBound`
- `polynomial_value_bounds`: `16744` missing field instances
  Fields: `cell.termLower`, `cell.termUpper`, `cell.polyLower`, `cell.polyUpper`, `cell.polynomialTermBounds`, `cell.polyLowerSum`, `cell.polyUpperSum`
- `raw_product_bounds`: `9568` missing field instances
  Fields: `cell.rawLower`, `cell.rawUpper`, `cell.componentProductLower`, `cell.componentProductUpper`, `cell.componentProductCornerLowerLLL`, `cell.componentProductCornerLowerLLU`, `cell.componentProductCornerLowerLUL`, `cell.componentProductCornerLowerLUU`, ...
- `row_sum_arithmetic`: `184` missing field instances
  Fields: `row.lowerSum`, `row.upperSum`
- `taylor_model_data`: `9568` missing field instances
  Fields: `cell.degree`, `cell.coeff`, `cell.remainder`, `cell.remainderNonneg`

## Example Missing Rows

### primary_finite
- row `0` d=`0.00` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`
- row `1` d=`0.25` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`
- row `2` d=`0.50` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`

### primary_tail
- row `0` d=`0.00` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`
- row `1` d=`0.25` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`
- row `2` d=`0.50` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`

### control_finite
- row `0` d=`0.00` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`
- row `1` d=`0.25` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`
- row `2` d=`0.50` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`

### control_tail
- row `0` d=`0.00` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`
- row `1` d=`0.25` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`
- row `2` d=`0.50` row_missing=`['lowerSum', 'upperSum']` first_chunk_missing=`['center', 'radius', 'degree', 'coeff', 'remainder', 'omegaLower', 'omegaUpper', 'omegaLowerBound', 'omegaUpperBound', 'shapeSqLower', 'shapeSqUpper', 'shapeSqLowerBound', 'shapeSqUpperBound', 'cosLower', 'cosUpper', 'cosLowerBound', 'cosUpperBound', 'rawLower', 'rawUpper', 'termLower', 'termUpper', 'polyLower', 'polyUpper', 'radiusNonneg', 'remainderNonneg', 'radiusLeft', 'radiusRight', 'polynomialTermBounds', 'polyLowerSum', 'polyUpperSum', 'diffLower', 'diffUpper', 'integralLower', 'integralUpper', 'componentProductLower', 'componentProductUpper']`

## Route Guard

- do not emit trusted Arb/acb integral theorems
- do not mutate A CSV, ARadius, radius-floor, or LDL
- do not route to Q3.Main or H1/PO3
- do not call Step33A.1-A closed until PayloadFin compiles
