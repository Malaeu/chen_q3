# Step33A.1-A Taylor Payload Product Abs Seed

This seed fills direct symmetric raw-product bounds using a checked
absolute-box theorem.  It avoids the generated 16-corner product
payload surface.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1`
- status: `product_abs_seed_chunk_bounds_geometry_row_sums_scale_cos_shape_omega_and_raw_product`
- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- product seeded cells: `2392`
- already present cells: `0`
- theorem: `RawOmegaATaylorModelCertificate.product_bounds_of_scale_abs_box`

## Populated Fields

- `rawLower`: `2392`
- `rawUpper`: `2392`
- `componentProductLower`: `2392`
- `componentProductUpper`: `2392`

## Families

| family | rows | chunks | product seeded cells | already present |
| --- | ---: | ---: | ---: | ---: |
| primary_finite | None | None | 598 | 0 |
| primary_tail | None | None | 598 | 0 |
| control_finite | None | None | 598 | 0 |
| control_tail | None | None | 598 | 0 |

## Guard

- product bounds use checked absolute-box theorem, not trusted Arb output
- direct product fields intentionally bypass 16-corner payload fields
- this seed does not contain Taylor polynomial or remainder proof data
- do not emit Lean until all proof-data fields are complete
