# Step33A.1-A Taylor Payload Polynomial Radius Seed

This seed pass fills direct polynomial value-bound fields only after
`degree`, `coeff`, `radius`, `radiusLeft`, and `radiusRight` already
exist for a cell.

## Verdict

- status: `polynomial_radius_seed_applied`
- source theorem: `RawOmegaATaylorModelCertificate.polynomial_value_bounds_of_sum_abs_coeff_mul_radius`
- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- seeded cells: `0`
- already present cells: `0`
- missing input cells: `2392`
- unsupported numeric input cells: `0`

## Missing Input Field Counts

- `degree`: `2392`
- `coeff`: `2392`
- `radius`: `0`
- `radiusLeft`: `0`
- `radiusRight`: `0`

## Route Guard

- product bounds use checked absolute-box theorem, not trusted Arb output
- direct product fields intentionally bypass 16-corner payload fields
- this seed does not contain Taylor polynomial or remainder proof data
- do not emit Lean until all proof-data fields are complete
- polynomial radius seed does not invent degree/coeff/remainder data
- do not emit Lean until inventory reports ready_to_generate_lean_payload
