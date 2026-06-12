# Step33A.1-A Refined Component-Value Contract

Fail-closed contract.  This is not Lean proof data.

## Verdict

- schema: `q3_psdpd_step33_a_refined_component_value_contract.v1`
- status: `component_value_contract_ready_but_coarse_product_box_rejected`
- receiver: `RawOmegaATaylorModelCertificate.ComponentValueChunkProofData`
- candidate subchunks: `100`
- proof-safe closed fields: `0`
- coarse product-box diff passes: `0`
- coarse product-box diff failures: `100`
- direct residual diff fields still needed: `200`

## Coarse Product-Box Feasibility

- k: `11`
- scaleUpper: `1/10`
- omegaMajorant: `200`
- shapeSqUpper decimal: `5.945454528648124812E-1`
- raw box half-width decimal: `1.189090905729624962E+1`
- test: `coarseRawBoxHalfWidth + polyAbs <= remainder`
- verdict: `rejected_for_pilot`

## Worst Coarse Diff Row

- subchunk: `0`
- interval: `(0.000000000000000000E+0, 1.000000000000000000E-1]`
- polyAbs: `77376358221405977/250000000000000000`
- remainder: `1/1000000000000000000`
- coarse required decimal: `1.220041449018187353E+1`
- coarse excess decimal: `1.220041449018187353E+1`
- sampled max residual: `1.172895333288075275E-19`

## Receiver Lemmas

- `RawOmegaATaylorModelCertificate.ComponentValueChunkProofData.valid`
- `RawOmegaATaylorModelCertificate.ComponentValueBounds.toValueBounds`
- `RawOmegaATaylorModelCertificate.diff_bounds_of_value_bounds`
- `RawOmegaATaylorModelCertificate.polynomial_value_bounds_of_sum_abs_coeff_mul_radius`
- `RawOmegaATaylorModelCertificate.product_bounds_of_scale_abs_box`

## Next Proof Route

- recommended: `direct_universal_residual_enclosure`
- fallback: `sharper_local_component_value_bounds`
- rejected: `coarse_product_abs_box_for_diff`
- reason: `The existing box raw bounds are order 1e1 while the pilot Taylor remainders are 1e-18.`

## Guard

- not Lean proof data
- do not emit a refined Lean payload from this contract
- do not count sampled residual rows as universal diff proofs
- do not use the coarse product abs box to prove tiny diff remainders
- next generator must produce universal diffLower/diffUpper proofs
- do not mutate CSV, ARadius, radius-floor, LDL, H1/PO3, or Q3.Main
