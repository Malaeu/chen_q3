# Step33A.1-A hRawCenterCoeffAbs Local Component Contract

Fail-closed contract only.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a_refined_subchunk_hraw_center_coeff_contract.v11`
- status: `arithmetic_ready_missing_component_interval_derivative_enclosures_not_lean_proof`
- receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at`
- zero-distance receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at_zero_distance`
- compact component receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_component_cert_scale_interval_corner_bounds_at_zero_distance`
- compact endpoint receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`
- compact direct endpoint receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`
- raw-center sample-envelope direct endpoint constructor: `RawOmegaATaylorModelCertificate.ResidualAnchorDerivativeSingleCellIntervalRawCenterCoeffSampleEnvelopeFiniteCoverData.of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`
- component ball cert receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert.of_anchor_abs_bounds`
- component anchor-deviation cert receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert.of_anchor_deviation_bounds`
- component Lipschitz cert receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert.of_anchor_lipschitz_bounds`
- component derivative cert receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert.of_anchor_deriv_bounds`
- component auto-diff derivative cert receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert.of_anchor_deriv_bounds_auto_differentiability`
- component interval-derivative cert receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_auto_differentiability`
- rows: `110`
- arithmetic-ready rows: `110`
- arithmetic-failed rows: `0`
- anchor memberships passing: `110`
- zero-distance rows: `110`
- scale proof references: `220`
- cos arithmetic passing: `220 / 220`
- component interval proofs open: `440`
- component interval certs open: `110`
- compact component rows: `110`
- component ball certs open: `110`
- component ball abs facts open: `220`
- component ball containment passing: `440 / 440`
- component anchor-deviation certs open: `110`
- component anchor-deviation analytic facts open: `440`
- component anchor-deviation containment comparisons open: `220`
- component Lipschitz certs open: `110`
- component Lipschitz bound choices open: `660`
- component Lipschitz analytic facts open: `440`
- component Lipschitz endpoint arithmetic passing: `220 / 220`
- component Lipschitz bound arithmetic comparisons open: `660`
- component derivative certs open: `110`
- component derivative bound choices open: `660`
- component derivative analytic facts open: `660`
- component derivative anchor/endpoint arithmetic passing: `330 / 330`
- component derivative bound arithmetic comparisons open: `660`
- component auto-diff derivative certs open: `110`
- component auto-diff fields closed by Lean: `220`
- component auto-diff derivative bound choices open: `660`
- component auto-diff derivative analytic facts open: `440`
- component auto-diff derivative anchor/endpoint arithmetic passing: `330 / 330`
- component auto-diff derivative bound arithmetic comparisons open: `660`
- component interval-derivative certs open: `110`
- component interval-derivative fields closed by Lean: `880`
- component interval-derivative endpoint facts open: `880`
- component interval-derivative arithmetic passing: `770 / 990`
- component interval-derivative containment comparisons open: `220`
- corner arithmetic passing: `3520 / 3520`
- coeff arithmetic passing: `220 / 220`
- proof-safe closed fields: `0`

## Rows By Family

| family | rows |
| --- | ---: |
| `primary_finite` | `110` |

## Worst Arithmetic Row

- family: `primary_finite`
- row: `0`
- parent chunk: `0`
- subchunk: `0`
- status: `arithmetic_ready_missing_component_interval_derivative_enclosures`
- min arithmetic margin: `0.000000000000000000E+18`

## Open Analytic Fields Per Row

```text
hOmegaLower
hOmegaUpper
hShapeSqLower
hShapeSqUpper
```

These four fields are now grouped per zero-distance row by
`LocalRawOmegaComponentIntervalCert`; the underlying analytic work is
unchanged, but the payload-facing interface is one cert per row.

The preferred proof-producing route for those certs is now
`LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_auto_differentiability`:
generated code proves ordinary two-sided endpoint intervals for
the Omega derivative, Omega anchor value, shape-square derivative,
and shape-square anchor value.  Lean converts those intervals into
nonnegative derivative slopes, local-radius definitions, and
center-error balls, then feeds
`of_anchor_deriv_bounds_auto_differentiability` internally.

For zero-distance rows, cosine fields are handled by the checked
`raw_center_coeff_abs_of_local_direct_endpoint_cert_scale_interval_corner_bounds_at_zero_distance`
wrapper using the generated direct endpoint package plus
`cosLower <= 1` and `1 <= cosUpper`.

## Guard

- not Lean proof data
- component interval proofs remain analytic obligations
- zero-distance rows expose one LocalRawOmegaComponentIntervalCert obligation instead of four scattered top-level omega/shape fields
- LocalRawOmegaComponentIntervalCert can now be built from two abs ball bounds plus four norm_num containment comparisons
- preferred v4 route builds those abs ball bounds from anchor-deviation and anchor-value enclosures
- preferred v5 route builds anchor-deviation from local Lipschitz bounds plus endpoint-radius arithmetic
- preferred v6 route builds Lipschitz bounds from derivative bounds on Set.Icc a b
- preferred v7 route discharges component differentiability via existing backend differentiability lemmas
- preferred v8 route converts derivative and anchor endpoint intervals into Lean-computed slope/error bounds
- arithmetic readiness only means future Lean emitter should be able to use norm_num on these constants
- uses d29_pi_p30_decimal_bounds scale mode
- does not emit RefinedPayloadFin
- does not touch CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3
