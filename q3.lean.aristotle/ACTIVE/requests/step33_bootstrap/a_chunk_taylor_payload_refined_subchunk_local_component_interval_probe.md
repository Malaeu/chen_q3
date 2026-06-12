# Step33A.1-A Local Component Interval Probe

Diagnostic only.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a_refined_subchunk_local_component_interval_probe.v2`
- status: `local_component_interval_probe_passed_not_lean_proof`
- receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at`
- Arb precision: `1024`
- sinc terms: `128`
- scale mode: `d29_pi_p30_decimal_bounds`
- scale lower: `0.095492965855137201461330258023`
- scale upper: `0.095492965855137201461330258024`
- scale pad override: `None`
- entries: `110`
- passed at some width: `110`
- failed at all widths: `0`
- proof-safe closed fields: `0`

## Width Distribution

| largest passing width | entries |
| ---: | ---: |
| `0.0000000000000000000000000000000001` | `4` |
| `0.00000000000000000000000000000001` | `6` |
| `0.000000000000000000000001` | `3` |
| `0.0000000000000000000001` | `97` |

## Worst Passing Margin

- family: `primary_finite`
- row: `0`
- parent chunk: `1`
- subchunk: `8`
- largest passing width: `0.00000000000000000000000000000001`
- min margin: `8.312257372078911514E-32`
- product width: `1.617320175218033006E-30`
- target width: `2.000000000000000000E-30`

## Next Lean Payload Contract

Each selected row still needs Lean proofs for:

```text
anchor ∈ Set.Ioc a b
∀ eta ∈ Set.Ioc a b, omegaLower <= step22OmegaArchWeight eta
∀ eta ∈ Set.Ioc a b, step22OmegaArchWeight eta <= omegaUpper
∀ eta ∈ Set.Ioc a b, shapeSqLower <= centeredBSplineImagTransformRealClosedForm k ell eta ^ 2
∀ eta ∈ Set.Ioc a b, centeredBSplineImagTransformRealClosedForm k ell eta ^ 2 <= shapeSqUpper
∀ eta ∈ Set.Ioc a b, cosLower <= Real.cos (eta * x)
∀ eta ∈ Set.Ioc a b, Real.cos (eta * x) <= cosUpper
scaleLower <= ell / Real.pi
ell / Real.pi <= scaleUpper
32 scale-interval product corner comparisons
2 coeff0 comparisons
```

## Guard

- diagnostic only, not Lean proof data
- uses local auxiliary intervals (a,b] around anchors
- uses tight rational scale interval, not coarse [9/100,1/10]
- requires later Lean hScaleLower/hScaleUpper facts
- requires later Lean omega/shape/cos interval proofs
- does not emit RefinedPayloadFin
- does not mutate CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3
