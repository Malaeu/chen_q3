# Step33A.1-A Raw-Center-Coeff Value-Bounds Worklist

Address-only worklist.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a_refined_subchunk_raw_center_coeff_value_bounds_worklist.v4`
- status: `raw_center_coeff_value_bounds_worklist_address_only`
- receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_raw_value_bounds_at`
- component corner receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_raw_component_corner_bounds_at`
- interval component corner receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_interval_raw_component_corner_bounds_at`
- local interval component corner receiver: `RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_local_interval_raw_component_corner_bounds_at`
- parents: `2`
- hRawCenterCoeffAbs fields: `110`
- raw-value analytic inputs: `220`
- component analytic inputs: `660`
- interval component inputs: `770`
- local interval component inputs: `770`
- anchor membership inputs: `110`
- product corner arithmetic inputs: `1760`
- coeff comparison arithmetic inputs: `220`
- coeff comparison arithmetic passing: `220`
- sampled diagnostic passing: `110`
- anchor diagnostic passing: `110`
- proof-safe closed fields: `0`

## Bound Shape

For each subchunk the target raw-value enclosure is:

```text
rawLower = coeff0 - sampleRadius
rawUpper = coeff0 + sampleRadius
```

The coeff0 comparisons are exact rational metadata; the two raw-value
inequalities remain analytic proof obligations.

The checked component-corner receiver can prove each raw-value
enclosure from six component bounds and sixteen rational product-corner
comparisons.

The checked interval-component receiver lets generated code reuse
component bounds on `(L,U]` plus the already seeded `hAnchorIn` fact,
instead of emitting separate pointwise component proofs at each anchor.

The checked local-interval receiver is the sharper active target when
full-subchunk component boxes are too wide: it uses an auxiliary
`anchor ∈ Set.Ioc a b` fact and component proofs on `(a,b]`, while
the Taylor certificate remains on its original `(L,U]` window.

## Worst Sampled Diagnostic

- family: `primary_finite`
- row: `0`
- parentChunk: `1`
- subchunk: `4`
- interval: `(1.400000000000000000E+1, 1.500000000000000000E+1]`
- sampleRadius: `1.000000000000000000E-30`
- sampled residual margin: `1.724596048574376726E-31`

## Parents

| family | row | parent | split | hRawCenterCoeffAbs | raw analytic inputs | coeff arithmetic | sampled pass |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `primary_finite` | `0` | `0` | `100` | `100` | `200` | `200` | `100` |
| `primary_finite` | `0` | `1` | `10` | `10` | `20` | `20` | `10` |

## Guard

- address-only worklist
- not Lean proof data
- sampled diagnostics are not trusted proof inputs
- component corner receiver is checked Lean glue, not a numerical oracle
- local interval component receiver allows a,b around anchor distinct from cert L,U
- rawLower/rawUpper are target enclosures around coeff0, not claims
- do not emit RefinedPayloadFin while raw-value inequalities remain unproved
- do not mutate CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3
