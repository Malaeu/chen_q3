# Step33A.1-A Refined Grid Width Accounting

Diagnostic only.  This compares sampled model-produced row intervals
against current generated row targets and recorded target-refresh slack.
It is not Lean proof data and does not mutate any payload.

## Summary

- degree: `12`
- probe suffix: `_decimal`
- proof data: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_product_abs_seed.json`

| family | policy | model width | target width | needed slack | available slack | verdict |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| `primary_finite` | `first_chunk_split50_rest_split10` | `1.686171000000000000E-13` | `9.400000000000000000E-18` | `1.686077000000000000E-13` | `9.127351807129486100E-19` | `exceeds_recorded_slack` |
| `control_finite` | `first_chunk_split50_rest_split10` | `1.849680000000000010E-13` | `2.700000000000000000E-18` | `1.849653000000000010E-13` | `7.745410560743634378E-17` | `exceeds_recorded_slack` |
| `primary_tail` | `all_split10` | `8.469840599917260358E-36` | `1.000000000000000000E-39` | `8.468840599917260358E-36` | `0.000000000000000000E+0` | `exceeds_recorded_slack` |
| `control_tail` | `all_split10` | `1.181871315464934210E-32` | `3.000000000000000000E-36` | `1.181571315464934210E-32` | `7.753281601564634378E-17` | `fits_recorded_slack` |

## Guard

- diagnostic only
- do not emit Lean payload from this file
- do not mutate CSV, ARadius, radius-floor, or LDL data
- row target refresh must be Lean-checked before payload emission
