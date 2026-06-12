# Step33A.1-A Refined Grid Width Accounting

Diagnostic only.  This compares sampled model-produced row intervals
against current generated row targets and recorded target-refresh slack.
It is not Lean proof data and does not mutate any payload.

## Summary

- degree: `16`
- proof data: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_product_abs_seed.json`

| family | policy | model width | target width | needed slack | available slack | verdict |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| `primary_finite` | `first_chunk_split50_rest_split10` | `5.735954211406929304E-15` | `9.400000000000000000E-18` | `5.726554211406929304E-15` | `9.127351807129486100E-19` | `exceeds_recorded_slack` |
| `control_finite` | `first_chunk_split50_rest_split10` | `5.315113721067649400E-15` | `2.700000000000000000E-18` | `5.312413721067649400E-15` | `7.745410560743634378E-17` | `exceeds_recorded_slack` |
| `primary_tail` | `all_split10` | `1.271121904442218263E-35` | `1.000000000000000000E-39` | `1.271021904442218263E-35` | `0.000000000000000000E+0` | `exceeds_recorded_slack` |
| `control_tail` | `all_split10` | `1.716020296314154915E-32` | `3.000000000000000000E-36` | `1.715720296314154915E-32` | `7.753281601564634378E-17` | `fits_recorded_slack` |

## Guard

- diagnostic only
- do not emit Lean payload from this file
- do not mutate CSV, ARadius, radius-floor, or LDL data
- row target refresh must be Lean-checked before payload emission
