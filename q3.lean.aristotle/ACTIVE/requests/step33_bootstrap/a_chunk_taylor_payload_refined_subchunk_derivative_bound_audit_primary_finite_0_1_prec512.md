# Step33A.1-A Refined Subchunk Derivative Bound Audit

Diagnostic derivative audit.  This is not Lean proof data.

## Verdict

- status: `derivative_audit_numeric_nonfinite_bounds_no_proof`
- family: `primary_finite`
- row: `0`
- parent chunk: `1`
- degree: `16`
- split: `10`

## Counts

| item | count |
| --- | ---: |
| `subchunks` | `10` |
| `checkedSubchunksBeforeError` | `0` |
| `numericErrorSubchunks` | `10` |
| `proofSafeClosedFields` | `0` |

## Numeric Errors

| subchunk | left | right | error | message |
| ---: | ---: | ---: | --- | --- |
| 0 | `1.000000000000000000E+1` | `1.100000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |
| 1 | `1.100000000000000000E+1` | `1.200000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |
| 2 | `1.200000000000000000E+1` | `1.300000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |
| 3 | `1.300000000000000000E+1` | `1.400000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |
| 4 | `1.400000000000000000E+1` | `1.500000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |
| 5 | `1.500000000000000000E+1` | `1.600000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |
| 6 | `1.600000000000000000E+1` | `1.700000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |
| 7 | `1.700000000000000000E+1` | `1.800000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |
| 8 | `1.800000000000000000E+1` | `1.900000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |
| 9 | `1.900000000000000000E+1` | `2.000000000000000000E+1` | `ValueError` | `non-finite Arb bound lower=NaN upper=NaN` |

## Guard

- do not emit Lean from this derivative audit
- non-finite Arb derivative bounds are a diagnostic blocker, not proof data
- rerun with sharper local bounds or adjusted precision/split before direct overlay emission
- proofSafeClosedFields remains zero
