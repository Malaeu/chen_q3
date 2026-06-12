# Step33A Canonical-A Kernel Obstruction

This is a non-mutating diagnostic.  It checks the necessary condition
for the current Step32/Step33 formula contract:

```text
C = A - P
```

If `C` is negative on `ker(Q)`, no `P0` split can certify the current
receiver without changing the semantic receiver or the assembler sign.

## Summary

| family | source | A ker(Q) min | A ker(Q) max | C=A-P ker(Q) min | C=A-P ker(Q) max | C nonnegative |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| primary | raw_step22_positive_axis | -1.0226763274327562e+00 | 7.2878758477976657e-01 | 1.9028360433413977e-04 | 2.6173846764364201e+00 | True |
| primary | transformed_step22_omega_arch_sign | -1.0110826719608505e+02 | -3.8662678729190482e+01 | -1.0166261779501350e+02 | -3.7520951447470431e+01 | False |
| primary | negative_transformed_step22_omega_arch_sign | 3.8662678729190482e+01 | 1.0110826719608505e+02 | 3.9802694867866670e+01 | 1.0236204332181914e+02 | True |
| control | raw_step22_positive_axis | -1.2461947201512449e+00 | 7.0369117301870443e-01 | 1.9075927801682280e-05 | 2.5829399901659920e+00 | True |
| control | transformed_step22_omega_arch_sign | -9.9655826808067829e+01 | -3.0870400785124033e+01 | -1.0027231457492014e+02 | -2.9530754335962591e+01 | False |
| control | negative_transformed_step22_omega_arch_sign | 3.0870400785124033e+01 | 9.9655826808067829e+01 | 3.2208844727093663e+01 | 1.0084265426845738e+02 | True |

## Decision

- transformed A feasible for current `C = A - P` contract: `False`
- worst family: `primary`
- worst transformed `C` minimum on `ker(Q)`: `-1.0166261779501350e+02`
- next action: `semantic sign/assembler review; do not search P0 split until C=A-P sign is resolved`

Interpretation:

The transformed Arch-sign receiver is not merely incompatible with the
old `P0` split.  With the current formula contract `C = A - P`, the
finite form itself is negative on the boundary-null subspace.  A new
`P0` split cannot repair that, because any split still sums back to
`C`.

The raw Step22 payload passes this necessary test, and `-transformed`
also passes numerically, but neither is acceptable as the analytic
receiver without a checked semantic sign/assembler theorem.
