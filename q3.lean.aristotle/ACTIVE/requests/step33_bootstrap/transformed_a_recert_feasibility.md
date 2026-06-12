# Step33A Transformed-A Recert Feasibility Dry-Run

This is a non-mutating diagnostic.  It scans the transformed Arch-sign A
against the existing split shape without editing CSV, radius-floor, or LDL data.

Key point: `tau * Q^T Q` vanishes on `ker(Q)`, so boundary-null negativity
cannot be repaired by increasing `tau`.

## Summary

| family | old-param D pass | old-param R pass | best joint ker(Q) min | signed kappa | theta | R ker(Q) min | D ker(Q) min | feasible |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| primary | False | False | -9.4613971912422613e+01 | 1.1525423728813560e+03 | 7.4999999999999997e-02 | -9.4020155510901176e+01 | -9.4613971912422613e+01 | False |
| control | False | False | -9.3340232641296438e+01 | 1.1525423728813560e+03 | 7.4999999999999997e-02 | -9.2488702985342258e+01 | -9.3340232641296438e+01 | False |

## Decision

- transformed-A recert feasible in scan: `False`
- tau can fix boundary-null failure: `False`
- worst family: `primary`
- worst joint boundary-null min: `-9.4613971912422613e+01`
- next action: `do not start LDL/radius-floor migration; escalate semantic/route choice or search a new split/P0 model`

Interpretation:

Under the existing split shape, transformed A does not have an immediate
finite PSD recert path.  The obstruction is already visible on `ker(Q)`,
so increasing penalty weights cannot repair it.
