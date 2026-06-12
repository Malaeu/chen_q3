# Step33A A-source convention audit

This is a non-mutating diagnostic.  It compares the Step22 `Omega(t)`
finite-window source against the active Lean `Q3.a_star` finite-window
source on the same positive window, then also compares their doubled
even/full-window values.

It is not a Lean proof object and does not edit `ARadius`, CSV files,
radius-floor data, or global payload radii.

## Summary

### primary

- k_spline: `11`
- rows: `23`
- worst distance index: `0`
- worst distance: `0.00`
- Step22 full-even midpoint: `2.467288907278439000000000000000e-1`
- Lean a_star full-even midpoint: `-7.889774143023172000000000000000e+1`
- absolute mismatch: `7.914447032095956390000000000000e+1`

### control

- k_spline: `9`
- rows: `23`
- worst distance index: `0`
- worst distance: `0.00`
- Step22 full-even midpoint: `5.249780731754968800000000000000e-2`
- Lean a_star full-even midpoint: `-7.520513017099184000000000000000e+1`
- absolute mismatch: `7.525762797830938968800000000000e+1`

## Interpretation

A valid local recenter proof cannot identify the current Step22 A payload
with the active Lean `centeredBSplineArchKernelProfile` receiver until the
Arch source convention is chosen and formalized.
