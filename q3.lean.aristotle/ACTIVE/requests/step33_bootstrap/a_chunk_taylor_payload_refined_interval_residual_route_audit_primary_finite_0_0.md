# Step33A.1-A Refined Interval Residual Route Audit

Fail-closed route audit.  This is not Lean proof data.

## Verdict

- schema: `q3_psdpd_step33_a_refined_interval_residual_route_audit.v1`
- status: `interval_residual_route_rejected_dependency_overestimate`
- audited subchunks: `2`
- passes at max split: `0`
- fails at max split: `2`
- proof-safe closed fields: `0`

## Worst Max-Split Row

- subchunk: `37`
- interval: `(3.700000000000000000E+0, 3.800000000000000000E+0]`
- max-split max abs diff: `3.180632550498579713E-4`
- sampled max residual: `5.167745095026847270E-19`
- estimated splits for 1e-18 remainder: `3.256967731710545626E+17`

## Route Verdict

- rejected: `plain_ball_interval_residual_subtraction`
- reason: `Ball interval subtraction overestimates the residual by many orders of magnitude compared with the 1e-18 remainder.`
- next recommended: `derivative_or_cauchy_taylor_remainder_enclosure`
- fallback: `much_sharper_symbolic_local_component_bounds`

## Guard

- not Lean proof data
- do not import Arb interval residual rows as trusted theorem
- do not increase split counts into a microtask swamp
- plain interval residual subtraction is rejected unless it passes at practical split counts
- next proof-producing generator should use derivative/Cauchy/Taylor-remainder structure
- do not mutate CSV, ARadius, radius-floor, LDL, H1/PO3, or Q3.Main
