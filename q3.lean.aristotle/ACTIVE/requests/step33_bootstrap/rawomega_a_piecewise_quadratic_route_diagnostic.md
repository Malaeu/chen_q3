# Raw-Omega A Quadratic Route Diagnostic

This is a sampled Arb + linear-programming diagnostic, not a Lean proof object.

- samples per window: `33`
- chunk size: `10`
- checked indices: `22`
- verdict: `piecewise_quadratic_route_sampled_too_coarse`

Positive excess means the full-window quadratic comparison route is
already too coarse at sampled points.  Zero excess only means the route
is not rejected by samples; Lean still needs pointwise comparison proofs
and scalar integral containments.

## primary k=11

- checked indices: `[22]`
- worst finite: index `22`, distance `5.50`, excess `1.002771093162155943E+0`
- worst tail: index `22`, distance `5.50`, excess `1.781019264658842132E-21`

## control k=9

- checked indices: `[22]`
- worst finite: index `22`, distance `5.50`, excess `9.921409451690328676E-1`
- worst tail: index `22`, distance `5.50`, excess `2.393425005341697048E-18`
