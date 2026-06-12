# Raw-Omega A Quadratic Route Diagnostic

This is a sampled Arb + linear-programming diagnostic, not a Lean proof object.

- samples per window: `257`
- chunk size: `full-window`
- checked indices: `22`
- verdict: `full_window_quadratic_route_sampled_too_coarse`

Positive excess means the full-window quadratic comparison route is
already too coarse at sampled points.  Zero excess only means the route
is not rejected by samples; Lean still needs pointwise comparison proofs
and scalar integral containments.

## primary k=11

- checked indices: `[22]`
- worst finite: index `22`, distance `5.50`, excess `5.613827501195398123E+0`
- worst tail: index `22`, distance `5.50`, excess `1.067109806918619420E-20`

## control k=9

- checked indices: `[22]`
- worst finite: index `22`, distance `5.50`, excess `6.154278758019347799E+0`
- worst tail: index `22`, distance `5.50`, excess `2.003299047276082066E-17`
