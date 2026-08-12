# Route B — request-local implementation plan

Updated: 2026-08-12 19:56 CEST

Status: `GOAL_058_G2B_NAME_LOCKED_EXECUTION_AUTHORIZED / NOT_RH / CHALLENGER`

This request-local plan does not override the root `IMPLEMENTATION_PLAN.md` or
promote Route B above the H-bridge mainline.

## Current action

Goal 058 G2b is selected. First implement
`Proposition59GroundLagrangeZeroSetBridge` under the exact name lock in
`docs/routeB_bus/CODEX_DIRECTIVE_ROUTE058_P59_G2B_2026-08-12.md`. The final CCM
supplier must be
`Q3.RouteB.ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized`.

In parallel, execute one finite M1 control-cell measurement of the source-locked ground
line against the source trial at `(lambda_sq,N)=(13,120)`. In the background, repair
EnvDump's import-collision failure and wire the derived index into `atom_describe.py`.
These two auxiliary lanes remain diagnostic/tooling work and cannot close a uniform
theorem or promote the route.

## Physical bus

- The newest physical root is `058`.
- `058_realzero_ground_diagonal_to_xi.goal.md` is unanswered and active.
- `059` is the next free number.
- `BUS_010: VOID`.
- Codex may not create a bus goal.

## D0 terminal closeout

The source-locked D0.7e.5a branch is terminal historical at base pin
`6af9170d15a38e451a76f8dbf2ad8725d62b6f5f`.

```text
historical stop: D0_7E_WPRIME_CONSUMER_MISSING
materialization: D0_7E_5A_TERMINAL_CLOSEOUT_AND_H2B_REPOINT_MATERIALIZED
CCM classification: SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY
CCM destination: G3/H2b conditional evidence only
```

The historical D0/WPrime/FZeo/equation-5c edge is not a live dependency.
Finite calibration facts and the generic `NormalizedTrackingRateTransfer` and
`SafeBoundsToSquareEnvelope` Lean receivers remain preserved.

## Execution rule

1. Execute the active physical Goal 058 only.
2. Preserve the P59 `_normalized` supplier name lock and the one-family invariant.
3. Validate P59, the finite M1 diagnostic, and EnvDump wiring independently.
4. Do not create Bus 010, promote Route B, or
   claim RH.

Validation:

```bash
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```
