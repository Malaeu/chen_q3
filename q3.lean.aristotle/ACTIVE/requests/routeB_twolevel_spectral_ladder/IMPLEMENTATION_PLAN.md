# Route B — request-local implementation plan

Updated: 2026-08-30 23:15 CEST

Status: `GOAL_058_WEIGHTED_RESIDUAL_SOURCE_RATE_SELECTED / NOT_RH / CHALLENGER`

This request-local plan does not override the root `IMPLEMENTATION_PLAN.md` or
promote Route B above the H-bridge mainline.

## Current action

The owner-authorized physical rerank selects exactly one read-only source
discriminator for `SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE`.  Its exact
consumer is

```text
sqrt(selectedFerrersFiniteCCMOddMass P k) *
  sqrt(selectedFerrersFiniteCCMResidualEnergy P k) -> 0
```

on the selected cofinal schedule.  The discriminator must identify an exact
current-shelf supplier or derivation and verify its implication to this
consumer.  Existing source records and plants are evidence; repeating the same
mode/chi or direct Satz9/Fuchs search is forbidden.

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

1. Keep the active physical Goal 058 open.
2. Execute only `SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE` as a read-only
   source discriminator.
3. Do not edit Lean, run numerics, call Aristotle, or dispatch a reviewer.
4. Preserve the P59 `_normalized` supplier name lock and the one-family invariant.
5. Do not create Bus 010, promote Route B, or
   claim RH.

Validation:

```bash
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```
