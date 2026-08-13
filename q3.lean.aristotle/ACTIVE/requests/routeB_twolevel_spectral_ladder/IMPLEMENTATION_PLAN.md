# Route B — request-local implementation plan

Updated: 2026-08-14 01:56 CEST

Status: `GOAL_058_G3_PROLATE_RATE_AND_FLOOR_OPEN / NOT_RH / CHALLENGER`

This request-local plan does not override the root `IMPLEMENTATION_PLAN.md` or
promote Route B above the H-bridge mainline.

## Current action

The explicit-limit leaf is closed by
`D0PstarExplicitCCMLimitFourier.lean`:

1. the literal polynomial-Gaussian `h` of CCM Eq. (7.1) is defined;
2. its Fourier invariance is proved in the current repository convention;
3. Poisson summation proves multiplicative inversion of `E_star h`.

The current G3 source obligation is the actual normalized two-mode prolate
`h_lambda` on `PairIndex`, the CCM Lemma 7.2 uniform `O(lambda^-2)` estimate to
the proved `h`, a nonzero central overlap and eventual projected denominator
floor, all bound to one precommitted coupled `(m,N)` schedule. G1 stays open as
the parallel spectral front.

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
2. Execute only
   `G3_PROLATE_RATE_CENTRAL_OVERLAP_DENOMINATOR_FLOOR` until it closes or
   reaches an honest source/API stop.
3. Preserve the P59 `_normalized` supplier name lock and the one-family invariant.
4. Do not create Bus 010, promote Route B, or
   claim RH.

Validation:

```bash
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```
