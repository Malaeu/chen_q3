# Route B — request-local implementation plan

Updated: 2026-08-14 01:20 CEST

Status: `GOAL_058_G3_EXPLICIT_LIMIT_PACKET_SELECTED / NOT_RH / CHALLENGER`

This request-local plan does not override the root `IMPLEMENTATION_PLAN.md` or
promote Route B above the H-bridge mainline.

## Current action

The selected bounded G3 source leaf is:

1. define the literal polynomial-Gaussian `h` of CCM Eq. (7.1);
2. prove its Fourier invariance in the current repository convention;
3. use Poisson summation to prove multiplicative inversion of `E_star h`;
4. feed the result to the proved production coefficient-reflection and
   denominator mechanisms.

G1 stays open as the parallel spectral front.  This leaf does not include the
prolate Lemmas 7.2--7.3 approximation rate or the coupled cofinal schedule.

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
2. Execute only `G3_EXPLICIT_H_FOURIER_POISSON_INVERSION` until it closes or
   reaches an honest source/API stop.
3. Preserve the P59 `_normalized` supplier name lock and the one-family invariant.
4. Do not create Bus 010, promote Route B, or
   claim RH.

Validation:

```bash
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```
