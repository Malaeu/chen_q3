# Route B — request-local implementation plan

Updated: 2026-08-03 23:57 CEST

Status: `IDLE_AWAITING_EXPLICIT_PROSHKA_MATHEMATICAL_TARGET / RB-IDLE-CONTROL / NOT_RH / CHALLENGER`

This request-local plan does not override the root `IMPLEMENTATION_PLAN.md` or
promote Route B above the H-bridge mainline.

## Current action

No mathematical front is selected. `RB-IDLE-CONTROL` is a non-mathematical
sentinel required by the existing state validator; it carries no theorem or
proof obligation.

The next authorized actor is the Proshka route judge. A separate transaction
must select exactly one of:

1. `G2` — H2a / `SimpleEvenLowestQWGround`.
2. `G3` — concrete `Theorem510RealZeroBridge` supplier.
3. `G5` — concrete S1/Montel family supply.
4. `G6` — full S2 identification wall.

G3 is the strongest candidate after the closeout, but it is not selected by
this document. Goal 051/M1 is not implicitly authorized.

## Physical bus

- `001..009` are closed.
- No unanswered physical goal exists.
- `010` is only the next free number.
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

1. Physical unanswered bus goal, if one ever appears, has precedence.
2. Otherwise remain idle until Proshka explicitly selects one mathematical
   front in a separate authorized transaction.
3. Execute only that bounded target and validate it independently.
4. Do not create Bus 010, authorize Goal 051 implicitly, promote Route B, or
   claim RH.

Validation:

```bash
python3 q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_status.py --check
```
