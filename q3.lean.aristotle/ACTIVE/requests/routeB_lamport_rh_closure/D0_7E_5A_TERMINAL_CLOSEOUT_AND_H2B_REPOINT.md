# D0.7e.5a terminal closeout and H2b repoint

Status: `D0_7E_5A_TERMINAL_CLOSEOUT_AND_H2B_REPOINT_MATERIALIZED`

Base pin: `6af9170d15a38e451a76f8dbf2ad8725d62b6f5f`

Materialized: 2026-08-03 23:57 CEST

Authority: Proshka verdict `AUTHORIZE_D0_TERMINAL_CLOSEOUT_AND_H2B_REPOINT_TRANSACTION`, accepted under the human owner's direct delegation. Mythos is not an active actor in this transaction.

## Scope and route effect

- The source-locked `D0.7e.5a` branch is terminally closed as an exhausted, pin-specific branch.
- Historical stop: `D0_7E_WPRIME_CONSUMER_MISSING`.
- The historical stop is not the current machine address after this transaction.
- The route is idle and awaits a separate, explicit Proshka selection of exactly one mathematical front.
- Route effect: none.
- Route label: `CHALLENGER / NOT_RH`.
- `ROUTE_PROMOTION=false`.
- `RH_CLAIMED=false`.
- `BUS_010: VOID`.
- Goal 051/M1 is not authorized or selected.

## Dependency-impact disposition

The completed read-only audit searched 180 unique tracked files.

| Surface | Count / edge | Disposition |
| --- | ---: | --- |
| Dedicated D0.7e.5a artifacts | 12 | `CLOSE_WITH_D0` |
| Active-leaf/current-stop mirrors | 98 | `CLOSE_WITH_D0` for pointer fields only; independent theorem/certificate bodies preserved |
| `FZeo` references | 18 | `CLOSE_WITH_D0` |
| Direct equation-5c references | 5 | `CLOSE_WITH_D0` |
| `D0.7e.5c ExactWPrimeConsumerIdentity` | 1 edge | `CLOSE_WITH_D0` |
| WPrime-specific `H3e ExactWPrimeTrackingTheorem` | 1 edge | `CLOSE_WITH_D0` |
| Concrete WPrime instantiation of `H4d2` | 1 edge | `CLOSE_WITH_D0` |
| CCM/determinant references used as failed D0 mints or falsifiers | 4 of 41 | `CLOSE_WITH_D0` |
| Remaining CCM operator/determinant/real-zero references | 37 of 41 | `REPOINT_TO_H2B` |

Closed material remains available only as explicitly terminal historical provenance. It is not a live dependency, selected consumer, or current route address.

## Preserved finite facts — exact strings

The following strings are preserved exactly as the transaction ledger facts:

```text
bCal=bDet=Fhat(0)/Xi(0)
CentralValueNonzero=BDetNonzero=FhatAtZeroNonzero=BCalNonzero
TrialNonzero does not imply CentralValueNonzero
bZeoMul=bCal^(-1) on the legal locus
G=bZeoMul*Fhat
G(0)=Xi(0)
independent (m,N) carrier
NormalizedTrackingRateTransfer
SafeBoundsToSquareEnvelope
```

The first six are finite calibration/nonzero-locus facts. The independent `(m,N)` carrier remains unchanged. `NormalizedTrackingRateTransfer` and `SafeBoundsToSquareEnvelope` remain generic Lean receivers; their WPrime-specific concrete instantiations are not retained as live edges.

## CCM classification and H2b repoint

Exact classification:

```text
SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY
```

The CCM finite rank-one operator, regularized determinant, and real-zero theorem are conditional neighboring evidence for `G3 / H2b / Theorem510RealZeroBridge`. They are not a source recovery of a nonnegative WPrime consumer and do not prove equation 5c.

This repoint does not set any of the following to proved:

```text
H2b
G3
Theorem510RealZeroBridge
```

Goal 051/M1 remains only a separate keystone and is not implicitly authorized.

## Four-front invariant

`docs/routeB_bus/MAP.md` remains byte-unchanged and continues to expose exactly four open fronts:

```text
G2 — H2a / SimpleEvenLowestQWGround
G3 — concrete Theorem510RealZeroBridge supplier
G5 — concrete S1/Montel family supply
G6 — full S2 identification wall
```

No front is selected or executed by this closeout transaction. G3 is the strongest candidate after closeout, but selection requires a separate explicit Proshka decision.

## Control-plane terminal state

```text
operational_status=IDLE_AWAITING_EXPLICIT_PROSHKA_MATHEMATICAL_TARGET
current_stage=RB-IDLE
current_obligation=RB-IDLE-CONTROL
current_active_leaf=RB-IDLE-CONTROL (non-mathematical control sentinel)
current_code=AWAITING_EXPLICIT_PROSHKA_MATHEMATICAL_TARGET
next_actor=Proshka route judge
physical_bus_goal=NONE
next_free_bus_number=010
codex_may_create_bus_goal=false
```

## Frozen boundaries

- No Lean file or theorem body is edited.
- No historical D0.7e.5a evidence artifact is deleted or rewritten.
- No WPrime, FZeo, `b` orientation, or equation 5c definition is minted.
- The CCM determinant is not renamed or promoted into the dead consumer slot.
- H2a, H2b, G3, S1, and S2 remain open where they were open.
- `docs/routeB_bus/MAP.md` is not edited.
- No physical Bus 010 file is created.
- Route B remains `CHALLENGER / NOT_RH`.

## Validation contract

Materialization is successful only if all of the following hold:

1. Canonical and mirror closeout artifacts are byte-identical.
2. `STATE.json`, `ROUTE_B_EXECUTION_STATE.json`, and `loop_state.json` parse strictly.
3. `routeb_status.py --check` exits zero.
4. No D0/WPrime/FZeo/5c item remains the current leaf, next action, live dependency, or selected consumer.
5. The preserved fact strings above are present unchanged.
6. Dedicated historical D0 artifacts and all Lean files remain untouched.
7. CCM is labeled exactly `SOURCE_PARTIAL_NEIGHBORING_DETERMINANT_ONLY` under conditional G3/H2b evidence, with no H2b closure.
8. `MAP.md` remains byte-unchanged with exactly G2, G3, G5, and G6 open.
9. Manifest hashes cover every changed or newly created transaction artifact except the self-excluded manifest.
10. Bus 010 remains absent; Goal 051 remains unauthorized; there is no route or RH promotion.
