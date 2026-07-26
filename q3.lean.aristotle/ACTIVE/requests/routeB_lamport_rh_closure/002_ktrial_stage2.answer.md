# kTrial → Lean — stage 2 answer

Date: `2026-07-26`

Verdict: `KTRIAL_STAGE2_ESTAR_CHAIN_LOCKED`

## Artifact

- File: `Q3/Proofs/RouteB/D0KTrialStage2.lean`
- Lines: `68`
- Hole scan: `0 sorry / 0 admit / 0 exact?`

## Source locks

| declaration | D0 / primary source |
| --- | --- |
| `E_star` | `D0_5_GROUND_AND_TRIAL_TYPES.md:81-88`; `PEN_3_3_G04_OBJECT_DICTIONARY.md:112-133`; `fulltext.md:1262-1267,1293-1297` |
| `gTrial_m` | `D0_5_GROUND_AND_TRIAL_TYPES.md:81-92`; `PEN_3_3_G04_OBJECT_DICTIONARY.md:127-133,141-160,169-180`; `fulltext.md:1293-1297,1410-1419` |
| `gTrial_m_N` | `D0_5_GROUND_AND_TRIAL_TYPES.md:81-92`; `PEN_3_3_G04_OBJECT_DICTIONARY.md:195-212` |

`hTrial_m` is the already source-fixed midpoint representative.  Its
`MemLp` witness is explicit; no opaque prolate constant or project axiom was
introduced.

## Build

```text
lake build Q3.Proofs.RouteB.D0KTrialStage2
Build completed successfully (7754 jobs).
exit code: 0
```

## Axioms

```text
'Q3.RouteB.D0Pstar.E_star' depends on axioms:
[propext, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.gTrial_m' depends on axioms:
[propext, Classical.choice, Quot.sound]
'Q3.RouteB.D0Pstar.gTrial_m_N' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

`ROUTE_B_STATE.md`: unchanged at this stage.
